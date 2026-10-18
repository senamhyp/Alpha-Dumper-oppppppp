from alpha.h02 import windows_run as _host_run

import bisect
import hashlib
import json
import mmap
import os
import stat
import struct
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Iterable, Mapping, Sequence

from alpha.p12 import SNAPSHOT_MAGIC, SNAPSHOT_VERSION, _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.c06 import LiveRuntimeInventory, rebind_method
from alpha.p29 import _runtime
from alpha.p38 import _binding as _proto_inventory_binding
from alpha.p40 import _roundtrip_binding
from alpha.h02 import (
    _file_fingerprint,
    file_identity,
    read_json,
    sha256_file,
)


PLAN_SCHEMA = "alpha.runtime-proto-field-mutation-plan/v2"
NORMALIZED_SCHEMA = "alpha.runtime-proto-field-mutation-probe/v2"
BUILD_PLAN_SCHEMA = "alpha.runtime-proto-field-mutation-build-plan/v1"
STATUS_SCHEMA = "alpha.runtime-proto-field-mutation-status/v1"
RESULT_SCHEMA = "alpha.runtime-proto-field-mutation-result/v2"
OUTPUT_MAGIC = b"ALPHAPM1"
OUTPUT_VERSION = 1
OUTPUT_HEADER = struct.Struct("<8s4I5Q64s")
OUTPUT_RECORD = struct.Struct("<8I8Q")


SNAPSHOT_INDEX_RECORD = struct.Struct("<QQ4I")


_SNAPSHOT_TYPE_BITS = struct.Struct("<QQ")
WIRE_VARINT = 0
WIRE_FIXED64 = 1
WIRE_LENGTH = 2
WIRE_FIXED32 = 5


TYPE_WIRE_MASKS: dict[int, int] = {
    0x02: 1 << WIRE_VARINT,
    0x03: 1 << WIRE_VARINT,
    0x04: 1 << WIRE_VARINT,
    0x05: 1 << WIRE_VARINT,
    0x06: 1 << WIRE_VARINT,
    0x07: 1 << WIRE_VARINT,
    0x08: (1 << WIRE_VARINT) | (1 << WIRE_FIXED32),
    0x09: (1 << WIRE_VARINT) | (1 << WIRE_FIXED32),
    0x0A: (1 << WIRE_VARINT) | (1 << WIRE_FIXED64),
    0x0B: (1 << WIRE_VARINT) | (1 << WIRE_FIXED64),
    0x0C: 1 << WIRE_FIXED32,
    0x0D: 1 << WIRE_FIXED64,
    0x0E: 1 << WIRE_LENGTH,
    0x11: 1 << WIRE_VARINT,
    0x12: 1 << WIRE_LENGTH,
    0x15: 1 << WIRE_LENGTH,
    0x1C: sum(1 << wire for wire in (0, 1, 2, 5)),
    0x1D: 1 << WIRE_LENGTH,
}


@dataclass(frozen=True)
class SnapshotRegion:
    address: int
    size: int
    file_offset: int

    @property
    def end(self) -> int:
        return self.address + self.size


class RuntimeSnapshot:


    _index_cache: tuple[bytes, tuple[SnapshotRegion, ...], tuple[int, ...], tuple[int, ...]] | None = None


    _HASH_BLOCK_BYTES = 8 * 1024 * 1024

    def __init__(self, path: Path):
        self.path = path
        self._file = path.open("rb")
        self._mapping = None
        self.content_digest: bytes | None = None


        self._type_enum_cache: dict[int, int] = {}
        try:
            self._mapping = mmap.mmap(self._file.fileno(), 0, access=mmap.ACCESS_READ)
            self._advise_sequential()
            self._initialize_index()
        except BaseException:
            if self._mapping is not None:
                self._mapping.close()
            self._file.close()
            raise

    def _advise_sequential(self) -> None:


        advise = getattr(os, "posix_fadvise", None)
        if advise is None:
            return
        try:
            advise(
                self._file.fileno(), 0, 0, os.POSIX_FADV_SEQUENTIAL
            )
        except (OSError, ValueError):
            pass

    def _initialize_index(self) -> None:
        if len(self._mapping) < 80:
            raise ValueError("runtime snapshot is truncated")
        values = struct.unpack_from("<8sII8Q", self._mapping, 0)
        magic, version, header_bytes = values[:3]
        if (magic, version) not in {
            (b"ALPHAMS4", 4), (SNAPSHOT_MAGIC, SNAPSHOT_VERSION)
        } or header_bytes != 80:
            raise ValueError("unsupported runtime snapshot schema")
        self.image_base = values[3]
        self.image_bytes = values[4]
        record_count = values[5]
        captured_bytes = values[6]
        self.region_count = values[7]
        content_digest = self._content_digest()
        cached = RuntimeSnapshot._index_cache
        if cached is not None and cached[0] == content_digest:
            self._regions, self._starts, self._prefix_ends = cached[1:]
            self.content_digest = content_digest
            return
        self._regions, self._starts, self._prefix_ends = self._parse_index(
            record_count, header_bytes, captured_bytes
        )
        if self._content_digest() != content_digest:
            raise ValueError("runtime snapshot changed while indexing")
        self.content_digest = content_digest
        RuntimeSnapshot._index_cache = (
            content_digest, self._regions, self._starts, self._prefix_ends
        )

    @property
    def content_sha256_hex(self) -> str:
        if self.content_digest is None:
            raise ValueError("runtime snapshot digest is unavailable")
        return self.content_digest.hex()

    @property
    def content_byte_count(self) -> int:
        return len(self._mapping)

    def sealed_identity(self) -> dict[str, Any]:
        return {
            "path": str(self.path),
            "bytes": self.content_byte_count,
            "sha256": self.content_sha256_hex,
        }

    def _content_digest(self) -> bytes:


        try:
            before = _file_fingerprint(self.path)
        except AcquisitionError as error:
            raise ValueError("runtime snapshot is unavailable") from error
        if self._fd_fingerprint() != before:
            raise ValueError("runtime snapshot changed while indexing")
        try:
            digest = sha256_file(self.path)
        except AcquisitionError as error:
            raise ValueError("runtime snapshot is unavailable") from error
        try:
            after = _file_fingerprint(self.path)
        except AcquisitionError as error:
            raise ValueError("runtime snapshot is unavailable") from error
        if self._fd_fingerprint() != after or after != before:
            raise ValueError("runtime snapshot changed while indexing")
        return bytes.fromhex(digest)

    def _fd_fingerprint(self) -> tuple[int, int, int, int, int]:


        try:
            status = os.fstat(self._file.fileno())
        except OSError as error:
            raise ValueError("runtime snapshot is unavailable") from error
        return (
            status.st_dev,
            status.st_ino,
            status.st_size,
            status.st_mtime_ns,
            status.st_ctime_ns,
        )

    def _parse_index(
        self, record_count: int, header_bytes: int, captured_bytes: int
    ) -> tuple[tuple[SnapshotRegion, ...], tuple[int, ...], tuple[int, ...]]:


        mapping = self._mapping
        mapping_len = len(mapping)
        unpack_record = SNAPSHOT_INDEX_RECORD.unpack_from
        region_cls = SnapshotRegion
        cursor = header_bytes
        regions: list[SnapshotRegion] = []
        append_region = regions.append
        observed_bytes = 0
        for _ in range(record_count):
            if cursor + 32 > mapping_len:
                raise ValueError("runtime snapshot record is truncated")
            address, size, _protect, _memory_type, _state, reserved = unpack_record(
                mapping, cursor
            )
            cursor += 32
            if reserved or not size or cursor + size > mapping_len:
                raise ValueError("runtime snapshot record is invalid")
            append_region(region_cls(address, size, cursor))
            cursor += size
            observed_bytes += size
        if cursor != mapping_len or observed_bytes != captured_bytes:
            raise ValueError("runtime snapshot envelope does not close exactly")


        regions = tuple(sorted(regions, key=lambda region: (region.address, region.size)))
        starts = tuple(region.address for region in regions)
        prefix_ends = []
        greatest_end = 0
        for region in regions:
            greatest_end = max(greatest_end, region.end)
            prefix_ends.append(greatest_end)
        return regions, starts, tuple(prefix_ends)

    def close(self) -> None:
        self._mapping.close()
        self._file.close()

    def __enter__(self) -> "RuntimeSnapshot":
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def read(self, address: int, size: int) -> bytes:
        if address <= 0 or size <= 0:
            raise ValueError("snapshot read must have a positive address and size")
        regions = self._regions
        starts = self._starts
        prefix_ends = self._prefix_ends
        mapping = self._mapping
        index = bisect.bisect_right(starts, address) - 1


        requested_end = address + size
        while index >= 0 and prefix_ends[index] >= requested_end:
            region = regions[index]
            if address + size <= region.end:
                offset = region.file_offset + address - region.address
                return mapping[offset : offset + size]
            index -= 1
        raise KeyError(f"address 0x{address:x}+0x{size:x} is absent from snapshot")

    def il2cpp_type_enum(self, descriptor: int) -> int:


        cached = self._type_enum_cache.get(descriptor)
        if cached is None:
            _data, bits = _SNAPSHOT_TYPE_BITS.unpack(self.read(descriptor, 16))
            cached = (bits >> 16) & 0xFF
            self._type_enum_cache[descriptor] = cached
        return cached


def _sha256(path: Path) -> str:


    return sha256_file(path)


def _load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"JSON root must be an object: {path}")
    return value


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime proto field mutation {label} is not owner-only"
        )
    return path


def _strict_u32_list(values: Iterable[Any], label: str) -> list[int]:
    result: list[int] = []
    for value in values:
        if not isinstance(value, int) or isinstance(value, bool) or not 0 < value <= 0x1FFFFFFF:
            raise ValueError(f"{label} contains an invalid protobuf field number")
        result.append(value)
    if len(result) != len(set(result)):
        raise ValueError(f"{label} contains duplicate field numbers")
    return sorted(result)


def _parser_candidate_wires(
    source: Mapping[str, Any], candidates: Sequence[int]
) -> dict[int, int]:
    raw = source.get("candidate_evidence_owner_only")
    if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes)):
        raise ValueError("parser candidate evidence is absent")
    output: dict[int, int] = {}
    for row in raw:
        if not isinstance(row, Mapping):
            raise ValueError("parser candidate evidence entry is invalid")
        number = row.get("number")
        wire = row.get("wire")
        raw_tag = row.get("raw_tag")
        sources = row.get("sources")
        if (
            not isinstance(number, int)
            or isinstance(number, bool)
            or not 0 < number <= 0x1FFFFFFF
            or not isinstance(wire, int)
            or isinstance(wire, bool)
            or wire not in (WIRE_VARINT, WIRE_FIXED64, WIRE_LENGTH, WIRE_FIXED32)
            or not isinstance(raw_tag, int)
            or isinstance(raw_tag, bool)
            or raw_tag != (number << 3) | wire
            or not isinstance(sources, Sequence)
            or isinstance(sources, (str, bytes))
            or "bounded-parser-tag-case" not in sources
        ):
            raise ValueError("parser candidate evidence entry is invalid")
        if number in output:
            raise ValueError("parser candidate evidence duplicates a field number")
        output[number] = wire
    if set(output) != set(candidates):
        raise ValueError("parser candidate evidence domain differs")
    return output


def normalize_plan(plan: Mapping[str, Any], snapshot: RuntimeSnapshot, *, allow_serializer_audit: bool = False) -> dict[str, Any]:
    if plan.get("schema") != PLAN_SCHEMA:
        raise ValueError("field mutation plan schema mismatch")
    if plan.get("status") != "offline-plan-complete":
        raise ValueError("field mutation plan is not complete")
    checks = plan.get("checks")
    if not isinstance(checks, Mapping) or not all(checks.values()):
        raise ValueError("field mutation plan checks are not all closed")
    policy = plan.get("policy")
    serializer_audit = (allow_serializer_audit and plan.get("purpose") == "signed-scalar-serializer-audit"
                        and isinstance(policy, Mapping) and policy.get("serializer_audit_required") is True)
    serializer_differential = (
        allow_serializer_audit
        and plan.get("purpose") == "normal-field-serializer-closure"
        and isinstance(policy, Mapping)
        and policy.get("serializer_differential_required") is True
    )
    serializer_plan = serializer_audit or serializer_differential
    if not isinstance(policy, Mapping) or not (policy.get("merge_from_only") or serializer_plan):
        raise ValueError("field mutation plan must be MergeFrom-only")
    if policy.get("write_to_used") and not serializer_plan:
        raise ValueError("WriteTo is forbidden for the mutation collector")

    normalized_messages: list[dict[str, Any]] = []
    deferred_fields: list[dict[str, Any]] = []
    field_count = 0
    expected_probes = 0
    observed_type_enums: dict[str, int] = {}
    mode_counts: dict[str, int] = {}
    for message_index, source in enumerate(plan.get("messages_owner_only", [])):
        if not isinstance(source, Mapping):
            raise ValueError("message probe entry must be an object")
        identity = source.get("type_identity_owner_only")
        fields = source.get("fields_owner_only")
        if not isinstance(identity, Mapping) or not isinstance(fields, Sequence) or not fields:
            raise ValueError("message probe entry lacks identity or fields")
        type_index = identity.get("type_index_owner_only")
        if not isinstance(type_index, int) or type_index < 0:
            raise ValueError("message probe identity is invalid")

        normalized_fields: list[dict[str, Any]] = []
        message_wire_mask = 0
        seen_field_indexes: set[int] = set()
        for raw_field in fields:
            if not isinstance(raw_field, Mapping):
                raise ValueError("field probe entry must be an object")
            field_index = raw_field.get("field_index_owner_only")
            offset = raw_field.get("managed_offset_owner_only")
            descriptor = raw_field.get("type_descriptor_owner_only")
            if (
                not isinstance(field_index, int)
                or field_index < 0
                or field_index in seen_field_indexes
                or not isinstance(offset, int)
                or not 0 <= offset <= 0xFFFFFFEF
                or not isinstance(descriptor, int)
                or not descriptor
            ):
                raise ValueError("field probe coordinates are invalid")
            seen_field_indexes.add(field_index)
            try:
                type_enum = snapshot.il2cpp_type_enum(descriptor)
            except KeyError:


                deferred_fields.append(
                    {
                        "message": str(source.get("message", "")),
                        "field_index_owner_only": field_index,
                        "type_descriptor_owner_only": descriptor,
                        "reason": "snapshot-unavailable-type-descriptor",
                    }
                )
                continue
            wire_mask = TYPE_WIRE_MASKS.get(type_enum)
            if wire_mask is None:
                deferred_fields.append(
                    {
                        "message": str(source.get("message", "")),
                        "field_index_owner_only": field_index,
                        "type_descriptor_owner_only": descriptor,
                        "runtime_type_enum": type_enum,
                        "reason": "unsupported-runtime-type-enum",
                    }
                )
                continue
            observed_type_enums[str(descriptor)] = type_enum
            message_wire_mask |= wire_mask
            normalized_fields.append(
                {
                    "field_index_owner_only": field_index,
                    "managed_offset_owner_only": offset + 16,
                    "field_data_offset_owner_only": offset,
                    "type_descriptor_owner_only": descriptor,
                    "runtime_type_enum": type_enum,
                    "wire_mask": wire_mask,
                    "name_owner_only": str(raw_field.get("name_owner_only", "")),
                }
            )

        if not normalized_fields:


            continue
        resolved = _strict_u32_list(source.get("resolved_numbers", []), "resolved_numbers")
        candidates = _strict_u32_list(source.get("candidate_numbers", []), "candidate_numbers")
        resolved_set = set(resolved)
        candidates = [number for number in candidates if number not in resolved_set]
        mode = source.get("candidate_mode")
        if mode not in {
            "oneof-enum-literals",
            "parser-evidence-tag-domain",
            "parser-exhaustion-audit",
            "static-assignment-evidence",
            "known-signed-scalar-audit",
            "serializer-current-runtime-observation",
            "runtime-parser-differential-scan",
        }:
            raise ValueError("field mutation candidate mode is not evidence-bound")
        mode_counts[str(mode)] = mode_counts.get(str(mode), 0) + 1
        scan_min = 0
        scan_max = 0
        if mode == "runtime-parser-differential-scan":
            scan_min = source.get("scan_min")
            scan_max = source.get("scan_max")
            if (
                type(scan_min) is not int or type(scan_max) is not int
                or not 1 <= scan_min <= scan_max <= 0x1FFFFFFF
                or scan_max - scan_min >= 4096
                or candidates != [
                    number for number in range(scan_min, scan_max + 1)
                    if number not in resolved_set
                ]
                or source.get("candidate_evidence_owner_only") not in (None, [])
            ):
                raise ValueError("runtime parser scan domain differs from explicit range")
        if not candidates and not serializer_differential:
            raise ValueError("explicit candidate message has no candidates")
        candidate_wires = (
            _parser_candidate_wires(source, candidates)
            if mode in {"parser-evidence-tag-domain", "parser-exhaustion-audit"}
            else {}
        )
        candidate_count = len(candidates)
        wire_count = sum(bool(message_wire_mask & (1 << wire)) for wire in (0, 1, 2, 5))
        expected_probes += (
            len(normalized_fields)
            if serializer_differential
            else candidate_count * wire_count
        )
        field_count += len(normalized_fields)
        normalized_messages.append(
            {
                "message_index_owner_only": message_index,
                "message": str(source.get("message", "")),
                "write_to_rva_owner_only": source.get("write_to_rva_owner_only"),
                "type_index_owner_only": type_index,
                "fields_owner_only": normalized_fields,
                "resolved_numbers": resolved,
                "candidate_mode": mode,
                "candidate_numbers": candidates,
                "candidate_wires_owner_only": candidate_wires,
                "scan_min": scan_min,
                "scan_max": scan_max,
                "wire_mask": message_wire_mask,
                "wire2_nonempty_payload": mode != "oneof-enum-literals",
            }
        )

    counts = plan.get("counts") if isinstance(plan.get("counts"), Mapping) else {}
    deferred_message_count = len(
        {
            str(row.get("message"))
            for row in deferred_fields
            if isinstance(row.get("message"), str) and row.get("message")
            and str(row.get("message"))
            not in {message["message"] for message in normalized_messages}
        }
    )
    if len(normalized_messages) + deferred_message_count != counts.get(
        "message_probe_count"
    ):
        raise ValueError("message probe count does not match the source plan")
    count_key = ("signed_scalar_field_count" if plan.get("purpose") == "signed-scalar-serializer-audit"
                 else "unresolved_field_count")
    if field_count + len(deferred_fields) != counts.get(count_key):
        raise ValueError("field probe count does not match the source plan")
    maximum_fields = max(
        (len(message["fields_owner_only"]) for message in normalized_messages),
        default=0,
    )
    if not expected_probes or not maximum_fields:
        raise ValueError("field mutation probe domain is empty")
    theoretical_result_bound = (
        field_count
        if serializer_differential
        else sum(
            len(message["fields_owner_only"])
            * len(message["candidate_numbers"])
            * sum(
                bool(message["wire_mask"] & (1 << wire))
                for wire in (WIRE_VARINT, WIRE_FIXED64, WIRE_LENGTH, WIRE_FIXED32)
            )
            for message in normalized_messages
        )
    )
    if not 0 < theoretical_result_bound <= ((1 << 63) - 1) // 96:
        raise ValueError("field mutation result capacity exceeds platform limits")
    return {
        "schema": NORMALIZED_SCHEMA,
        "status": "prepared",
        "target": dict(plan.get("target", {})),
        "counts": {
            "message_probe_count": len(normalized_messages),
            "field_probe_count": field_count,
            "expected_merge_probe_count": expected_probes,
            "maximum_fields_per_message": maximum_fields,
            "theoretical_result_bound": theoretical_result_bound,
            "result_capacity": theoretical_result_bound,
            "distinct_runtime_type_descriptor_count": len(observed_type_enums),
            "deferred_snapshot_unavailable_field_count": len(deferred_fields),
            "candidate_mode_counts": mode_counts,
        },
        "messages_owner_only": normalized_messages,
        "runtime_type_enums_owner_only": observed_type_enums,
        "deferred_unavailable_fields_owner_only": deferred_fields,
        "checks": {
            "source_plan_closed": True,
            "all_planned_field_descriptors_present_in_same_version_snapshot": True,
            "deferred_snapshot_unavailable_fields_recorded": all(
                isinstance(row, dict) and isinstance(row.get("reason"), str)
                for row in deferred_fields
            ),
            "all_runtime_type_enums_supported": True,
            "all_wire_masks_type_directed": True,
            "il2cpp_object_header_added_to_field_data_offsets": True,
            "known_field_numbers_excluded": True,
            "parser_candidate_tags_bound_to_current_parser_cases": True,
            "wire_two_payload_valid_for_string_bytes_message_and_packed_repeated": True,
            "write_to_contract_matches_plan": (
                bool(policy.get("write_to_used")) == serializer_plan
            ),
            "message_field_bound_closed": True,
            "result_capacity_covers_all_possible_probe_field_mutations": True,
        },
        "policy": {
            "merge_from_only": True,
            "write_to_used": False,
            "fresh_message_per_probe": True,
            "runtime_type_descriptor_revalidated_in_collector": False,
            "runtime_type_descriptor_requires_live_binding": True,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "saved_reference_generation_seed_used": False,
            "external_runtime_component_used": False,
            "implicit_full_protobuf_range_scan_used": False,
            "raw_pointers_owner_only": True,
        },
    }


def _semantic_operation(semantics: Mapping[str, Any], key: str) -> dict[str, int]:
    matches = [
        row
        for row in semantics.get("operations", [])
        if isinstance(row, Mapping)
        and row.get("key") == key
        and row.get("semantic_identity_resolved") is True
        and isinstance(row.get("method_pointer"), int)
        and isinstance(row.get("metadata_pointer"), int)
    ]
    if len(matches) != 1:
        raise AcquisitionError(
            f"runtime proto mutation semantic operation is unavailable: {key}"
        )
    return {
        "pointer": int(matches[0]["method_pointer"]),
        "metadata": int(matches[0]["metadata_pointer"]),
    }


def _bind_current_runtime(
    *,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    runtime_materializer_model: Path,
    roundtrip_binding: Mapping[str, Any] | None = None,
    _runtime_context: tuple | None = None,
) -> tuple[dict[str, Any], LiveRuntimeInventory]:
    runtime_binding = (
        _roundtrip_binding(
            native_output_receipt=native_output_receipt,
            proto_field_type_model=proto_field_type_model,
        )
        if roundtrip_binding is None else roundtrip_binding
    )
    if roundtrip_binding is not None and (
        runtime_binding.get("receipt") != file_identity(
            native_output_receipt.expanduser().resolve()
        )
        or runtime_binding.get("field_type_model") != file_identity(
            proto_field_type_model.expanduser().resolve()
        )
    ):
        raise AcquisitionError("cached runtime proto roundtrip binding is stale")
    _receipt, paths, runtime = (_runtime(native_output_receipt)
                              if _runtime_context is None else _runtime_context)
    live = LiveRuntimeInventory(
        materializer_model=runtime_materializer_model,
        binary=paths["binary"],
    )
    try:
        inventory = _proto_inventory_binding(native_output_receipt)
        semantics_path = _owner_file(
            Path(inventory["reflection_semantics"]["path"]),
            label="reflection semantics",
        )
        if file_identity(semantics_path) != inventory["reflection_semantics"]:
            raise AcquisitionError(
                "runtime proto mutation reflection semantics are stale"
            )
        semantics = read_json(semantics_path)
        if not isinstance(semantics, Mapping):
            raise AcquisitionError(
                "runtime proto mutation reflection semantics are invalid"
            )
        factory_source = runtime_binding.get("message_factory")
        extensions_source = runtime_binding.get("extensions")
        if not isinstance(factory_source, Mapping) or not isinstance(
            extensions_source, Mapping
        ):
            raise AcquisitionError("runtime proto mutation binding is incomplete")
        factory = rebind_method(runtime, live, factory_source)
        serializer = rebind_method(
            runtime,
            live,
            {
                "method_index": extensions_source.get("serializer_method_index"),
                "pointer": extensions_source.get("serializer_method_pointer"),
                "metadata": extensions_source.get("serializer_method_metadata"),
            },
        )
        merge = rebind_method(
            runtime,
            live,
            {
                "method_index": extensions_source.get("merge_method_index"),
                "pointer": extensions_source.get("merge_method_pointer"),
                "metadata": extensions_source.get("merge_method_metadata"),
            },
        )
        type_from_handle = rebind_method(
            runtime, live, _semantic_operation(semantics, "type.from_handle")
        )
        deltas = {
            factory["image_delta"],
            serializer["image_delta"],
            merge["image_delta"],
            type_from_handle["image_delta"],
        }
        if len(deltas) != 1:
            raise AcquisitionError("live runtime image rebasing is inconsistent")
        delta = deltas.pop()
        rebound_extensions = dict(extensions_source)
        rebound_extensions.update(
            {
                "serializer_method_index": serializer["method_index"],
                "serializer_method_pointer": serializer["pointer"],
                "serializer_method_metadata": serializer["metadata"],
                "merge_method_index": merge["method_index"],
                "merge_method_pointer": merge["pointer"],
                "merge_method_metadata": merge["metadata"],
            }
        )
        for key in (
            "serializer_array_new_pointer",
            "serializer_byte_array_class_slot",
            "serializer_object_new_pointer",
            "serializer_coded_output_class_slot",
        ):
            value = rebound_extensions.get(key)
            if isinstance(value, int) and value:
                rebound_extensions[key] = value + delta
        runtime_binding = dict(runtime_binding)
        runtime_binding["process_id"] = live.process_id
        runtime_binding["message_factory"] = factory
        runtime_binding["extensions"] = rebound_extensions
        runtime_binding["type_from_handle"] = type_from_handle
        runtime_binding["live_materializer"] = file_identity(
            runtime_materializer_model.expanduser().resolve()
        )
        runtime_binding["image_delta"] = delta
        return runtime_binding, live
    except Exception:
        live.close()
        raise


def _bind_probe_types(
    normalized: Mapping[str, Any], live: LiveRuntimeInventory
) -> dict[str, Any]:
    rebound = json.loads(json.dumps(normalized))
    messages = rebound.get("messages_owner_only")
    if not isinstance(messages, list):
        raise AcquisitionError("runtime proto mutation message domain is invalid")
    descriptors: set[int] = set()
    for message in messages:
        if not isinstance(message, dict):
            raise AcquisitionError("runtime proto mutation message row is invalid")
        type_index = message.get("type_index_owner_only")
        if not isinstance(type_index, int):
            raise AcquisitionError("runtime proto mutation type index is invalid")
        descriptor = live.type_row(type_index).embedded_descriptor(
            live.embedded_descriptor_byte_offset
        )
        message["type_descriptor_current_owner_only"] = descriptor
        descriptors.add(descriptor)
    rebound["counts"]["current_type_descriptor_count"] = len(descriptors)
    rebound["checks"]["all_message_types_rebound_to_current_runtime"] = True
    rebound["checks"]["no_saved_type_object_used"] = True
    rebound["policy"]["runtime_type_descriptor_revalidated_in_collector"] = True
    rebound["policy"]["runtime_type_descriptor_requires_live_binding"] = False
    rebound["policy"]["saved_type_object_used"] = False
    return rebound


def _c_u32(values: Sequence[int]) -> str:
    return ",".join(f"{value}u" for value in values) or "0u"


def _c_escape_wide(path: Path) -> str:
    value = _windows_z_path(path)
    return value.replace("\\", "\\\\").replace('"', '\\"')


def _flatten_probe(normalized: Mapping[str, Any]) -> tuple[list[dict[str, int]], list[dict[str, int]], list[int], list[int]]:
    messages: list[dict[str, int]] = []
    fields: list[dict[str, int]] = []
    candidates: list[int] = []
    resolved: list[int] = []
    for source in normalized["messages_owner_only"]:
        field_start = len(fields)
        for field in source["fields_owner_only"]:
            fields.append(
                {
                    "field_index": field["field_index_owner_only"],
                    "offset": field["managed_offset_owner_only"],
                    "type_enum": field["runtime_type_enum"],
                    "wire_mask": field["wire_mask"],
                }
            )
        candidate_start = len(candidates)
        candidates.extend(source["candidate_numbers"])
        resolved_start = len(resolved)
        resolved.extend(source["resolved_numbers"])
        messages.append(
            {
                "type_index": source["type_index_owner_only"],
                "field_start": field_start,
                "field_count": len(source["fields_owner_only"]),
                "candidate_start": candidate_start,
                "candidate_count": len(source["candidate_numbers"]),
                "resolved_start": resolved_start,
                "resolved_count": len(source["resolved_numbers"]),
                "scan_min": source["scan_min"],
                "scan_max": source["scan_max"],
                "wire_mask": source["wire_mask"],
                "wire2_nonempty": int(source["wire2_nonempty_payload"]),
                "type_descriptor": source[
                    "type_descriptor_current_owner_only"
                ],
            }
        )
    return messages, fields, candidates, resolved


def _require_int(mapping: Mapping[str, Any], key: str) -> int:
    value = mapping.get(key)
    if not isinstance(value, int) or not value:
        raise ValueError(f"binding is missing {key}")
    return value


def render_collector_c(
    normalized: Mapping[str, Any],
    *,
    runtime_binding: Mapping[str, Any],
    output_path: Path,
    status_path: Path,
) -> str:
    messages, fields, candidates, resolved = _flatten_probe(normalized)
    extensions = runtime_binding.get("extensions")
    if not isinstance(extensions, Mapping):
        raise ValueError("runtime binding lacks extension bindings")
    activator = runtime_binding.get("message_factory")
    if not isinstance(activator, Mapping):
        raise ValueError("runtime binding lacks the Activator factory")
    type_from_handle = runtime_binding.get("type_from_handle")
    if not isinstance(type_from_handle, Mapping):
        raise ValueError("runtime binding lacks Type.GetTypeFromHandle")
    executable_sha = str(normalized.get("target", {}).get("executable_sha256", ""))
    if len(executable_sha) != 64:
        raise ValueError("target executable digest is invalid")
    expected_pid = _require_int(runtime_binding, "process_id")
    merge_pointer = _require_int(extensions, "merge_method_pointer")
    merge_metadata = _require_int(extensions, "merge_method_metadata")
    array_new = _require_int(extensions, "serializer_array_new_pointer")
    byte_array_slot = _require_int(extensions, "serializer_byte_array_class_slot")
    activator_pointer = _require_int(activator, "pointer")
    activator_metadata = _require_int(activator, "metadata")
    type_from_handle_pointer = _require_int(type_from_handle, "pointer")
    type_from_handle_metadata = _require_int(type_from_handle, "metadata")
    expected_probes = normalized["counts"]["expected_merge_probe_count"]
    maximum_fields = normalized["counts"]["maximum_fields_per_message"]
    result_capacity = normalized["counts"]["result_capacity"]

    message_rows = ",\n".join(
        "    {%du,%du,%du,%du,%du,%du,%du,%du,%du,%du,%dull}"
        % (
            row["type_index"], row["field_start"], row["field_count"],
            row["candidate_start"], row["candidate_count"], row["resolved_start"],
            row["resolved_count"], row["scan_min"], row["scan_max"],
            row["wire2_nonempty"], row["type_descriptor"],
        )
        for row in messages
    )
    message_masks = _c_u32([row["wire_mask"] for row in messages])
    field_rows = ",\n".join(
        "    {%du,%du,%du,%du}"
        % (row["field_index"], row["offset"], row["type_enum"], row["wire_mask"])
        for row in fields
    )

    from alpha.p01 import GLOBALS, WINDOW_PROC, DISPATCH
    from alpha.p01 import GUARD, PROGRESS

    return f'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#define ALPHA_PROBE_BATCH 16u
#define ALPHA_MAX_FIELDS_PER_MESSAGE {maximum_fields}u
#define ALPHA_MAX_RESULTS {result_capacity}ull
#define ALPHA_REFERENCE_BYTES 96u
typedef struct probe_message{{uint32_t type_index,field_start,field_count,candidate_start,candidate_count;uint32_t resolved_start,resolved_count,scan_min,scan_max,wire2_nonempty;uint64_t type_descriptor;}}probe_message;
typedef struct probe_field{{uint32_t field_index,offset,type_enum,wire_mask;}}probe_field;
typedef struct field_snapshot{{uint64_t storage,root,class_pointer,storage_hash,reference_hash;}}field_snapshot;
typedef struct output_header{{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t result_count,completed_probes,expected_probes;uint64_t message_count,field_count;char executable_sha256[64];}}output_header;
typedef struct output_record{{uint32_t message_index,type_index,field_index,number;uint32_t wire,type_enum,flags,reserved;uint64_t before_root,after_root,before_class,after_class;uint64_t before_storage_hash,after_storage_hash;uint64_t before_reference_hash,after_reference_hash;}}output_record;
_Static_assert(sizeof(probe_message)==48,"probe message layout");
_Static_assert(sizeof(probe_field)==16,"probe field layout");
_Static_assert(sizeof(output_header)==128,"output header layout");
_Static_assert(sizeof(output_record)==96,"output record layout");
static const probe_message messages[]={{
{message_rows}
}};
static const uint32_t message_wire_masks[]={{{message_masks}}};
static const probe_field fields[]={{
{field_rows}
}};
static const uint32_t candidates[]={{{_c_u32(candidates)}}};
static const uint32_t resolved_numbers[]={{{_c_u32(resolved)}}};
static const uint32_t message_count={len(messages)}u,field_count={len(fields)}u;
static const uint64_t expected_probe_count={expected_probes}ull;
static const DWORD expected_pid={expected_pid}u;
static const char executable_sha256[]="{executable_sha}";
static const uintptr_t activator_pointer={activator_pointer}ull,activator_metadata={activator_metadata}ull;
static const uintptr_t type_from_handle_pointer={type_from_handle_pointer}ull,type_from_handle_metadata={type_from_handle_metadata}ull;
static const uintptr_t merge_pointer={merge_pointer}ull,merge_metadata={merge_metadata}ull;
static const uintptr_t array_new_pointer={array_new}ull,byte_array_class_slot={byte_array_slot}ull;
static const wchar_t output_path[]=L"{_c_escape_wide(output_path)}";
static const wchar_t status_path[]=L"{_c_escape_wide(status_path)}";
typedef uintptr_t(*static_onearg)(uintptr_t,uintptr_t);typedef uintptr_t(*twoarg_object)(uintptr_t,uintptr_t);typedef void(*static_twoarg_void)(uintptr_t,uintptr_t,uintptr_t);
static output_record results[ALPHA_MAX_RESULTS];static uint64_t result_count,completed_probes;static uint32_t message_cursor,candidate_cursor,wire_cursor;static uint32_t failure_kind,failure_message,failure_number,failure_wire;static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_complete;
{GLOBALS}
static int readable(uintptr_t value,SIZE_T bytes){{MEMORY_BASIC_INFORMATION r;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t end=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}}
static uint64_t hash_bytes(uint64_t h,const void*data,SIZE_T bytes){{const unsigned char*p=data;for(SIZE_T i=0;i<bytes;i++){{h^=p[i];h*=1099511628211ull;}}return h;}}
static SIZE_T storage_bytes(uint32_t t){{switch(t){{case 2:case 4:case 5:return 1u;case 3:case 6:case 7:return 2u;case 8:case 9:case 12:case 17:return 4u;default:return 8u;}}}}
static int reference_type(uint32_t t){{return t==14u||t==18u||t==21u||t==28u||t==29u;}}
static int take_snapshot(uintptr_t message,const probe_field*f,field_snapshot*out){{memset(out,0,sizeof(*out));uintptr_t address=message+f->offset;SIZE_T bytes=storage_bytes(f->type_enum);if(!readable(address,bytes))return 0;memcpy(&out->storage,(const void*)address,bytes);out->storage_hash=hash_bytes(1469598103934665603ull,(const void*)address,bytes);if(!reference_type(f->type_enum))return 1;out->root=out->storage;if(!out->root)return 1;if(!readable(out->root,8u))return 0;memcpy(&out->class_pointer,(const void*)out->root,8u);SIZE_T root_bytes=ALPHA_REFERENCE_BYTES;if(!readable(out->root,root_bytes)){{root_bytes=16u;if(!readable(out->root,root_bytes))return 0;}}uint64_t h=hash_bytes(1469598103934665603ull,(const void*)out->root,root_bytes);for(SIZE_T offset=16u;offset<=32u;offset+=8u){{uintptr_t child=0,child_class=0;memcpy(&child,(const void*)(out->root+offset),8u);if(!readable(child,64u))continue;memcpy(&child_class,(const void*)child,8u);if(!readable(child_class,64u))continue;h=hash_bytes(h,(const void*)child,64u);}}out->reference_hash=h;return 1;}}
static int same_snapshot(const field_snapshot*a,const field_snapshot*b){{return a->storage==b->storage&&a->root==b->root&&a->class_pointer==b->class_pointer&&a->storage_hash==b->storage_hash&&a->reference_hash==b->reference_hash;}}
static SIZE_T put_varint(unsigned char*out,uint64_t value){{SIZE_T n=0;do{{unsigned char byte=(unsigned char)(value&0x7fu);value>>=7;if(value)byte|=0x80u;out[n++]=byte;}}while(value);return n;}}
static SIZE_T make_payload(uint32_t number,uint32_t wire,uint32_t wire2_nonempty,unsigned char out[32]){{SIZE_T n=put_varint(out,((uint64_t)number<<3)|wire);if(wire==0u)out[n++]=1u;else if(wire==1u){{memset(out+n,0,8u);out[n]=1u;n+=8u;}}else if(wire==2u){{if(!wire2_nonempty)out[n++]=0u;else{{out[n++]=8u;for(unsigned i=0;i<4u;i++){{out[n++]=0x08u;out[n++]=0x01u;}}}}}}else if(wire==5u){{memset(out+n,0,4u);out[n]=1u;n+=4u;}}else return 0;return n;}}
static int is_resolved(const probe_message*m,uint32_t number){{for(uint32_t i=0;i<m->resolved_count;i++)if(resolved_numbers[m->resolved_start+i]==number)return 1;return 0;}}
static int current_number(const probe_message*m,uint32_t*out){{if(!m->candidate_count||candidate_cursor>=m->candidate_count)return 0;*out=candidates[m->candidate_start+candidate_cursor];return 1;}}
static int next_probe(uint32_t*mi,uint32_t*number,uint32_t*wire){{static const uint32_t wires[4]={{0u,1u,2u,5u}};while(message_cursor<message_count){{const probe_message*m=&messages[message_cursor];uint32_t value=0;if(!current_number(m,&value)){{message_cursor++;candidate_cursor=0;wire_cursor=0;continue;}}if(is_resolved(m,value)){{candidate_cursor++;wire_cursor=0;continue;}}while(wire_cursor<4u){{uint32_t selected=wires[wire_cursor++];if(message_wire_masks[message_cursor]&(1u<<selected)){{*mi=message_cursor;*number=value;*wire=selected;return 1;}}}}candidate_cursor++;wire_cursor=0;}}return 0;}}
static int append_result(uint32_t mi,const probe_field*f,uint32_t number,uint32_t wire,const field_snapshot*before,const field_snapshot*after){{for(uint64_t i=0;i<result_count;i++)if(results[i].message_index==mi&&results[i].field_index==f->field_index&&results[i].number==number&&results[i].wire==wire)return 1;if(result_count>=ALPHA_MAX_RESULTS)return 0;const probe_message*m=&messages[mi];output_record*r=&results[result_count++];memset(r,0,sizeof(*r));r->message_index=mi;r->type_index=m->type_index;r->field_index=f->field_index;r->number=number;r->wire=wire;r->type_enum=f->type_enum;r->flags=(before->root!=after->root?1u:0u)|(before->class_pointer!=after->class_pointer?2u:0u)|(before->reference_hash!=after->reference_hash?4u:0u);r->before_root=before->root;r->after_root=after->root;r->before_class=before->class_pointer;r->after_class=after->class_pointer;r->before_storage_hash=before->storage_hash;r->after_storage_hash=after->storage_hash;r->before_reference_hash=before->reference_hash;r->after_reference_hash=after->reference_hash;return 1;}}
static int run_one_probe(uint32_t mi,uint32_t number,uint32_t wire){{InterlockedExchange(&probe_phase,1);const probe_message*m=&messages[mi];if(m->field_count>ALPHA_MAX_FIELDS_PER_MESSAGE)return failure_kind=1,0;if(!readable(m->type_descriptor,16u))return failure_kind=2,0;static_onearg get_type=(static_onearg)type_from_handle_pointer;InterlockedExchange(&probe_phase,2);uintptr_t type_object=get_type(m->type_descriptor,type_from_handle_metadata);if(!type_object)return failure_kind=3,0;static_onearg create=(static_onearg)activator_pointer;InterlockedExchange(&probe_phase,3);uintptr_t message=create(type_object,activator_metadata);if(!message)return failure_kind=4,0;InterlockedExchange(&probe_phase,4);field_snapshot before[ALPHA_MAX_FIELDS_PER_MESSAGE],after[ALPHA_MAX_FIELDS_PER_MESSAGE];for(uint32_t i=0;i<m->field_count;i++)if(!take_snapshot(message,&fields[m->field_start+i],&before[i]))return failure_kind=5,0;unsigned char payload[32];SIZE_T payload_bytes=make_payload(number,wire,m->wire2_nonempty,payload);if(!payload_bytes)return failure_kind=6,0;uintptr_t byte_array_class=0;if(!readable(byte_array_class_slot,8u))return failure_kind=7,0;memcpy(&byte_array_class,(const void*)byte_array_class_slot,8u);if(!byte_array_class)return failure_kind=8,0;twoarg_object array_new=(twoarg_object)array_new_pointer;InterlockedExchange(&probe_phase,5);uintptr_t input=array_new(byte_array_class,payload_bytes);if(!input||!readable(input,0x20u+payload_bytes))return failure_kind=9,0;uint64_t observed_length=0;memcpy(&observed_length,(const void*)(input+0x18u),8u);if(observed_length!=payload_bytes)return failure_kind=10,0;memcpy((void*)(input+0x20u),payload,payload_bytes);static_twoarg_void merge=(static_twoarg_void)merge_pointer;InterlockedExchange(&probe_phase,6);merge(message,input,merge_metadata);InterlockedExchange(&probe_phase,7);for(uint32_t i=0;i<m->field_count;i++){{const probe_field*f=&fields[m->field_start+i];if(!take_snapshot(message,f,&after[i]))return failure_kind=11,0;if(!same_snapshot(&before[i],&after[i])&&!append_result(mi,f,number,wire,&before[i],&after[i]))return failure_kind=12,0;}}return 1;}}
static int capture_batch(void){{for(uint32_t i=0;i<ALPHA_PROBE_BATCH;i++){{uint32_t mi=0,number=0,wire=0;if(!next_probe(&mi,&number,&wire))return 1;failure_message=mi;failure_number=number;failure_wire=wire;if(!run_one_probe(mi,number,wire))return 0;completed_probes++;}}return 1;}}
{GUARD}
{WINDOW_PROC}
{PROGRESS}
typedef struct selection{{DWORD pid;HWND window;uint32_t count;}}selection;
static BOOL CALLBACK select_window(HWND w,LPARAM value){{selection*s=(selection*)(uintptr_t)value;DWORD pid=0;RECT bounds;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&bounds)||bounds.right<=bounds.left||bounds.bottom<=bounds.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){{s->window=w;s->count++;}}return TRUE;}}
{DISPATCH}
static void digest_hex(const unsigned char d[32],char o[65]){{static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){{o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}}o[64]=0;}}
static int sha256_file(const wchar_t*path,char output[65]){{HANDLE f=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL,*buffer=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,os);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(a,&h,object,os,NULL,0,0)<0)ok=0;while(ok){{DWORD n=0;if(!ReadFile(f,buffer,1048576u,&n,NULL)){{ok=0;break;}}if(!n)break;if(BCryptHashData(h,buffer,n,0)<0)ok=0;}}if(ok&&BCryptFinishHash(h,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,output);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(f);return ok;}}
static int executable_identity(char output[65]){{wchar_t path[32768];DWORD n=GetModuleFileNameW(NULL,path,(DWORD)(sizeof(path)/sizeof(path[0])));return n&&n<sizeof(path)/sizeof(path[0])&&sha256_file(path,output);}}
static int write_output(void){{output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"ALPHAPM1",8);h.version=1;h.header_bytes=sizeof(h);h.record_bytes=sizeof(output_record);h.result_count=result_count;h.completed_probes=completed_probes;h.expected_probes=expected_probe_count;h.message_count=message_count;h.field_count=field_count;memcpy(h.executable_sha256,executable_sha256,64);FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;int ok=fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(results,sizeof(*results),result_count,f)==result_count;if(fclose(f))ok=0;if(!ok)_wremove(output_path);else _wchmod(output_path,0600);return ok;}}
static void write_status(const char*status,int written){{FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{{\\n  \\\"schema\\\": \\\"alpha.runtime-proto-field-mutation-status/v1\\\",\\n  \\\"status\\\": \\\"%s\\\",\\n  \\\"process_id\\\": %lu,\\n  \\\"completed_probe_count\\\": %llu,\\n  \\\"expected_probe_count\\\": %llu,\\n  \\\"result_count\\\": %llu,\\n  \\\"failure_kind_owner_only\\\": %u,\\n  \\\"failure_message_owner_only\\\": %u,\\n  \\\"failure_number_owner_only\\\": %u,\\n  \\\"failure_wire_owner_only\\\": %u,\\n  \\\"output_written\\\": %s,\\n  \\\"fresh_runtime_observation\\\": true,\\n  \\\"runtime_type_descriptor_revalidated\\\": true,\\n  \\\"write_to_used\\\": false,\\n  \\\"saved_reference_generation_seed_used\\\": false,\\n  \\\"fixed_address_used\\\": false,\\n  \\\"fixed_offset_used\\\": false,\\n  \\\"external_runtime_component_used\\\": false\\n}}\\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)completed_probes,(unsigned long long)expected_probe_count,(unsigned long long)result_count,failure_kind,failure_message,failure_number,failure_wire,written?"true":"false");fclose(f);_wchmod(status_path,0600);}}
static DWORD WINAPI worker(LPVOID unused){{(void)unused;_wremove(output_path);_wremove(status_path);char digest[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(digest)||strcmp(digest,executable_sha256)){{failure_kind=100;write_status("identity_mismatch",0);return 0;}}int ok=dispatch();if(!ok){{write_status("capture_failed",0);return 0;}}if(completed_probes!=expected_probe_count){{failure_kind=101;write_status("probe_domain_mismatch",0);return 0;}}ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){{(void)reserved;if(reason==DLL_PROCESS_ATTACH){{DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}}return TRUE;}}
'''


def _private_binding(runtime_binding: Mapping[str, Any]) -> dict[str, Any]:
    extensions = runtime_binding.get("extensions")
    factory = runtime_binding.get("message_factory")
    type_from_handle = runtime_binding.get("type_from_handle")
    binary = runtime_binding.get("binary")
    if not all(
        isinstance(value, Mapping)
        for value in (extensions, factory, type_from_handle, binary)
    ):
        raise AcquisitionError("runtime proto mutation binding is incomplete")
    return {
        "process_id": _require_int(runtime_binding, "process_id"),
        "message_factory_owner_only": {
            "method_index": _require_int(factory, "method_index"),
            "pointer": _require_int(factory, "pointer"),
            "metadata": _require_int(factory, "metadata"),
        },
        "type_from_handle_owner_only": {
            "method_index": _require_int(type_from_handle, "method_index"),
            "pointer": _require_int(type_from_handle, "pointer"),
            "metadata": _require_int(type_from_handle, "metadata"),
        },
        "extensions_owner_only": {
            key: _require_int(extensions, key)
            for key in (
                "merge_method_index",
                "merge_method_pointer",
                "merge_method_metadata",
                "serializer_array_new_pointer",
                "serializer_byte_array_class_slot",
            )
        },
    }


def prepare_runtime_proto_field_mutations(
    *,
    mutation_plan: Path,
    snapshot: Path,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    runtime_materializer_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    mutation_plan = _owner_file(mutation_plan, label="plan")
    snapshot = _owner_file(snapshot, label="snapshot")
    native_output_receipt = _owner_file(
        native_output_receipt, label="native-output receipt"
    )
    proto_field_type_model = _owner_file(
        proto_field_type_model, label="field-type model"
    )
    runtime_materializer_model = _owner_file(
        runtime_materializer_model, label="runtime materializer model"
    )
    source_plan = _load_json(mutation_plan)
    try:
        with RuntimeSnapshot(snapshot) as memory:
            normalized = normalize_plan(source_plan, memory)
    except (KeyError, OSError, ValueError, struct.error) as error:
        raise AcquisitionError(
            f"runtime proto field mutation plan normalization failed: {error}"
        ) from error
    runtime_binding, live = _bind_current_runtime(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        runtime_materializer_model=runtime_materializer_model,
    )
    try:
        normalized = _bind_probe_types(normalized, live)
    finally:
        live.close()
    binary = runtime_binding.get("binary")
    if (
        not isinstance(binary, Mapping)
        or normalized.get("target", {}).get("executable_sha256")
        != binary.get("sha256")
    ):
        raise AcquisitionError(
            "runtime proto field mutation inputs target different executables"
        )

    output = output_dir / "runtime-proto-field-mutations.private.bin"
    status = output_dir / "runtime-proto-field-mutations-status.private.json"
    plan_path = output_dir / "runtime-proto-field-mutation-build-plan.private.json"
    probe_path = output_dir / "runtime-proto-field-mutation-probe.private.json"
    build_dir = _owner_directory(
        output_dir / "build-runtime-proto-field-mutations"
    )
    source_path = build_dir / "runtime-proto-field-mutations.c"
    injector_source = build_dir / "runtime-proto-field-mutations-injector.c"
    for stale in (output, status):
        stale.unlink(missing_ok=True)
    _private_json(probe_path, normalized)
    from alpha.p01 import harden_snapshot_reads
    _private_text(
        source_path,
        harden_snapshot_reads(render_collector_c(
            normalized,
            runtime_binding=runtime_binding,
            output_path=output,
            status_path=status,
        )),
    )
    _private_text(injector_source, runtime_injector_source())
    collector = build_dir / (
        "alpha-runtime-proto-field-mutations-"
        + file_identity(source_path)["sha256"][:12]
        + ".dll"
    )
    injector = build_dir / "alpha-runtime-proto-field-mutations-injector.exe"
    cc = _compiler(compiler)
    _build(
        [
            str(cc),
            "-O2",
            "-s",
            "-shared",
            "-Wall",
            "-Wextra",
            "-Wformat=2",
            "-Werror",
            str(source_path),
            "-o",
            str(collector),
            "-lbcrypt",
        ],
        label="runtime proto field mutation collector",
    )
    _build(
        [
            str(cc),
            "-O2",
            "-s",
            "-municode",
            "-Wall",
            "-Wextra",
            "-Wformat=2",
            "-Werror",
            str(injector_source),
            "-o",
            str(injector),
        ],
        label="runtime proto field mutation injector",
    )
    for artifact in (collector, injector):
        artifact.chmod(0o600)

    checks = {
        **normalized["checks"],
        "target_identity_matches_current_runtime_binding": True,
        "activator_factory_structurally_unique": True,
        "merge_from_structurally_unique": True,
        "all_runtime_addresses_rebound_from_current_process_inventory": True,
        "saved_type_object_absent_from_collector": True,
        "collector_compiles_without_warnings": True,
        "write_to_not_called": True,
    }
    policy = {
        **normalized["policy"],
        "runtime_merge_from_used": True,
        "runtime_write_to_used": False,
        "runtime_roles_structurally_derived": True,
        "current_runtime_inventory_required": True,
    }
    build_plan = {
        "schema": BUILD_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": binary["path"],
            "executable_sha256": binary["sha256"],
            "process_id": runtime_binding["process_id"],
        },
        "inputs": {
            "mutation_plan": file_identity(mutation_plan),
            "snapshot": file_identity(snapshot),
            "native_output_receipt": file_identity(native_output_receipt),
            "proto_field_type_model": file_identity(proto_field_type_model),
            "runtime_materializer_model": file_identity(
                runtime_materializer_model
            ),
        },
        "probe": file_identity(probe_path),
        "binding_owner_only": _private_binding(runtime_binding),
        "source": file_identity(source_path),
        "collector": file_identity(collector),
        "injector": file_identity(injector),
        "output_path": str(output),
        "status_path": str(status),
        "counts": normalized["counts"],
        "checks": checks,
        "policy": policy,
    }
    _private_json(plan_path, build_plan)
    return {
        "schema": BUILD_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binary["sha256"]},
        "counts": normalized["counts"],
        "checks": checks,
        "policy": policy,
    }


def _candidate_allowed(message: Mapping[str, Any], number: int) -> bool:
    if number in message["resolved_numbers"]:
        return False
    return number in message["candidate_numbers"]


def _validate_mutation_output(
    build_plan: Mapping[str, Any],
    normalized: Mapping[str, Any],
    status: Mapping[str, Any],
) -> dict[str, Any]:
    output = _owner_file(Path(build_plan["output_path"]), label="output")
    raw = output.read_bytes()
    if len(raw) < OUTPUT_HEADER.size:
        raise AcquisitionError("runtime proto field mutation output is truncated")
    header = OUTPUT_HEADER.unpack_from(raw)
    (
        magic,
        version,
        header_bytes,
        record_bytes,
        reserved,
        result_count,
        completed_probes,
        expected_probes,
        message_count,
        field_count,
        executable_sha,
    ) = header
    expected_counts = normalized["counts"]
    expected_size = OUTPUT_HEADER.size + result_count * OUTPUT_RECORD.size
    envelope_checks = {
        "status_complete": status.get("status") == "complete",
        "status_schema_matches": status.get("schema") == STATUS_SCHEMA,
        "header_identity_matches": (
            magic == OUTPUT_MAGIC
            and version == OUTPUT_VERSION
            and header_bytes == OUTPUT_HEADER.size
            and record_bytes == OUTPUT_RECORD.size
            and reserved == 0
            and executable_sha.decode("ascii")
            == build_plan["target"]["executable_sha256"]
        ),
        "record_envelope_closes": expected_size == len(raw),
        "probe_domain_complete": (
            completed_probes == expected_probes
            == expected_counts["expected_merge_probe_count"]
            == status.get("completed_probe_count")
            == status.get("expected_probe_count")
        ),
        "result_count_matches_status": result_count == status.get("result_count"),
        "message_count_matches_plan": (
            message_count == expected_counts["message_probe_count"]
        ),
        "field_count_matches_plan": field_count == expected_counts["field_probe_count"],
        "fresh_runtime_observation": (
            status.get("fresh_runtime_observation") is True
        ),
        "runtime_type_descriptor_revalidated": (
            status.get("runtime_type_descriptor_revalidated") is True
        ),
        "write_to_absent": status.get("write_to_used") is False,
        "saved_reference_generation_seed_absent": (
            status.get("saved_reference_generation_seed_used") is False
        ),
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": (
            status.get("external_runtime_component_used") is False
        ),
    }
    if not all(envelope_checks.values()):
        raise AcquisitionError(
            "runtime proto field mutation envelope failed: "
            + ", ".join(
                sorted(key for key, value in envelope_checks.items() if not value)
            )
        )

    messages = normalized["messages_owner_only"]
    observations: list[dict[str, Any]] = []
    incompatible_observations: list[dict[str, Any]] = []
    seen: set[tuple[int, int, int, int]] = set()
    groups: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for index in range(result_count):
        values = OUTPUT_RECORD.unpack_from(
            raw, OUTPUT_HEADER.size + index * OUTPUT_RECORD.size
        )
        (
            message_index,
            type_index,
            field_index,
            number,
            wire,
            type_enum,
            flags,
            row_reserved,
            before_root,
            after_root,
            before_class,
            after_class,
            before_storage_hash,
            after_storage_hash,
            before_reference_hash,
            after_reference_hash,
        ) = values
        if message_index >= len(messages):
            raise AcquisitionError("runtime proto mutation message index is invalid")
        message = messages[message_index]
        field = next(
            (
                item
                for item in message["fields_owner_only"]
                if item["field_index_owner_only"] == field_index
            ),
            None,
        )
        key = (message_index, field_index, number, wire)
        expected_flags = (
            (1 if before_root != after_root else 0)
            | (2 if before_class != after_class else 0)
            | (4 if before_reference_hash != after_reference_hash else 0)
        )
        changed = (
            before_root != after_root
            or before_class != after_class
            or before_storage_hash != after_storage_hash
            or before_reference_hash != after_reference_hash
        )
        wire_compatible = bool(
            field is not None and field["wire_mask"] & (1 << wire)
        )
        parser_evidence_wire = message["candidate_wires_owner_only"].get(number)
        if (
            field is None
            or type_index != message["type_index_owner_only"]
            or type_enum != field["runtime_type_enum"]
            or wire not in (0, 1, 2, 5)
            or not _candidate_allowed(message, number)
            or (
                parser_evidence_wire is not None
                and wire != parser_evidence_wire
            )
            or row_reserved
            or flags != expected_flags
            or key in seen
            or not changed
        ):
            raise AcquisitionError(
                f"runtime proto mutation record {index} violates its probe domain"
            )
        seen.add(key)
        observation = {
            "message_index_owner_only": message_index,
            "message": message["message"],
            "type_index_owner_only": type_index,
            "field_index_owner_only": field_index,
            "field_name_owner_only": field["name_owner_only"],
            "field_number": number,
            "wire": wire,
            "runtime_type_enum": type_enum,
            "wire_compatible_with_field_type": wire_compatible,
            "flags": flags,
            "before_root_owner_only": before_root,
            "after_root_owner_only": after_root,
            "before_class_owner_only": before_class,
            "after_class_owner_only": after_class,
            "before_storage_hash_owner_only": before_storage_hash,
            "after_storage_hash_owner_only": after_storage_hash,
            "before_reference_hash_owner_only": before_reference_hash,
            "after_reference_hash_owner_only": after_reference_hash,
        }
        observations.append(observation)
        if wire_compatible:
            groups.setdefault((message_index, field_index), []).append(
                observation
            )
        else:
            incompatible_observations.append(observation)

    assignments: list[dict[str, Any]] = []
    ambiguous_fields: list[dict[str, Any]] = []
    all_field_keys: set[tuple[int, int]] = set()
    for message_index, message in enumerate(messages):
        for field in message["fields_owner_only"]:
            key = (message_index, field["field_index_owner_only"])
            all_field_keys.add(key)
            rows = groups.get(key, [])
            numbers = sorted({row["field_number"] for row in rows})
            item = {
                "message_index_owner_only": message_index,
                "message": message["message"],
                "type_index_owner_only": message["type_index_owner_only"],
                "field_index_owner_only": field["field_index_owner_only"],
                "field_name_owner_only": field["name_owner_only"],
                "runtime_type_enum": field["runtime_type_enum"],
                "field_numbers": numbers,
                "wires": sorted({row["wire"] for row in rows}),
                "after_classes_owner_only": sorted(
                    {
                        row["after_class_owner_only"]
                        for row in rows
                        if row["after_class_owner_only"]
                    }
                ),
            }
            if len(numbers) == 1:
                item["field_number"] = numbers[0]
                assignments.append(item)
            elif len(numbers) > 1:
                ambiguous_fields.append(item)
    observed_keys = set(groups)
    unmutated = sorted(all_field_keys - observed_keys)
    checks = {
        **envelope_checks,
        "all_records_match_planned_coordinates": True,
        "all_records_are_actual_mutations": True,
        "all_records_unique": True,
        "all_field_numbers_within_candidate_domain": True,
        "parser_case_wires_match_runtime_mutations": True,
        "type_incompatible_side_effects_excluded_from_assignments": True,
        "result_capacity_covers_observed_mutations": (
            result_count <= int(build_plan["counts"]["result_capacity"])
        ),
    }
    return {
        "schema": RESULT_SCHEMA,
        "status": "runtime-validated",
        "target": {
            "executable_sha256": build_plan["target"]["executable_sha256"]
        },
        "counts": {
            "completed_probe_count": completed_probes,
            "result_count": result_count,
            "type_compatible_result_count": result_count
            - len(incompatible_observations),
            "type_incompatible_side_effect_count": len(
                incompatible_observations
            ),
            "observed_field_count": len(observed_keys),
            "unique_assignment_count": len(assignments),
            "ambiguous_field_count": len(ambiguous_fields),
            "unmutated_field_count": len(unmutated),
        },
        "assignments_owner_only": assignments,
        "ambiguous_fields_owner_only": ambiguous_fields,
        "unmutated_fields_owner_only": [
            {
                "message_index_owner_only": message_index,
                "field_index_owner_only": field_index,
            }
            for message_index, field_index in unmutated
        ],
        "observations_owner_only": observations,
        "type_incompatible_side_effects_owner_only": incompatible_observations,
        "inventory": file_identity(output),
        "status_receipt": file_identity(Path(build_plan["status_path"])),
        "inputs": build_plan["inputs"],
        "probe": build_plan["probe"],
        "collector_source": build_plan["source"],
        "plan_checks": build_plan["checks"],
        "checks": checks,
        "policy": build_plan["policy"],
        "owner_only": True,
    }


def validate_captured_runtime_proto_field_mutations(
    *, output_dir: Path
) -> dict[str, Any]:

    output_dir = _owner_directory(output_dir)
    build_plan_path = _owner_file(
        output_dir / "runtime-proto-field-mutation-build-plan.private.json",
        label="build plan",
    )
    build_plan = read_json(build_plan_path)
    if (
        not isinstance(build_plan, Mapping)
        or build_plan.get("schema") != BUILD_PLAN_SCHEMA
        or build_plan.get("status") != "prepared"
    ):
        raise AcquisitionError("runtime proto mutation build plan is invalid")
    probe_record = build_plan.get("probe")
    if not isinstance(probe_record, Mapping) or not isinstance(
        probe_record.get("path"), str
    ):
        raise AcquisitionError("runtime proto mutation probe binding is invalid")
    probe_path = _owner_file(Path(probe_record["path"]), label="probe")
    if file_identity(probe_path) != probe_record:
        raise AcquisitionError("runtime proto mutation probe binding is stale")
    status_path = _owner_file(
        Path(build_plan["status_path"]), label="status"
    )
    status = read_json(status_path)
    if not isinstance(status, Mapping) or status.get("status") != "complete":
        raise AcquisitionError("runtime proto mutation capture is not complete")
    result = _validate_mutation_output(
        build_plan, read_json(probe_path), status
    )
    result_path = output_dir / "runtime-proto-field-mutations.private.json"
    _private_json(result_path, result)
    return {
        "schema": RESULT_SCHEMA,
        "status": result["status"],
        "target": result["target"],
        "counts": result["counts"],
        "checks": result["checks"],
        "policy": result["policy"],
        "model": file_identity(result_path),
    }


def capture_runtime_proto_field_mutations(
    *,
    mutation_plan: Path,
    snapshot: Path,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    runtime_materializer_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 1800.0,
    process_check: Callable[[], None] | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_proto_field_mutations(
        mutation_plan=mutation_plan,
        snapshot=snapshot,
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        runtime_materializer_model=runtime_materializer_model,
        output_dir=output_dir,
        compiler=compiler,
    )
    build_plan = read_json(
        output_dir / "runtime-proto-field-mutation-build-plan.private.json"
    )
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine.expanduser().resolve()), Path(build_plan['injector']['path']), Path(build_plan['collector']['path']), Path(build_plan['target']['executable_path']).name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "runtime proto field mutation injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-proto-field-mutation-injector.private.log",
        json.dumps(
            {
                "returncode": injected.returncode,
                "stdout": injected.stdout,
                "stderr": injected.stderr,
            },
            ensure_ascii=False,
            indent=2,
        )
        + "\n",
    )
    if injected.returncode:
        raise AcquisitionError("runtime proto field mutation injection failed")
    status_path = Path(build_plan["status_path"])
    deadline = time.monotonic() + timeout
    status: dict[str, Any] | None = None
    next_process_check = time.monotonic()
    while time.monotonic() < deadline:
        if status_path.is_file():
            candidate = read_json(status_path)
            if isinstance(candidate, dict) and candidate.get("status"):
                status = candidate
                break
        if process_check is not None and time.monotonic() >= next_process_check:
            process_check()
            next_process_check = time.monotonic() + 30.0
        time.sleep(0.2)
    if status is None:
        raise AcquisitionError("runtime proto field mutation capture timed out")
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime proto field mutation capture failed "
            f"(kind={status.get('failure_kind_owner_only')}, "
            f"message={status.get('failure_message_owner_only')}, "
            f"number={status.get('failure_number_owner_only')}, "
            f"wire={status.get('failure_wire_owner_only')})"
        )
    _seal_runtime_output(Path(build_plan["output_path"]))
    normalized = read_json(Path(build_plan["probe"]["path"]))
    result = _validate_mutation_output(build_plan, normalized, status)
    result_path = output_dir / "runtime-proto-field-mutations.private.json"
    _private_json(result_path, result)
    return {
        "schema": RESULT_SCHEMA,
        "status": result["status"],
        "target": result["target"],
        "counts": result["counts"],
        "inventory": file_identity(result_path),
        "checks": result["checks"],
        "policy": result["policy"],
    }
