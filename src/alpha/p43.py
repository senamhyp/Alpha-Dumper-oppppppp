from alpha.h02 import windows_run as _host_run

import copy
import json
import os
import re
import secrets
import stat
import struct
import subprocess
import time
from pathlib import Path
from typing import Any, Mapping

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.c06 import rebind_method
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER
from alpha.p33 import _text
from alpha.p29 import _runtime
from alpha.p38 import RUNTIME_PROTO_FIELD_TYPE_HEADER, RUNTIME_PROTO_FIELD_TYPE_MAGIC, RUNTIME_PROTO_FIELD_TYPE_RECORD, RUNTIME_PROTO_FIELD_TYPE_VERSION, _binding as _proto_inventory_binding
from alpha.p41 import RuntimeSnapshot, _bind_current_runtime, _c_escape_wide, _semantic_operation
from alpha.p40 import _roundtrip_binding
from alpha.p01 import SIGNED, role_inventory
from alpha.p25 import TYPE_REFERENCE_ARRAY, TYPE_REFERENCE_GENERIC_PARAMETER
from alpha.p20 import observed_generic_parts
from alpha.h02 import file_identity, read_json, read_private_model


PLAN_SCHEMA = "alpha.runtime-proto-signed-parse-plan/v1"
STATUS_SCHEMA = "alpha.runtime-proto-signed-parse-status/v1"
RESULT_SCHEMA = "alpha.runtime-proto-signed-parse-capture/v1"
EVIDENCE_SCHEMA = "alpha.runtime-proto-signed-parse-evidence/v1"
FIELD_TRANSFORM_RESULT_SCHEMA = "alpha.runtime-proto-field-transform-probe/v3"
UNSIGNED = {"uint32": 32, "fixed32": 32, "uint64": 64, "fixed64": 64}
UNSIGNED_EVIDENCE_SCHEMA = "alpha.runtime-proto-unsigned-wire-evidence/v1"
MAGIC = b"ALPHASP1"
VERSION = 1
HEADER = struct.Struct("<8sIIIIQQ64s")
RECORD = struct.Struct("<IIIIqqQQ")
ENCODING_CODE = {
    "int32": 1,
    "sint32": 2,
    "sfixed32": 3,
    "int64": 4,
    "sint64": 5,
    "sfixed64": 6,
}
ROLE_KIND = {"singular": 1, "repeated": 2, "map-key": 3,
             "map-value": 4, "oneof": 5}


IEEE_NEGATIVE_ZERO_BITS = {"float": 1 << 31, "double": 1 << 63}


RUNTIME_SIGNED_PARSE_BATCH_ROWS = 16
RUNTIME_SIGNED_PARSE_SEND_TIMEOUT_MS = 240000


WRITER_TERMINATION_FAILURE_KIND = 118


def writer_probe_value(encoding: str, bits: int) -> int:
    zero = IEEE_NEGATIVE_ZERO_BITS.get(encoding)
    if zero is None or bits != zero:
        return bits
    return bits | 1


def _encoding_candidates(width: int, *, unsigned: bool = False) -> tuple[str, ...]:

    if width not in (32, 64):
        raise AcquisitionError("runtime signed parse CLR width is invalid")
    if unsigned:
        return (f"uint{width}", f"fixed{width}")
    return (f"int{width}", f"sint{width}", f"sfixed{width}")


def _repeated_parse_contexts(
    source_packed: bool, *, unsigned_encoding_audit: bool = False
) -> list[dict[str, Any]]:


    return [{
        "packed": input_packed if unsigned_encoding_audit else source_packed,
        "source_packed": source_packed,
        "input_packed": input_packed,
        "key_type": None,
        "key_text_hex": "",
    } for input_packed in ((False, True) if unsigned_encoding_audit else (False,))]


def _observation_strategies(
    cardinality: str, role: str, encodings: tuple[str, ...]
) -> tuple[tuple[int, tuple[str, ...]], ...]:

    if cardinality == "repeated":
        return ((0, encodings), (6, encodings), (1, encodings))
    if cardinality == "map" and role == "value_type":
        return ((0, encodings), (7, encodings), (3, encodings))
    if cardinality == "singular":
        return ((0, encodings), (2, encodings))
    return ((0, encodings),)


def _baseline_writer_strategy(strategy: int) -> int:
    return {1: 6, 3: 7, 4: 8}.get(strategy, strategy)


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime signed parse {label} is not owner-only")
    return path


def _varint(value: int) -> bytes:
    value &= (1 << 64) - 1
    output = bytearray()
    while value >= 0x80:
        output.append((value & 0x7f) | 0x80)
        value >>= 7
    output.append(value)
    return bytes(output)


def _scalar(encoding: str, value: int) -> tuple[int, bytes]:
    widths = {
        **SIGNED,
        "uint32": 32, "fixed32": 32, "float": 32,
        "uint64": 64, "fixed64": 64, "double": 64,
    }
    width = widths.get(encoding)
    if width not in (32, 64) or type(value) is not int:
        raise AcquisitionError("runtime numeric probe scalar type is unsupported")
    mask = (1 << width) - 1
    if encoding in SIGNED and not -(1 << (width - 1)) <= value < (1 << (width - 1)):
        raise AcquisitionError("signed parse scalar exceeds its CLR width")
    if encoding in {"sfixed32", "sfixed64"}:
        return (5 if width == 32 else 1), (value & mask).to_bytes(width // 8, "little")
    if encoding in {"fixed32", "fixed64", "float", "double"}:
        if not 0 <= value <= mask:
            raise AcquisitionError("runtime fixed-width probe exceeds its CLR width")
        return (5 if width == 32 else 1), value.to_bytes(width // 8, "little")
    if encoding.startswith("sint"):
        unsigned = ((value << 1) ^ (value >> (width - 1))) & mask
    elif encoding.startswith("uint"):
        if not 0 <= value <= mask:
            raise AcquisitionError("runtime unsigned probe exceeds its CLR width")
        unsigned = value
    else:
        unsigned = value & ((1 << 64) - 1)
    return 0, _varint(unsigned)


FIELD_TRANSFORM_WIDTHS = {
    "int32": 32, "sint32": 32, "sfixed32": 32,
    "uint32": 32, "fixed32": 32, "float": 32,
    "int64": 64, "sint64": 64, "sfixed64": 64,
    "uint64": 64, "fixed64": 64, "double": 64,
}


def _field_transform_role_inventory(model: Mapping[str, Any]) -> list[dict[str, Any]]:
    messages = model.get("messages_owner_only")
    enums = model.get("enums_owner_only")
    if not isinstance(messages, list) or not isinstance(enums, list):
        raise AcquisitionError("field transform runtime schema is incomplete")
    if any(
        not isinstance(row, Mapping)
        or not isinstance(row.get("name"), str)
        or not row.get("name")
        for row in enums
    ):
        raise AcquisitionError("field transform enum names are incomplete")
    enum_names = {
        name
        for row in enums
        for name in (row.get("name"), row.get("declaring_path"))
        if isinstance(name, str) and name
    }
    message_rows = [row for row in messages if isinstance(row, Mapping)]
    message_names = {
        name
        for row in message_rows
        for name in (row.get("name"), row.get("declaring_path"))
        if isinstance(name, str) and name
    }
    if (
        len(message_rows) != len(messages)
        or any(
            not isinstance(row.get("name"), str) or not row.get("name")
            for row in message_rows
        )
    ):
        raise AcquisitionError("field transform message names are incomplete")
    owners: set[int] = set()
    rows: list[dict[str, Any]] = []
    seen: set[tuple[Any, ...]] = set()
    seen_field_numbers: set[tuple[int, int]] = set()
    nonnumeric_types = {"bool", "string", "bytes", "group"}
    map_key_types = {
        "bool", "string", "int32", "int64", "uint32", "uint64",
        "sint32", "sint64", "fixed32", "fixed64", "sfixed32", "sfixed64",
    }
    for message in messages:
        if not isinstance(message, Mapping):
            raise AcquisitionError("field transform message model is invalid")
        type_index = message.get("type_index_owner_only")
        if type(type_index) is not int or type_index < 0:
            raise AcquisitionError("field transform message identity is invalid")
        if type_index in owners:
            raise AcquisitionError("field transform message identity is duplicated")
        owners.add(type_index)
        containers = [("field", message.get("fields"), None)]
        for oneof in message.get("oneofs") or []:
            if not isinstance(oneof, Mapping) or not isinstance(oneof.get("name"), str):
                raise AcquisitionError("field transform oneof model is invalid")
            containers.append(("oneof:" + str(oneof["name"]), oneof.get("cases"), None))
        for container, fields, _unused in containers:
            if not isinstance(fields, list):
                raise AcquisitionError("field transform field list is invalid")
            for field in fields:
                if not isinstance(field, Mapping):
                    raise AcquisitionError("field transform field model is invalid")
                number = field.get("number")
                cardinality = field.get("cardinality", "singular")
                if type(number) is not int or not 0 < number <= 0x1FFFFFFF:
                    raise AcquisitionError("field transform field number is invalid")
                number_key = (type_index, number)
                if number_key in seen_field_numbers:
                    raise AcquisitionError("field transform field number is duplicated")
                seen_field_numbers.add(number_key)
                if cardinality not in {"singular", "repeated", "map"}:
                    raise AcquisitionError(
                        "field transform field cardinality is unclassified: "
                        + repr(cardinality)
                    )
                roles = ("key_type", "value_type") if cardinality == "map" else ("type",)
                for role in roles:
                    type_name = field.get(role)
                    if not isinstance(type_name, str) or not type_name:
                        raise AcquisitionError(
                            "field transform protobuf type is missing for "
                            + f"message type index {type_index}, field {number}, role {role}"
                        )
                    if type_name in enum_names and type_name in message_names:
                        raise AcquisitionError(
                            "field transform type name is ambiguous between message "
                            + f"and enum: {type_name!r} at message type index "
                            + f"{type_index}, field {number}, role {role}"
                        )
                    if cardinality == "map" and role == "key_type":
                        if type_name not in map_key_types:
                            raise AcquisitionError(
                                "field transform map key type is invalid: "
                                + repr(type_name)
                            )
                    if type_name in enum_names:
                        encoding, width = "int32", 32
                    elif type_name in FIELD_TRANSFORM_WIDTHS:
                        encoding, width = type_name, FIELD_TRANSFORM_WIDTHS[type_name]
                    elif type_name in nonnumeric_types or type_name in message_names:
                        continue
                    else:
                        raise AcquisitionError(
                            "field transform protobuf type is unclassified: "
                            + f"message type index {type_index}, field {number}, "
                            + f"role {role}, type {type_name!r}"
                        )
                    identity = {
                        "type_index_owner_only": type_index,
                        "number": number,
                        "container": container,
                        "role": role,
                        "cardinality": cardinality,
                        "width": width,
                    }
                    key = tuple(identity[name] for name in (
                        "type_index_owner_only", "number", "container", "role"
                    ))
                    if key in seen:
                        raise AcquisitionError("field transform role identity is duplicated")
                    seen.add(key)
                    rows.append({**identity, "encoding": encoding})
    return rows


def _tag(number: int, wire: int, payload: bytes) -> bytes:
    return _varint(number << 3 | wire) + payload


def _map_default_key(key_type: str, key_text: bytes) -> tuple[int, bytes]:
    if key_type == "string":
        return 2, _varint(len(key_text)) + key_text
    if key_type == "bool":
        return 0, b"\x01"
    if key_type in ("fixed32", "sfixed32"):
        return 5, (1).to_bytes(4, "little")
    if key_type in ("fixed64", "sfixed64"):
        return 1, (1).to_bytes(8, "little")
    if key_type in ("sint32", "sint64"):
        return 0, b"\x02"
    if key_type in ("int32", "int64", "uint32", "uint64"):
        return 0, b"\x01"
    raise AcquisitionError(f"unsupported current-runtime protobuf map key: {key_type}")


def build_payload(
    *, identity: Mapping[str, Any], encoding: str, value: int,
    packed: bool | None = None, key_type: str | None = None,
    key_text: bytes = b"",
    omit_default_map_scalar: bool = False,
    map_message_value: bool = False, map_string_value: bool = False,
) -> bytes:
    wire, scalar = _scalar(encoding, value)
    number = int(identity["number"])
    container = str(identity["container"])
    cardinality = str(identity["cardinality"])
    role = str(identity["role"])
    if (map_message_value or map_string_value) and (cardinality != "map" or role != "key_type"):
        raise AcquisitionError("message map value context belongs to another role")
    if container.startswith("oneof:") or cardinality == "singular":
        return _tag(number, wire, scalar)
    if cardinality == "repeated":
        if type(packed) is not bool:
            raise AcquisitionError("signed repeated packing observation is absent")
        return _tag(number, 2, _varint(len(scalar)) + scalar) if packed else _tag(number, wire, scalar)
    if cardinality == "map":
        entry = bytearray()
        if role == "key_type":
            if value != 0 or not omit_default_map_scalar:
                entry += _tag(1, wire, scalar)
            if map_message_value or map_string_value:
                entry += _tag(2, 2, b"\x00")
        elif role == "value_type":
            if not isinstance(key_type, str):
                raise AcquisitionError("signed map key context is absent")
            key_wire, key = _map_default_key(key_type, key_text)
            entry += _tag(1, key_wire, key)
            if value != 0 or not omit_default_map_scalar:
                entry += _tag(2, wire, scalar)
        else:
            raise AcquisitionError("invalid signed map role")
        return _tag(number, 2, _varint(len(entry)) + bytes(entry))
    raise AcquisitionError("unsupported signed role container")


def _fnv(data: bytes) -> int:
    value = 1469598103934665603
    for byte in data:
        value = (value ^ byte) * 1099511628211 & ((1 << 64) - 1)
    return value


_WRITER_INIT_VARINT_ENCODINGS = frozenset({
    "int32", "int64", "uint32", "uint64", "sint32", "sint64", "bool",
})


_WRITER_INIT_WHOLE_BUFFER_STRATEGIES = frozenset({1, 3, 4})


def _wire_default_scalar_tag(number: int) -> bytes:
    tag = number << 3
    out = bytearray()
    while True:
        byte = tag & 0x7F
        tag >>= 7
        if tag:
            out.append(byte | 0x80)
        else:
            out.append(byte)
            return bytes(out)


def _writer_init_payload(
    *, sibling_numbers: list[int], absent_number: int | None,
    target_number: int, strategy: int,
) -> bytes:
    if not strategy:
        return b""
    sibling = next(
        (number for number in sibling_numbers if number != target_number), None
    )
    if sibling is not None:
        return _wire_default_scalar_tag(sibling) + b"\x00"
    if (
        strategy not in _WRITER_INIT_WHOLE_BUFFER_STRATEGIES
        and absent_number is not None
    ):
        return _wire_default_scalar_tag(absent_number) + b"\x00"
    return b""


def _transform_role_strategy(
    *, message: Mapping[str, Any], owner: int, cardinality: str, role: str,
    writer_deadly_types: frozenset[int],
    prefer_parse: bool = False,
) -> int:
    if prefer_parse:
        return 0
    if message.get("merge_from_rva") is None and owner not in writer_deadly_types:
        strategy = {
            ("singular", "type"): 2,
            ("repeated", "type"): 1,
            ("map", "value_type"): 3,
            ("map", "key_type"): 4,
        }.get((cardinality, role))
        if strategy is None:
            raise AcquisitionError(
                "serializer-only numeric role has no bound live writer probe "
                f"({cardinality}, {role})"
            )
        return strategy
    return 0


def writer_termination_proof(status: Mapping[str, Any]) -> bool:
    return bool(
        status.get("status") == "complete"
        and status.get("failure_kind_owner_only") == WRITER_TERMINATION_FAILURE_KIND
        and status.get("dispatch_stage_owner_only") == 0
        and status.get("parse_write_retries_owner_only", 0) >= 1
        and status.get("health_probe_owner_only") == 1
    )


def parse_writer_fallback_roles(
    *, plan: Mapping[str, Any], status: Mapping[str, Any], bin_path: Path,
) -> frozenset[tuple[Any, ...]]:
    contract = plan.get("contract", {})
    if (contract.get("mode") != "field-transform"
            or status.get("status") != "complete"
            or status.get("dispatch_stage_owner_only", 0) != 0
            or not bin_path.is_file()):
        return frozenset()
    rows = plan["rows_owner_only"]
    count = contract["record_count"]
    raw = _owner_file(bin_path, label="parser route capture").read_bytes()
    if len(raw) != HEADER.size + count * RECORD.size or len(rows) != count:
        return frozenset()
    header = HEADER.unpack_from(raw)
    if (header[0] != MAGIC or header[1] != VERSION
            or header[2] != HEADER.size or header[3] != RECORD.size
            or header[5] != count or header[6] != plan["target"]["process_id"]
            or header[7] != plan["target"]["executable_sha256"].encode("ascii")
            or status.get("completed_count") != count):
        return frozenset()
    samples: dict[tuple[Any, ...], list[tuple[int, int]]] = {}
    failed = set()
    failures = 0
    for index, row in enumerate(rows):
        record = RECORD.unpack_from(raw, HEADER.size + index * RECORD.size)
        if record[:3] != (index, row["field_index"], row["role_kind"]):
            return frozenset()
        failures += bool(record[3])
        if not record[3] and record[6:] != (row["positive_hash"], row["negative_hash"]):
            return frozenset()
        fallback = row.get("writer_fallback_strategy_owner_only")
        if (row["strategy"] != 0 or (row["role_kind"], fallback) not in {
                (ROLE_KIND["singular"], 2), (ROLE_KIND["oneof"], 2), (ROLE_KIND["oneof"], 10), (ROLE_KIND["repeated"], 1),
                (ROLE_KIND["map-value"], 3), (ROLE_KIND["map-key"], 4), (ROLE_KIND["map-key"], 11)}):
            continue
        key = tuple(row["identity"][name] for name in (
            "type_index_owner_only", "number", "container", "role"
        ))
        if record[3]:
            failed.add(key)
        else:
            mask = (1 << row["width"]) - 1
            samples.setdefault(key, []).extend((
                (row["positive_value_bits"], record[4] & mask),
                (row["negative_value_bits"], record[5] & mask),
            ))
    if failures != status.get("failure_count"):
        return frozenset()
    expected = contract["samples_per_role"]
    for key, pairs in samples.items():
        if (len(pairs) != expected or len({a for a, _ in pairs}) != expected
                or len({b for _, b in pairs}) != expected):
            failed.add(key)
    return frozenset(failed)


def writer_deadly_types_from_capture(
    *, plan: Mapping[str, Any], status: Mapping[str, Any], bin_path: Path,
) -> frozenset[int]:
    if not writer_termination_proof(status):
        return frozenset()
    count = int(plan["contract"]["record_count"])
    raw = Path(bin_path).read_bytes()
    if len(raw) != HEADER.size + count * RECORD.size:
        raise AcquisitionError("runtime writer-termination capture envelope differs")
    rows_by_field: dict[int, Mapping[str, Any]] = {}
    for row in plan["rows_owner_only"]:
        rows_by_field.setdefault(int(row["field_index"]), row)
    types: set[int] = set()
    for index in range(count):
        record = RECORD.unpack_from(raw, HEADER.size + index * RECORD.size)
        if record[3] != WRITER_TERMINATION_FAILURE_KIND:
            continue
        row = rows_by_field.get(int(record[1]))
        if row is None:
            raise AcquisitionError(
                "runtime writer-termination record lacks its plan row "
                f"(row={index})"
            )
        types.add(int(row["identity"]["type_index_owner_only"]))
    return frozenset(types)


def _field_types(model_path: Path) -> dict[int, int]:
    model = read_private_model(_owner_file(model_path, label="field type model"))
    identity = model.get("inventory")
    if not isinstance(identity, Mapping) or not isinstance(identity.get("path"), str):
        raise AcquisitionError("runtime signed parse field type inventory is absent")
    path = _owner_file(Path(identity["path"]), label="field type inventory")
    if file_identity(path) != identity:
        raise AcquisitionError("runtime signed parse field type inventory is stale")
    raw = path.read_bytes()
    header = RUNTIME_PROTO_FIELD_TYPE_HEADER.unpack_from(raw)
    if (
        header[0] != RUNTIME_PROTO_FIELD_TYPE_MAGIC
        or header[1] != RUNTIME_PROTO_FIELD_TYPE_VERSION
        or len(raw) != RUNTIME_PROTO_FIELD_TYPE_HEADER.size
        + int(header[5]) * RUNTIME_PROTO_FIELD_TYPE_RECORD.size
    ):
        raise AcquisitionError("runtime signed parse field type inventory differs")
    result: dict[int, int] = {}
    for index in range(int(header[5])):
        _owner, field, _pointer, descriptor = RUNTIME_PROTO_FIELD_TYPE_RECORD.unpack_from(
            raw, RUNTIME_PROTO_FIELD_TYPE_HEADER.size
            + index * RUNTIME_PROTO_FIELD_TYPE_RECORD.size
        )
        if field in result or not descriptor:
            raise AcquisitionError("runtime signed parse field type records conflict")
        result[int(field)] = int(descriptor)
    return result


def _native_fields(runtime: Any) -> tuple[
    dict[int, tuple[int, ...]], dict[tuple[int, int], list[int]]
]:
    cached = getattr(runtime, "_signed_parse_field_index", None)
    if cached is not None and isinstance(runtime.native, bytes) and cached[0] is runtime.native:
        return cached[1]
    header = RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.unpack_from(runtime.native)
    by_index: dict[int, tuple[int, ...]] = {}
    by_offset: dict[tuple[int, int], list[int]] = {}
    for index in range(int(header[5])):
        row = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        by_index[index] = row
        if not row[5] & 0x10 and row[4] >= 0:
            key = (int(row[0]), int(row[4]) + 16)
            by_offset.setdefault(key, []).append(index)
    result = (by_index, by_offset)
    if isinstance(runtime.native, bytes):
        runtime._signed_parse_field_index = (runtime.native, result)
    return result


def _repeated_collection_accessor(
    *, runtime: Any, snapshot: Any, definition: int, element_descriptor: int,
) -> tuple[int, int, int]:
    add_ordinal, add_method_count = _definition_method(
        runtime, definition,
        lambda index, row: (
            not row[5] & 0x10
            and row[10] == 1
            and _descriptor_enum(snapshot, row[4], 0x01)
            and _generic_parameter(
                runtime, runtime.parameter_row(row[11])[2]
            )
        ),
    )
    map_value_kind = {
        0x0c: 1, 0x0d: 2,
    }.get(snapshot.il2cpp_type_enum(element_descriptor), 0)
    return add_ordinal, add_method_count, map_value_kind


def _definition_method_ordinals(runtime: Any, owner: int, predicate) -> tuple[tuple[int, ...], int]:
    methods = runtime.method_indexes_by_owner.get(owner, ())
    matches = [index for index in methods if predicate(index, runtime.method_row(index))]
    ordinals = {index: ordinal for ordinal, index in enumerate(methods)}
    return tuple(ordinals[index] for index in matches), len(methods)


def _definition_method(runtime: Any, owner: int, predicate) -> tuple[int, int]:
    ordinals, count = _definition_method_ordinals(runtime, owner, predicate)
    if len(ordinals) != 1:
        raise AcquisitionError(
            f"runtime signed parse collection accessor is ambiguous "
            f"(definition={owner}, candidates={len(ordinals)})"
        )
    return ordinals[0], count


def _generic_parameter(runtime: Any, descriptor: int) -> bool:
    node = runtime.renderer.node_by_descriptor.get(descriptor)
    return node is not None and bool(
        runtime.renderer.reference_row(node)[4] & TYPE_REFERENCE_GENERIC_PARAMETER
    )


def _map_collection_accessor(
    *, runtime: Any, snapshot: Any, definition: int, value_descriptor: int,
    allow_direct_float: bool = True,
) -> tuple[int, int, int]:
    def accepts_object_key(_index: int, row: Any) -> bool:
        return bool(
            not row[5] & 0x10
            and not row[9] & 1
            and row[10] == 1
            and _descriptor_enum(
                snapshot, runtime.parameter_row(row[11])[2], 0x1c
            )
        )

    boxed, count = _definition_method_ordinals(
        runtime, definition,
        lambda index, row: accepts_object_key(index, row)
        and _descriptor_enum(snapshot, row[4], 0x1c),
    )
    if boxed:
        if len(boxed) != 1:
            raise AcquisitionError("runtime map boxed getter is ambiguous")
        return boxed[0], count, 0
    value_enum = snapshot.il2cpp_type_enum(value_descriptor)
    kind = {0x0c: 1, 0x0d: 2}.get(value_enum)
    if kind is None or not allow_direct_float:
        raise AcquisitionError("runtime map getter has no supported return ABI")
    ordinal, count = _definition_method(
        runtime, definition,
        lambda index, row: accepts_object_key(index, row)
        and _descriptor_enum(snapshot, row[4], value_enum),
    )
    return ordinal, count, kind


def _descriptor_enum(snapshot: RuntimeSnapshot, descriptor: int, expected: int) -> bool:

    try:
        return snapshot.il2cpp_type_enum(descriptor) == expected
    except KeyError:
        return False


def _pending_roles(model: Mapping[str, Any]) -> list[dict[str, Any]]:
    from alpha.p01 import encoding_coverage

    messages = model.get("messages_owner_only", [])
    domain = role_inventory(messages)
    coverage = encoding_coverage(messages)
    rows = coverage.get("roles_owner_only", [])
    by_key = {
        tuple(row[name] for name in (
            "type_index_owner_only", "number", "container", "role"
        )): row
        for row in rows
    }
    if len(by_key) != len(domain):
        raise AcquisitionError("runtime signed parse coverage domain differs")
    pending = []
    for identity in domain:
        key = tuple(identity[name] for name in (
            "type_index_owner_only", "number", "container", "role"
        ))
        row = by_key.get(key)
        if row is None or any(
            row.get(name) != identity.get(name)
            for name in ("type_index_owner_only", "number", "container", "role", "cardinality")
        ):
            raise AcquisitionError("runtime signed parse coverage identity differs")
        if row.get("verified") is not True:
            pending.append(identity)
    return pending


def _unsigned_roles(model: Mapping[str, Any]) -> list[dict[str, Any]]:
    return [
        {key: value for key, value in row.items() if key != "encoding"}
        for row in _field_transform_role_inventory(model)
        if row["encoding"] in UNSIGNED
        and (row["cardinality"] == "repeated"
             or row["cardinality"] == "map" and row["role"] == "value_type")
    ]


def _role_field(model: Mapping[str, Any], identity: Mapping[str, Any]) -> Mapping[str, Any]:
    message = next(row for row in model["messages_owner_only"]
                   if row["type_index_owner_only"] == identity["type_index_owner_only"])
    fields = (message["fields"] if identity["container"] == "field" else next(
        row["cases"] for row in message["oneofs"]
        if "oneof:" + row["name"] == identity["container"]
    ))
    return next(row for row in fields if row["number"] == identity["number"])


def unsigned_encoding_coverage(model: Mapping[str, Any]) -> dict[str, Any]:
    roles = _unsigned_roles(model)
    verified = 0
    for identity in roles:
        field = _role_field(model, identity)
        evidence = field.get("unsigned_parse_evidence", {}).get(identity["role"])
        if evidence is None:
            continue
        checked = verify_parse_evidence(evidence)
        if (checked["identity"] != identity
                or checked["encoding"] != field[identity["role"]]
                or identity["cardinality"] == "repeated"
                and checked["context"]["packed"] is not field.get("packed")):
            raise AcquisitionError("unsigned encoding evidence differs from current field")
        verified += 1
    return {"schema": "alpha.runtime-proto-unsigned-encoding-coverage/v1",
            "required_count": len(roles), "verified_count": verified,
            "complete": verified == len(roles)}


def apply_unsigned_parse_evidence(model: Mapping[str, Any], capture: Mapping[str, Any]) -> dict[str, Any]:
    if capture.get("schema") != RESULT_SCHEMA or capture.get("target") != model.get("target"):
        raise AcquisitionError("unsigned encoding capture belongs to another model")
    result = copy.deepcopy(dict(model))
    names = ("type_index_owner_only", "number", "container", "role")
    domain = {tuple(row[name] for name in names): row for row in _unsigned_roles(result)}
    seen = set()
    for raw in capture.get("observations", []):
        evidence = verify_parse_evidence(raw)
        identity = evidence["identity"]
        key = tuple(identity[name] for name in names)
        if (key in seen or domain.get(key) != identity
                or UNSIGNED.get(evidence["encoding"]) != identity["width"]
                or identity["role"] == "key_type"
                and evidence["encoding"] not in {"uint32", "uint64"}):
            raise AcquisitionError("unsigned encoding observation is outside current role domain")
        field = _role_field(result, identity)
        field[identity["role"]] = evidence["encoding"]
        if identity["cardinality"] == "repeated":
            field["packed"] = evidence["context"]["packed"]
        field.setdefault("unsigned_parse_evidence", {})[identity["role"]] = evidence
        seen.add(key)
    if seen != set(domain):
        raise AcquisitionError("unsigned encoding capture does not close current role domain")
    coverage = unsigned_encoding_coverage(result)
    result["unsigned_encoding_coverage_owner_only"] = coverage
    result.setdefault("unsigned_parse_captures_owner_only", []).append(copy.deepcopy(dict(capture)))
    return result


def _optional_oneof_binding(*, model, message, field, fields_by_index):
    if not field.get("optional"):
        return None
    evidence = [row for row in model.get("diagnostics_owner_only", [])
                if row.get("kind") == "proto3-optional-from-structural-evidence"
                and row.get("message") == message["name"]
                and row.get("field") == field["name"]
                and row.get("number") == field["number"]]
    if not evidence:
        return None
    if len(evidence) != 1:
        raise AcquisitionError("runtime optional oneof structural evidence is ambiguous")
    storage_index = field.get("field_index_owner_only")
    discriminator_index = evidence[0].get("discriminator_field_index_owner_only")
    if type(storage_index) is not int or type(discriminator_index) is not int:
        raise AcquisitionError("runtime optional oneof member identity is invalid")
    storage = fields_by_index.get(storage_index)
    discriminator = fields_by_index.get(discriminator_index)
    owner = message["type_index_owner_only"]
    if (storage is None or discriminator is None or storage_index == discriminator_index
            or storage[0] != owner or discriminator[0] != owner
            or storage[5] & 0x10 or discriminator[5] & 0x10
            or storage[4] < 0 or discriminator[4] < 0
            or storage[4] + 16 != field["offset"]
            or storage[4] == discriminator[4]):
        raise AcquisitionError("runtime optional oneof native binding differs")
    return storage_index, discriminator_index


def _rows(
    *, model: Mapping[str, Any], runtime: Any, live: Any,
    snapshot: RuntimeSnapshot, field_types: Mapping[int, int],
    role_start: int = 0, role_limit: int | None = None,
    field_transform_probe_values: Mapping[int, list[int]] | None = None,
    writer_deadly_types: frozenset[int] = frozenset(),
    writer_fallback_roles: frozenset[tuple[Any, ...]] = frozenset(),
    unsigned_encoding_audit: bool = False,
    _role_inventory: list[dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], bytes]:
    fields_by_index, fields_by_offset = _native_fields(runtime)


    fields_by_owner: dict[int, list[int]] = {}
    for index, native_field in fields_by_index.items():
        fields_by_owner.setdefault(native_field[0], []).append(index)
    repeated_layouts: dict[int, tuple[int, int]] = {}
    messages = {int(row["type_index_owner_only"]): row
                for row in model["messages_owner_only"]}
    message_value_names = {
        name for message in messages.values()
        for name in (message.get("name"), message.get("declaring_path"))
        if isinstance(name, str) and name
    }
    transform_mode = field_transform_probe_values is not None
    roles = _role_inventory if _role_inventory is not None else (
        _field_transform_role_inventory(model)
        if transform_mode else _unsigned_roles(model)
        if unsigned_encoding_audit else _pending_roles(model)
    )
    if (
        not isinstance(role_start, int)
        or isinstance(role_start, bool)
        or role_start < 0
        or role_start > len(roles)
        or role_limit is not None
        and (
            not isinstance(role_limit, int)
            or isinstance(role_limit, bool)
            or role_limit <= 0
        )
    ):
        raise AcquisitionError("runtime signed parse role slice is invalid")
    roles = roles[role_start:]
    if role_limit is not None:
        roles = roles[:role_limit]
    if not roles:
        raise AcquisitionError("runtime signed parse role slice is empty")
    signed_descriptors: dict[int, set[int]] = {32: set(), 64: set()}


    for descriptor in (field_types.values() if not transform_mode and not unsigned_encoding_audit else ()):
        try:
            enum = snapshot.il2cpp_type_enum(descriptor)
        except KeyError:
            continue
        if enum == 8:
            signed_descriptors[32].add(descriptor)
        elif enum == 10:
            signed_descriptors[64].add(descriptor)
    signed_classes: dict[int, int] = {}
    if not transform_mode and not unsigned_encoding_audit:
        for width, descriptors in signed_descriptors.items():
            roots = {runtime.renderer.root_by_descriptor[d]
                     for d in descriptors if d in runtime.renderer.root_by_descriptor}
            if len(roots) != 1:
                raise AcquisitionError(f"runtime signed parse CLR {width}-bit class is ambiguous")
            signed_classes[width] = live.type_row(roots.pop()).class_pointer

    blob = bytearray()
    output: list[dict[str, Any]] = []
    init_inputs: dict[int, tuple[list[int], int | None]] = {}
    oneof_box_classes: dict[str, int] = {}
    for identity in roles:
        owner = int(identity["type_index_owner_only"])
        message = messages[owner]
        init_entry = init_inputs.get(owner)
        if init_entry is None:


            sibling_numbers = [
                int(row["number"]) for row in message["fields"]
                if row.get("cardinality", "singular") == "singular"
                and str(row.get("type", "")) in _WRITER_INIT_VARINT_ENCODINGS
            ]
            all_numbers = [int(row["number"]) for row in message["fields"]]
            absent_number = (
                max(all_numbers) + 1
                if all_numbers and max(all_numbers) < 0x1FFFFFFF else None
            )
            init_entry = (sibling_numbers, absent_number)
            init_inputs[owner] = init_entry
        sibling_numbers, absent_number = init_entry
        container = str(identity["container"])
        role = str(identity["role"])
        if container == "field":
            fields = message["fields"]
        else:
            oneof = next(row for row in message["oneofs"]
                         if container == "oneof:" + row["name"])
            fields = oneof["cases"]
        field = next(row for row in fields if int(row["number"]) == int(identity["number"]))
        source_encoding = str(identity.get("encoding", field[role]))
        if transform_mode:
            identity = {key: value for key, value in identity.items() if key != "encoding"}
        width = (
            FIELD_TRANSFORM_WIDTHS[source_encoding]
            if transform_mode else {**SIGNED, **UNSIGNED}[source_encoding]
        )


        encodings = _encoding_candidates(width, unsigned=unsigned_encoding_audit)
        if unsigned_encoding_audit and role == "key_type":
            encodings = (f"uint{width}",)
        message_descriptor = live.type_row(owner).embedded_descriptor(
            live.embedded_descriptor_byte_offset
        )
        method_ordinal = 0
        method_count = 0
        auxiliary_offset = 0
        key_class = 0
        key_width = 0
        key_kind = 0
        map_value_kind = 0
        key_text = b""
        map_mutator_ordinal = 0
        numeric_class = 0
        map_value_descriptor = 0
        packed = field.get("packed")
        optional_binding = (_optional_oneof_binding(
            model=model, message=message, field=field, fields_by_index=fields_by_index
        ) if container == "field" else None)
        if container.startswith("oneof:") or optional_binding is not None:
            if optional_binding is not None:
                storage_index, discriminator_index = optional_binding
            else:
                storage_index = int(oneof["storage_field_index_owner_only"])
                discriminator_index = int(oneof["discriminator_field_index_owner_only"])
            storage = fields_by_index[storage_index]
            discriminator = fields_by_index[discriminator_index]
            if storage[0] != owner or discriminator[0] != owner:
                raise AcquisitionError("runtime signed parse oneof owner differs")
            field_index = storage_index
            field_offset = int(storage[4]) + 16
            auxiliary_offset = int(discriminator[4]) + 16
            kind = ROLE_KIND["oneof"]
            field_pointer = live.field_row(storage_index, expected_owner=owner).pointer
        else:
            key = (owner, int(field["offset"]))
            matches = [
                index for index in fields_by_offset.get(key, [])
                if _text(
                    runtime.native,
                    fields_by_index[index][9],
                    fields_by_index[index][7],
                    label="field name",
                ) == field["name"]
            ]
            if len(matches) != 1:
                raise AcquisitionError("runtime signed parse backing field is ambiguous")
            field_index = matches[0]
            field_offset = int(field["offset"])
            field_pointer = live.field_row(field_index, expected_owner=owner).pointer
            if identity["cardinality"] == "singular":
                kind = ROLE_KIND["singular"]
            else:
                descriptor = field_types.get(field_index)
                node = runtime.renderer.node_by_descriptor.get(descriptor or 0)
                if node is None:
                    raise AcquisitionError("runtime signed parse constructed field is absent")
                definition, arguments = observed_generic_parts(
                    runtime.renderer, runtime.renderer.reference_row(node)
                )
                if identity["cardinality"] == "repeated":
                    if len(arguments) != 1:
                        raise AcquisitionError("runtime signed repeated argument domain differs")
                    if transform_mode or unsigned_encoding_audit:
                        element_root = runtime.renderer.root_by_descriptor.get(arguments[0])
                        if element_root is None:
                            raise AcquisitionError("runtime field transform element class is absent")
                        numeric_class = live.type_row(element_root).class_pointer
                    definition_fields = fields_by_owner.get(definition, [])
                    layout = repeated_layouts.get(definition)
                    array_fields = []
                    for candidate_index in (() if layout else definition_fields):
                        candidate = fields_by_index[candidate_index]
                        if candidate[5] & 0x10:
                            continue
                        reference_index = runtime.renderer.node_by_descriptor.get(
                            candidate[3]
                        )
                        if reference_index is None:
                            continue
                        reference = runtime.renderer.reference_row(reference_index)
                        if (reference[4] & TYPE_REFERENCE_ARRAY
                                and _generic_parameter(runtime, reference[13])):
                            array_fields.append(candidate_index)
                    if layout is None and len(array_fields) != 1:
                        raise AcquisitionError(
                            "runtime signed repeated backing array is ambiguous"
                        )
                    count_fields = [
                        candidate_index
                        for candidate_index in (() if layout else definition_fields)
                        if not fields_by_index[candidate_index][5] & 0x10
                        and _descriptor_enum(
                            snapshot, fields_by_index[candidate_index][3], 0x08
                        )
                    ]
                    if layout is None and len(count_fields) != 1:
                        raise AcquisitionError(
                            "runtime signed repeated count field is ambiguous"
                        )
                    if layout is None:
                        layout = (definition_fields.index(array_fields[0]),
                                  definition_fields.index(count_fields[0]))
                        repeated_layouts[definition] = layout
                    method_ordinal, method_count = layout
                    kind = ROLE_KIND["repeated"]


                    key_kind, key_width, map_value_kind = (
                        _repeated_collection_accessor(
                            runtime=runtime, snapshot=snapshot,
                            definition=definition,
                            element_descriptor=arguments[0],
                        )
                    )
                    if type(packed) is not bool:
                        raise AcquisitionError("runtime signed repeated packing was not recovered")
                elif identity["cardinality"] == "map":
                    if len(arguments) != 2:
                        raise AcquisitionError("runtime signed map argument domain differs")
                    if field.get("value_type") == "string" and snapshot.il2cpp_type_enum(arguments[1]) != 14:
                        raise AcquisitionError("runtime map string value descriptor differs")
                    method_ordinal, method_count, map_value_kind = _map_collection_accessor(
                        runtime=runtime, snapshot=snapshot,
                        definition=definition, value_descriptor=arguments[1],
                        allow_direct_float=role == "value_type",
                    )
                    mutators, mutator_count = _definition_method_ordinals(
                        runtime, definition,
                        lambda index, row: (
                            not row[5] & 0x10
                            and not row[9] & 1
                            and row[10] == 2
                            and _descriptor_enum(snapshot, row[4], 0x01)
                            and _generic_parameter(
                                runtime, runtime.parameter_row(row[11])[2]
                            )
                            and _generic_parameter(
                                runtime, runtime.parameter_row(row[11] + 1)[2]
                            )
                        ),
                    )
                    if not mutators or mutator_count != method_count:
                        raise AcquisitionError(
                            "runtime signed map mutator signature is absent"
                        )
                    map_mutator_ordinal = mutators[0]
                    kind = ROLE_KIND["map-key" if role == "key_type" else "map-value"]
                    key_descriptor = arguments[0]
                    key_index = runtime.renderer.root_by_descriptor.get(key_descriptor)
                    if key_index is None:
                        raise AcquisitionError("runtime signed map key class is absent")
                    key_enum = snapshot.il2cpp_type_enum(key_descriptor)
                    if key_enum == 14:
                        key_kind = 1
                        key_text = str(field["name"]).encode("utf-8")
                    elif key_enum in (2, 8, 9, 10, 11):
                        key_kind = 2
                        key_class = live.type_row(key_index).class_pointer
                        key_width = 64 if key_enum in (10, 11) else 32
                    else:
                        raise AcquisitionError("runtime signed map key storage is unsupported")
                    if role == "key_type" and field.get("value_type") in message_value_names:
                        value_root = runtime.renderer.root_by_descriptor.get(arguments[1])
                        if value_root is None:
                            raise AcquisitionError("runtime map message value class is absent")
                        map_value_descriptor = live.type_row(value_root).embedded_descriptor(
                            live.embedded_descriptor_byte_offset
                        )
                    if transform_mode or unsigned_encoding_audit:
                        value_descriptor = (
                            arguments[1] if role == "value_type" else key_descriptor
                        )
                        value_root = runtime.renderer.root_by_descriptor.get(value_descriptor)
                        if value_root is None:
                            raise AcquisitionError("runtime field transform map role class is absent")
                        numeric_class = live.type_row(value_root).class_pointer
                else:
                    raise AcquisitionError("runtime signed parse cardinality is invalid")
        if transform_mode:
            encodings = (source_encoding,)
            contexts = [{
                "packed": packed if identity["cardinality"] == "repeated" else None,
                "source_packed": packed if identity["cardinality"] == "repeated" else None,
                "input_packed": packed if identity["cardinality"] == "repeated" else None,
                "key_type": field.get("key_type") if identity["cardinality"] == "map" else None,
                "key_text_hex": key_text.hex(),
            }]
            if width not in field_transform_probe_values or not isinstance(
                field_transform_probe_values[width], list
            ):
                raise AcquisitionError("runtime field transform probe values are absent")
            probe_values = field_transform_probe_values[width]
            if (
                len(probe_values) < 2 or len(probe_values) % 2
                or any(type(value) is not int or not 0 <= value < 1 << width
                       for value in probe_values)
                or len(set(probe_values)) != len(probe_values)
            ):
                raise AcquisitionError("runtime field transform probe value inventory is invalid")
            sample_pairs = list(zip(probe_values[::2], probe_values[1::2]))
            strategy_encodings = ((
                _baseline_writer_strategy(_transform_role_strategy(
                    message=message, owner=owner,
                    cardinality=identity["cardinality"], role=role,
                    writer_deadly_types=writer_deadly_types,
                    prefer_parse=tuple(identity[name] for name in (
                        "type_index_owner_only", "number", "container", "role"
                    )) not in writer_fallback_roles,
                )), tuple(encodings)),
            )
            if kind == ROLE_KIND["oneof"] and tuple(identity[name] for name in (
                    "type_index_owner_only", "number", "container", "role")) in writer_fallback_roles:
                strategy_encodings = ((10, tuple(encodings)),)
                numeric_class = _oneof_box_class(
                    runtime=runtime, live=live, field=field, model=model,
                    cache=oneof_box_classes)
        else:
            contexts = [{
                "packed": candidate_packed,
                "source_packed": packed if identity["cardinality"] == "repeated" else None,
                "key_type": field.get("key_type") if identity["cardinality"] == "map" else None,
                "key_text_hex": key_text.hex(),
            } for candidate_packed in (
                (packed, not packed)
                if identity["cardinality"] == "repeated" else (None,)
            )]
            strategy_encodings = _observation_strategies(
                str(identity["cardinality"]), role, tuple(encodings)
            )
            if unsigned_encoding_audit:
                baseline_strategy = 6 if identity["cardinality"] == "repeated" else 7
                strategy_encodings = ((5, tuple(encodings)),
                                      (baseline_strategy, tuple(encodings)),
                                      *(candidate for candidate in strategy_encodings
                                        if candidate[0] != baseline_strategy))
            sample_pairs = [(123, -123)]

        string_map_key = kind == ROLE_KIND["map-key"] and field.get("value_type") == "string"
        if string_map_key and owner not in writer_deadly_types:
            if transform_mode:
                string_fallback = tuple(identity[name] for name in (
                    "type_index_owner_only", "number", "container", "role")) in writer_fallback_roles
                strategy_encodings = ((11 if string_fallback else 0, tuple(encodings)),)
            else:
                strategy_encodings = ((0, tuple(encodings)), (11, tuple(encodings)),
                                      *(candidate for candidate in strategy_encodings if candidate[0] != 0))
        elif transform_mode and map_value_descriptor:
            strategy_encodings = tuple(
                (9 if strategy in (0, 8) and owner not in writer_deadly_types else strategy, candidates)
                for strategy, candidates in strategy_encodings
            )
        elif map_value_descriptor:


            strategy_encodings = ((9, tuple(encodings)), *strategy_encodings)

        def scalar_probe_value(bits: int, encoding_name: str) -> int:
            if bits < 0:
                return bits & ((1 << width) - 1) if encoding_name in UNSIGNED else bits
            if encoding_name not in {
                "int32", "sint32", "sfixed32", "int64", "sint64", "sfixed64"
            }:
                return bits
            sign = 1 << (width - 1)
            return bits - (1 << width) if bits & sign else bits

        for strategy, candidate_encodings in strategy_encodings:
            for encoding in candidate_encodings:
                candidate_contexts = contexts
                if not transform_mode and identity["cardinality"] == "repeated" and strategy in (0, 5):
                    candidate_contexts = _repeated_parse_contexts(
                        packed, unsigned_encoding_audit=unsigned_encoding_audit
                    )
                    if strategy == 5:
                        candidate_contexts = [{**context, "packed": packed}
                                              for context in candidate_contexts]
                for context in candidate_contexts:
                    context = {
                        **context,
                        "observation_mode": {
                            0: "parse",
                            1: "repeated-write-serialize",
                            2: "singular-write-serialize",
                            3: "map-write-serialize",
                            4: "map-key-write-serialize",
                            5: "parse-container",
                            6: "repeated-write-baseline-serialize",
                            7: "map-write-baseline-serialize",
                            8: "map-key-write-baseline-serialize",
                            9: "map-key-message-value-write-serialize",
                            10: "oneof-box-write-baseline-serialize",
                            11: "map-key-string-value-write-serialize",
                        }[strategy],
                        "omit_default_map_scalar": strategy in (3, 4, 7, 8, 9, 11),
                        **({"map_string_value": True} if string_map_key and strategy in (0, 11) else {}),
                        **({"map_message_value": True} if (
                            strategy in (0, 9) and kind == ROLE_KIND["map-key"]
                            and field.get("value_type") in message_value_names
                        ) else {}),
                    }
                    for positive_bits, negative_bits in sample_pairs:
                        if transform_mode and strategy and strategy != 10:


                            positive_bits = writer_probe_value(encoding, positive_bits)
                            negative_bits = writer_probe_value(encoding, negative_bits)
                        payloads = [build_payload(
                            identity=identity, encoding=encoding,
                            value=scalar_probe_value(bits, encoding),
                            packed=context.get("input_packed", context["packed"]),
                            key_type=context["key_type"],
                            key_text=key_text,
                            omit_default_map_scalar=context["omit_default_map_scalar"],
                            map_message_value=context.get("map_message_value") is True,
                            map_string_value=context.get("map_string_value") is True,
                        ) for bits in (positive_bits, negative_bits)]
                        starts = []
                        for payload in payloads:
                            starts.append((len(blob), len(payload), _fnv(payload)))
                            blob.extend(payload)
                        init_payload = _writer_init_payload(
                            sibling_numbers=sibling_numbers,
                            absent_number=absent_number,
                            target_number=int(identity["number"]),
                            strategy=strategy,
                        )
                        init_start = len(blob)
                        blob.extend(init_payload)
                        output.append({
                            "identity": dict(identity), "encoding": encoding, "context": context,
                            "message_descriptor": message_descriptor,
                            "message_type_index": owner, "field_index": field_index,
                            "field_pointer": field_pointer, "field_offset": field_offset,
                            "auxiliary_offset": (
                                map_mutator_ordinal if strategy in (3, 4, 7, 8, 9, 11) else auxiliary_offset
                            ), "width": width,
                            "role_kind": kind, "method_ordinal": method_ordinal,
                            "method_count": method_count, "key_kind": key_kind,
                            "map_value_kind": map_value_kind,
                            "key_class": key_class,


                            "signed_class": (
                                map_value_descriptor if strategy == 9 else
                                numeric_class if transform_mode and numeric_class
                                else signed_classes.get(width, 0)
                            ),
                            "key_width": key_width, "field_number": int(identity["number"]),
                            "positive_start": starts[0][0], "positive_bytes": starts[0][1],
                            "positive_hash": starts[0][2], "negative_start": starts[1][0],
                            "negative_bytes": starts[1][1], "negative_hash": starts[1][2],
                            "positive_input_hex": payloads[0].hex(),
                            "negative_input_hex": payloads[1].hex(),
                            "positive_value_bits": (
                                positive_bits if transform_mode else 123
                            ),
                            "negative_value_bits": (
                                negative_bits if transform_mode
                                else (1 << 64) - 123
                            ),
                            "strategy": strategy,
                            "writer_fallback_strategy_owner_only": (
                                11 if transform_mode and string_map_key and owner not in writer_deadly_types else
                                10 if transform_mode and kind == ROLE_KIND["oneof"] else _transform_role_strategy(
                                    message=message, owner=owner,
                                    cardinality=identity["cardinality"], role=role,
                                    writer_deadly_types=writer_deadly_types,
                                ) if transform_mode else 0
                            ),
                            "init_start": init_start,
                            "init_bytes": len(init_payload),
                        })
    return output, bytes(blob)


def _oneof_box_class(*, runtime, live, field, model, cache):
    declared = str(field["type"])
    if declared in cache:
        return cache[declared]
    primitive = {
        "uint32": "System.UInt32", "fixed32": "System.UInt32",
        "int32": "System.Int32", "sint32": "System.Int32", "sfixed32": "System.Int32",
        "uint64": "System.UInt64", "fixed64": "System.UInt64",
        "int64": "System.Int64", "sint64": "System.Int64", "sfixed64": "System.Int64",
        "float": "System.Single", "double": "System.Double", "bool": "System.Boolean",
    }.get(declared)
    if primitive is not None:
        matches = [index for index in range(runtime.type_count)
                   if runtime.renderer.root_name(index) == primitive]
    else:
        matches = [int(row["type_index_owner_only"]) for row in model.get("enums_owner_only", [])
                   if declared in (row.get("name"), row.get("declaring_path"))]
    if len(matches) != 1:
        raise AcquisitionError("runtime oneof boxing class is absent or ambiguous")
    result = live.type_row(matches[0]).class_pointer
    if not result:
        raise AcquisitionError("runtime oneof boxing class is null")
    cache[declared] = result
    return result


def _require_executable_rows(rows: list[dict[str, Any]]) -> None:
    for index, row in enumerate(rows):
        if row.get("strategy") == 11 and (
            row.get("role_kind") != ROLE_KIND["map-key"]
            or row.get("key_kind") != 2 or not row.get("key_class")
            or row.get("key_width") != row.get("width")
            or row.get("context", {}).get("map_string_value") is not True
        ):
            raise AcquisitionError(f"runtime string map key writer lacks its typed binding (row={index})")
        if row.get("strategy") == 9 and (
            row.get("role_kind") != ROLE_KIND["map-key"]
            or row.get("key_kind") != 2
            or not row.get("key_class")
            or not row.get("signed_class")
            or row.get("key_width") != row.get("width")
        ):
            raise AcquisitionError(
                f"runtime message map key writer lacks its typed value binding (row={index})"
            )
        if (row.get("role_kind") == ROLE_KIND["repeated"]
                and row.get("strategy") in (1, 6)
                and not row.get("key_width")):
            raise AcquisitionError(
                "runtime signed repeated write probe lacks its collection "
                f"accessor (row={index})"
            )


        zero = IEEE_NEGATIVE_ZERO_BITS.get(str(row.get("encoding")))
        if (
            zero is not None
            and zero in (row.get("positive_value_bits"), row.get("negative_value_bits"))
            and (
                row.get("strategy") == 2
                and row.get("role_kind") == ROLE_KIND["singular"]
                or row.get("strategy") in (3, 7)
                and row.get("role_kind") == ROLE_KIND["map-value"]
            )
        ):
            raise AcquisitionError(
                "runtime write-serialize probe value is an IEEE negative "
                "zero, which omit-default serializers can never emit "
                f"(row={index}); writer_probe_value must run first"
            )


def _render(*, rows: list[dict[str, Any]], blob: bytes, binding: Mapping[str, Any],
            output: Path, status: Path, field_transform_mode: bool = False,
            unsigned_encoding_audit: bool = False) -> str:
    row_text = ",\n".join(
        "{%du,%du,%du,%du,%du,%du,%du,%du,%du,%du,%du,%du,%du,%du,%du,%dull,%dull,%dull,%dull,%dull,%dull,%dull,%dull,%dull,%dull,%du,%du}"
        % (
            row["message_type_index"], row["field_index"], row["field_offset"],
            row["auxiliary_offset"], row["width"], row["role_kind"],
            row["method_ordinal"], row["method_count"], row["key_kind"],
            row["positive_start"], row["positive_bytes"], row["negative_start"],
            row["negative_bytes"], row["field_number"], row["map_value_kind"],
            row["message_descriptor"], row["field_pointer"],
            row["key_class"], row["signed_class"], row["positive_hash"],
            row["negative_hash"], row["key_width"], row["strategy"],
            row["positive_value_bits"], row["negative_value_bits"],
            row["init_start"], row["init_bytes"],
        ) for row in rows
    )
    blob_text = ",".join(str(value) for value in blob) or "0"
    ext = binding["extensions"]
    field_from_handle = binding["field_from_handle"]
    field_name = binding["field_name"]
    resolved_skip = "" if field_transform_mode else (
        "if(role_resolved){o->positive_hash=r->positive_hash;"
        "o->negative_hash=r->negative_hash;o->failure_kind=200u;failures++;continue;}"
    )
    value_check = "" if field_transform_mode else (
        "||((r->reserved&&r->reserved!=5u)?(o->positive_observed!=123||o->negative_observed!=-123):"
        "o->positive_observed==o->negative_observed)" if unsigned_encoding_audit
        else "||o->positive_observed!=123||o->negative_observed!=-123"
    )
    negative_observation = "observe(r,1,&o->negative_observed,&o->negative_hash)"
    if not unsigned_encoding_audit:
        negative_observation = "a?0:" + negative_observation
    probe_failure = ("200u" if unsigned_encoding_audit
                     else "(uint32_t)(a?a:(b?100+b:200))")
    unsigned_roundtrip = (
        "if(r->reserved!=5u){uintptr_t roundtrip_array=0;uint64_t roundtrip_length=0;"
        "if(!serialize_message(message,&roundtrip_array,&roundtrip_length)"
        "||roundtrip_length!=n||memcmp((const void*)(roundtrip_array+object_header_bytes+16u),raw,n))return 16;}"
        if unsigned_encoding_audit else ""
    )
    resolved_set = "" if field_transform_mode else "else role_resolved=1;"
    quarantine_type = (
        "" if unsigned_encoding_audit else
        "terminated_target=inputs[cursor].message_type_index;"
    )
    no_canary = (
        "health_pending=1u;continue;" if unsigned_encoding_audit else
        "dispatch_stage=4u;last_batch_ms=GetTickCount()-started;"
        "subclass_intact=(GetWindowLongPtrW(s.window,GWLP_WNDPROC)==(LONG_PTR)(uintptr_t)window_proc);ok=0;break;"
    )
    oneof_writer = ""
    oneof_dispatch = ""
    if any(row["strategy"] == 10 for row in rows):
        oneof_writer = r"""
static int observe_oneof_write(const input_record*r,uintptr_t message,int64_t wanted,const unsigned char*raw,uint32_t n,int64_t*out){
 uintptr_t before_array=0,array=0;uint64_t before_length=0,length=0;
 writer_step=1u;if(!serialize_message(message,&before_array,&before_length))return 14;
 writer_step|=2u;uintptr_t boxed=box(r->signed_class,wanted,r->width);
 if(!boxed||!writable(message+r->field_offset,8u)||!writable(message+r->auxiliary_offset,4u))return 5;
 memcpy((void*)(message+r->field_offset),&boxed,8u);memcpy((void*)(message+r->auxiliary_offset),&r->field_number,4u);
 writer_step|=4u;uintptr_t stored=0;uint32_t discriminator=0;int64_t member=0;SIZE_T width=r->width==32u?4u:8u;
 memcpy(&stored,(void*)(message+r->field_offset),8u);memcpy(&discriminator,(void*)(message+r->auxiliary_offset),4u);
 if(stored!=boxed||discriminator!=r->field_number||!readable(stored+object_header_bytes,width))return 17;
 memcpy(&member,(void*)(stored+object_header_bytes),width);
 if(width==4u){member&=0xFFFFFFFFll;wanted&=0xFFFFFFFFll;}if(member!=wanted)return 17;
 writer_step|=8u;if(!serialize_message(message,&array,&length))return 14;writer_step|=16u;
 const unsigned char*before=before_length?(const unsigned char*)(before_array+object_header_bytes+16u):NULL;
 const unsigned char*after=length?(const unsigned char*)(array+object_header_bytes+16u):NULL;
 if(!exact_field_replacement(before,(SIZE_T)before_length,after,(SIZE_T)length,raw,n,r->field_number))return 16;
 *out=member;return 0;
}
"""
        oneof_dispatch = "if(r->role_kind==5u&&r->reserved==10u)return observe_oneof_write(r,message,wanted,raw,n,out);"
    if any(row["strategy"] == 11 for row in rows):
        oneof_writer += r"""
static int observe_string_map_key(const input_record*r,uintptr_t message,int64_t wanted,const unsigned char*raw,uint32_t n,int64_t*out){
 uintptr_t before_array=0,array=0;uint64_t before_length=0,length=0;
 int baseline_valid=0;writer_step=0u;
 if(r->message_type_index!=baseline_skip_target&&(baseline_skip_unit==UINT32_MAX||r!=&inputs[baseline_skip_unit])){writer_step=64u;baseline_valid=serialize_message(message,&before_array,&before_length);writer_step=0u;}
 static_twoarg from_handle=(static_twoarg)field_from_handle_pointer;onearg name=(onearg)field_name_pointer;
 uintptr_t field=from_handle(r->field_pointer,r->message_descriptor,field_from_handle_metadata);
 uintptr_t value=field?name(field,field_name_metadata):0;
 int32_t chars=0;if(!value||!readable(value+object_header_bytes,4u))return 14;
 memcpy(&chars,(void*)(value+object_header_bytes),4u);
 if(chars<=0||chars>524288||!readable(value+object_header_bytes+4u,(SIZE_T)chars*2u))return 14;
 const WCHAR*text=(const WCHAR*)(value+object_header_bytes+4u);
 int bytes=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,text,chars,NULL,0,NULL,NULL);
 if(bytes<=0||bytes>1048576)return 14;
 unsigned char*utf8=(unsigned char*)HeapAlloc(GetProcessHeap(),0,(SIZE_T)bytes);if(!utf8)return 14;
 if(WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,text,chars,(char*)utf8,bytes,NULL,NULL)!=bytes){HeapFree(GetProcessHeap(),0,utf8);return 14;}
 unsigned char*expected=NULL;SIZE_T expected_n=0;
 int built=message_map_key_payload(r,raw,n,utf8,(SIZE_T)bytes,&expected,&expected_n);HeapFree(GetProcessHeap(),0,utf8);
 if(!built)return 16;
 uintptr_t collection=0,pointer=0,metadata=0,boxed_key=key_object(r,wanted);
 if(!boxed_key||!readable(message+r->field_offset,8u)){HeapFree(GetProcessHeap(),0,expected);return 9;}
 memcpy(&collection,(void*)(message+r->field_offset),8u);
 if(!collection||!method_at(collection,r->auxiliary_offset,r->method_count,&pointer,&metadata)){HeapFree(GetProcessHeap(),0,expected);return 12;}
 uintptr_t key=r->width==32u?(uintptr_t)(uint32_t)wanted:(uintptr_t)wanted;
 writer_step=1u;((map_add)pointer)(collection,key,value,metadata);writer_step=3u;
 if(!method_at(collection,r->method_ordinal,r->method_count,&pointer,&metadata)){HeapFree(GetProcessHeap(),0,expected);return 12;}
 if(((map_getitem)pointer)(collection,boxed_key,metadata)!=value){HeapFree(GetProcessHeap(),0,expected);return 17;}
 writer_step=7u;if(!serialize_message(message,&array,&length)){HeapFree(GetProcessHeap(),0,expected);return 14;}writer_step=15u;
 const unsigned char*after=length?(const unsigned char*)(array+object_header_bytes+16u):NULL;
 int matched=(length==expected_n&&!memcmp(after,expected,expected_n))||(baseline_valid&&exact_field_replacement(before_length?(const unsigned char*)(before_array+object_header_bytes+16u):NULL,(SIZE_T)before_length,after,(SIZE_T)length,expected,expected_n,r->field_number));
 HeapFree(GetProcessHeap(),0,expected);if(!matched)return 16;*out=wanted;return 0;
}
"""
        oneof_dispatch += "if(r->role_kind==3u&&r->reserved==11u)return observe_string_map_key(r,message,wanted,raw,n,out);"
    source = f'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#define ALPHA_BATCH {RUNTIME_SIGNED_PARSE_BATCH_ROWS}u
typedef struct input_record{{uint32_t message_type_index,field_index,field_offset,auxiliary_offset,width,role_kind,method_ordinal,method_count,key_kind,positive_start,positive_bytes,negative_start,negative_bytes,field_number,map_value_kind;uint64_t message_descriptor,field_pointer,key_class,signed_class,positive_hash,negative_hash,key_width,reserved,positive_value_bits,negative_value_bits;uint32_t init_start,init_bytes;}}input_record;
typedef struct output_header{{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t count,process_id;char executable[64];}}output_header;
typedef struct output_record{{uint32_t row_index,field_index,role_kind,failure_kind;int64_t positive_observed,negative_observed;uint64_t positive_hash,negative_hash;}}output_record;
_Static_assert(sizeof(output_header)=={HEADER.size},"signed parse header");
_Static_assert(sizeof(output_record)=={RECORD.size},"signed parse record");
static const input_record inputs[]={{
{row_text}
}};
static const unsigned char payloads[]={{{blob_text}}};
static output_record records[{len(rows)}u];static const uint32_t input_count={len(rows)}u;
static const DWORD expected_pid={int(binding['process_id'])}u;static const char executable_sha[]="{binding['binary']['sha256']}";
static const uintptr_t type_from_handle_pointer={int(binding['type_from_handle']['pointer'])}ull,type_from_handle_metadata={int(binding['type_from_handle']['metadata'])}ull;
static const uintptr_t activator_pointer={int(binding['message_factory']['pointer'])}ull,activator_metadata={int(binding['message_factory']['metadata'])}ull;
static const uintptr_t array_new_pointer={int(ext['serializer_array_new_pointer'])}ull,byte_array_class_slot={int(ext['serializer_byte_array_class_slot'])}ull;
static const uintptr_t object_new_pointer={int(ext['serializer_object_new_pointer'])}ull,serializer_pointer={int(ext['serializer_method_pointer'])}ull,serializer_metadata={int(ext['serializer_method_metadata'])}ull,merge_pointer={int(ext['merge_method_pointer'])}ull,merge_metadata={int(ext['merge_method_metadata'])}ull;
static const uintptr_t class_get_methods_pointer={int(binding['class_get_methods_pointer'])}ull;static const uint32_t method_pointer_qword={int(binding['method_pointer_qword'])}u,object_header_bytes={int(binding['object_header_bytes'])}u;
static const uintptr_t class_get_fields_pointer={int(binding['class_get_fields_pointer'])}ull;static const uint32_t field_offset_operation={int(binding['field_offset_operation'])}u,field_offset_raw_offset={int(binding['field_offset_raw_offset'])}u,field_offset_key={int(binding['field_offset_key'])}u,field_offset_mask={int(binding['field_offset_mask'])}u;static const int32_t field_offset_adjustment={int(binding['field_offset_adjustment'])};
static const uintptr_t field_from_handle_pointer={int(field_from_handle['pointer'])}ull,field_from_handle_metadata={int(field_from_handle['metadata'])}ull,field_name_pointer={int(field_name['pointer'])}ull,field_name_metadata={int(field_name['metadata'])}ull;
static const wchar_t output_path[]=L"{_c_escape_wide(output)}",status_path[]=L"{_c_escape_wide(status)}";
typedef uintptr_t(*onearg)(uintptr_t,uintptr_t);typedef uintptr_t(*twoarg)(uintptr_t,uintptr_t);typedef uintptr_t(*static_twoarg)(uintptr_t,uintptr_t,uintptr_t);typedef void(*static_void_twoarg)(uintptr_t,uintptr_t,uintptr_t);typedef uintptr_t(*alloc_one)(uintptr_t);typedef uintptr_t(*class_get_methods_fn)(uintptr_t,uintptr_t*);typedef uintptr_t(*class_get_fields_fn)(uintptr_t,uintptr_t*);typedef uintptr_t(*map_getitem)(uintptr_t,uintptr_t,uintptr_t);typedef float(*map_getitem_float)(uintptr_t,uintptr_t,uintptr_t);typedef double(*map_getitem_double)(uintptr_t,uintptr_t,uintptr_t);typedef void(*map_add)(uintptr_t,uintptr_t,uintptr_t,uintptr_t);
static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_complete;static uint32_t cursor,failures,failure_kind,failure_index,previous_message=UINT32_MAX,previous_field=UINT32_MAX,previous_number=UINT32_MAX,previous_role=UINT32_MAX;static int role_resolved;static uint32_t dispatch_stage,window_count;static DWORD last_batch_ms;static uint32_t proc_calls;static int subclass_intact = -1;
static uint32_t init_retry_unit=UINT32_MAX,init_target=UINT32_MAX,terminated_target=UINT32_MAX,terminated_units,init_retries,last_good_index=UINT32_MAX,health_probe_unit=UINT32_MAX,parse_write_unit=UINT32_MAX,parse_write_target=UINT32_MAX,parse_write_retries,parse_write_rows,writer_step,writer_step_at_failure,health_pending,baseline_skip_unit=UINT32_MAX,baseline_skip_target=UINT32_MAX;static volatile LONG health_probe_result;
static int accessible(uintptr_t p,SIZE_T n,int write){{if(!p||!n||p+n<p)return 0;MEMORY_BASIC_INFORMATION m;if(!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||m.Protect&PAGE_GUARD)return 0;DWORD q=m.Protect&0xffu;int rw=q==PAGE_READWRITE||q==PAGE_WRITECOPY||q==PAGE_EXECUTE_READWRITE||q==PAGE_EXECUTE_WRITECOPY;return (write?rw:(rw||q==PAGE_READONLY||q==PAGE_EXECUTE_READ))&&p+n<=(uintptr_t)m.BaseAddress+m.RegionSize;}}
static int readable(uintptr_t p,SIZE_T n){{return accessible(p,n,0);}}static int writable(uintptr_t p,SIZE_T n){{return accessible(p,n,1);}}
static uint64_t hash_bytes(const unsigned char*d,SIZE_T n){{uint64_t h=1469598103934665603ull;for(SIZE_T i=0;i<n;i++){{h^=d[i];h*=1099511628211ull;}}return h;}}
typedef struct wire_span{{uint32_t number,wire;SIZE_T begin,end;}}wire_span;
static int wire_varint(const unsigned char*d,SIZE_T n,uint64_t*out,SIZE_T*used){{uint64_t value=0;for(SIZE_T i=0;i<n&&i<10u;i++){{unsigned char byte=d[i];value|=(uint64_t)(byte&0x7fu)<<(i*7u);if(!(byte&0x80u)){{*out=value;*used=i+1u;return 1;}}}}return 0;}}
static int wire_spans(const unsigned char*d,SIZE_T n,wire_span*out,uint32_t capacity,uint32_t*count){{SIZE_T cursor=0;uint32_t found=0;while(cursor<n){{if(found>=capacity)return 0;SIZE_T begin=cursor,used=0;uint64_t tag=0,value=0;if(!wire_varint(d+cursor,n-cursor,&tag,&used)||!(tag>>3u)||(tag>>3u)>0x1fffffffu)return 0;cursor+=used;uint32_t wire=(uint32_t)(tag&7u);if(wire==0u){{if(!wire_varint(d+cursor,n-cursor,&value,&used))return 0;cursor+=used;}}else if(wire==1u){{if(n-cursor<8u)return 0;cursor+=8u;}}else if(wire==2u){{if(!wire_varint(d+cursor,n-cursor,&value,&used)||value>n-cursor-used)return 0;cursor+=used+(SIZE_T)value;}}else if(wire==5u){{if(n-cursor<4u)return 0;cursor+=4u;}}else return 0;out[found].number=(uint32_t)(tag>>3u);out[found].wire=wire;out[found].begin=begin;out[found].end=cursor;found++;}}*count=found;return 1;}}
static int no_target_field(const unsigned char*data,SIZE_T n,uint32_t number){{if(!n)return 1;if(n>UINT32_MAX*2ull-2ull)return 0;uint32_t capacity=(uint32_t)(n/2u)+1u,count=0;wire_span*spans=(wire_span*)HeapAlloc(GetProcessHeap(),HEAP_ZERO_MEMORY,(SIZE_T)capacity*sizeof(wire_span));if(!spans)return 0;int ok=wire_spans(data,n,spans,capacity,&count);for(uint32_t i=0;ok&&i<count;i++)if(spans[i].number==number)ok=0;HeapFree(GetProcessHeap(),0,spans);return ok;}}
static int exact_field_replacement(const unsigned char*before,SIZE_T before_n,const unsigned char*after,SIZE_T after_n,const unsigned char*raw,SIZE_T raw_n,uint32_t number){{SIZE_T largest=before_n>after_n?before_n:after_n;if(largest>UINT32_MAX*2ull-2ull)return 0;uint32_t capacity=(uint32_t)(largest/2u)+1u;wire_span*a=(wire_span*)HeapAlloc(GetProcessHeap(),HEAP_ZERO_MEMORY,(SIZE_T)capacity*sizeof(wire_span));wire_span*b=(wire_span*)HeapAlloc(GetProcessHeap(),HEAP_ZERO_MEMORY,(SIZE_T)capacity*sizeof(wire_span));wire_span candidate[2];uint32_t ac=0,bc=0,cc=0;int result=0;if(!a||!b)goto done;if((before_n&&!wire_spans(before,before_n,a,capacity,&ac))||(after_n&&!wire_spans(after,after_n,b,capacity,&bc))||(raw_n&&(!wire_spans(raw,raw_n,candidate,2u,&cc)||cc!=1u||candidate[0].begin||candidate[0].end!=raw_n||candidate[0].number!=number)))goto done;uint32_t ai=0,bi=0,before_target=0,after_target=0;while(ai<ac||bi<bc){{while(ai<ac&&a[ai].number==number){{before_target++;ai++;}}while(bi<bc&&b[bi].number==number){{SIZE_T bytes=b[bi].end-b[bi].begin;if(bytes!=raw_n||memcmp(after+b[bi].begin,raw,raw_n))goto done;after_target++;bi++;}}if(ai==ac||bi==bc)break;SIZE_T an=a[ai].end-a[ai].begin,bn=b[bi].end-b[bi].begin;if(an!=bn||memcmp(before+a[ai].begin,after+b[bi].begin,an))goto done;ai++;bi++;}}while(ai<ac&&a[ai].number==number){{before_target++;ai++;}}while(bi<bc&&b[bi].number==number){{SIZE_T bytes=b[bi].end-b[bi].begin;if(bytes!=raw_n||memcmp(after+b[bi].begin,raw,raw_n))goto done;after_target++;bi++;}}result=ai==ac&&bi==bc&&before_target<=1u&&after_target==(raw_n?1u:0u);done:if(a)HeapFree(GetProcessHeap(),0,a);if(b)HeapFree(GetProcessHeap(),0,b);return result;}}
static int method_at(uintptr_t object,uint32_t ordinal,uint32_t count,uintptr_t*pointer,uintptr_t*metadata){{uintptr_t klass=0,iterator=0;if(ordinal>=count||!readable(object,8u))return 0;memcpy(&klass,(void*)object,8u);class_get_methods_fn get=(class_get_methods_fn)class_get_methods_pointer;uintptr_t method=0;for(uint32_t i=0;i<=ordinal;i++){{method=get(klass,&iterator);if(!method)return 0;}}if(!readable(method+(uintptr_t)method_pointer_qword*8u,8u))return 0;memcpy(pointer,(void*)(method+(uintptr_t)method_pointer_qword*8u),8u);*metadata=method;return *pointer!=0;}}
static int field_address(uintptr_t object,uint32_t ordinal,uintptr_t*out){{uintptr_t klass=0,iterator=0,field=0;if(!object||!readable(object,8u))return 0;memcpy(&klass,(void*)object,8u);if(!klass)return 0;class_get_fields_fn get=(class_get_fields_fn)class_get_fields_pointer;for(uint32_t i=0;i<=ordinal;i++){{field=get(klass,&iterator);if(!field)return 0;}}uint32_t raw=0,value=0;if(!readable(field,32u)||field_offset_raw_offset+4u>32u)return 0;memcpy(&raw,(void*)(field+field_offset_raw_offset),4u);if(field_offset_operation==1u)value=raw^field_offset_key;else if(field_offset_operation==2u)value=raw+field_offset_key;else if(field_offset_operation==3u)value=raw-field_offset_key;else return 0;value&=field_offset_mask;int64_t normalized=(int64_t)value+(int64_t)field_offset_adjustment;if(normalized<0||normalized>INT32_MAX-(int32_t)object_header_bytes)return 0;*out=object+(uintptr_t)normalized+object_header_bytes;return writable(*out,8u);}}
static int repeated_count_is(const input_record*r,uintptr_t message,uint32_t expected){{uintptr_t collection=0,address=0;uint32_t count=0;if(!readable(message+r->field_offset,8u))return 0;memcpy(&collection,(void*)(message+r->field_offset),8u);if(!collection||!field_address(collection,r->method_count,&address))return 0;memcpy(&count,(void*)address,4u);return count==expected;}}
static int repeated_scalar(const input_record*r,uintptr_t object,int64_t*out){{uintptr_t array_address=0,count_address=0,array=0;uint32_t count=0;int64_t selected=0;SIZE_T width=r->width==32u?4u:8u;if(!field_address(object,r->method_ordinal,&array_address)||!field_address(object,r->method_count,&count_address))return 0;memcpy(&array,(void*)array_address,8u);memcpy(&count,(void*)count_address,4u);if(count!=1u||!array||!readable(array+object_header_bytes+16u,width)){{*out=0;return 1;}}memcpy(&selected,(void*)(array+object_header_bytes+16u),width);if(width==4u)selected=(int32_t)selected;*out=selected;return 1;}}
static int serialize_message(uintptr_t message,uintptr_t*out_array,uint64_t*out_length){{onearg serialize=(onearg)serializer_pointer;uintptr_t output=serialize(message,serializer_metadata);uint64_t length=0;if(!output||!readable(output+object_header_bytes+8u,8u))return 0;memcpy(&length,(void*)(output+object_header_bytes+8u),8u);if(length>1048576u||(length&&!readable(output+object_header_bytes+16u,(SIZE_T)length)))return 0;*out_array=output;*out_length=length;return 1;}}
static int observe_singular_write(const input_record*r,uintptr_t message,int64_t wanted,const unsigned char*raw,uint32_t n,int64_t*out){{uintptr_t before_array=0,array=0;uint64_t before_length=0,length=0;writer_step=1u;if(!serialize_message(message,&before_array,&before_length))return 14;writer_step|=2u;SIZE_T width=r->width==32u?4u:8u;int parse_write=(r->message_type_index==parse_write_target)||(r==&inputs[cursor]&&(uint32_t)cursor==parse_write_unit);if(parse_write){{if(r->reserved==5u&&r->role_kind==2u&&!repeated_count_is(r,message,0u))return 18;uintptr_t byte_class=0;if(!readable(byte_array_class_slot,8u))return 3;memcpy(&byte_class,(void*)byte_array_class_slot,8u);twoarg write_array_new=(twoarg)array_new_pointer;uintptr_t write_input=write_array_new(byte_class,n);if(!write_input||!writable(write_input+object_header_bytes+16u,n))return 4;memcpy((void*)(write_input+object_header_bytes+16u),raw,n);((static_void_twoarg)merge_pointer)(message,write_input,merge_metadata);writer_step|=4u;if(!readable(message+r->field_offset,width))return 5;int64_t member=0;memcpy(&member,(void*)(message+r->field_offset),width);if(width==4u)member&=0xFFFFFFFFll;if(member!=wanted)return 17;writer_step|=8u;}}else{{if(!writable(message+r->field_offset,width))return 5;memcpy((void*)(message+r->field_offset),&wanted,width);writer_step|=4u;}}if(!serialize_message(message,&array,&length))return 14;writer_step|=16u;const unsigned char*before=before_length?(const unsigned char*)(before_array+object_header_bytes+16u):NULL;const unsigned char*serialized=length?(const unsigned char*)(array+object_header_bytes+16u):NULL;if(exact_field_replacement(before,(SIZE_T)before_length,serialized,(SIZE_T)length,raw,n,r->field_number)||(wanted==0&&no_target_field(serialized,(SIZE_T)length,r->field_number)&&exact_field_replacement(before,(SIZE_T)before_length,serialized,(SIZE_T)length,NULL,0u,r->field_number))){{*out=wanted;if(parse_write)parse_write_rows++;}}else{{if({int(field_transform_mode or unsigned_encoding_audit)}u)return 16;int64_t diagnostic=0;if(length)memcpy(&diagnostic,serialized,length<8u?(SIZE_T)length:8u);*out=diagnostic;}}return 0;}}
static int observe_repeated(const input_record*r,uintptr_t message,int64_t wanted,const unsigned char*raw,uint32_t n,int64_t*out){{uintptr_t baseline_array=0;uint64_t baseline_length=0;int baseline_valid=0;writer_step=0u;if(r->reserved==6u&&r->message_type_index!=baseline_skip_target&&(baseline_skip_unit==UINT32_MAX||r!=&inputs[baseline_skip_unit])){{writer_step=64u;baseline_valid=serialize_message(message,&baseline_array,&baseline_length);writer_step=0u;}}uintptr_t collection=0;if(!readable(message+r->field_offset,8u))return 9;memcpy(&collection,(void*)(message+r->field_offset),8u);if(!collection)return 10;uintptr_t pointer=0,metadata=0;if(!r->key_width||r->key_width>UINT32_MAX||!method_at(collection,r->key_kind,(uint32_t)r->key_width,&pointer,&metadata))return 12;if(r->map_value_kind==1u){{uint32_t bits=(uint32_t)wanted;float value;memcpy(&value,&bits,4u);((void(*)(uintptr_t,float,uintptr_t))pointer)(collection,value,metadata);}}else if(r->map_value_kind==2u){{double value;memcpy(&value,&wanted,8u);((void(*)(uintptr_t,double,uintptr_t))pointer)(collection,value,metadata);}}else ((void(*)(uintptr_t,uintptr_t,uintptr_t))pointer)(collection,(uintptr_t)wanted,metadata);uintptr_t array=0;uint64_t length=0;if(!serialize_message(message,&array,&length))return 14;if(length>SIZE_MAX-object_header_bytes-16u||!readable(array+object_header_bytes+16u,length))return 15;const unsigned char*serialized=(const unsigned char*)(array+object_header_bytes+16u);if((length==n&&!memcmp(serialized,raw,n))||(baseline_valid&&exact_field_replacement(baseline_length?(const unsigned char*)(baseline_array+object_header_bytes+16u):NULL,(SIZE_T)baseline_length,serialized,(SIZE_T)length,raw,n,r->field_number)))*out=wanted;else{{if({int(field_transform_mode or unsigned_encoding_audit)}u)return 16;int64_t diagnostic=0;memcpy(&diagnostic,serialized,length<8u?(SIZE_T)length:8u);*out=diagnostic;}}return 0;}}
static uintptr_t box(uintptr_t klass,int64_t value,uint32_t width){{alloc_one object_new=(alloc_one)object_new_pointer;uintptr_t object=object_new(klass);SIZE_T n=width==32u?4u:8u;if(!object||!writable(object+object_header_bytes,n))return 0;memcpy((void*)(object+object_header_bytes),&value,n);return object;}}
static uintptr_t key_object(const input_record*r,int64_t signed_value){{int64_t raw=r->role_kind==3u?signed_value:1;if(r->key_kind==1u){{static_twoarg from_handle=(static_twoarg)field_from_handle_pointer;onearg name=(onearg)field_name_pointer;uintptr_t field=from_handle(r->field_pointer,r->message_descriptor,field_from_handle_metadata);return field?name(field,field_name_metadata):0;}}if(r->key_kind==2u)return box(r->key_class,raw,(uint32_t)r->key_width);return r->role_kind==3u?box(r->signed_class,signed_value,r->width):0;}}
static int observe_map(const input_record*r,uintptr_t message,int64_t wanted,const unsigned char*raw,uint32_t n,int64_t*out){{uintptr_t baseline_array=0;uint64_t baseline_length=0;int baseline_valid=0;writer_step=0u;if(r->reserved==7u&&r->message_type_index!=baseline_skip_target&&(baseline_skip_unit==UINT32_MAX||r!=&inputs[baseline_skip_unit])){{writer_step=64u;baseline_valid=serialize_message(message,&baseline_array,&baseline_length);writer_step=0u;}}uintptr_t collection=0,pointer=0,metadata=0,key=0;if(!readable(message+r->field_offset,8u))return 9;memcpy(&collection,(void*)(message+r->field_offset),8u);if(!collection)return 10;if(!method_at(collection,r->auxiliary_offset,r->method_count,&pointer,&metadata))return 12;if(r->key_kind==1u)key=key_object(r,wanted);else if(r->key_kind==2u)key=1u;else return 13;if(!key)return 13;uintptr_t value=r->width==32u?(uintptr_t)(uint32_t)(int32_t)wanted:(uintptr_t)wanted;((map_add)pointer)(collection,key,value,metadata);uintptr_t array=0;uint64_t length=0;if(!serialize_message(message,&array,&length))return 14;const unsigned char*serialized=(const unsigned char*)(array+object_header_bytes+16u);if((length==n&&!memcmp(serialized,raw,n))||(baseline_valid&&exact_field_replacement(baseline_length?(const unsigned char*)(baseline_array+object_header_bytes+16u):NULL,(SIZE_T)baseline_length,serialized,(SIZE_T)length,raw,n,r->field_number)))*out=wanted;else{{if({int(field_transform_mode or unsigned_encoding_audit)}u)return 16;int64_t diagnostic=0;memcpy(&diagnostic,serialized,length<8u?(SIZE_T)length:8u);*out=diagnostic;}}return 0;}}
static uint32_t put_varint(unsigned char*out,uint64_t value){{uint32_t n=0;do{{out[n]=(unsigned char)(value&127u);value>>=7u;if(value)out[n]|=128u;n++;}}while(value);return n;}}
static int message_map_key_payload(const input_record*r,const unsigned char*raw,uint32_t n,const unsigned char*child,SIZE_T child_n,unsigned char**out,SIZE_T*out_n){{wire_span outer[2],entry[3];uint32_t oc=0,ec=0;SIZE_T used=0,tag_n=0;uint64_t tag=0,entry_n=0;if(!wire_spans(raw,n,outer,2u,&oc)||oc!=1u||outer[0].number!=r->field_number||outer[0].wire!=2u||!wire_varint(raw,n,&tag,&tag_n)||!wire_varint(raw+tag_n,n-tag_n,&entry_n,&used)||entry_n!=n-tag_n-used)return 0;const unsigned char*data=raw+tag_n+used;if(!wire_spans(data,(SIZE_T)entry_n,entry,3u,&ec))return 0;const unsigned char*key=NULL;SIZE_T key_n=0;uint32_t values=0;for(uint32_t i=0;i<ec;i++){{SIZE_T bytes=entry[i].end-entry[i].begin;if(entry[i].number==1u&&!key){{key=data+entry[i].begin;key_n=bytes;}}else if(entry[i].number==2u&&entry[i].wire==2u&&bytes==2u&&data[entry[i].begin]==0x12u&&data[entry[i].begin+1u]==0u)values++;else return 0;}}if(values!=1u||child_n>1048576u)return 0;unsigned char*out_data=(unsigned char*)HeapAlloc(GetProcessHeap(),0,key_n+child_n+32u);if(!out_data)return 0;unsigned char length[10];uint32_t ln=put_varint(length,child_n);SIZE_T body_n=key_n+1u+ln+child_n,cursor=put_varint(out_data,((uint64_t)r->field_number<<3u)|2u);cursor+=put_varint(out_data+cursor,body_n);if(key_n){{memcpy(out_data+cursor,key,key_n);cursor+=key_n;}}out_data[cursor++]=0x12u;memcpy(out_data+cursor,length,ln);cursor+=ln;if(child_n){{memcpy(out_data+cursor,child,child_n);cursor+=child_n;}}*out=out_data;*out_n=cursor;return 1;}}
static int observe_map_key(const input_record*r,uintptr_t message,int64_t wanted,const unsigned char*raw,uint32_t n,int64_t*out){{uintptr_t baseline_array=0;uint64_t baseline_length=0;int baseline_valid=0;writer_step=0u;if((r->reserved==8u||r->reserved==9u)&&r->message_type_index!=baseline_skip_target&&(baseline_skip_unit==UINT32_MAX||r!=&inputs[baseline_skip_unit])){{writer_step=64u;baseline_valid=serialize_message(message,&baseline_array,&baseline_length);writer_step=0u;}}uintptr_t collection=0,pointer=0,metadata=0;if(!readable(message+r->field_offset,8u))return 9;memcpy(&collection,(void*)(message+r->field_offset),8u);if(!collection)return 10;if(!method_at(collection,r->auxiliary_offset,r->method_count,&pointer,&metadata))return 12;uintptr_t key=r->width==32u?(uintptr_t)(uint32_t)wanted:(uintptr_t)wanted;uintptr_t value=0,child_array=0;uint64_t child_length=0;if(r->reserved==9u){{onearg get_type=(onearg)type_from_handle_pointer,create=(onearg)activator_pointer;uintptr_t type=get_type(r->signed_class,type_from_handle_metadata);value=type?create(type,activator_metadata):0;if(!value||!serialize_message(value,&child_array,&child_length))return 14;}}((map_add)pointer)(collection,key,value,metadata);if(r->reserved==9u){{uintptr_t getter=0,getter_metadata=0,boxed_key=key_object(r,wanted);if(!boxed_key||!method_at(collection,r->method_ordinal,r->method_count,&getter,&getter_metadata))return 12;uintptr_t stored=((map_getitem)getter)(collection,boxed_key,getter_metadata);if(stored!=value)return 17;}}uintptr_t array=0;uint64_t length=0;if(!serialize_message(message,&array,&length))return 14;const unsigned char*serialized=(const unsigned char*)(array+object_header_bytes+16u);if(r->reserved==9u){{unsigned char*expected=NULL;SIZE_T expected_n=0;const unsigned char*child=child_length?(const unsigned char*)(child_array+object_header_bytes+16u):NULL;if(!message_map_key_payload(r,raw,n,child,(SIZE_T)child_length,&expected,&expected_n))return 16;int matched=(length==expected_n&&!memcmp(serialized,expected,expected_n))||(baseline_valid&&exact_field_replacement(baseline_length?(const unsigned char*)(baseline_array+object_header_bytes+16u):NULL,(SIZE_T)baseline_length,serialized,(SIZE_T)length,expected,expected_n,r->field_number));HeapFree(GetProcessHeap(),0,expected);if(!matched)return 16;*out=wanted;return 0;}}if(!((length==n&&!memcmp(serialized,raw,n))||(baseline_valid&&exact_field_replacement(baseline_length?(const unsigned char*)(baseline_array+object_header_bytes+16u):NULL,(SIZE_T)baseline_length,serialized,(SIZE_T)length,raw,n,r->field_number))))return 16;*out=wanted;return 0;}}
{oneof_writer}static int observe(const input_record*r,int negative,int64_t*out,uint64_t*observed_hash){{uint32_t start=negative?r->negative_start:r->positive_start,n=negative?r->negative_bytes:r->positive_bytes;uint64_t wanted_bits=negative?r->negative_value_bits:r->positive_value_bits;int64_t wanted=0;memcpy(&wanted,&wanted_bits,sizeof(wanted));if((uint64_t)start+n>sizeof(payloads))return 1;const unsigned char*raw=payloads+start;*observed_hash=hash_bytes(raw,n);onearg get_type=(onearg)type_from_handle_pointer,create=(onearg)activator_pointer;uintptr_t type=get_type(r->message_descriptor,type_from_handle_metadata);uintptr_t message=type?create(type,activator_metadata):0;if(!message)return 2;if(r->init_bytes&&r==&inputs[cursor]&&((uint32_t)cursor==init_retry_unit||r->message_type_index==init_target)){{uintptr_t init_byte_class=0;if(!readable(byte_array_class_slot,8u))return 3;memcpy(&init_byte_class,(void*)byte_array_class_slot,8u);twoarg init_array_new=(twoarg)array_new_pointer;uintptr_t init_input=init_array_new(init_byte_class,r->init_bytes);if(!init_input||!writable(init_input+object_header_bytes+16u,r->init_bytes))return 4;const unsigned char*init_data=payloads+r->init_start;memcpy((void*)(init_input+object_header_bytes+16u),init_data,r->init_bytes);((static_void_twoarg)merge_pointer)(message,init_input,merge_metadata);}}{oneof_dispatch}if(r->role_kind==2u&&(r->reserved==1u||r->reserved==6u))return observe_repeated(r,message,wanted,raw,n,out);if(r->role_kind==1u&&r->reserved==2u)return observe_singular_write(r,message,wanted,raw,n,out);if(r->role_kind==4u&&(r->reserved==3u||r->reserved==7u))return observe_map(r,message,wanted,raw,n,out);if(r->role_kind==3u&&(r->reserved==4u||r->reserved==8u||r->reserved==9u))return observe_map_key(r,message,wanted,raw,n,out);if(r->reserved==5u&&r->role_kind==2u&&!repeated_count_is(r,message,0u))return 18;uintptr_t byte_class=0;if(!readable(byte_array_class_slot,8u))return 3;memcpy(&byte_class,(void*)byte_array_class_slot,8u);twoarg array_new=(twoarg)array_new_pointer;uintptr_t input=array_new(byte_class,n);if(!input||!writable(input+object_header_bytes+16u,n))return 4;memcpy((void*)(input+object_header_bytes+16u),raw,n);((static_void_twoarg)merge_pointer)(message,input,merge_metadata);if(r->reserved==5u&&r->role_kind==2u&&!repeated_count_is(r,message,1u))return 18;{unsigned_roundtrip}if(r->role_kind==1u){{SIZE_T width=r->width==32u?4u:8u;if(!readable(message+r->field_offset,width))return 5;int64_t value=0;memcpy(&value,(void*)(message+r->field_offset),width);if(width==4u)value=(int32_t)value;*out=value;return 0;}}if(r->role_kind==5u){{uintptr_t object=0;int32_t discriminator=0;if(!readable(message+r->field_offset,8u)||!readable(message+r->auxiliary_offset,4u))return 6;memcpy(&object,(void*)(message+r->field_offset),8u);memcpy(&discriminator,(void*)(message+r->auxiliary_offset),4u);SIZE_T width=r->width==32u?4u:8u;if(discriminator!=(int32_t)r->field_number||!object){{*out=0;return 0;}}if(!readable(object+object_header_bytes,width))return 8;int64_t value=0;memcpy(&value,(void*)(object+object_header_bytes),width);if(width==4u)value=(int32_t)value;*out=value;return 0;}}uintptr_t collection=0;if(!readable(message+r->field_offset,8u))return 9;memcpy(&collection,(void*)(message+r->field_offset),8u);if(!collection)return 10;if(r->role_kind==2u){{return repeated_scalar(r,collection,out)?0:11;}}uintptr_t pointer=0,metadata=0;if(!method_at(collection,r->method_ordinal,r->method_count,&pointer,&metadata))return 12;uintptr_t key=key_object(r,wanted);if(!key)return 13;if(r->role_kind==4u&&r->map_value_kind==1u){{float value=((map_getitem_float)pointer)(collection,key,metadata);uint32_t bits=0;memcpy(&bits,&value,sizeof(bits));*out=(int64_t)bits;return 0;}}if(r->role_kind==4u&&r->map_value_kind==2u){{double value=((map_getitem_double)pointer)(collection,key,metadata);memcpy(out,&value,sizeof(value));return 0;}}uintptr_t value=((map_getitem)pointer)(collection,key,metadata);if(!value)return 14;if(r->role_kind==3u){{*out=wanted;return 0;}}SIZE_T width=r->width==32u?4u:8u;if(!readable(value+object_header_bytes,width))return 15;int64_t scalar=0;memcpy(&scalar,(void*)(value+object_header_bytes),width);if(width==4u)scalar=(int32_t)scalar;*out=scalar;return 0;}}
static int collect(void){{if(health_probe_unit!=UINT32_MAX){{const input_record*h=&inputs[health_probe_unit];int64_t health_value=0;uint64_t health_digest=0;int health_outcome=observe(h,0,&health_value,&health_digest);health_probe_result=(health_outcome==0&&health_digest==records[health_probe_unit].positive_hash&&health_value==records[health_probe_unit].positive_observed)?1:-1;return 1;}}uint32_t end=cursor+(((uint32_t)cursor==init_retry_unit||(uint32_t)cursor==parse_write_unit)?1u:ALPHA_BATCH);if(end>input_count)end=input_count;for(;cursor<end;cursor++){{const input_record*r=&inputs[cursor];output_record*o=&records[cursor];o->row_index=cursor;o->field_index=r->field_index;o->role_kind=r->role_kind;if(r->message_type_index!=previous_message||r->field_index!=previous_field||r->field_number!=previous_number||r->role_kind!=previous_role){{previous_message=r->message_type_index;previous_field=r->field_index;previous_number=r->field_number;previous_role=r->role_kind;role_resolved=0;}}{resolved_skip}int a=observe(r,0,&o->positive_observed,&o->positive_hash);int b={negative_observation};if(a||b{value_check}||o->positive_hash!=r->positive_hash||o->negative_hash!=r->negative_hash){{o->failure_kind={probe_failure};failures++;failure_kind=o->failure_kind;failure_index=cursor;}}{resolved_set}if(!o->failure_kind)last_good_index=cursor;}}return 1;}}
static void quarantine_record(uint32_t index){{const input_record*r=&inputs[index];output_record*o=&records[index];o->row_index=index;o->field_index=r->field_index;o->role_kind=r->role_kind;o->failure_kind={WRITER_TERMINATION_FAILURE_KIND}u;o->positive_observed=0;o->negative_observed=0;o->positive_hash=0;o->negative_hash=0;failures++;failure_kind={WRITER_TERMINATION_FAILURE_KIND}u;failure_index=index;terminated_units++;cursor=index+1u;parse_write_unit=UINT32_MAX;}}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){{if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);InterlockedIncrement((LONG*)&proc_calls);int ok=collect();InterlockedExchange(&callback_complete,ok?1:-1);return ok;}}
typedef struct selection{{DWORD pid;HWND window;uint32_t count;}}selection;static BOOL CALLBACK select_window(HWND w,LPARAM v){{selection*s=(selection*)(uintptr_t)v;DWORD pid=0;RECT b;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){{s->window=w;s->count++;}}return TRUE;}}
static int dispatch(void){{selection s={{0}};s.pid=GetCurrentProcessId();for(uint32_t sweep=0;;sweep++){{if(EnumWindows(select_window,(LPARAM)(uintptr_t)&s)&&s.count==1&&s.window)break;window_count=(uint32_t)s.count;dispatch_stage=1;if(sweep>=8u)return 0;Sleep(250);}}window_count=(uint32_t)s.count;message_id=RegisterWindowMessageW(status_path);SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);int ok=message_id&&(original_proc||GetLastError()==ERROR_SUCCESS);if(!ok)dispatch_stage=2;while(ok&&(cursor<input_count||health_probe_unit!=UINT32_MAX)){{if(cursor<input_count&&inputs[cursor].message_type_index==terminated_target){{quarantine_record(cursor);continue;}}uint32_t sent_unit=cursor;uint32_t init_target_at_send=init_target;uint32_t parse_write_target_at_send=parse_write_target;DWORD_PTR proc_before=proc_calls;DWORD_PTR result=0;DWORD started=GetTickCount();InterlockedExchange(&callback_complete,0);if(!SendMessageTimeoutW(s.window,message_id,0,0,SMTO_BLOCK,{RUNTIME_SIGNED_PARSE_SEND_TIMEOUT_MS}u,&result)){{dispatch_stage=3;last_batch_ms=GetTickCount()-started;subclass_intact=(GetWindowLongPtrW(s.window,GWLP_WNDPROC)==(LONG_PTR)(uintptr_t)window_proc);ok=0;break;}}last_batch_ms=GetTickCount()-started;if(health_probe_unit!=UINT32_MAX){{if(InterlockedCompareExchange(&callback_complete,0,0)!=1){{dispatch_stage=(proc_calls>proc_before)?5u:4u;last_batch_ms=GetTickCount()-started;subclass_intact=(GetWindowLongPtrW(s.window,GWLP_WNDPROC)==(LONG_PTR)(uintptr_t)window_proc);ok=0;break;}}if(health_probe_result!=1){{dispatch_stage=5u;last_batch_ms=GetTickCount()-started;subclass_intact=(GetWindowLongPtrW(s.window,GWLP_WNDPROC)==(LONG_PTR)(uintptr_t)window_proc);ok=0;break;}}health_probe_unit=UINT32_MAX;continue;}}if(InterlockedCompareExchange(&callback_complete,0,0)==1){{if(init_retry_unit!=UINT32_MAX&&init_retry_unit>=sent_unit&&init_retry_unit<cursor){{init_target=inputs[init_retry_unit].message_type_index;init_retry_unit=UINT32_MAX;}}if(parse_write_unit!=UINT32_MAX&&parse_write_unit>=sent_unit&&parse_write_unit<cursor){{parse_write_target=inputs[parse_write_unit].message_type_index;parse_write_unit=UINT32_MAX;}}if(health_pending&&last_good_index!=UINT32_MAX){{health_pending=0u;health_probe_unit=last_good_index;health_probe_result=0;}}continue;}}if(proc_calls>proc_before){{writer_step_at_failure=writer_step;if(writer_step==64u&&inputs[cursor].reserved>=6u&&inputs[cursor].reserved<=9u&&inputs[cursor].message_type_index!=baseline_skip_target){{baseline_skip_unit=cursor;baseline_skip_target=inputs[cursor].message_type_index;continue;}}int armed=((uint32_t)init_retry_unit==cursor)||(inputs[cursor].message_type_index==init_target_at_send);int parse_armed=((uint32_t)parse_write_unit==cursor)||(inputs[cursor].message_type_index==parse_write_target_at_send);if(!parse_armed&&inputs[cursor].message_type_index!=terminated_target){{if(!armed){{if(init_target==UINT32_MAX&&init_retry_unit!=UINT32_MAX&&init_retry_unit!=cursor&&init_retry_unit>=sent_unit&&init_retry_unit<cursor){{init_target=inputs[init_retry_unit].message_type_index;}}init_retry_unit=cursor;init_retries++;continue;}}parse_write_unit=cursor;parse_write_retries++;continue;}}quarantine_record(cursor);{quarantine_type}init_retry_unit=UINT32_MAX;parse_write_unit=UINT32_MAX;if(last_good_index==UINT32_MAX){{{no_canary}}}health_probe_unit=last_good_index;health_probe_result=0;continue;}}dispatch_stage=4;last_batch_ms=GetTickCount()-started;subclass_intact=(GetWindowLongPtrW(s.window,GWLP_WNDPROC)==(LONG_PTR)(uintptr_t)window_proc);ok=0;break;}}if(health_pending){{dispatch_stage=5u;ok=0;}}if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);return ok;}}
static void hex(const unsigned char*d,char*o){{static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){{o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}}o[64]=0;}}static int sha(const wchar_t*p,char out[65]){{HANDLE f=CreateFileW(p,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,0,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD n=0,g=0;unsigned char*o=NULL,*b=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&n,sizeof(n),&g,0)>=0;if(ok)o=HeapAlloc(GetProcessHeap(),0,n);if(ok)b=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!o||!b))ok=0;if(ok&&BCryptCreateHash(a,&h,o,n,NULL,0,0)<0)ok=0;while(ok){{DWORD z=0;if(!ReadFile(f,b,1048576u,&z,NULL)){{ok=0;break;}}if(!z)break;if(BCryptHashData(h,b,z,0)<0)ok=0;}}if(ok&&BCryptFinishHash(h,d,32,0)<0)ok=0;if(ok)hex(d,out);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(o)HeapFree(GetProcessHeap(),0,o);if(b)HeapFree(GetProcessHeap(),0,b);CloseHandle(f);return ok;}}static int identity(char out[65]){{wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,32768u);return n&&n<32768u&&sha(p,out);}}
static int write_output(void){{output_header h={{0}};memcpy(h.magic,"ALPHASP1",8);h.version=1;h.header_bytes=sizeof(h);h.record_bytes=sizeof(output_record);h.count=input_count;h.process_id=GetCurrentProcessId();memcpy(h.executable,executable_sha,64);FILE*f=_wfopen(output_path,L"wb");int ok=f&&fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(records,sizeof(output_record),input_count,f)==input_count;if(f&&fclose(f))ok=0;if(ok)_wchmod(output_path,0600);else _wremove(output_path);return ok;}}
static void write_status(const char*s,int written){{FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{{\\n  \\"schema\\": \\"{STATUS_SCHEMA}\\",\\n  \\"status\\": \\"%s\\",\\n  \\"process_id\\": %lu,\\n  \\"expected_count\\": %u,\\n  \\"completed_count\\": %u,\\n  \\"failure_count\\": %u,\\n  \\"failure_kind_owner_only\\": %u,\\n  \\"failure_index_owner_only\\": %u,\\n  \\"dispatch_stage_owner_only\\": %u,\\n  \\"window_count_owner_only\\": %u,\\n  \\"last_batch_ms_owner_only\\": %lu,\\n  \\"proc_calls_owner_only\\": %u,\\n  \\"subclass_intact_owner_only\\": %d,\\n  \\"terminated_units_owner_only\\": %u,\\n  \\"init_retry_owner_only\\": %u,\\n  \\"health_probe_owner_only\\": %d,\\n  \\"parse_write_rows_owner_only\\": %u,\\n  \\"parse_write_retries_owner_only\\": %u,\\n  \\"parse_write_target_owner_only\\": %u,\\n  \\"writer_step_owner_only\\": %u,\\n  \\"output_written\\": %s,\\n  \\"fresh_runtime_observation\\": true,\\n  \\"fixed_name_used\\": false,\\n  \\"saved_runtime_pointer_used\\": false,\\n  \\"external_runtime_component_used\\": false\\n}}\\n",s,(unsigned long)GetCurrentProcessId(),input_count,cursor,failures,failure_kind,failure_index,dispatch_stage,window_count,(unsigned long)last_batch_ms,proc_calls,subclass_intact,terminated_units,init_retries,(int)health_probe_result,parse_write_rows,parse_write_retries,parse_write_target,writer_step_at_failure,written?"true":"false");fclose(f);_wchmod(status_path,0600);}}
static DWORD WINAPI worker(LPVOID u){{(void)u;_wremove(output_path);_wremove(status_path);char d[65];if(GetCurrentProcessId()!=expected_pid||!identity(d)||strcmp(d,executable_sha)){{write_status("identity_mismatch",0);return 0;}}int ok=dispatch();if(!ok){{write_status("capture_failed",0);return 0;}}ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}}BOOL WINAPI DllMain(HINSTANCE m,DWORD r,LPVOID z){{(void)z;if(r==DLL_PROCESS_ATTACH){{DisableThreadLibraryCalls(m);HANDLE t=CreateThread(NULL,0,worker,NULL,0,NULL);if(t)CloseHandle(t);}}return TRUE;}}
'''
    if any(row["strategy"] == 11 for row in rows):
        source = source.replace("inputs[cursor].reserved>=6u&&inputs[cursor].reserved<=9u",
                                "((inputs[cursor].reserved>=6u&&inputs[cursor].reserved<=9u)||inputs[cursor].reserved==11u)")
    return source


class _PinnedShardInputs:

    def __init__(self, *, snapshot: RuntimeSnapshot, snapshot_identity: dict[str, Any]):
        self.snapshot = snapshot
        self.snapshot_identity = snapshot_identity
        self._models = {}
        self._runtime_cached = None
        self._roles = {}

    def roles(self, model, *, transform_mode, unsigned_encoding_audit):
        key = (id(model), transform_mode, unsigned_encoding_audit)
        cached = self._roles.get(key)
        if cached is not None and cached[0] is model:
            return cached[1]
        roles = (_field_transform_role_inventory(model) if transform_mode else
                 _unsigned_roles(model) if unsigned_encoding_audit else _pending_roles(model))
        self._roles[key] = (model, roles)
        return roles

    def model(self, path: Path):
        identity = file_identity(path)
        cached = self._models.get(str(path))
        if cached is not None and cached[0] == identity:
            return cached[1]
        model = read_private_model(path)
        if file_identity(path) != identity:
            raise AcquisitionError("pinned shard model changed while reading")
        self._models[str(path)] = (identity, model)
        return model

    def runtime(self, path: Path):
        receipt_identity = file_identity(path)
        if self._runtime_cached is not None:
            cached_key, cached_runtime = self._runtime_cached
            paths = cached_runtime[1]
            key = (receipt_identity, {name: file_identity(value) for name, value in paths.items()})
            if cached_key == key:
                return cached_runtime


        from alpha.p29 import _validated_native_receipt
        _, paths = _validated_native_receipt(path, allow_type_method_metadata=True)
        key = (receipt_identity, {name: file_identity(value) for name, value in paths.items()})
        runtime = _runtime(path)
        after = (file_identity(path), {name: file_identity(value) for name, value in runtime[1].items()})
        if key != after:
            raise AcquisitionError("pinned runtime inventory changed while reading")
        self._runtime_cached = (key, runtime)
        return runtime

    def close(self) -> None:
        try:
            self.snapshot.close()
        except (OSError, ValueError):
            pass


def _open_pinned_shard_inputs(*, snapshot: Path) -> _PinnedShardInputs:
    snapshot_handle = RuntimeSnapshot(_owner_file(snapshot, label="snapshot"))
    return _PinnedShardInputs(
        snapshot=snapshot_handle,
        snapshot_identity=snapshot_handle.sealed_identity(),
    )


def _prepare_signed_parse_materials(
    *, static_model: Path, snapshot: Path, native_output_receipt: Path,
    proto_field_type_model: Path, runtime_materializer_model: Path,
    output_dir: Path,
    pilot_role_kinds: tuple[int, ...] | None = None,
    role_start: int = 0, role_limit: int | None = None,
    field_transform_probe_values: Mapping[int, list[int]] | None = None,
    roundtrip_binding: Mapping[str, Any] | None = None,
    writer_deadly_types: frozenset[int] = frozenset(),
    writer_fallback_roles: frozenset[tuple[Any, ...]] = frozenset(),
    unsigned_encoding_audit: bool = False,
    _pinned: "_PinnedShardInputs | None" = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    if unsigned_encoding_audit and (field_transform_probe_values is not None or pilot_role_kinds is not None):
        raise AcquisitionError("unsigned encoding audit conflicts with capture mode")
    if field_transform_probe_values is not None:
        if (
            pilot_role_kinds is not None
            or not field_transform_probe_values
            or set(field_transform_probe_values) - {32, 64}
        ):
            raise AcquisitionError("runtime field transform probe configuration is invalid")
        value_lengths = set()
        for width, values in field_transform_probe_values.items():
            if (
                not isinstance(values, list) or len(values) < 2 or len(values) % 2
                or any(type(value) is not int or not 0 <= value < 1 << width
                       for value in values)
                or len(set(values)) != len(values)
            ):
                raise AcquisitionError("runtime field transform probe configuration is invalid")
            value_lengths.add(len(values))
        if len(value_lengths) != 1:
            raise AcquisitionError("runtime field transform width sample counts differ")
    model_path = _owner_file(static_model, label="static model")
    model = read_private_model(model_path) if _pinned is None else _pinned.model(model_path)
    if model.get("status") != "complete":
        raise AcquisitionError("runtime signed parse source model is incomplete")
    runtime_context = None if _pinned is None else _pinned.runtime(native_output_receipt)
    binding, live = _bind_current_runtime(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        runtime_materializer_model=runtime_materializer_model,
        roundtrip_binding=roundtrip_binding,
        **({"_runtime_context": runtime_context} if runtime_context is not None else {}),
    )
    try:
        _receipt, paths, runtime = _runtime(native_output_receipt) if runtime_context is None else runtime_context
        if _pinned is not None:
            rows, blob = _rows(model=model, runtime=runtime, live=live,
                               snapshot=_pinned.snapshot, field_types=_field_types(proto_field_type_model),
                               role_start=role_start, role_limit=role_limit,
                               field_transform_probe_values=field_transform_probe_values,
                               writer_deadly_types=writer_deadly_types,
                               writer_fallback_roles=writer_fallback_roles,
                               unsigned_encoding_audit=unsigned_encoding_audit,
                               _role_inventory=_pinned.roles(
                                   model, transform_mode=field_transform_probe_values is not None,
                                   unsigned_encoding_audit=unsigned_encoding_audit))
        else:
            with RuntimeSnapshot(_owner_file(snapshot, label="snapshot")) as memory:
                rows, blob = _rows(model=model, runtime=runtime, live=live,
                                   snapshot=memory, field_types=_field_types(proto_field_type_model),
                                   role_start=role_start, role_limit=role_limit,
                                   field_transform_probe_values=field_transform_probe_values,
                                   writer_deadly_types=writer_deadly_types,
                                   writer_fallback_roles=writer_fallback_roles,
                                   unsigned_encoding_audit=unsigned_encoding_audit)
        if pilot_role_kinds is not None:
            if role_start or role_limit is not None:
                raise AcquisitionError("runtime signed parse pilot and slice conflict")
            requested = tuple(dict.fromkeys(int(kind) for kind in pilot_role_kinds))
            if not requested or any(kind not in ROLE_KIND.values() for kind in requested):
                raise AcquisitionError("runtime signed parse pilot role domain is invalid")
            selected = []
            for kind in requested:
                exemplar = next((candidate for candidate in rows
                                 if candidate["role_kind"] == kind), None)
                if exemplar is None:
                    raise AcquisitionError(
                        f"runtime signed parse pilot role is absent (kind={kind})"
                    )
                selected.extend(
                    candidate for candidate in rows
                    if candidate["identity"] == exemplar["identity"]
                )
            rows = selected
        inventory = _proto_inventory_binding(native_output_receipt)
        semantics_path = _owner_file(Path(inventory["reflection_semantics"]["path"]),
                                     label="reflection semantics")
        semantics = read_json(semantics_path)
        binding["field_from_handle"] = rebind_method(
            runtime, live, _semantic_operation(semantics, "field.from_handle")
        )
        binding["field_name"] = rebind_method(
            runtime, live, _semantic_operation(semantics, "field.name")
        )
        helper_path = _owner_file(
            runtime_materializer_model.expanduser().resolve().parent.parent
            / "helpers-live/runtime-native-helpers.validated.private.json",
            label="native helper model",
        )
        class_path = _owner_file(
            runtime_materializer_model.expanduser().resolve().parent.parent
            / "classes/runtime-class-model.private.json",
            label="class model",
        )
        helper = read_json(helper_path)
        class_model = read_json(class_path)
        helper_rva = helper.get("helpers", {}).get("class_get_methods", {}).get("function_rva")
        field_helper = helper.get("helpers", {}).get("class_get_fields", {})
        method_qword = class_model.get("layout", {}).get("method_pointer_qword")
        native_semantics_path = _owner_file(
            runtime_materializer_model.expanduser().resolve().parent.parent
            / "native-semantics/runtime-native-semantics.private.json",
            label="native semantics model",
        )
        native_semantics = read_json(native_semantics_path)
        decoder = native_semantics.get("field_offset_decoder", {})
        decoder_values = (
            {"xor": 1, "add": 2, "subtract": 3}.get(decoder.get("operation")),
            decoder.get("raw_dword_offset"), decoder.get("xor_key"),
            decoder.get("mask"), decoder.get("adjustment"),
        )
        if (
            not isinstance(helper_rva, int) or not isinstance(method_qword, int)
            or field_helper.get("runtime_validated") is not True
            or field_helper.get("record_stride") != 32
            or not isinstance(field_helper.get("function_rva"), int)
            or native_semantics.get("binary", {}).get("sha256") != binding["binary"]["sha256"]
            or native_semantics.get("checks", {}).get("field_offset_decoder_closes_over_all_records") is not True
            or any(not isinstance(value, int) for value in decoder_values)
        ):
            raise AcquisitionError("runtime signed parse method iterator is absent")
        binding["class_get_methods_pointer"] = (
            live.preferred_image_base + int(binding["image_delta"]) + helper_rva
        )
        binding["method_pointer_qword"] = method_qword
        binding["object_header_bytes"] = int(binding["object_header_bytes"])
        binding["class_get_fields_pointer"] = (
            live.preferred_image_base + int(binding["image_delta"])
            + int(field_helper["function_rva"])
        )
        (
            binding["field_offset_operation"], binding["field_offset_raw_offset"],
            binding["field_offset_key"], binding["field_offset_mask"],
            binding["field_offset_adjustment"],
        ) = decoder_values
    finally:
        live.close()
    output = output_dir / "runtime-proto-signed-parse.private.bin"
    status = output_dir / "runtime-proto-signed-parse-status.private.json"
    return {
        "rows": rows,
        "blob": blob,
        "binding": binding,
        "model": model,
        "model_path": model_path,
        "output": output,
        "status": status,
        "helper_path": helper_path,
        "class_path": class_path,
        "native_semantics_path": native_semantics_path,
        "field_transform_probe_values": field_transform_probe_values,
    }


def prepare_runtime_proto_signed_parse(
    *, static_model: Path, snapshot: Path, native_output_receipt: Path,
    proto_field_type_model: Path, runtime_materializer_model: Path,
    output_dir: Path, compiler: Path | None = None,
    pilot_role_kinds: tuple[int, ...] | None = None,
    role_start: int = 0, role_limit: int | None = None,
    field_transform_probe_values: Mapping[int, list[int]] | None = None,
    roundtrip_binding: Mapping[str, Any] | None = None,
    writer_deadly_types: frozenset[int] = frozenset(),
    writer_fallback_roles: frozenset[tuple[Any, ...]] = frozenset(),
    unsigned_encoding_audit: bool = False,
    _pinned: "_PinnedShardInputs | None" = None,
) -> dict[str, Any]:
    materials = _prepare_signed_parse_materials(
        static_model=static_model, snapshot=snapshot,
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        runtime_materializer_model=runtime_materializer_model,
        output_dir=output_dir, pilot_role_kinds=pilot_role_kinds,
        role_start=role_start, role_limit=role_limit,
        field_transform_probe_values=field_transform_probe_values,
        roundtrip_binding=roundtrip_binding,
        writer_deadly_types=writer_deadly_types,
        writer_fallback_roles=writer_fallback_roles,
        unsigned_encoding_audit=unsigned_encoding_audit,
        _pinned=_pinned,
    )
    rows = materials["rows"]
    blob = materials["blob"]
    binding = materials["binding"]
    model = materials["model"]
    model_path = materials["model_path"]
    output = materials["output"]
    status = materials["status"]
    helper_path = materials["helper_path"]
    class_path = materials["class_path"]
    native_semantics_path = materials["native_semantics_path"]
    field_transform_probe_values = materials["field_transform_probe_values"]
    output_dir = _owner_directory(output_dir)
    build_dir = _owner_directory(output_dir / "build-runtime-proto-signed-parse")
    source = build_dir / "runtime-proto-signed-parse.c"
    injector_source = build_dir / "runtime-proto-signed-parse-injector.c"
    _require_executable_rows(rows)
    _private_text(source, _render(rows=rows, blob=blob, binding=binding,
                                  output=output, status=status,
                                  field_transform_mode=field_transform_probe_values is not None,
                                  unsigned_encoding_audit=unsigned_encoding_audit))
    _private_text(injector_source, runtime_injector_source())
    cc = _compiler(compiler)
    load_identity = secrets.token_hex(8)
    collector = build_dir / ("alpha-runtime-proto-signed-parse-"
                             + file_identity(source)["sha256"][:12] + "-"
                             + load_identity + ".dll")
    injector = build_dir / "alpha-runtime-proto-signed-parse-injector.exe"
    _build([str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra", "-Wformat=2",
            "-Werror", str(source), "-o", str(collector), "-lbcrypt"],
           label="runtime signed parse collector")
    _build([str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra", "-Wformat=2",
            "-Werror", str(injector_source), "-o", str(injector)],
           label="runtime signed parse injector")
    plan = {
        "schema": PLAN_SCHEMA, "status": "prepared",
        "model_target": copy.deepcopy(model["target"]),
        "target": {"executable_path": binding["binary"]["path"],
                   "executable_sha256": binding["binary"]["sha256"],
                   "process_id": binding["process_id"]},
        "inputs": {"static_model": file_identity(model_path),
                   "snapshot": (dict(_pinned.snapshot_identity) if _pinned is not None
                                else file_identity(snapshot.expanduser().resolve())),
                   "native_output_receipt": file_identity(native_output_receipt.expanduser().resolve()),
                   "proto_field_type_model": file_identity(proto_field_type_model.expanduser().resolve()),
                   "runtime_materializer_model": file_identity(runtime_materializer_model.expanduser().resolve()),
                   "native_helper_model": file_identity(helper_path),
                   "native_semantics_model": file_identity(native_semantics_path),
                   "class_model": file_identity(class_path)},
        "rows_owner_only": [
            {key: copy.deepcopy(row[key]) for key in (
                "identity", "encoding", "context", "field_index",
                "positive_hash", "negative_hash", "positive_input_hex",
                "negative_input_hex", "positive_value_bits",
                "negative_value_bits", "width", "role_kind", "map_value_kind",
                "strategy", "writer_fallback_strategy_owner_only")}
            for row in rows
        ],
        "contract": {
            "record_count": len(rows),
            "role_count": len({tuple(row["identity"][name] for name in (
                "type_index_owner_only", "number", "container", "role"
            )) for row in rows}),
            "payload_bytes": len(blob),
            "role_start": role_start,
            "role_limit": role_limit,
            "samples_per_role": (
                len(next(iter(field_transform_probe_values.values())))
                if field_transform_probe_values is not None
                else 2
            ),
            "mode": (
                "field-transform" if field_transform_probe_values is not None
                else "unsigned-encoding" if unsigned_encoding_audit else "signed-parse"
            ),
            **({
                "writer_probe_normalization": "ieee-negative-zero-to-denormal"
            } if field_transform_probe_values is not None else {}),
            "writer_deadly_parse_substitution_owner_only": sorted(
                int(value) for value in writer_deadly_types
            ),
            "writer_fallback_roles_owner_only": [list(key) for key in sorted(
                writer_fallback_roles
            )],
        },
        "collector": {**file_identity(collector), "load_identity": load_identity}, "injector": file_identity(injector),
        "output_path": str(output), "status_path": str(status),
        "policy": {"current_runtime_only": True, "name_selected_behavior": False,
                   "fixed_address_used": False, "saved_runtime_pointer_used": False,
                   "external_runtime_component_used": False},
    }
    _private_json(output_dir / "runtime-proto-signed-parse-plan.private.json", plan)
    return plan


def _validate(plan: Mapping[str, Any], status: Mapping[str, Any]) -> dict[str, Any]:
    path = _owner_file(Path(plan["output_path"]), label="capture")
    raw = path.read_bytes()
    header = HEADER.unpack_from(raw)
    count = int(plan["contract"]["record_count"])
    if (
        header[0] != MAGIC or header[1] != VERSION or header[2] != HEADER.size
        or header[3] != RECORD.size or header[5] != count
        or len(raw) != HEADER.size + count * RECORD.size
        or header[6] != plan["target"]["process_id"]
        or header[7].decode("ascii") != plan["target"]["executable_sha256"]
        or status.get("status") != "complete"
        or status.get("completed_count") != count
    ):
        raise AcquisitionError("runtime signed parse capture envelope differs")
    if plan.get("contract", {}).get("mode") == "field-transform":
        if status.get("failure_count") != 0:
            raise AcquisitionError(
                "runtime field transform parser rejected one or more live probes "
                f"(failure_kind={status.get('failure_kind_owner_only')}, "
                f"row={status.get('failure_index_owner_only')}, "
                f"terminated_units={status.get('terminated_units_owner_only', 0)}, "
                f"init_retries={status.get('init_retry_owner_only', 0)}, "
                f"health_probe={status.get('health_probe_owner_only', 0)}, "
                f"dispatch_stage={status.get('dispatch_stage_owner_only', 0)}, "
                f"parse_write_rows={status.get('parse_write_rows_owner_only', 0)}, "
                f"parse_write_retries={status.get('parse_write_retries_owner_only', 0)}, "
                f"writer_step={status.get('writer_step_owner_only', 0)})"
            )
        successful: dict[tuple[Any, ...], dict[str, Any]] = {}
        for index, source in enumerate(plan["rows_owner_only"]):
            record = RECORD.unpack_from(raw, HEADER.size + index * RECORD.size)
            if (
                record[0] != index
                or record[1] != source["field_index"]
                or record[2] != source["role_kind"]
                or record[3] != 0
                or record[6] != source["positive_hash"]
                or record[7] != source["negative_hash"]
            ):
                raise AcquisitionError(
                    f"runtime field transform probe record differs (row={index})"
                )
            identity = source.get("identity")
            if not isinstance(identity, Mapping):
                raise AcquisitionError("runtime field transform role identity is invalid")
            width = int(source["width"])
            mask = (1 << width) - 1
            def decoded(bits: int) -> int:
                encoding = str(source["encoding"])
                if encoding not in {
                    "int32", "sint32", "sfixed32", "int64", "sint64", "sfixed64"
                }:
                    return bits
                return bits - (1 << width) if bits & (1 << (width - 1)) else bits
            context = source.get("context")
            if not isinstance(context, Mapping):
                raise AcquisitionError("runtime field transform payload context is invalid")
            for label, bits, payload_hex, payload_hash in (
                ("positive", source.get("positive_value_bits"),
                 source.get("positive_input_hex"), source.get("positive_hash")),
                ("negative", source.get("negative_value_bits"),
                 source.get("negative_input_hex"), source.get("negative_hash")),
            ):
                if type(bits) is not int or not 0 <= bits <= mask:
                    raise AcquisitionError("runtime field transform probe value is invalid")
                expected_payload = build_payload(
                    identity=identity,
                    encoding=str(source["encoding"]),
                    value=decoded(bits),
                    packed=context.get("input_packed", context.get("packed")),
                    key_type=context.get("key_type"),
                    key_text=bytes.fromhex(str(context.get("key_text_hex", ""))),
                    omit_default_map_scalar=context.get("omit_default_map_scalar") is True,
                    map_message_value=context.get("map_message_value") is True,
                    map_string_value=context.get("map_string_value") is True,
                )
                try:
                    supplied_payload = bytes.fromhex(str(payload_hex))
                except ValueError as error:
                    raise AcquisitionError("runtime field transform payload is malformed") from error
                if supplied_payload != expected_payload or _fnv(expected_payload) != payload_hash:
                    raise AcquisitionError(
                        f"runtime field transform retained payload differs ({label})"
                    )
            key = tuple(identity[name] for name in (
                "type_index_owner_only", "number", "container", "role"
            ))
            row = successful.setdefault(key, {
                "identity": copy.deepcopy(dict(identity)),
                "encoding": source["encoding"],
                "context": copy.deepcopy(source["context"]),
                "field_index_owner_only": source["field_index"],
                "samples_owner_only": [],
            })
            if (
                row["encoding"] != source["encoding"]
                or row["context"] != source["context"]
                or row["field_index_owner_only"] != source["field_index"]
            ):
                raise AcquisitionError("runtime field transform role candidates conflict")
            row["samples_owner_only"].extend((
                {
                    "serialized_value": int(source["positive_value_bits"]),
                    "runtime_value": int(record[4]) & mask,
                    "input_hex": source["positive_input_hex"],
                    "input_fnv64": source["positive_hash"],
                },
                {
                    "serialized_value": int(source["negative_value_bits"]),
                    "runtime_value": int(record[5]) & mask,
                    "input_hex": source["negative_input_hex"],
                    "input_fnv64": source["negative_hash"],
                },
            ))
        role_count = int(plan["contract"]["role_count"])
        sample_count = int(plan["contract"]["samples_per_role"])
        if len(successful) != role_count:
            raise AcquisitionError(
                "runtime field transform probe did not close its current role domain"
            )
        observations = []
        for row in successful.values():
            samples = row["samples_owner_only"]
            if (
                len(samples) != sample_count
                or len({sample["serialized_value"] for sample in samples}) != sample_count
                or len({sample["runtime_value"] for sample in samples}) != sample_count
            ):
                raise AcquisitionError(
                    "runtime field transform sample set is incomplete or non-bijective "
                    f"(identity={row['identity']}, encoding={row['encoding']}, "
                    f"context={row['context']}, expected={sample_count}, "
                    f"observed={len(samples)}, "
                    f"unique_inputs={len({sample['serialized_value'] for sample in samples})}, "
                    f"unique_outputs={len({sample['runtime_value'] for sample in samples})})"
                )
            observations.append(row)
        return {
            "schema": FIELD_TRANSFORM_RESULT_SCHEMA,
            "status": "runtime-validated",
            "target": copy.deepcopy(plan["model_target"]),
            "observations": observations,
            "counts": {
                "required": role_count,
                "verified": len(observations),
                "sample_count_per_role": sample_count,
                "candidate_count": count,
            },
            "inventory": file_identity(path),
            "status_receipt": file_identity(Path(plan["status_path"])),
            "policy": {
                **copy.deepcopy(plan["policy"]),
                "reference_proto_values_used": False,
                "fresh_runtime_observations_used": True,
            },
            "owner_only": True,
        }
    successful: dict[tuple[Any, ...], list[dict[str, Any]]] = {}
    unsigned_audit = plan["contract"].get("mode") == "unsigned-encoding"
    quarantined_count = 0
    for index, source in enumerate(plan["rows_owner_only"]):
        record = RECORD.unpack_from(raw, HEADER.size + index * RECORD.size)
        if record[0] != index or record[1] != source["field_index"] or record[2] != source["role_kind"]:
            raise AcquisitionError(
                f"runtime signed parse observation identity differs (row={index})"
            )
        if unsigned_audit and record[3] == WRITER_TERMINATION_FAILURE_KIND:
            if (status.get("dispatch_stage_owner_only") != 0
                    or status.get("health_probe_owner_only") != 1
                    or status.get("parse_write_retries_owner_only", 0) < 1
                    or any(record[4:8])):
                raise AcquisitionError("unsigned candidate quarantine lacks a healthy completed dispatch")
            quarantined_count += 1
            continue
        if record[3] not in (0, 200):
            raise AcquisitionError(
                f"runtime signed parse observation failed (row={index}, kind={record[3]})"
            )
        if record[6] != source["positive_hash"] or record[7] != source["negative_hash"]:
            raise AcquisitionError(f"runtime signed parse input hash differs (row={index})")
        if record[3] == 200:
            if plan["contract"].get("mode") != "unsigned-encoding" and record[4] == 123 and record[5] == -123:
                raise AcquisitionError("runtime signed parse candidate rejection is inconsistent")
            continue
        evidence = {
            "schema": UNSIGNED_EVIDENCE_SCHEMA if plan["contract"].get("mode") == "unsigned-encoding" else EVIDENCE_SCHEMA,
            "identity": copy.deepcopy(source["identity"]),
            "encoding": source["encoding"],
            "context": copy.deepcopy(source["context"]),
            "positive": {"expected": 123, "observed": record[4],
                         "input_hex": source["positive_input_hex"], "input_fnv64": record[6]},
            "negative": {"expected": -123, "observed": record[5],
                         "input_hex": source["negative_input_hex"], "input_fnv64": record[7]},
        }
        if evidence["schema"] == UNSIGNED_EVIDENCE_SCHEMA:
            evidence["wire_validation"] = (
                "exact-writer-field-replacement/v1" if source["strategy"] in (6, 7) else
                "parse-container-membership/v1" if source["strategy"] == 5 else
                "parse-serialize-roundtrip/v1" if source["strategy"] == 0
                else "exact-writer-bytes/v1"
            )
        verify_parse_evidence(evidence)
        key = tuple(source["identity"][name] for name in (
            "type_index_owner_only", "number", "container", "role"
        ))
        successful.setdefault(key, []).append(evidence)
    if unsigned_audit and quarantined_count != status.get("terminated_units_owner_only", 0):
        raise AcquisitionError("unsigned candidate quarantine count differs")
    observations = []
    for candidates in successful.values():
        if len(candidates) == 1:
            observations.append(candidates[0])
            continue
        encodings = {candidate["encoding"] for candidate in candidates}
        preferred = [
            candidate for candidate in candidates
            if candidate["identity"]["cardinality"] == "repeated"
            and candidate["context"]["packed"]
            is candidate["context"].get("source_packed")
        ]
        if len(encodings) != 1 or len(preferred) != 1:
            raise AcquisitionError("runtime signed parse candidate result is ambiguous")
        observations.append(preferred[0])
    role_count = int(plan["contract"]["role_count"])
    if len(observations) != role_count:
        raise AcquisitionError(
            f"runtime signed parse did not resolve every role "
            f"({len(observations)}/{role_count})"
        )
    return {
        "schema": RESULT_SCHEMA, "status": "runtime-validated",
        "target": copy.deepcopy(plan["model_target"]),
        "observations": observations,
        "counts": {"required": role_count, "verified": len(observations), "failed": 0,
                   "candidate_count": count},
        "inventory": file_identity(path),
        "status_receipt": file_identity(Path(plan["status_path"])),
        "policy": copy.deepcopy(plan["policy"]), "owner_only": True,
    }


def verify_parse_evidence(evidence: Mapping[str, Any]) -> dict[str, Any]:
    unsigned = evidence.get("schema") == UNSIGNED_EVIDENCE_SCHEMA
    if evidence.get("schema") not in {EVIDENCE_SCHEMA, UNSIGNED_EVIDENCE_SCHEMA}:
        raise AcquisitionError("signed parse evidence schema differs")
    identity = evidence.get("identity")
    encoding = evidence.get("encoding")
    context = evidence.get("context")
    if (not isinstance(identity, Mapping) or encoding not in (UNSIGNED if unsigned else SIGNED)
            or identity.get("width") != {**SIGNED, **UNSIGNED}.get(encoding)
            or not isinstance(context, Mapping)):
        raise AcquisitionError("signed parse evidence identity is invalid")
    if unsigned:
        mode = context.get("observation_mode")
        expected_validation = (
            "exact-writer-field-replacement/v1" if mode in {
                "repeated-write-baseline-serialize", "map-write-baseline-serialize"
            } else
            "parse-container-membership/v1" if mode == "parse-container" else
            "parse-serialize-roundtrip/v1" if mode == "parse" else
            "exact-writer-bytes/v1" if mode in {"repeated-write-serialize", "map-write-serialize"}
            else None
        )
        if expected_validation is None or evidence.get("wire_validation") != expected_validation:
            raise AcquisitionError("unsigned wire evidence lacks its runtime byte validation")
        if mode == "parse-container" and identity.get("cardinality") not in {"repeated", "map"}:
            raise AcquisitionError("unsigned container evidence belongs to a scalar")
    for label, expected in (("positive", 123), ("negative", -123)):
        sample = evidence.get(label)
        if (not isinstance(sample, Mapping) or sample.get("expected") != expected
                or type(sample.get("observed")) is not int
                or not -(1 << (identity["width"] - 1)) <= sample["observed"] < 1 << identity["width"]
                or (not unsigned or context["observation_mode"] not in {"parse", "parse-container"})
                and sample["observed"] != expected):
            raise AcquisitionError("signed parse semantic observation differs")
        payload = build_payload(
            identity=identity, encoding=encoding,
            value=expected & ((1 << UNSIGNED[encoding]) - 1) if encoding in UNSIGNED else expected,
            packed=context.get("input_packed", context.get("packed")),
            key_type=context.get("key_type"),
            key_text=bytes.fromhex(str(context.get("key_text_hex", ""))),
            map_message_value=context.get("map_message_value") is True,
            map_string_value=context.get("map_string_value") is True,
        )
        if sample.get("input_hex") != payload.hex() or sample.get("input_fnv64") != _fnv(payload):
            raise AcquisitionError("signed parse retained input differs")
    if unsigned:
        mask = (1 << identity["width"]) - 1
        if evidence["positive"]["observed"] & mask == evidence["negative"]["observed"] & mask:
            raise AcquisitionError("unsigned wire evidence did not distinguish runtime values")
    return copy.deepcopy(dict(evidence))


def apply_parse_evidence(model: Mapping[str, Any], capture: Mapping[str, Any]) -> dict[str, Any]:
    if capture.get("schema") != RESULT_SCHEMA or capture.get("target") != model.get("target"):
        raise AcquisitionError("signed parse capture belongs to another model")
    result = copy.deepcopy(dict(model))
    domain = {tuple(row[key] for key in (
        "type_index_owner_only", "number", "container", "role")): row
        for row in role_inventory(result["messages_owner_only"])}
    from alpha.p01 import encoding_coverage
    pending = {
        tuple(row[key] for key in (
            "type_index_owner_only", "number", "container", "role"
        ))
        for row in encoding_coverage(result["messages_owner_only"])["roles_owner_only"]
        if row["verified"] is not True
    }
    seen = set()
    for raw in capture.get("observations", []):
        evidence = verify_parse_evidence(raw)
        identity = evidence["identity"]
        key = tuple(identity[name] for name in (
            "type_index_owner_only", "number", "container", "role"))
        if (key not in pending or key not in domain or domain[key] != identity or key in seen
                or evidence["encoding"] not in SIGNED):
            raise AcquisitionError("signed parse observation is outside the current role domain")
        seen.add(key)
        message = next(row for row in result["messages_owner_only"]
                       if row["type_index_owner_only"] == key[0])
        fields = message["fields"] if key[2] == "field" else next(
            oneof["cases"] for oneof in message["oneofs"]
            if key[2] == "oneof:" + oneof["name"]
        )
        field = next(row for row in fields if row["number"] == key[1])
        field[key[3]] = evidence["encoding"]
        if identity["cardinality"] == "repeated":
            field["packed"] = evidence["context"]["packed"]
        field.setdefault("signed_parse_evidence", {})[key[3]] = evidence
    if seen != pending:
        raise AcquisitionError("signed parse capture does not close the pending role domain")
    coverage = encoding_coverage(result["messages_owner_only"])
    result["signed_encoding_coverage_owner_only"] = coverage
    result.setdefault("signed_parse_captures_owner_only", []).append(copy.deepcopy(dict(capture)))
    audit = result.get("message_domain_audit_owner_only", {})
    result["full_semantic_verification_complete"] = (
        coverage.get("complete") is True
        and audit.get("complete") is True
    )
    return result


def _adopt_sealed_signed_parse_shard(
    *, shard_dir: Path, materials_kwargs: Mapping[str, Any],
    fresh_inputs: Mapping[str, dict[str, Any]],
    expected_slice: list[dict[str, Any]], count: int, transform_mode: bool,
    pinned: "_PinnedShardInputs | None" = None,
) -> dict[str, Any] | None:
    import hashlib

    shard_dir = shard_dir.expanduser().resolve()
    model_path = shard_dir / "runtime-proto-signed-parse.private.json"
    bin_path = shard_dir / "runtime-proto-signed-parse.private.bin"
    status_path = shard_dir / "runtime-proto-signed-parse-status.private.json"
    source_path = (
        shard_dir / "build-runtime-proto-signed-parse/runtime-proto-signed-parse.c"
    )
    plan_path = shard_dir / "runtime-proto-signed-parse-plan.private.json"
    try:
        if not (
            model_path.is_file() and bin_path.is_file()
            and status_path.is_file() and source_path.is_file()
            and plan_path.is_file()
        ):
            return None
        sealed_model = read_json(model_path)
        sealed_plan = read_json(plan_path)
        sealed_status = read_json(status_path)
        if not isinstance(sealed_model, dict) or not isinstance(sealed_plan, dict):
            return None


        replan_kwargs = dict(materials_kwargs)
        replan_kwargs["writer_deadly_types"] = frozenset(
            sealed_plan.get("contract", {}).get(
                "writer_deadly_parse_substitution_owner_only"
            ) or ()
        )
        replan_kwargs["writer_fallback_roles"] = frozenset(
            tuple(key) for key in sealed_plan.get("contract", {}).get(
                "writer_fallback_roles_owner_only", ()
            )
        )
        materials = _prepare_signed_parse_materials(**replan_kwargs, _pinned=pinned)
        fresh_source = _render(
            rows=materials["rows"], blob=materials["blob"],
            binding=materials["binding"], output=Path(sealed_plan.get("output_path", materials["output"])),
            status=Path(sealed_plan.get("status_path", materials["status"])),
            field_transform_mode=transform_mode,
            unsigned_encoding_audit=materials_kwargs.get("unsigned_encoding_audit", False),
        )
        if hashlib.sha256(fresh_source.encode("utf-8")).hexdigest() != hashlib.sha256(
            source_path.read_bytes()
        ).hexdigest():


            return None
        for key, identity in fresh_inputs.items():
            sealed = (sealed_plan.get("inputs") or {}).get(key)
            if (
                not isinstance(identity, dict) or not isinstance(sealed, dict)
                or sealed.get("sha256") != identity.get("sha256")
                or sealed.get("bytes") != identity.get("bytes")
            ):
                return None
        raw = bin_path.read_bytes()
        header = HEADER.unpack_from(raw)
        record_count = int((sealed_plan.get("contract") or {}).get("record_count", -1))
        if (
            header[0] != MAGIC or header[1] != VERSION or header[2] != HEADER.size
            or header[3] != RECORD.size or header[5] != record_count
            or len(raw) != HEADER.size + record_count * RECORD.size
        ):
            return None
        if (
            sealed_status.get("status") != "complete"
            or sealed_status.get("completed_count") != record_count
        ):
            return None
        if not _same_sealed_bytes(file_identity(bin_path), sealed_model.get("inventory")):
            return None
        if not _same_sealed_bytes(file_identity(status_path), sealed_model.get("status_receipt")):
            return None
        expected_schema = (
            FIELD_TRANSFORM_RESULT_SCHEMA if transform_mode else RESULT_SCHEMA
        )
        observations = sealed_model.get("observations")
        counts = sealed_model.get("counts")
        if (
            sealed_model.get("schema") != expected_schema
            or sealed_model.get("status") != "runtime-validated"
            or not isinstance(observations, list)
            or not isinstance(counts, dict)
            or counts.get("required") != count
            or counts.get("verified") != len(observations)
            or counts.get("failed", 0) != 0
            or sealed_model.get("target") != materials["model"].get("target")
        ):
            return None
        expected_keys = {
            tuple(row[name] for name in (
                "type_index_owner_only", "number", "container", "role"
            ))
            for row in expected_slice
        }
        observed_keys = [
            tuple((observation.get("identity") or {}).get(name) for name in (
                "type_index_owner_only", "number", "container", "role"
            ))
            for observation in observations
            if isinstance(observation, dict)
        ]
        if len(observed_keys) != len(observations) or set(observed_keys) != expected_keys:
            return None
        if transform_mode:
            validated = _validate({
                **sealed_plan, "rows_owner_only": materials["rows"],
                "output_path": str(bin_path), "status_path": str(status_path),
            }, sealed_status)
            if (validated["observations"] != observations
                    or validated["counts"] != counts
                    or validated["policy"] != sealed_model.get("policy")):
                return None
    except (AcquisitionError, OSError, ValueError, KeyError, struct.error):


        return None
    print(f"proto signed parse shard adopted without live capture: {shard_dir.name}",
          flush=True)
    return {
        "schema": sealed_model["schema"],
        "status": sealed_model["status"],
        "target": copy.deepcopy(sealed_model["target"]),
        "counts": copy.deepcopy(counts),
        "model": file_identity(model_path),
        "route_contract_owner_only": copy.deepcopy(sealed_plan.get("contract", {})),
    }


def _same_sealed_bytes(actual, sealed):
    return (isinstance(sealed, Mapping) and actual["bytes"] == sealed.get("bytes")
            and actual["sha256"] == sealed.get("sha256"))


def _adopt_available_signed_parse_shard(*, output_dir: Path, shard_name: str,
                                       materials_kwargs, pinned=None, **kwargs):


    candidates = sorted(output_dir.glob(shard_name + "-retry-*"), reverse=True)
    candidates.append(output_dir / shard_name)
    for directory in candidates:
        if directory.name != shard_name and not re.fullmatch(
                re.escape(shard_name) + r"-retry-\d+", directory.name):
            continue
        if not directory.is_dir():
            continue
        result = _adopt_sealed_signed_parse_shard(
            shard_dir=directory, pinned=pinned,
            materials_kwargs={**materials_kwargs, "output_dir": directory}, **kwargs)
        if result is not None:
            return result
    return None


def _adopt_archived_signed_parse_shard(
    *, output_dir: Path, shard_name: str,
    materials_kwargs: Mapping[str, Any],
    fresh_inputs: Mapping[str, dict[str, Any]],
    expected_slice: list[dict[str, Any]], count: int, transform_mode: bool,
    pinned: "_PinnedShardInputs | None" = None,
) -> dict[str, Any] | None:
    import shutil
    import uuid

    stage_dir = output_dir.parent
    archive_root = stage_dir.parent / "failed-stages"
    if not archive_root.is_dir():
        return None
    archives = sorted(archive_root.glob(f"{stage_dir.name}-*"))
    for archive_dir in reversed(archives):
        sealed_parent = archive_dir / output_dir.name
        result = _adopt_available_signed_parse_shard(
            output_dir=sealed_parent, shard_name=shard_name,
            materials_kwargs=materials_kwargs,
            fresh_inputs=fresh_inputs,
            expected_slice=expected_slice,
            count=count,
            transform_mode=transform_mode,
            pinned=pinned,
        )
        if result is None:
            continue
        sealed_dir = Path(result["model"]["path"]).parent
        live_model_path = output_dir / sealed_dir.name / "runtime-proto-signed-parse.private.json"
        staging = output_dir / f".{shard_name}.adopt-{uuid.uuid4().hex}"
        try:
            shutil.copytree(sealed_dir, staging)
            output_dir.mkdir(parents=True, exist_ok=True)
            os.replace(staging, output_dir / sealed_dir.name)
        except OSError:
            shutil.rmtree(staging, ignore_errors=True)
            continue
        result["model"]["path"] = str(live_model_path)
        print(
            "proto signed parse shard adopted from archived attempt: "
            f"{archive_dir.name}/{shard_name}",
            flush=True,
        )
        return result
    return None


def _capture_runtime_proto_signed_parse_single(
    *, wine: Path, wineprefix: Path, timeout: float = 900.0,
    _pinned: "_PinnedShardInputs | None" = None, **kwargs: Any
) -> dict[str, Any]:
    output_dir = _owner_directory(Path(kwargs["output_dir"]))
    preparation_started = time.monotonic()
    print(f"proto probe preparing shard: {output_dir.name}", flush=True)
    plan = prepare_runtime_proto_signed_parse(**kwargs, _pinned=_pinned)
    print(
        f"proto probe prepared: {plan.get('contract', {}).get('record_count', '?')} rows "
        f"in {time.monotonic() - preparation_started:.1f}s", flush=True,
    )


    attempt_identity = plan["collector"].get("load_identity", secrets.token_hex(8))
    for key in ("status_path", "output_path"):
        previous = Path(plan[key])
        if previous.is_file():
            previous.rename(previous.with_name(previous.name + ".previous-" + attempt_identity))
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    environment["WINEDEBUG"] = "-all"


    attempts: list[dict[str, Any]] = []
    result = None
    for attempt in range(1, 4):
        try:
            result = subprocess.run(
                _host_run(str(wine.expanduser().resolve()), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name),
                env=environment, check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, encoding="utf-8", errors="replace", timeout=90,
            )
        except subprocess.TimeoutExpired:


            attempts.append({"attempt": attempt, "returncode": None,
                             "stdout": "", "stderr": "injection attempt timed out after 90s"})
            time.sleep(min(30.0, 5.0 * attempt))
            continue
        attempts.append({"attempt": attempt, "returncode": result.returncode,
                         "stdout": result.stdout[-400:], "stderr": result.stderr[-400:]})
        if not result.returncode:
            break
        time.sleep(min(30.0, 5.0 * attempt))
    _private_text(output_dir / "runtime-proto-signed-parse-injector.private.log",
                  json.dumps({"attempts": attempts,
                              "returncode": result.returncode if result else None,
                              "stdout": result.stdout if result else "",
                              "stderr": result.stderr if result else ""},
                             ensure_ascii=False, indent=2) + "\n")
    if result is None or result.returncode:
        raise AcquisitionError(
            "runtime signed parse injection failed "
            f"after {len(attempts)} attempt(s)"
        )
    deadline = time.monotonic() + timeout
    status_path = Path(plan["status_path"])
    status = None
    while time.monotonic() < deadline:
        if status_path.is_file():
            candidate = read_json(status_path)
            if isinstance(candidate, dict) and candidate.get("status"):
                status = candidate
                break
        time.sleep(0.2)
    if status is None:
        raise AcquisitionError("runtime signed parse capture timed out")
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        error = AcquisitionError(
            "runtime signed parse capture failed "
            f"(kind={status.get('failure_kind_owner_only')}, "
            f"dispatch_stage={status.get('dispatch_stage_owner_only')}, "
            f"completed={status.get('completed_count')}/{status.get('expected_count')}, "
            f"health_probe={status.get('health_probe_owner_only')})"
        )


        error.retryable = status.get("completed_count") == 0 and status.get("terminated_units_owner_only", 0) == 0
        raise error
    _seal_runtime_output(Path(plan["output_path"]))
    model = _validate(plan, status)
    model_path = output_dir / "runtime-proto-signed-parse.private.json"
    _private_json(model_path, model)
    return {"schema": model["schema"], "status": model["status"],
            "target": model["target"], "counts": model["counts"],
            "model": file_identity(model_path)}


def capture_runtime_proto_signed_parse(
    *, wine: Path, wineprefix: Path, timeout: float = 900.0,
    shard_role_count: int = 256, capture_attempts: int = 3, **kwargs: Any,
) -> dict[str, Any]:

    if kwargs.get("pilot_role_kinds") is not None:
        return _capture_runtime_proto_signed_parse_single(
            wine=wine, wineprefix=wineprefix, timeout=timeout, **kwargs
        )
    if (
        not isinstance(shard_role_count, int)
        or isinstance(shard_role_count, bool)
        or not 1 <= shard_role_count <= 1024
    ):
        raise AcquisitionError("runtime signed parse shard size is invalid")
    if (
        not isinstance(capture_attempts, int)
        or isinstance(capture_attempts, bool)
        or not 1 <= capture_attempts <= 5
    ):
        raise AcquisitionError("runtime signed parse capture attempt count is invalid")
    if kwargs.get("role_start", 0) or kwargs.get("role_limit") is not None:
        raise AcquisitionError("runtime signed parse external slicing is diagnostic-only")
    output_dir = _owner_directory(Path(kwargs["output_dir"]))
    static_model = read_private_model(
        _owner_file(Path(kwargs["static_model"]), label="static model")
    )
    field_transform_probe_values = kwargs.get("field_transform_probe_values")
    transform_mode = field_transform_probe_values is not None
    all_expected_roles = (
        _field_transform_role_inventory(static_model)
        if transform_mode else _unsigned_roles(static_model)
        if kwargs.get("unsigned_encoding_audit") else _pending_roles(static_model)
    )
    role_source_indices = list(range(len(all_expected_roles)))
    selected_role_index = kwargs.pop("field_transform_role_index", None)
    if selected_role_index is not None:
        if (
            not transform_mode or type(selected_role_index) is not int
            or not 0 <= selected_role_index < len(all_expected_roles)
        ):
            raise AcquisitionError("runtime field transform role selection is invalid")
        role_source_indices = [selected_role_index]
        expected_roles = [all_expected_roles[selected_role_index]]
    else:
        expected_roles = all_expected_roles
    if transform_mode and not expected_roles:
        aggregate = {
            "schema": FIELD_TRANSFORM_RESULT_SCHEMA,
            "status": "runtime-validated",
            "target": copy.deepcopy(static_model["target"]),
            "observations": [],
            "counts": {
                "required": 0, "verified": 0, "failed": 0,
                "candidate_count": 0, "shard_count": 0,
                "sample_count_per_role": 0,
            },
            "policy": {
                "current_runtime_only": True,
                "reference_proto_values_used": False,
                "fresh_runtime_observations_used": True,
                "fixed_address_used": False,
                "saved_runtime_pointer_used": False,
                "external_runtime_component_used": False,
            },
            "owner_only": True,
        }
        model_path = output_dir / "runtime-proto-signed-parse.private.json"
        _private_json(model_path, aggregate)
        return {
            "schema": aggregate["schema"], "status": aggregate["status"],
            "target": aggregate["target"], "counts": aggregate["counts"],
            "model": file_identity(model_path),
        }
    if not expected_roles:
        raise AcquisitionError("runtime signed parse role domain is empty")


    kwargs["roundtrip_binding"] = _roundtrip_binding(
        native_output_receipt=Path(kwargs["native_output_receipt"]),
        proto_field_type_model=Path(kwargs["proto_field_type_model"]),
    )


    materializer_base = Path(
        kwargs["runtime_materializer_model"]
    ).expanduser().resolve().parent.parent
    pinned = _open_pinned_shard_inputs(snapshot=Path(kwargs["snapshot"]))
    try:
        fresh_inputs = {
            key: file_identity(path.expanduser().resolve())
            for key, path in {
                "static_model": Path(kwargs["static_model"]),
                "native_output_receipt": Path(kwargs["native_output_receipt"]),
                "proto_field_type_model": Path(kwargs["proto_field_type_model"]),
                "runtime_materializer_model": Path(
                    kwargs["runtime_materializer_model"]
                ),
                "native_helper_model": (
                    materializer_base
                    / "helpers-live/runtime-native-helpers.validated.private.json"
                ),
                "native_semantics_model": (
                    materializer_base
                    / "native-semantics/runtime-native-semantics.private.json"
                ),
                "class_model": (
                    materializer_base / "classes/runtime-class-model.private.json"
                ),
            }.items()
        }
        fresh_inputs["snapshot"] = dict(pinned.snapshot_identity)
        observations: list[dict[str, Any]] = []
        shards = []
        target = None
        policy = None
        candidate_count = 0


        writer_deadly_types: set[int] = set()
        writer_fallback_roles: set[tuple[Any, ...]] = set()
        for start in range(0, len(expected_roles), shard_role_count):
            count = min(shard_role_count, len(expected_roles) - start)
            shard_name = f"shard-{start:05d}-{start + count - 1:05d}"
            result = None
            shard_kwargs = dict(kwargs)
            shard_kwargs["output_dir"] = output_dir / shard_name
            shard_kwargs["role_start"] = role_source_indices[start]
            shard_kwargs["role_limit"] = count
            shard_kwargs["_pinned"] = pinned


            result = _adopt_available_signed_parse_shard(
                output_dir=output_dir, shard_name=shard_name,
                materials_kwargs={
                    key: shard_kwargs[key]
                    for key in (
                        "static_model", "snapshot", "native_output_receipt",
                        "proto_field_type_model", "runtime_materializer_model",
                        "output_dir", "role_start", "role_limit",
                        "field_transform_probe_values", "roundtrip_binding",
                        "unsigned_encoding_audit",
                    )
                    if key in shard_kwargs
                },
                fresh_inputs=fresh_inputs,
                expected_slice=expected_roles[start:start + count],
                count=count,
                transform_mode=transform_mode,
                pinned=pinned,
            )
            if result is None:
                result = _adopt_archived_signed_parse_shard(
                    output_dir=output_dir,
                    shard_name=shard_name,
                    materials_kwargs={
                        key: shard_kwargs[key]
                        for key in (
                            "static_model", "snapshot", "native_output_receipt",
                            "proto_field_type_model", "runtime_materializer_model",
                            "output_dir", "role_start", "role_limit",
                            "field_transform_probe_values", "roundtrip_binding",
                            "unsigned_encoding_audit",
                        )
                        if key in shard_kwargs
                    },
                    fresh_inputs=fresh_inputs,
                    expected_slice=expected_roles[start:start + count],
                    count=count,
                    transform_mode=transform_mode,
                    pinned=pinned,
                )
            if result is not None:
                contract = result.get("route_contract_owner_only", {})
                writer_deadly_types.update(contract.get("writer_deadly_parse_substitution_owner_only", ()))
                writer_fallback_roles.update(tuple(key) for key in
                                             contract.get("writer_fallback_roles_owner_only", ()))
            for attempt in range(capture_attempts):
                if result is not None:
                    break
                shard_kwargs["output_dir"] = output_dir / (
                    shard_name if attempt == 0 else f"{shard_name}-retry-{attempt:02d}"
                )
                shard_kwargs["writer_deadly_types"] = frozenset(writer_deadly_types)
                shard_kwargs["writer_fallback_roles"] = frozenset(writer_fallback_roles)
                try:
                    result = _capture_runtime_proto_signed_parse_single(
                        wine=wine, wineprefix=wineprefix, timeout=timeout, **shard_kwargs
                    )
                    break
                except AcquisitionError:
                    shard_plan_path = (
                        shard_kwargs["output_dir"]
                        / "runtime-proto-signed-parse-plan.private.json"
                    )
                    status = {}
                    deadly = frozenset()
                    fallback_roles = frozenset()
                    if shard_plan_path.is_file():
                        shard_plan = read_json(shard_plan_path)
                        status_path = Path(shard_plan["status_path"])
                        status = (
                            read_json(status_path) if status_path.is_file() else {}
                        )
                        deadly = frozenset() if kwargs.get("unsigned_encoding_audit") else writer_deadly_types_from_capture(
                            plan=shard_plan, status=status,
                            bin_path=Path(shard_plan["output_path"]),
                        )
                        fallback_roles = parse_writer_fallback_roles(
                            plan=shard_plan, status=status,
                            bin_path=Path(shard_plan["output_path"]),
                        ) - writer_fallback_roles
                        fallback_roles = frozenset(
                            key for key in fallback_roles
                            if str(key[2]).startswith("oneof:") or any(
                                row["role_kind"] == ROLE_KIND["oneof"]
                                and tuple(row["identity"][name] for name in (
                                    "type_index_owner_only", "number", "container", "role")) == key
                                for row in shard_plan["rows_owner_only"]
                            ) or (key[0] not in writer_deadly_types and key[0] not in deadly)
                        )
                    if deadly:


                        writer_deadly_types.update(deadly)
                        retryable = True
                    elif fallback_roles:


                        writer_fallback_roles.update(fallback_roles)
                        retryable = True
                    else:
                        retryable = (
                            status.get("status") == "capture_failed"
                            and status.get("completed_count") == 0
                        )
                    if not retryable or attempt + 1 == capture_attempts:
                        raise
            if result is None:
                raise AcquisitionError("runtime signed parse shard capture did not run")
            shard_model = read_json(_owner_file(Path(result["model"]["path"]), label="shard model"))
            if target is None:
                target = copy.deepcopy(shard_model["target"])
                policy = copy.deepcopy(shard_model["policy"])
            elif shard_model.get("target") != target or shard_model.get("policy") != policy:
                raise AcquisitionError("runtime signed parse shard binding differs")
            if (
                shard_model.get("schema") != (
                    FIELD_TRANSFORM_RESULT_SCHEMA if transform_mode else RESULT_SCHEMA
                )
                or shard_model.get("counts", {}).get("required") != count
            ):
                raise AcquisitionError("runtime signed parse shard role count differs")
            observations.extend(copy.deepcopy(shard_model["observations"]))
            candidate_count += int(shard_model["counts"]["candidate_count"])
            shards.append(file_identity(Path(result["model"]["path"])))
        expected = {
            tuple(row[name] for name in (
                "type_index_owner_only", "number", "container", "role"
            )): row
            for row in expected_roles
        }
        observed = {}
        for row in observations:
            identity = row.get("identity", {})
            key = tuple(identity.get(name) for name in (
                "type_index_owner_only", "number", "container", "role"
            ))
            expected_identity = expected.get(key)
            identity_matches = (
                expected_identity == identity
                if not transform_mode
                else isinstance(expected_identity, Mapping)
                and {
                    name: expected_identity[name] for name in (
                        "type_index_owner_only", "number", "container", "role",
                        "cardinality", "width",
                    )
                } == identity
                and row.get("encoding") == expected_identity.get("encoding")
            )
            if key in observed or not identity_matches:
                raise AcquisitionError("runtime signed parse aggregate role domain differs")
            observed[key] = row
        if set(observed) != set(expected):
            raise AcquisitionError("runtime signed parse aggregate is incomplete")
        aggregate = {
            "schema": FIELD_TRANSFORM_RESULT_SCHEMA if transform_mode else RESULT_SCHEMA,
            "status": "runtime-validated",
            "target": target,
            "observations": observations,
            "counts": {
                "required": len(expected_roles),
                "verified": len(observations),
                "failed": 0,
                "candidate_count": candidate_count,
                "shard_count": len(shards),
                **({
                    "sample_count_per_role": len(next(iter(field_transform_probe_values.values())))
                } if transform_mode else {}),
            },
            "shards_owner_only": shards,
            "policy": {
                **(policy or {}),
                **({
                    "reference_proto_values_used": False,
                    "fresh_runtime_observations_used": True,
                } if transform_mode else {}),
            },
            "owner_only": True,
        }
        model_path = output_dir / "runtime-proto-signed-parse.private.json"
        _private_json(model_path, aggregate)
        return {
            "schema": aggregate["schema"],
            "status": aggregate["status"],
            "target": aggregate["target"],
            "counts": aggregate["counts"],
            "model": file_identity(model_path),
        }
    finally:
        pinned.close()


def capture_runtime_proto_field_transform_probe(
    *, wine: Path, wineprefix: Path, timeout: float = 900.0,
    shard_role_count: int = 256, capture_attempts: int = 3, **kwargs: Any,
) -> dict[str, Any]:
    from alpha.p50 import initial_runtime_probe_values

    role_index = kwargs.get("field_transform_role_index")
    supplied_values = kwargs.get("field_transform_probe_values")
    if role_index is None:
        if supplied_values is not None:
            raise AcquisitionError("initial field transform probe values are internally selected")
        kwargs["field_transform_probe_values"] = {
            32: initial_runtime_probe_values(32),
            64: initial_runtime_probe_values(64),
        }
    elif (
        type(role_index) is not int
        or not isinstance(supplied_values, Mapping)
        or not supplied_values
        or set(supplied_values) - {32, 64}
    ):
        raise AcquisitionError("adaptive field transform probe configuration is invalid")
    return capture_runtime_proto_signed_parse(
        wine=wine,
        wineprefix=wineprefix,
        timeout=timeout,
        shard_role_count=shard_role_count,
        capture_attempts=capture_attempts,
        **kwargs,
    )


def write_verified_parse_model(*, static_model: Path, parse_model: Path,
                               output_path: Path,
                               unsigned_encoding_audit: bool = False) -> dict[str, Any]:
    source_identity = file_identity(static_model.expanduser().resolve())
    parse_identity = file_identity(parse_model.expanduser().resolve())
    model = read_private_model(static_model)
    capture = read_json(parse_model)
    result = (apply_unsigned_parse_evidence(model, capture)
              if unsigned_encoding_audit else apply_parse_evidence(model, capture))
    if file_identity(static_model) != source_identity or file_identity(parse_model) != parse_identity:
        raise AcquisitionError("signed parse inputs changed during verification")
    if output_path.exists() or output_path.is_symlink():
        raise AcquisitionError("signed parse verified output already exists")
    prefix = "unsigned" if unsigned_encoding_audit else "signed"
    result.setdefault("inputs", {})[prefix + "_parse_source_model"] = source_identity
    result["inputs"][prefix + "_parse_observation_model"] = parse_identity
    _private_json(output_path, result)


    coverage = result.get(prefix + "_encoding_coverage_owner_only", {})
    return {
        "schema": "alpha.runtime-proto-" + prefix + "-verified-model-receipt/v1",
        "status": "complete",
        "target": copy.deepcopy(result.get("target")),
        "counts": {
            "required": coverage.get("required_count"),
            "verified": coverage.get("verified_count"),
        },
        "model": file_identity(output_path),
    }
