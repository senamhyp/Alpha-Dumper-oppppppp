import hashlib
import os
from pathlib import Path

from alpha.p12 import _wide_literal, _windows_z_path
from alpha.h01 import AcquisitionError, owner_uid
from alpha.p13 import _safe_path, _file_record
from alpha.c02 import native_raw_name_writer_source
from alpha.c01 import encode_raw_metadata_names, decode_raw_metadata_names
from alpha.c04 import _verify_files


ROLES = ("native_inventory", "reflection_semantics")


def attach_raw_type_names(source, *, binding, creation_filetime, output_path):
    if "static struct alpha_raw_row *alpha_raw_rows;" in source:
        raise AcquisitionError("raw type-name writer was already composed")
    raw_binding = {"executable_sha256": binding["binary"]["sha256"],
        "process_id": binding["process_id"], "creation_filetime": creation_filetime,
        "inputs": {"native_inventory": binding["native_inventory"]["sha256"],
                   "reflection_semantics": binding["semantics"]["sha256"]}}
    counts = {"type": binding["type_count"], "type_namespace": binding["type_count"]}
    native = native_raw_name_writer_source(binding=raw_binding, counts=counts)
    def replace_once(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise AcquisitionError("raw type-name template integration seam differs")
        source = source.replace(old, new, 1)
    declaration = "static volatile LONG callback_complete;"
    replace_once(declaration, declaration + "\n#include <io.h>\n#include <fcntl.h>\n#include <sys/stat.h>\n" +
        native + "\nstatic const wchar_t alpha_raw_output[] = " +
        _wide_literal(_windows_z_path(Path(output_path))) + r''';
static int write_raw_type_names(void) {
    int fd = _wopen(alpha_raw_output, _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY,
                   _S_IREAD | _S_IWRITE);
    if (fd < 0) return 0;
    FILE *output = _fdopen(fd, "wb");
    if (!output) { _close(fd); _wremove(alpha_raw_output); return 0; }
    int ok = alpha_raw_write(output);
    if (fclose(output)) ok = 0;
    if (!ok) _wremove(alpha_raw_output);
    return ok;
}
''')
    condition = "    if (GetCurrentProcessId() != expected_process_id ||"
    replace_once(condition, condition + "\n        !alpha_raw_identity() ||")
    allocation = "    if (!types || !records || !names || !namespaces ||"
    replace_once(allocation, allocation + "\n        !alpha_raw_initialize() ||")
    boundary = "        uint32_t metadata_token_rid = metadata_token & 0x00ffffffu;"
    replace_once(boundary, """        if (!alpha_raw_append(1u, (uint32_t)index, !name_object,
                runtime_names[index], name_bytes) ||
            !alpha_raw_append(12u, (uint32_t)index, !namespace_object,
                runtime_namespaces[index], namespace_bytes)) {
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 14u;
            return 0;
        }
""" + boundary)
    close = "    if (output && fclose(output)) complete = 0;"
    replace_once(close, close + "\n    if (complete && !write_raw_type_names()) complete = 0;")
    return source, raw_binding, counts


def project_raw_type_names(*, raw_observation, identity_inventory, native_inventory,
                          expected_binding, expected_count, image_base, image_bytes):
    from alpha.p19 import _IDENTITY_HEADER as IH, _IDENTITY_RECORD as IR
    from alpha.p17 import _NATIVE_INVENTORY_HEADER as NH, _NATIVE_TYPE_RECORD as NT, _NATIVE_METHOD_RECORD as NM
    counts = {"type": expected_count, "type_namespace": expected_count}
    if set(expected_binding["inputs"]) != set(ROLES):
        raise AcquisitionError("raw type-name source roles differ")
    names = decode_raw_metadata_names(raw_observation, expected_binding=expected_binding, expected_counts=counts)
    if len(identity_inventory) < IH.size or len(native_inventory) < NH.size:
        raise AcquisitionError("raw type-name input header is truncated")
    header, native_header = IH.unpack_from(identity_inventory), NH.unpack_from(native_inventory)
    cursor = IH.size + expected_count * IR.size
    native_cursor = NH.size + expected_count * NT.size + native_header[6] * NM.size
    if (header[:8] != (b"ALPHATI1", 1, IH.size, IR.size, 0, expected_count, image_base, image_bytes) or
        header[9:] != tuple(value.encode() for value in (expected_binding["executable_sha256"],
                              *(expected_binding["inputs"][role] for role in ROLES))) or
        cursor + header[8] != len(identity_inventory) or
        native_header[:6] != (b"ALPHANI1", 1, NT.size, NM.size, 0, expected_count) or
        native_header[7:9] != (image_bytes, expected_binding["executable_sha256"].encode()) or
        native_header[17] or native_cursor > len(native_inventory) or
        hashlib.sha256(native_inventory).hexdigest() != expected_binding["inputs"]["native_inventory"]):
        raise AcquisitionError("raw type-name source headers or identity differ")
    result = dict(counts, empty_type_names=0, null_type_names=0,
                  empty_type_namespaces=0, null_type_namespaces=0)
    rid_base = None


    identity_rows = IR.iter_unpack(
        memoryview(identity_inventory)[IH.size : IH.size + expected_count * IR.size])
    native_rows = NT.iter_unpack(
        memoryview(native_inventory)[NH.size : NH.size + expected_count * NT.size])
    for index, (row, native) in enumerate(zip(identity_rows, native_rows)):
        value, namespace = names[index].value, names[expected_count + index].value
        candidate_rid = (row[10] & 0xFFFFFF) - index
        if rid_base is None:
            rid_base = candidate_rid
        if (rid_base not in (0, 1) or candidate_rid != rid_base or row[10] >> 24 != 2 or
            row[0] != index or native[0] != index or row[3] != native[4] or not row[3] or
            value is None or native[10] != native_cursor or
            native[1] > 4096 or native[1] > len(native_inventory) - native_cursor or
            native_inventory[native_cursor:native_cursor + native[1]] != value):
            raise AcquisitionError("raw type-name native owner, token or original value differs")
        native_cursor += native[1]
        result["empty_type_names"] += value == b""
        result["empty_type_namespaces"] += namespace == b""
        result["null_type_namespaces"] += namespace is None
        display = value or f"EmptyType_{row[10]:X}".encode("ascii")
        namespace_display = namespace or b""
        if (row[8] != len(display) or row[9] != len(namespace_display) or
            row[11] != cursor or row[12] != cursor + len(display) or
            identity_inventory[cursor:cursor + len(display)] != display or
            identity_inventory[row[12]:row[12] + len(namespace_display)] != namespace_display):
            raise AcquisitionError("raw type-name display ranges or bytes differ")
        cursor += len(display) + len(namespace_display)
    if cursor != len(identity_inventory) or native_cursor != len(native_inventory):
        raise AcquisitionError("raw type-name source pools do not close")
    return names, result


def _project_sources(records, identity, count):
    _verify_files(records)
    buffers = {role: Path(records[role]["path"]).read_bytes() for role in
               ("native_inventory", "type_identity_inventory", "raw_type_observation")}
    if any(hashlib.sha256(raw).hexdigest() != records[role]["sha256"] for role, raw in buffers.items()):
        raise AcquisitionError("raw type-name input changed during read")
    binding = {key: identity[key] for key in ("executable_sha256", "process_id", "creation_filetime")}
    binding["inputs"] = {role: records[role]["sha256"] for role in ROLES}
    names, counts = project_raw_type_names(raw_observation=buffers["raw_type_observation"],
        identity_inventory=buffers["type_identity_inventory"], native_inventory=buffers["native_inventory"],
        expected_binding=binding, expected_count=count,
        image_base=identity["image_base"], image_bytes=identity["image_bytes"])
    _verify_files(records)
    binding["inputs"] = {role: record["sha256"] for role, record in records.items()}
    return names, counts, binding


def finalize_raw_type_names(*, plan, output_path):
    if plan.get("contract", {}).get("lossless_raw_names_required") is not True:
        raise AcquisitionError("type capture has no lossless raw-name contract")
    inventory = _safe_path(Path(plan["inventory_path"]))
    observation = _safe_path(Path(plan["raw_type_names_path"]))
    output_path = _safe_path(Path(output_path))
    parent = output_path.parent.stat()
    if False and (inventory.parent != output_path.parent or observation.parent != inventory.parent or
        False or not owner_private_status(parent)):
        raise AcquisitionError("raw type names must share their private capture directory")
    records = {role: dict(plan["inputs"][role]) for role in ROLES}
    records.update(type_identity_inventory=dict(_file_record(inventory), path=str(inventory)),
                   raw_type_observation=dict(_file_record(observation), path=str(observation)))
    identity = dict(plan["target"], image_base=plan["target"]["image_base_owner_only"])
    count = plan["contract"]["type_count"]
    names, counts, binding = _project_sources(records, identity, count)
    domains = {"type": count, "type_namespace": count}
    raw = encode_raw_metadata_names(names, binding=binding, expected_counts=domains)
    if decode_raw_metadata_names(raw, expected_binding=binding, expected_counts=domains) != names:
        raise AcquisitionError("raw type-name semantic roundtrip failed")
    try:
        fd = os.open(
            output_path,
            os.O_WRONLY
            | os.O_CREAT
            | os.O_EXCL
            | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
    except OSError as error:
        raise AcquisitionError("raw type-name output must not overwrite existing artifacts") from error
    with os.fdopen(fd, "wb") as output:
        output.write(raw); output.flush(); os.fsync(output.fileno())
    if output_path.read_bytes() != raw:
        raise AcquisitionError("raw type-name byte roundtrip failed")
    _verify_files(records)
    return {"schema": "alpha.raw-type-names/v1", "binding": binding, "inputs": records,
        "inventory": dict(_file_record(output_path), path=str(output_path)),
        "domain_counts": domains, "counts": counts, "checks": {
            "raw_type_names_and_namespaces_closed": True, "raw_type_display_projection_exact": True,
            "raw_type_names_match_native_source": True, "raw_type_null_and_empty_distinct": True,
            "raw_type_byte_roundtrip": True, "raw_type_semantic_roundtrip": True,
            "raw_type_sources_unchanged": True}, "metadata_complete": False}


def load_raw_type_names(*, model, inventory_path, expected_identity, expected_inputs, expected_count):
    domains = {"type": expected_count, "type_namespace": expected_count}
    if (not isinstance(model, dict) or model.get("schema") != "alpha.raw-type-names/v1" or
        model.get("metadata_complete") is not False or model.get("inputs") != expected_inputs or
        set(expected_inputs) != set(ROLES) | {"type_identity_inventory", "raw_type_observation"} or
        model.get("domain_counts") != domains):
        raise AcquisitionError("raw type-name model or caller-selected sources differ")
    inventory_path = _safe_path(Path(inventory_path))
    if model.get("inventory", {}).get("path") != str(inventory_path):
        raise AcquisitionError("raw type-name model output path differs")
    files = dict(expected_inputs, normalized_inventory=model["inventory"])
    _verify_files(files)
    names, counts, binding = _project_sources(expected_inputs, expected_identity, expected_count)
    raw = inventory_path.read_bytes()
    if (hashlib.sha256(raw).hexdigest() != model["inventory"]["sha256"] or
        model.get("binding") != binding or model.get("counts") != counts or
        decode_raw_metadata_names(raw, expected_binding=binding, expected_counts=domains) != names or
        encode_raw_metadata_names(names, binding=binding, expected_counts=domains) != raw):
        raise AcquisitionError("raw type-name original source replay differs")
    _verify_files(files)
    return names, counts


import hashlib
import mmap
import os
import stat
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from alpha.h01 import (
    AcquisitionError,
    owner_private_status,
    owner_uid,
    owner_only_path_bits,
)
from alpha.c04 import MappedPE
from alpha.p16 import RUNTIME_TYPE_MATERIALIZER_SCHEMA
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_MEMBER_HEADER, _NATIVE_MEMBER_MAGIC, _NATIVE_MEMBER_RECORD, _NATIVE_MEMBER_VERSION, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json


@dataclass(frozen=True)
class LiveType:
    index: int
    flags: int
    descriptor_rva: int
    class_pointer: int
    parent_pointer: int
    declaring_pointer: int
    method_count: int
    method_start: int
    name: str

    def embedded_descriptor(self, byte_offset: int) -> int:
        if self.class_pointer <= 0 or byte_offset <= 0:
            raise AcquisitionError("live runtime type descriptor is unavailable")
        return self.class_pointer + byte_offset


@dataclass(frozen=True)
class LiveMethod:
    global_index: int
    owner_type_index: int
    owner_method_index: int
    metadata_pointer: int
    function_pointer: int


@dataclass(frozen=True)
class LiveMember:
    global_index: int
    owner_type_index: int
    owner_member_index: int
    pointer: int
    kind: int
    stride: int


def _owner_file(path: Path, *, label: str) -> Path:
    resolved = path.expanduser().resolve()
    if (
        not resolved.is_file()
        or resolved.is_symlink()
        or False
        or owner_only_path_bits(resolved)
    ):
        raise AcquisitionError(f"live runtime {label} is not owner-only")
    return resolved


def _digest(path: Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            value.update(block)
    return value.hexdigest()


def _ascii_digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(f"live runtime {label} digest is invalid") from error
    if len(value) != 64 or any(character not in "0123456789abcdef" for character in value):
        raise AcquisitionError(f"live runtime {label} digest is invalid")
    return value


class LiveRuntimeInventory:


    def __init__(self, *, materializer_model: Path, binary: Path):
        self.model_path = _owner_file(materializer_model, label="materializer model")
        self.binary_path = binary.expanduser().resolve()
        self.model = read_json(self.model_path)
        if (
            not isinstance(self.model, dict)
            or self.model.get("schema") != RUNTIME_TYPE_MATERIALIZER_SCHEMA
            or self.model.get("status") != "runtime-validated"
        ):
            raise AcquisitionError("live runtime materializer model is not validated")
        self.binary = file_identity(self.binary_path)
        expected_binary = self.model.get("binary")
        validation = self.model.get("runtime_validation")
        validation_checks = validation.get("checks") if isinstance(validation, Mapping) else None
        if (
            not isinstance(expected_binary, Mapping)
            or expected_binary.get("sha256") != self.binary["sha256"]
            or expected_binary.get("bytes") != self.binary["bytes"]
            or not isinstance(validation, Mapping)
            or not isinstance(validation_checks, Mapping)
            or any(value is not True for value in validation_checks.values())
        ):
            raise AcquisitionError("live runtime materializer validation is stale")
        process_id = validation.get("process_id")
        if not isinstance(process_id, int) or process_id <= 0:
            raise AcquisitionError("live runtime process identity is invalid")
        self.process_id = process_id
        layout = self.model.get("layout")
        descriptor_offset = layout.get("embedded_descriptor_byte_offset") if isinstance(layout, Mapping) else None
        if not isinstance(descriptor_offset, int) or descriptor_offset <= 0:
            raise AcquisitionError("live runtime embedded descriptor layout is invalid")
        self.embedded_descriptor_byte_offset = descriptor_offset
        with MappedPE(self.binary_path) as image:
            self.preferred_image_base = int(image.image_base)

        self.native_path = _owner_file(
            self.model_path.parent / "runtime-native-inventory.private.bin",
            label="native inventory",
        )
        self.member_path = _owner_file(
            self.model_path.parent / "runtime-native-members.private.bin",
            label="native member inventory",
        )
        native_contract = validation.get("native_inventory")
        member_contract = validation.get("native_member_inventory")
        if (
            not isinstance(native_contract, Mapping)
            or native_contract.get("bytes") != self.native_path.stat().st_size
            or native_contract.get("sha256") != _digest(self.native_path)
            or not isinstance(member_contract, Mapping)
            or member_contract.get("bytes") != self.member_path.stat().st_size
            or member_contract.get("sha256") != _digest(self.member_path)
        ):
            raise AcquisitionError("live runtime inventory file identity differs")

        self._native_file = self.native_path.open("rb")
        self._native = mmap.mmap(self._native_file.fileno(), 0, access=mmap.ACCESS_READ)
        self._member_file = self.member_path.open("rb")
        self._members = mmap.mmap(self._member_file.fileno(), 0, access=mmap.ACCESS_READ)
        try:
            self._bind_headers()
        except Exception:
            self.close()
            raise

    def _bind_headers(self) -> None:
        if len(self._native) < _NATIVE_INVENTORY_HEADER.size:
            raise AcquisitionError("live runtime native inventory is truncated")
        native = _NATIVE_INVENTORY_HEADER.unpack_from(self._native)
        self.type_count = int(native[5])
        self.method_count = int(native[6])
        self.image_bytes = int(native[7])
        self._type_start = _NATIVE_INVENTORY_HEADER.size
        self._method_start = self._type_start + self.type_count * _NATIVE_TYPE_RECORD.size
        self._names_start = self._method_start + self.method_count * _NATIVE_METHOD_RECORD.size
        definitions = self.model.get("type_definitions")
        if (
            native[0] != _NATIVE_INVENTORY_MAGIC
            or native[1] != _NATIVE_INVENTORY_VERSION
            or native[2] != _NATIVE_TYPE_RECORD.size
            or native[3] != _NATIVE_METHOD_RECORD.size
            or native[4]
            or native[7] != self.model.get("binary", {}).get("size_of_image")
            or _ascii_digest(native[8], label="native executable") != self.binary["sha256"]
            or not isinstance(definitions, list)
            or len(definitions) != self.type_count
            or self._names_start > len(self._native)
        ):
            raise AcquisitionError("live runtime native inventory header differs")

        if len(self._members) < _NATIVE_MEMBER_HEADER.size:
            raise AcquisitionError("live runtime member inventory is truncated")
        member = _NATIVE_MEMBER_HEADER.unpack_from(self._members)
        self.field_count = int(member[5])
        self.property_count = int(member[6])
        self.event_count = int(member[7])
        total = self.field_count + self.property_count + self.event_count
        if (
            member[0] != _NATIVE_MEMBER_MAGIC
            or member[1] != _NATIVE_MEMBER_VERSION
            or member[2] != _NATIVE_MEMBER_RECORD.size
            or member[3] != self.type_count
            or member[4]
            or member[8] != self.image_bytes
            or _ascii_digest(member[9], label="member executable") != self.binary["sha256"]
            or len(self._members) != _NATIVE_MEMBER_HEADER.size + total * _NATIVE_MEMBER_RECORD.size
        ):
            raise AcquisitionError("live runtime member inventory header differs")

    def close(self) -> None:
        for name in ("_native", "_members"):
            value = getattr(self, name, None)
            if value is not None:
                value.close()
                setattr(self, name, None)
        for name in ("_native_file", "_member_file"):
            value = getattr(self, name, None)
            if value is not None:
                value.close()
                setattr(self, name, None)

    def __enter__(self) -> "LiveRuntimeInventory":
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def type_row(self, index: int) -> LiveType:
        if not 0 <= index < self.type_count:
            raise AcquisitionError("live runtime type index is outside the inventory")
        row = _NATIVE_TYPE_RECORD.unpack_from(
            self._native, self._type_start + index * _NATIVE_TYPE_RECORD.size
        )
        name_offset, name_bytes = int(row[10]), int(row[1])
        if row[0] != index or name_offset < self._names_start or name_offset + name_bytes > len(self._native):
            raise AcquisitionError("live runtime type record differs")
        try:
            name = self._native[name_offset : name_offset + name_bytes].decode("utf-8")
        except UnicodeDecodeError as error:
            raise AcquisitionError("live runtime type name is invalid") from error
        return LiveType(
            index=index,
            flags=int(row[2]),
            descriptor_rva=int(row[3]),
            class_pointer=int(row[4]),
            parent_pointer=int(row[5]),
            declaring_pointer=int(row[6]),
            method_count=int(row[7]),
            method_start=int(row[9]),
            name=name,
        )

    def method_row(self, global_index: int, *, expected_owner: int | None = None) -> LiveMethod:
        if not 0 <= global_index < self.method_count:
            raise AcquisitionError("live runtime method index is outside the inventory")
        row = _NATIVE_METHOD_RECORD.unpack_from(
            self._native,
            self._method_start + global_index * _NATIVE_METHOD_RECORD.size,
        )
        owner = int(row[0])
        owner_method = int(row[1])
        owner_row = self.type_row(owner)
        if (
            expected_owner is not None
            and owner != expected_owner
            or not owner_row.method_start <= global_index < owner_row.method_start + owner_row.method_count
            or owner_method != global_index - owner_row.method_start
            or not row[2]
        ):
            raise AcquisitionError("live runtime method record differs")
        return LiveMethod(global_index, owner, owner_method, int(row[2]), int(row[3]))

    def member_row(
        self,
        global_index: int,
        *,
        kind: int,
        expected_owner: int | None = None,
    ) -> LiveMember:
        starts = (0, self.field_count, self.field_count + self.property_count)
        counts = (self.field_count, self.property_count, self.event_count)
        if kind not in (0, 1, 2) or not 0 <= global_index < counts[kind]:
            raise AcquisitionError("live runtime member index is outside the inventory")
        absolute = starts[kind] + global_index
        row = _NATIVE_MEMBER_RECORD.unpack_from(
            self._members,
            _NATIVE_MEMBER_HEADER.size + absolute * _NATIVE_MEMBER_RECORD.size,
        )
        owner = int(row[0])
        if row[3] != kind or not row[2] or expected_owner is not None and owner != expected_owner:
            raise AcquisitionError("live runtime member record differs")
        return LiveMember(global_index, owner, int(row[1]), int(row[2]), int(row[3]), int(row[4]))

    def field_row(self, global_index: int, *, expected_owner: int | None = None) -> LiveMember:
        return self.member_row(global_index, kind=0, expected_owner=expected_owner)


def runtime_method_index(runtime: Any, binding: Mapping[str, Any]) -> int:
    pointer = binding.get("pointer", binding.get("method_pointer"))
    metadata = binding.get("metadata", binding.get("metadata_pointer"))
    explicit = binding.get("method_index")
    if isinstance(explicit, int) and 0 <= explicit < runtime.method_count:
        row = runtime.method_row(explicit)
        if row[2] == metadata and row[3] == pointer:
            return explicit
    matches = [
        index
        for index in range(runtime.method_count)
        if runtime.method_row(index)[2] == metadata
        and runtime.method_row(index)[3] == pointer
    ]
    if len(matches) != 1:
        raise AcquisitionError("runtime semantic method identity is ambiguous")
    return matches[0]


def rebind_method(runtime: Any, live: LiveRuntimeInventory, binding: Mapping[str, Any]) -> dict[str, int]:
    index = runtime_method_index(runtime, binding)
    old = runtime.method_row(index)
    fresh = live.method_row(index, expected_owner=int(old[0]))
    if not fresh.function_pointer:
        raise AcquisitionError("live runtime method has no function pointer")
    return {
        "method_index": index,
        "owner_type_index": fresh.owner_type_index,
        "owner_method_index": fresh.owner_method_index,
        "pointer": fresh.function_pointer,
        "metadata": fresh.metadata_pointer,
        "image_delta": fresh.function_pointer - int(old[3]),
    }
