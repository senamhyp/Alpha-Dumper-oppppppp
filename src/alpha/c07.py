import collections
import struct
import threading
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.h04 import MemorySnapshot
from alpha.p16 import (
    METHOD_NAME_DECODE_OPERATION_CODES,
    REFLECTION_SEMANTICS_SCHEMA,
    _managed_string,
)
from alpha.p16 import RUNTIME_TYPE_MATERIALIZER_SCHEMA
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_MEMBER_HEADER, _NATIVE_MEMBER_MAGIC, _NATIVE_MEMBER_RECORD, _NATIVE_MEMBER_VERSION, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json


RUNTIME_NATIVE_SEMANTICS_SCHEMA = "alpha.runtime-native-semantics/v1"
_MASK64 = (1 << 64) - 1
_KINDS = ("field", "property", "event")
_SLOT_COUNTS = (4, 5, 6)
_CODEC_OPERATIONS = ("xor", "add", "subtract")
MIN_MANAGED_NAME_PAIR_COUNT = 2


@dataclass(frozen=True)
class NativeType:
    definition_index: int
    class_pointer: int
    methods: tuple[int, ...]
    method_pointers: tuple[int, ...] = ()
    descriptor_rva: int = 0
    hierarchy_pointer: int = 0


@dataclass(frozen=True)
class NativeMember:
    definition_index: int
    member_index: int
    pointer: int
    kind: int
    slots: tuple[int, ...]


@dataclass(frozen=True)
class FieldOffsetDecoder:
    method_pointer: int
    member_pointer_qword: int
    raw_dword_offset: int
    mask: int
    xor_key: int
    adjustment: int
    operation: str = "xor"


@dataclass(frozen=True)
class FieldTypeDecoderCandidate:
    method_pointer: int
    helper_pointer: int
    member_pointer_qword: int
    raw_qword_offset: int
    additive_constant: int
    operation: str = "add"
    adjustment: int = 0


@dataclass(frozen=True)
class FieldTypeDecoder:
    source_method_pointers: tuple[int, ...]
    helper_pointer: int
    member_pointer_qword: int
    raw_qword_offset: int
    additive_constant: int
    operation: str = "add"
    adjustment: int = 0


@dataclass(frozen=True)
class ClassParentDecoder:
    method_pointer: int
    raw_dword_offset: int
    base_pointer_slot: int
    base_pointer_indirections: int
    embedded_descriptor_adjustment: int
    managed_type_helper_pointer: int


def _decode(codec: dict[str, int | str], raw: int) -> int:
    operation = codec["operation"]
    key = codec["key"]
    if not isinstance(key, int):
        raise AcquisitionError("runtime native semantic codec key is invalid")
    if operation == "xor":
        return raw ^ key
    if operation == "add":
        return (raw - key) & _MASK64
    if operation == "subtract":
        return (key - raw) & _MASK64
    raise AcquisitionError("runtime native semantic codec operation is invalid")


def _codec_key(operation: str, raw: int, plain: int) -> int:
    if operation == "xor":
        return raw ^ plain
    if operation == "add":
        return (raw - plain) & _MASK64
    if operation == "subtract":
        return (raw + plain) & _MASK64
    raise AcquisitionError("runtime native semantic codec operation is invalid")


def _codec_key_xor(raw: int, plain: int) -> int:
    return raw ^ plain


def _codec_key_add(raw: int, plain: int) -> int:
    return (raw - plain) & _MASK64


def _codec_key_subtract(raw: int, plain: int) -> int:
    return (raw + plain) & _MASK64


_CODEC_KEY_BY_OPERATION = {
    "xor": _codec_key_xor,
    "add": _codec_key_add,
    "subtract": _codec_key_subtract,
}


def _owner_only(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError(f"runtime native semantic {label} is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError(f"runtime native semantic {label} is not owner-only")
    return path


def _ascii_digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime native semantic {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(character not in "0123456789abcdef" for character in value):
        raise AcquisitionError(f"runtime native semantic {label} digest is invalid")
    return value


_INVENTORY_MEMO_STABLE_FIELDS = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
_TYPES_METHODS_CACHE: tuple[Any, Any, Any] | None = None
_MEMBERS_CACHE: tuple[Any, Any, Any] | None = None


def _inventory_stable_fingerprint(path: Path) -> tuple[int, int, int, int, int] | None:
    try:
        status = path.stat()
    except OSError:
        return None
    return tuple(getattr(status, field) for field in _INVENTORY_MEMO_STABLE_FIELDS)


def _inventory_memo_fresh(
    path: Path, fingerprint: tuple[int, int, int, int, int] | None
) -> bool:
    if fingerprint is None:
        return False
    try:
        return _inventory_stable_fingerprint(path) == fingerprint
    except OSError:
        return False


def _load_types_and_methods(
    path: Path,
    *,
    executable_sha256: str,
    expected_identity: dict[str, Any],
) -> tuple[list[NativeType], dict[str, Any]]:
    global _TYPES_METHODS_CACHE
    path = _owner_only(path, label="type inventory")
    identity = file_identity(path)
    if identity["sha256"] != expected_identity.get("sha256") or identity[
        "bytes"
    ] != expected_identity.get("bytes"):
        raise AcquisitionError("runtime native semantic type inventory binding is stale")
    fingerprint = _inventory_stable_fingerprint(path)
    key = (str(path), fingerprint, executable_sha256)
    cached = _TYPES_METHODS_CACHE
    if cached is not None and fingerprint is not None and cached[0] == key:
        return cached[1], dict(cached[2])
    types, contract = _parse_types_and_methods(
        path, identity=identity, executable_sha256=executable_sha256
    )
    if _inventory_memo_fresh(path, fingerprint):
        _TYPES_METHODS_CACHE = (key, types, contract)
    return types, contract


def _parse_types_and_methods(
    path: Path,
    *,
    identity: dict[str, Any],
    executable_sha256: str,
) -> tuple[list[NativeType], dict[str, Any]]:
    data = path.read_bytes()
    if len(data) < _NATIVE_INVENTORY_HEADER.size:
        raise AcquisitionError("runtime native semantic type inventory is truncated")
    values = _NATIVE_INVENTORY_HEADER.unpack_from(data, 0)
    (
        magic,
        version,
        type_record_bytes,
        method_record_bytes,
        reserved,
        type_count,
        method_count,
        _image_bytes,
        executable_raw,
        materializer_raw,
        *_layout,
    ) = values
    if (
        magic != _NATIVE_INVENTORY_MAGIC
        or version != _NATIVE_INVENTORY_VERSION
        or type_record_bytes != _NATIVE_TYPE_RECORD.size
        or method_record_bytes != _NATIVE_METHOD_RECORD.size
        or reserved
        or not type_count
        or not method_count
        or _ascii_digest(executable_raw, label="executable") != executable_sha256
    ):
        raise AcquisitionError("runtime native semantic type inventory header is invalid")
    materializer_sha256 = _ascii_digest(materializer_raw, label="materializer")
    types_end = _NATIVE_INVENTORY_HEADER.size + type_count * _NATIVE_TYPE_RECORD.size
    methods_end = types_end + method_count * _NATIVE_METHOD_RECORD.size
    if methods_end > len(data):
        raise AcquisitionError("runtime native semantic type inventory is truncated")
    type_rows: list[tuple[Any, ...]] = []


    type_append = type_rows.append
    for expected_index, row in enumerate(
        _NATIVE_TYPE_RECORD.iter_unpack(
            memoryview(data)[
                _NATIVE_INVENTORY_HEADER.size : types_end
            ]
        )
    ):
        if (
            row[0] != expected_index
            or not row[4]
            or row[7] > method_count
            or row[9] > method_count
            or row[9] + row[7] > method_count
        ):
            raise AcquisitionError("runtime native semantic type row is invalid")
        type_append(row)
    methods: list[list[int]] = [[] for _ in range(type_count)]
    method_pointers: list[list[int]] = [[] for _ in range(type_count)]
    observed_method_count = 0
    for definition_index, method_index, metadata_pointer, method_pointer in (
        _NATIVE_METHOD_RECORD.iter_unpack(
            memoryview(data)[types_end:methods_end]
        )
    ):
        if (
            definition_index >= type_count
            or method_index != len(methods[definition_index])
            or not metadata_pointer
        ):
            raise AcquisitionError("runtime native semantic method row is invalid")
        methods[definition_index].append(metadata_pointer)
        method_pointers[definition_index].append(method_pointer)
        observed_method_count += 1
    if observed_method_count != method_count:
        raise AcquisitionError("runtime native semantic method count is invalid")
    types: list[NativeType] = []
    method_cursor = 0
    for index, (row, type_methods) in enumerate(zip(type_rows, methods)):
        if row[7] != len(type_methods) or row[9] != method_cursor:
            raise AcquisitionError("runtime native semantic method topology is invalid")
        types.append(
            NativeType(
                definition_index=index,
                class_pointer=row[4],
                methods=tuple(type_methods),
                method_pointers=tuple(method_pointers[index]),
                descriptor_rva=row[3],
                hierarchy_pointer=row[5],
            )
        )
        method_cursor += len(type_methods)
    return types, {
        "identity": identity,
        "type_count": type_count,
        "method_count": method_count,
        "materializer_model_sha256": materializer_sha256,
    }


def _load_members(
    path: Path,
    *,
    executable_sha256: str,
    expected_identity: dict[str, Any],
    type_count: int,
) -> tuple[tuple[list[NativeMember], ...], dict[str, Any]]:
    global _MEMBERS_CACHE
    path = _owner_only(path, label="member inventory")
    identity = file_identity(path)
    if identity["sha256"] != expected_identity.get("sha256") or identity[
        "bytes"
    ] != expected_identity.get("bytes"):
        raise AcquisitionError("runtime native semantic member inventory binding is stale")
    fingerprint = _inventory_stable_fingerprint(path)
    key = (str(path), fingerprint, executable_sha256, type_count)
    cached = _MEMBERS_CACHE
    if cached is not None and fingerprint is not None and cached[0] == key:
        return cached[1], dict(cached[2])
    domains, contract = _parse_members(
        path, identity=identity, executable_sha256=executable_sha256,
        type_count=type_count,
    )
    if _inventory_memo_fresh(path, fingerprint):
        _MEMBERS_CACHE = (key, domains, contract)
    return domains, contract


def _parse_members(
    path: Path,
    *,
    identity: dict[str, Any],
    executable_sha256: str,
    type_count: int,
) -> tuple[tuple[list[NativeMember], ...], dict[str, Any]]:
    data = path.read_bytes()
    if len(data) < _NATIVE_MEMBER_HEADER.size:
        raise AcquisitionError("runtime native semantic member inventory is truncated")
    values = _NATIVE_MEMBER_HEADER.unpack_from(data, 0)
    (
        magic,
        version,
        record_bytes,
        observed_type_count,
        reserved,
        field_count,
        property_count,
        event_count,
        _image_bytes,
        executable_raw,
        materializer_raw,
        helper_raw,
        *_layout,
    ) = values
    counts = (field_count, property_count, event_count)
    total = sum(counts)
    if (
        magic != _NATIVE_MEMBER_MAGIC
        or version != _NATIVE_MEMBER_VERSION
        or record_bytes != _NATIVE_MEMBER_RECORD.size
        or observed_type_count != type_count
        or reserved
        or any(not count for count in counts)
        or _ascii_digest(executable_raw, label="member executable")
        != executable_sha256
        or len(data) != _NATIVE_MEMBER_HEADER.size + total * record_bytes
    ):
        raise AcquisitionError("runtime native semantic member inventory header is invalid")
    materializer_sha256 = _ascii_digest(
        materializer_raw, label="member materializer"
    )
    helper_sha256 = _ascii_digest(helper_raw, label="native helper")


    slot_layouts = tuple(
        struct.Struct(f"<{slot_count}Q") for slot_count in _SLOT_COUNTS
    )
    strides = tuple(slot_count * 8 for slot_count in _SLOT_COUNTS)
    output: list[list[NativeMember]] = [[], [], []]
    expected_member = [collections.defaultdict(int) for _ in _KINDS]
    rows = _NATIVE_MEMBER_RECORD.iter_unpack(
        memoryview(data)[_NATIVE_MEMBER_HEADER.size :]
    )
    for expected_kind, count in enumerate(counts):
        layout = slot_layouts[expected_kind]
        stride = strides[expected_kind]
        expected_for_kind = expected_member[expected_kind]
        kind_rows = output[expected_kind]
        append = kind_rows.append
        for _ in range(count):
            definition_index, member_index, pointer, kind, observed_stride, payload = (
                next(rows)
            )
            if (
                kind != expected_kind
                or definition_index >= type_count
                or member_index != expected_for_kind[definition_index]
                or not pointer
                or observed_stride != stride
                or any(payload[stride:])
            ):
                raise AcquisitionError("runtime native semantic member row is invalid")
            expected_for_kind[definition_index] += 1
            append(
                NativeMember(
                    definition_index=definition_index,
                    member_index=member_index,
                    pointer=pointer,
                    kind=kind,
                    slots=layout.unpack_from(payload),
                )
            )
    return tuple(output), {
        "identity": identity,
        "counts": dict(zip(_KINDS, counts)),
        "materializer_model_sha256": materializer_sha256,
        "native_helper_model_sha256": helper_sha256,
    }


def _exact_scalar_codecs(
    rows: Iterable[tuple[int, int]],
    *,
    row_count: int,
) -> list[dict[str, int | str]]:


    iterator = iter(rows)
    try:
        first_raw, first_plain = next(iterator)
    except StopIteration:
        if 0 != row_count:
            raise AcquisitionError("runtime native semantic scalar domain is incomplete")
        return []
    key_xor = first_raw ^ first_plain
    key_add = (first_raw - first_plain) & _MASK64
    key_sub = (first_raw + first_plain) & _MASK64
    alive_xor = True
    alive_add = True
    alive_sub = True
    count = 1
    for raw, plain in iterator:
        count += 1
        if alive_xor and (raw ^ plain) != key_xor:
            alive_xor = False
        if alive_add and ((raw - plain) & _MASK64) != key_add:
            alive_add = False
        if alive_sub and ((raw + plain) & _MASK64) != key_sub:
            alive_sub = False
    if count != row_count:
        raise AcquisitionError("runtime native semantic scalar domain is incomplete")
    candidates: list[dict[str, int | str]] = []
    if alive_xor:
        candidates.append({"operation": "xor", "key": key_xor})
    if alive_add:
        candidates.append({"operation": "add", "key": key_add})
    if alive_sub:
        candidates.append({"operation": "subtract", "key": key_sub})
    return candidates


def _derive_parent_codec(
    members: list[NativeMember], types: list[NativeType]
) -> dict[str, int | str]:


    slot_count = len(members[0].slots)
    plains = [types[member.definition_index].class_pointer for member in members]
    member_count = len(members)
    candidates: list[dict[str, int | str]] = []
    mask = _MASK64
    for slot in range(slot_count):
        raw0 = members[0].slots[slot]
        plain0 = plains[0]
        key_xor = raw0 ^ plain0
        key_add = (raw0 - plain0) & mask
        key_sub = (raw0 + plain0) & mask
        alive_xor = True
        alive_add = True
        alive_sub = True
        for index in range(1, member_count):
            raw = members[index].slots[slot]
            plain = plains[index]
            if alive_xor and (raw ^ plain) != key_xor:
                alive_xor = False
                if not alive_add and not alive_sub:
                    break
            if alive_add and ((raw - plain) & mask) != key_add:
                alive_add = False
                if not alive_xor and not alive_sub:
                    break
            if alive_sub and ((raw + plain) & mask) != key_sub:
                alive_sub = False
                if not alive_xor and not alive_add:
                    break
        if alive_xor:
            candidates.append({"slot": slot, "operation": "xor", "key": key_xor})
        if alive_add:
            candidates.append({"slot": slot, "operation": "add", "key": key_add})
        if alive_sub:
            candidates.append(
                {"slot": slot, "operation": "subtract", "key": key_sub}
            )
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime native semantic parent codec is not structurally unique "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def _parse_class_parent_decoder(
    code: bytes,
    *,
    method_pointer: int,
) -> list[ClassParentDecoder]:
    candidates: list[ClassParentDecoder] = []
    for position in range(max(0, len(code) - 64)):
        if code[position : position + 2] != b"\x8b\x80":
            continue
        raw_dword_offset = struct.unpack_from("<I", code, position + 2)[0]
        window_end = min(len(code), position + 96)
        window = code[position + 6 : window_end]
        global_relative = window.find(b"\x48\x8b\x0d")
        if global_relative < 0:
            continue
        global_position = position + 6 + global_relative
        after_global = global_position + 7
        protected_shape = b"\x48\x8b\x09\x48\x01\xc1\x48\x83\xc1"
        shape_relative = code.find(
            protected_shape,
            after_global,
            min(len(code), after_global + 48),
        )
        if shape_relative < 0:
            continue
        adjustment_position = shape_relative + len(protected_shape)
        if adjustment_position >= len(code):
            continue
        adjustment = code[adjustment_position]
        tail_start = adjustment_position + 1
        tail_jump = code.find(
            b"\xe9", tail_start, min(len(code), tail_start + 40)
        )
        if tail_jump < 0 or tail_jump + 5 > len(code):
            continue
        base_pointer_slot = (
            method_pointer
            + global_position
            + 7
            + struct.unpack_from("<i", code, global_position + 3)[0]
        )
        managed_type_helper_pointer = (
            method_pointer
            + tail_jump
            + 5
            + struct.unpack_from("<i", code, tail_jump + 1)[0]
        )
        if (
            not raw_dword_offset
            or raw_dword_offset >= 4096
            or not adjustment
            or adjustment >= 256
        ):
            continue
        candidates.append(
            ClassParentDecoder(
                method_pointer=method_pointer,
                raw_dword_offset=raw_dword_offset,
                base_pointer_slot=base_pointer_slot,
                base_pointer_indirections=2,
                embedded_descriptor_adjustment=adjustment,
                managed_type_helper_pointer=managed_type_helper_pointer,
            )
        )
    return candidates


def _walk_class_parent_chain(
    snapshot: MemorySnapshot,
    hierarchy_pointer: int,
    class_pointer: int,
    by_class: dict[int, NativeType],
    bound: int,
) -> list[int]:
    chain: list[int] = []
    append = chain.append
    read_qwords = snapshot.qwords
    depth = 0
    while depth < bound:
        remaining = bound - depth
        span = 16 if remaining >= 16 else remaining
        values = read_qwords(hierarchy_pointer + depth * 8, span)
        if values is None:
            for offset in range(span):
                single = read_qwords(
                    hierarchy_pointer + (depth + offset) * 8, 1
                )
                if single is None:
                    return []
                current = single[0]
                if current not in by_class or current in chain:
                    return []
                append(current)
                if current == class_pointer:
                    return chain
        else:
            for current in values:
                if current not in by_class or current in chain:
                    return []
                append(current)
                if current == class_pointer:
                    return chain
        depth += span
    return chain


def _derive_class_parent_decoder(
    *,
    snapshot: MemorySnapshot,
    semantics: dict[str, Any],
    types: list[NativeType],
) -> tuple[ClassParentDecoder, dict[str, int]]:
    operations = [
        operation
        for operation in semantics.get("operations", [])
        if isinstance(operation, dict)
        and operation.get("key") == "type.base_type"
        and operation.get("semantic_identity_resolved") is True
    ]
    if len(operations) != 1:
        raise AcquisitionError(
            "runtime native semantic class-parent operation is not unique"
        )
    method_pointer = operations[0].get("method_pointer")
    if not isinstance(method_pointer, int) or not method_pointer:
        raise AcquisitionError(
            "runtime native semantic class-parent method is unavailable"
        )


    method_end = 0
    for native_type in types:
        for pointer in native_type.method_pointers:
            if pointer > method_pointer and (not method_end or pointer < method_end):
                method_end = pointer
    if not method_end:
        raise AcquisitionError(
            "runtime native semantic class-parent method extent is unavailable"
        )
    if method_end <= method_pointer or method_end - method_pointer > 65536:
        raise AcquisitionError(
            "runtime native semantic class-parent method extent is invalid"
        )
    code = snapshot.read(method_pointer, method_end - method_pointer)
    candidates = (
        _parse_class_parent_decoder(code, method_pointer=method_pointer)
        if code is not None
        else []
    )
    unique = {
        (
            candidate.raw_dword_offset,
            candidate.base_pointer_slot,
            candidate.base_pointer_indirections,
            candidate.embedded_descriptor_adjustment,
            candidate.managed_type_helper_pointer,
        ): candidate
        for candidate in candidates
    }
    if len(unique) != 1:
        raise AcquisitionError(
            "runtime native semantic class-parent decoder is not "
            f"structurally unique (candidates={len(unique)})"
        )
    decoder = next(iter(unique.values()))
    base_pointer = decoder.base_pointer_slot
    for _ in range(decoder.base_pointer_indirections):
        observed = snapshot.read(base_pointer, 8)
        if observed is None:
            raise AcquisitionError(
                "runtime native semantic class-parent base is unreadable"
            )
        base_pointer = int.from_bytes(observed, "little")
        if not base_pointer:
            raise AcquisitionError(
                "runtime native semantic class-parent base is null"
            )
    by_class = {native_type.class_pointer: native_type for native_type in types}


    raw_dword_offset = decoder.raw_dword_offset
    descriptor_adjustment = decoder.embedded_descriptor_adjustment
    image_base = snapshot.image_base
    snapshot_read = snapshot.read
    by_class_get = by_class.get
    chain_bound = len(by_class) + 1
    hierarchy_eligible = 0
    hierarchy_matches = 0
    hierarchy_mismatches = 0
    class_headers_readable = 0
    encoded_roots = 0
    decoded_parent_count = 0
    decoded_known_parent_count = 0
    decoded_unknown_parent_count = 0
    embedded_descriptor_readable = 0
    embedded_static_comparable = 0
    embedded_static_matches = 0
    for native_type in types:
        class_pointer = native_type.class_pointer
        raw = snapshot_read(
            class_pointer + raw_dword_offset, 4
        )
        if raw is None:
            continue
        class_headers_readable += 1
        encoded = int.from_bytes(raw, "little")
        decoded_parent = base_pointer + encoded if encoded else 0
        if encoded:
            decoded_parent_count += 1
            if decoded_parent in by_class:
                decoded_known_parent_count += 1
            else:
                decoded_unknown_parent_count += 1
            embedded = snapshot_read(
                decoded_parent + descriptor_adjustment,
                16,
            )
            if embedded is not None:
                embedded_descriptor_readable += 1
                known_parent = by_class_get(decoded_parent)
                if known_parent is not None and known_parent.descriptor_rva:
                    static = snapshot_read(
                        image_base + known_parent.descriptor_rva, 16
                    )
                    if static is not None:
                        embedded_static_comparable += 1
                        if static == embedded:
                            embedded_static_matches += 1
        else:
            encoded_roots += 1
        hierarchy_pointer = native_type.hierarchy_pointer
        if not hierarchy_pointer:
            continue
        chain = _walk_class_parent_chain(
            snapshot, hierarchy_pointer, class_pointer, by_class, chain_bound
        )
        if not chain or chain[-1] != class_pointer:
            continue
        expected_parent = chain[-2] if len(chain) > 1 else 0
        hierarchy_eligible += 1
        if decoded_parent == expected_parent:
            hierarchy_matches += 1
        else:
            hierarchy_mismatches += 1
    evidence = {
        "type_count": len(types),
        "class_header_readable_count": class_headers_readable,
        "class_header_snapshot_unavailable_count": len(types)
        - class_headers_readable,
        "encoded_root_count": encoded_roots,
        "decoded_parent_count": decoded_parent_count,
        "decoded_known_parent_count": decoded_known_parent_count,
        "decoded_unknown_parent_count": decoded_unknown_parent_count,
        "embedded_descriptor_readable_count": embedded_descriptor_readable,
        "embedded_static_comparable_count": embedded_static_comparable,
        "embedded_static_match_count": embedded_static_matches,
        "hierarchy_oracle_eligible_count": hierarchy_eligible,
        "hierarchy_oracle_match_count": hierarchy_matches,
        "hierarchy_oracle_mismatch_count": hierarchy_mismatches,
    }
    failed_requirements = []
    if hierarchy_eligible < 10_000:
        failed_requirements.append("hierarchy-oracle-support")
    if hierarchy_matches != hierarchy_eligible or hierarchy_mismatches:
        failed_requirements.append("hierarchy-oracle-agreement")


    if class_headers_readable < max(10_000, len(types) * 9 // 10):
        failed_requirements.append("class-header-coverage")
    if decoded_parent_count < len(types) * 9 // 10:
        failed_requirements.append("decoded-parent-coverage")
    if embedded_descriptor_readable < decoded_parent_count * 99 // 100:
        failed_requirements.append("embedded-descriptor-coverage")
    if embedded_static_comparable < 10_000:
        failed_requirements.append("embedded-static-support")
    if embedded_static_matches < embedded_static_comparable * 999 // 1000:
        failed_requirements.append("embedded-static-agreement")
    if failed_requirements:
        raise AcquisitionError(
            "runtime native semantic protected class-parent validation failed "
            f"(requirements={failed_requirements}; evidence={evidence}; "
            f"decoder={decoder})"
        )
    return decoder, evidence


def _method_codec_has_valid_key(
    *,
    raws: list[int],
    methods_by_member: list[tuple[int, ...]],
    operation: str,
) -> bool:
    member_count = len(raws)
    if not member_count:
        return False
    raw0 = raws[0]
    first_methods = methods_by_member[0]


    seen: set[int] = set()
    hypotheses: list[int] = []
    if raw0 not in seen:
        seen.add(raw0)
        hypotheses.append(raw0)
    if operation == "xor":
        for method in first_methods:
            key = raw0 ^ method
            if key not in seen:
                seen.add(key)
                hypotheses.append(key)
    elif operation == "add":
        mask = _MASK64
        for method in first_methods:
            key = (raw0 - method) & mask
            if key not in seen:
                seen.add(key)
                hypotheses.append(key)
    else:
        mask = _MASK64
        for method in first_methods:
            key = (method - raw0) & mask
            if key not in seen:
                seen.add(key)
                hypotheses.append(key)
    mask = _MASK64
    for key in hypotheses:
        nonzero = 0
        if operation == "xor":
            for index in range(member_count):
                decoded = raws[index] ^ key
                if decoded:
                    nonzero += 1
                    if decoded not in methods_by_member[index]:
                        break
            else:
                if nonzero:
                    return True
        elif operation == "add":
            for index in range(member_count):
                decoded = (raws[index] - key) & mask
                if decoded:
                    nonzero += 1
                    if decoded not in methods_by_member[index]:
                        break
            else:
                if nonzero:
                    return True
        else:
            for index in range(member_count):
                decoded = (key - raws[index]) & mask
                if decoded:
                    nonzero += 1
                    if decoded not in methods_by_member[index]:
                        break
            else:
                if nonzero:
                    return True
    return False


def _derive_method_codecs(
    members: list[NativeMember],
    types: list[NativeType],
    *,
    parent_slot: int,
) -> list[dict[str, int | str]]:
    candidates: list[dict[str, int | str]] = []
    slot_values: list[list[int]] = [
        [member.slots[slot] for member in members]
        for slot in range(len(members[0].slots))
    ]
    definition_indexes = [member.definition_index for member in members]
    methods_by_member = [types[index].methods for index in definition_indexes]
    for slot in range(len(members[0].slots)):
        if slot == parent_slot:
            continue
        raws = slot_values[slot]
        for operation in _CODEC_OPERATIONS:


            if not _method_codec_has_valid_key(
                raws=raws,
                methods_by_member=methods_by_member,
                operation=operation,
            ):
                continue


            keys = [
                raw ^ method
                for raw, member_methods in zip(raws, methods_by_member)
                for method in member_methods
            ] if operation == "xor" else [
                (raw - method) & _MASK64
                for raw, member_methods in zip(raws, methods_by_member)
                for method in member_methods
            ] if operation == "add" else [
                (method - raw) & _MASK64
                for raw, member_methods in zip(raws, methods_by_member)
                for method in member_methods
            ]
            if not keys:
                continue
            support = collections.Counter(keys)
            support_get = support.get
            key = max(support, key=support_get)
            method_support = support[key]
            if operation == "xor":
                decoded = [raw ^ key for raw in raws]
            elif operation == "add":
                decoded = [(raw - key) & _MASK64 for raw in raws]
            else:
                decoded = [(key - raw) & _MASK64 for raw in raws]
            nonzero = sum(value != 0 for value in decoded)
            valid = sum(
                value == 0 or value in types[index].methods
                for index, value in zip(definition_indexes, decoded)
            )
            if valid == len(members) and nonzero and method_support == nonzero:
                candidates.append(
                    {
                        "slot": slot,
                        "operation": operation,
                        "key": key,
                        "method_count": nonzero,
                        "null_count": len(members) - nonzero,
                    }
                )


    by_slot: dict[int, list[dict[str, int | str]]] = collections.defaultdict(list)
    for candidate in candidates:
        by_slot[int(candidate["slot"])].append(candidate)
    ambiguous = {slot: rows for slot, rows in by_slot.items() if len(rows) != 1}
    if ambiguous:
        raise AcquisitionError(
            "runtime native semantic method codec is ambiguous "
            f"(slots={sorted(ambiguous)})"
        )
    return [rows[0] for slot, rows in sorted(by_slot.items())]


def _reflection_name_pairs(
    *,
    snapshot: MemorySnapshot,
    semantics: dict[str, Any],
    members: list[NativeMember],
    runtime_owner: str,
) -> tuple[list[tuple[str, NativeMember]], dict[str, int]]:
    evidence = next(
        (
            value
            for value in semantics.get("object_evidence", [])
            if isinstance(value, dict) and value.get("runtime_owner") == runtime_owner
        ),
        None,
    )
    if not isinstance(evidence, dict):
        raise AcquisitionError("runtime native semantic name evidence is absent")
    class_pointer = evidence.get("class_pointer")
    name_qword = evidence.get("selected_field_qword")
    representative = evidence.get("representative")
    string_pointer = (
        representative.get("string_pointer")
        if isinstance(representative, dict)
        else None
    )
    string_header = snapshot.qwords(string_pointer, 1) if isinstance(
        string_pointer, int
    ) else None
    if (
        not isinstance(class_pointer, int)
        or not class_pointer
        or not isinstance(name_qword, int)
        or not 0 <= name_qword < 16
        or not string_header
        or not string_header[0]
    ):
        raise AcquisitionError("runtime native semantic name evidence is invalid")
    string_class = string_header[0]
    by_pointer = {member.pointer: member for member in members}
    pointer_support: collections.Counter[int] = collections.Counter()
    objects: list[tuple[int, ...]] = []
    for address in snapshot.references(class_pointer):
        values = snapshot.qwords(address, 16)
        if not values or values[0] != class_pointer:
            continue
        objects.append(values)
        for qword, value in enumerate(values):
            if value in by_pointer:
                pointer_support[qword] += 1
    if not pointer_support:
        raise AcquisitionError("runtime native semantic member-object link is absent")
    strongest = max(pointer_support.values())
    pointer_fields = [
        qword for qword, support in pointer_support.items() if support == strongest
    ]
    if len(pointer_fields) != 1 or strongest < 8:
        raise AcquisitionError(
            "runtime native semantic member-object link is not unique "
            f"(candidates={len(pointer_fields)}, support={strongest})"
        )
    pointer_qword = pointer_fields[0]
    pairs: list[tuple[str, NativeMember]] = []


    _managed_cache: dict[int, str | None] = {}
    for values in objects:
        member = by_pointer.get(values[pointer_qword])
        if member is None:
            continue
        string_pointer = values[name_qword]
        try:
            name = _managed_cache[string_pointer]
        except KeyError:
            name = _managed_string(
                snapshot,
                string_pointer,
                string_class=string_class,
                maximum=16_384,
            )
            _managed_cache[string_pointer] = name
        if name is not None:
            pairs.append((name, member))
    if len(pairs) < MIN_MANAGED_NAME_PAIR_COUNT:
        raise AcquisitionError(
            "runtime native semantic managed-name pair domain is incomplete "
            f"(owner={runtime_owner}, pairs={len(pairs)})"
        )
    return pairs, {
        "managed_object_count": len(objects),
        "member_pointer_qword": pointer_qword,
        "member_pointer_support": strongest,
        "managed_name_qword": name_qword,
        "managed_name_pair_count": len(pairs),
    }


def _name_anchor(
    pairs: list[tuple[str, NativeMember]],
) -> tuple[str, NativeMember, bytes]:
    named = [(name, member) for name, member in pairs if name]
    if not named:
        raise AcquisitionError("runtime native semantic name anchor is absent")
    anchor_name, anchor_member = max(named, key=lambda value: len(value[0]))
    try:
        anchor_raw = anchor_name.encode("utf-8") + b"\0"
    except UnicodeEncodeError as error:
        raise AcquisitionError("runtime native semantic name anchor is invalid") from error
    return anchor_name, anchor_member, anchor_raw


def _derive_name_codec(
    *,
    snapshot: MemorySnapshot,
    members: list[NativeMember],
    pairs: list[tuple[str, NativeMember]],
    observe_missing: Any = None,
    supplemental_names: dict[int, str] | None = None,
    anchor: tuple[str, NativeMember, bytes] | None = None,
    occurrences: Iterable[int] | None = None,
) -> tuple[dict[str, int | str], dict[str, int]]:


    _cstr_cache: dict[int, str | None] = {}

    def _cached_c_string(address: int) -> str | None:
        try:
            return _cstr_cache[address]
        except KeyError:
            pass
        value = snapshot.c_string(address, maximum=16_384)
        _cstr_cache[address] = value
        return value

    def lookup(address: int) -> str | None:
        value = _cached_c_string(address)
        return value if value is not None else (supplemental_names or {}).get(address)

    if anchor is None:
        anchor = _name_anchor(pairs)
    anchor_name, anchor_member, anchor_raw = anchor
    if occurrences is None:
        occurrences = list(snapshot.find_bytes(anchor_raw))
    else:


        occurrences = list(occurrences)
    if not occurrences or len(occurrences) > 4096:
        raise AcquisitionError(
            "runtime native semantic name anchor occurrence set is invalid"
        )
    candidates: list[dict[str, int | str]] = []
    partial: dict[tuple[int, str, int], tuple[dict[str, int | str], list[dict]]] = {}
    for slot in range(len(anchor_member.slots)):
        raw = anchor_member.slots[slot]
        for operation in _CODEC_OPERATIONS:
            for address in occurrences:
                codec: dict[str, int | str] = {
                    "slot": slot,
                    "operation": operation,
                    "key": _codec_key(operation, raw, address),
                }
                missing = []
                matched_owners = set()
                matched = 0
                for name, member in pairs:
                    name_pointer = _decode(codec, member.slots[slot])
                    actual = lookup(name_pointer)
                    if actual is None:
                        missing.append({"member_pointer": member.pointer, "slot": slot,
                            "encoded_value": member.slots[slot], "name_pointer": name_pointer, "name": name})
                    elif actual != name:
                        break
                    else:
                        matched += 1
                        matched_owners.add(member.definition_index)
                else:
                    if not missing:
                        candidates.append(codec)
                    elif matched >= max(8, MIN_MANAGED_NAME_PAIR_COUNT) and len(matched_owners) >= 2:
                        partial[(slot, operation, int(codec["key"]))] = (codec, missing)
    unique = {
        (int(value["slot"]), str(value["operation"]), int(value["key"])): value
        for value in candidates
    }
    if len(unique) != 1 or partial:
        if not unique and len(partial) == 1 and observe_missing is not None:
            _candidate, requests = next(iter(partial.values()))
            observations = observe_missing(requests)
            expected = {request["name_pointer"]: request["name"] for request in requests}
            if observations != expected:
                raise AcquisitionError("runtime native semantic supplemental name evidence is incomplete")
            codec, evidence = _derive_name_codec(snapshot=snapshot, members=members, pairs=pairs,
                                                supplemental_names=observations)
            evidence["runtime_verified_missing_name_pair_count"] = len(requests)
            return codec, evidence
        raise AcquisitionError(
            "runtime native semantic name codec is not structurally unique "
            f"(candidates={len(unique)}, incomplete_candidates={len(partial)})"
        )
    codec = next(iter(unique.values()))
    decoded = 0
    empty = 0
    live_verified = 0
    for member in members:
        address = _decode(codec, member.slots[int(codec["slot"])])
        name = lookup(address)
        if name is not None and supplemental_names and address in supplemental_names:
            live_verified += int(_cached_c_string(address) is None)
        if name is not None:
            decoded += 1
            if not name:
                empty += 1
    return codec, {
        "anchor_occurrence_count": len(occurrences),
        "managed_name_pair_count": len(pairs),
        "snapshot_decoded_name_count": decoded - live_verified,
        "snapshot_decoded_empty_name_count": empty,
        "snapshot_unavailable_name_count": len(members) - decoded + live_verified,
        "observed_decoded_name_count": decoded,
        "observed_unavailable_name_count": len(members) - decoded,
        "live_verified_name_count": live_verified,
    }


def _label_property_accessor_codecs(
    *,
    snapshot: MemorySnapshot,
    semantics: dict[str, Any],
    members: list[NativeMember],
    codecs: list[dict[str, int | str]],
    member_pointer_qword: int,
) -> tuple[list[dict[str, int | str]], dict[str, Any]]:
    object_evidence = next(
        (
            value
            for value in semantics.get("object_evidence", [])
            if isinstance(value, dict)
            and value.get("runtime_owner")
            == "System.Reflection.MonoProperty"
        ),
        None,
    )
    class_pointer = (
        object_evidence.get("class_pointer")
        if isinstance(object_evidence, dict)
        else None
    )
    accessor_fields = {
        value.get("operation_key"): value.get("selected_field_qword")
        for value in semantics.get("property_accessor_evidence", [])
        if isinstance(value, dict)
    }
    expected_fields = {
        "getter": accessor_fields.get("property.getter"),
        "setter": accessor_fields.get("property.setter"),
    }
    if (
        not isinstance(class_pointer, int)
        or class_pointer <= 0
        or set(expected_fields.values()) == {None}
        or any(
            not isinstance(field, int) or not 0 <= field < 32
            for field in expected_fields.values()
        )
        or len(codecs) != 2
    ):
        raise AcquisitionError(
            "runtime native semantic property accessor identity evidence is absent"
        )
    by_pointer = {member.pointer: member for member in members}
    support = {
        role: collections.Counter() for role in expected_fields
    }
    object_support = collections.Counter()
    for address in snapshot.references(class_pointer):
        fields = snapshot.qwords(address, 32)
        if not fields or fields[0] != class_pointer:
            continue
        member = by_pointer.get(fields[member_pointer_qword])
        if member is None:
            continue
        for role, field in expected_fields.items():
            method_object = fields[field]
            method_fields = (
                snapshot.qwords(method_object, 32) if method_object else None
            )
            if not method_fields:
                continue
            object_support[role] += 1
            for codec_index, codec in enumerate(codecs):
                slot = codec.get("slot")
                if not isinstance(slot, int) or not 0 <= slot < len(
                    member.slots
                ):
                    continue
                decoded = _decode(codec, member.slots[slot])
                if decoded and decoded in method_fields:
                    support[role][codec_index] += 1
    selected: dict[str, tuple[int, int]] = {}
    for role, counts in support.items():
        if not counts:
            raise AcquisitionError(
                "runtime native semantic property accessor identity is absent "
                f"(role={role})"
            )
        strongest = max(counts.values())
        candidates = [
            index for index, count in counts.items() if count == strongest
        ]
        if len(candidates) != 1 or strongest < 2:
            raise AcquisitionError(
                "runtime native semantic property accessor identity is not unique "
                f"(role={role}, candidates={len(candidates)}, "
                f"support={strongest})"
            )
        selected[role] = (candidates[0], strongest)
    if len({index for index, _support in selected.values()}) != len(
        selected
    ):
        raise AcquisitionError(
            "runtime native semantic property accessor codecs are not distinct"
        )
    labeled: list[dict[str, int | str]] = []
    for role in ("getter", "setter"):
        index, strongest = selected[role]
        labeled.append(
            {
                **codecs[index],
                "role": role,
                "semantic_support_count": strongest,
            }
        )
    return labeled, {
        "object_support": dict(sorted(object_support.items())),
        "codec_support": {
            role: dict(sorted(counts.items()))
            for role, counts in support.items()
        },
        "selected_codec_index": {
            role: index for role, (index, _support) in selected.items()
        },
        "selected_support": {
            role: strongest
            for role, (_index, strongest) in selected.items()
        },
    }


def _modrm_memory_operand(
    code: bytes,
    position: int,
    *,
    rex: int,
) -> tuple[int, int, int, int] | None:

    if position >= len(code):
        return None
    modrm = code[position]
    mode = modrm >> 6
    register = ((modrm >> 3) & 7) + (8 if rex & 4 else 0)
    base = (modrm & 7) + (8 if rex & 1 else 0)
    if mode == 0:


        if (modrm & 7) in (4, 5):
            return None
        return register, base, 0, position + 1
    if mode not in (1, 2) or (modrm & 7) == 4:
        return None
    displacement_bytes = 1 if mode == 1 else 4
    end = position + 1 + displacement_bytes
    if end > len(code):
        return None
    displacement = int.from_bytes(
        code[position + 1 : end], "little", signed=True
    )
    return register, base, displacement, end


def _register_immediate(
    code: bytes,
    position: int,
    *,
    register: int,
    operation: str,
) -> tuple[int, int] | None:
    rex = 0
    if position < len(code) and 0x40 <= code[position] <= 0x4F:
        rex = code[position]
        position += 1
    if position >= len(code):
        return None
    opcode = code[position]
    if register == 0 and operation == "xor" and opcode == 0x35:
        end = position + 5
        if end <= len(code):
            return int.from_bytes(code[position + 1 : end], "little"), end
        return None
    if register == 0 and operation in ("add", "subtract") and opcode in (
        0x05,
        0x2D,
    ):
        if (operation == "add") != (opcode == 0x05):
            return None
        end = position + 5
        if end <= len(code):
            immediate = int.from_bytes(
                code[position + 1 : end], "little", signed=True
            )
            return immediate if operation == "add" else -immediate, end
        return None
    if opcode not in (0x81, 0x83) or position + 2 > len(code):
        return None
    modrm = code[position + 1]
    extension = (modrm >> 3) & 7
    operand = (modrm & 7) + (8 if rex & 1 else 0)
    expected_extension = {"add": 0, "subtract": 5, "xor": 6}[operation]
    if modrm >> 6 != 3 or operand != register or extension != expected_extension:
        return None
    immediate_bytes = 1 if opcode == 0x83 else 4
    end = position + 2 + immediate_bytes
    if end > len(code):
        return None
    immediate = int.from_bytes(code[position + 2 : end], "little", signed=True)
    return immediate if operation != "subtract" else -immediate, end


def _parse_field_offset_decoder(
    code: bytes,
    *,
    method_pointer: int,
    expected_member_pointer_qword: int,
    member_stride: int,
) -> list[FieldOffsetDecoder]:
    record_registers: set[int] = set()
    for position in range(len(code)):
        cursor = position
        rex = 0
        if 0x40 <= code[cursor] <= 0x4F:
            rex = code[cursor]
            cursor += 1
        if not rex & 8 or cursor >= len(code) or code[cursor] != 0x8B:
            continue
        operand = _modrm_memory_operand(code, cursor + 1, rex=rex)
        if operand is None:
            continue
        destination, base, displacement, _end = operand
        if base == 1 and displacement == expected_member_pointer_qword * 8:
            record_registers.add(destination)
    if not record_registers:
        return []

    candidates: list[FieldOffsetDecoder] = []


    for position in range(len(code) - 5):
        cursor = position
        rex = 0
        if 0x40 <= code[cursor] <= 0x4F:
            rex = code[cursor]
            cursor += 1
        opcode = code[cursor]
        if not 0xB8 <= opcode <= 0xBF or cursor + 5 > len(code):
            continue
        result_register = opcode - 0xB8 + (8 if rex & 1 else 0)
        key = int.from_bytes(code[cursor + 1 : cursor + 5], "little")
        cursor += 5
        add_rex = 0
        if cursor < len(code) and 0x40 <= code[cursor] <= 0x4F:
            add_rex = code[cursor]
            cursor += 1
        if cursor >= len(code) or code[cursor] != 0x03:
            continue
        operand = _modrm_memory_operand(code, cursor + 1, rex=add_rex)
        if operand is None:
            continue
        destination, base, raw_offset, cursor = operand
        if (
            destination != result_register
            or base not in record_registers
            or raw_offset < 0
            or raw_offset + 4 > member_stride
        ):
            continue
        if result_register == 0 and code[cursor : cursor + 1] == b"\x25":
            if cursor + 5 > len(code):
                continue
            mask = int.from_bytes(code[cursor + 1 : cursor + 5], "little")
            cursor += 5
        else:
            and_rex = 0
            if cursor < len(code) and 0x40 <= code[cursor] <= 0x4F:
                and_rex = code[cursor]
                cursor += 1
            if cursor + 6 > len(code) or code[cursor] != 0x81:
                continue
            modrm = code[cursor + 1]
            register = (modrm & 7) + (8 if and_rex & 1 else 0)
            if modrm >> 6 != 3 or ((modrm >> 3) & 7) != 4 or register != result_register:
                continue
            mask = int.from_bytes(code[cursor + 2 : cursor + 6], "little")
            cursor += 6
        if not mask or mask == 0xFFFFFFFF or mask & (mask + 1):
            continue
        adjustment_result = _register_immediate(
            code, cursor, register=result_register, operation="add"
        )
        if adjustment_result is None:
            adjustment_result = _register_immediate(
                code, cursor, register=result_register, operation="subtract"
            )
        if adjustment_result is None:
            continue
        adjustment, cursor = adjustment_result
        while cursor < len(code) and code[cursor] in (0x90, 0x66):
            cursor += 1
        if cursor >= len(code) or code[cursor] not in (0xC3, 0xC2):
            continue
        candidates.append(
            FieldOffsetDecoder(
                method_pointer=method_pointer,
                member_pointer_qword=expected_member_pointer_qword,
                raw_dword_offset=raw_offset,
                mask=mask,
                xor_key=key,
                adjustment=adjustment,
                operation="add",
            )
        )

    for position in range(len(code) - 5):
        cursor = position
        rex = 0
        if 0x40 <= code[cursor] <= 0x4F:
            rex = code[cursor]
            cursor += 1
        opcode = code[cursor]
        if not 0xB8 <= opcode <= 0xBF or cursor + 5 > len(code):
            continue
        result_register = opcode - 0xB8 + (8 if rex & 1 else 0)
        mask = int.from_bytes(code[cursor + 1 : cursor + 5], "little")
        if not mask or mask == 0xFFFFFFFF or mask & (mask + 1):
            continue
        cursor += 5
        and_rex = 0
        if cursor < len(code) and 0x40 <= code[cursor] <= 0x4F:
            and_rex = code[cursor]
            cursor += 1
        if cursor >= len(code) or code[cursor] != 0x23:
            continue
        operand = _modrm_memory_operand(code, cursor + 1, rex=and_rex)
        if operand is None:
            continue
        destination, base, raw_offset, cursor = operand
        if (
            destination != result_register
            or base not in record_registers
            or raw_offset < 0
            or raw_offset + 4 > member_stride
        ):
            continue
        xor_result = _register_immediate(
            code, cursor, register=result_register, operation="xor"
        )
        if xor_result is None:
            continue
        xor_key, cursor = xor_result
        if xor_key & ~mask:
            continue
        adjustment_result = _register_immediate(
            code, cursor, register=result_register, operation="add"
        )
        if adjustment_result is None:
            adjustment_result = _register_immediate(
                code, cursor, register=result_register, operation="subtract"
            )
        if adjustment_result is None:
            continue
        adjustment, cursor = adjustment_result
        while cursor < len(code) and code[cursor] in (0x90, 0x66):
            cursor += 1
        if cursor >= len(code) or code[cursor] not in (0xC3, 0xC2):
            continue
        candidates.append(
            FieldOffsetDecoder(
                method_pointer=method_pointer,
                member_pointer_qword=expected_member_pointer_qword,
                raw_dword_offset=raw_offset,
                mask=mask,
                xor_key=xor_key,
                adjustment=adjustment,
                operation="xor",
            )
        )
    return candidates


def _decode_field_offset(decoder: FieldOffsetDecoder, member: NativeMember) -> int:
    payload = struct.pack(f"<{len(member.slots)}Q", *member.slots)
    raw = int.from_bytes(
        payload[decoder.raw_dword_offset : decoder.raw_dword_offset + 4], "little"
    )
    if decoder.operation == "xor":
        protected = (raw ^ decoder.xor_key) & decoder.mask
    elif decoder.operation == "add":
        protected = (raw + decoder.xor_key) & decoder.mask
    elif decoder.operation == "subtract":
        protected = (raw - decoder.xor_key) & decoder.mask
    else:
        raise AcquisitionError(
            "runtime native semantic field-offset operation is invalid"
        )
    unsigned = protected + decoder.adjustment
    unsigned &= 0xFFFFFFFF
    return unsigned if unsigned < 1 << 31 else unsigned - (1 << 32)


def _parse_field_type_decoder(
    code: bytes,
    *,
    method_pointer: int,
    expected_member_pointer_qword: int,
    member_stride: int,
) -> list[FieldTypeDecoderCandidate]:
    record_registers: set[int] = set()
    for position in range(len(code)):
        cursor = position
        rex = 0
        if 0x40 <= code[cursor] <= 0x4F:
            rex = code[cursor]
            cursor += 1
        if not rex & 8 or cursor >= len(code) or code[cursor] != 0x8B:
            continue
        operand = _modrm_memory_operand(code, cursor + 1, rex=rex)
        if operand is None:
            continue
        destination, base, displacement, _end = operand
        if base == 1 and displacement == expected_member_pointer_qword * 8:
            record_registers.add(destination)
    if not record_registers:
        return []

    candidates: list[FieldTypeDecoderCandidate] = []
    for position in range(len(code) - 10):
        cursor = position
        rex = 0
        if 0x40 <= code[cursor] <= 0x4F:
            rex = code[cursor]
            cursor += 1
        opcode = code[cursor]
        if (
            not rex & 8
            or not 0xB8 <= opcode <= 0xBF
            or cursor + 9 > len(code)
        ):
            continue
        result_register = opcode - 0xB8 + (8 if rex & 1 else 0)
        additive_constant = int.from_bytes(
            code[cursor + 1 : cursor + 9], "little"
        )
        cursor += 9
        add_rex = 0
        if cursor < len(code) and 0x40 <= code[cursor] <= 0x4F:
            add_rex = code[cursor]
            cursor += 1
        if (
            not add_rex & 8
            or cursor >= len(code)
            or code[cursor] not in (0x03, 0x33)
        ):
            continue
        operation = "add" if code[cursor] == 0x03 else "xor"
        operand = _modrm_memory_operand(code, cursor + 1, rex=add_rex)
        if operand is None:
            continue
        destination, base, raw_offset, cursor = operand
        if (
            destination != result_register
            or base not in record_registers
            or raw_offset < 0
            or raw_offset % 8
            or raw_offset + 8 > member_stride
        ):
            continue
        adjustment_result = _register_immediate(
            code, cursor, register=result_register, operation="add"
        )
        if adjustment_result is not None:
            adjustment, cursor = adjustment_result
            if operation == "add":
                additive_constant = (
                    additive_constant + adjustment
                ) & _MASK64
                adjustment = 0
        else:
            adjustment = 0
        if cursor + 5 > len(code) or code[cursor] != 0xE9:
            continue
        relative = int.from_bytes(code[cursor + 1 : cursor + 5], "little", signed=True)
        helper_pointer = method_pointer + cursor + 5 + relative
        candidates.append(
            FieldTypeDecoderCandidate(
                method_pointer=method_pointer,
                helper_pointer=helper_pointer,
                member_pointer_qword=expected_member_pointer_qword,
                raw_qword_offset=raw_offset,
                additive_constant=additive_constant,
                operation=operation,
                adjustment=adjustment,
            )
        )
    return candidates


def _decode_field_type(decoder: FieldTypeDecoder, member: NativeMember) -> int:
    if decoder.raw_qword_offset % 8:
        raise AcquisitionError("runtime native field-type qword is misaligned")
    slot = decoder.raw_qword_offset // 8
    if slot >= len(member.slots):
        raise AcquisitionError("runtime native field-type qword is out of range")
    raw = member.slots[slot]
    if decoder.operation == "add":
        decoded = (raw + decoder.additive_constant) & _MASK64
    elif decoder.operation == "xor":
        decoded = raw ^ decoder.additive_constant
    elif decoder.operation == "subtract":
        decoded = (raw - decoder.additive_constant) & _MASK64
    else:
        raise AcquisitionError(
            "runtime native field-type operation is invalid"
        )
    return (decoded + decoder.adjustment) & _MASK64


def _derive_field_type_decoder(
    *,
    binary: Path,
    snapshot: MemorySnapshot,
    semantics: dict[str, Any],
    types: list[NativeType],
    members: list[NativeMember],
    member_pointer_qword: int,
) -> tuple[FieldTypeDecoder, dict[str, Any]]:
    from alpha.p02 import derive_current_store

    if not members:
        raise AcquisitionError("runtime native field type domain is empty")
    evidence = derive_current_store(binary=binary, semantics=semantics, types=types, snapshot=snapshot)
    candidate = evidence["candidate"]
    if candidate["raw_qword_offset"] + 8 > len(members[0].slots) * 8:
        raise AcquisitionError("runtime native field type load exceeds member stride")
    decoder = FieldTypeDecoder(
        source_method_pointers=tuple(sorted({*evidence["source_operations"].values(), evidence["factory_helper"]})),
        helper_pointer=candidate["type_object_helper"], member_pointer_qword=member_pointer_qword,
        raw_qword_offset=candidate["raw_qword_offset"], additive_constant=candidate["key"],
        operation=candidate["operation"], adjustment=0,
    )
    pointers = [_decode_field_type(decoder, member) for member in members]
    if any(not pointer or pointer % 8 for pointer in pointers):
        raise AcquisitionError("runtime native field type descriptor domain is invalid")
    distinct = set(pointers)
    readable = {p for p in distinct if snapshot.read(p, 16) is not None}
    if not readable:
        raise AcquisitionError("runtime native field type has no descriptor byte evidence")
    readable_fields = sum(p in readable for p in pointers)
    evidence.update(decoded_field_count=len(pointers), distinct_descriptor_count=len(distinct),
        snapshot_readable_field_count=readable_fields, snapshot_unavailable_field_count=len(pointers) - readable_fields,
        snapshot_readable_distinct_descriptor_count=len(readable), snapshot_unavailable_distinct_descriptor_count=len(distinct) - len(readable),
        descriptor_prefix_observation_bytes=16, descriptor_size_proven=False,
        role_source="current-native-field-factory-cached-type-and-attribute-store",
        all_field_type_reference_graphs_verified=False, redundant_arithmetic_decoder_count=1)
    return decoder, evidence


def _derive_owner_descriptor_candidate(
    *,
    snapshot: MemorySnapshot,
    semantics: dict[str, Any],
    types: list[NativeType],
    members: list[NativeMember],
    member_pointer_qword: int,
) -> tuple[FieldTypeDecoder, dict[str, int]]:

    evidence = next(
        (
            value
            for value in semantics.get("object_evidence", [])
            if isinstance(value, dict)
            and value.get("runtime_owner") == "System.Reflection.MonoField"
        ),
        None,
    )
    class_pointer = evidence.get("class_pointer") if isinstance(evidence, dict) else None
    owners = [value for value in types if value.class_pointer == class_pointer]
    if len(owners) != 1 or not owners[0].method_pointers:
        raise AcquisitionError("runtime native semantic field owner is not unique")
    owner = owners[0]
    image_lower, image_upper = snapshot.image_range
    import bisect as _bisect

    all_method_pointers = sorted(
        {
            pointer
            for native_type in types
            for pointer in native_type.method_pointers
            if image_lower <= pointer < image_upper
        }
    )

    def _following(pointer: int) -> int | None:
        position = _bisect.bisect_right(all_method_pointers, pointer)
        if (
            position == 0
            or position >= len(all_method_pointers)
            or all_method_pointers[position - 1] != pointer
        ):
            return None
        return all_method_pointers[position]

    observations: list[FieldTypeDecoderCandidate] = []
    inspected = 0
    for method_pointer in sorted(set(owner.method_pointers)):
        end = _following(method_pointer)
        if end is None or end <= method_pointer:
            continue
        code = snapshot.read(method_pointer, end - method_pointer)
        if code is None:
            continue
        inspected += 1
        observations.extend(
            _parse_field_type_decoder(
                code,
                method_pointer=method_pointer,
                expected_member_pointer_qword=member_pointer_qword,
                member_stride=len(members[0].slots) * 8,
            )
        )
    groups: dict[
        tuple[int, int, int, int, str, int], set[int]
    ] = collections.defaultdict(set)
    for observation in observations:
        groups[
            (
                observation.helper_pointer,
                observation.member_pointer_qword,
                observation.raw_qword_offset,
                observation.additive_constant,
                observation.operation,
                observation.adjustment,
            )
        ].add(observation.method_pointer)
    qualified = [
        (key, source_methods)
        for key, source_methods in groups.items()
        if source_methods
    ]
    if len(qualified) != 1:
        raise AcquisitionError(
            "runtime native semantic field-type decoder is not structurally unique "
            f"(groups={len(groups)}, redundant_groups={len(qualified)})"
        )
    (
        helper_pointer,
        source_member_qword,
        raw_qword_offset,
        additive_constant,
        operation,
        adjustment,
    ), source_methods = qualified[0]
    if not image_lower <= helper_pointer < image_upper:
        raise AcquisitionError("runtime native semantic field-type helper is stale")
    decoder = FieldTypeDecoder(
        source_method_pointers=tuple(sorted(source_methods)),
        helper_pointer=helper_pointer,
        member_pointer_qword=source_member_qword,
        raw_qword_offset=raw_qword_offset,
        additive_constant=additive_constant,
        operation=operation,
        adjustment=adjustment,
    )
    pointers = [_decode_field_type(decoder, member) for member in members]
    if any(not pointer or pointer % 8 for pointer in pointers):
        raise AcquisitionError(
            "runtime native semantic field-type descriptor domain is invalid"
        )
    distinct_pointers = set(pointers)
    readable: dict[int, tuple[int, ...]] = {}
    for pointer in distinct_pointers:
        values = snapshot.qwords(pointer, 2)
        if values is not None:
            readable[pointer] = values
    structurally_valid = sum(
        values[1] >> 32 == 0 and ((values[1] >> 16) & 0xFF) != 0
        for values in readable.values()
    )
    if not readable or structurally_valid != len(readable):
        raise AcquisitionError(
            "runtime native semantic field-type descriptor validation failed"
        )
    readable_fields = sum(pointer in readable for pointer in pointers)
    return decoder, {
        "owner_method_body_count": inspected,
        "redundant_source_method_count": len(source_methods),
        "decoded_field_count": len(pointers),
        "distinct_descriptor_count": len(distinct_pointers),
        "snapshot_readable_field_count": readable_fields,
        "snapshot_unavailable_field_count": len(pointers) - readable_fields,
        "snapshot_readable_distinct_descriptor_count": len(readable),
        "snapshot_unavailable_distinct_descriptor_count": len(distinct_pointers)
        - len(readable),
        "structurally_valid_distinct_descriptor_count": structurally_valid,
        "distinct_type_enum_count": len(
            {(values[1] >> 16) & 0xFF for values in readable.values()}
        ),
    }


def _derive_field_offset_decoder(
    *,
    snapshot: MemorySnapshot,
    semantics: dict[str, Any],
    types: list[NativeType],
    members: list[NativeMember],
    member_pointer_qword: int,
) -> tuple[FieldOffsetDecoder, dict[str, int]]:
    evidence = next(
        (
            value
            for value in semantics.get("object_evidence", [])
            if isinstance(value, dict)
            and value.get("runtime_owner") == "System.Reflection.MonoField"
        ),
        None,
    )
    class_pointer = evidence.get("class_pointer") if isinstance(evidence, dict) else None
    owners = [value for value in types if value.class_pointer == class_pointer]
    if len(owners) != 1 or not owners[0].method_pointers:
        raise AcquisitionError("runtime native semantic field owner is not unique")
    owner = owners[0]
    image_lower, image_upper = snapshot.image_range
    import bisect as _bisect

    all_method_pointers = sorted(
        {
            pointer
            for native_type in types
            for pointer in native_type.method_pointers
            if image_lower <= pointer < image_upper
        }
    )

    def _following(pointer: int) -> int | None:
        position = _bisect.bisect_right(all_method_pointers, pointer)
        if (
            position == 0
            or position >= len(all_method_pointers)
            or all_method_pointers[position - 1] != pointer
        ):
            return None
        return all_method_pointers[position]

    candidates: list[FieldOffsetDecoder] = []
    inspected = 0
    for method_pointer in sorted(set(owner.method_pointers)):
        end = _following(method_pointer)
        if end is None or end <= method_pointer:
            continue
        code = snapshot.read(method_pointer, end - method_pointer)
        if code is None:
            continue
        inspected += 1
        candidates.extend(
            _parse_field_offset_decoder(
                code,
                method_pointer=method_pointer,
                expected_member_pointer_qword=member_pointer_qword,
                member_stride=len(members[0].slots) * 8,
            )
        )
    unique = {
        (
            value.method_pointer,
            value.member_pointer_qword,
            value.raw_dword_offset,
            value.mask,
            value.xor_key,
            value.adjustment,
            value.operation,
        ): value
        for value in candidates
    }
    if len(unique) != 1:
        raise AcquisitionError(
            "runtime native semantic field-offset decoder is not structurally unique "
            f"(candidates={len(unique)})"
        )
    decoder = next(iter(unique.values()))
    offsets = [_decode_field_offset(decoder, member) for member in members]
    return decoder, {
        "owner_method_body_count": inspected,
        "decoded_field_count": len(offsets),
        "distinct_offset_count": len(set(offsets)),
        "negative_offset_count": sum(value < 0 for value in offsets),
        "zero_offset_count": sum(value == 0 for value in offsets),
        "positive_offset_count": sum(value > 0 for value in offsets),
        "minimum_offset": min(offsets),
        "maximum_offset": max(offsets),
    }


def inspect_runtime_native_semantics(
    *,
    binary: Path,
    snapshot: Path,
    reflection_semantics_model: Path,
    materializer_model: Path,
    native_inventory: Path,
    native_member_inventory: Path,
    output: Path,
    name_observer: Any = None,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    snapshot = _owner_only(snapshot, label="memory snapshot")
    reflection_semantics_model = _owner_only(
        reflection_semantics_model, label="reflection semantic model"
    )
    materializer_model = _owner_only(
        materializer_model, label="validated materializer model"
    )
    identity = file_identity(binary)
    materializer = read_json(materializer_model)
    semantics = read_json(reflection_semantics_model)
    validation = materializer.get("runtime_validation") if isinstance(
        materializer, dict
    ) else None
    validation_checks = validation.get("checks") if isinstance(validation, dict) else None
    if (
        not isinstance(materializer, dict)
        or materializer.get("schema") != RUNTIME_TYPE_MATERIALIZER_SCHEMA
        or materializer.get("status") != "runtime-validated"
        or materializer.get("binary", {}).get("sha256") != identity["sha256"]
        or not isinstance(validation_checks, dict)
        or validation_checks.get("native_inventory_type_rows_bound") is not True
        or validation_checks.get("native_inventory_method_rows_bound") is not True
        or validation_checks.get("native_member_inventory_rows_bound") is not True
    ):
        raise AcquisitionError("runtime native semantic materializer is not validated")
    if (
        not isinstance(semantics, dict)
        or semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("binary", {}).get("sha256") != identity["sha256"]
        or semantics.get("snapshot", {}).get("sha256")
        != file_identity(snapshot)["sha256"]
        or semantics.get("checks", {}).get("method_name_decoder_derived") is not True
        or semantics.get("checks", {}).get("name_getters_semantically_unique")
        is not True
    ):
        raise AcquisitionError("runtime native semantic reflection binding is stale")
    expected_native = validation.get("native_inventory")
    expected_members = validation.get("native_member_inventory")
    if not isinstance(expected_native, dict) or not isinstance(expected_members, dict):
        raise AcquisitionError("runtime native semantic inventory binding is absent")
    types, native_contract = _load_types_and_methods(
        native_inventory,
        executable_sha256=identity["sha256"],
        expected_identity=expected_native,
    )
    members, member_contract = _load_members(
        native_member_inventory,
        executable_sha256=identity["sha256"],
        expected_identity=expected_members,
        type_count=len(types),
    )
    if (
        native_contract["materializer_model_sha256"]
        != member_contract["materializer_model_sha256"]
    ):
        raise AcquisitionError("runtime native semantic materializer hashes differ")

    parent_codecs = {
        kind: _derive_parent_codec(members[index], types)
        for index, kind in enumerate(_KINDS)
    }
    property_methods = _derive_method_codecs(
        members[1], types, parent_slot=int(parent_codecs["property"]["slot"])
    )
    event_methods = _derive_method_codecs(
        members[2], types, parent_slot=int(parent_codecs["event"]["slot"])
    )
    if len(property_methods) != 2 or len(event_methods) != 2:
        raise AcquisitionError(
            "runtime native semantic accessor topology is incomplete "
            f"(property={len(property_methods)}, event={len(event_methods)})"
        )
    name_codecs: dict[str, dict[str, int | str]] = {}
    name_evidence: dict[str, dict[str, int]] = {}
    with MemorySnapshot(snapshot) as memory:


        memory.capture_reference_hits(
            {
                evidence["class_pointer"]
                for evidence in semantics.get("object_evidence", [])
                if isinstance(evidence, dict)
                and isinstance(evidence.get("class_pointer"), int)
                and evidence["class_pointer"] > 0
            }
        )
        class_parent_decoder, class_parent_evidence = (
            _derive_class_parent_decoder(
                snapshot=memory,
                semantics=semantics,
                types=types,
            )
        )


        name_inputs = []
        for kind, runtime_owner, member_index in (
            ("field", "System.Reflection.MonoField", 0),
            ("property", "System.Reflection.MonoProperty", 1),
        ):
            pairs, object_evidence = _reflection_name_pairs(
                snapshot=memory,
                semantics=semantics,
                members=members[member_index],
                runtime_owner=runtime_owner,
            )
            name_inputs.append(
                (kind, member_index, pairs, object_evidence,
                 _name_anchor(pairs))
            )
        occurrence_tables = memory.find_bytes_many(
            [anchor[2] for _kind, _index, _pairs, _evidence, anchor
             in name_inputs]
        )
        for kind, member_index, pairs, object_evidence, anchor in name_inputs:
            occurrences = occurrence_tables[anchor[2]]
            if not occurrences or len(occurrences) > 4096:
                raise AcquisitionError(
                    "runtime native semantic name anchor occurrence set is "
                    "invalid"
                )
            codec, codec_evidence = _derive_name_codec(
                snapshot=memory,
                members=members[member_index],
                pairs=pairs,
                observe_missing=name_observer,
                anchor=anchor,
                occurrences=occurrences,
            )
            name_codecs[kind] = codec
            name_evidence[kind] = {**object_evidence, **codec_evidence}
        property_methods, property_accessor_role_evidence = (
            _label_property_accessor_codecs(
                snapshot=memory,
                semantics=semantics,
                members=members[1],
                codecs=property_methods,
                member_pointer_qword=name_evidence["property"][
                    "member_pointer_qword"
                ],
            )
        )
        field_offset_decoder, field_offset_evidence = _derive_field_offset_decoder(
            snapshot=memory,
            semantics=semantics,
            types=types,
            members=members[0],
            member_pointer_qword=name_evidence["field"]["member_pointer_qword"],
        )
        field_type_decoder, field_type_evidence = _derive_field_type_decoder(
            binary=binary,
            snapshot=memory,
            semantics=semantics,
            types=types,
            members=members[0],
            member_pointer_qword=name_evidence["field"]["member_pointer_qword"],
        )
    model = {
        "schema": RUNTIME_NATIVE_SEMANTICS_SCHEMA,
        "status": "partially-resolved",
        "stage": "protected-class-parent-and-native-member-codecs-derived",
        "binary": identity,
        "inputs": {
            "materializer_model": file_identity(materializer_model),
            "snapshot": file_identity(snapshot),
            "reflection_semantics_model": file_identity(
                reflection_semantics_model
            ),
            "native_inventory": native_contract["identity"],
            "native_member_inventory": member_contract["identity"],
            "source_materializer_model_sha256": native_contract[
                "materializer_model_sha256"
            ],
            "native_helper_model_sha256": member_contract[
                "native_helper_model_sha256"
            ],
        },
        "counts": {
            "types": len(types),
            "methods": native_contract["method_count"],
            **member_contract["counts"],
        },
        "parent_codecs": parent_codecs,
        "class_parent_decoder": {
            "method_pointer": class_parent_decoder.method_pointer,
            "raw_dword_offset": class_parent_decoder.raw_dword_offset,
            "base_pointer_slot": class_parent_decoder.base_pointer_slot,
            "base_pointer_indirections": (
                class_parent_decoder.base_pointer_indirections
            ),
            "embedded_descriptor_adjustment": (
                class_parent_decoder.embedded_descriptor_adjustment
            ),
            "managed_type_helper_pointer": (
                class_parent_decoder.managed_type_helper_pointer
            ),
        },
        "class_parent_evidence": class_parent_evidence,
        "accessor_codecs": {
            "property": property_methods,
            "event": event_methods,
        },
        "property_accessor_role_evidence": property_accessor_role_evidence,
        "name_codecs": name_codecs,
        "name_evidence": name_evidence,
        "field_offset_decoder": {
            "method_pointer": field_offset_decoder.method_pointer,
            "member_pointer_qword": field_offset_decoder.member_pointer_qword,
            "raw_dword_offset": field_offset_decoder.raw_dword_offset,
            "mask": field_offset_decoder.mask,
            "xor_key": field_offset_decoder.xor_key,
            "adjustment": field_offset_decoder.adjustment,
            "operation": field_offset_decoder.operation,
        },
        "field_offset_evidence": field_offset_evidence,
        "field_type_decoder": {
            "source_method_pointers": list(field_type_decoder.source_method_pointers),
            "helper_pointer": field_type_decoder.helper_pointer,
            "member_pointer_qword": field_type_decoder.member_pointer_qword,
            "raw_qword_offset": field_type_decoder.raw_qword_offset,
            "additive_constant": field_type_decoder.additive_constant,
            "operation": field_type_decoder.operation,
            "adjustment": field_type_decoder.adjustment,
        },
        "field_type_evidence": field_type_evidence,
        "checks": {
            "target_identity_bound": True,
            "validated_materializer_bound": True,
            "native_inventory_identity_bound": True,
            "native_member_inventory_identity_bound": True,
            "native_inventory_rows_revalidated": True,
            "native_member_rows_revalidated": True,
            "field_parent_codec_structurally_unique": True,
            "property_parent_codec_structurally_unique": True,
            "event_parent_codec_structurally_unique": True,
            "class_parent_decoder_structurally_unique": True,
            "class_parent_decoder_current_code_derived": True,
            "class_parent_decoder_hierarchy_oracle_exact": True,
            "class_parent_embedded_descriptors_structurally_valid": True,
            "property_accessor_codecs_close_over_all_records": True,
            "property_accessor_codecs_semantically_labeled": True,
            "event_accessor_codecs_close_over_all_records": True,
            "reflection_semantics_identity_bound": True,
            "snapshot_identity_bound": True,
            "field_name_codec_structurally_unique": True,
            "property_name_codec_structurally_unique": True,
            "field_offset_decoder_structurally_unique": True,
            "field_offset_decoder_closes_over_all_records": True,
            "field_type_decoder_structurally_unique": True,
            "field_type_decoder_redundantly_observed": False,
            "field_type_decoder_cached_type_store_bound": True,
            "field_type_decoder_same_object_attribute_store_bound": True,
            "field_type_decoder_closes_over_all_records": True,
            "field_type_readable_descriptor_prefixes_observed": True,
            "all_field_type_reference_graphs_verified": False,
            "external_runtime_component_used": False,
            "saved_reference_values_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "fixed_rva_used": False,
            "fixed_version_used": False,
        },
        "raw_codec_keys_and_slots_owner_only": True,
    }
    _private_json(output, model)
    return {
        "schema": RUNTIME_NATIVE_SEMANTICS_SCHEMA,
        "status": model["status"],
        "stage": model["stage"],
        "target": {"executable_sha256": identity["sha256"]},
        "counts": model["counts"],
        "derived": {
            "parent_codec_count": len(parent_codecs),
            "property_accessor_codec_count": len(property_methods),
            "event_accessor_codec_count": len(event_methods),
            "name_codec_count": len(name_codecs),
            "field_offset_decoder_count": 1,
            "field_type_decoder_count": 1,
            "class_parent_decoder_count": 1,
        },
        "checks": model["checks"],
        "raw_codec_keys_slots_and_pointers_exposed": False,
    }


from alpha.h02 import windows_run as _host_run

import json
import os
import struct
import subprocess
import time
from collections import defaultdict, deque
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

from alpha.p12 import SNAPSHOT_SCHEMA, _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid
from alpha.h04 import MemorySnapshot
from alpha.p14 import REFLECTION_BOOTSTRAP_SCHEMA
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA, _method_code, _method_parameters_shape, _method_return_type_shape
from alpha.p15 import RUNTIME_CLASS_SCHEMA
from alpha.p16 import RUNTIME_NATIVE_HELPER_SCHEMA
from alpha.c04 import MappedPE
from alpha.p16 import RUNTIME_TYPE_MATERIALIZER_SCHEMA
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_MEMBER_HEADER, _NATIVE_MEMBER_RECORD, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json


RUNTIME_REFLECTION_BEHAVIOR_PLAN_SCHEMA = (
    "alpha.runtime-reflection-behavior-plan/v1"
)
RUNTIME_REFLECTION_BEHAVIOR_STATUS_SCHEMA = (
    "alpha.runtime-reflection-behavior-status/v1"
)
RUNTIME_REFLECTION_BEHAVIOR_SCHEMA = (
    "alpha.runtime-reflection-behavior/v1"
)
_EVENT_OPERATION_KEYS = (
    "event.name",
    "event.add_method",
    "event.remove_method",
    "event.raise_method",
)
_EVENT_RELATION_OPERATION_KEYS = ("event.handler_type",)
_METHOD_OPERATION_KEYS = (
    "method.return_type",
    "method.parameters",
)
_MEMBER_OPERATION_KEYS = ("member.metadata_token",)
_TYPE_IDENTITY_OPERATION_KEYS = ("type.name", "type.namespace")
_TYPE_EXTENDED_OPERATION_KEYS = (
    "type.module",
    "type.interfaces",
    "type.is_enum",
    "type.is_value_type",
    "type.is_generic",
    "type.generic_definition",
    "type.is_generic_definition",
    "type.generic_arguments",
    "type.element_type",
    "type.base_type",
    "type.declaring_type",
    "type.attributes",
)
_TYPE_EXTENDED_FAMILIES = {
    "type.module": "module_pair",
    "type.interfaces": "interfaces",
    "type.is_enum": "is_enum",
    "type.is_value_type": "is_value_type",
    "type.is_generic": "is_generic",
    "type.generic_definition": "generic_definition",
    "type.is_generic_definition": "is_generic_definition",
    "type.generic_arguments": "generic_arguments",
    "type.element_type": "element_type",
    "type.base_type": "base_type",
    "type.declaring_type": "declaring_type_pair",
    "type.attributes": "attributes",
}
_REMAINING_OPERATION_KEYS = (
    "property.from_handle",
    "field.set_value",
    "field.get_value",
    "field.raw_constant",
    "field.from_handle",
    "method.from_handle",
    "enum.underlying_type",
)
_REMAINING_FAMILIES = {
    "property.from_handle": "property.from_handle",
    "field.set_value": "field.set_value",
    "field.get_value": "field.get_value",
    "field.raw_constant": "field.raw_constant",
    "field.from_handle": "field.from_handle",
    "method.from_handle": "method.from_handle",
    "enum.underlying_type": "enum.underlying_type",
}


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime reflection behavior {label} is not owner-only"
        )
    return path


def _direct_decoders() -> threading.local:
    global _DIRECT_DECODERS
    current = _DIRECT_DECODERS
    if current is None:
        current = threading.local()
        _DIRECT_DECODERS = current
    return current


def _direct_decoder() -> Any:
    decoder = getattr(_direct_decoders(), "decoder", None)
    if decoder is None:
        try:
            from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        except ImportError as error:
            raise AcquisitionError(
                "runtime reflection direct code decoding requires capstone"
            ) from error
        decoder = Cs(CS_ARCH_X86, CS_MODE_64)
        decoder.detail = True
        _direct_decoders().decoder = decoder
    return decoder


_DIRECT_DECODERS: threading.local | None = None


def _direct_calls(code: bytes, method_pointer: int) -> list[tuple[int, int]]:
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_IMM
    except ImportError as error:
        raise AcquisitionError(
            "runtime reflection direct call decoding requires capstone"
        ) from error
    decoder = _direct_decoder()
    output: list[tuple[int, int]] = []
    for instruction in decoder.disasm(code[:96], method_pointer):
        if (
            instruction.mnemonic == "call"
            and instruction.operands
            and instruction.operands[0].type == X86_OP_IMM
        ):
            output.append(
                (instruction.address - method_pointer, instruction.operands[0].imm)
            )
    return output


def _direct_jumps(
    code: bytes, method_pointer: int, *, scan_bytes: int = 96
) -> list[tuple[int, int]]:
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_IMM
    except ImportError as error:
        raise AcquisitionError(
            "runtime reflection direct jump decoding requires capstone"
        ) from error
    decoder = _direct_decoder()
    output: list[tuple[int, int]] = []
    for instruction in decoder.disasm(code[:scan_bytes], method_pointer):
        if (
            instruction.mnemonic == "jmp"
            and instruction.operands
            and instruction.operands[0].type == X86_OP_IMM
        ):
            output.append(
                (instruction.address - method_pointer, instruction.operands[0].imm)
            )
    return output


def _runtime_type_payload_flag_test_count(code: bytes) -> int:


    matches = 0
    for position in range(max(0, len(code) - 7)):
        rex = code[position]
        if rex not in (0x48, 0x49) or code[position + 1] != 0x8B:
            continue
        modrm = code[position + 2]

        if (
            modrm >> 6 != 0b01
            or (modrm >> 3) & 0b111 != 0b001
            or modrm & 0b111 == 0b100
            or code[position + 3] != 0x10
        ):
            continue
        if code[position + 4 : position + 8] != b"\xf6\x41\x0b\x40":
            continue
        matches += 1
    return matches


def _runtime_type_generic_definition_shape(code: bytes) -> bool:


    return _runtime_type_payload_flag_test_count(code) == 1


def _runtime_type_get_generic_definition_shape(code: bytes) -> bool:
    if not code or len(code) > 1_048_576:
        return False
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_IMM, X86_OP_MEM, X86_OP_REG
    except ImportError as error:
        raise AcquisitionError(
            "runtime reflection Type candidate decoding requires capstone"
        ) from error


    decoder = _direct_decoder()
    instructions = list(decoder.disasm(code, 0))
    if not instructions or instructions[-1].address + instructions[-1].size != len(code):
        return False
    flag_tests: collections.Counter[tuple[int, int, int]] = collections.Counter()
    for instruction in instructions:
        operands = instruction.operands
        if (
            instruction.mnemonic == "test"
            and len(operands) == 2
            and operands[0].type == X86_OP_MEM
            and operands[0].size == 1
            and not operands[0].mem.index
            and operands[1].type == X86_OP_IMM
            and 0 < operands[1].imm < 256
            and operands[1].imm & (operands[1].imm - 1) == 0
        ):
            flag_tests[(
                operands[0].mem.base,
                operands[0].mem.disp,
                operands[1].imm,
            )] += 1
    for (payload_register, _flag_offset, _flag_mask), count in flag_tests.items():
        if count != 2:
            continue
        for load in instructions:
            operands = load.operands
            if (
                load.mnemonic != "mov"
                or len(operands) != 2
                or operands[0].type != X86_OP_REG
                or operands[0].size != 8
                or operands[1].type != X86_OP_MEM
                or operands[1].size != 8
                or operands[1].mem.base != payload_register
                or operands[1].mem.index
                or not 0 < operands[1].mem.disp < 512
                or operands[1].mem.disp % 8
            ):
                continue
            generic_class_register = operands[0].reg
            for definition_load in instructions:
                definition_operands = definition_load.operands
                if (
                    definition_load.address <= load.address
                    or definition_load.mnemonic != "mov"
                    or len(definition_operands) != 2
                    or definition_operands[0].type != X86_OP_REG
                    or definition_operands[0].size != 4
                    or definition_operands[1].type != X86_OP_MEM
                    or definition_operands[1].size != 4
                    or definition_operands[1].mem.base != generic_class_register
                    or definition_operands[1].mem.index
                    or definition_operands[1].mem.disp != 0
                ):
                    continue
                following = [
                    item for item in instructions
                    if item.address > definition_load.address
                ]
                if any(
                    item.mnemonic == "call"
                    and item.operands
                    and item.operands[0].type == X86_OP_IMM
                    for item in following
                ) and any(
                    item.mnemonic == "jmp"
                    and item.operands
                    and item.operands[0].type == X86_OP_IMM
                    and not 0 <= item.operands[0].imm < len(code)
                    for item in following
                ):
                    return True
    return False


def _runtime_type_is_generic_definition_shape(code: bytes) -> bool:
    if not _runtime_type_generic_definition_shape(code):
        return False
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_IMM, X86_OP_MEM, X86_OP_REG
    except ImportError as error:
        raise AcquisitionError(
            "runtime reflection Type flag decoding requires capstone"
        ) from error
    decoder = _direct_decoder()
    instructions = list(decoder.disasm(code, 0))
    normalized_loads = 0
    for load, mask_instruction, shift_instruction in zip(
        instructions, instructions[1:], instructions[2:]
    ):
        load_operands = load.operands
        mask_operands = mask_instruction.operands
        shift_operands = shift_instruction.operands
        if (
            load.mnemonic != "movzx"
            or len(load_operands) != 2
            or load_operands[0].type != X86_OP_REG
            or load_operands[1].type != X86_OP_MEM
            or load_operands[1].size != 1
            or load_operands[1].mem.index
            or mask_instruction.mnemonic != "and"
            or len(mask_operands) != 2
            or mask_operands[0].type != X86_OP_REG
            or mask_operands[1].type != X86_OP_IMM
            or shift_instruction.mnemonic != "shr"
            or len(shift_operands) != 2
            or shift_operands[0].type != X86_OP_REG
            or shift_operands[1].type != X86_OP_IMM
        ):
            continue
        mask = mask_operands[1].imm
        load_register = decoder.reg_name(load_operands[0].reg)
        mask_register = decoder.reg_name(mask_operands[0].reg)
        shift_register = decoder.reg_name(shift_operands[0].reg)
        register_family = lambda name: (
            "rax" if name in ("rax", "eax", "ax", "al", "ah") else
            "rcx" if name in ("rcx", "ecx", "cx", "cl", "ch") else
            "rdx" if name in ("rdx", "edx", "dx", "dl", "dh") else
            "rbx" if name in ("rbx", "ebx", "bx", "bl", "bh") else
            name[:-1] if name and name[-1:] in ("d", "w", "b") else name
        )
        if (
            0 < mask < 256
            and mask & (mask - 1) == 0
            and shift_operands[1].imm == mask.bit_length() - 1
            and register_family(load_register)
            == register_family(mask_register)
            == register_family(shift_register)
        ):
            normalized_loads += 1
    return normalized_loads == 1


def _runtime_type_is_generic_shape(code: bytes) -> bool:
    if _runtime_type_payload_flag_test_count(code) != 1:
        return False
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_IMM, X86_OP_MEM
    except ImportError as error:
        raise AcquisitionError(
            "runtime reflection Type generic decoding requires capstone"
        ) from error
    decoder = _direct_decoder()
    instructions = list(decoder.disasm(code, 0))
    if not instructions or instructions[-1].address + instructions[-1].size != len(code):
        return False
    pointer_checks = [
        instruction.address
        for instruction in instructions
        if instruction.mnemonic == "cmp"
        and len(instruction.operands) == 2
        and instruction.operands[0].type == X86_OP_MEM
        and instruction.operands[0].size == 8
        and not instruction.operands[0].mem.index
        and 0 < instruction.operands[0].mem.disp < 512
        and instruction.operands[0].mem.disp % 8 == 0
        and instruction.operands[1].type == X86_OP_IMM
        and instruction.operands[1].imm == 0
    ]
    return (
        len(pointer_checks) == 1
        and any(
            instruction.mnemonic == "setne"
            and instruction.address > pointer_checks[0]
            for instruction in instructions
        )
        and any(instruction.mnemonic == "ret" for instruction in instructions)
        and len(_direct_calls(code, 0)) == 1
    )


def _runtime_type_boolean_predicate_pool_shape(code: bytes) -> bool:
    if not code or len(code) > 320:
        return False
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_IMM, X86_OP_MEM
    except ImportError as error:
        raise AcquisitionError(
            "runtime reflection Type predicate decoding requires capstone"
        ) from error
    decoder = _direct_decoder()
    instructions = list(decoder.disasm(code, 0))
    if (
        not instructions
        or instructions[-1].address + instructions[-1].size != len(code)
        or len(instructions) > 96
    ):
        return False
    calls = 0
    normalized = 0
    tail_jumps = 0
    comparisons = 0
    for instruction in instructions:
        mnemonic = instruction.mnemonic
        operands = instruction.operands
        if mnemonic == "call":
            calls += 1
        elif mnemonic == "int3":
            return False
        elif mnemonic in (
            "sete",
            "setne",
            "setz",
            "setnz",
            "setb",
            "setbe",
            "seta",
            "setae",
            "setg",
            "setge",
            "setl",
            "setle",
        ):
            normalized += 1
        elif (
            mnemonic == "and"
            and len(operands) == 2
            and operands[1].type == X86_OP_IMM
            and 0 < operands[1].imm < 256
        ):
            normalized += 1
        elif mnemonic == "jmp":
            tail_jumps += 1
        elif mnemonic in ("cmp", "test"):
            comparisons += 1
        elif mnemonic in ("mov", "movups") and operands:
            destination = operands[0]
            if destination.type == X86_OP_MEM:
                base = destination.mem.base
                name = decoder.reg_name(base) if base else ""
                if name not in ("rsp", "rbp"):
                    return False
    if not normalized and tail_jumps and comparisons:


        normalized = 1
    return calls <= 8 and normalized >= 1


def _runtime_type_attribute_getter_pool_shape(code: bytes) -> bool:
    if not code or len(code) > 320:
        return False
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_MEM, X86_OP_REG
    except ImportError as error:
        raise AcquisitionError(
            "runtime reflection Type attribute decoding requires capstone"
        ) from error
    decoder = _direct_decoder()
    instructions = list(decoder.disasm(code, 0))
    if (
        not instructions
        or instructions[-1].address + instructions[-1].size != len(code)
        or len(instructions) > 96
    ):
        return False
    calls = 0
    dword_loads = 0
    for instruction in instructions:
        mnemonic = instruction.mnemonic
        operands = instruction.operands
        if mnemonic == "call":
            calls += 1
        elif mnemonic.startswith("set"):
            return False
        elif mnemonic == "mov" and len(operands) == 2:
            destination = operands[0]
            source = operands[1]
            if (
                destination.type == X86_OP_REG
                and destination.size == 4
                and source.type == X86_OP_MEM
                and source.size == 4
                and not source.mem.index
                and 16 <= source.mem.disp <= 1024
                and source.mem.disp % 4 == 0
            ):
                dword_loads += 1
            elif destination.type == X86_OP_MEM:
                base = destination.mem.base
                name = decoder.reg_name(base) if base else ""
                if name not in ("rsp", "rbp"):
                    return False
    return calls <= 2 and dword_loads == 1


def _event_helper_result_shape(
    code: bytes,
    *,
    method_pointer: int,
    bool_argument: bool,
) -> tuple[int, int] | None:
    calls = _direct_calls(code, method_pointer)
    if len(calls) != 1:
        return None
    call_position, helper_pointer = calls[0]
    tail = code[call_position + 5 : min(len(code), call_position + 96)]
    load_prefix = (
        b"\x48\x8b\x74\x24" if bool_argument else b"\x48\x8b\x44\x24"
    )
    load = tail.find(load_prefix)
    if load < 0 or load + 5 > len(tail):
        return None
    stack_offset = tail[load + 4]
    if stack_offset < 0x20 or stack_offset > 0x78 or stack_offset % 8:
        return None
    visibility_patterns = (
        b"\x84\xdb",
        b"\x83\xe0\x07",
        b"\x83\xf8\x06",
    )
    if bool_argument:
        if not all(pattern in tail for pattern in visibility_patterns):
            return None
    elif any(pattern in tail for pattern in visibility_patterns):
        return None
    return helper_pointer, stack_offset


def _event_handler_type_shape(code: bytes) -> bool:

    if (
        not 112 <= len(code) <= 160
        or not code.startswith(b"\x48\x83\xec\x68\x48\x85\xc9")
        or len(_direct_calls(code, 0)) != 1
        or code.count(b"\x0f\x29\x44\x24") < 4
        or b"\x48\x8d\x54\x24" not in code
        or b"\x48\x8b\x01\x31\xd2\xff\x90" not in code
        or b"\x48\x8b\x48\x18\x48\x85\xc9" not in code
        or b"\x48\x8b\x40\x20\x48\x85\xc0" not in code
        or b"\x48\x8b\x40\x10\x48\x83\xc4\x68\xc3" not in code
        or code.count(b"\x48\x83\xc4\x68\xc3") != 2
        or code[-1:] != b"\xcc"
    ):
        return False
    return True


def _runtime_type_identity_string_shape(code: bytes) -> bool:
    return bool(
        36 <= len(code) <= 64
        and code.startswith(b"\x56\x48\x83\xec\x20\x48\x89\xce\x48\x8b\x0d")
        and len(_direct_calls(code, 0)) == 1
        and b"\x80\xb9" in code
        and b"\x48\x89\xf1\x48\x83\xc4\x20\x5e\xe9" in code
        and code[-2:] == b"\xeb\xec"
    )


def _runtime_type_identity_string_family(
    rows: list[dict[str, Any]],
    *,
    snapshot: MemorySnapshot,
    image: MappedPE,
    semantics: dict[str, Any],
) -> tuple[list[dict[str, Any]], dict[str, int | bool]]:
    if len(rows) < 2:
        raise AcquisitionError(
            "runtime reflection Type identity arity-zero domain is incomplete"
        )
    del snapshot, image, semantics
    selected: list[dict[str, Any]] = []
    identities: set[tuple[int, int]] = set()
    hidden_return_candidates = 0
    for row in rows:
        code = row["code_owner_only"]
        if (
            code.startswith(
                b"\x56\x57\x48\x83\xec\x28\x48\x89\xd7\x48\x89\xce"
            )
            and b"\x0f\x11\x06" in code
        ):
            hidden_return_candidates += 1
        identity = (
            row["metadata_pointer_owner_only"],
            row["method_pointer_owner_only"],
        )
        if identity in identities:
            raise AcquisitionError(
                "runtime reflection Type identity candidate is duplicated"
            )
        identities.add(identity)
        public_row = dict(row)
        public_row.pop("code_owner_only", None)
        selected.append(public_row)
    return selected, {
        "arity_zero_candidate_count": len(rows),
        "hidden_return_buffer_candidate_count": hidden_return_candidates,
        "runtime_identity_candidate_count": len(selected),
        "current_method_metadata_relation_required": True,
        "runtime_string_return_filter_required": True,
        "structural_string_return_safe": False,
        "direct_invocation_before_return_type_filter": False,
    }


def _default_lookup_collection_shape(code: bytes) -> bool:
    if (
        len(code) < 64
        or not code.startswith(b"\x56\x48\x83\xec")
        or code[4] < 0x20
        or code[5:8] != b"\x48\x85\xc9"
        or b"\x41\xb9\x1c\x00\x00\x00" not in code[:96]
        or b"\x0f\x57\xc0" not in code[:64]
        or b"\xc3" not in code[:128]
    ):
        return False
    return len(_direct_calls(code, 0)) >= 2


def _binding_flag_collection_shape(code: bytes) -> bool:

    return bool(
        len(code) >= 64
        and code.startswith(b"\x56\x48\x83\xec\x50")
        and all(
            pattern in code[:80]
            for pattern in (
                b"\x41\x89\xd1",
                b"\x48\x89\xca",
                b"\x0f\x57\xc0",
                b"\x48\x8d\x74\x24\x30",
                b"\x48\x8b\x15",
            )
        )
        and len(_direct_calls(code, 0)) == 2
    )


def _binding_flag_method_collection_shape(code: bytes) -> bool:
    return bool(
        len(code) >= 80
        and code.startswith(b"\x56\x48\x83\xec\x60")
        and all(
            pattern in code[:96]
            for pattern in (
                b"\x41\x89\xd1",
                b"\x48\x89\xca",
                b"\x0f\x57\xc0",
                b"\xc7\x44\x24\x20\x03\x00\x00\x00",
                b"\x48\x8d\x74\x24\x40",
                b"\x48\x8b\x15",
            )
        )
        and len(_direct_calls(code, 0)) == 2
    )


def _method_collection_candidates(
    *,
    snapshot: MemorySnapshot,
    image: MappedPE,
    classes: dict[str, Any],
    arity_offset: int,
) -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    for method in classes.get("methods", []):
        if (
            not isinstance(method, dict)
            or method.get("runtime_owner") != "System.RuntimeType"
        ):
            continue
        metadata_pointer = method.get("metadata_pointer")
        method_pointer = method.get("method_pointer")
        raw_arity = (
            snapshot.read(metadata_pointer + arity_offset, 1)
            if isinstance(metadata_pointer, int) and metadata_pointer
            else None
        )
        code = (
            _method_code(
                snapshot=snapshot,
                image=image,
                method_pointer=method_pointer,
            )
            if isinstance(method_pointer, int) and method_pointer
            else None
        )
        if (
            raw_arity
            and raw_arity[0] == 1
            and code is not None
            and _binding_flag_method_collection_shape(code)
        ):
            candidates.append(
                {
                    "method_index_owner_only": method.get("method_index"),
                    "metadata_pointer_owner_only": metadata_pointer,
                    "method_pointer_owner_only": method_pointer,
                }
            )
    if len(candidates) != 2:
        raise AcquisitionError(
            "runtime reflection method/constructor collection family is not "
            f"complete (candidates={len(candidates)})"
        )
    return candidates


def _metadata_token_dispatch_shape(
    *,
    snapshot: MemorySnapshot,
    image: MappedPE,
    method_pointer: int,
) -> dict[str, int] | None:
    thunk = snapshot.read(method_pointer, 5) if method_pointer else None
    if thunk is None or len(thunk) != 5 or thunk[0] != 0xE9:
        return None
    target = method_pointer + 5 + struct.unpack_from("<i", thunk, 1)[0]
    target_rva = target - snapshot.image_base
    function = image.containing_function(target_rva)
    if function is None or function.begin_rva != target_rva:
        return None
    code = snapshot.read(
        target,
        min(function.end_rva - function.begin_rva, 4096),
    )
    token_prefixes = tuple(
        struct.pack("<I", value << 24)
        for value in (0x02, 0x04, 0x06, 0x14, 0x17)
    )
    if (
        code is None
        or len(code) < 256
        or not code.startswith(b"\x48\x83\xec\x28\x48\x8b\x01")
        or sum(code.count(pattern) for pattern in token_prefixes) < 5
        or code.count(b"\xc3") < 5
        or b"\xcc" not in code[-8:]
    ):
        return None
    return {
        "dispatch_target_owner_only": target,
        "dispatch_function_bytes": len(code),
        "metadata_table_prefix_count": sum(
            code.count(pattern) for pattern in token_prefixes
        ),
    }


def _function_call_targets(
    *,
    snapshot: MemorySnapshot,
    image: MappedPE,
    function_rva: int,
) -> set[int]:
    function = image.containing_function(function_rva)
    if function is None or function.begin_rva != function_rva:
        return set()
    byte_count = function.end_rva - function.begin_rva
    code = snapshot.read(snapshot.image_base + function.begin_rva, byte_count)
    if code is None:
        return set()


    targets: set[int] = set()
    limit = len(code) - 4
    if limit <= 0:
        return set()
    containing = image.containing_function
    begin_rva = function.begin_rva
    unpack_from = struct.unpack_from
    for needle in (b"\xe8", b"\xe9"):
        position = code.find(needle, 0, limit)
        while position >= 0:
            displacement = unpack_from("<i", code, position + 1)[0]
            target = begin_rva + position + 5 + displacement
            child = containing(target)
            if child is not None and child.begin_rva == target:
                targets.add(target)
            position = code.find(needle, position + 1, limit)
    return targets


def _shortest_call_distance(
    *,
    snapshot: MemorySnapshot,
    image: MappedPE,
    start_rva: int,
    target_rva: int,
) -> int | None:
    pending: deque[tuple[int, int]] = deque(((start_rva, 0),))
    visited: set[int] = set()
    while pending:
        current, depth = pending.popleft()
        if current in visited:
            continue
        visited.add(current)
        if current == target_rva:
            return depth
        for target in _function_call_targets(
            snapshot=snapshot,
            image=image,
            function_rva=current,
        ):
            if target not in visited:
                pending.append((target, depth + 1))
    return None


def _event_definition_domain(
    *,
    materializer: dict[str, Any],
    member_inventory: Path,
) -> dict[str, Any]:
    identity = file_identity(member_inventory)
    expected = materializer.get("runtime_validation", {}).get(
        "native_member_inventory", {}
    )
    if (
        identity.get("sha256") != expected.get("sha256")
        or identity.get("bytes") != expected.get("bytes")
    ):
        raise AcquisitionError(
            "runtime reflection behavior native member inventory is stale"
        )
    raw = member_inventory.read_bytes()
    if len(raw) < _NATIVE_MEMBER_HEADER.size:
        raise AcquisitionError(
            "runtime reflection behavior native member inventory is truncated"
        )
    header = _NATIVE_MEMBER_HEADER.unpack_from(raw, 0)
    field_count, property_count, event_count = header[5:8]
    event_start = _NATIVE_MEMBER_HEADER.size + (
        field_count + property_count
    ) * _NATIVE_MEMBER_RECORD.size
    if (
        not event_count
        or len(raw)
        != event_start + event_count * _NATIVE_MEMBER_RECORD.size
    ):
        raise AcquisitionError(
            "runtime reflection behavior native event domain is invalid"
        )
    support: defaultdict[int, int] = defaultdict(int)


    record_size = _NATIVE_MEMBER_RECORD.size
    for row in _NATIVE_MEMBER_RECORD.iter_unpack(
        memoryview(raw)[event_start : event_start + event_count * record_size]
    ):
        if row[3] != 2:
            raise AcquisitionError(
                "runtime reflection behavior native event row is invalid"
            )
        support[row[0]] += 1
    strongest = max(support.values(), default=0)
    if not support or not strongest or sum(support.values()) != event_count:
        raise AcquisitionError(
            "runtime reflection behavior event definition domain is incomplete"
        )
    definitions = {
        row.get("type_definition_index"): row
        for row in materializer.get("type_definitions", [])
        if isinstance(row, dict)
    }
    selected = sorted(support, key=lambda index: (-support[index], index))
    descriptor_rvas: list[int] = []
    for definition_index in selected:
        definition = definitions.get(definition_index)
        descriptor_rva = (
            definition.get("descriptor_rva")
            if isinstance(definition, dict)
            else None
        )
        if not isinstance(descriptor_rva, int) or descriptor_rva <= 0:
            raise AcquisitionError(
                "runtime reflection behavior event descriptor domain is unavailable"
            )
        descriptor_rvas.append(descriptor_rva)
    if len(descriptor_rvas) != len(support) or len(set(descriptor_rvas)) != len(
        descriptor_rvas
    ):
        raise AcquisitionError(
            "runtime reflection behavior event descriptor domain is not unique"
        )
    member_metadata: dict[str, list[int]] = {
        "field": [],
        "property": [],
    }
    member_metadata_rows: dict[str, list[dict[str, int]]] = {
        "field": [],
        "property": [],
    }
    selected_set = set(selected)
    section_start = _NATIVE_MEMBER_HEADER.size
    member_record = _NATIVE_MEMBER_RECORD
    for kind, label, count in (
        (0, "field", field_count),
        (1, "property", property_count),
    ):


        region_end = section_start + count * record_size
        append_pointer = member_metadata[label].append
        append_row = member_metadata_rows[label].append
        for row in member_record.iter_unpack(
            memoryview(raw)[section_start:region_end]
        ):
            if row[3] != kind or not row[2]:
                raise AcquisitionError(
                    "runtime reflection behavior native member row is invalid"
            )
            if row[0] in selected_set:
                append_pointer(row[2])
                append_row(
                    {
                        "definition_index_owner_only": row[0],
                        "metadata_pointer_owner_only": row[2],
                    }
                )
        section_start = region_end
    if not all(member_metadata.values()) or any(
        len(values) != len(set(values))
        for values in member_metadata.values()
    ):
        raise AcquisitionError(
            "runtime reflection behavior member handle domain is incomplete"
        )
    return {
        "definition_indexes_owner_only": selected,
        "descriptor_rvas_owner_only": descriptor_rvas,
        "native_event_count": event_count,
        "event_bearing_type_count": len(selected),
        "strongest_event_count": strongest,
        "equal_strongest_support_count": sum(
            count == strongest for count in support.values()
        ),
        "member_metadata_pointers_owner_only": member_metadata,
        "member_metadata_rows_owner_only": member_metadata_rows,
    }


def _balanced_member_handle_samples(
    rows: list[dict[str, int]],
    *,
    descriptor_by_definition: dict[int, int],
    limit: int = 64,
) -> list[dict[str, int]]:
    by_definition: defaultdict[int, list[int]] = defaultdict(list)
    for row in rows:
        definition_index = row.get("definition_index_owner_only")
        metadata_pointer = row.get("metadata_pointer_owner_only")
        if (
            not isinstance(definition_index, int)
            or definition_index not in descriptor_by_definition
            or not isinstance(metadata_pointer, int)
            or metadata_pointer <= 0
        ):
            raise AcquisitionError(
                "runtime reflection behavior member handle row is invalid"
            )
        by_definition[definition_index].append(metadata_pointer)
    selected: list[dict[str, int]] = []
    depth = 0
    definitions = sorted(by_definition)
    while len(selected) < limit:
        added = False
        for definition_index in definitions:
            values = by_definition[definition_index]
            if depth >= len(values):
                continue
            selected.append(
                {
                    "definition_index_owner_only": definition_index,
                    "metadata_pointer_owner_only": values[depth],
                    "owner_descriptor_pointer_owner_only": (
                        descriptor_by_definition[definition_index]
                    ),
                }
            )
            added = True
            if len(selected) == limit:
                break
        if not added:
            break
        depth += 1
    if len(selected) < min(8, len(rows)):
        raise AcquisitionError(
            "runtime reflection behavior member handle sample is incomplete"
        )
    return selected


def _known_type_identity_domain(
    *,
    materializer: dict[str, Any],
    native_inventory: Path,
    class_rows: dict[str, Any],
) -> dict[str, Any]:
    identity = file_identity(native_inventory)
    expected = materializer.get("runtime_validation", {}).get(
        "native_inventory", {}
    )
    if (
        identity.get("sha256") != expected.get("sha256")
        or identity.get("bytes") != expected.get("bytes")
    ):
        raise AcquisitionError(
            "runtime reflection behavior native type inventory is stale"
        )
    raw = native_inventory.read_bytes()
    if len(raw) < _NATIVE_INVENTORY_HEADER.size:
        raise AcquisitionError(
            "runtime reflection behavior native type inventory is truncated"
        )
    header = _NATIVE_INVENTORY_HEADER.unpack_from(raw, 0)
    type_count, method_count = header[5:7]
    type_start = _NATIVE_INVENTORY_HEADER.size
    method_start = type_start + type_count * _NATIVE_TYPE_RECORD.size
    names_start = method_start + method_count * _NATIVE_METHOD_RECORD.size
    if (
        header[0] != _NATIVE_INVENTORY_MAGIC
        or header[1] != _NATIVE_INVENTORY_VERSION
        or header[2] != _NATIVE_TYPE_RECORD.size
        or header[3] != _NATIVE_METHOD_RECORD.size
        or header[4]
        or not type_count
        or names_start > len(raw)
    ):
        raise AcquisitionError(
            "runtime reflection behavior native type inventory is invalid"
        )
    by_class: dict[int, tuple[int, str]] = {}


    raw_len = len(raw)
    type_end = type_start + type_count * _NATIVE_TYPE_RECORD.size
    for index, row in enumerate(
        _NATIVE_TYPE_RECORD.iter_unpack(
            memoryview(raw)[type_start:type_end]
        )
    ):
        name_bytes, descriptor_rva, class_pointer, name_offset = (
            row[1],
            row[3],
            row[4],
            row[10],
        )
        if (
            row[0] != index
            or not descriptor_rva
            or not class_pointer
            or name_bytes > 4096
            or name_offset < names_start
            or name_offset + name_bytes > raw_len
        ):
            raise AcquisitionError(
                "runtime reflection behavior native type row is invalid"
            )
        try:
            current_name = raw[
                name_offset : name_offset + name_bytes
            ].decode("utf-8")
        except UnicodeDecodeError as error:
            raise AcquisitionError(
                "runtime reflection behavior native type name is invalid"
            ) from error
        by_class[class_pointer] = (descriptor_rva, current_name)
    rows: list[dict[str, Any]] = []
    for runtime_owner, class_row in sorted(class_rows.items()):
        if not isinstance(runtime_owner, str) or "." not in runtime_owner:
            continue
        class_pointer = class_row.get("class_pointer")
        native = by_class.get(class_pointer)
        namespace, type_name = runtime_owner.rsplit(".", 1)
        if native is None or native[1] != type_name:
            raise AcquisitionError(
                "runtime reflection behavior known type identity is stale"
            )
        rows.append(
            {
                "runtime_owner": runtime_owner,
                "namespace": namespace,
                "type_name": type_name,
                "descriptor_rva_owner_only": native[0],
            }
        )
    if len(rows) < 8:
        raise AcquisitionError(
            "runtime reflection behavior known type domain is incomplete"
        )
    return {
        "known_type_identity_rows_owner_only": rows,
        "native_inventory_identity": identity,
    }


def _runtime_type_semantic_samples(
    *,
    native_inventory: Path,
    snapshot: MemorySnapshot,
    class_rows: dict[str, Any],
) -> dict[str, Any]:
    raw = native_inventory.read_bytes()
    if len(raw) < _NATIVE_INVENTORY_HEADER.size:
        raise AcquisitionError(
            "runtime reflection Type semantic inventory is truncated"
        )
    header = _NATIVE_INVENTORY_HEADER.unpack_from(raw, 0)
    type_count, method_count = header[5:7]
    type_start = _NATIVE_INVENTORY_HEADER.size
    method_start = type_start + type_count * _NATIVE_TYPE_RECORD.size
    names_start = method_start + method_count * _NATIVE_METHOD_RECORD.size
    if (
        header[0] != _NATIVE_INVENTORY_MAGIC
        or header[1] != _NATIVE_INVENTORY_VERSION
        or header[2] != _NATIVE_TYPE_RECORD.size
        or header[3] != _NATIVE_METHOD_RECORD.size
        or header[4]
        or not type_count
        or names_start > len(raw)
    ):
        raise AcquisitionError(
            "runtime reflection Type semantic inventory is invalid"
        )
    records: list[tuple[tuple[int, ...], str]] = []
    by_class: dict[int, tuple[int, ...]] = {}


    raw_len = len(raw)
    type_end = type_start + type_count * _NATIVE_TYPE_RECORD.size
    append_record = records.append
    for index, row in enumerate(
        _NATIVE_TYPE_RECORD.iter_unpack(
            memoryview(raw)[type_start:type_end]
        )
    ):
        if (
            row[0] != index
            or not row[3]
            or not row[4]
            or row[1] > 4096
            or row[10] < names_start
            or row[10] + row[1] > raw_len
        ):
            raise AcquisitionError(
                "runtime reflection Type semantic row is invalid"
            )
        try:
            name = raw[row[10] : row[10] + row[1]].decode("utf-8")
        except UnicodeDecodeError as error:
            raise AcquisitionError(
                "runtime reflection Type semantic name is invalid"
            ) from error
        append_record((row, name))
        by_class[row[4]] = row

    def hierarchy(row: tuple[int, ...]) -> list[int] | None:
        if not row[5]:
            return None
        chain: list[int] = []
        for depth in range(len(by_class) + 1):
            observed = snapshot.read(row[5] + depth * 8, 8)
            if observed is None:
                return None
            class_pointer = struct.unpack("<Q", observed)[0]
            if class_pointer not in by_class or class_pointer in chain:
                return None
            chain.append(class_pointer)
            if class_pointer == row[4]:
                return chain
        return None

    enum_class = class_rows.get("System.Enum", {}).get("class_pointer")
    if not isinstance(enum_class, int) or enum_class not in by_class:
        raise AcquisitionError(
            "runtime reflection Type Enum semantic sentinel is unavailable"
        )
    enum_chain = hierarchy(by_class[enum_class])
    if enum_chain is None or len(enum_chain) < 3:
        raise AcquisitionError(
            "runtime reflection Type Enum hierarchy is unavailable"
        )
    value_type_class = enum_chain[-2]
    known_classes = {
        row.get("class_pointer")
        for row in class_rows.values()
        if isinstance(row, dict)
        and isinstance(row.get("class_pointer"), int)
    }
    selected_classes = set(known_classes)
    category_counts = {
        "enum": 0,
        "value": 0,
        "generic_definition": 0,
    }
    selected_rows: list[tuple[tuple[int, ...], str, list[int]]] = []

    def append(row: tuple[int, ...], name: str, chain: list[int]) -> None:
        if row[4] in selected_classes and any(
            existing[0][4] == row[4] for existing in selected_rows
        ):
            return
        selected_classes.add(row[4])
        selected_rows.append((row, name, chain))

    for row, name in records:
        if row[4] not in selected_classes:
            continue
        chain = hierarchy(row)
        if chain is not None:
            append(row, name, chain)
    for row, name in records:
        if all(value >= 4 for value in category_counts.values()):
            break
        chain = hierarchy(row)
        if chain is None:
            continue
        concrete_enum = enum_class in chain[:-1]
        concrete_value = (
            value_type_class in chain[:-1] and not concrete_enum
        )
        generic_definition = "`" in name
        nested = bool(row[6] and row[6] in by_class)
        categories = {
            "enum": concrete_enum,
            "value": concrete_value,
            "generic_definition": generic_definition,
        }
        if not any(
            enabled and category_counts[key] < 4
            for key, enabled in categories.items()
        ):
            continue
        append(row, name, chain)
        for key, enabled in categories.items():
            if enabled and category_counts[key] < 4:
                category_counts[key] += 1
    if any(value < 4 for value in category_counts.values()):
        raise AcquisitionError(
            "runtime reflection Type semantic sample categories are incomplete"
        )
    samples: list[dict[str, Any]] = []
    for row, name, chain in selected_rows:
        parent = by_class.get(chain[-2]) if len(chain) > 1 else None
        declaring = by_class.get(row[6]) if row[6] else None
        concrete_enum = enum_class in chain[:-1]
        concrete_value = (
            value_type_class in chain[:-1] and not concrete_enum
        )
        generic_definition = "`" in name
        expected_is_value_type = (
            row[4] not in {enum_class, value_type_class}
            and (concrete_enum or concrete_value)
        )
        samples.append(
            {
                "descriptor_pointer_owner_only": snapshot.image_base
                + row[3],
                "expected_base_descriptor_owner_only": (
                    snapshot.image_base + parent[3] if parent else 0
                ),
                "expected_declaring_descriptor_owner_only": (
                    snapshot.image_base + declaring[3]
                    if declaring
                    else 0
                ),
                "expected_declaring_available": (
                    row[4] in known_classes or declaring is not None
                ),
                "expected_is_enum": concrete_enum,
                "expected_is_value_type": expected_is_value_type,
                "expected_is_generic": generic_definition,
                "expected_is_generic_definition": generic_definition,
                "category_owner_only": (
                    "enum"
                    if concrete_enum
                    else "value"
                    if concrete_value
                    else "generic-definition"
                    if generic_definition
                    else "nested"
                    if declaring
                    else "known"
                ),
            }
        )
    return {
        "type_semantic_samples_owner_only": samples,
        "type_semantic_category_counts": category_counts,
        "type_semantic_sample_count": len(samples),
    }


def _runtime_type_ancestry_method_domain(
    *,
    native_inventory: Path,
    snapshot: MemorySnapshot,
    runtime_type_class: int,
) -> dict[str, Any]:
    raw = native_inventory.read_bytes()
    if len(raw) < _NATIVE_INVENTORY_HEADER.size:
        raise AcquisitionError(
            "runtime reflection Type ancestry inventory is truncated"
        )
    header = _NATIVE_INVENTORY_HEADER.unpack_from(raw, 0)
    type_count, method_count = header[5:7]
    type_start = _NATIVE_INVENTORY_HEADER.size
    method_start = type_start + type_count * _NATIVE_TYPE_RECORD.size
    method_end = method_start + method_count * _NATIVE_METHOD_RECORD.size
    if (
        header[0] != _NATIVE_INVENTORY_MAGIC
        or header[1] != _NATIVE_INVENTORY_VERSION
        or header[2] != _NATIVE_TYPE_RECORD.size
        or header[3] != _NATIVE_METHOD_RECORD.size
        or header[4]
        or not type_count
        or not method_count
        or method_end > len(raw)
    ):
        raise AcquisitionError(
            "runtime reflection Type ancestry inventory is invalid"
        )
    by_class: dict[int, tuple[int, ...]] = {}


    type_end = type_start + type_count * _NATIVE_TYPE_RECORD.size
    for index, row in enumerate(
        _NATIVE_TYPE_RECORD.iter_unpack(
            memoryview(raw)[type_start:type_end]
        )
    ):
        if row[0] != index or not row[4] or row[4] in by_class:
            raise AcquisitionError(
                "runtime reflection Type ancestry class domain is invalid"
            )
        by_class[row[4]] = row
    runtime_type_row = by_class.get(runtime_type_class)
    if runtime_type_row is None or not runtime_type_row[5]:
        raise AcquisitionError(
            "runtime reflection Type hierarchy root is unavailable"
        )
    hierarchy_pointer = runtime_type_row[5]
    chain: list[tuple[int, ...]] = []
    chain_classes: list[int] = []
    for depth in range(len(by_class) + 1):
        raw_class = snapshot.read(
            hierarchy_pointer + depth * struct.calcsize("<Q"),
            struct.calcsize("<Q"),
        )
        if raw_class is None:
            raise AcquisitionError(
                "runtime reflection Type hierarchy is unreadable"
            )
        current = struct.unpack("<Q", raw_class)[0]
        row = by_class.get(current)
        if row is None:
            raise AcquisitionError(
                "runtime reflection Type hierarchy class is unavailable "
                f"(depth={depth})"
            )
        if current in chain_classes:
            raise AcquisitionError(
                "runtime reflection Type hierarchy contains a cycle"
            )
        chain_classes.append(current)
        chain.append(row)
        if current == runtime_type_class:
            break
    if len(chain) < 4 or chain_classes[-1] != runtime_type_class:
        raise AcquisitionError(
            "runtime reflection Type ancestry is incomplete"
        )
    for depth, row in enumerate(chain):
        owner_hierarchy = row[5]
        owner_raw = snapshot.read(
            owner_hierarchy,
            (depth + 1) * struct.calcsize("<Q"),
        ) if owner_hierarchy else None
        if owner_raw is None or list(
            struct.unpack(f"<{depth + 1}Q", owner_raw)
        ) != chain_classes[: depth + 1]:
            raise AcquisitionError(
                "runtime reflection Type hierarchy prefixes disagree"
            )
    methods: list[dict[str, int]] = []
    for owner_depth, type_row in enumerate(chain):
        definition_index = type_row[0]
        owner_method_count = type_row[7]
        owner_method_start = type_row[9]
        if (
            owner_method_start > method_count
            or owner_method_count > method_count - owner_method_start
        ):
            raise AcquisitionError(
                "runtime reflection Type ancestry method extent is invalid"
            )
        for method_index in range(owner_method_count):
            record = _NATIVE_METHOD_RECORD.unpack_from(
                raw,
                method_start
                + (owner_method_start + method_index)
                * _NATIVE_METHOD_RECORD.size,
            )
            if (
                record[0] != definition_index
                or record[1] != method_index
                or not record[2]
            ):
                raise AcquisitionError(
                    "runtime reflection Type ancestry method row is invalid"
                )
            methods.append(
                {
                    "owner_depth_owner_only": owner_depth,
                    "method_index_owner_only": method_index,
                    "metadata_pointer_owner_only": record[2],
                    "method_pointer_owner_only": record[3],
                    "owner_descriptor_pointer_owner_only": (
                        snapshot.image_base + type_row[3]
                    ),
                }
            )
    if len(methods) < 8:
        raise AcquisitionError(
            "runtime reflection Type ancestry method domain is incomplete"
        )
    return {
        "ancestry_class_count": len(chain),
        "ancestry_method_count": len(methods),
        "methods_owner_only": methods,
    }


_REFLECTION_FAMILY_BY_METHOD_NAME = {
    "get_BaseType": "base_type",
    "GetElementType": "element_type",
    "GetGenericArguments": "generic_arguments",
    "GetGenericTypeDefinition": "generic_definition",
    "get_GenericTypeDefinition": "generic_definition",
    "GetInterfaces": "interfaces",
    "GetCustomAttributes": "attributes",
    "get_IsEnum": "is_enum",
    "get_IsValueType": "is_value_type",
    "get_IsGenericType": "is_generic",
    "get_IsGenericTypeDefinition": "is_generic_definition",
    "get_Module": "module_pair",
    "get_DeclaringType": "declaring_type_pair",
}


def _reflection_families_by_method_name(observation: Path) -> dict[str, dict[str, Any]]:
    from alpha.p22 import (
        RUNTIME_METHOD_NAME_HEADER,
        RUNTIME_METHOD_NAME_MAGIC,
        RUNTIME_METHOD_NAME_RECORD,
        RUNTIME_METHOD_NAME_VERSION,
    )

    try:
        if not observation.is_file() or observation.is_symlink():
            return {}
        raw = observation.read_bytes()
    except OSError:
        return {}
    if len(raw) < RUNTIME_METHOD_NAME_HEADER.size:
        return {}
    header = RUNTIME_METHOD_NAME_HEADER.unpack_from(raw, 0)
    if (
        header[0] != RUNTIME_METHOD_NAME_MAGIC
        or header[1] != RUNTIME_METHOD_NAME_VERSION
        or header[3] != RUNTIME_METHOD_NAME_RECORD.size
    ):
        return {}
    method_count = int(header[5])
    position = int(header[2])
    record_size = RUNTIME_METHOD_NAME_RECORD.size


    if position < 0 or method_count < 0:
        return {}
    try:
        records_end = position + method_count * record_size
    except OverflowError:
        return {}
    if records_end > len(raw):
        return {}
    families: dict[str, dict[str, Any]] = {}


    wanted = {
        name.encode("utf-8"): family
        for name, family in _REFLECTION_FAMILY_BY_METHOD_NAME.items()
    }
    wanted_family_count = len(set(_REFLECTION_FAMILY_BY_METHOD_NAME.values()))


    wanted_lengths = {len(key) for key in wanted}
    raw_len = len(raw)
    raw_local = raw
    wanted_local = wanted
    unpack = RUNTIME_METHOD_NAME_RECORD.iter_unpack
    view = memoryview(raw)[position:records_end]
    get_family = wanted_local.get
    for record in unpack(view):

        name_bytes = record[4]
        if name_bytes not in wanted_lengths:
            continue
        name_offset = record[3]
        if not name_bytes or name_offset < 0 or name_offset + name_bytes > raw_len:
            continue
        name_slice = raw_local[name_offset:name_offset + name_bytes]
        family = get_family(name_slice)
        if family and family not in families:
            try:
                name = name_slice.decode("utf-8")
            except UnicodeDecodeError:
                continue
            families[family] = {
                "metadata_pointer": record[2],
                "method_index": record[1],
                "name_owner_only": name,
            }
            if len(families) == wanted_family_count:
                break
    return families


def _runtime_type_extended_candidate_family(
    *,
    methods: list[dict[str, int]],
    snapshot: MemorySnapshot,
    image: MappedPE,
    arity_offset: int,
    boolean_invoker: int,
    named_operations: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[dict[str, list[dict[str, int]]], dict[str, Any]]:
    attribute_candidates: list[tuple[int, dict[str, int]]] = []
    pointer_by_metadata: dict[int, int] = {}
    families: dict[str, list[dict[str, int]]] = {
        key: []
        for key in (
            "module_pair",
            "base_type",
            "element_type",
            "generic_arguments",
            "generic_definition",
            "interfaces",
            "declaring_type_pair",
            "attributes",
            "boolean",
            "is_enum",
            "is_value_type",
            "is_generic_definition",
            "is_generic",
        )
    }
    hidden_return_count = 0
    arity_zero_count = 0
    boolean_predicate_pool: list[dict[str, int]] = []
    attribute_getter_pool: list[dict[str, int]] = []
    for method in methods:
        metadata = method.get("metadata_pointer_owner_only")
        pointer = method.get("method_pointer_owner_only")
        if not metadata or not pointer:
            continue
        raw_arity = snapshot.read(metadata + arity_offset, 1)
        code = _method_code(
            snapshot=snapshot,
            image=image,
            method_pointer=pointer,
        )
        if not raw_arity or raw_arity[0] or code is None:
            continue
        arity_zero_count += 1
        row = {
            "owner_depth_owner_only": method["owner_depth_owner_only"],
            "method_index_owner_only": method["method_index_owner_only"],
            "metadata_pointer_owner_only": metadata,
            "method_pointer_owner_only": pointer,
        }
        pointer_by_metadata.setdefault(int(metadata), int(pointer))
        if (
            code.startswith(
                b"\x56\x57\x48\x83\xec\x28\x48\x89\xd7\x48\x89\xce"
            )
            and b"\x0f\x11\x06" in code
        ):
            hidden_return_count += 1
            continue
        invoker_raw = snapshot.read(metadata + 16, 8)
        invoker = struct.unpack("<Q", invoker_raw)[0] if invoker_raw else 0
        if invoker == boolean_invoker:
            families["boolean"].append(row)


        if (
            24 <= len(code) <= 96
            and _runtime_type_is_generic_definition_shape(code)
            and len(_direct_calls(code, pointer)) == 1
        ):
            families["is_generic_definition"].append(row)
        if _runtime_type_is_generic_shape(code):
            families["is_generic"].append(row)
        if _runtime_type_boolean_predicate_pool_shape(code):
            boolean_predicate_pool.append(row)
        if _runtime_type_attribute_getter_pool_shape(code):
            attribute_getter_pool.append(row)
        calls = _direct_calls(code, pointer)
        jumps = _direct_jumps(code, pointer)
        if (
            code.startswith(
                b"\x48\x83\xec\x28\x48\x8b\x49\x10\xb2\x01\xe8"
            )
            and code[15:].startswith(
                b"\x48\x8b\x08\x48\x83\xc4\x28\xe9"
            )
            and len(calls) == 1
        ):
            families["module_pair"].append(row)
        if code.startswith(
            b"\x41\x56\x56\x57\x55\x53\x48\x83\xec\x20\x49\x89\xce"
        ):
            families["base_type"].append(row)
        if code.startswith(
            b"\x56\x48\x83\xec\x20\x48\x89\xce\x48\x8b\x49\x10"
            b"\xb2\x01\xe8"
        ):
            families["element_type"].append(row)
        if code.startswith(b"\x48\x83\xec\x28\x31\xd2\xe8"):
            families["generic_arguments"].append(row)
        if _runtime_type_get_generic_definition_shape(code):
            families["generic_definition"].append(row)
        if code.startswith(b"\x48\x8b\x49\x10\xe9") and jumps[:1]:
            families["declaring_type_pair"].append(row)
        if (
            16 <= len(code) <= 96
            and not calls
            and not jumps
            and code[:1] not in (b"\xe9",)
        ):
            attribute_loads = [
                struct.unpack_from("<I", code, position + 2)[0]
                for position in range(max(0, len(code) - 5))
                if code[position : position + 2] == b"\x8b\x80"
            ]
            if (
                len(attribute_loads) == 1
                and 16 <= attribute_loads[0] <= 1024
                and attribute_loads[0] % 4 == 0
            ):
                row["attribute_byte_offset_owner_only"] = attribute_loads[0]
                attribute_candidates.append((abs(len(code) - 31), row))
        if code[:1] == b"\xe9" and len(code) >= 5:
            target = pointer + 5 + struct.unpack_from("<i", code, 1)[0]
            function = image.containing_function(
                target - snapshot.image_base
            )
            if (
                function is not None
                and function.begin_rva == target - snapshot.image_base
                and function.end_rva - function.begin_rva <= 2048
            ):
                body = snapshot.read(
                    target, function.end_rva - function.begin_rva
                )
                if body and body.startswith(
                    b"\x55\x41\x57\x41\x56\x41\x55\x41\x54"
                ):
                    families["interfaces"].append(row)
    if boolean_predicate_pool:


        pool_by_metadata = {
            row["metadata_pointer_owner_only"]: row
            for row in boolean_predicate_pool
        }
        base_type_pointers = {
            row["method_pointer_owner_only"]
            for row in families["base_type"]
        }
        enum_pool: dict[int, dict[str, int]] = {}
        for metadata, row in pool_by_metadata.items():
            code = _method_code(
                snapshot=snapshot,
                image=image,
                method_pointer=row["method_pointer_owner_only"],
            )
            if code is None or not base_type_pointers:
                continue
            if base_type_pointers.intersection(
                target
                for _offset, target in _direct_calls(
                    code, row["method_pointer_owner_only"]
                )
            ):
                enum_pool[metadata] = row
        if not enum_pool:
            enum_pool = dict(pool_by_metadata)


        def most_derived(
            rows: dict[int, dict[str, int]],
        ) -> dict[int, dict[str, int]]:
            depths = {
                row["owner_depth_owner_only"] for row in rows.values()
            }
            if len(depths) <= 1:
                return rows
            derived = max(depths)
            return {
                metadata: row
                for metadata, row in rows.items()
                if row["owner_depth_owner_only"] == derived
            }

        enum_pool = most_derived(enum_pool)
        pool_by_metadata = most_derived(pool_by_metadata)
        for family, extra in (
            ("is_enum", enum_pool),
            ("is_value_type", pool_by_metadata),
        ):
            merged = {
                row["metadata_pointer_owner_only"]: row
                for row in families[family]
            }
            for metadata, row in extra.items():
                merged.setdefault(metadata, row)
            families[family] = list(merged.values())
        merged_boolean = {
            row["metadata_pointer_owner_only"]: row
            for row in families["boolean"]
        }
        for metadata, row in pool_by_metadata.items():
            merged_boolean.setdefault(metadata, row)
        families["boolean"] = list(merged_boolean.values())
    if attribute_getter_pool:
        attribute_pool = {
            row["metadata_pointer_owner_only"]: row
            for row in attribute_getter_pool
        }
        attribute_depths = {
            row["owner_depth_owner_only"] for row in attribute_pool.values()
        }
        if len(attribute_depths) > 1:
            attribute_pool = {
                metadata: row
                for metadata, row in attribute_pool.items()
                if row["owner_depth_owner_only"] == max(attribute_depths)
            }
        families["attributes"] = list(attribute_pool.values())
    elif not families["attributes"] and attribute_candidates:
        attribute_candidates.sort(key=lambda item: item[0])
        if (
            len(attribute_candidates) == 1
            or attribute_candidates[0][0] < attribute_candidates[1][0]
        ):
            families["attributes"].append(attribute_candidates[0][1])
    if named_operations:


        for family, operation in named_operations.items():
            if family not in families or families[family]:
                continue
            if not isinstance(operation, Mapping):
                continue
            metadata_pointer = operation.get(
                "metadata_pointer_owner_only", operation.get("metadata_pointer")
            )
            method_pointer = operation.get(
                "method_pointer_owner_only", operation.get("method_pointer")
            )
            if type(metadata_pointer) is not int or metadata_pointer <= 0:
                continue
            if type(method_pointer) is not int or method_pointer <= 0:
                method_pointer = pointer_by_metadata.get(metadata_pointer, 0)
            if method_pointer <= 0:
                continue
            families[family].append(
                {
                    "owner_depth_owner_only": int(
                        operation.get("owner_depth_owner_only", 0) or 0
                    ),
                    "method_index_owner_only": int(
                        operation.get("method_index_owner_only", 0) or 0
                    ),
                    "metadata_pointer_owner_only": metadata_pointer,
                    "method_pointer_owner_only": method_pointer,
                    "resolved_by_owner_only": "reflection-semantics-key",
                }
            )
    exact = {
        "base_type": 1,
        "element_type": 1,
        "generic_arguments": 1,
        "generic_definition": 1,
        "interfaces": 1,
        "is_generic_definition": 1,
        "is_generic": 1,
    }
    for key, expected in exact.items():
        if len(families[key]) != expected:
            raise AcquisitionError(
                "runtime reflection Type extended candidate is not unique "
                f"(kind={key}, candidates={len(families[key])})"
            )
    behavior_pool_families = ("attributes", "is_enum", "is_value_type")
    for key in behavior_pool_families:
        if not families[key]:
            raise AcquisitionError(
                "runtime reflection Type extended candidate is not unique "
                f"(kind={key}, candidates={len(families[key])})"
            )
    if (
        len(families["module_pair"]) != 2
        or len(families["declaring_type_pair"]) < 2
        or len(families["boolean"]) < 5
    ):
        raise AcquisitionError(
            "runtime reflection Type extended candidate families are "
            "incomplete "
            f"(module_pair={len(families['module_pair'])}, "
            "declaring_type_pair="
            f"{len(families['declaring_type_pair'])}, "
            f"boolean={len(families['boolean'])})"
        )
    return families, {
        "arity_zero_method_count": arity_zero_count,
        "hidden_return_buffer_count": hidden_return_count,
        "module_pair_count": len(families["module_pair"]),
        "declaring_type_equivalence_candidate_count": len(
            families["declaring_type_pair"]
        ),
        "boolean_abi_candidate_count": len(families["boolean"]),
        "boolean_predicate_pool_count": len(boolean_predicate_pool),
        "attribute_getter_pool_count": len(attribute_getter_pool),
        "behavior_selected_family_count": len(behavior_pool_families),
        "resolved_family_count": sum(
            1
            for key in (
                *exact,
                *behavior_pool_families,
            )
            if families[key]
        ),
    }


def _remaining_reflection_candidate_families(
    *,
    methods: list[dict[str, Any]],
    snapshot: MemorySnapshot,
    image: MappedPE,
    arity_offset: int,
) -> tuple[dict[str, list[dict[str, int]]], dict[str, Any]]:
    families: dict[str, list[dict[str, int]]] = {
        key: []
        for key in (
            "property.from_handle",
            "field.set_value",
            "field.get_value",
            "field.raw_constant",
            "field.from_handle",
            "method.from_handle",
            "enum.underlying_type",
        )
    }
    scanned = 0
    for method in methods:
        if not isinstance(method, dict):
            continue
        owner = method.get("runtime_owner")
        metadata = method.get("metadata_pointer")
        pointer = method.get("method_pointer")
        index = method.get("method_index")
        if (
            not isinstance(owner, str)
            or not isinstance(metadata, int)
            or not metadata
            or not isinstance(pointer, int)
            or not pointer
            or not isinstance(index, int)
        ):
            continue
        raw_arity = snapshot.read(metadata + arity_offset, 1)
        code = _method_code(
            snapshot=snapshot,
            image=image,
            method_pointer=pointer,
        )
        if not raw_arity or code is None:
            continue
        scanned += 1
        arity = raw_arity[0]
        row = {
            "method_index_owner_only": index,
            "metadata_pointer_owner_only": metadata,
            "method_pointer_owner_only": pointer,
            "runtime_parameter_count_owner_only": arity,
        }
        if (
            owner == "System.Reflection.PropertyInfo"
            and arity == 2
            and code.startswith(
                b"\x56\x57\x48\x83\xec\x28\x48\x85\xc9"
            )
            and b"\x48\x85\xd2" in code[:64]
        ):
            try:
                from capstone import Cs, CS_ARCH_X86, CS_MODE_64
                from capstone.x86 import X86_OP_IMM, X86_OP_MEM, X86_OP_REG
            except ImportError as error:
                raise AcquisitionError(
                    "runtime reflection property owner decoding requires capstone"
                ) from error
            decoder = _direct_decoder()
            instructions = list(decoder.disasm(code, pointer))
            receiver_aliases = {"rcx"}
            protection_shapes: set[tuple[str, int, int]] = set()
            for position, instruction in enumerate(instructions):
                operands = instruction.operands
                if (
                    instruction.mnemonic == "mov"
                    and len(operands) == 2
                    and operands[0].type == X86_OP_REG
                    and operands[0].size == 8
                    and operands[1].type == X86_OP_REG
                    and operands[1].size == 8
                    and decoder.reg_name(operands[1].reg) in receiver_aliases
                ):
                    receiver_aliases.add(decoder.reg_name(operands[0].reg))
                if (
                    instruction.mnemonic not in ("mov", "movabs")
                    or len(operands) != 2
                    or operands[0].type != X86_OP_REG
                    or operands[0].size != 8
                    or operands[1].type != X86_OP_IMM
                    or position + 1 >= len(instructions)
                ):
                    continue
                following = instructions[position + 1]
                next_operands = following.operands
                if (
                    following.mnemonic in ("add", "xor")
                    and len(next_operands) == 2
                    and next_operands[0].type == X86_OP_REG
                    and next_operands[0].reg == operands[0].reg
                    and next_operands[0].size == 8
                    and next_operands[1].type == X86_OP_MEM
                    and next_operands[1].size == 8
                    and not next_operands[1].mem.index
                    and decoder.reg_name(next_operands[1].mem.base)
                    in receiver_aliases
                    and 0 <= next_operands[1].mem.disp < 512
                ):
                    protection_shapes.add((
                        following.mnemonic,
                        operands[1].imm & _MASK64,
                        next_operands[1].mem.disp,
                    ))
            factory_handle_offsets: list[int] = []
            call_prefix = b"\x48\x89\xf9\x48\x89\xf2\xe8"


            code_limit = len(code) - 10
            position = code.find(call_prefix, 0) if code_limit > 0 else -1
            while position >= 0:
                if position >= code_limit:
                    break
                target = (
                    pointer
                    + position
                    + 11
                    + struct.unpack_from("<i", code, position + 7)[0]
                )
                function = image.containing_function(
                    target - snapshot.image_base
                )
                if (
                    function is None
                    or function.begin_rva != target - snapshot.image_base
                    or function.end_rva - function.begin_rva > 8192
                ):
                    position = code.find(call_prefix, position + 1)
                    continue
                body = snapshot.read(
                    target, function.end_rva - function.begin_rva
                )
                if not body:
                    position = code.find(call_prefix, position + 1)
                    continue
                store_needle = b"\x49\x89\x47"
                body_limit = len(body) - 3
                stores: list[tuple[int, int]] = []
                if body_limit > 0:
                    store = body.find(store_needle, 0)
                    while store >= 0:
                        if store >= body_limit:
                            break
                        stores.append((store, body[store + 3]))
                        store = body.find(store_needle, store + 1)
                pairs = [
                    (first, second)
                    for first in stores
                    for second in stores
                    if 0 < second[0] - first[0] <= 32
                    and second[1] == first[1] + 8
                ]
                if len(pairs) == 1:
                    factory_handle_offsets.append(pairs[0][1][1])
                position = code.find(call_prefix, position + 1)
            if (
                len(protection_shapes) == 1
                and len(factory_handle_offsets) == 1
                and factory_handle_offsets[0] % 8 == 0
            ):
                protection_shape = next(iter(protection_shapes))
                row["protected_owner_addend_owner_only"] = (
                    protection_shape[1]
                )
                row["protected_owner_byte_offset_owner_only"] = (
                    protection_shape[2]
                )
                row["protected_owner_codec_owner_only"] = (
                    protection_shape[0]
                )
                row["property_object_handle_byte_offset_owner_only"] = (
                    factory_handle_offsets[0]
                )
                families["property.from_handle"].append(row)
        if (
            owner == "System.Reflection.FieldInfo"
            and arity == 2
            and code.startswith(
                b"\x48\x83\xec\x38\x48\x85\xc9"
            )
            and b"\x0f\x57\xc0" in code[:32]
        ):
            families["field.set_value"].append(row)
        if (
            owner == "System.Reflection.MonoField"
            and arity == 1
            and code.startswith(
                b"\x41\x56\x56\x57\x53\x48\x83\xec\x28"
                b"\x48\x85\xc9"
            )
        ):
            families["field.get_value"].append(row)
        if (
            owner == "System.Reflection.MonoField"
            and arity == 0
            and code[:1] == b"\xe9"
            and _direct_jumps(code, pointer)[:1]
        ):
            families["field.raw_constant"].append(row)
        if (
            owner == "System.Reflection.FieldInfo"
            and arity == 2
            and code.startswith(
                b"\x56\x57\x48\x83\xec\x28\x48\x85\xc9"
            )
            and b"\x48\x85\xd2" in code[:64]
        ):
            families["field.from_handle"].append(row)
        if (
            owner == "System.Reflection.MethodBase"
            and arity == 3
            and code[:1] == b"\xe9"
            and _direct_jumps(code, pointer)[:1]
        ):
            families["method.from_handle"].append(row)
        if (
            owner == "System.Enum"
            and arity == 1
            and code.startswith(
                b"\x56\x48\x83\xec\x20\x48\x85\xc9\x74\x14"
                b"\x48\x8b\x01\x48\x8b\x80"
            )
        ):
            families["enum.underlying_type"].append(row)
    expected_counts = {
        "property.from_handle": 1,
        "field.set_value": 1,
        "field.get_value": 1,
        "field.raw_constant": 1,
        "field.from_handle": 1,
        "method.from_handle": 1,
        "enum.underlying_type": 3,
    }
    for key, expected in expected_counts.items():
        if len(families[key]) != expected:
            raise AcquisitionError(
                "runtime reflection remaining candidate family is not exact "
                f"(kind={key}, candidates={len(families[key])})"
            )
    return families, {
        "method_domain_count": scanned,
        "structurally_unique_candidate_count": 6,
        "enum_behavior_candidate_count": 3,
        "property_handle_protection_shape_unique": True,
        "property_handle_protection_current_code_derived": True,
        "property_factory_handle_store_pair_unique": True,
        "saved_method_ordinal_used": False,
    }


def _event_collection_candidate(
    *,
    snapshot: MemorySnapshot,
    image: MappedPE,
    classes: dict[str, Any],
    arity_offset: int,
    event_helper_rva: int,
) -> tuple[dict[str, Any], dict[str, int]]:
    shaped: list[dict[str, Any]] = []
    reachable: list[dict[str, Any]] = []
    for method in classes.get("methods", []):
        if (
            not isinstance(method, dict)
            or method.get("runtime_owner") != "System.RuntimeType"
        ):
            continue
        metadata_pointer = method.get("metadata_pointer")
        method_pointer = method.get("method_pointer")
        raw_arity = (
            snapshot.read(metadata_pointer + arity_offset, 1)
            if isinstance(metadata_pointer, int) and metadata_pointer
            else None
        )
        code = (
            _method_code(
                snapshot=snapshot,
                image=image,
                method_pointer=method_pointer,
            )
            if isinstance(method_pointer, int) and method_pointer
            else None
        )
        if (
            not raw_arity
            or raw_arity[0] != 1
            or code is None
            or not _binding_flag_collection_shape(code)
        ):
            continue
        function = image.containing_function(
            method_pointer - snapshot.image_base
        )
        if function is None:
            continue
        candidate = {
            "method_index_owner_only": method.get("method_index"),
            "metadata_pointer_owner_only": metadata_pointer,
            "method_pointer_owner_only": method_pointer,
        }
        shaped.append(candidate)
        distance = _shortest_call_distance(
            snapshot=snapshot,
            image=image,
            start_rva=function.begin_rva,
            target_rva=event_helper_rva,
        )
        if distance is not None:
            candidate["native_event_helper_distance_owner_only"] = distance
            reachable.append(candidate)
    if len(shaped) < 2 or len(reachable) != 1:
        raise AcquisitionError(
            "runtime reflection Event collection wrapper is not semantically "
            "unique "
            f"(shaped={len(shaped)}, event-reachable={len(reachable)})"
        )
    return reachable[0], {
        "binding_flag_collection_shape_count": len(shaped),
        "native_event_helper_reachable_count": len(reachable),
    }


def _member_collection_candidates(
    *,
    snapshot: MemorySnapshot,
    image: MappedPE,
    classes: dict[str, Any],
    arity_offset: int,
    helper_rvas: dict[str, int],
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    shaped: list[dict[str, Any]] = []
    for method in classes.get("methods", []):
        if (
            not isinstance(method, dict)
            or method.get("runtime_owner") != "System.RuntimeType"
        ):
            continue
        metadata_pointer = method.get("metadata_pointer")
        method_pointer = method.get("method_pointer")
        raw_arity = (
            snapshot.read(metadata_pointer + arity_offset, 1)
            if isinstance(metadata_pointer, int) and metadata_pointer
            else None
        )
        code = (
            _method_code(
                snapshot=snapshot,
                image=image,
                method_pointer=method_pointer,
            )
            if isinstance(method_pointer, int) and method_pointer
            else None
        )
        if (
            not raw_arity
            or raw_arity[0] != 1
            or code is None
            or not _binding_flag_collection_shape(code)
        ):
            continue
        function = image.containing_function(
            method_pointer - snapshot.image_base
        )
        if function is None:
            continue
        shaped.append(
            {
                "method_index_owner_only": method.get("method_index"),
                "metadata_pointer_owner_only": metadata_pointer,
                "method_pointer_owner_only": method_pointer,
                "function_rva_owner_only": function.begin_rva,
            }
        )
    mapped: dict[str, dict[str, Any]] = {}
    selected_ids: set[int] = set()
    reachability: dict[str, int] = {}
    for semantic_kind, helper_rva in helper_rvas.items():
        matches: list[dict[str, Any]] = []
        for candidate in shaped:
            distance = _shortest_call_distance(
                snapshot=snapshot,
                image=image,
                start_rva=candidate["function_rva_owner_only"],
                target_rva=helper_rva,
            )
            if distance is None:
                continue
            selected = dict(candidate)
            selected["native_helper_distance_owner_only"] = distance
            matches.append(selected)
        reachability[semantic_kind] = len(matches)
        if len(matches) != 1:
            raise AcquisitionError(
                "runtime reflection member collection wrapper is not unique "
                f"(kind={semantic_kind}, candidates={len(matches)})"
            )
        mapped[semantic_kind] = matches[0]
        selected_ids.add(matches[0]["method_index_owner_only"])
    residual = [
        candidate
        for candidate in shaped
        if candidate["method_index_owner_only"] not in selected_ids
    ]
    if len(shaped) != 4 or len(selected_ids) != len(helper_rvas) or len(residual) != 1:
        raise AcquisitionError(
            "runtime reflection member collection family is incomplete "
            f"(shaped={len(shaped)}, mapped={len(selected_ids)}, "
            f"residual={len(residual)})"
        )
    for candidate in mapped.values():
        candidate.pop("function_rva_owner_only", None)
    return mapped, {
        "binding_flag_collection_shape_count": len(shaped),
        "native_helper_reachability": reachability,
        "residual_method_wrapper_count": len(residual),
    }


def _binding(
    *,
    binary: Path,
    snapshot: Path,
    bootstrap_model: Path,
    class_model: Path,
    semantics_model: Path,
    materializer_model: Path | None = None,
    native_helper_model: Path | None = None,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    snapshot = _owner_file(snapshot, label="snapshot")
    bootstrap_model = _owner_file(bootstrap_model, label="bootstrap model")
    class_model = _owner_file(class_model, label="class model")
    semantics_model = _owner_file(semantics_model, label="semantic model")
    memory_status_path = _owner_file(
        snapshot.parent / "memory-status.private.json",
        label="memory capture status",
    )
    identity = file_identity(binary)
    bootstrap = read_json(bootstrap_model)
    classes = read_json(class_model)
    semantics = read_json(semantics_model)
    memory_status = read_json(memory_status_path)
    snapshot_identity = file_identity(snapshot)
    bootstrap_identity = file_identity(bootstrap_model)
    class_identity = file_identity(class_model)
    semantics_identity = file_identity(semantics_model)
    materializer_path: Path | None = None
    materializer: dict[str, Any] | None = None
    materializer_identity: dict[str, Any] | None = None
    native_helper_path: Path | None = None
    native_helpers: dict[str, Any] | None = None
    native_helper_identity: dict[str, Any] | None = None
    native_inventory_path: Path | None = None
    if (materializer_model is None) != (native_helper_model is None):
        raise AcquisitionError(
            "runtime reflection behavior fresh factory requires both the "
            "materializer and native helper models"
        )
    if materializer_model is not None:
        materializer_path = _owner_file(
            materializer_model, label="materializer model"
        )
        materializer = read_json(materializer_path)
        materializer_identity = file_identity(materializer_path)
        native_helper_path = _owner_file(
            native_helper_model, label="native helper model"
        )
        native_helpers = read_json(native_helper_path)
        native_helper_identity = file_identity(native_helper_path)
    if (
        not isinstance(bootstrap, dict)
        or bootstrap.get("schema") != REFLECTION_BOOTSTRAP_SCHEMA
        or bootstrap.get("binary", {}).get("sha256") != identity["sha256"]
        or not isinstance(classes, dict)
        or classes.get("schema") != RUNTIME_CLASS_SCHEMA
        or classes.get("snapshot", {}).get("sha256")
        != snapshot_identity["sha256"]
        or classes.get("bootstrap_model_sha256")
        != bootstrap_identity["sha256"]
        or not isinstance(semantics, dict)
        or semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("snapshot", {}).get("sha256")
        != snapshot_identity["sha256"]
        or semantics.get("class_model_sha256") != class_identity["sha256"]
        or not isinstance(memory_status, dict)
        or memory_status.get("schema") != SNAPSHOT_SCHEMA
        or memory_status.get("status") != "complete"
        or memory_status.get("snapshot_sha256")
        != snapshot_identity["sha256"]
        or memory_status.get("expected_executable_sha256")
        != identity["sha256"]
        or memory_status.get("observed_executable_sha256")
        != identity["sha256"]
    ):
        raise AcquisitionError(
            "runtime reflection behavior input binding is stale"
        )
    process_id = memory_status.get("process_id")
    arity_offset = semantics.get("method_parameter_count", {}).get(
        "selected_byte_offset"
    )
    method_name = [
        operation
        for operation in semantics.get("operations", [])
        if isinstance(operation, dict) and operation.get("key") == "method.name"
    ]
    if (
        not isinstance(process_id, int)
        or process_id <= 0
        or not isinstance(arity_offset, int)
        or not 0 <= arity_offset < 256
        or len(method_name) != 1
        or not method_name[0].get("method_pointer")
        or not method_name[0].get("metadata_pointer")
    ):
        raise AcquisitionError(
            "runtime reflection behavior semantic prerequisites are absent"
        )
    class_rows = {
        value.get("runtime_owner"): value
        for value in classes.get("classes", [])
        if isinstance(value, dict)
    }
    event_class = class_rows.get("System.Reflection.MonoEvent", {}).get(
        "class_pointer"
    )
    method_class = class_rows.get("System.Reflection.MonoMethod", {}).get(
        "class_pointer"
    )
    parameter_class = class_rows.get(
        "System.Reflection.MonoParameterInfo", {}
    ).get("class_pointer")
    runtime_type_class = class_rows.get("System.RuntimeType", {}).get(
        "class_pointer"
    )
    assembly_class = class_rows.get(
        "System.Reflection.MonoAssembly", {}
    ).get("class_pointer")
    field_class = class_rows.get("System.Reflection.MonoField", {}).get(
        "class_pointer"
    )
    property_class = class_rows.get(
        "System.Reflection.MonoProperty", {}
    ).get("class_pointer")
    if not all(
        isinstance(value, int) and value > 0
        for value in (
            event_class,
            method_class,
            parameter_class,
            runtime_type_class,
            assembly_class,
            field_class,
            property_class,
        )
    ):
        raise AcquisitionError(
            "runtime reflection behavior owner classes are incomplete"
        )
    fallback: dict[str, Any] | None = None
    if (
        materializer is not None
        and materializer_path is not None
        and native_helpers is not None
        and native_helper_path is not None
    ):
        validation = materializer.get("runtime_validation")
        helper_validation = native_helpers.get("runtime_validation")
        helper_rows = native_helpers.get("helpers", {})
        member_helpers = {
            "event": helper_rows.get("class_get_events"),
            "field": helper_rows.get("class_get_fields"),
            "property": helper_rows.get("class_get_properties"),
        }
        if (
            materializer.get("schema") != RUNTIME_TYPE_MATERIALIZER_SCHEMA
            or materializer.get("status") != "runtime-validated"
            or materializer.get("binary", {}).get("sha256")
            != identity["sha256"]
            or materializer.get("snapshot", {}).get("sha256")
            != snapshot_identity["sha256"]
            or not isinstance(validation, dict)
            or validation.get("process_id") != process_id
            or native_helpers.get("schema") != RUNTIME_NATIVE_HELPER_SCHEMA
            or native_helpers.get("status")
            != "native-member-iterators-runtime-classified"
            or native_helpers.get("binary", {}).get("sha256")
            != identity["sha256"]
            or native_helpers.get("bootstrap_model_sha256")
            != bootstrap_identity["sha256"]
            or native_helpers.get("class_model_sha256")
            != class_identity["sha256"]
            or not isinstance(helper_validation, dict)
            or helper_validation.get("process_id") != process_id
            or helper_validation.get("checks", {}).get("complete") is not True
            or not all(
                isinstance(helper, dict)
                and helper.get("runtime_validated") is True
                and helper.get("semantic_kind") == kind
                and isinstance(helper.get("function_rva"), int)
                and helper["function_rva"] > 0
                for kind, helper in member_helpers.items()
            )
        ):
            raise AcquisitionError(
                "runtime reflection behavior fresh factory binding is stale"
            )
        member_inventory = _owner_file(
            materializer_path.parent / "runtime-native-members.private.bin",
            label="native member inventory",
        )
        native_inventory_path = _owner_file(
            materializer_path.parent / "runtime-native-inventory.private.bin",
            label="native type inventory",
        )
        fallback = _event_definition_domain(
            materializer=materializer,
            member_inventory=member_inventory,
        )
        fallback["materializer_identity"] = materializer_identity
        fallback["member_inventory_identity"] = file_identity(member_inventory)
        fallback["native_helper_identity"] = native_helper_identity
        fallback["member_helper_rvas_owner_only"] = {
            kind: helper["function_rva"]
            for kind, helper in member_helpers.items()
        }
    with MemorySnapshot(snapshot) as memory, MappedPE(binary) as image:
        if memory.image_bytes != image.size_of_image:
            raise AcquisitionError(
                "runtime reflection behavior image binding is stale"
            )
        string_caches = [
            cache
            for cache in bootstrap.get("type_caches", [])
            if cache.get("namespace") == "System"
            and cache.get("type_name") == "String"
        ]
        if len(string_caches) != 1:
            raise AcquisitionError(
                "runtime reflection behavior String cache is not unique"
            )
        string_values = memory.qwords(
            memory.image_base + string_caches[0]["result_slot_rva"], 1
        )
        string_class = string_values[0] if string_values else 0
        if not string_class:
            raise AcquisitionError(
                "runtime reflection behavior String class is unavailable"
            )
        if fallback is not None:
            if materializer is None or native_inventory_path is None:
                raise AcquisitionError(
                    "runtime reflection Type identity inventory is absent"
                )
            identity_classes = dict(class_rows)
            identity_classes["System.String"] = {
                "class_pointer": string_class
            }
            fallback.update(
                _known_type_identity_domain(
                    materializer=materializer,
                    native_inventory=native_inventory_path,
                    class_rows=identity_classes,
                )
            )
        families: dict[int, dict[str, list[dict[str, Any]]]] = defaultdict(
            lambda: {"bool": [], "zero": []}
        )
        event_handler_candidates: list[dict[str, Any]] = []
        for method in classes.get("methods", []):
            if (
                not isinstance(method, dict)
                or method.get("runtime_owner")
                != "System.Reflection.MonoEvent"
            ):
                continue
            metadata_pointer = method.get("metadata_pointer")
            method_pointer = method.get("method_pointer")
            raw_arity = (
                memory.read(metadata_pointer + arity_offset, 1)
                if isinstance(metadata_pointer, int) and metadata_pointer
                else None
            )
            code = (
                _method_code(
                    snapshot=memory,
                    image=image,
                    method_pointer=method_pointer,
                )
                if isinstance(method_pointer, int) and method_pointer
                else None
            )
            if raw_arity is None or code is None:
                continue
            arity = raw_arity[0]
            for label, bool_argument, expected_arity in (
                ("bool", True, 1),
                ("zero", False, 0),
            ):
                if arity != expected_arity:
                    continue
                shape = _event_helper_result_shape(
                    code,
                    method_pointer=method_pointer,
                    bool_argument=bool_argument,
                )
                if shape is not None:
                    families[shape[0]][label].append(
                        {
                            "method_index_owner_only": method.get(
                                "method_index"
                            ),
                            "metadata_pointer_owner_only": metadata_pointer,
                            "method_pointer_owner_only": method_pointer,
                            "stack_offset_owner_only": shape[1],
                        }
                    )
        for method in classes.get("methods", []):
            if (
                not isinstance(method, dict)
                or method.get("runtime_owner")
                != "System.Reflection.EventInfo"
            ):
                continue
            metadata_pointer = method.get("metadata_pointer")
            method_pointer = method.get("method_pointer")
            raw_arity = (
                memory.read(metadata_pointer + arity_offset, 1)
                if isinstance(metadata_pointer, int) and metadata_pointer
                else None
            )
            code = (
                _method_code(
                    snapshot=memory,
                    image=image,
                    method_pointer=method_pointer,
                )
                if isinstance(method_pointer, int) and method_pointer
                else None
            )
            if (
                raw_arity
                and raw_arity[0] == 0
                and code is not None
                and _event_handler_type_shape(code)
            ):
                event_handler_candidates.append(
                    {
                        "method_index_owner_only": method.get("method_index"),
                        "metadata_pointer_owner_only": metadata_pointer,
                        "method_pointer_owner_only": method_pointer,
                    }
                )
        complete = [
            (helper, family)
            for helper, family in families.items()
            if len(family["bool"]) == 3
            and len(family["zero"]) == 3
            and len(
                {value["stack_offset_owner_only"] for value in family["bool"]}
            )
            == 3
            and len(
                {value["stack_offset_owner_only"] for value in family["zero"]}
            )
            == 3
        ]
        if len(complete) != 1:
            raise AcquisitionError(
                "runtime reflection behavior event helper family is not unique "
                f"(candidates={len(complete)})"
            )
        if fallback is not None and len(event_handler_candidates) != 1:
            raise AcquisitionError(
                "runtime reflection Event handler-type composition is not unique"
            )
        helper_pointer, family = complete[0]
        if fallback is not None:
            member_collections, collection_evidence = (
                _member_collection_candidates(
                    snapshot=memory,
                    image=image,
                    classes=classes,
                    arity_offset=arity_offset,
                    helper_rvas=fallback[
                        "member_helper_rvas_owner_only"
                    ],
                )
            )
            method_collections = _method_collection_candidates(
                snapshot=memory,
                image=image,
                classes=classes,
                arity_offset=arity_offset,
            )
            metadata_byte_offset = (
                semantics.get("method_name_decoder", {}).get(
                    "metadata_field_qword", -1
                )
                * 8
            )
            method_semantics: dict[str, list[dict[str, Any]]] = {
                key: [] for key in _METHOD_OPERATION_KEYS
            }
            method_return_shapes: list[dict[str, int]] = []
            type_identity_domain: list[dict[str, Any]] = []
            for method in classes.get("methods", []):
                if (
                    not isinstance(method, dict)
                    or method.get("runtime_owner")
                    != "System.Reflection.MonoMethod"
                ):
                    continue
                metadata_pointer = method.get("metadata_pointer")
                method_pointer = method.get("method_pointer")
                raw_arity = (
                    memory.read(metadata_pointer + arity_offset, 1)
                    if isinstance(metadata_pointer, int)
                    and metadata_pointer
                    else None
                )
                code = (
                    _method_code(
                        snapshot=memory,
                        image=image,
                        method_pointer=method_pointer,
                    )
                    if isinstance(method_pointer, int) and method_pointer
                    else None
                )
                if not raw_arity or raw_arity[0] != 0 or code is None:
                    continue
                row = {
                    "method_index_owner_only": method.get("method_index"),
                    "metadata_pointer_owner_only": metadata_pointer,
                    "method_pointer_owner_only": method_pointer,
                }
                return_shape = _method_return_type_shape(
                    code,
                    method_pointer=method_pointer,
                    metadata_byte_offset=metadata_byte_offset,
                )
                if return_shape is not None:
                    method_semantics["method.return_type"].append(row)
                    method_return_shapes.append(return_shape)
                if _method_parameters_shape(
                    code,
                    metadata_byte_offset=metadata_byte_offset,
                ) is not None:
                    method_semantics["method.parameters"].append(row)
            type_ancestry = _runtime_type_ancestry_method_domain(
                native_inventory=native_inventory_path,
                snapshot=memory,
                runtime_type_class=class_rows["System.RuntimeType"][
                    "class_pointer"
                ],
            )
            byref_operations = [
                operation
                for operation in semantics.get("operations", [])
                if isinstance(operation, dict)
                and operation.get("key") == "type.is_byref"
                and operation.get("semantic_identity_resolved") is True
            ]
            if len(byref_operations) != 1:
                raise AcquisitionError(
                    "runtime reflection Type boolean ABI sentinel is absent"
                )
            boolean_invoker_raw = memory.read(
                byref_operations[0]["metadata_pointer"] + 16, 8
            )
            if not boolean_invoker_raw:
                raise AcquisitionError(
                    "runtime reflection Type boolean ABI is unreadable"
                )
            named_operations: dict[str, Mapping[str, Any]] = {}
            by_name = _reflection_families_by_method_name(
                semantics_model.parent.parent
                / "method-names"
                / "runtime-method-names.private.bin"
            )
            for family_name, row in by_name.items():
                named_operations.setdefault(family_name, row)
            for operation in semantics.get("operations", []):
                if (
                    not isinstance(operation, Mapping)
                    or operation.get("semantic_identity_resolved") is not True
                ):
                    continue
                key = operation.get("key")
                if not isinstance(key, str) or not key.startswith("type."):
                    continue
                operation_family = key[len("type."):]
                named_operations[operation_family] = operation
                if operation_family == "module":
                    named_operations["module_pair"] = operation
                elif operation_family == "declaring_type":
                    named_operations["declaring_type_pair"] = operation
            type_extended_families, type_extended_evidence = (
                _runtime_type_extended_candidate_family(
                    methods=type_ancestry["methods_owner_only"],
                    snapshot=memory,
                    image=image,
                    arity_offset=arity_offset,
                    boolean_invoker=struct.unpack(
                        "<Q", boolean_invoker_raw
                    )[0],
                    named_operations=named_operations,
                )
            )
            remaining_families, remaining_evidence = (
                _remaining_reflection_candidate_families(
                    methods=classes.get("methods", []),
                    snapshot=memory,
                    image=image,
                    arity_offset=arity_offset,
                )
            )
            for method in type_ancestry["methods_owner_only"]:
                metadata_pointer = method.get("metadata_pointer")
                method_pointer = method.get("method_pointer")
                if metadata_pointer is None:
                    metadata_pointer = method.get(
                        "metadata_pointer_owner_only"
                    )
                if method_pointer is None:
                    method_pointer = method.get("method_pointer_owner_only")
                raw_arity = (
                    memory.read(metadata_pointer + arity_offset, 1)
                    if isinstance(metadata_pointer, int)
                    and metadata_pointer
                    else None
                )
                code = (
                    _method_code(
                        snapshot=memory,
                        image=image,
                        method_pointer=method_pointer,
                    )
                    if isinstance(method_pointer, int) and method_pointer
                    else None
                )
                if (
                    raw_arity
                    and raw_arity[0] == 0
                    and code is not None
                ):
                    type_identity_domain.append(
                        {
                            "method_index_owner_only": method.get(
                                "method_index_owner_only"
                            ),
                            "metadata_pointer_owner_only": metadata_pointer,
                            "method_pointer_owner_only": method_pointer,
                            "owner_descriptor_pointer_owner_only": method.get(
                                "owner_descriptor_pointer_owner_only"
                            ),
                            "code_owner_only": code,
                        }
                    )
            if any(
                len(method_semantics[key]) != 1
                for key in _METHOD_OPERATION_KEYS
            ):
                raise AcquisitionError(
                    "runtime reflection Method behavior candidates are not "
                    "semantically unique "
                    f"(return_type={len(method_semantics['method.return_type'])}, "
                    f"parameters={len(method_semantics['method.parameters'])})"
                )
            if len(method_return_shapes) != 1:
                raise AcquisitionError(
                    "runtime reflection Method return decoder is not unique"
                )
            (
                type_identity_candidates,
                type_identity_callgraph_evidence,
            ) = _runtime_type_identity_string_family(
                type_identity_domain,
                snapshot=memory,
                image=image,
                semantics=semantics,
            )
            metadata_token_candidates: list[dict[str, Any]] = []
            for method in classes.get("methods", []):
                if (
                    not isinstance(method, dict)
                    or method.get("runtime_owner")
                    != "System.Reflection.MemberInfo"
                ):
                    continue
                metadata_pointer = method.get("metadata_pointer")
                method_pointer = method.get("method_pointer")
                raw_arity = (
                    memory.read(metadata_pointer + arity_offset, 1)
                    if isinstance(metadata_pointer, int)
                    and metadata_pointer
                    else None
                )
                shape = (
                    _metadata_token_dispatch_shape(
                        snapshot=memory,
                        image=image,
                        method_pointer=method_pointer,
                    )
                    if isinstance(method_pointer, int) and method_pointer
                    else None
                )
                if raw_arity and raw_arity[0] == 0 and shape is not None:
                    metadata_token_candidates.append(
                        {
                            "method_index_owner_only": method.get(
                                "method_index"
                            ),
                            "metadata_pointer_owner_only": metadata_pointer,
                            "method_pointer_owner_only": method_pointer,
                            "dispatch_evidence_owner_only": shape,
                        }
                    )
            if len(metadata_token_candidates) != 1:
                raise AcquisitionError(
                    "runtime reflection metadata-token dispatch is not unique"
                )
            parameter_type = [
                operation
                for operation in semantics.get("operations", [])
                if isinstance(operation, dict)
                and operation.get("key") == "parameter.type"
                and operation.get("semantic_identity_resolved") is True
            ]
            if len(parameter_type) != 1 or not all(
                isinstance(parameter_type[0].get(field), int)
                and parameter_type[0][field] > 0
                for field in (
                    "method_index",
                    "metadata_pointer",
                    "method_pointer",
                )
            ):
                raise AcquisitionError(
                    "runtime reflection Parameter type operation is not unique"
                )
            field_attributes = [
                operation
                for operation in semantics.get("operations", [])
                if isinstance(operation, dict)
                and operation.get("key") == "field.attributes"
                and operation.get("semantic_identity_resolved") is True
            ]
            if len(field_attributes) != 1 or not all(
                isinstance(field_attributes[0].get(field), int)
                and field_attributes[0][field] > 0
                for field in (
                    "method_index",
                    "metadata_pointer",
                    "method_pointer",
                )
            ):
                raise AcquisitionError(
                    "runtime reflection Field attributes operation is not "
                    "unique"
                )
            from_handle = [
                operation
                for operation in semantics.get("operations", [])
                if isinstance(operation, dict)
                and operation.get("key") == "type.from_handle"
            ]
            if len(from_handle) != 1:
                raise AcquisitionError(
                    "runtime reflection behavior fresh Event factory is not unique"
                )
            fallback["descriptor_pointers_owner_only"] = [
                memory.image_base + descriptor_rva
                for descriptor_rva in fallback[
                    "descriptor_rvas_owner_only"
                ]
            ]
            descriptor_by_definition = dict(
                zip(
                    fallback["definition_indexes_owner_only"],
                    fallback["descriptor_pointers_owner_only"],
                    strict=True,
                )
            )
            fallback["member_handle_samples_owner_only"] = {
                kind: _balanced_member_handle_samples(
                    fallback["member_metadata_rows_owner_only"][kind],
                    descriptor_by_definition=descriptor_by_definition,
                )
                for kind in ("field", "property")
            }
            for row in fallback["known_type_identity_rows_owner_only"]:
                row["descriptor_pointer_owner_only"] = (
                    memory.image_base + row["descriptor_rva_owner_only"]
                )
            known_identity_by_owner = {
                row["runtime_owner"]: row
                for row in fallback[
                    "known_type_identity_rows_owner_only"
                ]
            }
            if not all(
                owner in known_identity_by_owner
                for owner in ("System.RuntimeType", "System.String")
            ):
                raise AcquisitionError(
                    "runtime reflection Type identity sentinels are absent"
                )
            fallback["runtime_type_descriptor_pointer_owner_only"] = (
                known_identity_by_owner["System.RuntimeType"][
                    "descriptor_pointer_owner_only"
                ]
            )
            fallback["string_descriptor_pointer_owner_only"] = (
                known_identity_by_owner["System.String"][
                    "descriptor_pointer_owner_only"
                ]
            )
            fallback["type_definition_count"] = len(
                materializer.get("type_definitions", [])
            )
            inventory_layout = materializer.get("inventory_layout", {})
            class_name_qword = inventory_layout.get(
                "class_name_pointer_qword"
            )
            if (
                not isinstance(class_name_qword, int)
                or not 0 <= class_name_qword < 128
            ):
                raise AcquisitionError(
                    "runtime reflection class-name layout is unavailable"
                )
            fallback["class_name_pointer_qword_owner_only"] = (
                class_name_qword
            )
            fallback["method_object_metadata_byte_offset_owner_only"] = (
                metadata_byte_offset
            )
            fallback["type_from_handle_owner_only"] = {
                "method_index_owner_only": from_handle[0]["method_index"],
                "metadata_pointer_owner_only": from_handle[0][
                    "metadata_pointer"
                ],
                "method_pointer_owner_only": from_handle[0]["method_pointer"],
            }
            fallback["collection_candidates_owner_only"] = [
                member_collections["event"]
            ]
            fallback["member_collection_candidates_owner_only"] = (
                member_collections
            )
            fallback["method_collection_candidates_owner_only"] = (
                method_collections
            )
            fallback["collection_callgraph_evidence"] = collection_evidence
            fallback["method_semantic_candidates_owner_only"] = {
                key: rows[0] for key, rows in method_semantics.items()
            }
            fallback["method_return_decoder_owner_only"] = (
                method_return_shapes[0]
            )
            fallback["method_name_decoder_owner_only"] = dict(
                semantics["method_name_decoder"]
            )
            fallback["member_semantic_candidates_owner_only"] = {
                "member.metadata_token": metadata_token_candidates[0],
                "field.attributes": {
                    "method_index_owner_only": field_attributes[0][
                        "method_index"
                    ],
                    "metadata_pointer_owner_only": field_attributes[0][
                        "metadata_pointer"
                    ],
                    "method_pointer_owner_only": field_attributes[0][
                        "method_pointer"
                    ],
                },
            }
            fallback["parameter_type_owner_only"] = {
                "method_index_owner_only": parameter_type[0]["method_index"],
                "metadata_pointer_owner_only": parameter_type[0][
                    "metadata_pointer"
                ],
                "method_pointer_owner_only": parameter_type[0][
                    "method_pointer"
                ],
            }
            fallback["event_handler_semantic_candidate_owner_only"] = (
                event_handler_candidates[0]
            )
            fallback["type_identity_string_candidates_owner_only"] = (
                type_identity_candidates
            )
            fallback["type_identity_callgraph_evidence"] = (
                type_identity_callgraph_evidence
            )
            fallback["type_identity_ancestry_evidence"] = {
                "ancestry_class_count": type_ancestry[
                    "ancestry_class_count"
                ],
                "ancestry_method_count": type_ancestry[
                    "ancestry_method_count"
                ],
                "hierarchy_prefixes_runtime_validated": True,
            }
            fallback["type_extended_candidates_owner_only"] = (
                type_extended_families
            )
            fallback["type_extended_structural_evidence"] = (
                type_extended_evidence
            )
            fallback["remaining_candidates_owner_only"] = (
                remaining_families
            )
            fallback["remaining_structural_evidence"] = (
                remaining_evidence
            )
            fallback.update(
                _runtime_type_semantic_samples(
                    native_inventory=native_inventory_path,
                    snapshot=memory,
                    class_rows=identity_classes,
                )
            )
        event_objects: list[int] = []
        for reference in memory.references(event_class):
            values = memory.qwords(reference, 1)
            if values and values[0] == event_class:
                event_objects.append(reference)
                if len(event_objects) == 64:
                    break
        if len(event_objects) < 8 and fallback is None:
            raise AcquisitionError(
                "runtime reflection behavior event object domain is incomplete"
            )
        image_base = memory.image_base
        image_bytes = memory.image_bytes
    return {
        "binary": identity,
        "snapshot": snapshot_identity,
        "bootstrap": bootstrap_identity,
        "classes": class_identity,
        "semantics": semantics_identity,
        "memory_status": file_identity(memory_status_path),
        "process_id": process_id,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "classes_owner_only": {
            "event": event_class,
            "method": method_class,
            "parameter": parameter_class,
            "runtime_type": runtime_type_class,
            "string": string_class,
            "assembly": assembly_class,
            "field": field_class,
            "property": property_class,
        },
        "method_name_owner_only": {
            "metadata": method_name[0]["metadata_pointer"],
            "pointer": method_name[0]["method_pointer"],
        },
        "method_parameter_count_byte_offset_owner_only": arity_offset,
        "helper_pointer_owner_only": helper_pointer,
        "bool_candidates_owner_only": family["bool"],
        "zero_candidates_owner_only": family["zero"],
        "snapshot_event_object_evidence_count": len(event_objects),
        "fresh_event_factory_owner_only": fallback,
    }


def _candidate_rows(values: list[dict[str, Any]]) -> str:
    return ",\n".join(
        "    {"
        f"{value['metadata_pointer_owner_only']}ull, "
        f"{value['method_pointer_owner_only']}ull, "
        f"{value['method_index_owner_only']}u"
        "}"
        for value in values
    )


def _type_identity_candidate_rows(values: list[dict[str, Any]]) -> str:
    return ",\n".join(
        "    {"
        f"{value['metadata_pointer_owner_only']}ull, "
        f"{value['method_pointer_owner_only']}ull, "
        f"{value['method_index_owner_only']}u, "
        f"{value['owner_descriptor_pointer_owner_only']}ull"
        "}"
        for value in values
    )


def runtime_reflection_behavior_source(
    *,
    binding: dict[str, Any],
    status_path: Path,
) -> str:
    status_literal = _wide_literal(_windows_z_path(status_path))
    classes = binding["classes_owner_only"]
    method_name = binding["method_name_owner_only"]
    method_parameter_count_byte_offset = binding.get(
        "method_parameter_count_byte_offset_owner_only", 0
    )
    bool_rows = _candidate_rows(binding["bool_candidates_owner_only"])
    zero_rows = _candidate_rows(binding["zero_candidates_owner_only"])
    fallback = binding.get("fresh_event_factory_owner_only")
    if isinstance(fallback, dict):
        type_from_handle = fallback["type_from_handle_owner_only"]
        type_from_handle_row = (
            "    {"
            f"{type_from_handle['metadata_pointer_owner_only']}ull, "
            f"{type_from_handle['method_pointer_owner_only']}ull, "
            f"{type_from_handle['method_index_owner_only']}u"
            "}"
        )
        collection_rows = _candidate_rows(
            fallback["collection_candidates_owner_only"]
        )
        collection_count = len(
            fallback["collection_candidates_owner_only"]
        )
        event_descriptor_rows = ",\n".join(
            f"    {value}ull"
            for value in fallback["descriptor_pointers_owner_only"]
        )
        event_descriptor_count = len(
            fallback["descriptor_pointers_owner_only"]
        )
        method_collection_rows = _candidate_rows(
            fallback["method_collection_candidates_owner_only"]
        )
        method_collection_count = len(
            fallback["method_collection_candidates_owner_only"]
        )
        field_collection_row = _candidate_rows(
            [fallback["member_collection_candidates_owner_only"]["field"]]
        )
        property_collection_row = _candidate_rows(
            [
                fallback["member_collection_candidates_owner_only"][
                    "property"
                ]
            ]
        )
        method_return_row = _candidate_rows(
            [fallback["method_semantic_candidates_owner_only"][
                "method.return_type"
            ]]
        )
        method_parameters_row = _candidate_rows(
            [fallback["method_semantic_candidates_owner_only"][
                "method.parameters"
            ]]
        )
        metadata_token_row = _candidate_rows(
            [fallback["member_semantic_candidates_owner_only"][
                "member.metadata_token"
            ]]
        )
        field_attributes_row = _candidate_rows(
            [fallback["member_semantic_candidates_owner_only"][
                "field.attributes"
            ]]
        )
        parameter_type_row = _candidate_rows(
            [fallback["parameter_type_owner_only"]]
        )
        event_handler_row = _candidate_rows(
            [fallback["event_handler_semantic_candidate_owner_only"]]
        )
        type_identity_rows = _type_identity_candidate_rows(
            fallback["type_identity_string_candidates_owner_only"]
        )
        type_identity_candidate_count = len(
            fallback["type_identity_string_candidates_owner_only"]
        )
        extended = fallback["type_extended_candidates_owner_only"]
        module_rows = _candidate_rows(extended["module_pair"])
        module_candidate_count = len(extended["module_pair"])
        declaring_rows = _candidate_rows(extended["declaring_type_pair"])
        declaring_candidate_count = len(
            extended["declaring_type_pair"]
        )
        extended_single_rows = {
            key: _candidate_rows(extended[key])
            for key in (
                "base_type",
                "element_type",
                "generic_arguments",
                "generic_definition",
                "interfaces",
                "attributes",
                "is_enum",
                "is_value_type",
                "is_generic_definition",
                "is_generic",
            )
        }
        extended_single_counts = {
            key: len(extended[key])
            for key in extended_single_rows
        }
        remaining = fallback["remaining_candidates_owner_only"]
        remaining_single_rows = {
            key: _candidate_rows(remaining[key])
            for key in (
                "property.from_handle",
                "field.set_value",
                "field.get_value",
                "field.raw_constant",
                "field.from_handle",
                "method.from_handle",
            )
        }
        enum_underlying_rows = _candidate_rows(
            remaining["enum.underlying_type"]
        )
        enum_underlying_candidate_count = len(
            remaining["enum.underlying_type"]
        )
        property_handle_protection = remaining[
            "property.from_handle"
        ][0]
        property_handle_owner_addend = property_handle_protection[
            "protected_owner_addend_owner_only"
        ]
        property_handle_owner_codec = {
            "add": 1,
            "xor": 2,
        }.get(
            property_handle_protection.get(
                "protected_owner_codec_owner_only"
            ),
            0,
        )
        if not property_handle_owner_codec:
            raise AcquisitionError(
                "runtime reflection property owner codec is unsupported"
            )
        property_handle_owner_byte_offset = property_handle_protection[
            "protected_owner_byte_offset_owner_only"
        ]
        property_object_handle_byte_offset = property_handle_protection[
            "property_object_handle_byte_offset_owner_only"
        ]
        member_metadata = fallback[
            "member_metadata_pointers_owner_only"
        ]
        field_metadata_rows = ",\n".join(
            f"    {value}ull" for value in member_metadata["field"]
        )
        field_metadata_count = len(member_metadata["field"])
        property_metadata_rows = ",\n".join(
            f"    {value}ull" for value in member_metadata["property"]
        )
        property_metadata_count = len(member_metadata["property"])
        handle_samples = fallback["member_handle_samples_owner_only"]
        field_handle_sample_rows = ",\n".join(
            "    {"
            f"{row['metadata_pointer_owner_only']}ull, "
            f"{row['owner_descriptor_pointer_owner_only']}ull"
            "}"
            for row in handle_samples["field"]
        )
        field_handle_sample_count = len(handle_samples["field"])
        property_handle_sample_rows = ",\n".join(
            "    {"
            f"{row['metadata_pointer_owner_only']}ull, "
            f"{row['owner_descriptor_pointer_owner_only']}ull"
            "}"
            for row in handle_samples["property"]
        )
        property_handle_sample_count = len(handle_samples["property"])
        type_semantic_rows = ",\n".join(
            "    {"
            f"{row['descriptor_pointer_owner_only']}ull, "
            f"{row['expected_base_descriptor_owner_only']}ull, "
            f"{row['expected_declaring_descriptor_owner_only']}ull, "
            f"{int(row['expected_declaring_available'])}u, "
            f"{int(row['expected_is_enum'])}u, "
            f"{int(row['expected_is_value_type'])}u, "
            f"{int(row['expected_is_generic'])}u, "
            f"{int(row['expected_is_generic_definition'])}u"
            "}"
            for row in fallback["type_semantic_samples_owner_only"]
        )
        type_semantic_sample_count = fallback[
            "type_semantic_sample_count"
        ]
        structural_string_safe = int(
            fallback.get("type_identity_callgraph_evidence", {}).get(
                "structural_string_return_safe"
            )
            is True
        )
        known_type_rows = ",\n".join(
            "    {"
            f"{row['descriptor_pointer_owner_only']}ull, "
            f"{_wide_literal(row['namespace'])}, "
            f"{_wide_literal(row['type_name'])}"
            "}"
            for row in fallback["known_type_identity_rows_owner_only"]
        )
        known_type_count = len(
            fallback["known_type_identity_rows_owner_only"]
        )
        runtime_type_descriptor = fallback[
            "runtime_type_descriptor_pointer_owner_only"
        ]
        string_descriptor = fallback[
            "string_descriptor_pointer_owner_only"
        ]
        type_definition_count = fallback["type_definition_count"]
        class_name_pointer_qword = fallback[
            "class_name_pointer_qword_owner_only"
        ]
        method_object_metadata_byte_offset = fallback[
            "method_object_metadata_byte_offset_owner_only"
        ]
        return_decoder = fallback["method_return_decoder_owner_only"]
        return_managed_type_helper = return_decoder["managed_type_helper"]
        return_context_owner_byte_offset = return_decoder[
            "return_type_owner_byte_offset"
        ]
        return_context_embedded_type_byte_offset = return_decoder[
            "embedded_type_byte_offset"
        ]
        return_cache_node_byte_offset = return_decoder[
            "cache_node_byte_offset"
        ]
        return_encoded_type_byte_offset = return_decoder[
            "encoded_type_byte_offset"
        ]
        return_type_xor_key = return_decoder["xor_key"]
        return_lazy_node_helper = return_decoder["lazy_node_helper"]
        name_decoder = fallback["method_name_decoder_owner_only"]
        method_name_node_qword = name_decoder["name_node_field_qword"]
        method_name_encoded_qword = name_decoder[
            "encoded_name_field_qword"
        ]
        name_decode_operation = name_decoder.get("decode_operation")
        method_name_decode_key = name_decoder.get("decode_key")
        if name_decode_operation is None and type(name_decoder.get("xor_key")) is int:
            legacy_xor_key = name_decoder["xor_key"]
            if legacy_xor_key > 0:
                name_decode_operation = "xor"
                method_name_decode_key = legacy_xor_key
        if (
            type(name_decode_operation) is not str
            or name_decode_operation not in METHOD_NAME_DECODE_OPERATION_CODES
            or type(method_name_decode_key) is not int
            or not 0 < method_name_decode_key < 1 << 64
        ):
            raise AcquisitionError(
                "runtime reflection method name decoder operation is invalid"
            )
        method_name_decode_operation_code = (
            METHOD_NAME_DECODE_OPERATION_CODES[name_decode_operation]
        )
        method_name_lazy_initializer = name_decoder["lazy_initializer"]
        fresh_relation_available = 1
    else:
        type_from_handle_row = "    {0ull, 0ull, 0u}"
        collection_rows = "    {0ull, 0ull, 0u}"
        collection_count = 0
        event_descriptor_rows = "    0ull"
        event_descriptor_count = 0
        method_collection_rows = "    {0ull, 0ull, 0u}"
        method_collection_count = 0
        field_collection_row = "    {0ull, 0ull, 0u}"
        property_collection_row = "    {0ull, 0ull, 0u}"
        method_return_row = "    {0ull, 0ull, 0u}"
        method_parameters_row = "    {0ull, 0ull, 0u}"
        metadata_token_row = "    {0ull, 0ull, 0u}"
        field_attributes_row = "    {0ull, 0ull, 0u}"
        parameter_type_row = "    {0ull, 0ull, 0u}"
        event_handler_row = "    {0ull, 0ull, 0u}"
        type_identity_rows = "    {0ull, 0ull, 0u, 0ull}"
        type_identity_candidate_count = 0
        module_rows = "    {0ull, 0ull, 0u}"
        module_candidate_count = 0
        declaring_rows = "    {0ull, 0ull, 0u}"
        declaring_candidate_count = 0
        extended_single_rows = {
            key: "    {0ull, 0ull, 0u}"
            for key in (
                "base_type",
                "element_type",
                "generic_arguments",
                "generic_definition",
                "interfaces",
                "attributes",
                "is_enum",
                "is_value_type",
                "is_generic_definition",
                "is_generic",
            )
        }
        extended_single_counts = {
            key: 0 for key in extended_single_rows
        }
        remaining_single_rows = {
            key: "    {0ull, 0ull, 0u}"
            for key in (
                "property.from_handle",
                "field.set_value",
                "field.get_value",
                "field.raw_constant",
                "field.from_handle",
                "method.from_handle",
            )
        }
        enum_underlying_rows = "    {0ull, 0ull, 0u}"
        enum_underlying_candidate_count = 0
        property_handle_owner_addend = 0
        property_handle_owner_codec = 0
        property_handle_owner_byte_offset = 0
        property_object_handle_byte_offset = 0
        field_metadata_rows = "    0ull"
        field_metadata_count = 0
        property_metadata_rows = "    0ull"
        property_metadata_count = 0
        field_handle_sample_rows = "    {0ull, 0ull}"
        field_handle_sample_count = 0
        property_handle_sample_rows = "    {0ull, 0ull}"
        property_handle_sample_count = 0
        type_semantic_rows = (
            "    {0ull, 0ull, 0ull, 0u, 0u, 0u, 0u, 0u}"
        )
        type_semantic_sample_count = 0
        structural_string_safe = 0
        known_type_rows = "    {0ull, L\"\", L\"\"}"
        known_type_count = 0
        runtime_type_descriptor = 0
        string_descriptor = 0
        type_definition_count = 0
        class_name_pointer_qword = 0
        method_object_metadata_byte_offset = 0
        return_managed_type_helper = 0
        return_context_owner_byte_offset = 0
        return_context_embedded_type_byte_offset = 0
        return_cache_node_byte_offset = 0
        return_encoded_type_byte_offset = 0
        return_type_xor_key = 0
        return_lazy_node_helper = 0
        method_name_node_qword = 0
        method_name_encoded_qword = 0
        method_name_decode_operation_code = 0
        method_name_decode_key = 0
        method_name_lazy_initializer = 0
        fresh_relation_available = 0
    return rf'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <wchar.h>

#define ALPHA_EVENT_OBJECT_LIMIT 64u
#define ALPHA_FIELD_OBJECT_LIMIT 256u
#define ALPHA_EVENT_BOOL_CANDIDATE_COUNT 3u
#define ALPHA_EVENT_ZERO_CANDIDATE_COUNT 3u
#define ALPHA_MEMBER_BINDING_FLAGS 0x3cu
#define ALPHA_TYPE_IDENTITY_METHOD_BINDING_FLAGS ALPHA_MEMBER_BINDING_FLAGS
#define ALPHA_RUNTIME_TYPE_HANDLE_QWORD_LIMIT 32u
#define ALPHA_METHOD_METADATA_OBJECT_SCAN_QWORDS 32u
#define ALPHA_METHOD_METADATA_SAMPLE_BYTES 256u
#define ALPHA_TYPE_COLLECTION_CANDIDATE_COUNT {collection_count}u
#define ALPHA_METHOD_COLLECTION_CANDIDATE_COUNT {method_collection_count}u
#define ALPHA_EVENT_TYPE_DESCRIPTOR_COUNT {event_descriptor_count}u
#define ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT {type_identity_candidate_count}u
#define ALPHA_TYPE_IDENTITY_STRUCTURAL_STRING_SAFE {structural_string_safe}u
#define ALPHA_TYPE_MODULE_CANDIDATE_COUNT {module_candidate_count}u
#define ALPHA_TYPE_DECLARING_CANDIDATE_COUNT {declaring_candidate_count}u
#define ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT \
    {extended_single_counts['attributes']}u
#define ALPHA_TYPE_IS_ENUM_CANDIDATE_COUNT \
    {extended_single_counts['is_enum']}u
#define ALPHA_TYPE_IS_VALUE_TYPE_CANDIDATE_COUNT \
    {extended_single_counts['is_value_type']}u
#define ALPHA_TYPE_SEMANTIC_SAMPLE_COUNT {type_semantic_sample_count}u
#define ALPHA_ENUM_UNDERLYING_CANDIDATE_COUNT \
    {enum_underlying_candidate_count}u
#define ALPHA_FIELD_METADATA_COUNT {field_metadata_count}u
#define ALPHA_PROPERTY_METADATA_COUNT {property_metadata_count}u
#define ALPHA_FIELD_HANDLE_SAMPLE_COUNT {field_handle_sample_count}u
#define ALPHA_PROPERTY_HANDLE_SAMPLE_COUNT {property_handle_sample_count}u
#define ALPHA_KNOWN_TYPE_IDENTITY_COUNT {known_type_count}u
#define ALPHA_TYPE_DEFINITION_COUNT {type_definition_count}u
#define ALPHA_CLASS_NAME_POINTER_QWORD {class_name_pointer_qword}u
#define ALPHA_METHOD_OBJECT_METADATA_BYTE_OFFSET \
    {method_object_metadata_byte_offset}u
#define ALPHA_METHOD_PARAMETER_COUNT_BYTE_OFFSET \
    {method_parameter_count_byte_offset}u
#define ALPHA_RETURN_CACHE_NODE_BYTE_OFFSET \
    {return_cache_node_byte_offset}u
#define ALPHA_RETURN_ENCODED_TYPE_BYTE_OFFSET \
    {return_encoded_type_byte_offset}u
#define ALPHA_RETURN_CONTEXT_OWNER_BYTE_OFFSET \
    {return_context_owner_byte_offset}u
#define ALPHA_RETURN_CONTEXT_EMBEDDED_TYPE_BYTE_OFFSET \
    {return_context_embedded_type_byte_offset}u
#define ALPHA_METHOD_NAME_NODE_QWORD {method_name_node_qword}u
#define ALPHA_METHOD_NAME_ENCODED_QWORD {method_name_encoded_qword}u
#define ALPHA_PROPERTY_HANDLE_OWNER_BYTE_OFFSET \
    {property_handle_owner_byte_offset}u
#define ALPHA_PROPERTY_HANDLE_OWNER_CODEC \
    {property_handle_owner_codec}u
#define ALPHA_PROPERTY_OBJECT_HANDLE_BYTE_OFFSET \
    {property_object_handle_byte_offset}u
#define ALPHA_FRESH_RELATION_AVAILABLE {fresh_relation_available}u
#define ALPHA_TYPE_COLLECTION_STORAGE \
    (ALPHA_TYPE_COLLECTION_CANDIDATE_COUNT \
        ? ALPHA_TYPE_COLLECTION_CANDIDATE_COUNT : 1u)
#define ALPHA_TYPE_IDENTITY_STORAGE \
    (ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT \
        ? ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT : 1u)
#define ALPHA_KNOWN_TYPE_IDENTITY_STORAGE \
    (ALPHA_KNOWN_TYPE_IDENTITY_COUNT \
        ? ALPHA_KNOWN_TYPE_IDENTITY_COUNT : 1u)

typedef struct alpha_candidate {{
    uintptr_t metadata;
    uintptr_t pointer;
    uint32_t source_index;
}} alpha_candidate;

typedef struct alpha_type_identity_candidate {{
    uintptr_t metadata;
    uintptr_t pointer;
    uint32_t source_index;
    uintptr_t owner_descriptor;
}} alpha_type_identity_candidate;

typedef struct alpha_known_type_identity {{
    uintptr_t descriptor;
    const wchar_t *namespace_name;
    const wchar_t *type_name;
}} alpha_known_type_identity;

typedef struct alpha_type_semantic_sample {{
    uintptr_t descriptor;
    uintptr_t expected_base_descriptor;
    uintptr_t expected_declaring_descriptor;
    uint8_t expected_declaring_available;
    uint8_t expected_is_enum;
    uint8_t expected_is_value_type;
    uint8_t expected_is_generic;
    uint8_t expected_is_generic_definition;
}} alpha_type_semantic_sample;

typedef struct alpha_member_handle_sample {{
    uintptr_t metadata;
    uintptr_t owner_descriptor;
}} alpha_member_handle_sample;

typedef uintptr_t (*alpha_instance_noarg)(uintptr_t, uintptr_t);
typedef uint32_t (*alpha_instance_dword)(uintptr_t, uintptr_t);
typedef uint8_t (*alpha_instance_bool)(uintptr_t, uintptr_t);
typedef uintptr_t (*alpha_instance_boolarg)(uintptr_t, uint32_t, uintptr_t);
typedef uintptr_t (*alpha_instance_onearg)(
    uintptr_t, uintptr_t, uintptr_t
);
typedef void (*alpha_instance_twoarg_void)(
    uintptr_t, uintptr_t, uintptr_t, uintptr_t
);
typedef uintptr_t (*alpha_instance_flagsarg)(
    uintptr_t, uint32_t, uintptr_t
);
typedef uintptr_t (*alpha_static_qwordarg)(uintptr_t, uintptr_t);
typedef uintptr_t (*alpha_static_twoarg)(
    uintptr_t, uintptr_t, uintptr_t
);
typedef uintptr_t (*alpha_static_threearg)(
    uintptr_t, uintptr_t, uint32_t, uintptr_t
);
typedef uintptr_t (*alpha_static_onearg)(uintptr_t);

static const char expected_executable_sha256[] =
    "{binding['binary']['sha256']}";
static const DWORD expected_process_id = {binding['process_id']}u;
static const uintptr_t expected_image_base = {binding['image_base']}ull;
static const uint64_t expected_image_bytes = {binding['image_bytes']}ull;
static const char expected_snapshot_sha256[] =
    "{binding['snapshot']['sha256']}";
static const char expected_semantics_sha256[] =
    "{binding['semantics']['sha256']}";
static const uintptr_t event_class = {classes['event']}ull;
static const uintptr_t method_class = {classes['method']}ull;
static const uintptr_t parameter_class = {classes['parameter']}ull;
static const uintptr_t runtime_type_class = {classes['runtime_type']}ull;
static const uintptr_t string_class = {classes['string']}ull;
static const uintptr_t assembly_class = {classes.get('assembly', 0)}ull;
static const uintptr_t field_class = {classes.get('field', 0)}ull;
static const uintptr_t property_class = {classes.get('property', 0)}ull;
static const uintptr_t runtime_type_descriptor = {runtime_type_descriptor}ull;
static const uintptr_t string_descriptor = {string_descriptor}ull;
static const uintptr_t return_managed_type_helper =
    {return_managed_type_helper}ull;
static const uintptr_t return_lazy_node_helper =
    {return_lazy_node_helper}ull;
static const uintptr_t return_type_xor_key = {return_type_xor_key}ull;
static const uint32_t method_name_decode_operation =
    {method_name_decode_operation_code}u;
static const uintptr_t method_name_decode_key =
    {method_name_decode_key}ull;
static const uintptr_t method_name_lazy_initializer =
    {method_name_lazy_initializer}ull;
static const uintptr_t property_handle_owner_addend =
    {property_handle_owner_addend}ull;
static const uintptr_t method_name_metadata = {method_name['metadata']}ull;
static const uintptr_t method_name_pointer = {method_name['pointer']}ull;
static const alpha_candidate bool_candidates[] = {{
{bool_rows}
}};
static const alpha_candidate zero_candidates[] = {{
{zero_rows}
}};
static const alpha_candidate type_from_handle_candidate[] = {{
{type_from_handle_row}
}};
static const alpha_candidate type_collection_candidates[] = {{
{collection_rows}
}};
static const alpha_candidate method_collection_candidate[] = {{
{method_collection_rows}
}};
static const alpha_candidate field_collection_candidate[] = {{
{field_collection_row}
}};
static const alpha_candidate property_collection_candidate[] = {{
{property_collection_row}
}};
static const alpha_candidate method_return_candidate[] = {{
{method_return_row}
}};
static const alpha_candidate method_parameters_candidate[] = {{
{method_parameters_row}
}};
static const alpha_candidate metadata_token_candidate[] = {{
{metadata_token_row}
}};
static const alpha_candidate field_attributes_candidate[] = {{
{field_attributes_row}
}};
static const alpha_candidate parameter_type_candidate[] = {{
{parameter_type_row}
}};
static const alpha_candidate event_handler_candidate[] = {{
{event_handler_row}
}};
static const alpha_type_identity_candidate type_identity_candidates[] = {{
{type_identity_rows}
}};
static const alpha_candidate type_module_candidates[] = {{
{module_rows}
}};
static const alpha_candidate type_declaring_candidates[] = {{
{declaring_rows}
}};
static const alpha_candidate type_base_candidate[] = {{
{extended_single_rows['base_type']}
}};
static const alpha_candidate type_element_candidate[] = {{
{extended_single_rows['element_type']}
}};
static const alpha_candidate type_generic_arguments_candidate[] = {{
{extended_single_rows['generic_arguments']}
}};
static const alpha_candidate type_generic_definition_candidate[] = {{
{extended_single_rows['generic_definition']}
}};
static const alpha_candidate type_interfaces_candidate[] = {{
{extended_single_rows['interfaces']}
}};
static const alpha_candidate type_attributes_candidate[] = {{
{extended_single_rows['attributes']}
}};
static const alpha_candidate type_is_enum_candidate[] = {{
{extended_single_rows['is_enum']}
}};
static const alpha_candidate type_is_value_type_candidate[] = {{
{extended_single_rows['is_value_type']}
}};
static const alpha_candidate type_is_generic_candidate[] = {{
{extended_single_rows['is_generic']}
}};
static const alpha_candidate type_is_generic_definition_candidate[] = {{
{extended_single_rows['is_generic_definition']}
}};
static const alpha_candidate property_from_handle_candidate[] = {{
{remaining_single_rows['property.from_handle']}
}};
static const alpha_candidate field_set_value_candidate[] = {{
{remaining_single_rows['field.set_value']}
}};
static const alpha_candidate field_get_value_candidate[] = {{
{remaining_single_rows['field.get_value']}
}};
static const alpha_candidate field_raw_constant_candidate[] = {{
{remaining_single_rows['field.raw_constant']}
}};
static const alpha_candidate field_from_handle_candidate[] = {{
{remaining_single_rows['field.from_handle']}
}};
static const alpha_candidate method_from_handle_candidate[] = {{
{remaining_single_rows['method.from_handle']}
}};
static const alpha_candidate enum_underlying_candidates[] = {{
{enum_underlying_rows}
}};
static const alpha_type_semantic_sample type_semantic_samples[] = {{
{type_semantic_rows}
}};
static const alpha_known_type_identity known_type_identities[] = {{
{known_type_rows}
}};
static const uintptr_t event_type_descriptors[] = {{
{event_descriptor_rows}
}};
static const uintptr_t field_metadata_domain[] = {{
{field_metadata_rows}
}};
static const uintptr_t property_metadata_domain[] = {{
{property_metadata_rows}
}};
static const alpha_member_handle_sample field_handle_samples[] = {{
{field_handle_sample_rows}
}};
static const alpha_member_handle_sample property_handle_samples[] = {{
{property_handle_sample_rows}
}};
static const wchar_t status_output[] = {status_literal};
static const wchar_t pending_status_output[] = {_wide_literal(_windows_z_path(status_path.with_name(status_path.name + '.pending')))};

static HMODULE self_module;
static HANDLE probe_event;
static UINT probe_message;
static WNDPROC original_window_proc;
static volatile LONG probe_state;
static volatile LONG probe_request, probe_sequence, probe_active;
static DWORD probe_dispatch_failure, probe_dispatch_error;
static volatile LONG probe_stage;
static volatile LONG fresh_factory_stage;
static volatile LONG fresh_factory_type_valid;
static volatile LONG fresh_factory_nonnull_arrays;
static volatile LONG fresh_factory_readable_arrays;
static volatile LONG fresh_factory_max_event_count;
static volatile LONG derived_array_length_qword;
static volatile LONG derived_array_vector_qword;
static uintptr_t parameter_array_class;
static volatile LONG parameter_array_length_qword;
static volatile LONG parameter_array_vector_qword;
static volatile LONG fresh_method_object_count;
static volatile LONG method_return_runtime_type_count;
static volatile LONG method_parameter_array_count;
static volatile LONG method_parameter_object_count;
static volatile LONG method_token_table_match_count;
static volatile LONG method_token_distinct_count;
static volatile LONG event_handler_relation_count;
static volatile LONG event_handler_match_count;
static volatile LONG fresh_type_identity_count;
static volatile LONG type_string_return_candidate_count;
static volatile LONG type_filter_runtime_sentinel_count;
static volatile LONG type_filter_reflected_method_count;
static volatile LONG type_filter_string_return_method_count;
static volatile LONG type_filter_metadata_match_count;
static volatile LONG type_filter_method_array_lengths[2];
static volatile LONG type_filter_method_class_counts[2];
static volatile LONG type_filter_method_name_counts[2];
static volatile LONG type_filter_method_token_counts[2];
static volatile LONG type_filter_method_identity_counts[2];
static volatile LONG type_filter_observed_tokens[8];
static volatile LONG type_name_match_count;
static volatile LONG type_namespace_match_count;
static volatile LONG type_name_selected = -1;
static volatile LONG type_namespace_selected = -1;
static volatile LONG type_extended_sample_count;
static volatile LONG type_extended_base_match_count;
static volatile LONG type_extended_element_match_count;
static volatile LONG type_extended_attribute_stable_count;
static volatile LONG type_extended_enum_match_count;
static volatile LONG type_extended_value_match_count;
static volatile LONG type_extended_generic_match_count;
static volatile LONG type_extended_generic_definition_match_count;
static volatile LONG type_extended_generic_argument_match_count;
static volatile LONG type_extended_interface_shape_count;
static volatile LONG type_extended_generic_definition_result_count;
static volatile LONG type_extended_generic_definition_expected_count;
static volatile LONG type_extended_attributes_selected = -1;
static volatile LONG type_extended_enum_selected = -1;
static volatile LONG type_extended_value_selected = -1;
static volatile LONG type_extended_module_selected = -1;
static volatile LONG type_extended_module_match_count;
static volatile LONG type_extended_declaring_selected = -1;
static volatile LONG type_extended_declaring_equivalent_count;
static volatile LONG type_extended_declaring_expected_count;
static volatile LONG type_extended_declaring_match_count;
static volatile LONG remaining_field_object_count;
static volatile LONG remaining_property_object_count;
static volatile LONG remaining_field_handle_match_count;
static volatile LONG remaining_property_handle_match_count;
static volatile LONG remaining_method_handle_match_count;
static volatile LONG remaining_field_handle_expected_count;
static volatile LONG remaining_property_handle_expected_count;
static volatile LONG remaining_field_handle_token_match_count;
static volatile LONG remaining_property_handle_token_match_count;
static volatile LONG remaining_property_handle_derived_count;
static volatile LONG remaining_property_handle_qword_selected = -1;
static volatile LONG remaining_field_static_count;
static volatile LONG remaining_field_literal_count;
static volatile LONG remaining_field_mutable_static_count;
static volatile LONG remaining_field_get_value_count;
static volatile LONG remaining_field_raw_constant_count;
static volatile LONG remaining_field_raw_constant_match_count;
static volatile LONG remaining_field_set_same_count;
static volatile LONG remaining_enum_sample_count;
static volatile LONG remaining_enum_candidate_matches[3];
static volatile LONG remaining_enum_selected = -1;

static int readable(uintptr_t value, SIZE_T bytes) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !bytes || value + bytes < value ||
        !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD)
        return 0;
    DWORD protect = region.Protect & 0xffu;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    return protect && protect != PAGE_NOACCESS && end >= value &&
        value + bytes <= end;
}}

static int object_class(uintptr_t object, uintptr_t expected) {{
    uintptr_t observed = 0;
    if (!readable(object, sizeof(observed))) return 0;
    memcpy(&observed, (const void *)object, sizeof(observed));
    return observed == expected;
}}

static int runtime_type_matches_descriptor(
    uintptr_t object,
    uintptr_t descriptor,
    int handle_qword
) {{
    if (!descriptor) return !object;
    if (!object_class(object, runtime_type_class) || handle_qword < 0)
        return 0;
    uintptr_t handle = 0;
    uintptr_t handle_address = object +
        (uintptr_t)handle_qword * sizeof(uintptr_t);
    if (handle_address < object ||
        !readable(handle_address, sizeof(handle))) return 0;
    memcpy(&handle, (const void *)handle_address, sizeof(handle));
    unsigned char observed[16] = {{0}};
    unsigned char expected[16] = {{0}};
    if (!readable(handle, sizeof(observed)) ||
        !readable(descriptor, sizeof(expected))) return 0;
    memcpy(observed, (const void *)handle, sizeof(observed));
    memcpy(expected, (const void *)descriptor, sizeof(expected));
    return !memcmp(observed, expected, sizeof(observed));
}}

static uintptr_t member_metadata_handle(
    uintptr_t object,
    const uintptr_t *domain,
    uint32_t domain_count
) {{
    uintptr_t selected = 0;
    uint32_t matches = 0;
    if (!object || !domain || !domain_count) return 0;
    for (uint32_t qword = 2u; qword < 16u; qword++) {{
        uintptr_t value = 0;
        uintptr_t address = object + (uintptr_t)qword * sizeof(uintptr_t);
        if (address < object || !readable(address, sizeof(value))) return 0;
        memcpy(&value, (const void *)address, sizeof(value));
        for (uint32_t index = 0; index < domain_count; index++) {{
            if (value != domain[index]) continue;
            selected = value;
            matches++;
        }}
    }}
    return matches == 1u ? selected : 0;
}}

static int plausible_native_class(uintptr_t value) {{
    uintptr_t name_address = value +
        (uintptr_t)ALPHA_CLASS_NAME_POINTER_QWORD * sizeof(uintptr_t);
    uintptr_t name = 0;
    if (!value || name_address < value ||
        !readable(name_address, sizeof(name))) return 0;
    memcpy(&name, (const void *)name_address, sizeof(name));
    if (!name || !readable(name, 1u)) return 0;
    for (uint32_t index = 0; index <= 4096u; index++) {{
        if (!readable(name + index, 1u)) return 0;
        unsigned char observed = 0;
        memcpy(&observed, (const void *)(name + index), 1u);
        if (!observed) return index > 0u;
    }}
    return 0;
}}

static uintptr_t property_runtime_handle(
    uintptr_t object,
    uint32_t *selected_qword
) {{
    if (selected_qword) *selected_qword = 0;
    uintptr_t selected = 0;
    uint32_t matches = 0;
    if (!object || !ALPHA_PROPERTY_HANDLE_OWNER_BYTE_OFFSET) return 0;
    for (uint32_t handle_qword = 2u; handle_qword < 16u; handle_qword++) {{
        uintptr_t handle = 0;
        uintptr_t handle_address = object +
            (uintptr_t)handle_qword * sizeof(uintptr_t);
        if (handle_address < object ||
            !readable(handle_address, sizeof(handle))) return 0;
        memcpy(&handle, (const void *)handle_address, sizeof(handle));
        uintptr_t encoded_address = handle +
            ALPHA_PROPERTY_HANDLE_OWNER_BYTE_OFFSET;
        uintptr_t encoded = 0;
        if (!handle || encoded_address < handle ||
            !readable(encoded_address, sizeof(encoded))) continue;
        memcpy(&encoded, (const void *)encoded_address, sizeof(encoded));
        uintptr_t decoded = 0;
        if (ALPHA_PROPERTY_HANDLE_OWNER_CODEC == 1u)
            decoded = encoded + property_handle_owner_addend;
        else if (ALPHA_PROPERTY_HANDLE_OWNER_CODEC == 2u)
            decoded = encoded ^ property_handle_owner_addend;
        else
            continue;
        if (!readable(decoded, sizeof(uintptr_t))) continue;
        uint32_t owner_matches = 0;
        for (uint32_t owner_qword = 2u; owner_qword < 16u; owner_qword++) {{
            uintptr_t owner = 0;
            uintptr_t owner_address = object +
                (uintptr_t)owner_qword * sizeof(uintptr_t);
            if (owner_address < object ||
                !readable(owner_address, sizeof(owner))) return 0;
            memcpy(&owner, (const void *)owner_address, sizeof(owner));
            if (owner == decoded) owner_matches++;
        }}
        if (owner_matches != 1u && !plausible_native_class(decoded))
            continue;
        selected = handle;
        if (selected_qword) *selected_qword = handle_qword;
        matches++;
    }}
    if (matches != 1u && selected_qword) *selected_qword = 0;
    return matches == 1u ? selected : 0;
}}

static int typed_array_objects(
    uintptr_t array_object,
    uintptr_t expected_class,
    uintptr_t output[ALPHA_EVENT_OBJECT_LIMIT],
    uint32_t *output_count,
    int allow_empty
) {{
    if (output_count) *output_count = 0;
    if (!array_object || !readable(array_object, 8u * sizeof(uintptr_t)))
        return 0;
    for (uint32_t length_qword = 1; length_qword < 8; length_qword++) {{
        uintptr_t length = 0;
        memcpy(&length, (const void *)(array_object +
            (uintptr_t)length_qword * sizeof(uintptr_t)), sizeof(length));
        if (length > 4096u || (!length && !allow_empty)) continue;
        for (uint32_t vector_qword = length_qword + 1;
             vector_qword < 10; vector_qword++) {{
            uintptr_t vector = array_object +
                (uintptr_t)vector_qword * sizeof(uintptr_t);
            uint32_t take = length > ALPHA_EVENT_OBJECT_LIMIT
                ? ALPHA_EVENT_OBJECT_LIMIT : (uint32_t)length;
            if (take && !readable(vector, take * sizeof(uintptr_t))) continue;
            uint32_t valid = 0;
            for (; valid < take; valid++) {{
                uintptr_t element = 0;
                memcpy(&element, (const void *)(vector +
                    (uintptr_t)valid * sizeof(uintptr_t)), sizeof(element));
                if (!object_class(element, expected_class)) break;
                output[valid] = element;
            }}
            if (valid == take) {{
                if (output_count) *output_count = take;
                if (length) {{
                    InterlockedExchange(
                        &derived_array_length_qword, (LONG)length_qword
                    );
                    InterlockedExchange(
                        &derived_array_vector_qword, (LONG)vector_qword
                    );
                }}
                return 1;
            }}
        }}
    }}
    return 0;
}}

static int derived_typed_array_objects(
    uintptr_t array_object,
    uintptr_t expected_class,
    uintptr_t output[ALPHA_EVENT_OBJECT_LIMIT],
    uint32_t *output_count
) {{
    if (output_count) *output_count = 0;
    LONG length_qword = InterlockedCompareExchange(
        &derived_array_length_qword, 0, 0
    );
    LONG vector_qword = InterlockedCompareExchange(
        &derived_array_vector_qword, 0, 0
    );
    if (!array_object || length_qword <= 0 || vector_qword <= length_qword ||
        vector_qword >= 10 || !readable(
            array_object, (SIZE_T)(vector_qword + 1) * sizeof(uintptr_t)
        )) return 0;
    uintptr_t length = 0;
    memcpy(&length, (const void *)(array_object +
        (uintptr_t)length_qword * sizeof(uintptr_t)), sizeof(length));
    if (length > 4096u) return 0;
    uint32_t take = length > ALPHA_EVENT_OBJECT_LIMIT
        ? ALPHA_EVENT_OBJECT_LIMIT : (uint32_t)length;
    uintptr_t vector = array_object +
        (uintptr_t)vector_qword * sizeof(uintptr_t);
    if (take && !readable(vector, take * sizeof(uintptr_t))) return 0;
    for (uint32_t index = 0; index < take; index++) {{
        uintptr_t element = 0;
        memcpy(&element, (const void *)(vector +
            (uintptr_t)index * sizeof(uintptr_t)), sizeof(element));
        if (!object_class(element, expected_class)) return 0;
        output[index] = element;
    }}
    if (output_count) *output_count = take;
    return 1;
}}

static int parameter_array_objects(
    uintptr_t array_object,
    uintptr_t output[ALPHA_EVENT_OBJECT_LIMIT],
    uint32_t *output_count
) {{
    if (output_count) *output_count = 0;
    LONG length_qword = InterlockedCompareExchange(
        &parameter_array_length_qword, 0, 0
    );
    LONG vector_qword = InterlockedCompareExchange(
        &parameter_array_vector_qword, 0, 0
    );
    if (!parameter_array_class || !array_object ||
        length_qword <= 0 || vector_qword <= length_qword ||
        vector_qword >= 10 || !readable(
            array_object, (SIZE_T)(vector_qword + 1) * sizeof(uintptr_t)
        )) return 0;
    uintptr_t observed_class = 0;
    memcpy(&observed_class, (const void *)array_object,
        sizeof(observed_class));
    uintptr_t length = 0;
    memcpy(&length, (const void *)(array_object +
        (uintptr_t)length_qword * sizeof(uintptr_t)), sizeof(length));
    if (length > 4096u ||
        (length && observed_class != parameter_array_class) ||
        (!length && !readable(observed_class, 2u * sizeof(uintptr_t))))
        return 0;
    uint32_t take = length > ALPHA_EVENT_OBJECT_LIMIT
        ? ALPHA_EVENT_OBJECT_LIMIT : (uint32_t)length;
    uintptr_t vector = array_object +
        (uintptr_t)vector_qword * sizeof(uintptr_t);
    if (take && !readable(vector, take * sizeof(uintptr_t))) return 0;
    for (uint32_t index = 0; index < take; index++) {{
        uintptr_t element = 0;
        memcpy(&element, (const void *)(vector +
            (uintptr_t)index * sizeof(uintptr_t)), sizeof(element));
        if (!object_class(element, parameter_class)) return 0;
        output[index] = element;
    }}
    if (output_count) *output_count = take;
    return 1;
}}

static uint32_t create_fresh_member_objects(
    const alpha_candidate *collection,
    uintptr_t expected_class,
    uintptr_t *output,
    uintptr_t *owner_descriptors,
    int event_diagnostics,
    uint32_t output_capacity
) {{
    if (!collection || !collection->pointer || !collection->metadata ||
        !output || !output_capacity ||
        !ALPHA_EVENT_TYPE_DESCRIPTOR_COUNT ||
        !type_from_handle_candidate[0].pointer ||
        !type_from_handle_candidate[0].metadata)
        return 0;
    alpha_static_qwordarg from_handle =
        (alpha_static_qwordarg)type_from_handle_candidate[0].pointer;
    alpha_instance_flagsarg collect =
        (alpha_instance_flagsarg)collection->pointer;
    uint32_t output_total = 0;
    for (uint32_t type_index = 0;
         type_index < ALPHA_EVENT_TYPE_DESCRIPTOR_COUNT &&
         output_total < output_capacity; type_index++) {{
        uintptr_t type_object = from_handle(
            event_type_descriptors[type_index],
            type_from_handle_candidate[0].metadata
        );
        if (!object_class(type_object, runtime_type_class)) continue;
        if (event_diagnostics)
            InterlockedExchange(&fresh_factory_type_valid, 1);
        uintptr_t array_object = collect(
            type_object, ALPHA_MEMBER_BINDING_FLAGS,
            collection->metadata
        );
        if (event_diagnostics) {{
            if (array_object)
                InterlockedIncrement(&fresh_factory_nonnull_arrays);
            if (readable(array_object, 8u * sizeof(uintptr_t)))
                InterlockedIncrement(&fresh_factory_readable_arrays);
        }}
        uintptr_t observed[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
        uint32_t count = 0;
        if (!typed_array_objects(
                array_object, expected_class, observed, &count, 0
            )) continue;
        uint32_t available = output_capacity - output_total;
        if (count > available) count = available;
        memcpy(output + output_total, observed,
            (SIZE_T)count * sizeof(uintptr_t));
        if (owner_descriptors)
            for (uint32_t index = 0; index < count; index++)
                owner_descriptors[output_total + index] =
                    event_type_descriptors[type_index];
        output_total += count;
    }}
    if (event_diagnostics) {{
        LONG observed = (LONG)output_total;
        LONG previous = InterlockedCompareExchange(
            &fresh_factory_max_event_count, 0, 0
        );
        while (observed > previous) {{
            LONG raced = InterlockedCompareExchange(
                &fresh_factory_max_event_count, observed, previous
            );
            if (raced == previous) break;
            previous = raced;
        }}
        InterlockedExchange(
            &fresh_factory_stage, output_total >= 8 ? 60 : 30
        );
    }}
    return output_total;
}}

static uint32_t create_fresh_event_objects(
    uintptr_t output[ALPHA_EVENT_OBJECT_LIMIT]
) {{
    InterlockedExchange(&probe_stage, 10);
    uint32_t count = ALPHA_TYPE_COLLECTION_CANDIDATE_COUNT
        ? create_fresh_member_objects(
            &type_collection_candidates[0], event_class, output, NULL, 1,
            ALPHA_EVENT_OBJECT_LIMIT
        ) : 0;
    InterlockedExchange(&probe_stage, count >= 8 ? 30 : 29);
    return count;
}}

static int managed_prefix(uintptr_t object, const wchar_t *prefix) {{
    int32_t length = 0;
    SIZE_T prefix_length = wcslen(prefix);
    if (!object_class(object, string_class) ||
        !readable(object + 16u, sizeof(length))) return 0;
    memcpy(&length, (const void *)(object + 16u), sizeof(length));
    if (length < 0 || (SIZE_T)length < prefix_length ||
        !readable(object + 20u, prefix_length * sizeof(wchar_t))) return 0;
    return !memcmp(
        (const void *)(object + 20u), prefix,
        prefix_length * sizeof(wchar_t)
    );
}}

static int managed_equals(uintptr_t object, const wchar_t *expected) {{
    int32_t length = 0;
    SIZE_T expected_length = wcslen(expected);
    if (!object_class(object, string_class) || expected_length > INT32_MAX ||
        !readable(object + 16u, sizeof(length))) return 0;
    memcpy(&length, (const void *)(object + 16u), sizeof(length));
    if (length < 0 || (SIZE_T)length != expected_length ||
        (expected_length && !readable(
            object + 20u, expected_length * sizeof(wchar_t)
        ))) return 0;
    return !expected_length || !memcmp(
        (const void *)(object + 20u), expected,
        expected_length * sizeof(wchar_t)
    );
}}

static int managed_value_equal(uintptr_t left, uintptr_t right) {{
    if (left == right) return 1;
    if (!left || !right ||
        !readable(left, 2u * sizeof(uintptr_t)) ||
        !readable(right, 2u * sizeof(uintptr_t))) return 0;
    uintptr_t left_class = 0, right_class = 0;
    memcpy(&left_class, (const void *)left, sizeof(left_class));
    memcpy(&right_class, (const void *)right, sizeof(right_class));
    if (!left_class || left_class != right_class) return 0;
    if (left_class == string_class) {{
        int32_t left_length = 0, right_length = 0;
        if (!readable(left + 16u, sizeof(left_length)) ||
            !readable(right + 16u, sizeof(right_length))) return 0;
        memcpy(&left_length, (const void *)(left + 16u),
            sizeof(left_length));
        memcpy(&right_length, (const void *)(right + 16u),
            sizeof(right_length));
        if (left_length < 0 || left_length != right_length ||
            left_length > 4096) return 0;
        SIZE_T bytes = (SIZE_T)left_length * sizeof(wchar_t);
        return !bytes ||
            (readable(left + 20u, bytes) &&
             readable(right + 20u, bytes) &&
             !memcmp((const void *)(left + 20u),
                     (const void *)(right + 20u), bytes));
    }}
    unsigned char left_payload[16] = {{0}};
    unsigned char right_payload[16] = {{0}};
    if (!readable(left + 16u, sizeof(left_payload)) ||
        !readable(right + 16u, sizeof(right_payload))) return 0;
    memcpy(left_payload, (const void *)(left + 16u), sizeof(left_payload));
    memcpy(right_payload, (const void *)(right + 16u),
        sizeof(right_payload));
    return !memcmp(left_payload, right_payload, sizeof(left_payload));
}}

static uintptr_t current_native_method_name(uintptr_t metadata) {{
    if (!metadata || !method_name_decode_operation ||
        !method_name_decode_key ||
        !method_name_lazy_initializer) return 0;
    uintptr_t node = 0, encoded = 0, value = 0;
    uintptr_t node_address = metadata +
        (uintptr_t)ALPHA_METHOD_NAME_NODE_QWORD * sizeof(uintptr_t);
    if (node_address < metadata ||
        !readable(node_address, sizeof(node))) return 0;
    memcpy(&node, (const void *)node_address, sizeof(node));
    if (node) {{
        uintptr_t encoded_address = node +
            (uintptr_t)ALPHA_METHOD_NAME_ENCODED_QWORD * sizeof(uintptr_t);
        if (encoded_address < node ||
            !readable(encoded_address, sizeof(encoded))) return 0;
        memcpy(&encoded, (const void *)encoded_address, sizeof(encoded));
        switch (method_name_decode_operation) {{
        case {METHOD_NAME_DECODE_OPERATION_CODES['xor']}u:
            value = encoded ^ method_name_decode_key;
            break;
        case {METHOD_NAME_DECODE_OPERATION_CODES['add']}u:
            value = encoded + method_name_decode_key;
            break;
        default:
            return 0;
        }}
    }}
    if (!value) {{
        alpha_static_onearg initialize =
            (alpha_static_onearg)method_name_lazy_initializer;
        value = initialize(metadata);
    }}
    return readable(value, 1u) ? value : 0;
}}

static int managed_equals_native_name(
    uintptr_t managed_name, uintptr_t native_name
) {{
    int32_t length = 0;
    char converted[4096];
    if (!object_class(managed_name, string_class) || !native_name ||
        !readable(managed_name + 16u, sizeof(length))) return 0;
    memcpy(&length, (const void *)(managed_name + 16u), sizeof(length));
    if (length < 0 || length > 1024 ||
        (length && !readable(
            managed_name + 20u, (SIZE_T)length * sizeof(wchar_t)
        ))) return 0;
    int converted_bytes = WideCharToMultiByte(
        CP_UTF8, WC_ERR_INVALID_CHARS,
        (const wchar_t *)(managed_name + 20u), length,
        converted, (int)sizeof(converted), NULL, NULL
    );
    if ((length && !converted_bytes) ||
        converted_bytes >= (int)sizeof(converted) ||
        !readable(native_name, (SIZE_T)converted_bytes + 1u)) return 0;
    return !memcmp(
            converted, (const void *)native_name, (SIZE_T)converted_bytes
        ) && !*(const unsigned char *)(native_name + converted_bytes);
}}

static uint32_t current_native_method_token_occurrences(
    uintptr_t metadata, uint32_t token
) {{
    uint32_t occurrences = 0;
    uint32_t table = token & 0xff000000u;
    uint32_t row = token & 0x00ffffffu;
    uint32_t limit = ALPHA_METHOD_PARAMETER_COUNT_BYTE_OFFSET;
    if (!metadata || table != 0x06000000u || !row || !limit ||
        limit > ALPHA_METHOD_METADATA_SAMPLE_BYTES ||
        !readable(metadata, limit)) return 0;
    for (uint32_t offset = 0;
         offset + sizeof(uint32_t) <= limit;
         offset += sizeof(uint32_t)) {{
        uint32_t observed = 0;
        memcpy(
            &observed, (const void *)(metadata + offset),
            sizeof(observed)
        );
        if (observed == token || observed + 1u == row)
            occurrences++;
    }}
    return occurrences;
}}

static void digest_hex(const unsigned char digest[32], char output[65]) {{
    static const char alphabet[] = "0123456789abcdef";
    for (int index = 0; index < 32; index++) {{
        output[index * 2] = alphabet[digest[index] >> 4];
        output[index * 2 + 1] = alphabet[digest[index] & 15];
    }}
    output[64] = 0;
}}

static int sha256_file(const wchar_t *path, char output[65]) {{
    HANDLE input = CreateFileW(
        path, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (input == INVALID_HANDLE_VALUE) return 0;
    BCRYPT_ALG_HANDLE algorithm = NULL;
    BCRYPT_HASH_HANDLE hash = NULL;
    DWORD object_size = 0, received = 0;
    unsigned char *object = NULL;
    unsigned char *buffer = NULL;
    unsigned char digest[32];
    int ok = BCryptOpenAlgorithmProvider(
        &algorithm, BCRYPT_SHA256_ALGORITHM, NULL, 0
    ) >= 0 && BCryptGetProperty(
        algorithm, BCRYPT_OBJECT_LENGTH,
        (PUCHAR)&object_size, sizeof(object_size), &received, 0
    ) >= 0 && object_size && received == sizeof(object_size);
    if (ok) object = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, object_size
    );
    if (ok) buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, 1024 * 1024
    );
    if (ok && (!object || !buffer)) ok = 0;
    if (ok && BCryptCreateHash(
            algorithm, &hash, object, object_size, NULL, 0, 0
        ) < 0) ok = 0;
    while (ok) {{
        DWORD count = 0;
        if (!ReadFile(input, buffer, 1024 * 1024, &count, NULL)) {{
            ok = 0;
            break;
        }}
        if (!count) break;
        if (BCryptHashData(hash, buffer, count, 0) < 0) ok = 0;
    }}
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) < 0) ok = 0;
    if (ok) digest_hex(digest, output);
    if (hash) BCryptDestroyHash(hash);
    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);
    if (object) HeapFree(GetProcessHeap(), 0, object);
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    CloseHandle(input);
    return ok;
}}

static int executable_identity(char output[65]) {{
    wchar_t path[32768];
    DWORD length = GetModuleFileNameW(
        NULL, path, (DWORD)(sizeof(path) / sizeof(path[0]))
    );
    return length && length < sizeof(path) / sizeof(path[0]) &&
        sha256_file(path, output);
}}

static int image_identity(void) {{
    unsigned char *image = (unsigned char *)GetModuleHandleW(NULL);
    if (!image || (uintptr_t)image != expected_image_base) return 0;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)image;
    if (dos->e_magic != IMAGE_DOS_SIGNATURE || dos->e_lfanew <= 0 ||
        dos->e_lfanew > 1024 * 1024) return 0;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(image + dos->e_lfanew);
    return nt->Signature == IMAGE_NT_SIGNATURE &&
        nt->OptionalHeader.Magic == IMAGE_NT_OPTIONAL_HDR64_MAGIC &&
        nt->OptionalHeader.SizeOfImage == expected_image_bytes;
}}

static void write_status(
    const wchar_t *destination,
    const char *status,
    const char *observed_hash,
    uint32_t live_objects,
    const uint64_t zero_string[3],
    const uint64_t zero_type[3],
    const uint64_t zero_other[3],
    const uint64_t bool_null[3],
    const uint64_t bool_add[3],
    const uint64_t bool_remove[3],
    const uint64_t bool_raise[3],
    const uint64_t bool_other[3],
    int name_selected,
    int add_selected,
    int remove_selected,
    int raise_selected
) {{
    FILE *output = _wfopen(destination, L"wb");
    if (!output) return;
    fprintf(output,
        "{{\n"
        "  \"schema\": \"{RUNTIME_REFLECTION_BEHAVIOR_STATUS_SCHEMA}\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"expected_snapshot_sha256\": \"%s\",\n"
        "  \"expected_semantics_sha256\": \"%s\",\n"
        "  \"probe_stage\": %ld,\n"
        "  \"fresh_factory_stage\": %ld,\n"
        "  \"fresh_factory_type_valid\": %s,\n"
        "  \"fresh_factory_nonnull_array_count\": %ld,\n"
        "  \"fresh_factory_readable_array_count\": %ld,\n"
        "  \"fresh_factory_max_event_count\": %ld,\n"
        "  \"live_event_object_count\": %u,\n"
        "  \"fresh_method_object_count\": %ld,\n"
        "  \"method_return_runtime_type_count\": %ld,\n"
        "  \"method_parameter_array_count\": %ld,\n"
        "  \"method_parameter_object_count\": %ld,\n"
        "  \"method_token_table_match_count\": %ld,\n"
        "  \"method_token_distinct_count\": %ld,\n"
        "  \"event_handler_relation_count\": %ld,\n"
        "  \"event_handler_match_count\": %ld,\n"
        "  \"fresh_type_identity_count\": %ld,\n"
        "  \"type_string_return_candidate_count\": %ld,\n"
        "  \"type_filter_runtime_sentinel_count\": %ld,\n"
        "  \"type_filter_reflected_method_count\": %ld,\n"
        "  \"type_filter_string_return_method_count\": %ld,\n"
        "  \"type_filter_metadata_match_count\": %ld,\n"
        "  \"type_filter_method_array_lengths\": [%ld, %ld],\n"
        "  \"type_filter_method_class_counts\": [%ld, %ld],\n"
        "  \"type_filter_method_name_counts\": [%ld, %ld],\n"
        "  \"type_filter_method_token_counts\": [%ld, %ld],\n"
        "  \"type_filter_method_identity_counts\": [%ld, %ld],\n"
        "  \"type_filter_observed_tokens_owner_only\": "
        "[%lu, %lu, %lu, %lu, %lu, %lu, %lu, %lu],\n"
        "  \"type_name_match_count\": %ld,\n"
        "  \"type_namespace_match_count\": %ld,\n"
        "  \"type_extended_sample_count\": %ld,\n"
        "  \"type_extended_base_match_count\": %ld,\n"
        "  \"type_extended_element_match_count\": %ld,\n"
        "  \"type_extended_attribute_stable_count\": %ld,\n"
        "  \"type_extended_enum_match_count\": %ld,\n"
        "  \"type_extended_value_match_count\": %ld,\n"
        "  \"type_extended_generic_match_count\": %ld,\n"
        "  \"type_extended_generic_definition_match_count\": %ld,\n"
        "  \"type_extended_generic_argument_match_count\": %ld,\n"
        "  \"type_extended_interface_shape_count\": %ld,\n"
        "  \"type_extended_generic_definition_result_count\": %ld,\n"
        "  \"type_extended_generic_definition_expected_count\": %ld,\n"
        "  \"type_extended_attributes_selected\": %ld,\n"
        "  \"type_extended_enum_selected\": %ld,\n"
        "  \"type_extended_value_selected\": %ld,\n"
        "  \"type_extended_module_selected\": %ld,\n"
        "  \"type_extended_module_match_count\": %ld,\n"
        "  \"type_extended_declaring_selected\": %ld,\n"
        "  \"type_extended_declaring_equivalent_count\": %ld,\n"
        "  \"type_extended_declaring_expected_count\": %ld,\n"
        "  \"type_extended_declaring_match_count\": %ld,\n"
        "  \"remaining_field_object_count\": %ld,\n"
        "  \"remaining_property_object_count\": %ld,\n"
        "  \"remaining_field_handle_match_count\": %ld,\n"
        "  \"remaining_property_handle_match_count\": %ld,\n"
        "  \"remaining_method_handle_match_count\": %ld,\n"
        "  \"remaining_field_handle_expected_count\": %ld,\n"
        "  \"remaining_property_handle_expected_count\": %ld,\n"
        "  \"remaining_field_handle_token_match_count\": %ld,\n"
        "  \"remaining_property_handle_token_match_count\": %ld,\n"
        "  \"remaining_property_handle_derived_count\": %ld,\n"
        "  \"remaining_property_handle_qword_selected_owner_only\": %ld,\n"
        "  \"remaining_field_static_count\": %ld,\n"
        "  \"remaining_field_literal_count\": %ld,\n"
        "  \"remaining_field_mutable_static_count\": %ld,\n"
        "  \"remaining_field_get_value_count\": %ld,\n"
        "  \"remaining_field_raw_constant_count\": %ld,\n"
        "  \"remaining_field_raw_constant_match_count\": %ld,\n"
        "  \"remaining_field_set_same_count\": %ld,\n"
        "  \"remaining_enum_sample_count\": %ld,\n"
        "  \"remaining_enum_candidate_matches\": [%ld, %ld, %ld],\n"
        "  \"remaining_enum_selected\": %ld,\n"
        "  \"zero_candidates\": [\n",
        status, (unsigned long)GetCurrentProcessId(),
        (unsigned long)expected_process_id, expected_executable_sha256,
        observed_hash ? observed_hash : "", expected_snapshot_sha256,
        expected_semantics_sha256,
        (long)InterlockedCompareExchange(&probe_stage, 0, 0),
        (long)InterlockedCompareExchange(&fresh_factory_stage, 0, 0),
        InterlockedCompareExchange(&fresh_factory_type_valid, 0, 0)
            ? "true" : "false",
        (long)InterlockedCompareExchange(
            &fresh_factory_nonnull_arrays, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &fresh_factory_readable_arrays, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &fresh_factory_max_event_count, 0, 0
        ), live_objects,
        (long)InterlockedCompareExchange(&fresh_method_object_count, 0, 0),
        (long)InterlockedCompareExchange(
            &method_return_runtime_type_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &method_parameter_array_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &method_parameter_object_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &method_token_table_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &method_token_distinct_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &event_handler_relation_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &event_handler_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &fresh_type_identity_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_string_return_candidate_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_runtime_sentinel_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_reflected_method_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_string_return_method_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_metadata_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_array_lengths[0], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_array_lengths[1], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_class_counts[0], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_class_counts[1], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_name_counts[0], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_name_counts[1], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_token_counts[0], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_token_counts[1], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_identity_counts[0], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_filter_method_identity_counts[1], 0, 0
        ),
        (unsigned long)InterlockedCompareExchange(
            &type_filter_observed_tokens[0], 0, 0
        ),
        (unsigned long)InterlockedCompareExchange(
            &type_filter_observed_tokens[1], 0, 0
        ),
        (unsigned long)InterlockedCompareExchange(
            &type_filter_observed_tokens[2], 0, 0
        ),
        (unsigned long)InterlockedCompareExchange(
            &type_filter_observed_tokens[3], 0, 0
        ),
        (unsigned long)InterlockedCompareExchange(
            &type_filter_observed_tokens[4], 0, 0
        ),
        (unsigned long)InterlockedCompareExchange(
            &type_filter_observed_tokens[5], 0, 0
        ),
        (unsigned long)InterlockedCompareExchange(
            &type_filter_observed_tokens[6], 0, 0
        ),
        (unsigned long)InterlockedCompareExchange(
            &type_filter_observed_tokens[7], 0, 0
        ),
        (long)InterlockedCompareExchange(&type_name_match_count, 0, 0),
        (long)InterlockedCompareExchange(
            &type_namespace_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_sample_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_base_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_element_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_attribute_stable_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_enum_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_value_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_generic_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_generic_definition_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_generic_argument_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_interface_shape_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_generic_definition_result_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_generic_definition_expected_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_attributes_selected, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_enum_selected, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_value_selected, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_module_selected, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_module_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_declaring_selected, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_declaring_equivalent_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_declaring_expected_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &type_extended_declaring_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_object_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_property_object_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_handle_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_property_handle_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_method_handle_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_handle_expected_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_property_handle_expected_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_handle_token_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_property_handle_token_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_property_handle_derived_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_property_handle_qword_selected, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_static_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_literal_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_mutable_static_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_get_value_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_raw_constant_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_raw_constant_match_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_field_set_same_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_enum_sample_count, 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_enum_candidate_matches[0], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_enum_candidate_matches[1], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_enum_candidate_matches[2], 0, 0
        ),
        (long)InterlockedCompareExchange(
            &remaining_enum_selected, 0, 0
        )
    );
    for (uint32_t index = 0; index < 3; index++) fprintf(output,
        "    {{\"source_index_owner_only\": %u, "
        "\"metadata_pointer_owner_only\": %llu, "
        "\"method_pointer_owner_only\": %llu, "
        "\"string_count\": %llu, \"runtime_type_count\": %llu, "
        "\"other_count\": %llu}}%s\n",
        zero_candidates[index].source_index,
        (unsigned long long)zero_candidates[index].metadata,
        (unsigned long long)zero_candidates[index].pointer,
        (unsigned long long)zero_string[index],
        (unsigned long long)zero_type[index],
        (unsigned long long)zero_other[index],
        index == 2 ? "" : ","
    );
    fprintf(output, "  ],\n  \"bool_candidates\": [\n");
    for (uint32_t index = 0; index < 3; index++) fprintf(output,
        "    {{\"source_index_owner_only\": %u, "
        "\"metadata_pointer_owner_only\": %llu, "
        "\"method_pointer_owner_only\": %llu, "
        "\"null_count\": %llu, \"add_count\": %llu, "
        "\"remove_count\": %llu, \"raise_count\": %llu, "
        "\"other_count\": %llu}}%s\n",
        bool_candidates[index].source_index,
        (unsigned long long)bool_candidates[index].metadata,
        (unsigned long long)bool_candidates[index].pointer,
        (unsigned long long)bool_null[index],
        (unsigned long long)bool_add[index],
        (unsigned long long)bool_remove[index],
        (unsigned long long)bool_raise[index],
        (unsigned long long)bool_other[index], index == 2 ? "" : ","
    );
    fprintf(output,
        "  ],\n"
        "  \"selected\": {{\n"
        "    \"event.name\": %d,\n"
        "    \"event.add_method\": %d,\n"
        "    \"event.remove_method\": %d,\n"
        "    \"event.raise_method\": %d\n"
        "  }},\n"
        "  \"type_selected\": {{\n"
        "    \"type.name\": %ld,\n"
        "    \"type.namespace\": %ld\n"
        "  }},\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"current_process_identity_bound\": true,\n"
        "  \"saved_alias_used\": false,\n"
        "  \"fixed_ordinal_used\": false,\n"
        "  \"external_runtime_component_used\": false,\n"
        "  \"dispatch_failure_kind\": %lu,\n"
        "  \"dispatch_win32_error\": %lu\n"
        "}}\n",
        name_selected, add_selected, remove_selected, raise_selected,
        (long)InterlockedCompareExchange(&type_name_selected, 0, 0),
        (long)InterlockedCompareExchange(&type_namespace_selected, 0, 0),
        (unsigned long)probe_dispatch_failure, (unsigned long)probe_dispatch_error
    );
    fflush(output);
    fclose(output);
    _wchmod(destination, 0600);
}}

static int unique_index(const uint64_t counts[3], uint64_t minimum) {{
    int selected = -1;
    for (int index = 0; index < 3; index++) {{
        if (counts[index] < minimum) continue;
        if (selected >= 0) return -1;
        selected = index;
    }}
    return selected;
}}

static int unique_dynamic_index(
    const uint64_t *counts, uint32_t count, uint64_t minimum
) {{
    int selected = -1;
    if (!counts || !count) return -1;
    for (uint32_t index = 0; index < count; index++) {{
        if (counts[index] < minimum) continue;
        if (selected >= 0) return -1;
        selected = (int)index;
    }}
    return selected;
}}

static int run_probe(void) {{
    InterlockedExchange(&probe_stage, 1);
    uint64_t zero_string[3] = {{0}}, zero_type[3] = {{0}};
    uint64_t zero_other[3] = {{0}}, bool_null[3] = {{0}};
    uint64_t bool_add[3] = {{0}}, bool_remove[3] = {{0}};
    uint64_t bool_raise[3] = {{0}}, bool_other[3] = {{0}};
    uintptr_t event_objects[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
    /* All managed objects are freshly rooted by current-runtime arrays. */
    uint32_t discovered_objects = ALPHA_TYPE_COLLECTION_CANDIDATE_COUNT
        ? create_fresh_event_objects(event_objects) : 0;
    InterlockedExchange(&probe_stage, 40);
    uint32_t live_objects = 0;
    alpha_instance_noarg get_name =
        (alpha_instance_noarg)method_name_pointer;
    for (uint32_t object_index = 0;
         object_index < discovered_objects; object_index++) {{
        uintptr_t event_object = event_objects[object_index];
        if (!object_class(event_object, event_class)) continue;
        live_objects++;
        for (uint32_t index = 0; index < 3; index++) {{
            alpha_instance_noarg invoke =
                (alpha_instance_noarg)zero_candidates[index].pointer;
            uintptr_t value = invoke(
                event_object, zero_candidates[index].metadata
            );
            if (object_class(value, string_class)) zero_string[index]++;
            else if (object_class(value, runtime_type_class)) zero_type[index]++;
            else zero_other[index]++;
        }}
        for (uint32_t index = 0; index < 3; index++) {{
            alpha_instance_boolarg invoke =
                (alpha_instance_boolarg)bool_candidates[index].pointer;
            uintptr_t method = invoke(
                event_object, 1u, bool_candidates[index].metadata
            );
            if (!method) {{
                bool_null[index]++;
                continue;
            }}
            if (!object_class(method, method_class)) {{
                bool_other[index]++;
                continue;
            }}
            uintptr_t name = get_name(method, method_name_metadata);
            if (managed_prefix(name, L"add_")) bool_add[index]++;
            else if (managed_prefix(name, L"remove_")) bool_remove[index]++;
            else if (managed_prefix(name, L"raise_")) bool_raise[index]++;
            else bool_other[index]++;
        }}
    }}
    InterlockedExchange(&probe_stage, 41);
    int name_selected = unique_index(zero_string, 8);
    int add_selected = unique_index(bool_add, 8);
    int remove_selected = unique_index(bool_remove, 8);
    uint64_t raise_domain[3] = {{0}};
    for (uint32_t index = 0; index < 3; index++)
        raise_domain[index] = bool_null[index] + bool_raise[index];
    int raise_selected = unique_index(raise_domain, 8);
    InterlockedExchange(&probe_stage, 42);
    uint64_t type_name_matches[ALPHA_TYPE_IDENTITY_STORAGE] = {{0}};
    uint64_t type_namespace_matches[ALPHA_TYPE_IDENTITY_STORAGE] = {{0}};
    unsigned char safe_string_candidate[ALPHA_TYPE_IDENTITY_STORAGE] = {{0}};
    uint32_t safe_string_candidates = 0;
    uint32_t string_return_methods = 0, metadata_matches = 0;
    uint32_t fresh_types = 0;
    uint32_t reflected_type_methods = 0;
    int runtime_type_handle_qword = -1;
    uintptr_t known_type_objects[ALPHA_KNOWN_TYPE_IDENTITY_STORAGE] = {{0}};
    if (ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT >= 2u &&
        ALPHA_KNOWN_TYPE_IDENTITY_COUNT >= 8u &&
        ALPHA_METHOD_COLLECTION_CANDIDATE_COUNT &&
        type_from_handle_candidate[0].pointer &&
        type_from_handle_candidate[0].metadata &&
        method_return_candidate[0].pointer &&
        method_return_candidate[0].metadata &&
        metadata_token_candidate[0].pointer &&
        metadata_token_candidate[0].metadata &&
        runtime_type_descriptor && string_descriptor &&
        ALPHA_TYPE_DEFINITION_COUNT) {{
        alpha_static_qwordarg from_handle =
            (alpha_static_qwordarg)type_from_handle_candidate[0].pointer;
        alpha_instance_noarg get_method_return_type =
            (alpha_instance_noarg)method_return_candidate[0].pointer;
        alpha_instance_dword get_identity_method_token =
            (alpha_instance_dword)metadata_token_candidate[0].pointer;
        InterlockedExchange(&probe_stage, 70);
        uintptr_t runtime_type_object = from_handle(
            runtime_type_descriptor, type_from_handle_candidate[0].metadata
        );
        uintptr_t string_type_object = from_handle(
            string_descriptor, type_from_handle_candidate[0].metadata
        );
        uint64_t string_definition_index = UINT64_MAX;
        int string_definition_valid = 0;
        if (object_class(runtime_type_object, runtime_type_class) &&
            object_class(string_type_object, runtime_type_class)) {{
            uint32_t handle_qword_support[
                ALPHA_RUNTIME_TYPE_HANDLE_QWORD_LIMIT
            ] = {{0}};
            for (uint32_t type_index = 0;
                 type_index < ALPHA_KNOWN_TYPE_IDENTITY_COUNT; type_index++) {{
                uintptr_t descriptor =
                    known_type_identities[type_index].descriptor;
                uint64_t expected_descriptor[2] = {{UINT64_MAX, 0}};
                if (!readable(descriptor, sizeof(expected_descriptor)))
                    continue;
                memcpy(
                    expected_descriptor, (const void *)descriptor,
                    sizeof(expected_descriptor)
                );
                if (expected_descriptor[0] >= ALPHA_TYPE_DEFINITION_COUNT)
                    continue;
                uintptr_t type_object = from_handle(
                    descriptor, type_from_handle_candidate[0].metadata
                );
                if (!object_class(type_object, runtime_type_class)) continue;
                known_type_objects[type_index] = type_object;
                fresh_types++;
                for (uint32_t qword = 2u;
                     qword < ALPHA_RUNTIME_TYPE_HANDLE_QWORD_LIMIT; qword++) {{
                    uintptr_t candidate_handle = 0;
                    if (!readable(
                            type_object +
                                (uintptr_t)qword * sizeof(uintptr_t),
                            sizeof(candidate_handle)
                        )) continue;
                    memcpy(
                        &candidate_handle,
                        (const void *)(type_object +
                            (uintptr_t)qword * sizeof(uintptr_t)),
                        sizeof(candidate_handle)
                    );
                    uint64_t observed_descriptor[2] = {{0}};
                    if (!readable(
                            candidate_handle, sizeof(observed_descriptor)
                        )) continue;
                    memcpy(
                        observed_descriptor, (const void *)candidate_handle,
                        sizeof(observed_descriptor)
                    );
                    if (!memcmp(
                            observed_descriptor, expected_descriptor,
                            sizeof(observed_descriptor)
                        )) handle_qword_support[qword]++;
                }}
            }}
            if (fresh_types == ALPHA_KNOWN_TYPE_IDENTITY_COUNT) {{
                for (uint32_t qword = 2u;
                     qword < ALPHA_RUNTIME_TYPE_HANDLE_QWORD_LIMIT; qword++) {{
                    if (handle_qword_support[qword] != fresh_types) continue;
                    if (runtime_type_handle_qword >= 0) {{
                        runtime_type_handle_qword = -2;
                        break;
                    }}
                    runtime_type_handle_qword = (int)qword;
                }}
            }}
#if ALPHA_KNOWN_TYPE_IDENTITY_COUNT > 0
            if (string_descriptor && readable(string_descriptor, sizeof(string_definition_index)))
                memcpy(
                    &string_definition_index,
                    (const void *)string_descriptor,
                    sizeof(string_definition_index)
                );
#endif
            string_definition_valid =
                string_definition_index < ALPHA_TYPE_DEFINITION_COUNT;
            if (runtime_type_handle_qword >= 0 && string_definition_valid)
                InterlockedExchange(
                    &type_filter_runtime_sentinel_count, (LONG)fresh_types
                );
            int method_collection_selected = -1;
            for (uint32_t collection_index = 0;
                 runtime_type_handle_qword >= 0 && string_definition_valid &&
                 collection_index < ALPHA_METHOD_COLLECTION_CANDIDATE_COUNT;
                 collection_index++) {{
                alpha_instance_flagsarg collect_methods =
                    (alpha_instance_flagsarg)
                        method_collection_candidate[collection_index].pointer;
                if (!collect_methods ||
                    !method_collection_candidate[collection_index].metadata)
                    continue;
                uintptr_t method_array = collect_methods(
                    runtime_type_object,
                    ALPHA_TYPE_IDENTITY_METHOD_BINDING_FLAGS,
                    method_collection_candidate[collection_index].metadata
                );
                LONG length_qword = InterlockedCompareExchange(
                    &derived_array_length_qword, 0, 0
                );
                LONG vector_qword = InterlockedCompareExchange(
                    &derived_array_vector_qword, 0, 0
                );
                if (!method_array || length_qword <= 0 ||
                    vector_qword <= length_qword || vector_qword >= 10 ||
                    !readable(
                        method_array,
                        (SIZE_T)(vector_qword + 1) * sizeof(uintptr_t)
                    )) continue;
                uintptr_t method_count = 0;
                memcpy(
                    &method_count,
                    (const void *)(method_array +
                        (uintptr_t)length_qword * sizeof(uintptr_t)),
                    sizeof(method_count)
                );
                uintptr_t method_vector = method_array +
                    (uintptr_t)vector_qword * sizeof(uintptr_t);
                if (!method_count || method_count > 4096u ||
                    method_count > SIZE_MAX / sizeof(uintptr_t) ||
                    !readable(
                        method_vector,
                        (SIZE_T)method_count * sizeof(uintptr_t)
                    )) continue;
                if (collection_index < 2u)
                    InterlockedExchange(
                        &type_filter_method_array_lengths[collection_index],
                        (LONG)method_count
                    );
                unsigned char candidate_seen[
                    ALPHA_TYPE_IDENTITY_STORAGE
                ] = {{0}};
                unsigned char candidate_string[
                    ALPHA_TYPE_IDENTITY_STORAGE
                ] = {{0}};
                uint32_t candidate_reflected = 0;
                uint32_t candidate_metadata_matches = 0;
                uint32_t candidate_string_returns = 0;
                uint32_t candidate_method_classes = 0;
                uint32_t candidate_name_methods = 0;
                uint32_t candidate_token_methods = 0;
                int method_array_valid = 1;
                for (uintptr_t method_index = 0;
                     method_index < method_count; method_index++) {{
                    uintptr_t method_object = 0;
                    memcpy(
                        &method_object,
                        (const void *)(method_vector +
                            method_index * sizeof(uintptr_t)),
                        sizeof(method_object)
                    );
                    if (!object_class(method_object, method_class)) continue;
                    candidate_method_classes++;
                    int matched_candidate = -1;
                    uintptr_t managed_method_name = get_name(
                        method_object, method_name_metadata
                    );
                    uint32_t managed_method_token =
                        get_identity_method_token(
                            method_object,
                            metadata_token_candidate[0].metadata
                        );
                    uintptr_t reflected_metadata = 0;
                    uintptr_t reflected_metadata_address = method_object +
                        ALPHA_METHOD_OBJECT_METADATA_BYTE_OFFSET;
                    if (reflected_metadata_address < method_object ||
                        !readable(
                            reflected_metadata_address,
                            sizeof(reflected_metadata)
                        )) continue;
                    memcpy(
                        &reflected_metadata,
                        (const void *)reflected_metadata_address,
                        sizeof(reflected_metadata)
                    );
                    if (!reflected_metadata) continue;
                    if (!collection_index && method_index < 8u)
                        InterlockedExchange(
                            &type_filter_observed_tokens[method_index],
                            (LONG)managed_method_token
                        );
                    if ((managed_method_token & 0xff000000u) !=
                            0x06000000u ||
                        !(managed_method_token & 0x00ffffffu))
                        continue;
                    uint32_t current_name_matches = 0;
                    uint32_t current_token_matches = 0;
                    for (uint32_t candidate = 0;
                         candidate < ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT;
                         candidate++) {{
                        uintptr_t native_method_name =
                            current_native_method_name(
                                type_identity_candidates[candidate].metadata
                            );
                        if (managed_equals_native_name(
                                managed_method_name, native_method_name
                            )) current_name_matches++;
                        if (current_native_method_token_occurrences(
                                type_identity_candidates[candidate].metadata,
                                managed_method_token
                            ) == 1u) current_token_matches++;
                        if (reflected_metadata !=
                            type_identity_candidates[candidate].metadata)
                            continue;
                        if (matched_candidate >= 0 &&
                            matched_candidate != (int)candidate) {{
                            matched_candidate = -2;
                            break;
                        }}
                        matched_candidate = (int)candidate;
                    }}
                    if (current_name_matches) candidate_name_methods++;
                    if (current_token_matches) candidate_token_methods++;
                    if (matched_candidate < 0) continue;
                    if (candidate_seen[matched_candidate]) continue;
                    candidate_seen[matched_candidate] = 1;
                    candidate_reflected++;
                    uintptr_t return_type = get_method_return_type(
                        method_object, method_return_candidate[0].metadata
                    );
                    if (!object_class(return_type, runtime_type_class))
                        continue;
                    uintptr_t return_handle = 0;
                    if (!readable(
                            return_type +
                                (uintptr_t)runtime_type_handle_qword *
                                    sizeof(uintptr_t),
                            sizeof(return_handle)
                        )) continue;
                    memcpy(
                        &return_handle,
                        (const void *)(return_type +
                            (uintptr_t)runtime_type_handle_qword *
                                sizeof(uintptr_t)),
                        sizeof(return_handle)
                    );
                    uint64_t return_definition_index = UINT64_MAX;
                    if (!readable(
                            return_handle, sizeof(return_definition_index)
                        )) continue;
                    memcpy(
                        &return_definition_index,
                        (const void *)return_handle,
                        sizeof(return_definition_index)
                    );
                    if (return_definition_index >=
                        ALPHA_TYPE_DEFINITION_COUNT) continue;
                    candidate_metadata_matches++;
                    if (return_definition_index != string_definition_index)
                        continue;
                    candidate_string[matched_candidate] = 1;
                    candidate_string_returns++;
                }}
                if (collection_index < 2u) {{
                    InterlockedExchange(
                        &type_filter_method_class_counts[collection_index],
                        (LONG)candidate_method_classes
                    );
                    InterlockedExchange(
                        &type_filter_method_name_counts[collection_index],
                        (LONG)candidate_name_methods
                    );
                    InterlockedExchange(
                        &type_filter_method_token_counts[collection_index],
                        (LONG)candidate_token_methods
                    );
                    InterlockedExchange(
                        &type_filter_method_identity_counts[collection_index],
                        (LONG)candidate_reflected
                    );
                }}
                if (!method_array_valid || candidate_reflected < 2u)
                    continue;
                if (method_collection_selected >= 0) {{
                    method_collection_selected = -2;
                    reflected_type_methods = 0;
                    metadata_matches = 0;
                    string_return_methods = 0;
                    safe_string_candidates = 0;
                    memset(
                        safe_string_candidate, 0,
                        sizeof(safe_string_candidate)
                    );
                    break;
                }}
                method_collection_selected = (int)collection_index;
                reflected_type_methods = candidate_reflected;
                metadata_matches = candidate_metadata_matches;
                string_return_methods = candidate_string_returns;
                safe_string_candidates = candidate_string_returns;
                memcpy(
                    safe_string_candidate, candidate_string,
                    sizeof(safe_string_candidate)
                );
            }}
        }}
        alpha_static_threearg identity_method_from_handle =
            (alpha_static_threearg)
                method_from_handle_candidate[0].pointer;
        if (runtime_type_handle_qword >= 0 && string_definition_valid &&
            identity_method_from_handle &&
            method_from_handle_candidate[0].metadata) {{
            unsigned char direct_string_candidate[
                ALPHA_TYPE_IDENTITY_STORAGE
            ] = {{0}};
            uint32_t direct_reflected = 0;
            uint32_t direct_string_returns = 0;
            for (uint32_t candidate = 0;
                 candidate < ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT;
                 candidate++) {{
                uintptr_t candidate_metadata =
                    type_identity_candidates[candidate].metadata;
                uintptr_t candidate_owner =
                    type_identity_candidates[candidate].owner_descriptor;
                if (!candidate_metadata || !candidate_owner) continue;
                uintptr_t method_object = identity_method_from_handle(
                    candidate_metadata, candidate_owner, 1u,
                    method_from_handle_candidate[0].metadata
                );
                if (!object_class(method_object, method_class)) continue;
                uintptr_t observed_metadata = 0;
                uintptr_t observed_metadata_address = method_object +
                    ALPHA_METHOD_OBJECT_METADATA_BYTE_OFFSET;
                if (observed_metadata_address < method_object ||
                    !readable(
                        observed_metadata_address,
                        sizeof(observed_metadata)
                    )) continue;
                memcpy(
                    &observed_metadata,
                    (const void *)observed_metadata_address,
                    sizeof(observed_metadata)
                );
                if (observed_metadata != candidate_metadata) continue;
                direct_reflected++;
                uintptr_t return_type = get_method_return_type(
                    method_object, method_return_candidate[0].metadata
                );
                if (!object_class(return_type, runtime_type_class)) continue;
                uintptr_t return_handle = 0;
                uintptr_t return_handle_address = return_type +
                    (uintptr_t)runtime_type_handle_qword * sizeof(uintptr_t);
                if (return_handle_address < return_type ||
                    !readable(return_handle_address, sizeof(return_handle)))
                    continue;
                memcpy(
                    &return_handle,
                    (const void *)return_handle_address,
                    sizeof(return_handle)
                );
                uint64_t return_definition_index = UINT64_MAX;
                if (!readable(
                        return_handle, sizeof(return_definition_index)
                    )) continue;
                memcpy(
                    &return_definition_index,
                    (const void *)return_handle,
                    sizeof(return_definition_index)
                );
                if (return_definition_index != string_definition_index)
                    continue;
                direct_string_candidate[candidate] = 1u;
                direct_string_returns++;
            }}
            if (direct_reflected >= 2u && direct_string_returns >= 2u) {{
                reflected_type_methods = direct_reflected;
                metadata_matches = direct_reflected;
                string_return_methods = direct_string_returns;
                safe_string_candidates = direct_string_returns;
                memcpy(
                    safe_string_candidate, direct_string_candidate,
                    sizeof(safe_string_candidate)
                );
            }}
        }}
        if (ALPHA_TYPE_IDENTITY_STRUCTURAL_STRING_SAFE &&
            ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT == 2u) {{
            safe_string_candidate[0] = 1u;
            safe_string_candidate[1] = 1u;
            safe_string_candidates = 2u;
            string_return_methods = 2u;
        }}
        InterlockedExchange(
            &type_filter_reflected_method_count,
            (LONG)reflected_type_methods
        );
        InterlockedExchange(
            &type_filter_string_return_method_count,
            (LONG)string_return_methods
        );
        InterlockedExchange(
            &type_filter_metadata_match_count, (LONG)metadata_matches
        );
        InterlockedExchange(
            &type_string_return_candidate_count,
            (LONG)safe_string_candidates
        );
        InterlockedExchange(&probe_stage, 79);
        for (uint32_t type_index = 0;
             safe_string_candidates >= 2u &&
             type_index < ALPHA_KNOWN_TYPE_IDENTITY_COUNT; type_index++) {{
            uintptr_t type_object = known_type_objects[type_index];
            if (!object_class(type_object, runtime_type_class)) continue;
            for (uint32_t candidate = 0;
                 candidate < ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT;
                 candidate++) {{
                if (!safe_string_candidate[candidate]) continue;
                InterlockedExchange(
                    &probe_stage,
                    (LONG)(80u + type_index)
                );
                alpha_instance_noarg invoke = (alpha_instance_noarg)
                    type_identity_candidates[candidate].pointer;
                uintptr_t value = invoke(
                    type_object,
                    type_identity_candidates[candidate].metadata
                );
                if (managed_equals(
                        value,
                        known_type_identities[type_index].type_name
                    )) type_name_matches[candidate]++;
                if (managed_equals(
                        value,
                        known_type_identities[type_index].namespace_name
                    )) type_namespace_matches[candidate]++;
            }}
        }}
        uint32_t extended_samples = 0;
        uint32_t base_matches = 0, element_matches = 0;
        uint32_t attribute_stable = 0;
        uint32_t enum_matches = 0, value_matches = 0;
        uint32_t generic_matches = 0, generic_definition_matches = 0;
        uint32_t generic_argument_matches = 0, interface_shapes = 0;
        uint32_t generic_definition_results = 0;
        uint32_t generic_definition_expected = 0;
        uint32_t module_nonnull[2] = {{0}};
        uint32_t module_pair_matches = 0;
        uint32_t declaring_matches[2] = {{0}};
        uint32_t declaring_expected = 0;
        uint32_t enum_samples = 0;
        uint64_t enum_candidate_matches[3] = {{0}};
        int current_module_selected = -1;
        int current_declaring_selected = -1;
        uint32_t current_declaring_equivalent = 0;
        /*
         * Build-independent predicate resolution.
         *
         * Older builds shared one native invoker between the boolean
         * reflection predicates and exposed stable prologue bytes, so the
         * plan could hand over a single structural candidate per family.
         * Newer builds keep neither property.  The plan therefore hands over
         * a side-effect-free predicate pool, and the family is decided here
         * by fresh-runtime behavior over the semantic sample domain: exactly
         * one pool entry must match the whole expected vector, otherwise the
         * stage stays fail-closed.
         */
        uint64_t enum_pool_matches[ALPHA_TYPE_IS_ENUM_CANDIDATE_COUNT] =
            {{0}};
        uint64_t value_pool_matches
            [ALPHA_TYPE_IS_VALUE_TYPE_CANDIDATE_COUNT] = {{0}};
        uint64_t attribute_pool_matches
            [ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT] = {{0}};
        uint32_t attribute_pool_wide
            [ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT] = {{0}};
        uint32_t attribute_pool_distinct
            [ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT] = {{0}};
        uint32_t attribute_pool_first
            [ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT] = {{0}};
        uint32_t attribute_pool_observed
            [ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT] = {{0}};
        int current_enum_predicate_selected = -1;
        int current_value_selected = -1;
        int current_attribute_selected = -1;
        if (runtime_type_handle_qword >= 0 &&
            ALPHA_TYPE_SEMANTIC_SAMPLE_COUNT >= 8u &&
            type_from_handle_candidate[0].pointer &&
            type_from_handle_candidate[0].metadata) {{
            for (uint32_t sample_index = 0;
                 sample_index < ALPHA_TYPE_SEMANTIC_SAMPLE_COUNT;
                 sample_index++) {{
                const alpha_type_semantic_sample *sample =
                    &type_semantic_samples[sample_index];
                uintptr_t type_object = from_handle(
                    sample->descriptor,
                    type_from_handle_candidate[0].metadata
                );
                if (!runtime_type_matches_descriptor(
                        type_object, sample->descriptor,
                        runtime_type_handle_qword
                    )) continue;
                extended_samples++;
                for (uint32_t candidate = 0;
                     candidate < ALPHA_TYPE_IS_ENUM_CANDIDATE_COUNT;
                     candidate++) {{
                    if (!type_is_enum_candidate[candidate].pointer ||
                        !type_is_enum_candidate[candidate].metadata)
                        continue;
                    alpha_instance_bool invoke = (alpha_instance_bool)
                        type_is_enum_candidate[candidate].pointer;
                    uint8_t observed = invoke(
                        type_object,
                        type_is_enum_candidate[candidate].metadata
                    );
                    if (observed <= 1u && observed ==
                        (uint8_t)sample->expected_is_enum)
                        enum_pool_matches[candidate]++;
                }}
                for (uint32_t candidate = 0;
                     candidate < ALPHA_TYPE_IS_VALUE_TYPE_CANDIDATE_COUNT;
                     candidate++) {{
                    if (!type_is_value_type_candidate[candidate].pointer ||
                        !type_is_value_type_candidate[candidate].metadata)
                        continue;
                    alpha_instance_bool invoke = (alpha_instance_bool)
                        type_is_value_type_candidate[candidate].pointer;
                    uint8_t observed = invoke(
                        type_object,
                        type_is_value_type_candidate[candidate].metadata
                    );
                    if (observed <= 1u && observed ==
                        (uint8_t)sample->expected_is_value_type)
                        value_pool_matches[candidate]++;
                }}
                for (uint32_t candidate = 0;
                     candidate < ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT;
                     candidate++) {{
                    if (!type_attributes_candidate[candidate].pointer ||
                        !type_attributes_candidate[candidate].metadata)
                        continue;
                    alpha_instance_dword invoke = (alpha_instance_dword)
                        type_attributes_candidate[candidate].pointer;
                    uint32_t first_value = invoke(
                        type_object,
                        type_attributes_candidate[candidate].metadata
                    );
                    uint32_t second_value = invoke(
                        type_object,
                        type_attributes_candidate[candidate].metadata
                    );
                    if (first_value != second_value) continue;
                    if (first_value > 0x00ffffffu) continue;
                    if (first_value > 1u)
                        attribute_pool_wide[candidate] = 1u;
                    if (!attribute_pool_observed[candidate]) {{
                        attribute_pool_first[candidate] = first_value;
                        attribute_pool_observed[candidate] = 1u;
                    }} else if (
                        first_value != attribute_pool_first[candidate]
                    ) {{
                        attribute_pool_distinct[candidate] = 1u;
                    }}
                    attribute_pool_matches[candidate]++;
                }}
            }}
            for (uint32_t candidate = 0;
                 candidate < ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT;
                 candidate++) {{
                if (!attribute_pool_wide[candidate] ||
                    !attribute_pool_distinct[candidate])
                    attribute_pool_matches[candidate] = 0;
            }}
            current_enum_predicate_selected = unique_dynamic_index(
                enum_pool_matches,
                ALPHA_TYPE_IS_ENUM_CANDIDATE_COUNT,
                extended_samples
            );
            current_value_selected = unique_dynamic_index(
                value_pool_matches,
                ALPHA_TYPE_IS_VALUE_TYPE_CANDIDATE_COUNT,
                extended_samples
            );
            current_attribute_selected = unique_dynamic_index(
                attribute_pool_matches,
                ALPHA_TYPE_ATTRIBUTES_CANDIDATE_COUNT,
                extended_samples
            );
        }}
        InterlockedExchange(
            &type_extended_attributes_selected,
            (LONG)current_attribute_selected
        );
        InterlockedExchange(
            &type_extended_enum_selected, (LONG)current_enum_predicate_selected
        );
        InterlockedExchange(
            &type_extended_value_selected, (LONG)current_value_selected
        );
        if (runtime_type_handle_qword >= 0 &&
            ALPHA_TYPE_SEMANTIC_SAMPLE_COUNT >= 8u &&
            ALPHA_TYPE_MODULE_CANDIDATE_COUNT == 2u &&
            ALPHA_TYPE_DECLARING_CANDIDATE_COUNT == 2u &&
            type_base_candidate[0].pointer &&
            type_base_candidate[0].metadata &&
            type_element_candidate[0].pointer &&
            type_element_candidate[0].metadata &&
            type_generic_arguments_candidate[0].pointer &&
            type_generic_arguments_candidate[0].metadata &&
            type_generic_definition_candidate[0].pointer &&
            type_generic_definition_candidate[0].metadata &&
            type_interfaces_candidate[0].pointer &&
            type_interfaces_candidate[0].metadata &&
            current_attribute_selected >= 0 &&
            type_attributes_candidate[current_attribute_selected].pointer &&
            type_attributes_candidate[current_attribute_selected].metadata &&
            current_enum_predicate_selected >= 0 &&
            type_is_enum_candidate[current_enum_predicate_selected].pointer &&
            type_is_enum_candidate[current_enum_predicate_selected].metadata &&
            current_value_selected >= 0 &&
            type_is_value_type_candidate[current_value_selected].pointer &&
            type_is_value_type_candidate[current_value_selected].metadata &&
            type_is_generic_candidate[0].pointer &&
            type_is_generic_candidate[0].metadata &&
            type_is_generic_definition_candidate[0].pointer &&
            type_is_generic_definition_candidate[0].metadata) {{
            alpha_instance_noarg get_base_type =
                (alpha_instance_noarg)type_base_candidate[0].pointer;
            alpha_instance_noarg get_element_type =
                (alpha_instance_noarg)type_element_candidate[0].pointer;
            alpha_instance_noarg get_generic_arguments =
                (alpha_instance_noarg)
                    type_generic_arguments_candidate[0].pointer;
            alpha_instance_noarg get_generic_definition =
                (alpha_instance_noarg)
                    type_generic_definition_candidate[0].pointer;
            alpha_instance_noarg get_interfaces =
                (alpha_instance_noarg)type_interfaces_candidate[0].pointer;
            alpha_instance_dword get_attributes =
                (alpha_instance_dword)
                    type_attributes_candidate[current_attribute_selected].pointer;
            alpha_instance_bool get_is_enum =
                (alpha_instance_bool)
                    type_is_enum_candidate[current_enum_predicate_selected].pointer;
            alpha_instance_bool get_is_value_type =
                (alpha_instance_bool)
                    type_is_value_type_candidate[current_value_selected].pointer;
            alpha_instance_bool get_is_generic =
                (alpha_instance_bool)type_is_generic_candidate[0].pointer;
            alpha_instance_bool get_is_generic_definition =
                (alpha_instance_bool)
                    type_is_generic_definition_candidate[0].pointer;
            for (uint32_t sample_index = 0;
                 sample_index < ALPHA_TYPE_SEMANTIC_SAMPLE_COUNT;
                 sample_index++) {{
                const alpha_type_semantic_sample *sample =
                    &type_semantic_samples[sample_index];
                InterlockedExchange(
                    &probe_stage, (LONG)(2000u + sample_index * 20u)
                );
                uintptr_t type_object = from_handle(
                    sample->descriptor,
                    type_from_handle_candidate[0].metadata
                );
                if (!runtime_type_matches_descriptor(
                        type_object, sample->descriptor,
                        runtime_type_handle_qword
                    )) continue;
                InterlockedExchange(
                    &probe_stage, (LONG)(2001u + sample_index * 20u)
                );
                uintptr_t base_type = get_base_type(
                    type_object, type_base_candidate[0].metadata
                );
                if (runtime_type_matches_descriptor(
                        base_type, sample->expected_base_descriptor,
                        runtime_type_handle_qword
                    )) base_matches++;
                InterlockedExchange(
                    &probe_stage, (LONG)(2002u + sample_index * 20u)
                );
                uintptr_t element_type = get_element_type(
                    type_object, type_element_candidate[0].metadata
                );
                if (!element_type) element_matches++;
                InterlockedExchange(
                    &probe_stage, (LONG)(2003u + sample_index * 20u)
                );
                uint32_t attributes_first = get_attributes(
                    type_object,
                    type_attributes_candidate[current_attribute_selected].metadata
                );
                uint32_t attributes_second = get_attributes(
                    type_object,
                    type_attributes_candidate[current_attribute_selected].metadata
                );
                if (attributes_first == attributes_second)
                    attribute_stable++;
                InterlockedExchange(
                    &probe_stage, (LONG)(2004u + sample_index * 20u)
                );
                uint8_t is_enum = get_is_enum(
                    type_object,
                    type_is_enum_candidate[current_enum_predicate_selected].metadata
                );
                uint8_t is_value_type = get_is_value_type(
                    type_object,
                    type_is_value_type_candidate[current_value_selected].metadata
                );
                uint8_t is_generic = get_is_generic(
                    type_object, type_is_generic_candidate[0].metadata
                );
                uint8_t is_generic_definition = get_is_generic_definition(
                    type_object,
                    type_is_generic_definition_candidate[0].metadata
                );
                if (is_enum <= 1u &&
                    is_enum == sample->expected_is_enum) enum_matches++;
                if (is_value_type <= 1u &&
                    is_value_type == sample->expected_is_value_type)
                    value_matches++;
                if (is_generic <= 1u &&
                    is_generic == sample->expected_is_generic)
                    generic_matches++;
                if (is_generic_definition <= 1u &&
                    is_generic_definition ==
                        sample->expected_is_generic_definition)
                    generic_definition_matches++;
                if (sample->expected_is_enum &&
                    ALPHA_ENUM_UNDERLYING_CANDIDATE_COUNT == 3u) {{
                    enum_samples++;
                    for (uint32_t candidate = 0; candidate < 3u;
                         candidate++) {{
                        alpha_static_qwordarg get_underlying =
                            (alpha_static_qwordarg)
                                enum_underlying_candidates[candidate].pointer;
                        uintptr_t underlying = get_underlying(
                            type_object,
                            enum_underlying_candidates[candidate].metadata
                        );
                        if (!object_class(
                                underlying, runtime_type_class
                            )) continue;
                        uint8_t underlying_is_enum = get_is_enum(
                            underlying,
                            type_is_enum_candidate[current_enum_predicate_selected].metadata
                        );
                        uint8_t underlying_is_value = get_is_value_type(
                            underlying,
                            type_is_value_type_candidate[current_value_selected].metadata
                        );
                        if (!underlying_is_enum &&
                            underlying_is_value == 1u)
                            enum_candidate_matches[candidate]++;
                    }}
                }}
                InterlockedExchange(
                    &probe_stage, (LONG)(2009u + sample_index * 20u)
                );
                uintptr_t interfaces = get_interfaces(
                    type_object, type_interfaces_candidate[0].metadata
                );
                uintptr_t interface_objects[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
                uint32_t interface_count = 0;
                if (typed_array_objects(
                        interfaces, runtime_type_class, interface_objects,
                        &interface_count, 0
                    ) || derived_typed_array_objects(
                        interfaces, runtime_type_class, interface_objects,
                        &interface_count
                    )) interface_shapes++;
                InterlockedExchange(
                    &probe_stage, (LONG)(2008u + sample_index * 20u)
                );
                uintptr_t generic_arguments = get_generic_arguments(
                    type_object,
                    type_generic_arguments_candidate[0].metadata
                );
                uintptr_t argument_objects[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
                uint32_t argument_count = 0;
                if (derived_typed_array_objects(
                        generic_arguments, runtime_type_class,
                        argument_objects, &argument_count
                    ) && ((sample->expected_is_generic && argument_count) ||
                          (!sample->expected_is_generic && !argument_count)))
                    generic_argument_matches++;
                if (is_generic_definition == 1u) {{
                    generic_definition_expected++;
                    InterlockedExchange(
                        &probe_stage, (LONG)(2010u + sample_index * 20u)
                    );
                    uintptr_t definition = get_generic_definition(
                        type_object,
                        type_generic_definition_candidate[0].metadata
                    );
                    if (runtime_type_matches_descriptor(
                            definition, sample->descriptor,
                            runtime_type_handle_qword
                        )) generic_definition_results++;
                }}
                uintptr_t module_results[2] = {{0}};
                if (sample->expected_declaring_available)
                    declaring_expected++;
                for (uint32_t candidate = 0; candidate < 2u; candidate++) {{
                    InterlockedExchange(
                        &probe_stage,
                        (LONG)(2011u + sample_index * 20u + candidate * 2u)
                    );
                    alpha_instance_noarg get_module =
                        (alpha_instance_noarg)
                            type_module_candidates[candidate].pointer;
                    uintptr_t module = get_module(
                        type_object,
                        type_module_candidates[candidate].metadata
                    );
                    module_results[candidate] = module;
                    if (readable(module, sizeof(uintptr_t)))
                        module_nonnull[candidate]++;
                    InterlockedExchange(
                        &probe_stage,
                        (LONG)(2012u + sample_index * 20u + candidate * 2u)
                    );
                    alpha_instance_noarg get_declaring =
                        (alpha_instance_noarg)
                            type_declaring_candidates[candidate].pointer;
                    uintptr_t declaring = get_declaring(
                        type_object,
                        type_declaring_candidates[candidate].metadata
                    );
                    if (sample->expected_declaring_available &&
                        runtime_type_matches_descriptor(
                            declaring,
                            sample->expected_declaring_descriptor,
                            runtime_type_handle_qword
                        )) declaring_matches[candidate]++;
                }}
                if (module_results[0] &&
                    module_results[0] == module_results[1])
                    module_pair_matches++;
            }}
            if (module_nonnull[0] == extended_samples &&
                module_nonnull[1] == extended_samples &&
                module_pair_matches == extended_samples) {{
                current_module_selected = 0;
                InterlockedExchange(
                    &type_extended_module_match_count,
                    (LONG)module_pair_matches
                );
            }}
            for (uint32_t candidate = 0; candidate < 2u; candidate++) {{
                if (!declaring_expected ||
                    declaring_matches[candidate] != declaring_expected)
                    continue;
                current_declaring_equivalent++;
                if (current_declaring_selected < 0)
                    current_declaring_selected = (int)candidate;
            }}
            if (current_declaring_selected >= 0)
                InterlockedExchange(
                    &type_extended_declaring_match_count,
                    (LONG)declaring_matches[current_declaring_selected]
                );
        }}
        InterlockedExchange(
            &type_extended_sample_count, (LONG)extended_samples
        );
        InterlockedExchange(
            &type_extended_base_match_count, (LONG)base_matches
        );
        InterlockedExchange(
            &type_extended_element_match_count, (LONG)element_matches
        );
        InterlockedExchange(
            &type_extended_attribute_stable_count, (LONG)attribute_stable
        );
        InterlockedExchange(
            &type_extended_enum_match_count, (LONG)enum_matches
        );
        InterlockedExchange(
            &type_extended_value_match_count, (LONG)value_matches
        );
        InterlockedExchange(
            &type_extended_generic_match_count, (LONG)generic_matches
        );
        InterlockedExchange(
            &type_extended_generic_definition_match_count,
            (LONG)generic_definition_matches
        );
        InterlockedExchange(
            &type_extended_generic_argument_match_count,
            (LONG)generic_argument_matches
        );
        InterlockedExchange(
            &type_extended_interface_shape_count, (LONG)interface_shapes
        );
        InterlockedExchange(
            &type_extended_generic_definition_result_count,
            (LONG)generic_definition_results
        );
        InterlockedExchange(
            &type_extended_generic_definition_expected_count,
            (LONG)generic_definition_expected
        );
        InterlockedExchange(
            &type_extended_module_selected, (LONG)current_module_selected
        );
        InterlockedExchange(
            &type_extended_declaring_selected,
            (LONG)current_declaring_selected
        );
        InterlockedExchange(
            &type_extended_declaring_equivalent_count,
            (LONG)current_declaring_equivalent
        );
        InterlockedExchange(
            &type_extended_declaring_expected_count,
            (LONG)declaring_expected
        );
        int current_enum_selected = unique_dynamic_index(
            enum_candidate_matches,
            ALPHA_ENUM_UNDERLYING_CANDIDATE_COUNT,
            enum_samples >= 4u ? enum_samples : UINT64_MAX
        );
        InterlockedExchange(
            &remaining_enum_sample_count, (LONG)enum_samples
        );
        for (uint32_t candidate = 0; candidate < 3u; candidate++)
            InterlockedExchange(
                &remaining_enum_candidate_matches[candidate],
                (LONG)enum_candidate_matches[candidate]
            );
        InterlockedExchange(
            &remaining_enum_selected, (LONG)current_enum_selected
        );
        InterlockedExchange(&probe_stage, 119);
    }}
    int current_type_name_selected = unique_dynamic_index(
        type_name_matches, ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT, 8
    );
    int current_type_namespace_selected = unique_dynamic_index(
        type_namespace_matches, ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT, 8
    );
    InterlockedExchange(&fresh_type_identity_count, (LONG)fresh_types);
    InterlockedExchange(
        &type_name_selected, (LONG)current_type_name_selected
    );
    InterlockedExchange(
        &type_namespace_selected, (LONG)current_type_namespace_selected
    );
    InterlockedExchange(
        &type_name_match_count,
        current_type_name_selected >= 0
            ? (LONG)type_name_matches[current_type_name_selected] : 0
    );
    InterlockedExchange(
        &type_namespace_match_count,
        current_type_namespace_selected >= 0
            ? (LONG)type_namespace_matches[current_type_namespace_selected] : 0
    );
    uint32_t handler_relations = 0, handler_matches = 0;
    if (ALPHA_FRESH_RELATION_AVAILABLE && add_selected >= 0 &&
        method_parameters_candidate[0].pointer &&
        method_parameters_candidate[0].metadata &&
        parameter_type_candidate[0].pointer &&
        parameter_type_candidate[0].metadata &&
        event_handler_candidate[0].pointer &&
        event_handler_candidate[0].metadata) {{
        alpha_instance_boolarg get_add_method =
            (alpha_instance_boolarg)bool_candidates[add_selected].pointer;
        alpha_instance_noarg get_parameters_for_handler =
            (alpha_instance_noarg)method_parameters_candidate[0].pointer;
        alpha_instance_noarg get_parameter_type =
            (alpha_instance_noarg)parameter_type_candidate[0].pointer;
        alpha_instance_noarg get_event_handler_type =
            (alpha_instance_noarg)event_handler_candidate[0].pointer;
        for (uint32_t index = 0; index < discovered_objects; index++) {{
            uintptr_t event_object = event_objects[index];
            if (!object_class(event_object, event_class)) continue;
            uintptr_t add_method = get_add_method(
                event_object, 1u, bool_candidates[add_selected].metadata
            );
            if (!object_class(add_method, method_class)) continue;
            uintptr_t parameter_array = get_parameters_for_handler(
                add_method, method_parameters_candidate[0].metadata
            );
            uintptr_t parameters[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
            uint32_t parameter_count = 0;
            if (!typed_array_objects(
                    parameter_array, parameter_class, parameters,
                    &parameter_count, 0
                ) || parameter_count != 1) continue;
            uintptr_t observed_array_class = 0;
            memcpy(&observed_array_class, (const void *)parameter_array,
                sizeof(observed_array_class));
            parameter_array_class = observed_array_class;
            InterlockedExchange(
                &parameter_array_length_qword,
                InterlockedCompareExchange(
                    &derived_array_length_qword, 0, 0
                )
            );
            InterlockedExchange(
                &parameter_array_vector_qword,
                InterlockedCompareExchange(
                    &derived_array_vector_qword, 0, 0
                )
            );
            uintptr_t parameter_type = get_parameter_type(
                parameters[0], parameter_type_candidate[0].metadata
            );
            if (!object_class(parameter_type, runtime_type_class)) continue;
            handler_relations++;
            uintptr_t observed = get_event_handler_type(
                event_object, event_handler_candidate[0].metadata
            );
            if (observed == parameter_type &&
                object_class(observed, runtime_type_class))
                handler_matches++;
        }}
    }}
    InterlockedExchange(
        &event_handler_relation_count, (LONG)handler_relations
    );
    InterlockedExchange(
        &event_handler_match_count, (LONG)handler_matches
    );
    uintptr_t method_objects[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
    uintptr_t method_owner_descriptors[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
    uint32_t discovered_methods = 0;
    int method_collection_selected = -1;
    for (uint32_t candidate = 0;
         candidate < ALPHA_METHOD_COLLECTION_CANDIDATE_COUNT; candidate++) {{
        uintptr_t observed[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
        uintptr_t observed_owners[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
        uint32_t count = create_fresh_member_objects(
            &method_collection_candidate[candidate], method_class,
            observed, observed_owners, 0, ALPHA_EVENT_OBJECT_LIMIT
        );
        if (count < 8) continue;
        if (method_collection_selected >= 0) {{
            method_collection_selected = -2;
            discovered_methods = 0;
            break;
        }}
        method_collection_selected = (int)candidate;
        discovered_methods = count;
        memcpy(method_objects, observed,
            (SIZE_T)count * sizeof(uintptr_t));
        memcpy(method_owner_descriptors, observed_owners,
            (SIZE_T)count * sizeof(uintptr_t));
    }}
    uint32_t live_methods = 0, return_types = 0;
    uint32_t parameter_arrays = 0, parameter_objects = 0;
    uint32_t method_tokens = 0, distinct_tokens = 0;
    uint32_t observed_tokens[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
    alpha_instance_noarg get_return_type =
        (alpha_instance_noarg)method_return_candidate[0].pointer;
    alpha_instance_noarg get_parameters =
        (alpha_instance_noarg)method_parameters_candidate[0].pointer;
    alpha_instance_dword get_metadata_token =
        (alpha_instance_dword)metadata_token_candidate[0].pointer;
    if (get_return_type && get_parameters &&
        get_metadata_token &&
        method_return_candidate[0].metadata &&
        method_parameters_candidate[0].metadata &&
        metadata_token_candidate[0].metadata) {{
        for (uint32_t index = 0; index < discovered_methods; index++) {{
            uintptr_t method_object = method_objects[index];
            if (!object_class(method_object, method_class)) continue;
            live_methods++;
            uintptr_t return_type = get_return_type(
                method_object, method_return_candidate[0].metadata
            );
            if (object_class(return_type, runtime_type_class)) return_types++;
            uintptr_t parameters = get_parameters(
                method_object, method_parameters_candidate[0].metadata
            );
            uintptr_t observed[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
            uint32_t parameter_count = 0;
            if (parameter_array_objects(
                    parameters, observed, &parameter_count
                )) {{
                parameter_arrays++;
                parameter_objects += parameter_count;
            }}
            uint32_t token = get_metadata_token(
                method_object, metadata_token_candidate[0].metadata
            );
            if ((token & 0xff000000u) == 0x06000000u &&
                (token & 0x00ffffffu)) {{
                method_tokens++;
                int duplicate = 0;
                for (uint32_t prior = 0; prior < distinct_tokens; prior++)
                    if (observed_tokens[prior] == token) duplicate = 1;
                if (!duplicate)
                    observed_tokens[distinct_tokens++] = token;
            }}
        }}
    }}
    InterlockedExchange(&fresh_method_object_count, (LONG)live_methods);
    InterlockedExchange(
        &method_return_runtime_type_count, (LONG)return_types
    );
    InterlockedExchange(
        &method_parameter_array_count, (LONG)parameter_arrays
    );
    InterlockedExchange(
        &method_parameter_object_count, (LONG)parameter_objects
    );
    InterlockedExchange(&method_token_table_match_count, (LONG)method_tokens);
    InterlockedExchange(&method_token_distinct_count, (LONG)distinct_tokens);
    uintptr_t field_objects[ALPHA_FIELD_OBJECT_LIMIT] = {{0}};
    uintptr_t field_owner_descriptors[ALPHA_FIELD_OBJECT_LIMIT] = {{0}};
    uintptr_t property_objects[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
    uintptr_t property_owner_descriptors[ALPHA_EVENT_OBJECT_LIMIT] = {{0}};
    uint32_t discovered_fields = create_fresh_member_objects(
        &field_collection_candidate[0], field_class, field_objects,
        field_owner_descriptors, 0, ALPHA_FIELD_OBJECT_LIMIT
    );
    uint32_t discovered_properties = create_fresh_member_objects(
        &property_collection_candidate[0], property_class,
        property_objects, property_owner_descriptors, 0,
        ALPHA_EVENT_OBJECT_LIMIT
    );
    uint32_t field_handle_matches = 0;
    uint32_t property_handle_matches = 0;
    uint32_t method_handle_matches = 0;
    uint32_t field_handle_tokens = 0;
    uint32_t property_handle_tokens = 0;
    uint32_t property_handles_derived = 0;
    alpha_static_twoarg field_from_handle =
        (alpha_static_twoarg)field_from_handle_candidate[0].pointer;
    alpha_static_twoarg property_from_handle =
        (alpha_static_twoarg)property_from_handle_candidate[0].pointer;
    alpha_static_threearg method_from_handle =
        (alpha_static_threearg)method_from_handle_candidate[0].pointer;
    if (field_from_handle && field_from_handle_candidate[0].metadata) {{
        for (uint32_t index = 0;
             index < ALPHA_FIELD_HANDLE_SAMPLE_COUNT; index++) {{
            uintptr_t metadata = field_handle_samples[index].metadata;
            uintptr_t owner = field_handle_samples[index].owner_descriptor;
            if (!metadata || !owner) continue;
            InterlockedExchange(&probe_stage, (LONG)(3000u + index));
            uintptr_t roundtrip = field_from_handle(
                metadata, owner,
                field_from_handle_candidate[0].metadata
            );
            if (object_class(roundtrip, field_class)) {{
                field_handle_matches++;
                uint32_t token = get_metadata_token(
                    roundtrip, metadata_token_candidate[0].metadata
                );
                if ((token & 0xff000000u) == 0x04000000u &&
                    (token & 0x00ffffffu))
                    field_handle_tokens++;
            }}
            InterlockedExchange(
                &remaining_field_handle_match_count,
                (LONG)field_handle_matches
            );
            InterlockedExchange(
                &remaining_field_handle_token_match_count,
                (LONG)field_handle_tokens
            );
        }}
    }}
    InterlockedExchange(
        &remaining_field_handle_expected_count,
        (LONG)ALPHA_FIELD_HANDLE_SAMPLE_COUNT
    );
    if (property_from_handle &&
        property_from_handle_candidate[0].metadata) {{
        /* The current factory's uniquely derived store offset identifies
           the handle slot. Scanning past the object's extent admits adjacent
           heap objects and cannot establish uniqueness. Validate this slot
           through the factory roundtrip and exact token/handle identity. */
        uint32_t selected_qword =
            ALPHA_PROPERTY_OBJECT_HANDLE_BYTE_OFFSET / sizeof(uintptr_t);
        if (ALPHA_PROPERTY_OBJECT_HANDLE_BYTE_OFFSET % sizeof(uintptr_t) ||
            selected_qword < 2u || selected_qword >= 16u) {{
            selected_qword = 0;
        }}
        if (selected_qword) {{
            InterlockedExchange(
                &remaining_property_handle_qword_selected,
                (LONG)selected_qword
            );
        }}
        for (uint32_t index = 0;
             selected_qword && index < discovered_properties; index++) {{
            uintptr_t handle = 0;
            uintptr_t handle_address = property_objects[index] +
                (uintptr_t)selected_qword * sizeof(uintptr_t);
            if (handle_address < property_objects[index] ||
                !readable(handle_address, sizeof(handle))) continue;
            memcpy(&handle, (const void *)handle_address, sizeof(handle));
            uintptr_t encoded_address = handle +
                ALPHA_PROPERTY_HANDLE_OWNER_BYTE_OFFSET;
            if (!handle || encoded_address < handle ||
                !readable(encoded_address, sizeof(uintptr_t))) continue;
            uint32_t original_token = get_metadata_token(
                property_objects[index], metadata_token_candidate[0].metadata
            );
            if ((original_token & 0xff000000u) != 0x17000000u ||
                !(original_token & 0x00ffffffu)) continue;
            InterlockedExchange(&probe_stage, (LONG)(3100u + index));
            uintptr_t roundtrip = property_from_handle(
                handle, 0,
                property_from_handle_candidate[0].metadata
            );
            if (object_class(roundtrip, property_class)) {{
                property_handle_matches++;
                uint32_t token = get_metadata_token(
                    roundtrip, metadata_token_candidate[0].metadata
                );
                if (token == original_token) {{
                    property_handle_tokens++;
                    uintptr_t returned_handle = 0;
                    uintptr_t returned_slot = roundtrip +
                        ALPHA_PROPERTY_OBJECT_HANDLE_BYTE_OFFSET;
                    if (returned_slot >= roundtrip &&
                        readable(returned_slot, sizeof(returned_handle))) {{
                        memcpy(&returned_handle, (const void *)returned_slot,
                               sizeof(returned_handle));
                        if (returned_handle == handle) {{
                            property_handles_derived++;
                            InterlockedExchange(
                                &remaining_property_handle_derived_count,
                                (LONG)property_handles_derived
                            );
                        }}
                    }}
                }}
            }}
            InterlockedExchange(
                &remaining_property_handle_match_count,
                (LONG)property_handle_matches
            );
            InterlockedExchange(
                &remaining_property_handle_token_match_count,
                (LONG)property_handle_tokens
            );
        }}
    }}
    InterlockedExchange(
        &remaining_property_handle_expected_count,
        (LONG)discovered_properties
    );
    if (method_from_handle && method_from_handle_candidate[0].metadata) {{
        for (uint32_t index = 0; index < discovered_methods; index++) {{
            uintptr_t metadata = 0;
            uintptr_t address = method_objects[index] +
                ALPHA_METHOD_OBJECT_METADATA_BYTE_OFFSET;
            if (address < method_objects[index] ||
                !readable(address, sizeof(metadata))) continue;
            memcpy(&metadata, (const void *)address, sizeof(metadata));
            if (!metadata || !method_owner_descriptors[index]) continue;
            InterlockedExchange(&probe_stage, (LONG)(3200u + index));
            uintptr_t roundtrip = method_from_handle(
                metadata, method_owner_descriptors[index], 1u,
                method_from_handle_candidate[0].metadata
            );
            uintptr_t roundtrip_metadata = 0;
            uintptr_t roundtrip_address = roundtrip +
                ALPHA_METHOD_OBJECT_METADATA_BYTE_OFFSET;
            if (object_class(roundtrip, method_class) &&
                roundtrip_address >= roundtrip &&
                readable(roundtrip_address, sizeof(roundtrip_metadata))) {{
                memcpy(
                    &roundtrip_metadata, (const void *)roundtrip_address,
                    sizeof(roundtrip_metadata)
                );
                if (roundtrip_metadata == metadata)
                    method_handle_matches++;
            }}
        }}
    }}
    uint32_t field_static_count = 0;
    uint32_t field_literal_count = 0;
    uint32_t field_mutable_static_count = 0;
    uint32_t field_get_value_count = 0;
    uint32_t field_raw_constant_count = 0;
    uint32_t field_raw_constant_matches = 0;
    uint32_t field_set_same_count = 0;
    alpha_instance_dword field_attributes =
        (alpha_instance_dword)field_attributes_candidate[0].pointer;
    alpha_instance_onearg field_get_value =
        (alpha_instance_onearg)field_get_value_candidate[0].pointer;
    alpha_instance_noarg field_raw_constant =
        (alpha_instance_noarg)field_raw_constant_candidate[0].pointer;
    alpha_instance_twoarg_void field_set_value =
        (alpha_instance_twoarg_void)field_set_value_candidate[0].pointer;
    if (field_attributes && field_attributes_candidate[0].metadata &&
        field_get_value && field_get_value_candidate[0].metadata &&
        field_raw_constant && field_raw_constant_candidate[0].metadata &&
        field_set_value && field_set_value_candidate[0].metadata) {{
        for (uint32_t index = 0; index < discovered_fields; index++) {{
            uint32_t attributes = field_attributes(
                field_objects[index], field_attributes_candidate[0].metadata
            );
            if (!(attributes & 0x10u)) continue;
            field_static_count++;
            InterlockedExchange(&probe_stage, (LONG)(3300u + index));
            uintptr_t before = field_get_value(
                field_objects[index], 0,
                field_get_value_candidate[0].metadata
            );
            field_get_value_count++;
            if (attributes & 0x40u) {{
                field_literal_count++;
                uintptr_t constant = field_raw_constant(
                    field_objects[index],
                    field_raw_constant_candidate[0].metadata
                );
                field_raw_constant_count++;
                if (managed_value_equal(before, constant))
                    field_raw_constant_matches++;
            }} else if (!(attributes & 0x20u) &&
                       field_mutable_static_count < 8u) {{
                field_mutable_static_count++;
                field_set_value(
                    field_objects[index], 0, before,
                    field_set_value_candidate[0].metadata
                );
                uintptr_t after = field_get_value(
                    field_objects[index], 0,
                    field_get_value_candidate[0].metadata
                );
                if (managed_value_equal(before, after))
                    field_set_same_count++;
            }}
            InterlockedExchange(
                &remaining_field_static_count, (LONG)field_static_count
            );
            InterlockedExchange(
                &remaining_field_literal_count, (LONG)field_literal_count
            );
            InterlockedExchange(
                &remaining_field_mutable_static_count,
                (LONG)field_mutable_static_count
            );
            InterlockedExchange(
                &remaining_field_get_value_count,
                (LONG)field_get_value_count
            );
            InterlockedExchange(
                &remaining_field_raw_constant_count,
                (LONG)field_raw_constant_count
            );
            InterlockedExchange(
                &remaining_field_raw_constant_match_count,
                (LONG)field_raw_constant_matches
            );
            InterlockedExchange(
                &remaining_field_set_same_count,
                (LONG)field_set_same_count
            );
        }}
    }}
    InterlockedExchange(
        &remaining_field_object_count, (LONG)discovered_fields
    );
    InterlockedExchange(
        &remaining_property_object_count, (LONG)discovered_properties
    );
    InterlockedExchange(
        &remaining_field_handle_match_count, (LONG)field_handle_matches
    );
    InterlockedExchange(
        &remaining_property_handle_match_count,
        (LONG)property_handle_matches
    );
    InterlockedExchange(
        &remaining_method_handle_match_count, (LONG)method_handle_matches
    );
    InterlockedExchange(
        &remaining_field_handle_token_match_count,
        (LONG)field_handle_tokens
    );
    InterlockedExchange(
        &remaining_property_handle_token_match_count,
        (LONG)property_handle_tokens
    );
    int method_complete = method_collection_selected >= 0 &&
        live_methods >= 8 && return_types == live_methods &&
        parameter_arrays == live_methods && parameter_objects >= 8 &&
        method_tokens == live_methods && distinct_tokens == live_methods;
    int handler_complete = !ALPHA_FRESH_RELATION_AVAILABLE ||
        (handler_relations >= 8 && handler_matches == handler_relations);
    int type_identity_complete = !ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT ||
        (((ALPHA_TYPE_IDENTITY_STRUCTURAL_STRING_SAFE &&
           ALPHA_TYPE_IDENTITY_CANDIDATE_COUNT == 2u) ||
          (reflected_type_methods >= 2 &&
           metadata_matches == reflected_type_methods)) &&
         safe_string_candidates >= 2 && fresh_types >= 8 &&
         current_type_name_selected >= 0 &&
         current_type_namespace_selected >= 0 &&
         current_type_name_selected != current_type_namespace_selected &&
         type_name_matches[current_type_name_selected] == fresh_types &&
         type_namespace_matches[current_type_namespace_selected] ==
             fresh_types);
    LONG extended_sample_count = InterlockedCompareExchange(
        &type_extended_sample_count, 0, 0
    );
    LONG generic_definition_expected_count = InterlockedCompareExchange(
        &type_extended_generic_definition_expected_count, 0, 0
    );
    LONG declaring_expected_count = InterlockedCompareExchange(
        &type_extended_declaring_expected_count, 0, 0
    );
    int type_extended_complete = !ALPHA_TYPE_SEMANTIC_SAMPLE_COUNT ||
        (extended_sample_count >= 8 &&
         extended_sample_count == (LONG)ALPHA_TYPE_SEMANTIC_SAMPLE_COUNT &&
         InterlockedCompareExchange(
             &type_extended_base_match_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_element_match_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_attribute_stable_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_enum_match_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_value_match_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_generic_match_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_generic_definition_match_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_generic_argument_match_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_interface_shape_count, 0, 0
         ) == extended_sample_count &&
         generic_definition_expected_count >= 4 &&
         InterlockedCompareExchange(
             &type_extended_generic_definition_result_count, 0, 0
         ) == generic_definition_expected_count &&
         InterlockedCompareExchange(
             &type_extended_module_selected, 0, 0
         ) >= 0 &&
         InterlockedCompareExchange(
             &type_extended_module_match_count, 0, 0
         ) == extended_sample_count &&
         InterlockedCompareExchange(
             &type_extended_declaring_selected, 0, 0
         ) >= 0 &&
         InterlockedCompareExchange(
             &type_extended_declaring_equivalent_count, 0, 0
         ) >= 1 &&
         declaring_expected_count >= 8 &&
         InterlockedCompareExchange(
             &type_extended_declaring_match_count, 0, 0
         ) == declaring_expected_count &&
         InterlockedCompareExchange(
             &type_extended_attributes_selected, 0, 0
         ) >= 0 &&
         InterlockedCompareExchange(
             &type_extended_enum_selected, 0, 0
         ) >= 0 &&
         InterlockedCompareExchange(
             &type_extended_value_selected, 0, 0
         ) >= 0);
    int complete = live_objects >= 8 && name_selected >= 0 &&
        add_selected >= 0 && remove_selected >= 0 && raise_selected >= 0 &&
        add_selected != remove_selected && add_selected != raise_selected &&
        remove_selected != raise_selected && method_complete &&
        handler_complete && type_identity_complete && type_extended_complete;
    char executable_sha256[65] = {{0}};
    int identity = GetCurrentProcessId() == expected_process_id &&
        image_identity() && executable_identity(executable_sha256) &&
        !strcmp(executable_sha256, expected_executable_sha256);
    write_status(pending_status_output, identity && complete ? "complete" : "behavior-rejected",
        executable_sha256, live_objects, zero_string, zero_type, zero_other,
        bool_null, bool_add, bool_remove, bool_raise, bool_other,
        name_selected, add_selected, remove_selected, raise_selected);
    return identity && complete;
}}

static LRESULT CALLBACK probe_window_proc(
    HWND window, UINT message, WPARAM parameter, LPARAM data
) {{
    if (message == probe_message) {{
        LONG request = (LONG)parameter;
        if (!request || InterlockedCompareExchange(&probe_request, 0, 0) != request ||
            InterlockedCompareExchange(&probe_active, 1, 0)) return 0;
        if (InterlockedCompareExchange(&probe_request, 0, request) != request ||
            InterlockedCompareExchange(&probe_state, 1, 0) != 0) {{
            InterlockedExchange(&probe_active, 0); return 0;
        }}
        InterlockedExchange(&probe_state, run_probe() ? 2 : -1);
        if (probe_event) SetEvent(probe_event);
        InterlockedExchange(&probe_active, 0);
        return probe_state == 2;
    }}
    return original_window_proc
        ? CallWindowProcW(
            original_window_proc, window, message, parameter, data
        )
        : DefWindowProcW(window, message, parameter, data);
}}

typedef struct alpha_window {{
    DWORD process_id;
    HWND selected;
    DWORD thread_id;
    uint32_t count;
}} alpha_window;

static BOOL CALLBACK select_window(HWND window, LPARAM parameter) {{
    alpha_window *selection = (alpha_window *)(uintptr_t)parameter;
    DWORD process_id = 0;
    RECT bounds;
    if (!selection || !IsWindowVisible(window) ||
        GetWindow(window, GW_OWNER) != NULL ||
        !GetWindowRect(window, &bounds) || bounds.right <= bounds.left ||
        bounds.bottom <= bounds.top) return TRUE;
    DWORD thread_id = GetWindowThreadProcessId(window, &process_id);
    if (process_id != selection->process_id || !thread_id) return TRUE;
    selection->selected = window;
    selection->thread_id = thread_id;
    selection->count++;
    return TRUE;
}}

static int dispatch_probe(HWND window) {{
    for (uint32_t attempt = 0; attempt < 17u; attempt++) {{
        LONG request = InterlockedIncrement(&probe_sequence);
        InterlockedExchange(&probe_request, request);
        DWORD_PTR result = 0;
        SetLastError(0);
        int sent = SendMessageTimeoutW(window, probe_message, (WPARAM)request, 0,
            SMTO_BLOCK, 60000, &result) != 0;
        probe_dispatch_error = GetLastError();
        InterlockedExchange(&probe_request, 0);
        for (uint32_t wait = 0;
             InterlockedCompareExchange(&probe_active, 0, 0) && wait < 2000u;
             wait++) Sleep(1);
        if (InterlockedCompareExchange(&probe_active, 0, 0)) {{
            probe_dispatch_failure = 504u; return 0;
        }}
        LONG state = InterlockedCompareExchange(&probe_state, 0, 0);
        if (state == 2 || state == -1) {{
            probe_dispatch_error = 0;
            return WaitForSingleObject(probe_event, 0) == WAIT_OBJECT_0;
        }}
        if (sent || state != 0) {{ probe_dispatch_failure = 505u; return 0; }}
        if (attempt + 1u < 17u) Sleep(250);
    }}
    probe_dispatch_failure = 506u; return 0;
}}

static DWORD WINAPI worker(void *unused) {{
    (void)unused;
    char executable_sha256[65] = {{0}};
    if (GetCurrentProcessId() != expected_process_id || !image_identity() ||
        !executable_identity(executable_sha256) ||
        strcmp(executable_sha256, expected_executable_sha256)) {{
        uint64_t empty[3] = {{0}};
        write_status(status_output, "identity-binding-rejected", executable_sha256, 0,
            empty, empty, empty, empty, empty, empty, empty, empty,
            -1, -1, -1, -1);
        return 1;
    }}
    alpha_window selection = {{0}};
    selection.process_id = GetCurrentProcessId();
    if (!EnumWindows(select_window, (LPARAM)(uintptr_t)&selection) ||
        selection.count != 1 || !selection.selected || !selection.thread_id) {{
        uint64_t empty[3] = {{0}};
        write_status(status_output, "managed-window-rejected", executable_sha256, 0,
            empty, empty, empty, empty, empty, empty, empty, empty,
            -1, -1, -1, -1);
        return 2;
    }}
    probe_message = RegisterWindowMessageW(
        L"ALPHA v2 current runtime reflection behavior"
    );
    probe_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    if (!probe_message || !probe_event) {{
        probe_dispatch_failure = 501u; probe_dispatch_error = GetLastError();
    }}
    SetLastError(0);
    if (!probe_dispatch_failure) original_window_proc = (WNDPROC)(uintptr_t)SetWindowLongPtrW(
        selection.selected, GWLP_WNDPROC,
        (LONG_PTR)(uintptr_t)probe_window_proc
    );
    DWORD subclass_error = GetLastError();
    int subclassed = original_window_proc && subclass_error == ERROR_SUCCESS;
    if (!subclassed && !probe_dispatch_failure) {{
        probe_dispatch_failure = 502u; probe_dispatch_error = subclass_error;
    }}
    int dispatched = subclassed && dispatch_probe(selection.selected);
    InterlockedExchange(&probe_request, 0);
    if (subclassed) {{
        SetLastError(0);
        LONG_PTR restored = SetWindowLongPtrW(selection.selected, GWLP_WNDPROC,
            (LONG_PTR)(uintptr_t)original_window_proc);
        DWORD restore_error = GetLastError();
        if (!restored || restore_error != ERROR_SUCCESS) {{
            probe_dispatch_failure = 503u; probe_dispatch_error = restore_error; dispatched = 0;
        }}
    }}
    /* A complete observation is private until callback quiescence AND hook
       restoration. The next stage must never race this collector's cleanup. */
    int inactive = !InterlockedCompareExchange(&probe_active, 0, 0);
    int published = dispatched && inactive && MoveFileExW(pending_status_output, status_output,
        MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH);
    if (!published) {{
        if (dispatched && inactive && !probe_dispatch_failure) {{
            probe_dispatch_failure = 507u; probe_dispatch_error = GetLastError();
        }}
        uint64_t empty[3] = {{0}};
        write_status(status_output, "managed-callback-rejected", executable_sha256, 0,
            empty, empty, empty, empty, empty, empty, empty, empty,
            -1, -1, -1, -1);
    }}
    /* An in-flight callback may still signal this event. Retain it on failure. */
    if (probe_event && inactive) {{ CloseHandle(probe_event); probe_event = NULL; }}
    return published && probe_state == 2 ? 0 : 3;
}}

BOOL WINAPI DllMain(HINSTANCE instance, DWORD reason, LPVOID reserved) {{
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {{
        self_module = instance;
        DisableThreadLibraryCalls(instance);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }}
    return TRUE;
}}
'''


def prepare_runtime_reflection_behavior(
    *,
    binary: Path,
    snapshot: Path,
    bootstrap_model: Path,
    class_model: Path,
    semantics_model: Path,
    output_dir: Path,
    materializer_model: Path | None = None,
    native_helper_model: Path | None = None,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        snapshot=snapshot,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
        semantics_model=semantics_model,
        materializer_model=materializer_model,
        native_helper_model=native_helper_model,
    )
    status_path = output_dir / "runtime-reflection-behavior-status.private.json"
    if any(path.exists() for path in (status_path, status_path.with_name(status_path.name + ".pending"),
            output_dir / "runtime-reflection-behavior-plan.private.json")):
        raise AcquisitionError("reflection behavior capture requires a new output directory")
    build_dir = _owner_directory(output_dir / "build-reflection-behavior")
    source_path = build_dir / "runtime-reflection-behavior.c"
    injector_source = build_dir / "runtime-reflection-behavior-injector.c"
    injector = build_dir / "alpha-runtime-reflection-behavior-injector.exe"
    _private_text(
        source_path,
        runtime_reflection_behavior_source(
            binding=binding,
            status_path=status_path,
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    collector = build_dir / (
        "alpha-runtime-reflection-behavior-"
        + file_identity(source_path)["sha256"][:12]
        + ".dll"
    )
    selected_compiler = _compiler(compiler)


    with ThreadPoolExecutor(max_workers=2) as executor:
        collector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler),
                "-O2",
                "-s",
                "-shared",
                "-Wall",
                "-Wextra",
                "-Wformat=2",
                "-Werror=format",
                str(source_path),
                "-o",
                str(collector),
                "-lbcrypt",
            ],
            label="runtime reflection behavior probe",
            source_path=source_path,
            output_path=collector,
        )
        injector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler),
                "-O2",
                "-s",
                "-municode",
                "-Wall",
                "-Wextra",
                "-Wformat=2",
                "-Werror=format",
                str(injector_source),
                "-o",
                str(injector),
            ],
            label="runtime reflection behavior injector",
            source_path=injector_source,
            output_path=injector,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector, injector):
        artifact.chmod(0o600)
    plan_inputs = {
        key: binding[key]
        for key in (
            "snapshot",
            "bootstrap",
            "classes",
            "semantics",
            "memory_status",
        )
    }
    fresh_factory = binding.get("fresh_event_factory_owner_only")
    extended_available = (
        isinstance(fresh_factory, dict)
        and isinstance(
            fresh_factory.get("type_extended_candidates_owner_only"), dict
        )
        and isinstance(
            fresh_factory.get("type_semantic_sample_count"), int
        )
        and fresh_factory["type_semantic_sample_count"] >= 8
    )
    remaining_candidates = (
        fresh_factory.get("remaining_candidates_owner_only")
        if isinstance(fresh_factory, dict)
        else None
    )
    remaining_evidence = (
        fresh_factory.get("remaining_structural_evidence")
        if isinstance(fresh_factory, dict)
        else None
    )
    remaining_available = (
        isinstance(remaining_candidates, dict)
        and set(remaining_candidates) == set(_REMAINING_FAMILIES.values())
        and all(
            isinstance(remaining_candidates.get(family), list)
            and len(remaining_candidates[family])
            == (3 if key == "enum.underlying_type" else 1)
            for key, family in _REMAINING_FAMILIES.items()
        )
        and isinstance(remaining_evidence, dict)
        and remaining_evidence.get("structurally_unique_candidate_count")
        == 6
        and remaining_evidence.get("enum_behavior_candidate_count") == 3
        and remaining_evidence.get(
            "property_handle_protection_shape_unique"
        )
        is True
        and remaining_evidence.get(
            "property_factory_handle_store_pair_unique"
        )
        is True
    )
    structural_string_safe = int(
        isinstance(fresh_factory, dict)
        and fresh_factory.get("type_identity_callgraph_evidence", {}).get(
            "structural_string_return_safe"
        )
        is True
    )
    if isinstance(fresh_factory, dict):
        plan_inputs["materializer"] = fresh_factory[
            "materializer_identity"
        ]
        plan_inputs["native_member_inventory"] = fresh_factory[
            "member_inventory_identity"
        ]
        plan_inputs["native_helpers"] = fresh_factory[
            "native_helper_identity"
        ]
        plan_inputs["native_inventory"] = fresh_factory[
            "native_inventory_identity"
        ]
    plan = {
        "schema": RUNTIME_REFLECTION_BEHAVIOR_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": plan_inputs,
        "collector": file_identity(collector),
        "injector": file_identity(injector),
        "status_path": str(status_path),
        "contract": {
            "operation_keys": list(_EVENT_OPERATION_KEYS)
            + (
                list(_EVENT_RELATION_OPERATION_KEYS)
                + list(_METHOD_OPERATION_KEYS)
                + list(_MEMBER_OPERATION_KEYS)
                + list(_TYPE_IDENTITY_OPERATION_KEYS)
                + (
                    list(_TYPE_EXTENDED_OPERATION_KEYS)
                    if extended_available
                    else []
                )
                + (
                    list(_REMAINING_OPERATION_KEYS)
                    if remaining_available
                    else []
                )
                if fresh_factory
                else []
            ),
            "snapshot_event_object_evidence_count": binding[
                "snapshot_event_object_evidence_count"
            ],
            "bool_candidate_count": 3,
            "zero_candidate_count": 3,
            "fresh_event_factory_available": isinstance(
                fresh_factory, dict
            ),
            "fresh_method_behavior_available": isinstance(
                fresh_factory, dict
            ),
            "fresh_event_handler_relation_available": isinstance(
                fresh_factory, dict
            ),
            "fresh_type_identity_behavior_available": isinstance(
                fresh_factory, dict
            ),
            "fresh_type_extended_behavior_available": extended_available,
            "fresh_remaining_behavior_available": remaining_available,
            "type_extended_sample_count": (
                fresh_factory["type_semantic_sample_count"]
                if extended_available
                else 0
            ),
            "type_identity_candidate_count": (
                len(
                    fresh_factory[
                        "type_identity_string_candidates_owner_only"
                    ]
                )
                if isinstance(fresh_factory, dict)
                else 0
            ),
        },
        "candidates_owner_only": {
            "bool": binding["bool_candidates_owner_only"],
            "zero": binding["zero_candidates_owner_only"],
            "fresh_event_factory": fresh_factory,
        },
        "policy": {
            "same_process_required": True,
            "managed_window_thread_required": True,
            "current_executable_sha256_embedded": True,
            "fresh_behavior_required": True,
            "live_event_object_discovery_required": True,
            "snapshot_object_pointer_reuse": False,
            "fresh_event_factory_current_inventory_bound": isinstance(
                fresh_factory, dict
            ),
            "native_event_helper_callgraph_required": isinstance(
                fresh_factory, dict
            ),
            "fresh_method_array_behavior_required": isinstance(
                fresh_factory, dict
            ),
            "fresh_event_handler_parameter_relation_required": isinstance(
                fresh_factory, dict
            ),
            "fresh_known_type_identity_behavior_required": isinstance(
                fresh_factory, dict
            ),
            "fresh_type_extended_semantics_required": extended_available,
            "type_extended_behavior_selection_required": extended_available,
            "fresh_remaining_semantics_required": remaining_available,
            "type_identity_runtime_string_return_filter_required": isinstance(
                fresh_factory, dict
            ) and not structural_string_safe,
            "type_identity_structural_string_constructor_required": bool(
                structural_string_safe
            ),
            "type_identity_current_method_name_relation_required": isinstance(
                fresh_factory, dict
            ) and not structural_string_safe,
            "saved_alias_used": False,
            "fixed_ordinal_used": False,
            "external_runtime_component_used": False,
            "raw_pointers_owner_only": True,
        },
    }
    _private_json(
        output_dir / "runtime-reflection-behavior-plan.private.json", plan
    )
    return {
        "schema": RUNTIME_REFLECTION_BEHAVIOR_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "contract": plan["contract"],
        "policy": plan["policy"],
    }


def capture_runtime_reflection_behavior(
    *,
    binary: Path,
    snapshot: Path,
    bootstrap_model: Path,
    class_model: Path,
    semantics_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    materializer_model: Path | None = None,
    native_helper_model: Path | None = None,
    compiler: Path | None = None,
    timeout: float = 120.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_reflection_behavior(
        binary=binary,
        snapshot=snapshot,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
        semantics_model=semantics_model,
        materializer_model=materializer_model,
        native_helper_model=native_helper_model,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-reflection-behavior-plan.private.json"
    plan = read_json(plan_path)
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError(
            "runtime reflection behavior Wine selection is unavailable"
        )
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "runtime reflection behavior injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-reflection-behavior-injector.private.log",
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
        raise AcquisitionError(
            "runtime reflection behavior injection failed "
            f"({injected.returncode})"
        )
    status_path = Path(plan["status_path"])
    deadline = time.monotonic() + max(1.0, timeout)
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        if status_path.is_file():
            try:
                value = json.loads(status_path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                value = None
            if isinstance(value, dict):
                status = value
                break
        time.sleep(0.25)
    if status is None:
        raise AcquisitionError("runtime reflection behavior capture timed out")
    _seal_runtime_output(status_path)
    selected = status.get("selected")
    type_selected = status.get("type_selected")
    bool_candidates = status.get("bool_candidates")
    zero_candidates = status.get("zero_candidates")
    relation_required = plan.get("contract", {}).get(
        "fresh_event_handler_relation_available"
    ) is True
    type_identity_required = plan.get("contract", {}).get(
        "fresh_type_identity_behavior_available"
    ) is True
    type_extended_required = plan.get("contract", {}).get(
        "fresh_type_extended_behavior_available"
    ) is True
    remaining_required = plan.get("contract", {}).get(
        "fresh_remaining_behavior_available"
    ) is True
    plan_fresh_factory = plan.get("candidates_owner_only", {}).get(
        "fresh_event_factory"
    )
    type_extended_candidates = (
        plan_fresh_factory.get("type_extended_candidates_owner_only")
        if isinstance(plan_fresh_factory, dict)
        else None
    )
    type_extended_evidence = (
        plan_fresh_factory.get("type_extended_structural_evidence")
        if isinstance(plan_fresh_factory, dict)
        else None
    )
    remaining_candidates = (
        plan_fresh_factory.get("remaining_candidates_owner_only")
        if isinstance(plan_fresh_factory, dict)
        else None
    )
    remaining_evidence = (
        plan_fresh_factory.get("remaining_structural_evidence")
        if isinstance(plan_fresh_factory, dict)
        else None
    )
    type_extended_selected: dict[str, int] = {}
    behavior_selected_status = {
        "type.attributes": "type_extended_attributes_selected",
        "type.is_enum": "type_extended_enum_selected",
        "type.is_value_type": "type_extended_value_selected",
    }
    if type_extended_required and isinstance(type_extended_candidates, dict):
        for key in _TYPE_EXTENDED_OPERATION_KEYS:
            if key == "type.module":
                index = status.get("type_extended_module_selected")
            elif key == "type.declaring_type":
                index = status.get("type_extended_declaring_selected")
            elif key in behavior_selected_status:
                index = status.get(behavior_selected_status[key])
            else:
                index = 0
            type_extended_selected[key] = index
    valid_type_extended_selection = (
        not type_extended_required
        or (
            isinstance(type_extended_candidates, dict)
            and set(type_extended_selected)
            == set(_TYPE_EXTENDED_OPERATION_KEYS)
            and all(
                isinstance(type_extended_selected[key], int)
                and isinstance(
                    type_extended_candidates.get(
                        _TYPE_EXTENDED_FAMILIES[key]
                    ),
                    list,
                )
                and 0
                <= type_extended_selected[key]
                < len(
                    type_extended_candidates[
                        _TYPE_EXTENDED_FAMILIES[key]
                    ]
                )
                for key in _TYPE_EXTENDED_OPERATION_KEYS
            )
        )
    )
    remaining_selected: dict[str, int] = {}
    if remaining_required and isinstance(remaining_candidates, dict):
        for key in _REMAINING_OPERATION_KEYS:
            remaining_selected[key] = (
                status.get("remaining_enum_selected")
                if key == "enum.underlying_type"
                else 0
            )
    valid_remaining_selection = (
        not remaining_required
        or (
            isinstance(remaining_candidates, dict)
            and set(remaining_selected) == set(_REMAINING_OPERATION_KEYS)
            and all(
                isinstance(remaining_selected[key], int)
                and isinstance(
                    remaining_candidates.get(_REMAINING_FAMILIES[key]),
                    list,
                )
                and 0
                <= remaining_selected[key]
                < len(
                    remaining_candidates[_REMAINING_FAMILIES[key]]
                )
                for key in _REMAINING_OPERATION_KEYS
            )
        )
    )
    type_identity_structurally_bound = (
        plan.get("policy", {}).get(
            "type_identity_structural_string_constructor_required"
        )
        is True
        and plan.get("contract", {}).get("type_identity_candidate_count")
        == 2
    )
    valid_selection = (
        isinstance(selected, dict)
        and set(selected) == set(_EVENT_OPERATION_KEYS)
        and all(isinstance(selected[key], int) for key in _EVENT_OPERATION_KEYS)
        and 0 <= selected["event.name"] < 3
        and all(
            0 <= selected[key] < 3
            for key in _EVENT_OPERATION_KEYS[1:]
        )
        and len({selected[key] for key in _EVENT_OPERATION_KEYS[1:]}) == 3
    )
    valid_type_selection = (
        isinstance(type_selected, dict)
        and set(type_selected) == set(_TYPE_IDENTITY_OPERATION_KEYS)
        and all(
            isinstance(type_selected[key], int)
            and 0
            <= type_selected[key]
            < plan.get("contract", {}).get(
                "type_identity_candidate_count", 0
            )
            for key in _TYPE_IDENTITY_OPERATION_KEYS
        )
        and len(
            {type_selected[key] for key in _TYPE_IDENTITY_OPERATION_KEYS}
        )
        == 2
    )
    checks = {
        "schema": status.get("schema")
        == RUNTIME_REFLECTION_BEHAVIOR_STATUS_SCHEMA,
        "complete": status.get("status") == "complete",
        "same_process": status.get("process_id")
        == plan["target"]["process_id"]
        and status.get("expected_process_id")
        == plan["target"]["process_id"],
        "executable_identity_bound": status.get(
            "observed_executable_sha256"
        )
        == plan["target"]["executable_sha256"],
        "input_identities_embedded": status.get("expected_snapshot_sha256")
        == plan["inputs"]["snapshot"]["sha256"]
        and status.get("expected_semantics_sha256")
        == plan["inputs"]["semantics"]["sha256"],
        "live_event_domain_complete": isinstance(
            status.get("live_event_object_count"), int
        )
        and status["live_event_object_count"] >= 8,
        "candidate_domains_complete": isinstance(bool_candidates, list)
        and len(bool_candidates) == 3
        and isinstance(zero_candidates, list)
        and len(zero_candidates) == 3,
        "all_event_operations_unique": valid_selection,
        "fresh_method_behavior_complete": (
            isinstance(status.get("fresh_method_object_count"), int)
            and status["fresh_method_object_count"] >= 8
            and status.get("method_return_runtime_type_count")
            == status["fresh_method_object_count"]
            and status.get("method_parameter_array_count")
            == status["fresh_method_object_count"]
            and isinstance(status.get("method_parameter_object_count"), int)
            and status["method_parameter_object_count"] >= 8
        ),
        "fresh_metadata_token_behavior_complete": (
            isinstance(status.get("fresh_method_object_count"), int)
            and status["fresh_method_object_count"] >= 8
            and status.get("method_token_table_match_count")
            == status["fresh_method_object_count"]
            and status.get("method_token_distinct_count")
            == status["fresh_method_object_count"]
        ),
        "fresh_event_handler_behavior_complete": (
            not relation_required
            or (
                isinstance(status.get("event_handler_relation_count"), int)
                and status["event_handler_relation_count"] >= 8
                and status.get("event_handler_match_count")
                == status["event_handler_relation_count"]
            )
        ),
        "fresh_type_identity_behavior_complete": (
            not type_identity_required
            or (
                valid_type_selection
                and isinstance(status.get("fresh_type_identity_count"), int)
                and status["fresh_type_identity_count"] >= 8
                and status.get("type_filter_runtime_sentinel_count")
                == status["fresh_type_identity_count"]
                and (
                    type_identity_structurally_bound
                    or (
                        isinstance(
                            status.get(
                                "type_filter_reflected_method_count"
                            ),
                            int,
                        )
                        and status[
                            "type_filter_reflected_method_count"
                        ]
                        >= 2
                        and status.get("type_filter_metadata_match_count")
                        == status.get("type_filter_reflected_method_count")
                    )
                )
                and status.get("type_filter_string_return_method_count")
                == status.get("type_string_return_candidate_count")
                and isinstance(
                    status.get("type_string_return_candidate_count"), int
                )
                and status["type_string_return_candidate_count"] >= 2
                and status.get("type_name_match_count")
                == status["fresh_type_identity_count"]
                and status.get("type_namespace_match_count")
                == status["fresh_type_identity_count"]
            )
        ),
        "fresh_type_extended_behavior_complete": (
            not type_extended_required
            or (
                valid_type_extended_selection
                and isinstance(type_extended_evidence, dict)
                and type_extended_evidence.get("resolved_family_count") == 10
                and type_extended_evidence.get(
                    "behavior_selected_family_count"
                )
                == 3
                and type_extended_evidence.get("module_pair_count") == 2
                and type_extended_evidence.get(
                    "declaring_type_equivalence_candidate_count"
                )
                == 2
                and isinstance(
                    status.get("type_extended_sample_count"), int
                )
                and status["type_extended_sample_count"]
                == plan.get("contract", {}).get(
                    "type_extended_sample_count"
                )
                and status["type_extended_sample_count"] >= 8
                and all(
                    status.get(field)
                    == status["type_extended_sample_count"]
                    for field in (
                        "type_extended_base_match_count",
                        "type_extended_element_match_count",
                        "type_extended_attribute_stable_count",
                        "type_extended_enum_match_count",
                        "type_extended_value_match_count",
                        "type_extended_generic_match_count",
                        "type_extended_generic_definition_match_count",
                        "type_extended_generic_argument_match_count",
                        "type_extended_interface_shape_count",
                        "type_extended_module_match_count",
                    )
                )
                and isinstance(
                    status.get(
                        "type_extended_generic_definition_expected_count"
                    ),
                    int,
                )
                and status[
                    "type_extended_generic_definition_expected_count"
                ]
                >= 4
                and status.get(
                    "type_extended_generic_definition_result_count"
                )
                == status[
                    "type_extended_generic_definition_expected_count"
                ]
                and isinstance(
                    status.get("type_extended_declaring_expected_count"),
                    int,
                )
                and status["type_extended_declaring_expected_count"] >= 8
                and status.get("type_extended_declaring_match_count")
                == status["type_extended_declaring_expected_count"]
                and isinstance(
                    status.get(
                        "type_extended_declaring_equivalent_count"
                    ),
                    int,
                )
                and status[
                    "type_extended_declaring_equivalent_count"
                ]
                >= 1
            )
        ),
        "fresh_remaining_behavior_complete": (
            not remaining_required
            or (
                valid_remaining_selection
                and isinstance(remaining_evidence, dict)
                and remaining_evidence.get(
                    "structurally_unique_candidate_count"
                )
                == 6
                and remaining_evidence.get(
                    "enum_behavior_candidate_count"
                )
                == 3
                and remaining_evidence.get(
                    "property_handle_protection_shape_unique"
                )
                is True
                and remaining_evidence.get(
                    "property_factory_handle_store_pair_unique"
                )
                is True
                and isinstance(
                    status.get("remaining_field_handle_expected_count"), int
                )
                and status["remaining_field_handle_expected_count"] >= 64
                and status.get("remaining_field_handle_match_count")
                == status["remaining_field_handle_expected_count"]
                and status.get(
                    "remaining_field_handle_token_match_count"
                )
                == status["remaining_field_handle_expected_count"]
                and isinstance(
                    status.get("remaining_property_handle_expected_count"),
                    int,
                )
                and status["remaining_property_handle_expected_count"] >= 64
                and status.get("remaining_property_handle_match_count")
                == status["remaining_property_handle_expected_count"]
                and status.get(
                    "remaining_property_handle_token_match_count"
                )
                == status["remaining_property_handle_expected_count"]
                and isinstance(
                    status.get("remaining_property_handle_derived_count"), int
                )
                and status["remaining_property_handle_derived_count"]
                == status["remaining_property_handle_expected_count"]
                and isinstance(
                    status.get(
                        "remaining_property_handle_qword_selected_owner_only"
                    ),
                    int,
                )
                and status[
                    "remaining_property_handle_qword_selected_owner_only"
                ]
                >= 2
                and status.get("remaining_method_handle_match_count")
                == status.get("fresh_method_object_count")
                and isinstance(status.get("remaining_enum_sample_count"), int)
                and status["remaining_enum_sample_count"] >= 4
                and isinstance(
                    status.get("remaining_enum_candidate_matches"), list
                )
                and len(status["remaining_enum_candidate_matches"]) == 3
                and status["remaining_enum_candidate_matches"][
                    remaining_selected["enum.underlying_type"]
                ]
                == status["remaining_enum_sample_count"]
                and all(
                    count == 0
                    for index, count in enumerate(
                        status["remaining_enum_candidate_matches"]
                    )
                    if index
                    != remaining_selected["enum.underlying_type"]
                )
                and isinstance(status.get("remaining_field_static_count"), int)
                and status["remaining_field_static_count"] >= 8
                and status.get("remaining_field_get_value_count")
                == status["remaining_field_static_count"]
                and isinstance(
                    status.get("remaining_field_literal_count"), int
                )
                and status["remaining_field_literal_count"] >= 4
                and status.get("remaining_field_raw_constant_count")
                == status["remaining_field_literal_count"]
                and status.get("remaining_field_raw_constant_match_count")
                == status["remaining_field_literal_count"]
                and isinstance(
                    status.get("remaining_field_mutable_static_count"), int
                )
                and status["remaining_field_mutable_static_count"] >= 4
                and status.get("remaining_field_set_same_count")
                == status["remaining_field_mutable_static_count"]
            )
        ),
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        )
        is True,
        "saved_alias_absent": status.get("saved_alias_used") is False,
        "fixed_ordinal_absent": status.get("fixed_ordinal_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    validated = all(checks.values())
    receipt = {
        "schema": RUNTIME_REFLECTION_BEHAVIOR_SCHEMA,
        "status": "validated" if validated else "rejected",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"]
        },
        "inputs": plan["inputs"],
        "selected_owner_only": selected,
        "type_selected_owner_only": type_selected,
        "type_extended_selected_owner_only": type_extended_selected,
        "remaining_selected_owner_only": remaining_selected,
        "candidate_observations_owner_only": {
            "bool": bool_candidates,
            "zero": zero_candidates,
        },
        "operation_count": len(plan["contract"]["operation_keys"])
        if validated
        else 0,
        "checks": checks,
        "owner_only": True,
    }
    _private_json(
        output_dir / "runtime-reflection-behavior-receipt.private.json",
        receipt,
    )
    return {
        "schema": RUNTIME_REFLECTION_BEHAVIOR_SCHEMA,
        "status": receipt["status"],
        "target": receipt["target"],
        "operation_count": receipt["operation_count"],
        "operation_keys": (
            list(plan["contract"]["operation_keys"])
            if validated
            else []
        ),
        "live_event_object_count": status.get("live_event_object_count", 0),
        "fresh_method_object_count": status.get(
            "fresh_method_object_count", 0
        ),
        "checks": checks,
        "raw_pointers_and_candidate_indexes_exposed": False,
    }
