import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.p01 import reflection_contract
from alpha.p02 import runtime_inventory_contract
from alpha.p04 import load_runtime_member_detail_observation
from alpha.p08 import load_runtime_method_native_observation
from alpha.p06 import load_runtime_type_graph_observation
from alpha.h02 import file_identity, sha256_file


RUNTIME_FIELD_NATIVE_SCHEMA = "alpha.runtime-field-native-observation/v1"
RUNTIME_FIELD_NATIVE_MAGIC = b"ALPHAFN1"
RUNTIME_FIELD_NATIVE_VERSION = 1
RUNTIME_FIELD_NATIVE_HEADER = struct.Struct(
    "<8sIIII64s64s64s64s64s64sQQIIII"
)
RUNTIME_FIELD_NATIVE_ENTRY = struct.Struct("<QQQQIIII")
MAXIMUM_FIELD_METADATA_STRIDE = 256
FIELD_ATTRIBUTE_STATIC = 0x10
FIELD_ATTRIBUTE_LITERAL = 0x40
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime field native {label} is invalid"
        ) from error
    if not _SHA256.fullmatch(value):
        raise AcquisitionError(f"runtime field native {label} is invalid")
    return value


def load_runtime_field_native_observation(
    path: Path,
    *,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    type_graph_observation_path: Path,
    method_native_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    member_detail_observation_path = (
        member_detail_observation_path.expanduser().resolve()
    )
    type_graph_observation_path = type_graph_observation_path.expanduser().resolve()
    method_native_observation_path = (
        method_native_observation_path.expanduser().resolve()
    )
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime field native observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError("runtime field native observation is not owner-only")
    details = load_runtime_member_detail_observation(
        member_detail_observation_path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    graph = load_runtime_type_graph_observation(
        type_graph_observation_path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        member_detail_observation_path=member_detail_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    methods = load_runtime_method_native_observation(
        method_native_observation_path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        member_detail_observation_path=member_detail_observation_path,
        type_graph_observation_path=type_graph_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    try:
        data = path.read_bytes()
    except OSError as error:
        raise AcquisitionError(
            "runtime field native observation is unreadable"
        ) from error
    if len(data) < RUNTIME_FIELD_NATIVE_HEADER.size:
        raise AcquisitionError("runtime field native observation is truncated")
    (
        magic,
        version,
        header_bytes,
        pointer_bytes,
        reserved,
        executable_raw,
        reflection_raw,
        inventory_raw,
        details_raw,
        graph_raw,
        methods_raw,
        type_count,
        field_count,
        metadata_stride,
        offset_dword_index,
        token_dword_index,
        reserved_two,
    ) = RUNTIME_FIELD_NATIVE_HEADER.unpack_from(data)
    executable_sha256 = _digest(executable_raw, label="target digest")
    reflection_sha256 = _digest(reflection_raw, label="reflection digest")
    inventory_sha256 = _digest(inventory_raw, label="inventory digest")
    details_sha256 = _digest(details_raw, label="member-detail digest")
    graph_sha256 = _digest(graph_raw, label="type-graph digest")
    methods_sha256 = _digest(methods_raw, label="method-native digest")
    reflection = reflection_contract()
    inventory = runtime_inventory_contract()
    if (
        magic != RUNTIME_FIELD_NATIVE_MAGIC
        or version != RUNTIME_FIELD_NATIVE_VERSION
        or header_bytes != RUNTIME_FIELD_NATIVE_HEADER.size
        or pointer_bytes != 8
        or reserved
        or reserved_two
        or executable_sha256 != details["target"]["executable_sha256"]
        or executable_sha256 != graph["target"]["executable_sha256"]
        or executable_sha256 != methods["target"]["executable_sha256"]
        or reflection_sha256
        != reflection["contract_id"].rsplit(":", 1)[-1]
        or inventory_sha256 != inventory["contract_id"].rsplit(":", 1)[-1]
        or details_sha256 != sha256_file(member_detail_observation_path)
        or graph_sha256 != sha256_file(type_graph_observation_path)
        or methods_sha256 != sha256_file(method_native_observation_path)
        or type_count != details["type_count"]
        or field_count != details["counts"]["fields"]
        or metadata_stride < 24
        or metadata_stride > MAXIMUM_FIELD_METADATA_STRIDE
        or metadata_stride % 8
        or offset_dword_index >= metadata_stride // 4
        or token_dword_index >= metadata_stride // 4
        or offset_dword_index == token_dword_index
    ):
        raise AcquisitionError("runtime field native header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime field native target binding is stale")
    expected_fields = [
        field
        for type_record in details["types"]
        for field in type_record["fields"]
    ]
    position = header_bytes
    records: list[dict[str, Any]] = []
    metadata_objects: set[int] = set()
    static_count = 0
    literal_count = 0
    for field_index, expected in enumerate(expected_fields):
        end = position + RUNTIME_FIELD_NATIVE_ENTRY.size
        if end > len(data):
            raise AcquisitionError("runtime field native entry is truncated")
        (
            member_object,
            metadata_object,
            declaring_class,
            type_handle,
            field_offset,
            metadata_token,
            attributes,
            entry_reserved,
        ) = RUNTIME_FIELD_NATIVE_ENTRY.unpack_from(data, position)
        position = end
        if (
            member_object != expected["member_object"]
            or not metadata_object
            or metadata_object & 7
            or metadata_object in metadata_objects
            or not declaring_class
            or declaring_class & 7
            or not type_handle
            or type_handle & 7
            or metadata_token != expected["metadata_token"]
            or attributes != expected["attributes"]
            or entry_reserved
        ):
            raise AcquisitionError("runtime field native entry is invalid")
        metadata_objects.add(metadata_object)
        if attributes & FIELD_ATTRIBUTE_STATIC:
            static_count += 1
        if attributes & FIELD_ATTRIBUTE_LITERAL:
            literal_count += 1
        records.append(
            {
                "field_index": field_index,
                "member_object": member_object,
                "metadata_object": metadata_object,
                "declaring_class": declaring_class,
                "type_handle": type_handle,
                "offset": field_offset,
                "metadata_token": metadata_token,
                "attributes": attributes,
            }
        )
    if position != len(data):
        raise AcquisitionError("runtime field native observation has a trailer")
    return {
        "schema": RUNTIME_FIELD_NATIVE_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contracts": {
            "reflection_contract_id": reflection["contract_id"],
            "inventory_contract_id": inventory["contract_id"],
            "member_detail_observation_sha256": details_sha256,
            "type_graph_observation_sha256": graph_sha256,
            "method_native_observation_sha256": methods_sha256,
        },
        "type_count": type_count,
        "field_count": field_count,
        "static_field_count": static_count,
        "literal_field_count": literal_count,
        "metadata_stride": metadata_stride,
        "offset_dword_index": offset_dword_index,
        "token_dword_index": token_dword_index,
        "fields": records,
        "identity": file_identity(path),
        "raw_native_addresses_owner_only": True,
    }


def inspect_runtime_field_native_observation(
    path: Path,
    *,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    type_graph_observation_path: Path,
    method_native_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_field_native_observation(
        path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        member_detail_observation_path=member_detail_observation_path,
        type_graph_observation_path=type_graph_observation_path,
        method_native_observation_path=method_native_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_FIELD_NATIVE_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contracts": model["contracts"],
        "type_count": model["type_count"],
        "field_count": model["field_count"],
        "static_field_count": model["static_field_count"],
        "literal_field_count": model["literal_field_count"],
        "identity": model["identity"],
        "raw_native_addresses_exposed": False,
    }
