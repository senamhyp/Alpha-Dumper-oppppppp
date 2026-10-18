import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.p01 import reflection_contract
from alpha.p02 import runtime_inventory_contract
from alpha.p04 import load_runtime_member_detail_observation
from alpha.p06 import load_runtime_type_graph_observation
from alpha.h02 import file_identity, sha256_file


RUNTIME_METHOD_NATIVE_SCHEMA = "alpha.runtime-method-native-observation/v2"
RUNTIME_METHOD_NATIVE_MAGIC = b"ALPHAMN2"
RUNTIME_METHOD_NATIVE_VERSION = 2
RUNTIME_METHOD_NATIVE_HEADER = struct.Struct(
    "<8sIIII64s64s64s64s64sQQQQ"
)
RUNTIME_METHOD_NATIVE_ENTRY = struct.Struct("<QQQII")
MAXIMUM_NATIVE_IMAGE_BYTES = 4 * 1024 * 1024 * 1024
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime method native {label} is invalid"
        ) from error
    if not _SHA256.fullmatch(value):
        raise AcquisitionError(f"runtime method native {label} is invalid")
    return value


def load_runtime_method_native_observation(
    path: Path,
    *,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    type_graph_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    member_detail_observation_path = member_detail_observation_path.expanduser().resolve()
    type_graph_observation_path = type_graph_observation_path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime method native observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError("runtime method native observation is not owner-only")
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
    try:
        data = path.read_bytes()
    except OSError as error:
        raise AcquisitionError(
            "runtime method native observation is unreadable"
        ) from error
    if len(data) < RUNTIME_METHOD_NATIVE_HEADER.size:
        raise AcquisitionError("runtime method native observation is truncated")
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
        image_base,
        image_bytes,
        type_count,
        method_count,
    ) = RUNTIME_METHOD_NATIVE_HEADER.unpack_from(data)
    executable_sha256 = _digest(executable_raw, label="target digest")
    reflection_sha256 = _digest(reflection_raw, label="reflection digest")
    inventory_sha256 = _digest(inventory_raw, label="inventory digest")
    details_sha256 = _digest(details_raw, label="member-detail digest")
    graph_sha256 = _digest(graph_raw, label="type-graph digest")
    reflection = reflection_contract()
    inventory = runtime_inventory_contract()
    expected_method_count = details["counts"]["methods"] + details["counts"][
        "constructors"
    ]
    if (
        magic != RUNTIME_METHOD_NATIVE_MAGIC
        or version != RUNTIME_METHOD_NATIVE_VERSION
        or header_bytes != RUNTIME_METHOD_NATIVE_HEADER.size
        or pointer_bytes != 8
        or reserved != 0
        or executable_sha256 != details["target"]["executable_sha256"]
        or executable_sha256 != graph["target"]["executable_sha256"]
        or reflection_sha256
        != reflection["contract_id"].rsplit(":", 1)[-1]
        or inventory_sha256 != inventory["contract_id"].rsplit(":", 1)[-1]
        or details_sha256 != sha256_file(member_detail_observation_path)
        or graph_sha256 != sha256_file(type_graph_observation_path)
        or not image_base
        or image_base & 0xFFFF
        or not 0 < image_bytes <= MAXIMUM_NATIVE_IMAGE_BYTES
        or type_count != details["type_count"]
        or method_count != expected_method_count
    ):
        raise AcquisitionError("runtime method native header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime method native target binding is stale")
    expected_methods = [
        method
        for type_record in details["types"]
        for category in ("methods", "constructors")
        for method in type_record[category]
    ]
    position = header_bytes
    records: list[dict[str, Any]] = []
    metadata_objects: set[int] = set()
    executable_count = 0
    slotted_count = 0
    rvas: set[int] = set()
    for method_index, expected_method in enumerate(expected_methods):
        end = position + RUNTIME_METHOD_NATIVE_ENTRY.size
        if end > len(data):
            raise AcquisitionError("runtime method native entry is truncated")
        member_object, metadata_object, method_pointer, rva, slot = (
            RUNTIME_METHOD_NATIVE_ENTRY.unpack_from(data, position)
        )
        position = end
        if (
            member_object != expected_method["member_object"]
            or not metadata_object
            or metadata_object & 7
            or metadata_object in metadata_objects
            or slot > 0xFFFF
            or bool(expected_method["attributes"] & 0x40)
            != (slot != 0xFFFF)
            or bool(method_pointer) != bool(rva)
            or method_pointer
            and (
                method_pointer != image_base + rva
                or rva >= image_bytes
            )
        ):
            raise AcquisitionError("runtime method native entry is invalid")
        metadata_objects.add(metadata_object)
        if rva:
            executable_count += 1
            rvas.add(rva)
        if slot != 0xFFFF:
            slotted_count += 1
        records.append(
            {
                "method_index": method_index,
                "member_object": member_object,
                "metadata_object": metadata_object,
                "method_pointer": method_pointer or None,
                "rva": rva,
                "slot": slot if slot != 0xFFFF else None,
            }
        )
    if position != len(data):
        raise AcquisitionError("runtime method native observation has a trailer")
    return {
        "schema": RUNTIME_METHOD_NATIVE_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contracts": {
            "reflection_contract_id": reflection["contract_id"],
            "inventory_contract_id": inventory["contract_id"],
            "member_detail_observation_sha256": details_sha256,
            "type_graph_observation_sha256": graph_sha256,
        },
        "type_count": type_count,
        "method_count": method_count,
        "executable_method_count": executable_count,
        "unique_rva_count": len(rvas),
        "slotted_method_count": slotted_count,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "methods": records,
        "identity": file_identity(path),
        "raw_native_addresses_owner_only": True,
    }


def inspect_runtime_method_native_observation(
    path: Path,
    *,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    type_graph_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_method_native_observation(
        path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        member_detail_observation_path=member_detail_observation_path,
        type_graph_observation_path=type_graph_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_METHOD_NATIVE_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contracts": model["contracts"],
        "type_count": model["type_count"],
        "method_count": model["method_count"],
        "executable_method_count": model["executable_method_count"],
        "unique_rva_count": model["unique_rva_count"],
        "slotted_method_count": model["slotted_method_count"],
        "identity": model["identity"],
        "raw_native_addresses_exposed": False,
    }
