import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.p01 import reflection_contract
from alpha.p02 import runtime_inventory_contract
from alpha.p10 import load_runtime_metadata_usage_observation
from alpha.p08 import MAXIMUM_NATIVE_IMAGE_BYTES
from alpha.p07 import load_runtime_type_native_observation
from alpha.h02 import file_identity, sha256_file


RUNTIME_TYPE_METADATA_USAGE_SCHEMA = (
    "alpha.runtime-type-metadata-usage-observation/v1"
)
RUNTIME_TYPE_METADATA_USAGE_MAGIC = b"ALPHATU1"
RUNTIME_TYPE_METADATA_USAGE_VERSION = 1
RUNTIME_TYPE_METADATA_USAGE_HEADER = struct.Struct(
    "<8sIIII64s64s64s64s64s64sQQQQQII"
)
RUNTIME_TYPE_METADATA_USAGE_ENTRY = struct.Struct("<IIQ")
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime type metadata usage {label} is invalid"
        ) from error
    if not _SHA256.fullmatch(value):
        raise AcquisitionError(f"runtime type metadata usage {label} is invalid")
    return value


def load_runtime_type_metadata_usage_observation(
    path: Path,
    *,
    metadata_path: Path,
    metadata_usage_observation_path: Path,
    type_native_observation_path: Path,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    type_graph_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    metadata_usage_observation_path = (
        metadata_usage_observation_path.expanduser().resolve()
    )
    type_native_observation_path = type_native_observation_path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError(
            "runtime type metadata usage observation is unavailable"
        )
    if owner_only_path_bits(path):
        raise AcquisitionError(
            "runtime type metadata usage observation is not owner-only"
        )
    usages = load_runtime_metadata_usage_observation(
        metadata_usage_observation_path,
        metadata_path=metadata_path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        member_detail_observation_path=member_detail_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    types = load_runtime_type_native_observation(
        type_native_observation_path,
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
            "runtime type metadata usage observation is unreadable"
        ) from error
    if len(data) < RUNTIME_TYPE_METADATA_USAGE_HEADER.size:
        raise AcquisitionError(
            "runtime type metadata usage observation is truncated"
        )
    (
        magic,
        version,
        header_bytes,
        pointer_bytes,
        reserved,
        executable_raw,
        metadata_raw,
        reflection_raw,
        inventory_raw,
        type_native_raw,
        metadata_usage_raw,
        image_base,
        image_bytes,
        types_array_rva,
        type_count,
        type_usage_count,
        matching_array_count,
        reserved_two,
    ) = RUNTIME_TYPE_METADATA_USAGE_HEADER.unpack_from(data)
    executable_sha256 = _digest(executable_raw, label="target digest")
    metadata_sha256 = _digest(metadata_raw, label="metadata digest")
    reflection_sha256 = _digest(reflection_raw, label="reflection digest")
    inventory_sha256 = _digest(inventory_raw, label="inventory digest")
    type_native_sha256 = _digest(type_native_raw, label="type-native digest")
    metadata_usage_sha256 = _digest(
        metadata_usage_raw, label="metadata-usage digest"
    )
    reflection = reflection_contract()
    inventory = runtime_inventory_contract()
    expected_usages = [
        record for record in usages["usages"] if record["usage_kind"] == 1
    ]
    array_bytes = type_count * pointer_bytes
    maximum_source = max(
        (record["source_index"] for record in expected_usages), default=-1
    )
    if (
        magic != RUNTIME_TYPE_METADATA_USAGE_MAGIC
        or version != RUNTIME_TYPE_METADATA_USAGE_VERSION
        or header_bytes != RUNTIME_TYPE_METADATA_USAGE_HEADER.size
        or pointer_bytes != 8
        or reserved
        or reserved_two
        or executable_sha256 != usages["target"]["executable_sha256"]
        or executable_sha256 != types["target"]["executable_sha256"]
        or metadata_sha256 != usages["contracts"]["metadata_sha256"]
        or reflection_sha256
        != reflection["contract_id"].rsplit(":", 1)[-1]
        or inventory_sha256 != inventory["contract_id"].rsplit(":", 1)[-1]
        or type_native_sha256 != sha256_file(type_native_observation_path)
        or metadata_usage_sha256 != sha256_file(metadata_usage_observation_path)
        or not image_base
        or image_base & 0xFFFF
        or not 0 < image_bytes <= MAXIMUM_NATIVE_IMAGE_BYTES
        or not type_count
        or type_count > image_bytes // pointer_bytes
        or maximum_source < 0
        or type_count <= maximum_source
        or types_array_rva & 7
        or types_array_rva >= image_bytes
        or array_bytes > image_bytes - types_array_rva
        or type_usage_count != len(expected_usages)
        or not type_usage_count
        or matching_array_count != 1
    ):
        raise AcquisitionError("runtime type metadata usage header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError(
            "runtime type metadata usage target binding is stale"
        )
    expected_bytes = (
        header_bytes + type_usage_count * RUNTIME_TYPE_METADATA_USAGE_ENTRY.size
    )
    if len(data) != expected_bytes:
        raise AcquisitionError(
            "runtime type metadata usage observation extent is invalid"
        )
    nodes_by_handle = {
        record["type_handle"]: record for record in types["nodes"]
    }
    position = header_bytes
    records: list[dict[str, int]] = []
    selected_handles: set[int] = set()
    for expected in expected_usages:
        destination_index, source_index, type_handle = (
            RUNTIME_TYPE_METADATA_USAGE_ENTRY.unpack_from(data, position)
        )
        position += RUNTIME_TYPE_METADATA_USAGE_ENTRY.size
        node = nodes_by_handle.get(type_handle)
        if (
            destination_index != expected["destination_index"]
            or source_index != expected["source_index"]
            or node is None
            or type_handle in selected_handles
        ):
            raise AcquisitionError(
                "runtime type metadata usage entry is invalid"
            )
        selected_handles.add(type_handle)
        records.append(
            {
                "destination_index": destination_index,
                "source_index": source_index,
                "rva": expected["rva"],
                "node_index": node["node_index"],
                "type_object": node["type_object"],
                "type_handle": type_handle,
            }
        )
    if position != len(data) or len(selected_handles) != type_usage_count:
        raise AcquisitionError(
            "runtime type metadata usage observation is incomplete"
        )
    return {
        "schema": RUNTIME_TYPE_METADATA_USAGE_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contracts": {
            "metadata_sha256": metadata_sha256,
            "reflection_contract_id": reflection["contract_id"],
            "inventory_contract_id": inventory["contract_id"],
            "type_native_observation_sha256": type_native_sha256,
            "metadata_usage_observation_sha256": metadata_usage_sha256,
        },
        "image_base": image_base,
        "image_bytes": image_bytes,
        "types_array_rva": types_array_rva,
        "type_count": type_count,
        "type_usage_count": type_usage_count,
        "matching_array_count": matching_array_count,
        "types": records,
        "identity": file_identity(path),
        "fixed_address_seed_used": False,
        "fixed_type_count_seed_used": False,
        "raw_native_addresses_owner_only": True,
    }


def inspect_runtime_type_metadata_usage_observation(
    path: Path,
    **arguments: Any,
) -> dict[str, Any]:
    model = load_runtime_type_metadata_usage_observation(path, **arguments)
    return {
        "schema": RUNTIME_TYPE_METADATA_USAGE_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contracts": model["contracts"],
        "type_count": model["type_count"],
        "type_usage_count": model["type_usage_count"],
        "matching_array_count": model["matching_array_count"],
        "identity": model["identity"],
        "fixed_address_seed_used": False,
        "fixed_type_count_seed_used": False,
        "raw_native_addresses_exposed": False,
    }
