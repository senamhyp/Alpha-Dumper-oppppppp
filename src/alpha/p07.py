import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.p01 import reflection_contract
from alpha.p02 import runtime_inventory_contract
from alpha.p06 import load_runtime_type_graph_observation
from alpha.h02 import file_identity, sha256_file


RUNTIME_TYPE_NATIVE_SCHEMA = "alpha.runtime-type-native-observation/v1"
RUNTIME_TYPE_NATIVE_MAGIC = b"ALPHATN1"
RUNTIME_TYPE_NATIVE_VERSION = 1
RUNTIME_TYPE_NATIVE_HEADER = struct.Struct("<8sIIII64s64s64s64sQQ")
RUNTIME_TYPE_NATIVE_ENTRY = struct.Struct("<QQ")
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(f"runtime type native {label} is invalid") from error
    if not _SHA256.fullmatch(value):
        raise AcquisitionError(f"runtime type native {label} is invalid")
    return value


def load_runtime_type_native_observation(
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
    type_graph_observation_path = type_graph_observation_path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime type native observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError("runtime type native observation is not owner-only")
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
        raise AcquisitionError("runtime type native observation is unreadable") from error
    if len(data) < RUNTIME_TYPE_NATIVE_HEADER.size:
        raise AcquisitionError("runtime type native observation is truncated")
    (
        magic,
        version,
        header_bytes,
        pointer_bytes,
        reserved,
        executable_raw,
        reflection_raw,
        inventory_raw,
        graph_raw,
        node_count,
        unique_handle_count,
    ) = RUNTIME_TYPE_NATIVE_HEADER.unpack_from(data)
    executable_sha256 = _digest(executable_raw, label="target digest")
    reflection_sha256 = _digest(reflection_raw, label="reflection digest")
    inventory_sha256 = _digest(inventory_raw, label="inventory digest")
    graph_sha256 = _digest(graph_raw, label="type-graph digest")
    reflection = reflection_contract()
    inventory = runtime_inventory_contract()
    if (
        magic != RUNTIME_TYPE_NATIVE_MAGIC
        or version != RUNTIME_TYPE_NATIVE_VERSION
        or header_bytes != RUNTIME_TYPE_NATIVE_HEADER.size
        or pointer_bytes != 8
        or reserved
        or executable_sha256 != graph["target"]["executable_sha256"]
        or reflection_sha256
        != reflection["contract_id"].rsplit(":", 1)[-1]
        or inventory_sha256 != inventory["contract_id"].rsplit(":", 1)[-1]
        or graph_sha256 != sha256_file(type_graph_observation_path)
        or node_count != graph["node_count"]
        or unique_handle_count != node_count
    ):
        raise AcquisitionError("runtime type native header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime type native target binding is stale")
    expected_bytes = header_bytes + node_count * RUNTIME_TYPE_NATIVE_ENTRY.size
    if len(data) != expected_bytes:
        raise AcquisitionError("runtime type native observation extent is invalid")
    position = header_bytes
    handles: set[int] = set()
    records: list[dict[str, int]] = []
    for node_index, expected in enumerate(graph["nodes"]):
        type_object, type_handle = RUNTIME_TYPE_NATIVE_ENTRY.unpack_from(data, position)
        position += RUNTIME_TYPE_NATIVE_ENTRY.size
        if (
            type_object != expected["type_object"]
            or not type_handle
            or type_handle & 7
            or type_handle in handles
        ):
            raise AcquisitionError("runtime type native entry is invalid")
        handles.add(type_handle)
        records.append(
            {
                "node_index": node_index,
                "type_object": type_object,
                "type_handle": type_handle,
            }
        )
    if position != len(data) or len(handles) != node_count:
        raise AcquisitionError("runtime type native observation is incomplete")
    return {
        "schema": RUNTIME_TYPE_NATIVE_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contracts": {
            "reflection_contract_id": reflection["contract_id"],
            "inventory_contract_id": inventory["contract_id"],
            "type_graph_observation_sha256": graph_sha256,
        },
        "node_count": node_count,
        "unique_handle_count": len(handles),
        "nodes": records,
        "identity": file_identity(path),
        "raw_native_addresses_owner_only": True,
    }


def inspect_runtime_type_native_observation(
    path: Path,
    **arguments: Any,
) -> dict[str, Any]:
    model = load_runtime_type_native_observation(path, **arguments)
    return {
        "schema": RUNTIME_TYPE_NATIVE_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contracts": model["contracts"],
        "node_count": model["node_count"],
        "unique_handle_count": model["unique_handle_count"],
        "identity": model["identity"],
        "raw_native_addresses_exposed": False,
    }
