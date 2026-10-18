import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.p01 import reflection_contract
from alpha.p02 import runtime_inventory_contract
from alpha.p06 import discover_runtime_metadata_mapping
from alpha.p08 import MAXIMUM_NATIVE_IMAGE_BYTES
from alpha.h02 import file_identity, sha256_file


RUNTIME_METADATA_USAGE_SCHEMA = "alpha.runtime-metadata-usage-observation/v1"
RUNTIME_METADATA_USAGE_MAGIC = b"ALPHAMU1"
RUNTIME_METADATA_USAGE_VERSION = 1
RUNTIME_METADATA_USAGE_HEADER = struct.Struct(
    "<8sIIII64s64s64s64s64s64sQQQQII"
)
RUNTIME_METADATA_USAGE_ENTRY = struct.Struct("<Q")
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime metadata usage {label} is invalid"
        ) from error
    if not _SHA256.fullmatch(value):
        raise AcquisitionError(f"runtime metadata usage {label} is invalid")
    return value


def load_runtime_metadata_usage_observation(
    path: Path,
    *,
    metadata_path: Path,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    metadata_path = metadata_path.expanduser().resolve()
    type_identity_observation_path = (
        type_identity_observation_path.expanduser().resolve()
    )
    member_detail_observation_path = (
        member_detail_observation_path.expanduser().resolve()
    )
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime metadata usage observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError(
            "runtime metadata usage observation is not owner-only"
        )
    mapping = discover_runtime_metadata_mapping(
        metadata_path=metadata_path,
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
            "runtime metadata usage observation is unreadable"
        ) from error
    if len(data) < RUNTIME_METADATA_USAGE_HEADER.size:
        raise AcquisitionError("runtime metadata usage observation is truncated")
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
        identity_raw,
        detail_raw,
        image_base,
        image_bytes,
        usage_count,
        metadata_usage_array_rva,
        unique_slot_count,
        matching_array_count,
    ) = RUNTIME_METADATA_USAGE_HEADER.unpack_from(data)
    executable_sha256 = _digest(executable_raw, label="target digest")
    metadata_sha256 = _digest(metadata_raw, label="metadata digest")
    reflection_sha256 = _digest(reflection_raw, label="reflection digest")
    inventory_sha256 = _digest(inventory_raw, label="inventory digest")
    identity_sha256 = _digest(identity_raw, label="type-identity digest")
    detail_sha256 = _digest(detail_raw, label="member-detail digest")
    reflection = reflection_contract()
    inventory = runtime_inventory_contract()
    expected_usage_count = mapping["counts"]["metadata_usage_count"]
    array_bytes = usage_count * RUNTIME_METADATA_USAGE_ENTRY.size
    if (
        magic != RUNTIME_METADATA_USAGE_MAGIC
        or version != RUNTIME_METADATA_USAGE_VERSION
        or header_bytes != RUNTIME_METADATA_USAGE_HEADER.size
        or pointer_bytes != RUNTIME_METADATA_USAGE_ENTRY.size
        or reserved
        or executable_sha256 != mapping["target"]["executable_sha256"]
        or metadata_sha256 != mapping["metadata"]["sha256"]
        or reflection_sha256
        != reflection["contract_id"].rsplit(":", 1)[-1]
        or inventory_sha256 != inventory["contract_id"].rsplit(":", 1)[-1]
        or identity_sha256 != sha256_file(type_identity_observation_path)
        or detail_sha256 != sha256_file(member_detail_observation_path)
        or not image_base
        or image_base & 0xFFFF
        or not 0 < image_bytes <= MAXIMUM_NATIVE_IMAGE_BYTES
        or not usage_count
        or usage_count != expected_usage_count
        or usage_count > image_bytes // RUNTIME_METADATA_USAGE_ENTRY.size
        or metadata_usage_array_rva & 7
        or metadata_usage_array_rva >= image_bytes
        or array_bytes > image_bytes - metadata_usage_array_rva
        or unique_slot_count != usage_count
        or matching_array_count != 1
    ):
        raise AcquisitionError("runtime metadata usage header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime metadata usage target binding is stale")
    expected_bytes = header_bytes + array_bytes
    if len(data) != expected_bytes:
        raise AcquisitionError(
            "runtime metadata usage observation extent is invalid"
        )
    image_end = image_base + image_bytes
    if image_end <= image_base:
        raise AcquisitionError("runtime metadata usage image extent is invalid")
    usages: list[dict[str, Any]] = []
    slot_pointers: set[int] = set()
    position = header_bytes
    for pair in mapping["metadata_usage_pairs"]:
        slot_pointer = RUNTIME_METADATA_USAGE_ENTRY.unpack_from(data, position)[0]
        position += RUNTIME_METADATA_USAGE_ENTRY.size
        if (
            slot_pointer < image_base
            or slot_pointer >= image_end
            or slot_pointer & 7
            or slot_pointer in slot_pointers
        ):
            raise AcquisitionError("runtime metadata usage slot is invalid")
        slot_pointers.add(slot_pointer)
        usages.append(
            {
                **pair,
                "slot_pointer": slot_pointer,
                "rva": slot_pointer - image_base,
            }
        )
    if position != len(data) or len(slot_pointers) != usage_count:
        raise AcquisitionError("runtime metadata usage observation is incomplete")
    return {
        "schema": RUNTIME_METADATA_USAGE_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contracts": {
            "metadata_sha256": metadata_sha256,
            "reflection_contract_id": reflection["contract_id"],
            "inventory_contract_id": inventory["contract_id"],
            "type_identity_observation_sha256": identity_sha256,
            "member_detail_observation_sha256": detail_sha256,
        },
        "usage_count": usage_count,
        "usage_kind_counts": mapping["metadata_usage_kind_counts"],
        "image_base": image_base,
        "image_bytes": image_bytes,
        "metadata_usage_array_rva": metadata_usage_array_rva,
        "matching_array_count": matching_array_count,
        "usages": usages,
        "identity": file_identity(path),
        "fixed_address_seed_used": False,
        "saved_reference_generation_seed_used": False,
        "raw_native_addresses_owner_only": True,
    }


def inspect_runtime_metadata_usage_observation(
    path: Path,
    *,
    metadata_path: Path,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_metadata_usage_observation(
        path,
        metadata_path=metadata_path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        member_detail_observation_path=member_detail_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_METADATA_USAGE_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contracts": model["contracts"],
        "usage_count": model["usage_count"],
        "usage_kind_counts": model["usage_kind_counts"],
        "matching_array_count": model["matching_array_count"],
        "identity": model["identity"],
        "fixed_address_seed_used": False,
        "saved_reference_generation_seed_used": False,
        "raw_native_addresses_exposed": False,
    }
