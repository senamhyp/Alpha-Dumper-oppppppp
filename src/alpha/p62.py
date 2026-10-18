import hashlib
import json
import os
import struct
import tempfile
import zlib
from pathlib import Path
from typing import Any

from alpha.p61 import validate_dump_ir
from alpha.h01 import AcquisitionError
from alpha.p01 import reflection_contract
from alpha.h02 import file_identity


SYNTHETIC_ASSEMBLY_SCHEMA = "alpha.synthetic-gameassembly/v1"
SYNTHETIC_PAYLOAD_MAGIC = b"BALV2GA1"
SYNTHETIC_PAYLOAD_VERSION = 1
SYNTHETIC_PAYLOAD_HEADER = struct.Struct("<8sIIQQ32s32s32s")
_FILE_ALIGNMENT = 0x200
_SECTION_ALIGNMENT = 0x1000
_IMAGE_BASE = 0x140000000
_SECTION_NAME = b".bal\0\0\0\0"


def _align(value: int, alignment: int) -> int:
    return (value + alignment - 1) & ~(alignment - 1)


def _canonical_ir(payload: dict[str, Any]) -> bytes:
    validate_dump_ir(payload)
    return json.dumps(
        payload,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def _atomic_bytes(path: Path, data: bytes) -> None:
    path = path.expanduser().resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "wb") as sink:
            sink.write(data)
            sink.flush()
            os.fsync(sink.fileno())
        os.replace(temporary_path, path)
    finally:
        temporary_path.unlink(missing_ok=True)


def _pe_image(section_payload: bytes) -> bytes:
    raw_size = _align(len(section_payload), _FILE_ALIGNMENT)
    headers_size = _FILE_ALIGNMENT
    image_size = _align(0x1000 + len(section_payload), _SECTION_ALIGNMENT)
    dos = bytearray(0x80)
    struct.pack_into("<H", dos, 0, 0x5A4D)
    struct.pack_into("<I", dos, 0x3C, 0x80)
    coff = struct.pack(
        "<HHIIIHH",
        0x8664,
        1,
        0,
        0,
        0,
        0xF0,
        0x2022,
    )
    optional = bytearray(0xF0)
    struct.pack_into("<HBB", optional, 0, 0x20B, 14, 0)
    struct.pack_into("<III", optional, 4, 0, raw_size, 0)
    struct.pack_into("<II", optional, 16, 0, 0)
    struct.pack_into("<Q", optional, 24, _IMAGE_BASE)
    struct.pack_into("<II", optional, 32, _SECTION_ALIGNMENT, _FILE_ALIGNMENT)
    struct.pack_into("<HHHHHH", optional, 40, 6, 0, 0, 0, 6, 0)
    struct.pack_into("<I", optional, 52, 0)
    struct.pack_into("<III", optional, 56, image_size, headers_size, 0)
    struct.pack_into("<HH", optional, 68, 3, 0)
    struct.pack_into(
        "<QQQQII",
        optional,
        72,
        0x100000,
        0x1000,
        0x100000,
        0x1000,
        0,
        16,
    )
    section = struct.pack(
        "<8sIIIIIIHHI",
        _SECTION_NAME,
        len(section_payload),
        0x1000,
        raw_size,
        headers_size,
        0,
        0,
        0,
        0,
        0x40000040,
    )
    headers = bytes(dos) + b"PE\0\0" + coff + bytes(optional) + section
    if len(headers) > headers_size:
        raise AcquisitionError("synthetic assembly PE headers overflowed")
    return (
        headers
        + bytes(headers_size - len(headers))
        + section_payload
        + bytes(raw_size - len(section_payload))
    )


def build_synthetic_gameassembly(
    payload: dict[str, Any],
    *,
    output: Path,
) -> dict[str, Any]:
    raw_ir = _canonical_ir(payload)
    compressed = zlib.compress(raw_ir, level=9)
    contract_digest = bytes.fromhex(
        reflection_contract()["contract_id"].rsplit(":", 1)[-1]
    )
    executable_digest = bytes.fromhex(payload["target"]["executable_sha256"])
    ir_digest = hashlib.sha256(raw_ir).digest()
    section_payload = SYNTHETIC_PAYLOAD_HEADER.pack(
        SYNTHETIC_PAYLOAD_MAGIC,
        SYNTHETIC_PAYLOAD_VERSION,
        SYNTHETIC_PAYLOAD_HEADER.size,
        len(raw_ir),
        len(compressed),
        executable_digest,
        contract_digest,
        ir_digest,
    ) + compressed
    output = output.expanduser().resolve()
    _atomic_bytes(output, _pe_image(section_payload))
    return inspect_synthetic_gameassembly(
        output,
        expected_executable_sha256=payload["target"]["executable_sha256"],
    )


def inspect_synthetic_gameassembly(
    path: Path,
    *,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("synthetic GameAssembly is unavailable")
    data = path.read_bytes()
    if len(data) < _FILE_ALIGNMENT + SYNTHETIC_PAYLOAD_HEADER.size:
        raise AcquisitionError("synthetic GameAssembly is truncated")
    if data[:2] != b"MZ":
        raise AcquisitionError("synthetic GameAssembly DOS header is invalid")
    pe_offset = struct.unpack_from("<I", data, 0x3C)[0]
    if data[pe_offset : pe_offset + 4] != b"PE\0\0":
        raise AcquisitionError("synthetic GameAssembly PE signature is invalid")
    machine, section_count = struct.unpack_from("<HH", data, pe_offset + 4)
    optional_bytes = struct.unpack_from("<H", data, pe_offset + 4 + 16)[0]
    optional_offset = pe_offset + 4 + 20
    if (
        machine != 0x8664
        or section_count != 1
        or optional_bytes != 0xF0
        or struct.unpack_from("<H", data, optional_offset)[0] != 0x20B
    ):
        raise AcquisitionError("synthetic GameAssembly architecture is invalid")
    section_offset = optional_offset + optional_bytes
    name, virtual_bytes, _virtual_rva, raw_bytes, raw_offset = struct.unpack_from(
        "<8sIIII", data, section_offset
    )
    if (
        name != _SECTION_NAME
        or not virtual_bytes
        or raw_offset != _FILE_ALIGNMENT
        or raw_bytes < virtual_bytes
        or raw_offset + raw_bytes != len(data)
    ):
        raise AcquisitionError("synthetic GameAssembly BAL section is invalid")
    section = data[raw_offset : raw_offset + virtual_bytes]
    (
        magic,
        version,
        header_bytes,
        uncompressed_bytes,
        compressed_bytes,
        executable_digest,
        contract_digest,
        ir_digest,
    ) = SYNTHETIC_PAYLOAD_HEADER.unpack_from(section)
    expected_contract = bytes.fromhex(
        reflection_contract()["contract_id"].rsplit(":", 1)[-1]
    )
    if (
        magic != SYNTHETIC_PAYLOAD_MAGIC
        or version != SYNTHETIC_PAYLOAD_VERSION
        or header_bytes != SYNTHETIC_PAYLOAD_HEADER.size
        or compressed_bytes != len(section) - header_bytes
        or contract_digest != expected_contract
    ):
        raise AcquisitionError("synthetic GameAssembly payload binding is invalid")
    executable_sha256 = executable_digest.hex()
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.casefold()
    ):
        raise AcquisitionError("synthetic GameAssembly target binding is stale")
    try:
        raw_ir = zlib.decompress(section[header_bytes:])
        payload = json.loads(raw_ir.decode("utf-8"))
    except (zlib.error, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AcquisitionError("synthetic GameAssembly payload is invalid") from error
    if (
        len(raw_ir) != uncompressed_bytes
        or hashlib.sha256(raw_ir).digest() != ir_digest
        or not isinstance(payload, dict)
        or payload.get("target", {}).get("executable_sha256") != executable_sha256
    ):
        raise AcquisitionError("synthetic GameAssembly IR integrity is invalid")
    totals = validate_dump_ir(payload)
    return {
        "schema": SYNTHETIC_ASSEMBLY_SCHEMA,
        "status": "complete",
        "identity": file_identity(path),
        "target": {"executable_sha256": executable_sha256},
        "reflection_contract_id": reflection_contract()["contract_id"],
        "ir_sha256": ir_digest.hex(),
        "ir_bytes": len(raw_ir),
        "compressed_ir_bytes": compressed_bytes,
        "counts": totals,
        "section_name": ".bal",
        "valid_pe32_plus": True,
        "fixed_target_address_used": False,
        "external_runtime_component_used": False,
    }
