from alpha.h02 import windows_run as _host_run

import hashlib
import json
import os
import array
import stat
import struct
import subprocess
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from itertools import compress
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import (
    _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output,
    _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source,
)
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.p20 import (
    RUNTIME_METADATA_USAGE_VALUE_STATUS_SCHEMA,
    select_constructed_seeds,
)
from alpha.p20 import RUNTIME_METADATA_USAGE_VALUE_HEADER, RUNTIME_METADATA_USAGE_VALUE_MAGIC, RUNTIME_METADATA_USAGE_VALUE_VERSION
from alpha.p25 import (
    RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_RECORD,
    RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION,
    TYPE_REFERENCE_GENERIC, TYPE_REFERENCE_GENERIC_DEFINITION, TYPE_REFERENCE_SHAPE_MASK,
)
from alpha.h02 import file_identity, read_json


RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA = (
    "alpha.runtime-constructed-generic-layout/v1"
)
RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_STATUS_SCHEMA = (
    "alpha.runtime-constructed-generic-layout-status/v1"
)
RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC = b"ALPHACG1"
RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION = 1
RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER_BYTES = 264


RUNTIME_TYPE_DESCRIPTOR_VALUE_SCHEMA = (
    "alpha.runtime-type-descriptor-value-inventory/v1"
)
RUNTIME_TYPE_DESCRIPTOR_VALUE_MAGIC = b"ALPHATV1"
RUNTIME_TYPE_DESCRIPTOR_VALUE_VERSION = 1
RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER = struct.Struct(
    "<8sIIIIQQQ64s64s64s"
)
RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD = struct.Struct("<QQQQ")
RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQ64s64s64s64s"
)
RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD = struct.Struct(
    f"<QQQQQQQII{RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER_BYTES}s"
)
RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD = struct.Struct("<QQqII32s")
_ZERO_CLASS_HEADER = bytes(RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER_BYTES)
_ZERO_NATIVE_RECORD = bytes(32)

_SEED_MAGIC = b"ALPHACS1"
_SEED_VERSION = 1
_SEED_HEADER = struct.Struct("<8sIIIIQQ64s64s64s")
_SEED_RECORD = struct.Struct("<QQQQ")


_CONSTRUCTED_SEED_REFERENCE_UNIT = RUNTIME_TYPE_REFERENCE_RECORD.format[1:]
_CONSTRUCTED_SEED_VALUE_UNIT = RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.format[1:]
_CONSTRUCTED_SEED_CHUNK_ROWS = 8192


_CONSTRUCTED_SEED_SHAPE_CONTRIBUTES = tuple(
    bool(shape & TYPE_REFERENCE_GENERIC and not shape & TYPE_REFERENCE_GENERIC_DEFINITION)
    for shape in range(TYPE_REFERENCE_SHAPE_MASK + 1)
)
_CONSTRUCTED_SEED_SHAPE_REJECTED = tuple(
    bool(shape & TYPE_REFERENCE_GENERIC_DEFINITION and not shape & TYPE_REFERENCE_GENERIC)
    for shape in range(TYPE_REFERENCE_SHAPE_MASK + 1)
)


def _column_bytes(values: list[int]) -> bytes:
    return array.array("Q", values).tobytes()


def select_constructed_seeds_flat(
    reference_raw: bytes, value_raw: bytes, reference_base: int, value_base: int,
    node_count: int,
) -> list[tuple[int, int, int, int]]:
    if node_count <= 0:
        raise AcquisitionError("runtime constructed generic domain is empty")
    reference_end = reference_base + node_count * RUNTIME_TYPE_REFERENCE_RECORD.size
    value_end = value_base + node_count * RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size
    reference_descriptors: list[int] = []
    shapes: list[int] = []
    position = reference_base
    chunk = struct.Struct("<" + _CONSTRUCTED_SEED_REFERENCE_UNIT * _CONSTRUCTED_SEED_CHUNK_ROWS)
    while position < reference_end:
        count = min(_CONSTRUCTED_SEED_CHUNK_ROWS, (reference_end - position) // RUNTIME_TYPE_REFERENCE_RECORD.size)
        flat = (
            chunk if count == _CONSTRUCTED_SEED_CHUNK_ROWS
            else struct.Struct("<" + _CONSTRUCTED_SEED_REFERENCE_UNIT * count)
        ).unpack_from(reference_raw, position)
        reference_descriptors.extend(flat[0::19])
        shapes.extend(flat[4::19])
        position += count * RUNTIME_TYPE_REFERENCE_RECORD.size
    descriptors: list[int] = []
    current_pointers: list[int] = []
    datas: list[int] = []
    position = value_base
    chunk = struct.Struct("<" + _CONSTRUCTED_SEED_VALUE_UNIT * _CONSTRUCTED_SEED_CHUNK_ROWS)
    while position < value_end:
        count = min(_CONSTRUCTED_SEED_CHUNK_ROWS, (value_end - position) // RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size)
        flat = (
            chunk if count == _CONSTRUCTED_SEED_CHUNK_ROWS
            else struct.Struct("<" + _CONSTRUCTED_SEED_VALUE_UNIT * count)
        ).unpack_from(value_raw, position)
        descriptors.extend(flat[0::4])
        current_pointers.extend(flat[1::4])
        datas.extend(flat[2::4])
        position += count * RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size
    if (
        reference_descriptors != descriptors
        or 0 in descriptors
        or 0 in current_pointers
        or len(set(descriptors)) != node_count
        or len(set(current_pointers)) != node_count
        or max(shapes) > TYPE_REFERENCE_SHAPE_MASK
        or any(map(_CONSTRUCTED_SEED_SHAPE_REJECTED.__getitem__, shapes))
    ):
        return select_constructed_seeds(
            (RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
                reference_raw,
                reference_base + index * RUNTIME_TYPE_REFERENCE_RECORD.size)
             for index in range(node_count)),
            (RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.unpack_from(
                value_raw,
                value_base + index * RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size)
             for index in range(node_count)))
    alignment_bytes = b"\x07" + b"\x00" * 7
    alignment_mask = int.from_bytes(alignment_bytes * node_count, "little")
    if (
        int.from_bytes(_column_bytes(descriptors), "little") & alignment_mask
        or int.from_bytes(_column_bytes(current_pointers), "little") & alignment_mask
    ):
        return select_constructed_seeds(
            (RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
                reference_raw,
                reference_base + index * RUNTIME_TYPE_REFERENCE_RECORD.size)
             for index in range(node_count)),
            (RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.unpack_from(
                value_raw,
                value_base + index * RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size)
             for index in range(node_count)))
    contributing = list(map(_CONSTRUCTED_SEED_SHAPE_CONTRIBUTES.__getitem__, shapes))
    index_datas = list(compress(datas, contributing))


    high_mask = int.from_bytes((b"\x00" * 4 + b"\xff" * 4) * len(index_datas), "little")
    if int.from_bytes(array.array("Q", index_datas).tobytes(), "little") & high_mask:
        raise AcquisitionError("runtime constructed generic index is invalid")
    index_descriptors = list(compress(descriptors, contributing))
    index_currents = list(compress(current_pointers, contributing))
    counts = Counter(index_datas)
    first = dict(zip(
        reversed(index_datas),
        reversed(list(zip(index_descriptors, index_currents))),
    ))
    rows = {
        data: (first[data][0], first[data][1], data, counts[data])
        for data in counts
    }
    if not rows:
        raise AcquisitionError("runtime constructed generic domain is empty")
    return [rows[index] for index in sorted(rows)]


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime constructed generic {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime constructed generic {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
        raise AcquisitionError(
            f"runtime constructed generic {label} digest is invalid"
        )
    return value


def _codec(model: dict[str, Any]) -> tuple[int, int, int, int, int]:
    row = model.get("field_offset_decoder")
    if not isinstance(row, dict):
        raise AcquisitionError("runtime field offset decoder is unavailable")
    operation_name = row.get("operation", "xor")
    operations = {"xor": 1, "add": 2, "subtract": 3}
    values = (
        operations.get(operation_name),
        row.get("raw_dword_offset"),
        row.get("xor_key"),
        row.get("mask"),
        row.get("adjustment"),
    )
    if any(not isinstance(value, int) for value in values):
        raise AcquisitionError("runtime field offset decoder is invalid")
    operation, raw_offset, key, mask, adjustment = values
    if (
        operation not in (1, 2, 3)
        or not 0 <= raw_offset <= 28
        or raw_offset & 3
        or not 0 <= key <= 0xFFFFFFFF
        or not 0 < mask <= 0xFFFFFFFF
        or not -(1 << 31) <= adjustment < (1 << 31)
    ):
        raise AcquisitionError("runtime field offset decoder is invalid")
    return operation, raw_offset, key, mask, adjustment


def _binding(
    *, binary: Path, native_helper_model: Path, native_semantics_model: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    descriptor_value_model: Path, descriptor_value_inventory: Path,
    metadata_usage_value_model: Path, metadata_usage_value_inventory: Path,
    metadata_usage_value_status: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    identity = file_identity(binary)
    helper_path = _owner_file(native_helper_model, label="native helper model")
    semantics_path = _owner_file(
        native_semantics_model, label="native semantics model"
    )
    reference_model_path = _owner_file(
        type_reference_model, label="type reference model"
    )
    reference_path = _owner_file(
        type_reference_inventory, label="type reference inventory"
    )
    value_model_path = _owner_file(
        descriptor_value_model, label="descriptor value model"
    )
    value_path = _owner_file(
        descriptor_value_inventory, label="descriptor value inventory"
    )
    usage_model_path = _owner_file(
        metadata_usage_value_model, label="metadata usage value model"
    )
    usage_path = _owner_file(
        metadata_usage_value_inventory,
        label="metadata usage value inventory",
    )
    usage_status_path = _owner_file(
        metadata_usage_value_status,
        label="metadata usage value status receipt",
    )
    helper = read_json(helper_path)
    semantics = read_json(semantics_path)
    reference_model = read_json(reference_model_path)
    value_model = read_json(value_model_path)
    usage_model = read_json(usage_model_path)
    usage_status = read_json(usage_status_path)
    get_fields = (
        helper.get("helpers", {}).get("class_get_fields", {})
        if isinstance(helper, dict) else {}
    )
    if (
        not isinstance(helper, dict)
        or helper.get("binary", {}).get("sha256") != identity["sha256"]
        or get_fields.get("runtime_validated") is not True
        or not isinstance(get_fields.get("function_rva"), int)
        or not 0 < get_fields["function_rva"] < identity["bytes"]
        or get_fields.get("record_stride") != 32
    ):
        raise AcquisitionError("runtime class field helper binding is stale")
    if (
        not isinstance(semantics, dict)
        or semantics.get("binary", {}).get("sha256") != identity["sha256"]
        or semantics.get("checks", {}).get(
            "field_offset_decoder_closes_over_all_records"
        ) is not True
    ):
        raise AcquisitionError("runtime native semantics binding is stale")
    if (
        not isinstance(reference_model, dict)
        or reference_model.get("schema") != RUNTIME_TYPE_REFERENCE_SCHEMA
        or reference_model.get("status") != "runtime-validated"
        or reference_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or reference_model.get("inventory", {}).get("sha256")
        != file_identity(reference_path)["sha256"]
        or not all(reference_model.get("checks", {}).values())
    ):
        raise AcquisitionError("runtime type reference binding is stale")
    if (
        not isinstance(value_model, dict)
        or value_model.get("schema") != RUNTIME_TYPE_DESCRIPTOR_VALUE_SCHEMA
        or value_model.get("status") != "runtime-validated"
        or value_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or value_model.get("inventory", {}).get("sha256")
        != file_identity(value_path)["sha256"]
        or value_model.get("inputs", {}).get(
            "type_reference_inventory", {}
        ).get("sha256") != file_identity(reference_path)["sha256"]
        or any(
            value_model.get("checks", {}).get(key) is not True
            for key in (
                "all_current_pointers_unique",
                "all_descriptor_values_read_from_current_process",
                "all_descriptors_unique",
                "executable_bound",
                "fresh_runtime_observation",
                "node_count_exact",
                "reference_bound",
                "rows_structurally_valid",
                "size_exact",
            )
        )
        or value_model.get("checks", {}).get("fixed_address_used") is not False
        or value_model.get("checks", {}).get("fixed_rva_used") is not False
    ):
        raise AcquisitionError("runtime descriptor value binding is stale")
    if (
        not isinstance(usage_model, dict)
        or usage_model.get("status") != "runtime-validated"
        or usage_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or usage_model.get("inventory", {}).get("sha256")
        != file_identity(usage_path)["sha256"]
        or any(
            usage_model.get("checks", {}).get(key) is not True
            for key in (
                "fresh_runtime_observation",
                "generic_record_domain_complete",
                "header_bound",
                "records_valid",
                "two_observations_match",
                "type_record_helper_runtime_derived",
            )
        )
        or usage_model.get("checks", {}).get("fixed_address_absent") is not True
        or usage_model.get("checks", {}).get("fixed_offset_absent") is not True
    ):
        raise AcquisitionError("runtime metadata usage value binding is stale")
    reference_raw = reference_path.read_bytes()
    value_raw = value_path.read_bytes()
    usage_raw = usage_path.read_bytes()
    if (
        len(reference_raw) < RUNTIME_TYPE_REFERENCE_HEADER.size
        or len(value_raw) < RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.size
        or len(usage_raw) < RUNTIME_METADATA_USAGE_VALUE_HEADER.size
    ):
        raise AcquisitionError("runtime constructed generic input is truncated")
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
    value_header = RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.unpack_from(value_raw)
    usage_header = RUNTIME_METADATA_USAGE_VALUE_HEADER.unpack_from(usage_raw)
    node_count = reference_header[5]
    if (
        reference_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or reference_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or value_header[0] != RUNTIME_TYPE_DESCRIPTOR_VALUE_MAGIC
        or value_header[1] != RUNTIME_TYPE_DESCRIPTOR_VALUE_VERSION
        or value_header[5] != node_count
        or usage_header[0] != RUNTIME_METADATA_USAGE_VALUE_MAGIC
        or usage_header[1] != RUNTIME_METADATA_USAGE_VALUE_VERSION
        or usage_header[9] <= 0
        or usage_header[13] < 32
        or usage_header[13] > 256
        or usage_header[13] & (usage_header[13] - 1)
    ):
        raise AcquisitionError("runtime constructed generic header binding is invalid")
    if (
        not isinstance(usage_status, dict)
        or usage_status.get("schema") != RUNTIME_METADATA_USAGE_VALUE_STATUS_SCHEMA
        or usage_status.get("status") != "complete"
        or usage_status.get("two_observations_match") is not True
        or type(usage_status.get("generic_state_global_owner_only")) is not int
        or usage_status.get("generic_state_global_owner_only") <= 0
        or type(usage_status.get("generic_state_field_owner_only")) is not int
        or usage_status.get("generic_state_field_owner_only") < 0
        or usage_status.get("generic_record_base_owner_only") != usage_header[12]
        or usage_status.get("generic_record_stride") != usage_header[13]
    ):
        raise AcquisitionError(
            "runtime metadata usage status binding is stale"
        )
    process_id = value_header[7]
    if process_id <= 0 or process_id != value_model["target"].get("process_id"):
        raise AcquisitionError("runtime constructed generic process binding is stale")
    reference_base = RUNTIME_TYPE_REFERENCE_HEADER.size
    value_base = RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.size
    if (reference_base + node_count * RUNTIME_TYPE_REFERENCE_RECORD.size <= len(reference_raw)
            and value_base + node_count * RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size <= len(value_raw)):
        rows = select_constructed_seeds_flat(
            reference_raw, value_raw, reference_base, value_base, node_count)
    else:
        rows = select_constructed_seeds(
            (RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(reference_raw,
                reference_base+index*RUNTIME_TYPE_REFERENCE_RECORD.size)
             for index in range(node_count)),
            (RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.unpack_from(value_raw,
                value_base+index*RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size)
             for index in range(node_count)))
    operation, raw_offset, key, mask, adjustment = _codec(semantics)
    return {
        "binary": identity,
        "native_helper_model": file_identity(helper_path),
        "native_semantics_model": file_identity(semantics_path),
        "type_reference_model": file_identity(reference_model_path),
        "type_reference_inventory": file_identity(reference_path),
        "descriptor_value_model": file_identity(value_model_path),
        "descriptor_value_inventory": file_identity(value_path),
        "metadata_usage_value_model": file_identity(usage_model_path),
        "metadata_usage_value_inventory": file_identity(usage_path),
        "metadata_usage_value_status": file_identity(usage_status_path),
        "generic_state_global": usage_status["generic_state_global_owner_only"],
        "generic_state_field": usage_status["generic_state_field_owner_only"],
        "process_id": process_id,
        "image_base": usage_header[8],
        "image_bytes": usage_header[9],
        "generic_record_base": usage_header[12],
        "generic_record_stride": usage_header[13],
        "class_get_fields_rva": get_fields["function_rva"],
        "field_offset_operation": operation,
        "field_offset_raw_offset": raw_offset,
        "field_offset_key": key,
        "field_offset_mask": mask,
        "field_offset_adjustment": adjustment,
        "rows": rows,
        "maximum_generic_index": rows[-1][2],
        "node_count": node_count,
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

#define CLASS_HEADER_BYTES $class_header_bytes
#define HASH_CHUNK (1024u * 1024u)

typedef struct seed_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t record_count, maximum_generic_index;
    char executable_sha256[64], reference_sha256[64], values_sha256[64];
} seed_header;
typedef struct seed_record {
    uint64_t descriptor, current_pointer, generic_index, alias_count;
} seed_record;
typedef struct output_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes;
    uint32_t field_record_bytes; uint64_t record_count, field_count;
    uint64_t process_id, image_base, image_bytes, generic_record_base;
    uint64_t generic_record_stride;
    char executable_sha256[64], seed_sha256[64];
    char helper_sha256[64], semantics_sha256[64];
} output_header;
typedef struct output_record {
    uint64_t descriptor, current_pointer, generic_index, definition_index;
    uint64_t generic_inst, cached_type, class_pointer;
    uint32_t alias_count, field_count;
    unsigned char class_header[CLASS_HEADER_BYTES];
} output_record;
typedef struct field_record {
    uint64_t generic_index, metadata_pointer;
    int64_t offset; uint32_t ordinal, reserved;
    unsigned char native_record[32];
} field_record;

_Static_assert(sizeof(seed_header) == $seed_header_bytes, "seed header");
_Static_assert(sizeof(seed_record) == $seed_record_bytes, "seed record");
_Static_assert(sizeof(output_header) == $output_header_bytes, "output header");
_Static_assert(sizeof(output_record) == $output_record_bytes, "output record");
_Static_assert(sizeof(field_record) == $field_record_bytes, "field record");

static const DWORD expected_pid = ${process_id}u;
static const uint64_t expected_image_base = ${image_base}ull;
static const uint64_t expected_image_bytes = ${image_bytes}ull;
/* The generic class table is heap allocated and reallocated while the client
   runs, so the base recorded by an earlier observation is provenance only.
   Each capture pass re-derives the live base from the runtime-derived state
   chain: live_base = *(*(generic_state_global) + generic_state_field). */
static const uintptr_t recorded_generic_record_base = ${generic_record_base}ull;
static const uintptr_t generic_state_global = ${generic_state_global}ull;
static const uint32_t generic_state_field = ${generic_state_field}u;
static const uint64_t generic_record_stride = ${generic_record_stride}ull;
static const uint64_t class_get_fields_rva = ${class_get_fields_rva}ull;
static const uint32_t field_offset_operation = ${field_offset_operation}u;
static const uint32_t field_offset_raw_offset = ${field_offset_raw_offset}u;
static const uint32_t field_offset_key = ${field_offset_key}u;
static const uint32_t field_offset_mask = ${field_offset_mask}u;
static const int32_t field_offset_adjustment = ${field_offset_adjustment};
static const char executable_sha256[] = "$executable_sha256";
static const char reference_sha256[] = "$reference_sha256";
static const char values_sha256[] = "$values_sha256";
static const char helper_sha256[] = "$helper_sha256";
static const char semantics_sha256[] = "$semantics_sha256";
static const char seed_sha256[] = "$seed_sha256";
static const wchar_t seed_path[] = $seed_path;
static const wchar_t output_path[] = $output_path;
static const wchar_t status_path[] = $status_path;

typedef uintptr_t (*class_get_fields_fn)(uintptr_t, uintptr_t *);

static int readable(uintptr_t value, SIZE_T bytes) {
    MEMORY_BASIC_INFORMATION region;
    if (!value || !bytes || value + bytes < value ||
        !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD) return 0;
    DWORD protect = region.Protect & 0xffu;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    return protect && protect != PAGE_NOACCESS && end >= value &&
        value + bytes <= end;
}
static void digest_hex(const unsigned char digest[32], char output[65]) {
    static const char alphabet[] = "0123456789abcdef";
    for (int i = 0; i < 32; i++) {
        output[i * 2] = alphabet[digest[i] >> 4];
        output[i * 2 + 1] = alphabet[digest[i] & 15];
    }
    output[64] = 0;
}
static int sha256_file(const wchar_t *path, char output[65]) {
    HANDLE input = CreateFileW(path, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (input == INVALID_HANDLE_VALUE) return 0;
    BCRYPT_ALG_HANDLE algorithm = NULL; BCRYPT_HASH_HANDLE hash = NULL;
    DWORD object_size = 0, received = 0; unsigned char digest[32];
    unsigned char *object = NULL, *buffer = NULL;
    int ok = BCryptOpenAlgorithmProvider(&algorithm,
        BCRYPT_SHA256_ALGORITHM, NULL, 0) >= 0 &&
        BCryptGetProperty(algorithm, BCRYPT_OBJECT_LENGTH,
            (PUCHAR)&object_size, sizeof(object_size), &received, 0) >= 0;
    if (ok) object = HeapAlloc(GetProcessHeap(), 0, object_size);
    if (ok) buffer = HeapAlloc(GetProcessHeap(), 0, HASH_CHUNK);
    if (ok && (!object || !buffer)) ok = 0;
    if (ok && BCryptCreateHash(algorithm, &hash, object, object_size,
            NULL, 0, 0) < 0) ok = 0;
    while (ok) { DWORD count = 0;
        if (!ReadFile(input, buffer, HASH_CHUNK, &count, NULL)) { ok = 0; break; }
        if (!count) break;
        if (BCryptHashData(hash, buffer, count, 0) < 0) ok = 0;
    }
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) < 0) ok = 0;
    if (ok) digest_hex(digest, output);
    if (hash) BCryptDestroyHash(hash);
    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);
    if (object) HeapFree(GetProcessHeap(), 0, object);
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    CloseHandle(input); return ok;
}
static int executable_identity(char output[65]) {
    wchar_t path[32768]; DWORD length = GetModuleFileNameW(
        NULL, path, (DWORD)(sizeof(path) / sizeof(path[0])));
    return length && length < sizeof(path) / sizeof(path[0]) &&
        sha256_file(path, output);
}
static int decode_offset(uintptr_t field, int64_t *result) {
    uint32_t raw = 0, value = 0;
    if (!readable(field, 32u) || field_offset_raw_offset + 4u > 32u)
        return 0;
    memcpy(&raw, (const void *)(field + field_offset_raw_offset), 4u);
    if (field_offset_operation == 1u) value = raw ^ field_offset_key;
    else if (field_offset_operation == 2u) value = raw + field_offset_key;
    else if (field_offset_operation == 3u) value = raw - field_offset_key;
    else return 0;
    value &= field_offset_mask;
    *result = (int64_t)value + (int64_t)field_offset_adjustment;
    return 1;
}
static int capture(
    const seed_record *seeds, uint64_t count, output_record *records,
    field_record **fields_out, uint64_t *field_count_out,
    uint64_t *failure_index, uint32_t *failure_kind, uintptr_t *base_out
) {
    uintptr_t state_value = 0, live_base = 0;
    uint64_t total = 0;
    *failure_index = 0; *failure_kind = 0; *base_out = 0;
    memcpy(&state_value, (const void *)generic_state_global, 8u);
    if (!state_value || !readable(state_value + generic_state_field, 8u)) {
        *failure_kind = 11u; return 0;
    }
    memcpy(&live_base, (const void *)(state_value + generic_state_field), 8u);
    if (!live_base || !readable(live_base, 32u)) {
        *failure_kind = 12u; return 0;
    }
    *base_out = live_base;
    class_get_fields_fn get_fields = (class_get_fields_fn)(
        expected_image_base + class_get_fields_rva);
    for (uint64_t i = 0; i < count; i++) {
        uintptr_t record_pointer = live_base +
            (uintptr_t)seeds[i].generic_index * generic_record_stride;
        uint64_t generic[4] = {0};
        if (record_pointer < live_base ||
            !readable(record_pointer, sizeof(generic))) {
            *failure_index = i + 1u; *failure_kind = 1u; return 0;
        }
        memcpy(generic, (const void *)record_pointer, sizeof(generic));
        if (generic[0] >> 32 || !generic[1] || !generic[3] ||
            !readable((uintptr_t)generic[1], 16u) ||
            !readable((uintptr_t)generic[3], CLASS_HEADER_BYTES)) {
            *failure_index = i + 1u; *failure_kind = generic[3] ? 2u : 3u;
            return 0;
        }
        uintptr_t iterator = 0; uint32_t field_count = 0;
        for (;;) {
            uintptr_t field = get_fields((uintptr_t)generic[3], &iterator);
            if (!field) break;
            if (!readable(field, 32u) || field_count == UINT32_MAX) {
                *failure_index = i + 1u; *failure_kind = 4u; return 0;
            }
            field_count++;
        }
        if (total + field_count < total || total + field_count > 50000000ull) {
            *failure_index = i + 1u; *failure_kind = 5u; return 0;
        }
        output_record *target = &records[i];
        target->descriptor = seeds[i].descriptor;
        target->current_pointer = seeds[i].current_pointer;
        target->generic_index = seeds[i].generic_index;
        target->definition_index = generic[0];
        target->generic_inst = generic[1];
        target->cached_type = generic[2];
        target->class_pointer = generic[3];
        target->alias_count = (uint32_t)seeds[i].alias_count;
        target->field_count = field_count;
        memcpy(target->class_header, (const void *)(uintptr_t)generic[3],
            CLASS_HEADER_BYTES);
        total += field_count;
    }
    if (total > SIZE_MAX / sizeof(field_record)) {
        *failure_kind = 6u; return 0;
    }
    field_record *fields = total ? calloc((SIZE_T)total, sizeof(*fields)) : NULL;
    if (total && !fields) { *failure_kind = 7u; return 0; }
    uint64_t cursor = 0;
    for (uint64_t i = 0; i < count; i++) {
        uintptr_t iterator = 0;
        for (uint32_t ordinal = 0; ordinal < records[i].field_count; ordinal++) {
            uintptr_t field = get_fields((uintptr_t)records[i].class_pointer,
                &iterator);
            field_record *target = &fields[cursor++];
            if (!field || !decode_offset(field, &target->offset)) {
                free(fields); *failure_index = i + 1u; *failure_kind = 8u;
                return 0;
            }
            target->generic_index = records[i].generic_index;
            target->metadata_pointer = field;
            target->ordinal = ordinal;
            memcpy(target->native_record, (const void *)field, 32u);
        }
        if (get_fields((uintptr_t)records[i].class_pointer, &iterator)) {
            free(fields); *failure_index = i + 1u; *failure_kind = 9u;
            return 0;
        }
    }
    if (cursor != total) { free(fields); *failure_kind = 10u; return 0; }
    *fields_out = fields; *field_count_out = total; return 1;
}
static int same_capture(
    const output_record *left, const output_record *right, uint64_t count,
    const field_record *left_fields, const field_record *right_fields,
    uint64_t field_count
) {
    return !memcmp(left, right, (SIZE_T)count * sizeof(*left)) &&
        (!field_count || !memcmp(left_fields, right_fields,
            (SIZE_T)field_count * sizeof(*left_fields)));
}
static void write_status(const char *state, int complete, uint64_t records,
    uint64_t fields, uint64_t failure_index, uint32_t failure_kind,
    int two_match, uint64_t live_base) {
    FILE *out = _wfopen(status_path, L"wb"); if (!out) return;
    fprintf(out,
        "{\n  \"schema\": \"$status_schema\",\n"
        "  \"status\": \"%s\",\n  \"complete\": %s,\n"
        "  \"process_id\": %lu,\n  \"record_count\": %llu,\n"
        "  \"field_count\": %llu,\n"
        "  \"generic_record_base_owner_only\": %llu,\n"
        "  \"recorded_generic_record_base_owner_only\": %llu,\n"
        "  \"generic_table_base_freshly_resolved\": %s,\n"
        "  \"failure_index_owner_only\": %llu,\n"
        "  \"failure_kind_owner_only\": %u,\n"
        "  \"two_observations_match\": %s,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"saved_constructed_layout_used\": false,\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_offset_used\": false,\n"
        "  \"external_runtime_component_used\": false\n}\n",
        state, complete ? "true" : "false", GetCurrentProcessId(),
        (unsigned long long)records, (unsigned long long)fields,
        (unsigned long long)live_base,
        (unsigned long long)recorded_generic_record_base,
        live_base ? "true" : "false",
        (unsigned long long)failure_index, failure_kind,
        two_match ? "true" : "false");
    fclose(out); _wchmod(status_path, 0600);
}
static DWORD WINAPI worker(LPVOID unused) {
    (void)unused; _wremove(output_path); _wremove(status_path);
    char executable[65], seed_digest[65];
    if (GetCurrentProcessId() != expected_pid ||
        !executable_identity(executable) || strcmp(executable, executable_sha256) ||
        !sha256_file(seed_path, seed_digest) || strcmp(seed_digest, seed_sha256)) {
        write_status("identity_mismatch", 0, 0, 0, 0, 100u, 0, 0); return 0;
    }
    FILE *input = _wfopen(seed_path, L"rb"); seed_header header;
    if (!input || fread(&header, 1, sizeof(header), input) != sizeof(header) ||
        memcmp(header.magic, "ALPHACS1", 8) || header.version != $seed_version ||
        header.header_bytes != sizeof(header) ||
        header.record_bytes != sizeof(seed_record) || header.reserved ||
        memcmp(header.executable_sha256, executable_sha256, 64) ||
        memcmp(header.reference_sha256, reference_sha256, 64) ||
        memcmp(header.values_sha256, values_sha256, 64) ||
        !header.record_count || header.record_count > 2000000ull ||
        header.record_count > SIZE_MAX / sizeof(seed_record)) {
        if (input) fclose(input);
        write_status("seed_invalid", 0, 0, 0, 0, 101u, 0, 0); return 0;
    }
    seed_record *seeds = malloc((SIZE_T)header.record_count * sizeof(*seeds));
    if (!seeds || fread(seeds, sizeof(*seeds), (SIZE_T)header.record_count,
            input) != (SIZE_T)header.record_count || fgetc(input) != EOF) {
        if (input) fclose(input);
        free(seeds);
        write_status("seed_read_failed", 0, 0, 0, 0, 102u, 0, 0); return 0;
    }
    fclose(input);
    SIZE_T record_bytes = (SIZE_T)header.record_count * sizeof(output_record);
    output_record *first = calloc(1u, record_bytes);
    output_record *second = calloc(1u, record_bytes);
    field_record *first_fields = NULL, *second_fields = NULL;
    uint64_t first_count = 0, second_count = 0, failure_index = 0;
    uint32_t failure_kind = 0;
    uintptr_t first_base = 0, second_base = 0;
    int first_ok = first && second && capture(seeds, header.record_count,
        first, &first_fields, &first_count, &failure_index, &failure_kind,
        &first_base);
    Sleep(250u);
    int second_ok = first_ok && capture(seeds, header.record_count,
        second, &second_fields, &second_count, &failure_index, &failure_kind,
        &second_base);
    int match = second_ok && first_count == second_count &&
        first_base == second_base && same_capture(
        first, second, header.record_count, first_fields, second_fields,
        first_count);
    int written = 0;
    if (match) {
        FILE *out = _wfopen(output_path, L"wb");
        output_header output; memset(&output, 0, sizeof(output));
        memcpy(output.magic, "ALPHACG1", 8);
        output.version = $output_version; output.header_bytes = sizeof(output);
        output.record_bytes = sizeof(output_record);
        output.field_record_bytes = sizeof(field_record);
        output.record_count = header.record_count; output.field_count = first_count;
        output.process_id = GetCurrentProcessId();
        output.image_base = expected_image_base; output.image_bytes = expected_image_bytes;
        output.generic_record_base = first_base;
        output.generic_record_stride = generic_record_stride;
        memcpy(output.executable_sha256, executable_sha256, 64);
        memcpy(output.seed_sha256, seed_sha256, 64);
        memcpy(output.helper_sha256, helper_sha256, 64);
        memcpy(output.semantics_sha256, semantics_sha256, 64);
        written = out && fwrite(&output, 1, sizeof(output), out) == sizeof(output) &&
            fwrite(first, 1, record_bytes, out) == record_bytes &&
            (!first_count || fwrite(first_fields, sizeof(*first_fields),
                (SIZE_T)first_count, out) == (SIZE_T)first_count);
        if (out && fclose(out)) written = 0;
        if (written) _wchmod(output_path, 0600); else _wremove(output_path);
    }
    write_status(written ? "complete" : (match ? "write_failed" :
        (second_ok ? "observation_unstable" : "capture_failed")),
        written, header.record_count, first_count, failure_index,
        failure_kind, match, first_base);
    free(seeds); free(first); free(second); free(first_fields); free(second_fields);
    return 0;
}
BOOL WINAPI DllMain(HINSTANCE module, DWORD reason, LPVOID reserved) {
    (void)module; (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(module);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }
    return TRUE;
}
''')


def prepare_runtime_constructed_generic_layout(
    *, binary: Path, native_helper_model: Path, native_semantics_model: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    descriptor_value_model: Path, descriptor_value_inventory: Path,
    metadata_usage_value_model: Path, metadata_usage_value_inventory: Path,
    metadata_usage_value_status: Path,
    output_dir: Path, compiler: Path | None = None, extent_operation_model: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        native_helper_model=native_helper_model,
        native_semantics_model=native_semantics_model,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        descriptor_value_model=descriptor_value_model,
        descriptor_value_inventory=descriptor_value_inventory,
        metadata_usage_value_model=metadata_usage_value_model,
        metadata_usage_value_inventory=metadata_usage_value_inventory,
        metadata_usage_value_status=metadata_usage_value_status,
    )
    if extent_operation_model is None:
        raise AcquisitionError("constructed capture requires a code-derived extent operation")
    from alpha.p20 import load_extent_operation
    reference_target=read_json(type_reference_model)["target"]
    load_extent_operation(extent_operation_model,expected_target=reference_target)
    seed_path = output_dir / "runtime-constructed-generic-seed.private.bin"
    output_path = output_dir / "runtime-constructed-generic-layout.private.bin"
    status_path = output_dir / "runtime-constructed-generic-layout-status.private.json"
    model_path = output_dir / "runtime-constructed-generic-layout.private.json"
    build_dir = _owner_directory(output_dir / "build-constructed-generic-layout")
    source_path = build_dir / "runtime-constructed-generic-layout.c"
    injector_source_path = build_dir / "runtime-constructed-generic-layout-injector.c"


    collector_path = build_dir / (
        "alpha-runtime-constructed-generic-layout-"
        f"{time.time_ns():x}.dll"
    )
    injector_path = build_dir / "alpha-runtime-constructed-generic-layout-injector.exe"
    for path in (output_path, status_path, model_path):
        path.unlink(missing_ok=True)
    reference_sha = binding["type_reference_inventory"]["sha256"]
    values_sha = binding["descriptor_value_inventory"]["sha256"]
    seed = bytearray(_SEED_HEADER.pack(
        _SEED_MAGIC, _SEED_VERSION, _SEED_HEADER.size, _SEED_RECORD.size, 0,
        len(binding["rows"]), binding["maximum_generic_index"],
        binding["binary"]["sha256"].encode("ascii"),
        reference_sha.encode("ascii"), values_sha.encode("ascii"),
    ))
    for row in binding["rows"]:
        seed.extend(_SEED_RECORD.pack(*row))
    seed_path.write_bytes(seed)
    os.chmod(seed_path, 0o600)
    seed_identity = file_identity(seed_path)
    source = _COLLECTOR.substitute(
        class_header_bytes=RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER_BYTES,
        seed_header_bytes=_SEED_HEADER.size,
        seed_record_bytes=_SEED_RECORD.size,
        output_header_bytes=RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size,
        output_record_bytes=RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size,
        field_record_bytes=RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.size,
        process_id=binding["process_id"],
        image_base=binding["image_base"],
        image_bytes=binding["image_bytes"],
        generic_record_base=binding["generic_record_base"],
        generic_state_global=binding["generic_state_global"],
        generic_state_field=binding["generic_state_field"],
        generic_record_stride=binding["generic_record_stride"],
        class_get_fields_rva=binding["class_get_fields_rva"],
        field_offset_operation=binding["field_offset_operation"],
        field_offset_raw_offset=binding["field_offset_raw_offset"],
        field_offset_key=binding["field_offset_key"],
        field_offset_mask=binding["field_offset_mask"],
        field_offset_adjustment=binding["field_offset_adjustment"],
        executable_sha256=binding["binary"]["sha256"],
        reference_sha256=reference_sha,
        values_sha256=values_sha,
        helper_sha256=binding["native_helper_model"]["sha256"],
        semantics_sha256=binding["native_semantics_model"]["sha256"],
        seed_sha256=seed_identity["sha256"],
        seed_path=_wide_literal(_windows_z_path(seed_path)),
        output_path=_wide_literal(_windows_z_path(output_path)),
        status_path=_wide_literal(_windows_z_path(status_path)),
        status_schema=RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_STATUS_SCHEMA,
        seed_version=_SEED_VERSION,
        output_version=RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION,
    )
    _private_text(source_path, source)
    _private_text(injector_source_path, runtime_injector_source())
    selected_compiler = _compiler(compiler)


    with ThreadPoolExecutor(max_workers=2) as executor:
        collector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler), "-shared", "-O2", "-s", "-Wall", "-Wextra",
                "-Wformat=2", "-Werror", str(source_path), "-o", str(collector_path),
                "-lbcrypt",
            ],
            label="runtime constructed generic collector",
            source_path=source_path,
            output_path=collector_path,
        )
        injector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler), "-O2", "-s", "-municode", "-Wall", "-Wextra",
                "-Wformat=2", "-Werror", str(injector_source_path), "-o",
                str(injector_path),
            ],
            label="runtime constructed generic injector",
            source_path=injector_source_path,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": "alpha.runtime-constructed-generic-layout-plan/v1",
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "creation_filetime": reference_target["creation_filetime"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            key: binding[key]
            for key in (
                "native_helper_model", "native_semantics_model",
                "type_reference_model", "type_reference_inventory",
                "descriptor_value_model", "descriptor_value_inventory",
                "metadata_usage_value_model",
                "metadata_usage_value_inventory",
                "metadata_usage_value_status",
            )
        },
        "extent_operation": file_identity(extent_operation_model),
        "contract": {
            "constructed_selection_source": "observed-reflection-shape",
            "native_kind_tag_used_for_selection": False,
            "record_count": len(binding["rows"]),
            "maximum_generic_index": binding["maximum_generic_index"],
            "generic_record_stride": binding["generic_record_stride"],
            "class_header_bytes": RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER_BYTES,
            "field_record_bytes": RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.size,
        },
        "runtime_contract_owner_only": {
            "generic_record_base": binding["generic_record_base"],
            "generic_state_global": binding["generic_state_global"],
            "generic_state_field": binding["generic_state_field"],
            "class_get_fields_rva": binding["class_get_fields_rva"],
            "field_offset_operation": binding["field_offset_operation"],
            "field_offset_raw_offset": binding["field_offset_raw_offset"],
            "field_offset_key": binding["field_offset_key"],
            "field_offset_mask": binding["field_offset_mask"],
            "field_offset_adjustment": binding["field_offset_adjustment"],
        },
        "seed": seed_identity,
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "policy": {
            "same_process_required": True,
            "runtime_generic_table_current_process_derived": True,
            "class_field_iterator_current_code_derived": True,
            "field_offset_codec_current_code_derived": True,
            "two_observations_required": True,
            "saved_constructed_layout_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(output_dir / "runtime-constructed-generic-layout-plan.private.json", plan)
    return plan


def _validate_capture(plan: dict[str, Any], status: dict[str, Any]) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = _owner_file(Path(plan["output_path"]), label="layout inventory")
    raw = output_path.read_bytes()
    if len(raw) < RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size:
        raise AcquisitionError("runtime constructed generic output is truncated")
    header = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.unpack_from(raw)
    record_count = header[5]
    field_count = header[6]
    records_end = (
        RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        + record_count * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
    )
    expected_size = (
        records_end
        + field_count * RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.size
    )
    header_ok = (
        header[0] == RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC
        and header[1] == RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
        and header[2] == RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        and header[3] == RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
        and header[4] == RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.size
        and record_count == plan["contract"]["record_count"]
        and header[7] == plan["target"]["process_id"]
        and header[8] == plan["target"]["image_base_owner_only"]
        and header[9] == plan["target"]["image_bytes"]
        and header[10] == status.get("generic_record_base_owner_only")
        and status.get("recorded_generic_record_base_owner_only")
        == plan["runtime_contract_owner_only"]["generic_record_base"]
        and status.get("generic_table_base_freshly_resolved") is True
        and header[11] == plan["contract"]["generic_record_stride"]
        and _digest(header[12], label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[13], label="seed") == plan["seed"]["sha256"]
        and _digest(header[14], label="helper")
        == plan["inputs"]["native_helper_model"]["sha256"]
        and _digest(header[15], label="semantics")
        == plan["inputs"]["native_semantics_model"]["sha256"]
        and len(raw) == expected_size
    )
    indexes: set[int] = set()
    classes: set[int] = set()
    alias_total = 0
    record_field_total = 0
    class_headers: dict[int, bytes] = {}
    rows_ok = header_ok


    records_region = memoryview(raw)[
        RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size:records_end
    ]
    try:
        for row in RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.iter_unpack(
            records_region if rows_ok else records_region[:0]
        ):
            (
                descriptor, current, generic_index, definition_index,
                generic_inst, _cached_type, class_pointer, alias_count,
                current_field_count, class_header,
            ) = row
            if (
                not descriptor or descriptor & 7 or not current or current & 7
                or generic_index in indexes or definition_index >> 32
                or not generic_inst or not class_pointer or class_pointer & 7
                or class_pointer in classes or not alias_count
                or class_header == _ZERO_CLASS_HEADER
            ):
                rows_ok = False
                break
            indexes.add(generic_index)
            classes.add(class_pointer)
            class_headers[generic_index] = class_header
            alias_total += alias_count
            record_field_total += current_field_count
    finally:
        records_region.release()
    fields_ok = rows_ok and record_field_total == field_count
    field_indexes: dict[int, int] = {}
    fields_region = memoryview(raw)[records_end:records_end + field_count * RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.size]
    try:
        for row in RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.iter_unpack(
            fields_region if fields_ok else fields_region[:0]
        ):
            generic_index, metadata_pointer, offset, ordinal, reserved, native = row
            expected_ordinal = field_indexes.get(generic_index, 0)
            if (
                generic_index not in indexes or not metadata_pointer
                or ordinal != expected_ordinal or reserved
                or offset < -(1 << 31)
                or offset > 0xFFFFFFFF or native == _ZERO_NATIVE_RECORD
            ):
                fields_ok = False
                break
            field_indexes[generic_index] = expected_ordinal + 1
    finally:
        fields_region.release()
    from alpha.p20 import load_extent_operation
    from alpha.c03 import observe_candidate_extents
    from alpha.c04 import _verify_files
    extent_record=plan.get("extent_operation")
    if not isinstance(extent_record,dict):
        raise AcquisitionError("constructed extent operation is absent; header search is not allowed")
    _verify_files({"extent_operation":extent_record})
    operation,extent_inputs=load_extent_operation(Path(extent_record["path"]),expected_target=plan["target"])
    evidence=observe_candidate_extents(operation,class_headers,include_rows=False) if rows_ok else None
    candidate=evidence["load"]["candidate"] if evidence else None
    instance_size_offset=candidate["class_extent_offset"] if candidate else None
    instance_size_width=candidate["class_extent_width"] if candidate else 0
    _verify_files(extent_inputs)
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "header_bound": header_ok,
        "all_constructed_generic_rows_valid": rows_ok,
        "generic_indexes_unique": rows_ok and len(indexes) == record_count,
        "materialized_classes_unique": rows_ok and len(classes) == record_count,
        "generic_table_base_freshly_resolved": (
            status.get("generic_table_base_freshly_resolved") is True
            and status.get("recorded_generic_record_base_owner_only")
            == plan["runtime_contract_owner_only"]["generic_record_base"]
        ),
        "all_constructed_fields_valid": fields_ok,
        "field_count_exact": fields_ok and record_field_total == field_count,
        "class_extent_load_code_derived": evidence is not None,
        "aliases_cover_full_generic_reference_domain": (
            rows_ok and alias_total >= record_count
        ),
        "two_observations_match": status.get("two_observations_match") is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_layout_absent": status.get("saved_constructed_layout_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    return {
        "constructed_generic_class_count": record_count,
        "constructed_generic_alias_count": alias_total,
        "constructed_generic_field_count": field_count,
        "maximum_generic_index": max(indexes) if indexes else 0,
        "instance_size_byte_offset": instance_size_offset,
        "instance_size_width_bytes": instance_size_width,
        "inventory_sha256": hashlib.sha256(raw).hexdigest(),
    }, checks


def capture_runtime_constructed_generic_layout(
    *, binary: Path, native_helper_model: Path, native_semantics_model: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    descriptor_value_model: Path, descriptor_value_inventory: Path,
    metadata_usage_value_model: Path, metadata_usage_value_inventory: Path,
    metadata_usage_value_status: Path,
    output_dir: Path, wine: Path, wineprefix: Path,
    compiler: Path | None = None, timeout: float = 900.0, event_capture_plan: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    if event_capture_plan is None:
        raise AcquisitionError("constructed capture requires current event/ancestry sources for extent derivation")
    from alpha.p20 import capture_extent_operation
    extent_operation_model=capture_extent_operation(binary=binary,event_capture_plan=event_capture_plan,
        output_dir=output_dir/"extent-operation",wine=wine,wineprefix=wineprefix,compiler=compiler)
    plan = prepare_runtime_constructed_generic_layout(
        binary=binary,
        native_helper_model=native_helper_model,
        native_semantics_model=native_semantics_model,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        descriptor_value_model=descriptor_value_model,
        descriptor_value_inventory=descriptor_value_inventory,
        metadata_usage_value_model=metadata_usage_value_model,
        metadata_usage_value_inventory=metadata_usage_value_inventory,
        metadata_usage_value_status=metadata_usage_value_status,
        output_dir=output_dir,
        compiler=compiler,
        extent_operation_model=extent_operation_model,
    )
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine.expanduser().resolve()), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "runtime constructed generic injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-constructed-generic-layout-injector.private.log",
        json.dumps(
            {
                "returncode": injected.returncode,
                "stdout": injected.stdout,
                "stderr": injected.stderr,
            },
            ensure_ascii=False,
            indent=2,
        ) + "\n",
    )
    if injected.returncode:
        raise AcquisitionError("runtime constructed generic injection failed")
    deadline = time.monotonic() + timeout
    status_path = Path(plan["status_path"])
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        if status_path.is_file():
            try:
                candidate = read_json(status_path)
            except (OSError, ValueError):
                candidate = None
            if isinstance(candidate, dict) and candidate.get("status"):
                status = candidate
                break
        time.sleep(0.2)
    if status is None:
        raise AcquisitionError("runtime constructed generic capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime constructed generic capture failed "
            f"(status={status.get('status')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    counts, checks = _validate_capture(plan, status)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime constructed generic validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    model = {
        "schema": RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA,
        "status": "runtime-validated",
        "target": dict(plan["target"]),
        "inputs": plan["inputs"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "extent_operation": plan["extent_operation"],
        "constructed_selection_source": plan["contract"]["constructed_selection_source"],
        "native_kind_tag_used_for_selection": False,
        "native_type_grammar_proven": False,
        "native_layout_complete": False,
        "metadata_complete": False,
        "owner_only": True,
    }
    _private_json(Path(plan["model_path"]), model)
    return model
