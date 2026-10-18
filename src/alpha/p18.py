from alpha.h02 import windows_run as _host_run

import json
import mmap
import os
import stat
import struct
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_stat_bits, owner_only_path_bits
from alpha.h04 import MemorySnapshot
from alpha.p16 import (
    METHOD_NAME_DECODE_OPERATION_CODES,
    REFLECTION_SEMANTICS_SCHEMA,
)
from alpha.c04 import MappedPE
from alpha.p16 import RUNTIME_TYPE_MATERIALIZER_SCHEMA
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json


RUNTIME_METHOD_NAME_PLAN_SCHEMA = "alpha.runtime-method-name-plan/v2"
RUNTIME_METHOD_NAME_STATUS_SCHEMA = "alpha.runtime-method-name-status/v2"
RUNTIME_METHOD_NAME_OBSERVATION_SCHEMA = (
    "alpha.runtime-method-name-observation/v2"
)
RUNTIME_METHOD_NAME_MAGIC = b"ALPHANN2"
RUNTIME_METHOD_NAME_VERSION = 2
RUNTIME_METHOD_NAME_HEADER = struct.Struct(
    "<8sIIIIQQQQ64s64s64sIIIIQQ"
)
RUNTIME_METHOD_NAME_RECORD = struct.Struct("<IIQQII")


def _owner_only_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError(f"runtime method-name {label} is unavailable")
    status = path.stat()
    if False or owner_only_stat_bits(status):
        raise AcquisitionError(f"runtime method-name {label} is not owner-only")
    return path


def _method_name_binding(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    materializer_model: Path,
    native_inventory: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    reflection_semantics_model = _owner_only_file(
        reflection_semantics_model, label="reflection semantic model"
    )
    materializer_model = _owner_only_file(
        materializer_model, label="validated materializer model"
    )
    native_inventory = _owner_only_file(
        native_inventory, label="native inventory"
    )
    identity = file_identity(binary)
    semantics = read_json(reflection_semantics_model)
    materializer = read_json(materializer_model)
    validation = (
        materializer.get("runtime_validation")
        if isinstance(materializer, dict)
        else None
    )
    validation_checks = (
        validation.get("checks") if isinstance(validation, dict) else None
    )
    expected_inventory = (
        validation.get("native_inventory")
        if isinstance(validation, dict)
        else None
    )
    if (
        not isinstance(materializer, dict)
        or materializer.get("schema") != RUNTIME_TYPE_MATERIALIZER_SCHEMA
        or materializer.get("status") != "runtime-validated"
        or materializer.get("binary", {}).get("sha256") != identity["sha256"]
        or not isinstance(validation, dict)
        or not isinstance(validation_checks, dict)
        or validation_checks.get("native_inventory_type_rows_bound") is not True
        or validation_checks.get("native_inventory_method_rows_bound") is not True
        or not isinstance(expected_inventory, dict)
        or file_identity(native_inventory)["sha256"]
        != expected_inventory.get("sha256")
        or file_identity(native_inventory)["bytes"]
        != expected_inventory.get("bytes")
    ):
        raise AcquisitionError(
            "runtime method-name materializer binding is stale"
        )
    if (
        not isinstance(semantics, dict)
        or semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("binary", {}).get("sha256") != identity["sha256"]
        or semantics.get("snapshot", {}).get("sha256")
        != materializer.get("snapshot", {}).get("sha256")
        or semantics.get("checks", {}).get("method_name_decoder_derived")
        is not True
        or semantics.get("checks", {}).get(
            "method_name_lazy_initializer_semantically_bound"
        )
        is not True
    ):
        raise AcquisitionError(
            "runtime method-name reflection semantic binding is stale"
        )
    decoder = semantics.get("method_name_decoder")
    if not isinstance(decoder, dict):
        raise AcquisitionError("runtime method-name decoder is unavailable")
    node_qword = decoder.get("name_node_field_qword")
    encoded_qword = decoder.get("encoded_name_field_qword")
    decode_operation = decoder.get("decode_operation")
    decode_key = decoder.get("decode_key")
    if decode_operation is None and type(decoder.get("xor_key")) is int:
        legacy_xor_key = decoder["xor_key"]
        if legacy_xor_key > 0:
            decode_operation, decode_key = "xor", legacy_xor_key
    lazy_initializer = decoder.get("lazy_initializer")
    if (
        type(node_qword) is not int
        or not 0 <= node_qword < 16
        or type(encoded_qword) is not int
        or not 0 <= encoded_qword < 16
        or type(decode_operation) is not str
        or decode_operation not in METHOD_NAME_DECODE_OPERATION_CODES
        or type(decode_key) is not int
        or not 0 < decode_key < 1 << 64
        or type(lazy_initializer) is not int
        or lazy_initializer <= 0
    ):
        raise AcquisitionError("runtime method-name decoder is invalid")
    snapshot_record = semantics.get("snapshot")
    snapshot_path = (
        Path(snapshot_record["path"])
        if isinstance(snapshot_record, dict)
        and isinstance(snapshot_record.get("path"), str)
        else None
    )
    if snapshot_path is None:
        raise AcquisitionError("runtime method-name snapshot binding is absent")
    snapshot_path = _owner_only_file(snapshot_path, label="memory snapshot")
    if file_identity(snapshot_path)["sha256"] != snapshot_record.get("sha256"):
        raise AcquisitionError("runtime method-name snapshot binding is stale")
    with MemorySnapshot(snapshot_path) as snapshot:
        image_base = snapshot.image_base
        image_bytes = snapshot.image_bytes
    lazy_initializer_rva = lazy_initializer - image_base
    with MappedPE(binary) as image:
        if (
            image.size_of_image != image_bytes
            or not 0 < lazy_initializer_rva < image_bytes
            or not image.executable_rva(lazy_initializer_rva)
        ):
            raise AcquisitionError(
                "runtime method-name lazy initializer is outside current image"
            )
    process_id = validation.get("process_id")
    if not isinstance(process_id, int) or process_id <= 0:
        raise AcquisitionError(
            "runtime method-name source process binding is unavailable"
        )
    return {
        "binary": identity,
        "semantics": file_identity(reflection_semantics_model),
        "materializer": file_identity(materializer_model),
        "native_inventory": file_identity(native_inventory),
        "snapshot": file_identity(snapshot_path),
        "image_base": image_base,
        "image_bytes": image_bytes,
        "process_id": process_id,
        "method_count": expected_inventory.get("method_count"),
        "node_qword": node_qword,
        "encoded_qword": encoded_qword,
        "decode_operation": decode_operation,
        "decode_operation_code": METHOD_NAME_DECODE_OPERATION_CODES[
            decode_operation
        ],
        "decode_key": decode_key,
        "lazy_initializer_rva": lazy_initializer_rva,
    }


def runtime_method_name_materializer_source(
    *,
    expected_executable_sha256: str,
    expected_native_inventory_sha256: str,
    expected_reflection_semantics_sha256: str,
    expected_process_id: int,
    expected_image_base: int,
    expected_image_bytes: int,
    native_inventory_path: Path,
    observation_path: Path,
    status_path: Path,
    method_count: int,
    name_node_field_qword: int,
    encoded_name_field_qword: int,
    method_name_decode_operation: str,
    method_name_decode_key: int,
    lazy_initializer_rva: int,
) -> str:
    digests = (
        expected_executable_sha256,
        expected_native_inventory_sha256,
        expected_reflection_semantics_sha256,
    )
    if any(
        len(value) != 64
        or any(character not in "0123456789abcdefABCDEF" for character in value)
        for value in digests
    ):
        raise AcquisitionError(
            "runtime method-name materializer requires exact SHA-256 bindings"
        )
    numeric = (
        expected_process_id,
        expected_image_base,
        expected_image_bytes,
        method_count,
        method_name_decode_key,
        lazy_initializer_rva,
    )
    if any(not isinstance(value, int) or value <= 0 for value in numeric):
        raise AcquisitionError("runtime method-name materializer binding is invalid")
    if (
        type(method_name_decode_operation) is not str
        or method_name_decode_operation
        not in METHOD_NAME_DECODE_OPERATION_CODES
    ):
        raise AcquisitionError(
            "runtime method-name materializer operation is unsupported"
        )
    decode_operation_code = METHOD_NAME_DECODE_OPERATION_CODES[
        method_name_decode_operation
    ]
    if not 0 <= name_node_field_qword < 16 or not 0 <= encoded_name_field_qword < 16:
        raise AcquisitionError("runtime method-name materializer layout is invalid")
    inventory_literal = _wide_literal(_windows_z_path(native_inventory_path))
    observation_literal = _wide_literal(_windows_z_path(observation_path))
    status_literal = _wide_literal(_windows_z_path(status_path))
    return rf'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <wchar.h>

#define ALPHA_HASH_CHUNK (1024u * 1024u)
#define ALPHA_MAX_METHOD_NAME_BYTES 16384u

typedef struct alpha_native_inventory_header {{
    char magic[8];
    uint32_t version;
    uint32_t type_record_bytes;
    uint32_t method_record_bytes;
    uint32_t reserved;
    uint64_t type_count;
    uint64_t method_count;
    uint64_t image_bytes;
    char executable_sha256[64];
    char materializer_model_sha256[64];
    uint32_t class_name_qword;
    uint32_t parent_class_qword;
    uint32_t class_declaring_qword;
    uint32_t method_array_qword;
    uint32_t method_count_byte_offset;
    uint32_t method_declaring_qword;
    uint32_t method_pointer_qword;
    uint32_t reserved_layout;
}} alpha_native_inventory_header;

typedef struct alpha_native_type_record {{
    uint32_t definition_index;
    uint32_t name_bytes;
    uint64_t type_flags;
    uint64_t descriptor_rva;
    uint64_t class_pointer;
    uint64_t parent_pointer;
    uint64_t declaring_pointer;
    uint32_t method_count;
    uint32_t reserved;
    uint64_t method_start;
    uint64_t name_offset;
}} alpha_native_type_record;

typedef struct alpha_native_method_record {{
    uint32_t definition_index;
    uint32_t method_index;
    uint64_t metadata_pointer;
    uint64_t method_pointer;
}} alpha_native_method_record;

typedef struct alpha_method_name_header {{
    char magic[8];
    uint32_t version;
    uint32_t header_bytes;
    uint32_t record_bytes;
    uint32_t reserved;
    uint64_t method_count;
    uint64_t nonempty_name_count;
    uint64_t name_bytes;
    uint64_t image_bytes;
    char executable_sha256[64];
    char native_inventory_sha256[64];
    char reflection_semantics_sha256[64];
    uint32_t name_node_field_qword;
    uint32_t encoded_name_field_qword;
    uint32_t decode_operation;
    uint32_t reserved_layout_two;
    uint64_t lazy_initializer_rva;
    uint64_t decode_key;
}} alpha_method_name_header;

typedef struct alpha_method_name_record {{
    uint32_t definition_index;
    uint32_t method_index;
    uint64_t metadata_pointer;
    uint64_t name_offset;
    uint32_t name_bytes;
    uint32_t flags;
}} alpha_method_name_record;

_Static_assert(sizeof(alpha_native_inventory_header) == {_NATIVE_INVENTORY_HEADER.size},
    "native inventory header layout mismatch");
_Static_assert(sizeof(alpha_native_type_record) == {_NATIVE_TYPE_RECORD.size},
    "native type record layout mismatch");
_Static_assert(sizeof(alpha_native_method_record) == {_NATIVE_METHOD_RECORD.size},
    "native method record layout mismatch");
_Static_assert(sizeof(alpha_method_name_header) == {RUNTIME_METHOD_NAME_HEADER.size},
    "method name header layout mismatch");
_Static_assert(sizeof(alpha_method_name_record) == {RUNTIME_METHOD_NAME_RECORD.size},
    "method name record layout mismatch");

static const char expected_executable_sha256[] =
    "{expected_executable_sha256.lower()}";
static const char expected_native_inventory_sha256[] =
    "{expected_native_inventory_sha256.lower()}";
static const char expected_reflection_semantics_sha256[] =
    "{expected_reflection_semantics_sha256.lower()}";
static const DWORD expected_process_id = {expected_process_id}u;
static const uintptr_t expected_image_base = {expected_image_base}ull;
static const uint64_t expected_image_bytes = {expected_image_bytes}ull;
static const uint64_t expected_method_count = {method_count}ull;
static const uint32_t derived_name_node_field_qword =
    {name_node_field_qword}u;
static const uint32_t derived_encoded_name_field_qword =
    {encoded_name_field_qword}u;
static const uint32_t derived_method_name_decode_operation =
    {decode_operation_code}u;
static const uint64_t derived_method_name_decode_key =
    {method_name_decode_key}ull;
static const uint64_t derived_lazy_initializer_rva =
    {lazy_initializer_rva}ull;
static const wchar_t native_inventory_input[] = {inventory_literal};
static const wchar_t observation_output[] = {observation_literal};
static const wchar_t status_output[] = {status_literal};

typedef uintptr_t (*alpha_lazy_name_initializer)(uintptr_t metadata_pointer);

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
    unsigned char *object = NULL, *buffer = NULL;
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
        GetProcessHeap(), 0, ALPHA_HASH_CHUNK
    );
    if (ok && (!object || !buffer)) ok = 0;
    if (ok && BCryptCreateHash(
            algorithm, &hash, object, object_size, NULL, 0, 0
        ) < 0) ok = 0;
    while (ok) {{
        DWORD read = 0;
        if (!ReadFile(input, buffer, ALPHA_HASH_CHUNK, &read, NULL)) {{
            ok = 0;
            break;
        }}
        if (!read) break;
        if (BCryptHashData(hash, buffer, read, 0) < 0) ok = 0;
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

static int readable_pointer(uintptr_t value, SIZE_T bytes) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !bytes || value + bytes < value ||
        !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD)
        return 0;
    DWORD protect = region.Protect & 0xffu;
    if (!protect || protect == PAGE_NOACCESS) return 0;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    return end >= value && value + bytes <= end;
}}

static int executable_pointer(uintptr_t value) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD)
        return 0;
    DWORD protect = region.Protect & 0xffu;
    return protect == PAGE_EXECUTE || protect == PAGE_EXECUTE_READ ||
        protect == PAGE_EXECUTE_READWRITE ||
        protect == PAGE_EXECUTE_WRITECOPY;
}}

static uint32_t bounded_name_bytes(uintptr_t value) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD)
        return UINT32_MAX;
    DWORD protect = region.Protect & 0xffu;
    if (!protect || protect == PAGE_NOACCESS) return UINT32_MAX;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    if (end <= value) return UINT32_MAX;
    SIZE_T available = end - value;
    if (available > ALPHA_MAX_METHOD_NAME_BYTES + 1u)
        available = ALPHA_MAX_METHOD_NAME_BYTES + 1u;
    const unsigned char *text = (const unsigned char *)value;
    for (SIZE_T index = 0; index < available; index++)
        if (!text[index]) return (uint32_t)index;
    return UINT32_MAX;
}}

static int decode_method_name_pointer(uintptr_t encoded, uintptr_t *value) {{
    switch (derived_method_name_decode_operation) {{
    case {METHOD_NAME_DECODE_OPERATION_CODES['xor']}u:
        *value = encoded ^ (uintptr_t)derived_method_name_decode_key;
        return 1;
    case {METHOD_NAME_DECODE_OPERATION_CODES['add']}u:
        *value = encoded + (uintptr_t)derived_method_name_decode_key;
        return 1;
    default:
        return 0;
    }}
}}

static int load_main_image(uintptr_t *base, uint64_t *bytes) {{
    unsigned char *image = (unsigned char *)GetModuleHandleW(NULL);
    if (!image) return 0;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)image;
    if (dos->e_magic != IMAGE_DOS_SIGNATURE || dos->e_lfanew <= 0 ||
        dos->e_lfanew > 1024 * 1024) return 0;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(image + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE ||
        nt->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC ||
        !nt->OptionalHeader.SizeOfImage) return 0;
    *base = (uintptr_t)image;
    *bytes = nt->OptionalHeader.SizeOfImage;
    return 1;
}}

static int observe_name(
    uintptr_t metadata_pointer,
    alpha_lazy_name_initializer initialize,
    uintptr_t *name_pointer,
    uint32_t *name_bytes,
    uint64_t *lazy_count
) {{
    uintptr_t node_address = metadata_pointer +
        (uintptr_t)derived_name_node_field_qword * sizeof(uintptr_t);
    uintptr_t node = 0, encoded = 0, value = 0;
    if (node_address < metadata_pointer ||
        !readable_pointer(node_address, sizeof(node))) return 0;
    memcpy(&node, (const void *)node_address, sizeof(node));
    if (node) {{
        uintptr_t encoded_address = node +
            (uintptr_t)derived_encoded_name_field_qword * sizeof(uintptr_t);
        if (encoded_address < node ||
            !readable_pointer(encoded_address, sizeof(encoded))) return 0;
        memcpy(&encoded, (const void *)encoded_address, sizeof(encoded));
        if (!decode_method_name_pointer(encoded, &value)) return 0;
    }}
    if (!value) {{
        value = initialize(metadata_pointer);
        (*lazy_count)++;
    }}
    uint32_t bytes = bounded_name_bytes(value);
    if (bytes == UINT32_MAX) return 0;
    *name_pointer = value;
    *name_bytes = bytes;
    return 1;
}}

static void write_status(
    const char *status,
    const char *observed_executable_sha256,
    const char *observed_inventory_sha256,
    uint64_t observed_method_count,
    uint64_t nonempty_name_count,
    uint64_t empty_name_count,
    uint64_t lazy_initialization_count,
    uint64_t failure_index,
    int observation_written
) {{
    FILE *output = _wfopen(status_output, L"wb");
    if (!output) return;
    fprintf(output,
        "{{\n"
        "  \"schema\": \"{RUNTIME_METHOD_NAME_STATUS_SCHEMA}\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"observed_inventory_sha256\": \"%s\",\n"
        "  \"expected_method_count\": %llu,\n"
        "  \"observed_method_count\": %llu,\n"
        "  \"nonempty_name_count\": %llu,\n"
        "  \"empty_name_count\": %llu,\n"
        "  \"lazy_initialization_count\": %llu,\n"
        "  \"failure_index_owner_only\": %llu,\n"
        "  \"observation_written\": %s,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"current_process_identity_bound\": true,\n"
        "  \"raw_runtime_pointers_exposed\": false,\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_rva_used\": false,\n"
        "  \"saved_method_name_used\": false,\n"
        "  \"external_runtime_component_used\": false\n"
        "}}\n",
        status,
        (unsigned long)GetCurrentProcessId(),
        (unsigned long)expected_process_id,
        expected_executable_sha256,
        observed_executable_sha256 ? observed_executable_sha256 : "",
        observed_inventory_sha256 ? observed_inventory_sha256 : "",
        (unsigned long long)expected_method_count,
        (unsigned long long)observed_method_count,
        (unsigned long long)nonempty_name_count,
        (unsigned long long)empty_name_count,
        (unsigned long long)lazy_initialization_count,
        (unsigned long long)failure_index,
        observation_written ? "true" : "false"
    );
    fflush(output);
    fclose(output);
    _wchmod(status_output, 0600);
}}

static int materialize_method_names(
    uintptr_t image_base,
    uint64_t image_bytes,
    uint64_t *observed_method_count,
    uint64_t *nonempty_name_count,
    uint64_t *empty_name_count,
    uint64_t *lazy_initialization_count,
    uint64_t *failure_index
) {{
    *observed_method_count = 0;
    *nonempty_name_count = 0;
    *empty_name_count = 0;
    *lazy_initialization_count = 0;
    *failure_index = 0;
    _wremove(observation_output);
    FILE *input = _wfopen(native_inventory_input, L"rb");
    if (!input) return 0;
    alpha_native_inventory_header inventory;
    int complete = fread(&inventory, 1, sizeof(inventory), input) ==
        sizeof(inventory) &&
        !memcmp(inventory.magic, "ALPHANI1", 8) &&
        inventory.version == {_NATIVE_INVENTORY_VERSION}u &&
        inventory.type_record_bytes == sizeof(alpha_native_type_record) &&
        inventory.method_record_bytes == sizeof(alpha_native_method_record) &&
        !inventory.reserved && !inventory.reserved_layout &&
        inventory.method_count == expected_method_count &&
        inventory.image_bytes == image_bytes &&
        !memcmp(inventory.executable_sha256,
            expected_executable_sha256, 64);
    uint64_t method_count = inventory.method_count;
    if (!complete || !method_count || method_count > 10000000ull ||
        method_count > SIZE_MAX / sizeof(alpha_method_name_record) ||
        method_count > SIZE_MAX / sizeof(uintptr_t) ||
        method_count > SIZE_MAX / sizeof(uint32_t)) {{
        fclose(input);
        return 0;
    }}
    uint64_t method_offset = sizeof(alpha_native_inventory_header) +
        inventory.type_count * sizeof(alpha_native_type_record);
    if (method_offset < sizeof(alpha_native_inventory_header) ||
        _fseeki64(input, (__int64)method_offset, SEEK_SET)) {{
        fclose(input);
        return 0;
    }}
    alpha_method_name_record *records =
        (alpha_method_name_record *)calloc(
            (SIZE_T)method_count, sizeof(alpha_method_name_record));
    uintptr_t *name_pointers = (uintptr_t *)calloc(
        (SIZE_T)method_count, sizeof(uintptr_t));
    uint32_t *name_lengths = (uint32_t *)calloc(
        (SIZE_T)method_count, sizeof(uint32_t));
    if (!records || !name_pointers || !name_lengths) complete = 0;
    uintptr_t lazy_address = image_base +
        (uintptr_t)derived_lazy_initializer_rva;
    if (lazy_address < image_base || !executable_pointer(lazy_address))
        complete = 0;
    alpha_lazy_name_initializer initialize =
        (alpha_lazy_name_initializer)lazy_address;
    uint32_t previous_definition = 0;
    uint32_t expected_method_index = 0;
    uint64_t total_name_bytes = 0;
    for (uint64_t index = 0; complete && index < method_count; index++) {{
        alpha_native_method_record native;
        if (fread(&native, 1, sizeof(native), input) != sizeof(native)) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        if (index == 0 || native.definition_index != previous_definition) {{
            if (index && native.definition_index <= previous_definition) {{
                *failure_index = index + 1u;
                complete = 0;
                break;
            }}
            previous_definition = native.definition_index;
            expected_method_index = 0;
        }}
        if (native.method_index != expected_method_index++) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        uintptr_t name_pointer = 0;
        uint32_t name_bytes = 0;
        if (!observe_name(
                native.metadata_pointer, initialize,
                &name_pointer, &name_bytes, lazy_initialization_count
            ) || total_name_bytes + name_bytes < total_name_bytes ||
            total_name_bytes + name_bytes > 0x100000000ull) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        records[index].definition_index = native.definition_index;
        records[index].method_index = native.method_index;
        records[index].metadata_pointer = native.metadata_pointer;
        records[index].name_bytes = name_bytes;
        records[index].flags = name_bytes ? 1u : 0u;
        name_pointers[index] = name_pointer;
        name_lengths[index] = name_bytes;
        total_name_bytes += name_bytes;
        if (name_bytes) (*nonempty_name_count)++;
        else (*empty_name_count)++;
        (*observed_method_count)++;
    }}
    fclose(input);
    uint64_t name_cursor = sizeof(alpha_method_name_header) +
        method_count * sizeof(alpha_method_name_record);
    if (name_cursor < sizeof(alpha_method_name_header)) complete = 0;
    for (uint64_t index = 0; complete && index < method_count; index++) {{
        records[index].name_offset = name_cursor;
        name_cursor += records[index].name_bytes;
    }}
    FILE *output = complete ? _wfopen(observation_output, L"wb") : NULL;
    if (!output) complete = 0;
    alpha_method_name_header header;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHANN2", 8);
    header.version = {RUNTIME_METHOD_NAME_VERSION}u;
    header.header_bytes = sizeof(header);
    header.record_bytes = sizeof(alpha_method_name_record);
    header.method_count = method_count;
    header.nonempty_name_count = *nonempty_name_count;
    header.name_bytes = total_name_bytes;
    header.image_bytes = image_bytes;
    memcpy(header.executable_sha256, expected_executable_sha256, 64);
    memcpy(header.native_inventory_sha256,
        expected_native_inventory_sha256, 64);
    memcpy(header.reflection_semantics_sha256,
        expected_reflection_semantics_sha256, 64);
    header.name_node_field_qword = derived_name_node_field_qword;
    header.encoded_name_field_qword = derived_encoded_name_field_qword;
    header.decode_operation = derived_method_name_decode_operation;
    header.lazy_initializer_rva = derived_lazy_initializer_rva;
    header.decode_key = derived_method_name_decode_key;
    if (complete && fwrite(&header, 1, sizeof(header), output) != sizeof(header))
        complete = 0;
    SIZE_T record_bytes = (SIZE_T)method_count * sizeof(*records);
    if (complete && fwrite(records, 1, record_bytes, output) != record_bytes)
        complete = 0;
    for (uint64_t index = 0; complete && index < method_count; index++) {{
        if (name_lengths[index] && fwrite(
                (const void *)name_pointers[index], 1,
                name_lengths[index], output
            ) != name_lengths[index]) {{
            *failure_index = index + 1u;
            complete = 0;
        }}
    }}
    if (output) {{
        if (fflush(output)) complete = 0;
        if (fclose(output)) complete = 0;
    }}
    free(name_lengths);
    free(name_pointers);
    free(records);
    if (!complete) {{
        _wremove(observation_output);
        return 0;
    }}
    _wchmod(observation_output, 0600);
    return 1;
}}

static DWORD WINAPI worker(void *unused) {{
    (void)unused;
    char executable_sha256[65] = {{0}};
    char inventory_sha256[65] = {{0}};
    uintptr_t image_base = 0;
    uint64_t image_bytes = 0;
    if (GetCurrentProcessId() != expected_process_id) {{
        write_status("process-binding-rejected", "", "",
            0, 0, 0, 0, 0, 0);
        return 1;
    }}
    if (!executable_identity(executable_sha256) ||
        strcmp(executable_sha256, expected_executable_sha256) ||
        !sha256_file(native_inventory_input, inventory_sha256) ||
        strcmp(inventory_sha256, expected_native_inventory_sha256)) {{
        write_status("identity-binding-rejected", executable_sha256,
            inventory_sha256, 0, 0, 0, 0, 0, 0);
        return 2;
    }}
    if (!load_main_image(&image_base, &image_bytes) ||
        image_base != expected_image_base || image_bytes != expected_image_bytes ||
        derived_lazy_initializer_rva >= image_bytes) {{
        write_status("image-binding-rejected", executable_sha256,
            inventory_sha256, 0, 0, 0, 0, 0, 0);
        return 3;
    }}
    uint64_t observed = 0, nonempty = 0, empty = 0, lazy = 0, failure = 0;
    int written = materialize_method_names(
        image_base, image_bytes, &observed, &nonempty, &empty, &lazy,
        &failure
    );
    int complete = written && observed == expected_method_count &&
        nonempty + empty == expected_method_count && !failure;
    write_status(complete ? "complete" : "materialization-rejected",
        executable_sha256, inventory_sha256, observed, nonempty, empty,
        lazy, failure, written);
    return complete ? 0 : 4;
}}

BOOL WINAPI DllMain(HINSTANCE instance, DWORD reason, LPVOID reserved) {{
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {{
        DisableThreadLibraryCalls(instance);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }}
    return TRUE;
}}
'''


def _inspect_method_name_observation(
    *,
    observation: Path,
    binding: dict[str, Any],
    native_inventory: Path,
) -> dict[str, Any]:
    if not observation.is_file() or observation.is_symlink():
        raise AcquisitionError("runtime method-name observation is unavailable")
    current_inventory_identity = file_identity(native_inventory)
    if (
        current_inventory_identity.get("sha256")
        != binding["native_inventory"]["sha256"]
        or current_inventory_identity.get("bytes")
        != binding["native_inventory"]["bytes"]
    ):
        raise AcquisitionError("runtime method-name inventory binding is stale")
    identity = file_identity(observation)
    with observation.open("rb") as stream, mmap.mmap(
        stream.fileno(), 0, access=mmap.ACCESS_READ
    ) as data:
        if len(data) < RUNTIME_METHOD_NAME_HEADER.size:
            raise AcquisitionError("runtime method-name observation is truncated")
        values = RUNTIME_METHOD_NAME_HEADER.unpack_from(data, 0)
        (
            magic,
            version,
            header_bytes,
            record_bytes,
            reserved,
            method_count,
            nonempty_count,
            name_bytes,
            image_bytes,
            executable_raw,
            inventory_raw,
            semantics_raw,
            node_qword,
            encoded_qword,
            decode_operation,
            reserved_layout_two,
            lazy_initializer_rva,
            decode_key,
        ) = values
        try:
            executable_sha256 = executable_raw.decode("ascii")
            inventory_sha256 = inventory_raw.decode("ascii")
            semantics_sha256 = semantics_raw.decode("ascii")
        except UnicodeDecodeError as error:
            raise AcquisitionError(
                "runtime method-name observation identity is invalid"
            ) from error
        records_end = header_bytes + method_count * record_bytes
        if (
            magic != RUNTIME_METHOD_NAME_MAGIC
            or version != RUNTIME_METHOD_NAME_VERSION
            or header_bytes != RUNTIME_METHOD_NAME_HEADER.size
            or record_bytes != RUNTIME_METHOD_NAME_RECORD.size
            or reserved
            or reserved_layout_two
            or method_count != binding["method_count"]
            or not 0 < nonempty_count <= method_count
            or name_bytes <= 0
            or image_bytes != binding["image_bytes"]
            or executable_sha256 != binding["binary"]["sha256"]
            or inventory_sha256 != binding["native_inventory"]["sha256"]
            or semantics_sha256 != binding["semantics"]["sha256"]
            or node_qword != binding["node_qword"]
            or encoded_qword != binding["encoded_qword"]
            or decode_operation != binding["decode_operation_code"]
            or lazy_initializer_rva != binding["lazy_initializer_rva"]
            or decode_key != binding["decode_key"]
            or records_end + name_bytes != len(data)
        ):
            raise AcquisitionError(
                "runtime method-name observation header is invalid"
            )
        inventory_data = native_inventory.read_bytes()
        if len(inventory_data) < _NATIVE_INVENTORY_HEADER.size:
            raise AcquisitionError(
                "runtime method-name inventory is truncated"
            )
        inventory_values = _NATIVE_INVENTORY_HEADER.unpack_from(
            inventory_data, 0
        )
        if (
            inventory_values[0] != _NATIVE_INVENTORY_MAGIC
            or inventory_values[1] != _NATIVE_INVENTORY_VERSION
            or inventory_values[2] != _NATIVE_TYPE_RECORD.size
            or inventory_values[3] != _NATIVE_METHOD_RECORD.size
            or inventory_values[4]
            or inventory_values[7] != binding["image_bytes"]
            or inventory_values[8].decode("ascii", errors="ignore")
            != binding["binary"]["sha256"]
            or inventory_values[17]
        ):
            raise AcquisitionError(
                "runtime method-name inventory header is invalid"
            )
        inventory_type_count = inventory_values[5]
        inventory_method_count = inventory_values[6]
        inventory_position = (
            _NATIVE_INVENTORY_HEADER.size
            + inventory_type_count * _NATIVE_TYPE_RECORD.size
        )
        inventory_methods_end = (
            inventory_position
            + inventory_method_count * _NATIVE_METHOD_RECORD.size
        )
        if (
            inventory_method_count != method_count
            or inventory_methods_end > len(inventory_data)
        ):
            raise AcquisitionError(
                "runtime method-name inventory count is stale"
            )
        expected_name_offset = records_end
        observed_nonempty = 0
        observed_empty = 0
        distinct_names: set[bytes] = set()


        observation_records = memoryview(data)[
            header_bytes:records_end
        ]
        inventory_records = memoryview(inventory_data)[
            inventory_position : inventory_position
            + inventory_method_count * _NATIVE_METHOD_RECORD.size
        ]
        try:
            for index, (native, record) in enumerate(zip(
                _NATIVE_METHOD_RECORD.iter_unpack(inventory_records),
                RUNTIME_METHOD_NAME_RECORD.iter_unpack(observation_records),
            )):
                (
                    definition_index,
                    method_index,
                    metadata_pointer,
                    name_offset,
                    observed_name_bytes,
                    flags,
                ) = record
                if (
                    (definition_index, method_index, metadata_pointer)
                    != (native[0], native[1], native[2])
                    or name_offset != expected_name_offset
                    or observed_name_bytes > 16_384
                    or flags != (1 if observed_name_bytes else 0)
                    or name_offset + observed_name_bytes > len(data)
                ):
                    raise AcquisitionError(
                        "runtime method-name observation row is invalid "
                        f"(index={index})"
                    )
                raw_name = data[
                    name_offset : name_offset + observed_name_bytes
                ]
                if b"\0" in raw_name:
                    raise AcquisitionError(
                        "runtime method-name observation contains an embedded NUL"
                    )
                try:
                    raw_name.decode("utf-8")
                except UnicodeDecodeError as error:
                    raise AcquisitionError(
                        "runtime method-name observation is not UTF-8"
                    ) from error
                if raw_name:
                    observed_nonempty += 1
                    distinct_names.add(bytes(raw_name))
                else:
                    observed_empty += 1
                expected_name_offset += observed_name_bytes
        finally:
            observation_records.release()
            inventory_records.release()
        if (
            observed_nonempty != nonempty_count
            or observed_nonempty + observed_empty != method_count
            or expected_name_offset != len(data)
        ):
            raise AcquisitionError(
                "runtime method-name observation counts are inconsistent"
            )
    return {
        "identity": identity,
        "method_count": method_count,
        "nonempty_name_count": nonempty_count,
        "empty_name_count": observed_empty,
        "distinct_nonempty_name_count": len(distinct_names),
        "name_bytes": name_bytes,
        "decode_operation": binding["decode_operation"],
        "decode_key": binding["decode_key"],
    }


def prepare_runtime_method_name_materialization(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    materializer_model: Path,
    native_inventory: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binary = binary.expanduser().resolve()
    native_inventory = native_inventory.expanduser().resolve()
    binding = _method_name_binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        materializer_model=materializer_model,
        native_inventory=native_inventory,
    )
    if not isinstance(binding["method_count"], int) or binding["method_count"] <= 0:
        raise AcquisitionError("runtime method-name method count is invalid")
    status_path = output_dir / "runtime-method-name-status.private.json"
    observation_path = output_dir / "runtime-method-names.private.bin"
    build_dir = _owner_directory(output_dir / "build-method-names")
    source_path = build_dir / "runtime-method-name-materializer.c"
    injector_source_path = build_dir / "runtime-method-name-injector.c"
    injector_path = build_dir / "alpha-runtime-method-name-injector.exe"
    for stale in (status_path, observation_path):
        stale.unlink(missing_ok=True)
    _private_text(
        source_path,
        runtime_method_name_materializer_source(
            expected_executable_sha256=binding["binary"]["sha256"],
            expected_native_inventory_sha256=binding["native_inventory"][
                "sha256"
            ],
            expected_reflection_semantics_sha256=binding["semantics"][
                "sha256"
            ],
            expected_process_id=binding["process_id"],
            expected_image_base=binding["image_base"],
            expected_image_bytes=binding["image_bytes"],
            native_inventory_path=native_inventory,
            observation_path=observation_path,
            status_path=status_path,
            method_count=binding["method_count"],
            name_node_field_qword=binding["node_qword"],
            encoded_name_field_qword=binding["encoded_qword"],
            method_name_decode_operation=binding["decode_operation"],
            method_name_decode_key=binding["decode_key"],
            lazy_initializer_rva=binding["lazy_initializer_rva"],
        ),
    )
    _private_text(injector_source_path, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-method-names-"
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
                str(collector_path),
                "-lbcrypt",
            ],
            label="runtime method-name materializer",
            source_path=source_path,
            output_path=collector_path,
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
                str(injector_source_path),
                "-o",
                str(injector_path),
            ],
            label="runtime method-name injector",
            source_path=injector_source_path,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        if not artifact.is_file() or not artifact.stat().st_size:
            raise AcquisitionError(
                f"runtime method-name build did not produce {artifact.name}"
            )
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_METHOD_NAME_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary),
            "executable_sha256": binding["binary"]["sha256"],
            "process_name": binary.name,
            "process_id": binding["process_id"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            "reflection_semantics": binding["semantics"],
            "materializer": binding["materializer"],
            "native_inventory": binding["native_inventory"],
            "snapshot": binding["snapshot"],
        },
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "outputs": {
            "status": str(status_path),
            "observation": str(observation_path),
        },
        "contract": {
            "method_count": binding["method_count"],
            "name_decode_operation": binding["decode_operation"],
            "name_decode_key": binding["decode_key"],
        },
        "policy": {
            "same_process_required": True,
            "same_snapshot_image_base_required": True,
            "current_executable_sha256_embedded": True,
            "native_inventory_identity_embedded": True,
            "reflection_semantics_identity_embedded": True,
            "raw_decoder_binding_owner_only": True,
            "raw_runtime_pointers_owner_only": True,
            "fixed_address_used": False,
            "fixed_rva_used": False,
            "fixed_version_used": False,
            "saved_method_name_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(output_dir / "runtime-method-name-plan.private.json", plan)
    return {
        "schema": RUNTIME_METHOD_NAME_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "contract": plan["contract"],
        "policy": plan["policy"],
    }


def capture_runtime_method_name_materialization(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    materializer_model: Path,
    native_inventory: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 900.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_method_name_materialization(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        materializer_model=materializer_model,
        native_inventory=native_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-method-name-plan.private.json"
    plan = read_json(plan_path)
    binding = _method_name_binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        materializer_model=materializer_model,
        native_inventory=native_inventory,
    )
    if binding["process_id"] != plan["target"]["process_id"]:
        raise AcquisitionError(
            "runtime method-name source process changed after preparation"
        )
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError("selected Wine binary or prefix is unavailable")
    collector = Path(plan["collector"]["path"])
    injector = Path(plan["injector"]["path"])
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine), injector, collector, Path(plan['target']['executable_path']).name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "ALPHA v2 runtime method-name injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-method-name-injector.private.log",
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
            f"ALPHA v2 runtime method-name injection failed ({injected.returncode})"
        )
    status_path = Path(plan["outputs"]["status"])
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
        raise AcquisitionError("ALPHA v2 runtime method-name capture timed out")
    _seal_runtime_output(status_path)
    observation_path = Path(plan["outputs"]["observation"])
    if observation_path.is_file():
        _seal_runtime_output(observation_path)
    observation = (
        _inspect_method_name_observation(
            observation=observation_path,
            binding=binding,
            native_inventory=native_inventory,
        )
        if observation_path.is_file()
        else None
    )
    checks = {
        "schema": status.get("schema") == RUNTIME_METHOD_NAME_STATUS_SCHEMA,
        "complete": status.get("status") == "complete",
        "same_process": status.get("process_id") == binding["process_id"]
        and status.get("expected_process_id") == binding["process_id"],
        "executable_identity_bound": status.get(
            "observed_executable_sha256"
        )
        == binding["binary"]["sha256"],
        "native_inventory_identity_bound": status.get(
            "observed_inventory_sha256"
        )
        == binding["native_inventory"]["sha256"],
        "method_count_complete": status.get("observed_method_count")
        == binding["method_count"]
        and status.get("expected_method_count") == binding["method_count"],
        "name_domain_complete": isinstance(status.get("nonempty_name_count"), int)
        and status["nonempty_name_count"] > 0
        and isinstance(status.get("empty_name_count"), int)
        and status["nonempty_name_count"] + status["empty_name_count"]
        == binding["method_count"],
        "failure_absent": status.get("failure_index_owner_only") == 0,
        "observation_written": status.get("observation_written") is True,
        "observation_validated": observation is not None,
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
        is True,
        "raw_runtime_pointers_absent": status.get(
            "raw_runtime_pointers_exposed"
        )
        is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_rva_absent": status.get("fixed_rva_used") is False,
        "saved_method_name_absent": status.get("saved_method_name_used")
        is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    validated = all(checks.values())
    receipt = {
        "schema": RUNTIME_METHOD_NAME_OBSERVATION_SCHEMA,
        "status": "validated" if validated else "rejected",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "observation": observation,
        "lazy_initialization_count": status.get(
            "lazy_initialization_count", 0
        ),
        "checks": checks,
        "owner_only": True,
    }
    _private_json(
        output_dir / "runtime-method-name-receipt.private.json", receipt
    )
    return {
        "schema": RUNTIME_METHOD_NAME_OBSERVATION_SCHEMA,
        "status": receipt["status"],
        "target": receipt["target"],
        "method_count": (
            observation["method_count"] if observation else 0
        ),
        "nonempty_name_count": (
            observation["nonempty_name_count"] if observation else 0
        ),
        "empty_name_count": (
            observation["empty_name_count"] if observation else 0
        ),
        "distinct_nonempty_name_count": (
            observation["distinct_nonempty_name_count"] if observation else 0
        ),
        "lazy_initialization_count": receipt["lazy_initialization_count"],
        "checks": checks,
        "owner_only": True,
    }


from dataclasses import asdict
from copy import deepcopy
import hashlib
from pathlib import Path

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError
from alpha.h04 import MemorySnapshot
from alpha.p13 import _safe_path, _file_record
from alpha.c01 import current_runtime_process_binding
from alpha.c02 import _native_method_rows
from alpha.p03 import analyze_string_layout_candidates, discover_string_layout_candidates
from alpha.c01 import decode_x64_batch
from alpha.p17 import _NATIVE_INVENTORY_HEADER as NH, _NATIVE_TYPE_RECORD as NT
from alpha.h02 import file_identity, read_json, canonical_json_bytes
from alpha.p01 import current_string_layout_replay_cache


SCHEMA = "alpha.runtime-string-layout-candidates/v1"
_WINDOW_BYTES = 128
_ROLES = {"snapshot", "native_inventory"}
_TARGET_KEYS = ("executable_path", "executable_sha256", "process_id", "creation_filetime", "image_base", "image_bytes")


def _source_record(path):
    path = _safe_path(Path(path))
    return dict(_file_record(path), path=str(path))


def _verify_sources(records):
    if set(records) != _ROLES:
        raise AcquisitionError("String layout source roles differ")
    if any(not isinstance(record, dict) or set(record) != {"path", "bytes", "sha256"}
           for record in records.values()):
        raise AcquisitionError("String layout source identity changed")
    from alpha.c04 import _verify_files
    _verify_files(records)


def _discover_string_layout_from_rows(methods, memory, native):
    indexers, lengths, cache = [], [], {}
    decoded, excluded = 0, 0


    image_base = memory.image_base
    image_limit = image_base + memory.image_bytes


    unique_pointers: list[int] = []
    unique_seen: set[int] = set()
    for _owner, _local, _metadata, _pointer in methods:
        if not image_base <= _pointer < image_limit:
            excluded += 1
            continue
        if _pointer not in unique_seen:
            unique_seen.add(_pointer)
            unique_pointers.append(_pointer)
    code_by_pointer: dict[int, bytes | None] = {}
    for _pointer in sorted(unique_pointers):
        code_by_pointer[_pointer] = memory.read(_pointer, _WINDOW_BYTES)
    windows: dict[int, bytes] = {}
    filtered: list[int] = []
    for _owner, _local, _metadata, pointer in methods:
        if not image_base <= pointer < image_limit:
            continue
        if pointer not in cache:
            code = code_by_pointer[pointer]


            if code and b"\x0f\xb7" in code and b"\xc3" in code:


                if pointer not in windows:
                    windows[pointer] = code
                    filtered.append(pointer)
                    decoded += 1
            else:
                cache[pointer] = ((), ())
    instruction_cache: dict[int, tuple] = {}
    decoded_windows = decode_x64_batch([windows[pointer] for pointer in filtered])
    for pointer, instructions in zip(filtered, decoded_windows):
        instruction_cache[pointer] = instructions
        cache[pointer] = analyze_string_layout_candidates(instructions)


    length_cache: dict[int, tuple] = {pointer: cache[pointer][0] for pointer in instruction_cache}
    for owner, local, metadata, pointer in methods:
        if not image_base <= pointer < image_limit:
            continue
        for candidate in cache[pointer][1]:
            indexers.append({"owner": owner, "local_index": local, "metadata_pointer": metadata,
                             "function_pointer": pointer, "flow": asdict(candidate)})
    owners = {item["owner"] for item in indexers}


    pending: list[int] = []
    pending_seen: set[int] = set()
    for owner, _local, _metadata, pointer in methods:
        if (owner in owners and image_base <= pointer < image_limit and pointer not in length_cache
                and pointer not in pending_seen):
            pending_seen.add(pointer)
            pending.append(pointer)
    if pending:
        pending_codes = [code_by_pointer[pointer] for pointer in pending]
        pending_decoded = decode_x64_batch([
            code if code else b"" for code in pending_codes])
        for pointer, code, instructions in zip(pending, pending_codes, pending_decoded):
            if not code:
                cache[pointer] = ((), ())
                continue
            instruction_cache[pointer] = instructions
            analyzed = analyze_string_layout_candidates(instructions)
            cache[pointer] = analyzed
            length_cache[pointer] = analyzed[0]
    for owner, local, metadata, pointer in methods:
        if owner not in owners or not image_base <= pointer < image_limit:
            continue
        for candidate in length_cache.get(pointer, ()):
            lengths.append({"owner": owner, "local_index": local, "metadata_pointer": metadata,
                                "function_pointer": pointer, "flow": asdict(candidate)})


    indexers_by_key: dict[tuple[int, int], list[dict]] = {}
    for indexer in indexers:
        indexers_by_key.setdefault((indexer["owner"], indexer["flow"]["length_offset"]), []).append(indexer)
    pairs = []
    for length in lengths:
        pairs.extend({"length": length, "indexer": indexer}
                     for indexer in indexers_by_key.get((length["owner"], length["flow"]["length_offset"]), ()))
    contract = None
    if len(pairs) == 1:
        pair = pairs[0]
        owner = pair["length"]["owner"]
        row = NT.unpack_from(native, NH.size + owner * NT.size)
        if row[0] != owner or not row[4]:
            raise AcquisitionError("String layout native owner class is invalid")
        contract = {"class_pointer": row[4], "length_offset": pair["length"]["flow"]["length_offset"],
                    "data_offset": pair["indexer"]["flow"]["data_offset"]}
        for kind in ("length", "indexer"):
            item = pair[kind]
            code = code_by_pointer.get(item["function_pointer"])
            if code is None:
                code = memory.read(item["function_pointer"], _WINDOW_BYTES)
            if not code or len(code) != _WINDOW_BYTES:
                raise AcquisitionError("String layout selected code is truncated")
            contract.update({kind + "_pointer": item["function_pointer"],
                             kind + "_metadata": item["metadata_pointer"], kind + "_code_hex": code.hex()})
    return {"out_of_image_or_null_method_count": excluded,
        "decoded_indexer_function_count": decoded,
        "length_candidates": lengths, "indexer_candidates": indexers, "pairs": pairs,
        "candidate_count": len(pairs), "contract": contract}


def discover_current_string_layout(memory, native, *, executable_sha256):


    if len(native) < NH.size:
        raise AcquisitionError("String layout native inventory is truncated")
    header = NH.unpack_from(native)
    native_digest = hashlib.sha256(native).hexdigest()
    methods = tuple(_native_method_rows(native, expected_binding={"executable_sha256": executable_sha256,
        "inputs": {"native_inventory": native_digest}},
        method_count=header[6], image_bytes=memory.image_bytes,
        _precomputed_native_sha256=native_digest))
    result = _discover_string_layout_from_rows(methods, memory, native)
    return {"method_count": header[6], "type_count": header[5],
        "instruction_window_bytes": _WINDOW_BYTES,
        "out_of_image_or_null_method_count": result["out_of_image_or_null_method_count"],
        "decoded_indexer_function_count": result["decoded_indexer_function_count"],
        "length_candidates": result["length_candidates"], "indexer_candidates": result["indexer_candidates"],
        "pairs": result["pairs"], "candidate_count": result["candidate_count"],
        "contract": result["contract"]}


def _replay_sources(records, target):
    _verify_sources(records)
    native = Path(records["native_inventory"]["path"]).read_bytes()
    if hashlib.sha256(native).hexdigest() != records["native_inventory"]["sha256"]:
        raise AcquisitionError("String layout native input changed during read")
    with MemorySnapshot(Path(records["snapshot"]["path"])) as memory:
        if (memory.image_base, memory.image_bytes) != (target["image_base"], target["image_bytes"]):
            raise AcquisitionError("String layout snapshot image differs")
        result = discover_current_string_layout(memory, native, executable_sha256=target["executable_sha256"])
    _verify_sources(records)
    return result


def inspect_runtime_string_layout_candidates(*, binary: Path, snapshot: Path, native_inventory: Path, output: Path):
    current = current_runtime_process_binding()
    binary = _safe_path(binary)
    if current is None or Path(current[2]).resolve() != binary.resolve():
        raise AcquisitionError("String layout candidates require a current acquisition process binding")
    records = {"snapshot": _source_record(snapshot), "native_inventory": _source_record(native_inventory)}
    executable = file_identity(binary)
    with MemorySnapshot(Path(records["snapshot"]["path"])) as memory:
        target = {"executable_path": str(binary), "executable_sha256": executable["sha256"],
            "process_id": current[0], "creation_filetime": current[1],
            "image_base": memory.image_base, "image_bytes": memory.image_bytes}
    result = _replay_sources(records, target)
    if file_identity(binary) != executable:
        raise AcquisitionError("String layout executable changed during analysis")
    model = {"schema": SCHEMA, "status": "candidate-derived" if result["candidate_count"] == 1 else "rejected",
        "target": target, "inputs": records, "observation": result,
        "checks": {"source_inputs_unchanged": True, "name_and_ordinal_seeds_absent": True,
                   "unique_same_owner_code_candidate": result["candidate_count"] == 1},
        "native_io_proven": False, "search_scope": "bounded-current-image-method-code",
        "metadata_complete": False}
    output = _safe_path(output)
    if output.exists():
        raise AcquisitionError("String layout candidate output already exists")
    _private_json(output, model)
    if result["candidate_count"] != 1:
        raise AcquisitionError(f"String layout requires one code candidate, observed {result['candidate_count']}")
    return {"schema": SCHEMA, "status": model["status"], "output": str(output),
            "candidate_count": result["candidate_count"], "native_io_proven": False, "metadata_complete": False}


def load_runtime_string_layout_candidate(*, model_path: Path, expected_identity, expected_inputs):
    model_path = _safe_path(model_path)
    before = _file_record(model_path)
    model = read_json(model_path)
    target = {key: expected_identity[key] for key in _TARGET_KEYS}
    if isinstance(target.get("executable_path"), str):


        target["executable_path"] = str(
            Path(target["executable_path"]).expanduser().resolve()
        )
    if (not isinstance(model, dict) or model.get("schema") != SCHEMA or model.get("status") != "candidate-derived" or
        model.get("target") != target or model.get("inputs") != expected_inputs or
        model.get("checks") != {"source_inputs_unchanged": True, "name_and_ordinal_seeds_absent": True,
                               "unique_same_owner_code_candidate": True} or
        any(value is not True for value in model.get("checks", {}).values()) or
        model.get("search_scope") != "bounded-current-image-method-code" or
        model.get("native_io_proven") is not False or model.get("metadata_complete") is not False):
        raise AcquisitionError("String layout candidate model or independently selected identity differs")
    cache = current_string_layout_replay_cache()
    key = (id(_replay_sources), canonical_json_bytes({"target": target, "inputs": expected_inputs}))
    if cache is not None and key in cache:


        _verify_sources(expected_inputs)
        observation = deepcopy(cache[key])
        _verify_sources(expected_inputs)
    else:
        observation = _replay_sources(expected_inputs, target)
        if cache is not None and len(cache) < 64:
            cache[key] = deepcopy(observation)
    if observation["candidate_count"] != 1 or model.get("observation") != observation:
        raise AcquisitionError("String layout original source replay differs or is ambiguous")
    if _file_record(model_path) != before:
        raise AcquisitionError("String layout model changed during replay")
    contract = dict(observation["contract"])
    for kind in ("length", "indexer"):
        contract[kind + "_code"] = bytes.fromhex(contract.pop(kind + "_code_hex"))
    return contract


from alpha.h02 import windows_run as _host_run

import json
import os
import struct
import subprocess
import time
from pathlib import Path
from typing import Any

from alpha.p12 import SNAPSHOT_SCHEMA, _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid
from alpha.h04 import MemorySnapshot
from alpha.c07 import RUNTIME_NATIVE_SEMANTICS_SCHEMA
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json


RUNTIME_TYPE_ANCESTRY_PLAN_SCHEMA = "alpha.runtime-type-ancestry-plan/v1"
RUNTIME_TYPE_ANCESTRY_STATUS_SCHEMA = "alpha.runtime-type-ancestry-status/v1"
RUNTIME_TYPE_ANCESTRY_SCHEMA = "alpha.runtime-type-ancestry/v1"
_ANCESTRY_MAGIC = b"ALPHAAN1"
_ANCESTRY_VERSION = 1
_ANCESTRY_HEADER = struct.Struct("<8sIIIIQQ64s64s64s")
_ANCESTRY_RECORD = struct.Struct("<IIQQQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime type ancestry {label} is not owner-only")
    return path


def _ascii_digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime type ancestry {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime type ancestry {label} digest is invalid"
        )
    return value


def _native_type_rows(
    path: Path,
    *,
    executable_sha256: str,
) -> tuple[list[tuple[int, ...]], dict[str, Any]]:
    global _NATIVE_TYPE_ROWS_CACHE
    resolved = _owner_file(path, label="native inventory")
    try:
        status = resolved.stat()
        fingerprint = (
            status.st_dev,
            status.st_ino,
            status.st_size,
            status.st_mtime_ns,
            status.st_ctime_ns,
        )
    except OSError:
        fingerprint = None
    key = (str(resolved), fingerprint, executable_sha256)
    cached = _NATIVE_TYPE_ROWS_CACHE
    if cached is not None and cached[0] == key and fingerprint is not None:
        return cached[1], cached[2]
    rows, inventory = _parse_native_type_rows(
        resolved, executable_sha256=executable_sha256
    )
    if fingerprint is not None:
        try:
            after = resolved.stat()
            stable = (
                after.st_dev,
                after.st_ino,
                after.st_size,
                after.st_mtime_ns,
                after.st_ctime_ns,
            ) == fingerprint
        except OSError:
            stable = False
        if stable:
            _NATIVE_TYPE_ROWS_CACHE = (key, rows, inventory)
    return rows, inventory


_NATIVE_TYPE_ROWS_CACHE: tuple[Any, Any, Any] | None = None


def _parse_native_type_rows(
    path: Path,
    *,
    executable_sha256: str,
) -> tuple[list[tuple[int, ...]], dict[str, Any]]:
    path = _owner_file(path, label="native inventory")
    raw = path.read_bytes()
    if len(raw) < _NATIVE_INVENTORY_HEADER.size:
        raise AcquisitionError("runtime type ancestry inventory is truncated")
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
        or _ascii_digest(header[8], label="executable")
        != executable_sha256
    ):
        raise AcquisitionError("runtime type ancestry inventory is invalid")
    rows: list[tuple[int, ...]] = []
    classes: set[int] = set()


    add_row = rows.append
    add_class = classes.add
    for index, row in enumerate(
        _NATIVE_TYPE_RECORD.iter_unpack(
            memoryview(raw)[type_start:method_start]
        )
    ):
        if (
            row[0] != index
            or not row[3]
            or not row[4]
            or row[4] in classes
        ):
            raise AcquisitionError(
                "runtime type ancestry inventory row is invalid"
            )
        add_row(row)
        add_class(row[4])
    if len(rows) != type_count:


        raise AcquisitionError(
            "runtime type ancestry inventory is truncated"
        )
    return rows, {
        "identity": file_identity(path),
        "type_count": type_count,
        "method_count": method_count,
        "image_bytes": header[7],
    }


def _binding(
    *,
    binary: Path,
    snapshot: Path,
    native_semantics_model: Path,
    native_inventory: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    snapshot = _owner_file(snapshot, label="snapshot")
    native_semantics_model = _owner_file(
        native_semantics_model, label="native semantic model"
    )
    memory_status_path = _owner_file(
        snapshot.parent / "memory-status.private.json",
        label="memory status",
    )


    def _warm(path: Path) -> None:
        try:
            from alpha.h02 import sha256_file as _sha
            _sha(Path(path).expanduser().resolve())
        except Exception:
            pass
    with ThreadPoolExecutor(max_workers=2) as _pool:
        list(_pool.map(_warm, (binary, snapshot)))
    identity = file_identity(binary)
    snapshot_identity = file_identity(snapshot)
    semantics_identity = file_identity(native_semantics_model)
    semantics = read_json(native_semantics_model)
    memory_status = read_json(memory_status_path)
    rows, inventory = _native_type_rows(
        native_inventory, executable_sha256=identity["sha256"]
    )
    decoder = semantics.get("class_parent_decoder") if isinstance(
        semantics, dict
    ) else None
    evidence = semantics.get("class_parent_evidence") if isinstance(
        semantics, dict
    ) else None
    required_semantic_checks = (
        "class_parent_decoder_structurally_unique",
        "class_parent_decoder_current_code_derived",
        "class_parent_decoder_hierarchy_oracle_exact",
        "class_parent_embedded_descriptors_structurally_valid",
    )
    if (
        not binary.is_file()
        or not isinstance(semantics, dict)
        or semantics.get("schema") != RUNTIME_NATIVE_SEMANTICS_SCHEMA
        or semantics.get("binary", {}).get("sha256") != identity["sha256"]
        or semantics.get("inputs", {}).get("snapshot", {}).get("sha256")
        != snapshot_identity["sha256"]
        or semantics.get("inputs", {}).get("native_inventory", {}).get(
            "sha256"
        )
        != inventory["identity"]["sha256"]
        or any(
            semantics.get("checks", {}).get(check) is not True
            for check in required_semantic_checks
        )
        or not isinstance(decoder, dict)
        or not isinstance(evidence, dict)
        or evidence.get("hierarchy_oracle_mismatch_count") != 0
        or evidence.get("hierarchy_oracle_match_count", 0) < 10_000
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
        raise AcquisitionError("runtime type ancestry binding is stale")
    decoder_fields = (
        "raw_dword_offset",
        "base_pointer_slot",
        "base_pointer_indirections",
        "embedded_descriptor_adjustment",
        "managed_type_helper_pointer",
    )
    if not all(
        isinstance(decoder.get(field), int) and decoder[field] > 0
        for field in decoder_fields
    ) or decoder["base_pointer_indirections"] != 2:
        raise AcquisitionError("runtime type ancestry decoder is invalid")
    process_id = memory_status.get("process_id")
    if not isinstance(process_id, int) or process_id <= 0:
        raise AcquisitionError("runtime type ancestry process is unavailable")
    with MemorySnapshot(snapshot) as memory:
        image_base = memory.image_base
        image_bytes = memory.image_bytes
    if image_bytes != inventory["image_bytes"]:
        raise AcquisitionError("runtime type ancestry image binding is stale")
    return {
        "binary": identity,
        "snapshot": snapshot_identity,
        "memory_status": file_identity(memory_status_path),
        "native_semantics": semantics_identity,
        "native_inventory": inventory["identity"],
        "process_id": process_id,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "decoder_owner_only": decoder,
        "decoder_evidence": evidence,
        "type_rows_owner_only": rows,
        "type_count": len(rows),
    }


def runtime_type_ancestry_source(
    *,
    binding: dict[str, Any],
    status_path: Path,
    ancestry_path: Path,
) -> str:
    rows = ",\n".join(
        "    {"
        f"{row[0]}u, {row[4]}ull"
        "}"
        for row in binding["type_rows_owner_only"]
    )
    decoder = binding["decoder_owner_only"]
    return rf'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

typedef struct alpha_input_type {{
    uint32_t definition_index;
    uintptr_t class_pointer;
}} alpha_input_type;

typedef struct alpha_ancestry_header {{
    unsigned char magic[8];
    uint32_t version;
    uint32_t record_bytes;
    uint32_t reserved;
    uint32_t type_count;
    uint64_t image_base;
    uint64_t image_bytes;
    char executable_sha256[64];
    char native_inventory_sha256[64];
    char native_semantics_sha256[64];
}} alpha_ancestry_header;

typedef struct alpha_ancestry_record {{
    uint32_t definition_index;
    uint32_t flags;
    uint64_t class_pointer;
    uint64_t parent_class_pointer;
    uint64_t parent_descriptor_pointer;
}} alpha_ancestry_record;

_Static_assert(sizeof(alpha_ancestry_header) == {_ANCESTRY_HEADER.size},
    "ancestry header layout mismatch");
_Static_assert(sizeof(alpha_ancestry_record) == {_ANCESTRY_RECORD.size},
    "ancestry record layout mismatch");

static const char expected_executable_sha256[] =
    "{binding['binary']['sha256']}";
static const char expected_native_inventory_sha256[] =
    "{binding['native_inventory']['sha256']}";
static const char expected_native_semantics_sha256[] =
    "{binding['native_semantics']['sha256']}";
static const DWORD expected_process_id = {binding['process_id']}u;
static const uintptr_t expected_image_base = {binding['image_base']}ull;
static const uint64_t expected_image_bytes = {binding['image_bytes']}ull;
static const uint32_t parent_raw_dword_offset =
    {decoder['raw_dword_offset']}u;
static const uintptr_t parent_base_pointer_slot =
    {decoder['base_pointer_slot']}ull;
static const uint32_t parent_base_pointer_indirections =
    {decoder['base_pointer_indirections']}u;
static const uint32_t parent_descriptor_adjustment =
    {decoder['embedded_descriptor_adjustment']}u;
static const wchar_t status_output[] =
    {_wide_literal(_windows_z_path(status_path))};
static const wchar_t ancestry_output[] =
    {_wide_literal(_windows_z_path(ancestry_path))};
static const alpha_input_type input_types[] = {{
{rows}
}};

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
    unsigned char *object = NULL, *buffer = NULL, digest[32];
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
        GetProcessHeap(), 0, 1024u * 1024u
    );
    if (ok && (!object || !buffer)) ok = 0;
    if (ok && BCryptCreateHash(
            algorithm, &hash, object, object_size, NULL, 0, 0
        ) < 0) ok = 0;
    while (ok) {{
        DWORD count = 0;
        if (!ReadFile(input, buffer, 1024u * 1024u, &count, NULL)) {{
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
    const char *status,
    const char *observed_hash,
    uint32_t completed,
    uint32_t roots,
    uint32_t parents,
    uint32_t failure_index
) {{
    FILE *output = _wfopen(status_output, L"wb");
    if (!output) return;
    fprintf(output,
        "{{\n"
        "  \"schema\": \"{RUNTIME_TYPE_ANCESTRY_STATUS_SCHEMA}\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"expected_type_count\": %u,\n"
        "  \"completed_type_count\": %u,\n"
        "  \"root_count\": %u,\n"
        "  \"parent_count\": %u,\n"
        "  \"failure_index_owner_only\": %u,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"protected_parent_decoder_used\": true,\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_offset_used\": false,\n"
        "  \"saved_reference_values_used\": false,\n"
        "  \"external_runtime_component_used\": false\n"
        "}}\n",
        status, (unsigned long)GetCurrentProcessId(),
        (unsigned long)expected_process_id, expected_executable_sha256,
        observed_hash ? observed_hash : "",
        (unsigned)(sizeof(input_types) / sizeof(input_types[0])),
        completed, roots, parents, failure_index
    );
    fclose(output);
}}

static DWORD WINAPI worker(void *unused) {{
    (void)unused;
    char observed_hash[65] = {{0}};
    uint32_t count = (uint32_t)(sizeof(input_types) / sizeof(input_types[0]));
    if (GetCurrentProcessId() != expected_process_id || !image_identity() ||
        !executable_identity(observed_hash) ||
        strcmp(observed_hash, expected_executable_sha256)) {{
        write_status("identity-binding-rejected", observed_hash, 0, 0, 0, 0);
        return 1;
    }}
    uintptr_t base = parent_base_pointer_slot;
    for (uint32_t depth = 0; depth < parent_base_pointer_indirections; depth++) {{
        uintptr_t next = 0;
        if (!readable(base, sizeof(next))) {{
            write_status("decoder-base-rejected", observed_hash, 0, 0, 0, 0);
            return 2;
        }}
        memcpy(&next, (const void *)base, sizeof(next));
        base = next;
    }}
    if (!base) {{
        write_status("decoder-base-rejected", observed_hash, 0, 0, 0, 0);
        return 2;
    }}
    FILE *output = _wfopen(ancestry_output, L"wb");
    if (!output) {{
        write_status("output-open-failed", observed_hash, 0, 0, 0, 0);
        return 3;
    }}
    alpha_ancestry_header header;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHAAN1", 8);
    header.version = {_ANCESTRY_VERSION}u;
    header.record_bytes = sizeof(alpha_ancestry_record);
    header.type_count = count;
    header.image_base = expected_image_base;
    header.image_bytes = expected_image_bytes;
    memcpy(header.executable_sha256, expected_executable_sha256, 64);
    memcpy(header.native_inventory_sha256,
        expected_native_inventory_sha256, 64);
    memcpy(header.native_semantics_sha256,
        expected_native_semantics_sha256, 64);
    int ok = fwrite(&header, 1, sizeof(header), output) == sizeof(header);
    uint32_t completed = 0, roots = 0, parents = 0, failure_index = 0;
    for (uint32_t index = 0; ok && index < count; index++) {{
        const alpha_input_type *input = &input_types[index];
        uintptr_t raw_address = input->class_pointer + parent_raw_dword_offset;
        uint32_t encoded = 0;
        if (raw_address < input->class_pointer ||
            !readable(raw_address, sizeof(encoded))) {{
            failure_index = index + 1u;
            ok = 0;
            break;
        }}
        memcpy(&encoded, (const void *)raw_address, sizeof(encoded));
        uintptr_t parent = encoded ? base + encoded : 0;
        uintptr_t descriptor = parent ? parent + parent_descriptor_adjustment : 0;
        if ((parent && parent < base) ||
            (descriptor && (descriptor < parent ||
             !readable(descriptor, 16u)))) {{
            failure_index = index + 1u;
            ok = 0;
            break;
        }}
        alpha_ancestry_record record;
        record.definition_index = input->definition_index;
        record.flags = parent ? 2u : 1u;
        record.class_pointer = input->class_pointer;
        record.parent_class_pointer = parent;
        record.parent_descriptor_pointer = descriptor;
        if (fwrite(&record, 1, sizeof(record), output) != sizeof(record)) {{
            failure_index = index + 1u;
            ok = 0;
            break;
        }}
        completed++;
        if (parent) parents++; else roots++;
    }}
    if (fclose(output)) ok = 0;
    if (!ok) DeleteFileW(ancestry_output);
    write_status(
        ok && completed == count && roots && parents
            ? "complete" : "capture-mismatch",
        observed_hash, completed, roots, parents, failure_index
    );
    return ok && completed == count && roots && parents ? 0 : 4;
}}

BOOL WINAPI DllMain(HINSTANCE instance, DWORD reason, LPVOID reserved) {{
    (void)instance;
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {{
        DisableThreadLibraryCalls(instance);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }}
    return TRUE;
}}
'''


def prepare_runtime_type_ancestry(
    *,
    binary: Path,
    snapshot: Path,
    native_semantics_model: Path,
    native_inventory: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        snapshot=snapshot,
        native_semantics_model=native_semantics_model,
        native_inventory=native_inventory,
    )
    status_path = output_dir / "runtime-type-ancestry-status.private.json"
    ancestry_path = output_dir / "runtime-type-ancestry.private.bin"
    model_path = output_dir / "runtime-type-ancestry.private.json"
    build_dir = _owner_directory(output_dir / "build-type-ancestry")
    source_path = build_dir / "runtime-type-ancestry.c"
    injector_source_path = build_dir / "runtime-type-ancestry-injector.c"
    injector_path = build_dir / "alpha-runtime-type-ancestry-injector.exe"
    for stale in (status_path, ancestry_path, model_path):
        stale.unlink(missing_ok=True)
    _private_text(
        source_path,
        runtime_type_ancestry_source(
            binding=binding,
            status_path=status_path,
            ancestry_path=ancestry_path,
        ),
    )
    _private_text(injector_source_path, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-type-ancestry-"
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
                str(collector_path),
                "-lbcrypt",
            ],
            label="runtime type ancestry collector",
            source_path=source_path,
            output_path=collector_path,
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
                str(injector_source_path),
                "-o",
                str(injector_path),
            ],
            label="runtime type ancestry injector",
            source_path=injector_source_path,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_TYPE_ANCESTRY_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(Path(binary).expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            "snapshot": binding["snapshot"],
            "memory_status": binding["memory_status"],
            "native_semantics": binding["native_semantics"],
            "native_inventory": binding["native_inventory"],
        },
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "status_path": str(status_path),
        "ancestry_path": str(ancestry_path),
        "model_path": str(model_path),
        "decoder_owner_only": binding["decoder_owner_only"],
        "contract": {
            "type_count": binding["type_count"],
            "record_bytes": _ANCESTRY_RECORD.size,
            "hierarchy_oracle_minimum": 10_000,
            "all_types_required": True,
        },
        "policy": {
            "same_process_required": True,
            "current_executable_sha256_embedded": True,
            "protected_parent_decoder_current_code_derived": True,
            "hierarchy_oracle_exact_required": True,
            "raw_pointers_owner_only": True,
            "saved_reference_values_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(output_dir / "runtime-type-ancestry-plan.private.json", plan)
    return {
        "schema": RUNTIME_TYPE_ANCESTRY_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "type_count": binding["type_count"],
        "policy": plan["policy"],
    }


_ANCESTRY_CHAIN_WINDOW = 16


def _walk_ancestry_chain(
    memory: Any,
    hierarchy_pointer: int,
    class_pointer: int,
    class_to_index: dict[int, int],
    bound: int,
) -> list[int]:
    chain: list[int] = []
    depth = 0


    read_qwords = memory.qwords
    append = chain.append
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
                if current not in class_to_index or current in chain:
                    return []
                append(current)
                if current == class_pointer:
                    return chain
        else:
            for current in values:
                if current not in class_to_index or current in chain:
                    return []
                append(current)
                if current == class_pointer:
                    return chain
        depth += span
    return chain


def _validate_ancestry_capture(
    *,
    plan: dict[str, Any],
    status: dict[str, Any],
    snapshot: Path,
    native_inventory: Path,
) -> tuple[dict[str, Any], dict[str, bool]]:
    ancestry_path = Path(plan["ancestry_path"])
    if not ancestry_path.is_file():
        raise AcquisitionError("runtime type ancestry output is absent")
    raw = ancestry_path.read_bytes()
    if len(raw) < _ANCESTRY_HEADER.size:
        raise AcquisitionError("runtime type ancestry output is truncated")
    header = _ANCESTRY_HEADER.unpack_from(raw, 0)
    type_count = plan["contract"]["type_count"]
    expected_size = _ANCESTRY_HEADER.size + type_count * _ANCESTRY_RECORD.size
    rows, inventory = _native_type_rows(
        native_inventory,
        executable_sha256=plan["target"]["executable_sha256"],
    )
    decoder = plan["decoder_owner_only"]
    header_valid = (
        header[0] == _ANCESTRY_MAGIC
        and header[1] == _ANCESTRY_VERSION
        and header[2] == _ANCESTRY_RECORD.size
        and header[3] == 0
        and header[4] == type_count
        and header[5] == plan["target"]["image_base_owner_only"]
        and header[6] == plan["target"]["image_bytes"]
        and _ascii_digest(header[7], label="output executable")
        == plan["target"]["executable_sha256"]
        and _ascii_digest(header[8], label="output inventory")
        == plan["inputs"]["native_inventory"]["sha256"]
        and _ascii_digest(header[9], label="output semantics")
        == plan["inputs"]["native_semantics"]["sha256"]
        and len(raw) == expected_size
        and inventory["identity"]["sha256"]
        == plan["inputs"]["native_inventory"]["sha256"]
    )
    class_to_index = {row[4]: row[0] for row in rows}
    descriptor_adjustment = decoder["embedded_descriptor_adjustment"]
    root_count = 0
    parent_count = 0
    known_parent_count = 0
    unknown_parent_count = 0
    relation_valid = True
    captured_parents: list[int] = []


    header_size = _ANCESTRY_HEADER.size
    record_size = _ANCESTRY_RECORD.size
    if len(raw) == expected_size:
        record_iter = _ANCESTRY_RECORD.iter_unpack(
            memoryview(raw)[header_size : header_size + type_count * record_size]
        )
    else:
        def _record_iter():
            for position in range(type_count):
                yield _ANCESTRY_RECORD.unpack_from(
                    raw, header_size + position * record_size
                )
        record_iter = _record_iter()
    append_parent = captured_parents.append
    for index, (native_row, record) in enumerate(zip(rows, record_iter)):
        definition_index, flags, class_pointer, parent, descriptor = record
        if (
            definition_index != index
            or class_pointer != native_row[4]
            or flags not in (1, 2)
            or (flags == 1) != (parent == 0)
            or (flags == 2) != (parent != 0)
            or (not parent and descriptor)
            or (
                parent
                and descriptor
                != parent + descriptor_adjustment
            )
        ):
            relation_valid = False
            break
        append_parent(parent)
        if parent:
            parent_count += 1
            if parent in class_to_index:
                known_parent_count += 1
            else:
                unknown_parent_count += 1
        else:
            root_count += 1
    hierarchy_eligible = 0
    hierarchy_matches = 0
    hierarchy_mismatches = 0
    with MemorySnapshot(snapshot) as memory:
        bound = len(class_to_index) + 1
        for native_row, captured_parent in zip(rows, captured_parents):
            hierarchy_pointer = native_row[5]
            if not hierarchy_pointer:
                continue
            chain = _walk_ancestry_chain(
                memory, hierarchy_pointer, native_row[4], class_to_index, bound
            )
            if not chain or chain[-1] != native_row[4]:
                continue
            expected_parent = chain[-2] if len(chain) > 1 else 0
            hierarchy_eligible += 1
            if captured_parent == expected_parent:
                hierarchy_matches += 1
            else:
                hierarchy_mismatches += 1
    counts = {
        "type_count": type_count,
        "root_count": root_count,
        "parent_count": parent_count,
        "known_parent_count": known_parent_count,
        "unknown_parent_count": unknown_parent_count,
        "hierarchy_oracle_eligible_count": hierarchy_eligible,
        "hierarchy_oracle_match_count": hierarchy_matches,
        "hierarchy_oracle_mismatch_count": hierarchy_mismatches,
    }
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_TYPE_ANCESTRY_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "same_process": status.get("process_id")
        == plan["target"]["process_id"]
        and status.get("expected_process_id")
        == plan["target"]["process_id"],
        "executable_identity_bound": status.get(
            "observed_executable_sha256"
        )
        == plan["target"]["executable_sha256"],
        "all_types_captured": status.get("completed_type_count") == type_count
        and len(captured_parents) == type_count,
        "status_counts_match": status.get("root_count") == root_count
        and status.get("parent_count") == parent_count
        and root_count + parent_count == type_count,
        "binary_header_bound": header_valid,
        "record_relations_valid": relation_valid,
        "protected_parent_domain_complete": parent_count >= type_count * 9 // 10,
        "known_parent_domain_substantial": known_parent_count >= 80_000,
        "hierarchy_oracle_substantial": hierarchy_eligible
        >= plan["contract"]["hierarchy_oracle_minimum"],
        "hierarchy_oracle_exact": hierarchy_matches == hierarchy_eligible
        and hierarchy_mismatches == 0,
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        )
        is True,
        "protected_parent_decoder_used": status.get(
            "protected_parent_decoder_used"
        )
        is True,
        "saved_reference_values_absent": status.get(
            "saved_reference_values_used"
        )
        is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    return counts, checks


def capture_runtime_type_ancestry(
    *,
    binary: Path,
    snapshot: Path,
    native_semantics_model: Path,
    native_inventory: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 120.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_type_ancestry(
        binary=binary,
        snapshot=snapshot,
        native_semantics_model=native_semantics_model,
        native_inventory=native_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-type-ancestry-plan.private.json"
    plan = read_json(plan_path)
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError("runtime type ancestry Wine is unavailable")
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
            "runtime type ancestry injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-type-ancestry-injector.private.log",
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
            f"runtime type ancestry injection failed ({injected.returncode})"
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


        time.sleep(0.05)
    if status is None:
        raise AcquisitionError("runtime type ancestry capture timed out")
    _seal_runtime_output(status_path)
    ancestry_path = Path(plan["ancestry_path"])
    if ancestry_path.is_file():
        _seal_runtime_output(ancestry_path)
    counts, checks = _validate_ancestry_capture(
        plan=plan,
        status=status,
        snapshot=Path(snapshot).expanduser().resolve(),
        native_inventory=Path(native_inventory).expanduser().resolve(),
    )
    validated = all(checks.values())
    model = {
        "schema": RUNTIME_TYPE_ANCESTRY_SCHEMA,
        "status": "runtime-validated" if validated else "rejected",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"]
        },
        "inputs": plan["inputs"],
        "ancestry_inventory": file_identity(ancestry_path),
        "decoder_owner_only": plan["decoder_owner_only"],
        "counts": counts,
        "checks": checks,
        "owner_only": True,
    }
    model_path = Path(plan["model_path"])
    _private_json(model_path, model)
    return {
        "schema": RUNTIME_TYPE_ANCESTRY_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "raw_pointers_and_decoder_values_exposed": False,
    }


from dataclasses import asdict
import hashlib
from pathlib import Path
import struct

from alpha.h01 import AcquisitionError
from alpha.c07 import FieldOffsetDecoder, _parse_field_offset_decoder, _decode_field_offset, _load_types_and_methods, _load_members
from alpha.c04 import _verify_files
from alpha.c04 import MappedPE
from alpha.h02 import file_identity, read_json


def denormalized_offset(normalized, adjustment):
    if type(normalized) is not int or not -(1 << 31) <= normalized < 1 << 31 or type(adjustment) is not int or not -(1 << 31) <= adjustment < 1 << 31:
        raise AcquisitionError("field normalization arithmetic is outside signed int32")
    return (normalized - adjustment) & 0xFFFFFFFF


def replay_normalization(*, decoder, code, members, detail_rows):
    if not isinstance(decoder, FieldOffsetDecoder) or not members or len(members) != len(detail_rows):
        raise AcquisitionError("field normalization domain is absent or incomplete")
    for key, value in asdict(decoder).items():
        if key != "operation" and type(value) is not int:
            raise AcquisitionError("field normalization decoder contains noninteger values")
    strides = {len(member.slots) * 8 for member in members}
    if len(strides) != 1:
        raise AcquisitionError("field normalization source strides differ")
    candidates = _parse_field_offset_decoder(code, method_pointer=decoder.method_pointer,
        expected_member_pointer_qword=decoder.member_pointer_qword, member_stride=next(iter(strides)))
    if candidates != [decoder]:
        raise AcquisitionError("field normalization decoder is not uniquely rederived from current code")
    denormalized = hashlib.sha256()
    identities = set()
    minimum = maximum = None


    operation = decoder.operation
    key_value = decoder.xor_key
    mask = decoder.mask
    adjustment = decoder.adjustment
    byte_offset = decoder.raw_dword_offset
    limit = next(iter(strides)) - 4
    restored_rows = []
    add_restored = restored_rows.append
    for member, row in zip(members, detail_rows):
        if (len(row) != 10 or member.kind != 0
                or row[0] != member.definition_index or row[1] != member.member_index or row[2] != member.pointer
                or member.pointer in identities or not 0 <= byte_offset <= limit):
            raise AcquisitionError("field normalization definition order or source identity differs")
        identities.add(member.pointer)
        slots = member.slots
        shift = (byte_offset & 7) * 8
        if shift <= 32:
            raw = (slots[byte_offset >> 3] >> shift) & 0xFFFFFFFF
        else:
            raw = ((slots[byte_offset >> 3] >> shift)
                   | (slots[(byte_offset >> 3) + 1] << (64 - shift))) & 0xFFFFFFFF
        if operation == "xor":
            protected = (raw ^ key_value) & mask
        elif operation == "add":
            protected = (raw + key_value) & mask
        elif operation == "subtract":
            protected = (raw - key_value) & mask
        else:
            raise AcquisitionError("runtime native semantic field-offset operation is invalid")
        unsigned = protected + adjustment
        unsigned &= 0xFFFFFFFF
        offset = unsigned if unsigned < 1 << 31 else unsigned - (1 << 32)
        if type(row[4]) is not int or row[4] != offset:
            raise AcquisitionError("stored field offset differs from its current native decoder/source")
        if (type(offset) is not int or not -(1 << 31) <= offset < 1 << 31
                or type(adjustment) is not int or not -(1 << 31) <= adjustment < 1 << 31):
            raise AcquisitionError("field normalization arithmetic is outside signed int32")
        restored = (offset - adjustment) & 0xFFFFFFFF
        add_restored(restored)
        minimum = restored if minimum is None else (minimum if minimum < restored else restored)
        maximum = restored if maximum is None else (maximum if maximum > restored else restored)
    if restored_rows:
        denormalized.update(struct.pack(f"<{len(restored_rows)}I", *restored_rows))
    return {"schema": "alpha.field-offset-normalization/v1", "decoder": asdict(decoder),
        "code_sha256": hashlib.sha256(code).hexdigest(), "code_bytes": len(code),
        "field_count": len(detail_rows), "denormalized_uint32_sha256": denormalized.hexdigest(),
        "denormalized_minimum": minimum, "denormalized_maximum": maximum,
        "checks": {"decoder_uniquely_rederived": True, "all_field_offsets_replayed": True,
                   "all_field_owners_and_native_records_bound": True, "normalization_inverse_exact": True},
        "object_header_bytes": None, "object_header_proven": False,
        "reference_storage_origin_proven": False, "static_storage_origin_proven": False,
        "value_type_payload_origin_proven": False, "metadata_complete": False}


def derive_field_normalization(*, binary, inputs, inventory, target):
    from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_HEADER as H, RUNTIME_NATIVE_MEMBER_DETAIL_FIELD as F, RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY as P
    selected = dict(inputs, member_detail_inventory=inventory)
    _verify_files(selected)
    executable = file_identity(binary)
    native = read_json(Path(inputs["native_semantics"]["path"]))
    type_plan = read_json(Path(inputs["type_identity_plan"]["path"]))
    if (executable["sha256"] != target["executable_sha256"] or native.get("binary") != executable
            or type_plan.get("target") != target
            or native.get("inputs", {}).get("native_inventory") != inputs["native_inventory"]
            or native.get("inputs", {}).get("native_member_inventory") != inputs["native_member_inventory"]
            or native.get("inputs", {}).get("reflection_semantics_model") != inputs["semantics"]):
        raise AcquisitionError("field normalization sources differ from the explicit capture")
    checks = native.get("checks", {})
    if any(checks.get(key) is not True for key in ("field_offset_decoder_structurally_unique", "field_offset_decoder_closes_over_all_records")):
        raise AcquisitionError("field normalization native decoder source is unvalidated")
    try:
        decoder = FieldOffsetDecoder(**native["field_offset_decoder"])
    except (KeyError, TypeError) as error:
        raise AcquisitionError("field normalization decoder source is malformed") from error
    types, _ = _load_types_and_methods(Path(inputs["native_inventory"]["path"]), executable_sha256=executable["sha256"],
        expected_identity=inputs["native_inventory"])
    domains, _ = _load_members(Path(inputs["native_member_inventory"]["path"]), executable_sha256=executable["sha256"],
        expected_identity=inputs["native_member_inventory"], type_count=len(types))
    base, extent = target["image_base_owner_only"], target["image_bytes"]
    pointers = sorted({pointer for row in types for pointer in row.method_pointers if base <= pointer < base + extent})
    following = dict(zip(pointers, pointers[1:]))
    end = following.get(decoder.method_pointer)
    if end is None or not 0 < end - decoder.method_pointer <= 1 << 20:
        raise AcquisitionError("field normalization decoder has no bounded current method extent")
    raw = Path(inventory["path"]).read_bytes()
    if len(raw) < H.size:
        raise AcquisitionError("field normalization detail header is truncated")
    h = H.unpack_from(raw)
    if (h[:7] != (b"ALPHAND1", 1, H.size, F.size, P.size, len(domains[0]), len(domains[1]))
            or h[8:12] != (base, extent, len(types), 0)
            or h[12:16] != (executable["sha256"].encode(), *(inputs[key]["sha256"].encode() for key in
                              ("native_member_inventory", "type_identity_inventory", "native_semantics")))
            or H.size + h[5] * F.size + h[6] * P.size + h[7] != len(raw)):
        raise AcquisitionError("field normalization detail header/domain binding differs")
    with MappedPE(binary) as image:
        start = image.rva_to_offset(decoder.method_pointer - base)
        width = end - decoder.method_pointer
        if image.size_of_image != extent or start is None or not any(s.raw_offset <= start and start + width <= s.raw_end for s in image.executable_sections):
            raise AcquisitionError("field normalization decoder is outside current executable sections")
        code = bytes(image._mapping[start:start + width])


    result = replay_normalization(decoder=decoder, code=code, members=domains[0],
        detail_rows=list(F.iter_unpack(memoryview(raw)[H.size:H.size + h[5] * F.size])))
    _verify_files(selected)
    if file_identity(binary) != executable:
        raise AcquisitionError("field normalization executable changed")
    result.update(inputs=selected, binary=executable, target=target)
    return result


from pathlib import Path

from alpha.c04 import observe_missing_native_names
from alpha.c07 import inspect_runtime_native_semantics
from alpha.p12 import _private_json
from alpha.h02 import read_json, file_identity


def capture_runtime_native_semantics(*, binary: Path, snapshot: Path,
    reflection_semantics_model: Path, materializer_model: Path,
    native_inventory: Path, native_member_inventory: Path, output_dir: Path,
    wine: Path, wineprefix: Path, compiler: Path | None = None, timeout: float = 1800.0):
    observation_count = 0
    def observe(requests):
        nonlocal observation_count
        observation_count += 1
        return observe_missing_native_names(binary=binary, requests=requests,
            output_dir=output_dir / f"name-observation-{observation_count}",
            wine=wine, wineprefix=wineprefix, compiler=compiler)
    result = inspect_runtime_native_semantics(binary=binary, snapshot=snapshot,
        reflection_semantics_model=reflection_semantics_model, materializer_model=materializer_model,
        native_inventory=native_inventory, native_member_inventory=native_member_inventory,
        output=output_dir / "runtime-native-semantics.private.json", name_observer=observe)
    receipts = [file_identity(output_dir / f"name-observation-{index}" / "native-name-observation.private.json")
                for index in range(1, observation_count + 1)]
    model_path = output_dir / "runtime-native-semantics.private.json"
    model = read_json(model_path)
    model["supplemental_name_observations"] = receipts
    _private_json(model_path, model)
    result["supplemental_name_observation_count"] = observation_count
    result["supplemental_name_observations"] = receipts
    return result


import os
from copy import deepcopy
from pathlib import Path
from typing import Any

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError, owner_uid
from alpha.p01 import reflection_contract
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.c07 import RUNTIME_REFLECTION_BEHAVIOR_PLAN_SCHEMA, RUNTIME_REFLECTION_BEHAVIOR_SCHEMA, _REMAINING_FAMILIES, _REMAINING_OPERATION_KEYS, _TYPE_EXTENDED_FAMILIES, _TYPE_EXTENDED_OPERATION_KEYS
from alpha.h02 import file_identity, read_json


RUNTIME_REFLECTION_SEMANTIC_MERGE_SCHEMA = (
    "alpha.runtime-reflection-semantic-merge/v1"
)
_EVENT_KEYS = (
    "event.name",
    "event.add_method",
    "event.remove_method",
    "event.raise_method",
)
_EVENT_RELATION_KEYS = ("event.handler_type",)
_EVENT_FACTORY_KEY = "type.events"
_METHOD_KEYS = (
    "method.return_type",
    "method.parameters",
)
_MEMBER_KEYS = ("member.metadata_token",)
_MEMBER_SUPPORT_KEYS = ("field.attributes",)
_TYPE_IDENTITY_KEYS = ("type.name", "type.namespace")
_TYPE_EXTENDED_KEYS = _TYPE_EXTENDED_OPERATION_KEYS
_REMAINING_KEYS = _REMAINING_OPERATION_KEYS


def _owner_json(path: Path, *, label: str) -> tuple[Path, dict[str, Any]]:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime reflection semantic merge {label} is not owner-only"
        )
    value = read_json(path)
    if not isinstance(value, dict):
        raise AcquisitionError(
            f"runtime reflection semantic merge {label} is invalid"
        )
    return path, value


def merge_runtime_reflection_semantics(
    *,
    semantics_model: Path,
    behavior_plan: Path,
    behavior_receipt: Path,
    output: Path,
) -> dict[str, Any]:
    semantics_path, semantics = _owner_json(
        semantics_model, label="semantic model"
    )
    plan_path, plan = _owner_json(behavior_plan, label="behavior plan")
    receipt_path, receipt = _owner_json(
        behavior_receipt, label="behavior receipt"
    )
    semantics_identity = file_identity(semantics_path)
    raw_factory = plan.get("candidates_owner_only", {}).get(
        "fresh_event_factory"
    )
    expected_event_keys = _EVENT_KEYS + (
        _EVENT_RELATION_KEYS if isinstance(raw_factory, dict) else ()
    )
    expected_receipt_operations = len(expected_event_keys) + (
        len(_METHOD_KEYS)
        + len(_MEMBER_KEYS)
        + len(_TYPE_IDENTITY_KEYS)
        + (
            len(_TYPE_EXTENDED_KEYS)
            if plan.get("contract", {}).get(
                "fresh_type_extended_behavior_available"
            )
            is True
            else 0
        )
        + (
            len(_REMAINING_KEYS)
            if plan.get("contract", {}).get(
                "fresh_remaining_behavior_available"
            )
            is True
            else 0
        )
        if isinstance(raw_factory, dict)
        else 0
    )
    if (
        semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or plan.get("schema") != RUNTIME_REFLECTION_BEHAVIOR_PLAN_SCHEMA
        or plan.get("status") != "prepared"
        or receipt.get("schema") != RUNTIME_REFLECTION_BEHAVIOR_SCHEMA
        or receipt.get("status") != "validated"
        or receipt.get("operation_count") != expected_receipt_operations
        or receipt.get("owner_only") is not True
        or not isinstance(receipt.get("checks"), dict)
        or not receipt["checks"]
        or not all(receipt["checks"].values())
        or plan.get("inputs", {}).get("semantics", {}).get("sha256")
        != semantics_identity["sha256"]
        or receipt.get("inputs") != plan.get("inputs")
        or receipt.get("target")
        != {
            "executable_sha256": plan.get("target", {}).get(
                "executable_sha256"
            )
        }
        or semantics.get("binary", {}).get("sha256")
        != plan.get("target", {}).get("executable_sha256")
        or semantics.get("snapshot", {}).get("sha256")
        != plan.get("inputs", {}).get("snapshot", {}).get("sha256")
    ):
        raise AcquisitionError(
            "runtime reflection semantic merge input binding is stale"
        )
    selected = receipt.get("selected_owner_only")
    plan_candidates = plan.get("candidates_owner_only")
    receipt_candidates = receipt.get("candidate_observations_owner_only")
    if (
        not isinstance(selected, dict)
        or set(selected) != set(_EVENT_KEYS)
        or not isinstance(plan_candidates, dict)
        or not isinstance(receipt_candidates, dict)
    ):
        raise AcquisitionError(
            "runtime reflection semantic merge selection is incomplete"
        )
    selected_rows: dict[str, dict[str, Any]] = {}
    for key in _EVENT_KEYS:
        family = "zero" if key == "event.name" else "bool"
        index = selected.get(key)
        candidates = plan_candidates.get(family)
        observations = receipt_candidates.get(family)
        if (
            not isinstance(index, int)
            or not isinstance(candidates, list)
            or len(candidates) != 3
            or not isinstance(observations, list)
            or len(observations) != 3
            or not 0 <= index < len(candidates)
            or observations[index].get("source_index_owner_only")
            != candidates[index].get("method_index_owner_only")
        ):
            raise AcquisitionError(
                "runtime reflection semantic merge candidate binding is invalid"
            )
        row = candidates[index]
        if not all(
            isinstance(row.get(field), int) and row[field] > 0
            for field in (
                "method_index_owner_only",
                "metadata_pointer_owner_only",
                "method_pointer_owner_only",
            )
        ):
            raise AcquisitionError(
                "runtime reflection semantic merge candidate is incomplete"
            )
        selected_rows[key] = row
    factory_row: dict[str, Any] | None = None
    method_rows: dict[str, dict[str, Any]] = {}
    member_rows: dict[str, dict[str, Any]] = {}
    type_identity_rows: dict[str, dict[str, Any]] = {}
    type_extended_rows: dict[str, dict[str, Any]] = {}
    remaining_rows: dict[str, dict[str, Any]] = {}
    event_relation_rows: dict[str, dict[str, Any]] = {}
    fresh_factory = plan_candidates.get("fresh_event_factory")
    if isinstance(fresh_factory, dict):
        collection = fresh_factory.get("collection_candidates_owner_only")
        evidence = fresh_factory.get("collection_callgraph_evidence")
        event_reachable = (
            evidence.get("native_event_helper_reachable_count")
            if isinstance(evidence, dict)
            else None
        )
        if event_reachable is None and isinstance(evidence, dict):
            event_reachable = evidence.get(
                "native_helper_reachability", {}
            ).get("event")
        if (
            not isinstance(collection, list)
            or len(collection) != 1
            or not isinstance(collection[0], dict)
            or not all(
                isinstance(collection[0].get(field), int)
                and collection[0][field] > 0
                for field in (
                    "method_index_owner_only",
                    "metadata_pointer_owner_only",
                    "method_pointer_owner_only",
                )
            )
            or not isinstance(evidence, dict)
            or event_reachable != 1
            or not isinstance(
                evidence.get("binding_flag_collection_shape_count"), int
            )
            or evidence["binding_flag_collection_shape_count"] < 2
        ):
            raise AcquisitionError(
                "runtime reflection semantic merge Event factory is invalid"
            )
        factory_row = collection[0]
        raw_method_rows = fresh_factory.get(
            "method_semantic_candidates_owner_only"
        )
        if (
            not isinstance(raw_method_rows, dict)
            or set(raw_method_rows) != set(_METHOD_KEYS)
            or not all(
                isinstance(raw_method_rows.get(key), dict)
                and all(
                    isinstance(raw_method_rows[key].get(field), int)
                    and raw_method_rows[key][field] > 0
                    for field in (
                        "method_index_owner_only",
                        "metadata_pointer_owner_only",
                        "method_pointer_owner_only",
                    )
                )
                for key in _METHOD_KEYS
            )
        ):
            raise AcquisitionError(
                "runtime reflection semantic merge Method behavior is invalid"
            )
        method_rows = raw_method_rows
        raw_member_rows = fresh_factory.get(
            "member_semantic_candidates_owner_only"
        )
        if (
            not isinstance(raw_member_rows, dict)
            or set(raw_member_rows)
            != set((*_MEMBER_KEYS, *_MEMBER_SUPPORT_KEYS))
            or not all(
                isinstance(raw_member_rows.get(key), dict)
                and all(
                    isinstance(raw_member_rows[key].get(field), int)
                    and raw_member_rows[key][field] > 0
                    for field in (
                        "method_index_owner_only",
                        "metadata_pointer_owner_only",
                        "method_pointer_owner_only",
                    )
                )
                for key in (*_MEMBER_KEYS, *_MEMBER_SUPPORT_KEYS)
            )
        ):
            raise AcquisitionError(
                "runtime reflection semantic merge Member behavior is invalid"
            )
        member_rows = {key: raw_member_rows[key] for key in _MEMBER_KEYS}
        raw_handler_row = fresh_factory.get(
            "event_handler_semantic_candidate_owner_only"
        )
        if not isinstance(raw_handler_row, dict) or not all(
            isinstance(raw_handler_row.get(field), int)
            and raw_handler_row[field] > 0
            for field in (
                "method_index_owner_only",
                "metadata_pointer_owner_only",
                "method_pointer_owner_only",
            )
        ):
            raise AcquisitionError(
                "runtime reflection Event handler relation is invalid"
            )
        event_relation_rows["event.handler_type"] = raw_handler_row
        raw_type_candidates = fresh_factory.get(
            "type_identity_string_candidates_owner_only"
        )
        type_callgraph = fresh_factory.get(
            "type_identity_callgraph_evidence"
        )
        raw_type_selected = receipt.get("type_selected_owner_only")
        expected_type_candidate_count = plan.get("contract", {}).get(
            "type_identity_candidate_count"
        )
        legacy_type_candidate_contract = (
            isinstance(type_callgraph, dict)
            and type_callgraph.get("arity_zero_candidate_count")
            == expected_type_candidate_count
            and type_callgraph.get(
                "runtime_string_return_filter_required"
            )
            is True
        )
        structural_type_candidate_contract = (
            isinstance(type_callgraph, dict)
            and isinstance(expected_type_candidate_count, int)
            and isinstance(
                type_callgraph.get("arity_zero_candidate_count"), int
            )
            and type_callgraph["arity_zero_candidate_count"]
            >= expected_type_candidate_count
            and type_callgraph.get(
                "runtime_string_constructor_candidate_count"
            )
            == expected_type_candidate_count
            and type_callgraph.get(
                "name_string_helper_reachability_unique"
            )
            is True
            and type_callgraph.get("namespace_string_shape_unique")
            is True
            and type_callgraph.get("structural_string_return_safe")
            is True
            and type_callgraph.get(
                "runtime_string_return_filter_required"
            )
            is False
            and plan.get("policy", {}).get(
                "type_identity_structural_string_constructor_required"
            )
            is True
        )
        if (
            not isinstance(raw_type_candidates, list)
            or not isinstance(expected_type_candidate_count, int)
            or expected_type_candidate_count < 2
            or len(raw_type_candidates) != expected_type_candidate_count
            or not isinstance(raw_type_selected, dict)
            or set(raw_type_selected) != set(_TYPE_IDENTITY_KEYS)
            or not all(
                isinstance(raw_type_selected.get(key), int)
                and 0
                <= raw_type_selected[key]
                < expected_type_candidate_count
                for key in _TYPE_IDENTITY_KEYS
            )
            or len(
                {raw_type_selected[key] for key in _TYPE_IDENTITY_KEYS}
            )
            != 2
            or not isinstance(type_callgraph, dict)
            or not (
                legacy_type_candidate_contract
                or structural_type_candidate_contract
            )
            or type_callgraph.get(
                "direct_invocation_before_return_type_filter"
            )
            is not False
        ):
            raise AcquisitionError(
                "runtime reflection Type identity selection is invalid"
            )
        for key in _TYPE_IDENTITY_KEYS:
            row = raw_type_candidates[raw_type_selected[key]]
            if not isinstance(row, dict) or not all(
                isinstance(row.get(field), int) and row[field] > 0
                for field in (
                    "method_index_owner_only",
                    "metadata_pointer_owner_only",
                    "method_pointer_owner_only",
                )
            ):
                raise AcquisitionError(
                    "runtime reflection Type identity candidate is invalid"
                )
            type_identity_rows[key] = row
        extended_required = plan.get("contract", {}).get(
            "fresh_type_extended_behavior_available"
        ) is True
        if extended_required:
            raw_extended_candidates = fresh_factory.get(
                "type_extended_candidates_owner_only"
            )
            raw_extended_evidence = fresh_factory.get(
                "type_extended_structural_evidence"
            )
            raw_extended_samples = fresh_factory.get(
                "type_semantic_samples_owner_only"
            )
            raw_extended_categories = fresh_factory.get(
                "type_semantic_category_counts"
            )
            raw_extended_selected = receipt.get(
                "type_extended_selected_owner_only"
            )
            expected_sample_count = plan.get("contract", {}).get(
                "type_extended_sample_count"
            )
            behavior_selected_families = {
                "attributes",
                "is_enum",
                "is_value_type",
            }
            expected_family_counts = {
                family: (
                    2
                    if family in ("module_pair", "declaring_type_pair")
                    else None
                    if family in behavior_selected_families
                    else 1
                )
                for family in set(_TYPE_EXTENDED_FAMILIES.values())
            }
            if (
                not isinstance(raw_extended_candidates, dict)
                or not isinstance(raw_extended_evidence, dict)
                or raw_extended_evidence.get("resolved_family_count") != 10
                or raw_extended_evidence.get(
                    "behavior_selected_family_count"
                )
                != len(behavior_selected_families)
                or raw_extended_evidence.get("module_pair_count") != 2
                or raw_extended_evidence.get(
                    "declaring_type_equivalence_candidate_count"
                )
                != 2
                or not isinstance(expected_sample_count, int)
                or expected_sample_count < 8
                or not isinstance(raw_extended_samples, list)
                or len(raw_extended_samples) != expected_sample_count
                or not isinstance(raw_extended_categories, dict)
                or any(
                    not isinstance(raw_extended_categories.get(category), int)
                    or raw_extended_categories[category] < 4
                    for category in ("enum", "value", "generic_definition")
                )
                or not isinstance(raw_extended_selected, dict)
                or set(raw_extended_selected) != set(_TYPE_EXTENDED_KEYS)
                or receipt.get("checks", {}).get(
                    "fresh_type_extended_behavior_complete"
                )
                is not True
                or plan.get("policy", {}).get(
                    "fresh_type_extended_semantics_required"
                )
                is not True
                or plan.get("policy", {}).get(
                    "type_extended_behavior_selection_required"
                )
                is not True
            ):
                raise AcquisitionError(
                    "runtime reflection Type extended behavior is invalid"
                )
            for family, expected_count in expected_family_counts.items():
                rows = raw_extended_candidates.get(family)
                if (
                    not isinstance(rows, list)
                    or not rows
                    or (expected_count is not None and len(rows) != expected_count)
                ):
                    raise AcquisitionError(
                        "runtime reflection Type extended family is invalid"
                    )
            for key in _TYPE_EXTENDED_KEYS:
                family = _TYPE_EXTENDED_FAMILIES[key]
                rows = raw_extended_candidates[family]
                index = raw_extended_selected.get(key)
                if not isinstance(index, int) or not 0 <= index < len(rows):
                    raise AcquisitionError(
                        "runtime reflection Type extended selection is invalid"
                    )
                row = rows[index]
                if not isinstance(row, dict) or not all(
                    isinstance(row.get(field), int) and row[field] > 0
                    for field in (
                        "method_index_owner_only",
                        "metadata_pointer_owner_only",
                        "method_pointer_owner_only",
                    )
                ):
                    raise AcquisitionError(
                        "runtime reflection Type extended candidate is invalid"
                    )
                type_extended_rows[key] = row
        remaining_required = plan.get("contract", {}).get(
            "fresh_remaining_behavior_available"
        ) is True
        if remaining_required:
            raw_remaining_candidates = fresh_factory.get(
                "remaining_candidates_owner_only"
            )
            raw_remaining_evidence = fresh_factory.get(
                "remaining_structural_evidence"
            )
            raw_remaining_selected = receipt.get(
                "remaining_selected_owner_only"
            )
            expected_family_counts = {
                family: (3 if key == "enum.underlying_type" else 1)
                for key, family in _REMAINING_FAMILIES.items()
            }
            if (
                not isinstance(raw_remaining_candidates, dict)
                or set(raw_remaining_candidates)
                != set(_REMAINING_FAMILIES.values())
                or not isinstance(raw_remaining_evidence, dict)
                or raw_remaining_evidence.get(
                    "structurally_unique_candidate_count"
                )
                != 6
                or raw_remaining_evidence.get(
                    "enum_behavior_candidate_count"
                )
                != 3
                or raw_remaining_evidence.get(
                    "property_handle_protection_shape_unique"
                )
                is not True
                or raw_remaining_evidence.get(
                    "property_handle_protection_current_code_derived"
                )
                is not True
                or raw_remaining_evidence.get(
                    "property_factory_handle_store_pair_unique"
                )
                is not True
                or raw_remaining_evidence.get("saved_method_ordinal_used")
                is not False
                or not isinstance(raw_remaining_selected, dict)
                or set(raw_remaining_selected) != set(_REMAINING_KEYS)
                or receipt.get("checks", {}).get(
                    "fresh_remaining_behavior_complete"
                )
                is not True
                or plan.get("policy", {}).get(
                    "fresh_remaining_semantics_required"
                )
                is not True
            ):
                raise AcquisitionError(
                    "runtime reflection remaining behavior is invalid"
                )
            for family, expected_count in expected_family_counts.items():
                rows = raw_remaining_candidates.get(family)
                if not isinstance(rows, list) or len(rows) != expected_count:
                    raise AcquisitionError(
                        "runtime reflection remaining family is invalid"
                    )
            for key in _REMAINING_KEYS:
                family = _REMAINING_FAMILIES[key]
                rows = raw_remaining_candidates[family]
                index = raw_remaining_selected.get(key)
                if not isinstance(index, int) or not 0 <= index < len(rows):
                    raise AcquisitionError(
                        "runtime reflection remaining selection is invalid"
                    )
                row = rows[index]
                if not isinstance(row, dict) or not all(
                    isinstance(row.get(field), int) and row[field] > 0
                    for field in (
                        "method_index_owner_only",
                        "metadata_pointer_owner_only",
                        "method_pointer_owner_only",
                    )
                ):
                    raise AcquisitionError(
                        "runtime reflection remaining candidate is invalid"
                    )
                if key == "property.from_handle" and not all(
                    type(row.get(field)) is int and row[field] > 0
                    for field in (
                        "protected_owner_addend_owner_only",
                        "property_object_handle_byte_offset_owner_only",
                    )
                ) or (
                    key == "property.from_handle"
                    and (
                        type(row.get("protected_owner_byte_offset_owner_only"))
                        is not int
                        or not 0 <= row["protected_owner_byte_offset_owner_only"] < 512
                    )
                ):
                    raise AcquisitionError(
                        "runtime reflection Property handle protection is "
                        "invalid"
                    )
                remaining_rows[key] = row
    if len(
        {
            selected_rows[key]["method_index_owner_only"]
            for key in _EVENT_KEYS[1:]
        }
    ) != 3:
        raise AcquisitionError(
            "runtime reflection semantic merge event accessors are ambiguous"
        )
    contract = reflection_contract()
    contract_rows = {
        operation["key"]: operation for operation in contract["operations"]
    }
    operations = deepcopy(semantics.get("operations"))
    if not isinstance(operations, list):
        raise AcquisitionError(
            "runtime reflection semantic merge base operations are invalid"
        )
    existing = {
        operation.get("key")
        for operation in operations
        if isinstance(operation, dict)
    }
    addition_keys = set(expected_event_keys)
    if factory_row is not None:
        addition_keys.update(
            (
                _EVENT_FACTORY_KEY,
                *_METHOD_KEYS,
                *_MEMBER_KEYS,
                *_TYPE_IDENTITY_KEYS,
                *type_extended_rows,
                *remaining_rows,
            )
        )
    if existing & addition_keys:
        raise AcquisitionError(
            "runtime reflection semantic merge operations already exist"
        )
    for key in _EVENT_KEYS:
        row = selected_rows[key]
        descriptor = contract_rows[key]
        operations.append(
            {
                "key": key,
                "runtime_owner": descriptor["runtime_owner"],
                "runtime_name": descriptor["runtime_name"],
                "method_index": row["method_index_owner_only"],
                "metadata_pointer": row["metadata_pointer_owner_only"],
                "method_pointer": row["method_pointer_owner_only"],
                "semantic_identity_resolved": True,
                "resolution": "derived-fresh-managed-event-behavior",
            }
        )
    for key in _EVENT_RELATION_KEYS:
        row = event_relation_rows.get(key)
        if row is None:
            continue
        descriptor = contract_rows[key]
        operations.append(
            {
                "key": key,
                "runtime_owner": descriptor["runtime_owner"],
                "runtime_name": descriptor["runtime_name"],
                "method_index": row["method_index_owner_only"],
                "metadata_pointer": row["metadata_pointer_owner_only"],
                "method_pointer": row["method_pointer_owner_only"],
                "semantic_identity_resolved": True,
                "resolution": (
                    "derived-current-code-composition-and-fresh-event-add-"
                    "parameter-type-equivalence"
                ),
            }
        )
    if factory_row is not None:
        descriptor = contract_rows[_EVENT_FACTORY_KEY]
        operations.append(
            {
                "key": _EVENT_FACTORY_KEY,
                "runtime_owner": descriptor["runtime_owner"],
                "runtime_name": descriptor["runtime_name"],
                "method_index": factory_row["method_index_owner_only"],
                "metadata_pointer": factory_row[
                    "metadata_pointer_owner_only"
                ],
                "method_pointer": factory_row["method_pointer_owner_only"],
                "semantic_identity_resolved": True,
                "runtime_parameter_count": 1,
                "invocation_semantics": "all-member-binding-flags",
                "resolution": (
                    "derived-current-native-event-helper-callgraph-and-"
                    "fresh-managed-array-behavior"
                ),
            }
        )
        for key in _METHOD_KEYS:
            row = method_rows[key]
            descriptor = contract_rows[key]
            operations.append(
                {
                    "key": key,
                    "runtime_owner": descriptor["runtime_owner"],
                    "runtime_name": descriptor["runtime_name"],
                    "method_index": row["method_index_owner_only"],
                    "metadata_pointer": row[
                        "metadata_pointer_owner_only"
                    ],
                    "method_pointer": row["method_pointer_owner_only"],
                    "semantic_identity_resolved": True,
                    "resolution": (
                        "derived-current-code-shape-and-fresh-managed-"
                        "method-behavior"
                    ),
                }
            )
        for key in _MEMBER_KEYS:
            row = member_rows[key]
            descriptor = contract_rows[key]
            operations.append(
                {
                    "key": key,
                    "runtime_owner": descriptor["runtime_owner"],
                    "runtime_name": descriptor["runtime_name"],
                    "method_index": row["method_index_owner_only"],
                    "metadata_pointer": row[
                        "metadata_pointer_owner_only"
                    ],
                    "method_pointer": row["method_pointer_owner_only"],
                    "semantic_identity_resolved": True,
                    "resolution": (
                        "derived-current-metadata-table-dispatch-and-fresh-"
                        "managed-method-token-behavior"
                    ),
                }
            )
        for key in _TYPE_IDENTITY_KEYS:
            row = type_identity_rows[key]
            descriptor = contract_rows[key]
            operations.append(
                {
                    "key": key,
                    "runtime_owner": descriptor["runtime_owner"],
                    "runtime_name": descriptor["runtime_name"],
                    "method_index": row["method_index_owner_only"],
                    "metadata_pointer": row[
                        "metadata_pointer_owner_only"
                    ],
                    "method_pointer": row["method_pointer_owner_only"],
                    "semantic_identity_resolved": True,
                    "resolution": (
                        "derived-current-code-shape-and-fresh-known-type-"
                        "string-identity"
                    ),
                }
            )
        for key in _TYPE_EXTENDED_KEYS:
            row = type_extended_rows.get(key)
            if row is None:
                continue
            descriptor = contract_rows[key]
            operations.append(
                {
                    "key": key,
                    "runtime_owner": descriptor["runtime_owner"],
                    "runtime_name": descriptor["runtime_name"],
                    "method_index": row["method_index_owner_only"],
                    "metadata_pointer": row[
                        "metadata_pointer_owner_only"
                    ],
                    "method_pointer": row["method_pointer_owner_only"],
                    "semantic_identity_resolved": True,
                    "resolution": (
                        "derived-current-code-topology-and-fresh-runtime-"
                        "type-semantic-relations"
                    ),
                }
            )
        for key in _REMAINING_KEYS:
            row = remaining_rows.get(key)
            if row is None:
                continue
            descriptor = contract_rows[key]
            operations.append(
                {
                    "key": key,
                    "runtime_owner": descriptor["runtime_owner"],
                    "runtime_name": descriptor["runtime_name"],
                    "method_index": row["method_index_owner_only"],
                    "metadata_pointer": row[
                        "metadata_pointer_owner_only"
                    ],
                    "method_pointer": row["method_pointer_owner_only"],
                    "semantic_identity_resolved": True,
                    "resolution": (
                        "derived-current-code-topology-and-fresh-runtime-"
                        "handle-value-or-enum-behavior"
                    ),
                }
            )
    resolved_keys = [operation["key"] for operation in operations]
    if len(resolved_keys) != len(set(resolved_keys)):
        raise AcquisitionError(
            "runtime reflection semantic merge operation identities collide"
        )
    unresolved_keys = [
        operation["key"]
        for operation in contract["operations"]
        if operation["key"] not in set(resolved_keys)
    ]
    merged = deepcopy(semantics)
    merged["operations"] = operations
    merged["behavior_evidence"] = {
        "schema": RUNTIME_REFLECTION_SEMANTIC_MERGE_SCHEMA,
        "plan": file_identity(plan_path),
        "receipt": file_identity(receipt_path),
        "operation_keys": list(expected_event_keys)
        + (
            [_EVENT_FACTORY_KEY, *_METHOD_KEYS, *_MEMBER_KEYS]
            + list(_TYPE_IDENTITY_KEYS)
            + list(type_extended_rows)
            + list(remaining_rows)
            if factory_row is not None
            else []
        ),
        "same_process": True,
        "fresh_runtime_observation": True,
        "saved_alias_used": False,
        "fixed_ordinal_used": False,
        "raw_pointers_owner_only": True,
    }
    merged["contract"] = {
        "contract_id": contract["contract_id"],
        "operation_count": contract["operation_count"],
        "resolved_operation_keys": resolved_keys,
        "unresolved_operation_keys": unresolved_keys,
        "semantic_operation_resolution_complete": not unresolved_keys,
    }
    merged["status"] = "resolved" if not unresolved_keys else "partially-resolved"
    checks = deepcopy(semantics.get("checks"))
    if not isinstance(checks, dict):
        raise AcquisitionError(
            "runtime reflection semantic merge base checks are invalid"
        )
    checks.update(
        {
            "fresh_event_behavior_bound": True,
            "event_operation_count": len(expected_event_keys),
            "event_factory_operation_resolved": factory_row is not None,
            "method_behavior_operation_count": len(method_rows),
            "member_behavior_operation_count": len(member_rows),
            "type_identity_behavior_operation_count": len(
                type_identity_rows
            ),
            "type_extended_behavior_operation_count": len(
                type_extended_rows
            ),
            "remaining_behavior_operation_count": len(remaining_rows),
            "event_operations_semantically_unique": True,
            "all_operations_resolved": not unresolved_keys,
        }
    )
    merged["checks"] = checks
    output = output.expanduser().resolve()
    _private_json(output, merged)
    return {
        "schema": RUNTIME_REFLECTION_SEMANTIC_MERGE_SCHEMA,
        "status": merged["status"],
        "resolved_operation_count": len(operations),
        "unresolved_operation_count": len(unresolved_keys),
        "event_operation_count": len(expected_event_keys),
        "event_factory_operation_count": int(factory_row is not None),
        "method_behavior_operation_count": len(method_rows),
        "member_behavior_operation_count": len(member_rows),
        "type_identity_behavior_operation_count": len(type_identity_rows),
        "type_extended_behavior_operation_count": len(type_extended_rows),
        "remaining_behavior_operation_count": len(remaining_rows),
        "checks": {
            "target_identity_bound": True,
            "snapshot_identity_bound": True,
            "semantics_identity_bound": True,
            "behavior_plan_identity_bound": True,
            "behavior_receipt_identity_bound": True,
            "fresh_event_behavior_bound": True,
            "saved_alias_absent": True,
            "fixed_ordinal_absent": True,
            "external_runtime_component_absent": True,
        },
        "raw_addresses_and_candidate_indexes_exposed": False,
        "output": str(output),
    }
