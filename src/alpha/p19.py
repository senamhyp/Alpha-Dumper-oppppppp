from alpha.h02 import windows_run as _host_run

import json
import os
import secrets
import struct
import subprocess
import time
from pathlib import Path
from alpha.c01 import current_runtime_process_binding
from alpha.c04 import RuntimeProcessLifetimeGuard
from alpha.c06 import attach_raw_type_names, finalize_raw_type_names, load_raw_type_names, ROLES as RAW_TYPE_ROLES
from alpha.p18 import load_runtime_string_layout_candidate
from alpha.c04 import native_string_reader_source, validate_string_layout_io
from typing import Any

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import (
    AcquisitionError,
    owner_only_path_bits,
    owner_uid,
    same_executable_path,
)
from alpha.p14 import REFLECTION_BOOTSTRAP_SCHEMA
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p15 import RUNTIME_CLASS_SCHEMA
from alpha.p18 import RUNTIME_TYPE_ANCESTRY_SCHEMA
from alpha.p16 import RUNTIME_TYPE_MATERIALIZER_SCHEMA
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json
from alpha.stage_catalog import acquisition_stage_plan


RUNTIME_TYPE_IDENTITY_PLAN_SCHEMA = (
    "alpha.runtime-type-identity-inventory-plan/v1"
)
RUNTIME_TYPE_IDENTITY_STATUS_SCHEMA = (
    "alpha.runtime-type-identity-inventory-status/v1"
)
RUNTIME_TYPE_IDENTITY_SCHEMA = "alpha.runtime-type-identity-inventory/v1"
_IDENTITY_MAGIC = b"ALPHATI1"
_IDENTITY_VERSION = 1
_IDENTITY_HEADER = struct.Struct("<8sIIIIQQQQ64s64s64s")
_IDENTITY_RECORD = struct.Struct("<IIQQQQQIIIIQQ")
_REQUIRED_OPERATIONS = (
    "type.from_handle",
    "type.name",
    "type.namespace",
    "type.module",
    "type.declaring_type",
    "type.attributes",
    "type.is_enum",
    "type.is_value_type",
    "member.metadata_token",
)


RUNTIME_TYPE_IDENTITY_BATCH_ROWS = 512


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime type identity {label} is not owner-only"
        )
    return path


def _ascii_digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime type identity {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime type identity {label} digest is invalid"
        )
    return value


def _native_inventory_header(
    path: Path,
    *,
    executable_sha256: str,
) -> dict[str, Any]:
    path = _owner_file(path, label="native inventory")
    raw = path.read_bytes()
    if len(raw) < _NATIVE_INVENTORY_HEADER.size:
        raise AcquisitionError("runtime type identity inventory is truncated")
    header = _NATIVE_INVENTORY_HEADER.unpack_from(raw, 0)
    type_count, method_count = header[5:7]
    records_end = (
        _NATIVE_INVENTORY_HEADER.size
        + type_count * _NATIVE_TYPE_RECORD.size
        + method_count * _NATIVE_METHOD_RECORD.size
    )
    if (
        header[0] != _NATIVE_INVENTORY_MAGIC
        or header[1] != _NATIVE_INVENTORY_VERSION
        or header[2] != _NATIVE_TYPE_RECORD.size
        or header[3] != _NATIVE_METHOD_RECORD.size
        or header[4]
        or not type_count
        or not method_count
        or records_end > len(raw)
        or _ascii_digest(header[8], label="executable")
        != executable_sha256
    ):
        raise AcquisitionError("runtime type identity inventory is invalid")
    return {
        "identity": file_identity(path),
        "type_count": type_count,
        "method_count": method_count,
        "image_bytes": header[7],
    }


def _identity_binding(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    native_inventory: Path,
    ancestry_model: Path,
    string_layout_model: Path | None = None,
) -> dict[str, Any]:
    current = current_runtime_process_binding()
    if current is None or string_layout_model is None:
        raise AcquisitionError("type identity requires current String layout evidence")


    binary = binary.expanduser()
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantic model"
    )
    ancestry_path = _owner_file(ancestry_model, label="ancestry model")
    identity = file_identity(binary)
    semantics = read_json(semantics_path)
    ancestry = read_json(ancestry_path)
    if (
        not isinstance(semantics, dict)
        or semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary", {}).get("sha256") != identity["sha256"]
        or semantics.get("contract", {}).get(
            "semantic_operation_resolution_complete"
        )
        is not True
        or semantics.get("checks", {}).get("all_operations_resolved")
        is not True
        or semantics.get("behavior_evidence", {}).get(
            "fresh_runtime_observation"
        )
        is not True
    ):
        raise AcquisitionError(
            "runtime type identity semantic binding is stale"
        )
    operations = {
        operation.get("key"): operation
        for operation in semantics.get("operations", [])
        if isinstance(operation, dict)
    }
    if set(_REQUIRED_OPERATIONS) - set(operations) or any(
        operations[key].get("semantic_identity_resolved") is not True
        or not isinstance(operations[key].get("method_pointer"), int)
        or operations[key]["method_pointer"] <= 0
        or not isinstance(operations[key].get("metadata_pointer"), int)
        or operations[key]["metadata_pointer"] <= 0
        for key in _REQUIRED_OPERATIONS
    ):
        raise AcquisitionError(
            "runtime type identity operation binding is incomplete"
        )
    behavior = semantics.get("behavior_evidence")
    if not isinstance(behavior, dict):
        raise AcquisitionError("runtime type identity behavior is absent")
    plan_record = behavior.get("plan")
    receipt_record = behavior.get("receipt")
    if not isinstance(plan_record, dict) or not isinstance(receipt_record, dict):
        raise AcquisitionError(
            "runtime type identity behavior receipts are absent"
        )
    plan_path = _owner_file(Path(plan_record["path"]), label="behavior plan")
    receipt_path = _owner_file(
        Path(receipt_record["path"]), label="behavior receipt"
    )
    if (
        file_identity(plan_path)["sha256"] != plan_record.get("sha256")
        or file_identity(receipt_path)["sha256"]
        != receipt_record.get("sha256")
    ):
        raise AcquisitionError(
            "runtime type identity behavior binding is stale"
        )
    plan = read_json(plan_path)
    receipt = read_json(receipt_path)
    if (
        not isinstance(plan, dict)
        or not isinstance(receipt, dict)
        or receipt.get("status") != "validated"
        or not all(receipt.get("checks", {}).values())
        or plan.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or plan.get("target", {}).get("process_id") <= 0
    ):
        raise AcquisitionError(
            "runtime type identity behavior receipt is invalid"
        )
    fresh_factory = plan.get("candidates_owner_only", {}).get(
        "fresh_event_factory"
    )
    known_identity_rows = (
        fresh_factory.get("known_type_identity_rows_owner_only")
        if isinstance(fresh_factory, dict)
        else None
    )
    known_descriptors = (
        [
            row.get("descriptor_pointer_owner_only")
            for row in known_identity_rows
            if isinstance(row, dict)
        ]
        if isinstance(known_identity_rows, list)
        else []
    )
    warmup_descriptors = (
        fresh_factory.get("descriptor_pointers_owner_only")
        if isinstance(fresh_factory, dict)
        else None
    )
    runtime_type_descriptor = (
        fresh_factory.get("runtime_type_descriptor_pointer_owner_only")
        if isinstance(fresh_factory, dict)
        else None
    )
    if (
        len(known_descriptors) < 8
        or len(set(known_descriptors)) != len(known_descriptors)
        or any(not isinstance(value, int) or value <= 0 for value in known_descriptors)
        or not isinstance(runtime_type_descriptor, int)
        or runtime_type_descriptor <= 0
        or runtime_type_descriptor not in known_descriptors
        or not isinstance(warmup_descriptors, list)
        or len(warmup_descriptors) < 8
        or len(set(warmup_descriptors)) != len(warmup_descriptors)
        or any(
            not isinstance(value, int) or value <= 0
            for value in warmup_descriptors
        )
    ):
        raise AcquisitionError(
            "runtime type identity handle derivation domain is incomplete"
        )
    class_record = plan.get("inputs", {}).get("classes")
    bootstrap_record = plan.get("inputs", {}).get("bootstrap")
    snapshot_record = plan.get("inputs", {}).get("snapshot")
    materializer_record = plan.get("inputs", {}).get("materializer")
    if not all(
        isinstance(value, dict)
        for value in (
            class_record,
            bootstrap_record,
            snapshot_record,
            materializer_record,
        )
    ):
        raise AcquisitionError(
            "runtime type identity class, snapshot, or materializer binding "
            "is absent"
        )
    class_path = _owner_file(Path(class_record["path"]), label="class model")
    bootstrap_path = _owner_file(
        Path(bootstrap_record["path"]), label="bootstrap model"
    )
    snapshot_path = _owner_file(
        Path(snapshot_record["path"]), label="snapshot"
    )
    materializer_path = _owner_file(
        Path(materializer_record["path"]), label="materializer model"
    )
    classes = read_json(class_path)
    bootstrap = read_json(bootstrap_path)
    materializer = read_json(materializer_path)
    if (
        file_identity(class_path)["sha256"] != class_record.get("sha256")
        or file_identity(bootstrap_path)["sha256"]
        != bootstrap_record.get("sha256")
        or file_identity(snapshot_path)["sha256"]
        != snapshot_record.get("sha256")
        or file_identity(materializer_path)["sha256"]
        != materializer_record.get("sha256")
        or not isinstance(classes, dict)
        or classes.get("schema") != RUNTIME_CLASS_SCHEMA
        or not isinstance(bootstrap, dict)
        or bootstrap.get("schema") != REFLECTION_BOOTSTRAP_SCHEMA
        or not isinstance(materializer, dict)
        or materializer.get("schema") != RUNTIME_TYPE_MATERIALIZER_SCHEMA
        or materializer.get("status") != "runtime-validated"
        or materializer.get("checks", {}).get(
            "all_type_definitions_materialized"
        )
        is not True
        or materializer.get("checks", {}).get(
            "materializer_runtime_validated"
        )
        is not True
        or materializer.get("checks", {}).get(
            "external_runtime_component_used"
        )
        is not False
        or materializer.get("checks", {}).get("fixed_address_used")
        is not False
        or materializer.get("checks", {}).get("fixed_offset_used")
        is not False
        or materializer.get("checks", {}).get("fixed_rva_used")
        is not False
        or materializer.get("checks", {}).get("fixed_version_used")
        is not False
        or materializer.get("checks", {}).get("saved_descriptor_used")
        is not False
        or not all(
            materializer.get("runtime_validation", {})
            .get("checks", {})
            .values()
        )
        or materializer.get("binary", {}).get("sha256")
        != identity["sha256"]
        or materializer.get("snapshot", {}).get("sha256")
        != snapshot_record.get("sha256")
    ):
        raise AcquisitionError(
            "runtime type identity class, snapshot, or materializer model "
            "is stale"
        )
    embedded_descriptor_byte_offset = materializer.get("layout", {}).get(
        "embedded_descriptor_byte_offset"
    )
    if (
        not isinstance(embedded_descriptor_byte_offset, int)
        or not 0 < embedded_descriptor_byte_offset < 4096
        or embedded_descriptor_byte_offset % 8
    ):
        raise AcquisitionError(
            "runtime type identity embedded descriptor binding is absent"
        )
    class_pointers = {
        row.get("runtime_owner"): row.get("class_pointer")
        for row in classes.get("classes", [])
        if isinstance(row, dict)
    }
    runtime_type_class = class_pointers.get("System.RuntimeType")
    if current[0] != plan["target"]["process_id"] or not same_executable_path(
        current[2], binary
    ):
        raise AcquisitionError("type identity behavior process differs from current binding")
    layout_path = _owner_file(string_layout_model, label="String layout model")
    layout_identity = file_identity(layout_path)
    string_layout = load_runtime_string_layout_candidate(
        model_path=layout_path,
        expected_identity={"executable_path": str(binary), "executable_sha256": identity["sha256"],
            "process_id": current[0], "creation_filetime": current[1],
            "image_base": plan["target"]["image_base_owner_only"], "image_bytes": plan["target"]["image_bytes"]},
        expected_inputs={"snapshot": file_identity(snapshot_path), "native_inventory": file_identity(native_inventory)})
    if file_identity(layout_path) != layout_identity:
        raise AcquisitionError("type identity String layout model changed")
    string_class = string_layout["class_pointer"]
    string_descriptor = string_class + embedded_descriptor_byte_offset
    if string_descriptor >= 1 << 64:
        raise AcquisitionError("type identity String descriptor overflows")
    if not isinstance(runtime_type_class, int) or not runtime_type_class or not isinstance(
        string_class, int
    ) or not string_class:
        raise AcquisitionError(
            "runtime type identity required classes are unavailable"
        )
    inventory = _native_inventory_header(
        native_inventory, executable_sha256=identity["sha256"]
    )
    expected_inventory = plan.get("inputs", {}).get("native_inventory")
    if (
        not isinstance(expected_inventory, dict)
        or inventory["identity"]["sha256"]
        != expected_inventory.get("sha256")
        or inventory["image_bytes"]
        != plan.get("target", {}).get("image_bytes")
        or materializer.get("runtime_validation", {})
        .get("native_inventory", {})
        .get("sha256")
        != inventory["identity"]["sha256"]
    ):
        raise AcquisitionError(
            "runtime type identity native inventory is stale"
        )
    if (
        not isinstance(ancestry, dict)
        or ancestry.get("schema") != RUNTIME_TYPE_ANCESTRY_SCHEMA
        or ancestry.get("status") != "runtime-validated"
        or ancestry.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or ancestry.get("inputs", {}).get("native_inventory", {}).get(
            "sha256"
        )
        != inventory["identity"]["sha256"]
        or ancestry.get("counts", {}).get("type_count")
        != inventory["type_count"]
        or not all(ancestry.get("checks", {}).values())
    ):
        raise AcquisitionError("runtime type identity ancestry is stale")
    ancestry_inventory_record = ancestry.get("ancestry_inventory")
    if not isinstance(ancestry_inventory_record, dict):
        raise AcquisitionError(
            "runtime type identity ancestry inventory is absent"
        )
    ancestry_inventory_path = _owner_file(
        Path(ancestry_inventory_record["path"]),
        label="ancestry inventory",
    )
    if (
        file_identity(ancestry_inventory_path)["sha256"]
        != ancestry_inventory_record.get("sha256")
    ):
        raise AcquisitionError(
            "runtime type identity ancestry inventory is stale"
        )
    return {
        "binary": identity,
        "semantics": file_identity(semantics_path),
        "behavior_plan": file_identity(plan_path),
        "behavior_receipt": file_identity(receipt_path),
        "class_model": file_identity(class_path),
        "bootstrap_model": file_identity(bootstrap_path),
        "snapshot": file_identity(snapshot_path),
        "materializer_model": file_identity(materializer_path),
        "native_inventory": inventory["identity"],
        "ancestry_model": file_identity(ancestry_path),
        "ancestry_inventory": file_identity(ancestry_inventory_path),
        "process_id": plan["target"]["process_id"],
        "image_base": plan["target"]["image_base_owner_only"],
        "image_bytes": plan["target"]["image_bytes"],
        "type_count": inventory["type_count"],
        "runtime_type_class": runtime_type_class,
        "string_class": string_class,
        "string_layout_contract": string_layout,
        "string_layout_model": layout_identity,
        "known_descriptors_owner_only": known_descriptors,
        "warmup_descriptors_owner_only": warmup_descriptors,
        "runtime_type_descriptor_owner_only": runtime_type_descriptor,
        "string_descriptor_owner_only": string_descriptor,
        "embedded_type_descriptor_offset_owner_only": (
            embedded_descriptor_byte_offset
        ),
        "operations_owner_only": {
            key: {
                "pointer": operations[key]["method_pointer"],
                "metadata": operations[key]["metadata_pointer"],
            }
            for key in _REQUIRED_OPERATIONS
        },
    }


def runtime_type_identity_inventory_source(
    *,
    binding: dict[str, Any],
    native_inventory_path: Path,
    output_path: Path,
    status_path: Path,
) -> str:
    operations = binding["operations_owner_only"]
    known_descriptors = ", ".join(
        f"{value}ull" for value in binding["known_descriptors_owner_only"]
    )
    warmup_descriptors = ", ".join(
        f"{value}ull" for value in binding["warmup_descriptors_owner_only"]
    )

    def pointer(key: str) -> int:
        return operations[key]["pointer"]

    def metadata(key: str) -> int:
        return operations[key]["metadata"]

    return rf'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#define ALPHA_MAX_MANAGED_TEXT 16384u
#define ALPHA_HANDLE_QWORD_LIMIT 16u

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
    uint32_t layout[8];
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

typedef struct alpha_identity_header {{
    char magic[8];
    uint32_t version;
    uint32_t header_bytes;
    uint32_t record_bytes;
    uint32_t reserved;
    uint64_t type_count;
    uint64_t image_base;
    uint64_t image_bytes;
    uint64_t string_bytes;
    char executable_sha256[64];
    char native_inventory_sha256[64];
    char reflection_semantics_sha256[64];
}} alpha_identity_header;

typedef struct alpha_identity_record {{
    uint32_t definition_index;
    uint32_t flags;
    uint64_t descriptor_pointer;
    uint64_t class_pointer;
    uint64_t module_pointer;
    uint64_t declaring_descriptor_pointer;
    uint64_t type_object;
    uint32_t attributes;
    uint32_t name_bytes;
    uint32_t namespace_bytes;
    uint32_t reserved;
    uint64_t name_offset;
    uint64_t namespace_offset;
}} alpha_identity_record;

_Static_assert(sizeof(alpha_native_inventory_header) ==
    {_NATIVE_INVENTORY_HEADER.size}, "native header layout mismatch");
_Static_assert(sizeof(alpha_native_type_record) ==
    {_NATIVE_TYPE_RECORD.size}, "native type layout mismatch");
_Static_assert(sizeof(alpha_identity_header) ==
    {_IDENTITY_HEADER.size}, "identity header layout mismatch");
_Static_assert(sizeof(alpha_identity_record) ==
    {_IDENTITY_RECORD.size}, "identity record layout mismatch");

static const char expected_executable_sha256[] =
    "{binding['binary']['sha256']}";
static const char expected_native_inventory_sha256[] =
    "{binding['native_inventory']['sha256']}";
static const char expected_reflection_semantics_sha256[] =
    "{binding['semantics']['sha256']}";
static const DWORD expected_process_id = {binding['process_id']}u;
static const uintptr_t expected_image_base = {binding['image_base']}ull;
static const uint64_t expected_image_bytes = {binding['image_bytes']}ull;
static const uint64_t expected_type_count = {binding['type_count']}ull;
static const uintptr_t runtime_type_class =
    {binding['runtime_type_class']}ull;
static const uintptr_t string_class = {binding['string_class']}ull;
static const uintptr_t known_descriptors[] = {{{known_descriptors}}};
static const uintptr_t warmup_descriptors[] = {{{warmup_descriptors}}};
static const uintptr_t runtime_type_descriptor =
    {binding['runtime_type_descriptor_owner_only']}ull;
static const uintptr_t string_descriptor =
    {binding['string_descriptor_owner_only']}ull;
static const uint32_t embedded_type_descriptor_offset =
    {binding['embedded_type_descriptor_offset_owner_only']}u;
static const wchar_t native_inventory_input[] =
    {_wide_literal(_windows_z_path(native_inventory_path))};
static const wchar_t identity_output[] =
    {_wide_literal(_windows_z_path(output_path))};
static const wchar_t status_output[] =
    {_wide_literal(_windows_z_path(status_path))};

typedef uintptr_t (*alpha_static_qwordarg)(uintptr_t, uintptr_t);
typedef uintptr_t (*alpha_instance_noarg)(uintptr_t, uintptr_t);
typedef uint32_t (*alpha_instance_dword)(uintptr_t, uintptr_t);
typedef uint8_t (*alpha_instance_bool)(uintptr_t, uintptr_t);

typedef struct alpha_candidate {{
    uintptr_t metadata;
    uintptr_t pointer;
    uint32_t index;
}} alpha_candidate;

static const alpha_candidate type_from_handle_candidate[] = {{
    {{{metadata('type.from_handle')}ull, {pointer('type.from_handle')}ull, 0u}}
}};
static const uintptr_t name_pointer = {pointer('type.name')}ull;
static const uintptr_t name_metadata = {metadata('type.name')}ull;
static const uintptr_t namespace_pointer = {pointer('type.namespace')}ull;
static const uintptr_t namespace_metadata = {metadata('type.namespace')}ull;
static const uintptr_t module_pointer = {pointer('type.module')}ull;
static const uintptr_t module_metadata = {metadata('type.module')}ull;
static const uintptr_t declaring_pointer = {pointer('type.declaring_type')}ull;
static const uintptr_t declaring_metadata = {metadata('type.declaring_type')}ull;
static const uintptr_t attributes_pointer = {pointer('type.attributes')}ull;
static const uintptr_t attributes_metadata = {metadata('type.attributes')}ull;
static const uintptr_t metadata_token_pointer =
    {pointer('member.metadata_token')}ull;
static const uintptr_t metadata_token_metadata =
    {metadata('member.metadata_token')}ull;
static const uintptr_t is_enum_pointer = {pointer('type.is_enum')}ull;
static const uintptr_t is_enum_metadata = {metadata('type.is_enum')}ull;
static const uintptr_t is_value_pointer = {pointer('type.is_value_type')}ull;
static const uintptr_t is_value_metadata = {metadata('type.is_value_type')}ull;
static volatile LONG diagnostic_handle_samples;
static volatile LONG diagnostic_handle_exact_candidates;
static volatile LONG diagnostic_handle_max_support;
static volatile LONG diagnostic_descriptor_readable;
static volatile LONG diagnostic_from_handle_nonzero;
static volatile LONG diagnostic_from_handle_object_readable;
static volatile LONG diagnostic_warmup_descriptor_readable;
static volatile LONG diagnostic_warmup_nonzero;
static volatile LONG diagnostic_warmup_object_readable;
static volatile LONG diagnostic_warmup_runtime_type;
static UINT probe_message;
static WNDPROC original_window_proc;
static alpha_native_type_record *runtime_types;
static alpha_identity_record *runtime_records;
static char **runtime_names;
static char **runtime_namespaces;
static uint32_t runtime_handle_qword;
static uint64_t runtime_capture_index;
static uint64_t runtime_completed;
static uint64_t runtime_name_count;
static uint64_t runtime_namespace_count;
static uint64_t runtime_module_count;
static uint64_t runtime_declaring_count;
static uint64_t runtime_enum_count;
static uint64_t runtime_value_count;
static uint64_t runtime_synthetic_name_count;
static uint64_t runtime_metadata_token_match_count;
static uint32_t runtime_metadata_token_rid_base;
static uint64_t runtime_string_bytes;
static uint64_t runtime_failure_index;
static uint32_t runtime_failure_kind;
static uint32_t runtime_failure_observed_token;
static uint32_t runtime_failure_expected_token;
static uint32_t runtime_failure_name_bytes;
static uint32_t runtime_failure_name_is_module;
static volatile LONG callback_action;
static volatile LONG callback_complete;

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

static int safe_read(uintptr_t value, void *output, SIZE_T bytes) {{
    if (!output || !readable(value, bytes)) return 0;
    memcpy(output, (const void *)value, bytes);
    return 1;
}}

static int object_class(uintptr_t object, uintptr_t expected) {{
    uintptr_t observed = 0;
    if (!readable(object, sizeof(observed))) return 0;
    memcpy(&observed, (const void *)object, sizeof(observed));
    return observed == expected;
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
    HANDLE input = CreateFileW(path, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (input == INVALID_HANDLE_VALUE) return 0;
    BCRYPT_ALG_HANDLE algorithm = NULL;
    BCRYPT_HASH_HANDLE hash = NULL;
    DWORD object_size = 0, received = 0;
    unsigned char *object = NULL, *buffer = NULL, digest[32];
    int ok = BCryptOpenAlgorithmProvider(
        &algorithm, BCRYPT_SHA256_ALGORITHM, NULL, 0) >= 0 &&
        BCryptGetProperty(algorithm, BCRYPT_OBJECT_LENGTH,
            (PUCHAR)&object_size, sizeof(object_size), &received, 0) >= 0 &&
        object_size && received == sizeof(object_size);
    if (ok) object = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, object_size);
    if (ok) buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, 1024u * 1024u);
    if (ok && (!object || !buffer)) ok = 0;
    if (ok && BCryptCreateHash(
            algorithm, &hash, object, object_size, NULL, 0, 0) < 0) ok = 0;
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
        NULL, path, (DWORD)(sizeof(path) / sizeof(path[0])));
    return length && length < sizeof(path) / sizeof(path[0]) &&
        sha256_file(path, output);
}}

{native_string_reader_source(contract=binding['string_layout_contract'], output_path=output_path.parent / 'runtime-string-layout-io.private.json')}

static int descriptor_from_type(
    uintptr_t object, uint32_t handle_qword, uintptr_t *descriptor
) {{
    *descriptor = 0;
    if (!object) return 1;
    if (!object_class(object, runtime_type_class) ||
        handle_qword < 2u || handle_qword >= ALPHA_HANDLE_QWORD_LIMIT)
        return 0;
    uintptr_t address = object + (uintptr_t)handle_qword * sizeof(uintptr_t);
    unsigned char probe[16];
    if (address < object ||
        !safe_read(address, descriptor, sizeof(*descriptor))) return 0;
    return safe_read(*descriptor, probe, sizeof(probe));
}}

static int descriptors_equal(uintptr_t left, uintptr_t right) {{
    unsigned char left_value[16], right_value[16];
    return safe_read(left, left_value, sizeof(left_value)) &&
        safe_read(right, right_value, sizeof(right_value)) &&
        !memcmp(left_value, right_value, sizeof(left_value));
}}

static int derive_handle_qword(uint32_t *selected) {{
    alpha_static_qwordarg from_handle =
        (alpha_static_qwordarg)type_from_handle_candidate[0].pointer;
    uint32_t support[ALPHA_HANDLE_QWORD_LIMIT] = {{0}};
    uint32_t samples = 0;
    uint32_t descriptor_readable = 0;
    uint32_t from_handle_nonzero = 0;
    uint32_t from_handle_object_readable = 0;
    uint32_t known_count = (uint32_t)(
        sizeof(known_descriptors) / sizeof(known_descriptors[0]));
    uint32_t warmup_count = 0;
    uint32_t warmup_descriptor_readable = 0;
    uint32_t warmup_nonzero = 0;
    uint32_t warmup_object_readable = 0;
    for (uint32_t index = 0;
         index < sizeof(warmup_descriptors) / sizeof(warmup_descriptors[0]);
         index++) {{
        if (readable(warmup_descriptors[index], 16u))
            warmup_descriptor_readable++;
        uintptr_t object = from_handle(
            warmup_descriptors[index],
            type_from_handle_candidate[0].metadata);
        if (object) warmup_nonzero++;
        if (readable(object, sizeof(uintptr_t))) warmup_object_readable++;
        if (object_class(object, runtime_type_class)) warmup_count++;
    }}
    InterlockedExchange(&diagnostic_warmup_descriptor_readable,
        (LONG)warmup_descriptor_readable);
    InterlockedExchange(&diagnostic_warmup_nonzero, (LONG)warmup_nonzero);
    InterlockedExchange(&diagnostic_warmup_object_readable,
        (LONG)warmup_object_readable);
    InterlockedExchange(&diagnostic_warmup_runtime_type, (LONG)warmup_count);
    if (warmup_count < 8u) return 0;
    uintptr_t runtime_type_object = from_handle(
        runtime_type_descriptor, type_from_handle_candidate[0].metadata);
    uintptr_t string_type_object = from_handle(
        string_descriptor, type_from_handle_candidate[0].metadata);
    if (!object_class(runtime_type_object, runtime_type_class) ||
        !object_class(string_type_object, runtime_type_class)) return 0;
    for (uint32_t index = 0; index < known_count; index++) {{
        uintptr_t descriptor = known_descriptors[index];
        unsigned char expected[16];
        if (!safe_read(descriptor, expected, sizeof(expected)))
            continue;
        descriptor_readable++;
        uintptr_t object = from_handle(
            descriptor, type_from_handle_candidate[0].metadata);
        if (object) from_handle_nonzero++;
        if (readable(object, sizeof(uintptr_t)))
            from_handle_object_readable++;
        if (!object_class(object, runtime_type_class)) continue;
        samples++;
        for (uint32_t qword = 2u; qword < ALPHA_HANDLE_QWORD_LIMIT; qword++) {{
            uintptr_t handle = 0;
            uintptr_t address = object + (uintptr_t)qword * sizeof(uintptr_t);
            if (!safe_read(address, &handle, sizeof(handle))) continue;
            unsigned char observed[16];
            if (!safe_read(handle, observed, sizeof(observed))) continue;
            if (!memcmp(observed, expected, sizeof(expected))) support[qword]++;
        }}
    }}
    uint32_t matches = 0;
    uint32_t max_support = 0;
    *selected = 0;
    for (uint32_t qword = 2u; qword < ALPHA_HANDLE_QWORD_LIMIT; qword++) {{
        if (support[qword] > max_support) max_support = support[qword];
        if (support[qword] != samples) continue;
        *selected = qword;
        matches++;
    }}
    InterlockedExchange(&diagnostic_handle_samples, (LONG)samples);
    InterlockedExchange(&diagnostic_handle_exact_candidates, (LONG)matches);
    InterlockedExchange(&diagnostic_handle_max_support, (LONG)max_support);
    InterlockedExchange(
        &diagnostic_descriptor_readable, (LONG)descriptor_readable);
    InterlockedExchange(
        &diagnostic_from_handle_nonzero, (LONG)from_handle_nonzero);
    InterlockedExchange(&diagnostic_from_handle_object_readable,
        (LONG)from_handle_object_readable);
    return samples == known_count && samples >= 16u && matches == 1u;
}}

static int capture_type_batch(void) {{
    alpha_static_qwordarg from_handle =
        (alpha_static_qwordarg)type_from_handle_candidate[0].pointer;
    alpha_instance_noarg get_name = (alpha_instance_noarg)name_pointer;
    alpha_instance_noarg get_namespace =
        (alpha_instance_noarg)namespace_pointer;
    alpha_instance_noarg get_module = (alpha_instance_noarg)module_pointer;
    alpha_instance_noarg get_declaring =
        (alpha_instance_noarg)declaring_pointer;
    alpha_instance_dword get_attributes =
        (alpha_instance_dword)attributes_pointer;
    alpha_instance_dword get_metadata_token =
        (alpha_instance_dword)metadata_token_pointer;
    alpha_instance_bool get_is_enum = (alpha_instance_bool)is_enum_pointer;
    alpha_instance_bool get_is_value = (alpha_instance_bool)is_value_pointer;
    uint64_t end = runtime_capture_index + {RUNTIME_TYPE_IDENTITY_BATCH_ROWS}u;
    if (end < runtime_capture_index || end > expected_type_count)
        end = expected_type_count;
    for (; runtime_capture_index < end; runtime_capture_index++) {{
        uint64_t index = runtime_capture_index;
        const alpha_native_type_record *native = &runtime_types[index];
        if (native->definition_index != index || !native->descriptor_rva ||
            native->descriptor_rva >= expected_image_bytes ||
            !native->class_pointer) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 1u;
            return 0;
        }}
        uintptr_t descriptor = native->class_pointer +
            embedded_type_descriptor_offset;
        if (descriptor < native->class_pointer) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 2u;
            return 0;
        }}
        uintptr_t object = from_handle(
            descriptor, type_from_handle_candidate[0].metadata);
        uintptr_t observed_descriptor = 0;
        if (!object_class(object, runtime_type_class) ||
            !descriptor_from_type(
                object, runtime_handle_qword, &observed_descriptor) ||
            !descriptors_equal(observed_descriptor, descriptor)) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 3u;
            return 0;
        }}
        uintptr_t name_object = get_name(object, name_metadata);
        uintptr_t namespace_object = get_namespace(object, namespace_metadata);
        uintptr_t module = get_module(object, module_metadata);
        uintptr_t declaring_object = get_declaring(object, declaring_metadata);
        uintptr_t declaring_descriptor = 0;
        uint32_t attributes = get_attributes(object, attributes_metadata);
        uint8_t is_enum = get_is_enum(object, is_enum_metadata);
        uint8_t is_value = get_is_value(object, is_value_metadata);
        uint32_t metadata_token = get_metadata_token(
            object, metadata_token_metadata);
        uint32_t name_bytes = 0, namespace_bytes = 0;
        if (!managed_utf8(
                name_object, 0, &runtime_names[index], &name_bytes)) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 4u;
            return 0;
        }}
        if (!managed_utf8(namespace_object, 1,
                &runtime_namespaces[index], &namespace_bytes)) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 6u;
            return 0;
        }}
        uint32_t metadata_token_rid = metadata_token & 0x00ffffffu;
        if ((metadata_token & 0xff000000u) != 0x02000000u ||
            index > 0x00ffffffu) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 11u;
            return 0;
        }}
        if (!index) runtime_metadata_token_rid_base = metadata_token_rid;
        uint64_t expected_metadata_token_rid =
            index + (uint64_t)runtime_metadata_token_rid_base;
        if (runtime_metadata_token_rid_base > 1u ||
            expected_metadata_token_rid > 0x00ffffffu ||
            metadata_token_rid != expected_metadata_token_rid) {{
            runtime_failure_observed_token = metadata_token;
            runtime_failure_expected_token = 0x02000000u |
                (uint32_t)expected_metadata_token_rid;
            runtime_failure_name_bytes = name_bytes;
            runtime_failure_name_is_module =
                name_bytes == 8u && runtime_names[index] &&
                !memcmp(runtime_names[index], "<Module>", 8u);
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 11u;
            return 0;
        }}
        runtime_metadata_token_match_count++;
        if (!name_bytes) {{
            char synthetic[32];
            int count = snprintf(
                synthetic, sizeof(synthetic), "EmptyType_%X", metadata_token);
            if (count <= 0 || count >= (int)sizeof(synthetic)) {{
                runtime_failure_index = index + 1u;
                runtime_failure_kind = 12u;
                return 0;
            }}
            runtime_names[index] = (char *)malloc((SIZE_T)count);
            if (!runtime_names[index]) {{
                runtime_failure_index = index + 1u;
                runtime_failure_kind = 13u;
                return 0;
            }}
            memcpy(runtime_names[index], synthetic, (SIZE_T)count);
            name_bytes = (uint32_t)count;
            runtime_synthetic_name_count++;
        }}
        if (!module || !readable(module, sizeof(uintptr_t))) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 7u;
            return 0;
        }}
        if (!descriptor_from_type(
                declaring_object, runtime_handle_qword,
                &declaring_descriptor)) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 8u;
            return 0;
        }}
        if (declaring_descriptor) {{
            uint64_t declaring_index = UINT64_MAX;
            if (!safe_read(
                    declaring_descriptor, &declaring_index,
                    sizeof(declaring_index)) ||
                declaring_index >= expected_type_count) {{
                runtime_failure_index = index + 1u;
                runtime_failure_kind = 14u;
                return 0;
            }}
            uintptr_t canonical_declaring =
                runtime_types[declaring_index].class_pointer +
                embedded_type_descriptor_offset;
            if (canonical_declaring <
                    runtime_types[declaring_index].class_pointer ||
                !descriptors_equal(
                    declaring_descriptor, canonical_declaring)) {{
                runtime_failure_index = index + 1u;
                runtime_failure_kind = 15u;
                return 0;
            }}
            declaring_descriptor = canonical_declaring;
        }}
        if (is_enum > 1u || is_value > 1u) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 9u;
            return 0;
        }}
        if (runtime_string_bytes + name_bytes < runtime_string_bytes ||
            runtime_string_bytes + name_bytes + namespace_bytes
                < runtime_string_bytes) {{
            runtime_failure_index = index + 1u;
            runtime_failure_kind = 10u;
            return 0;
        }}
        alpha_identity_record *record = &runtime_records[index];
        record->definition_index = (uint32_t)index;
        record->flags = 1u | 2u | (namespace_bytes ? 4u : 0u) | 8u |
            (declaring_descriptor ? 16u : 0u) |
            (is_enum ? 32u : 0u) | (is_value ? 64u : 0u);
        record->descriptor_pointer = descriptor;
        record->class_pointer = native->class_pointer;
        record->module_pointer = module;
        record->declaring_descriptor_pointer = declaring_descriptor;
        record->type_object = object;
        record->attributes = attributes;
        record->name_bytes = name_bytes;
        record->namespace_bytes = namespace_bytes;
        record->reserved = metadata_token;
        runtime_string_bytes += name_bytes + namespace_bytes;
        runtime_completed++;
        runtime_name_count++;
        if (namespace_bytes) runtime_namespace_count++;
        runtime_module_count++;
        if (declaring_descriptor) runtime_declaring_count++;
        if (is_enum) runtime_enum_count++;
        if (is_value) runtime_value_count++;
    }}
    return 1;
}}

static volatile LONG current_request, request_sequence, callback_active;
static LRESULT CALLBACK probe_window_proc(HWND window,UINT message,WPARAM wparam,LPARAM lparam){{
    if(message!=probe_message)return CallWindowProcW(original_window_proc,window,message,wparam,lparam);
    LONG request=(LONG)wparam;
    if(!request||InterlockedCompareExchange(&current_request,0,0)!=request||
       InterlockedCompareExchange(&callback_active,1,0))return 0;
    /* Consume the generation exactly once. A delayed, duplicated or reentrant
       message must never repeat layout discovery or advance another batch. */
    if(InterlockedCompareExchange(&current_request,0,request)!=request){{
        InterlockedExchange(&callback_active,0);return 0;
    }}
    LONG action=InterlockedCompareExchange(&callback_action,0,0);
    int ok=action==1?derive_handle_qword(&runtime_handle_qword):action==2?capture_type_batch():0;
    InterlockedExchange(&callback_complete,ok?1:-1);
    InterlockedExchange(&callback_active,0);
    return ok;
}}
typedef struct selection{{DWORD pid;HWND window;uint32_t count;}}selection;
static BOOL CALLBACK select_window(HWND window,LPARAM value){{selection*s=(selection*)(uintptr_t)value;DWORD pid=0;RECT bounds;if(!IsWindowVisible(window)||GetWindow(window,GW_OWNER)||!GetWindowRect(window,&bounds)||bounds.right<=bounds.left||bounds.bottom<=bounds.top)return TRUE;GetWindowThreadProcessId(window,&pid);if(pid==s->pid){{s->window=window;s->count++;}}return TRUE;}}
static int dispatch_managed_capture(void){{
    selection s={{0}};s.pid=GetCurrentProcessId();
    if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window){{runtime_failure_kind=400;runtime_failure_index=s.count;return 0;}}
    probe_message=RegisterWindowMessageW(L"ALPHA v2 current runtime full type identity inventory");
    if(!probe_message){{runtime_failure_kind=402;runtime_failure_index=GetLastError();return 0;}}
    SetLastError(0);
    original_window_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)probe_window_proc);
    DWORD error=GetLastError();
    if(!original_window_proc||error!=ERROR_SUCCESS){{runtime_failure_kind=403;runtime_failure_index=error;return 0;}}
    int ok=1,layouts_ready=0;uint32_t retries=0;
    while(ok&&(!layouts_ready||runtime_capture_index<expected_type_count)){{
        DWORD_PTR result=0;uint64_t before=runtime_capture_index;
        LONG request=InterlockedIncrement(&request_sequence);
        InterlockedExchange(&callback_action,layouts_ready?2:1);
        InterlockedExchange(&callback_complete,0);
        InterlockedExchange(&current_request,request);
        SetLastError(0);
        int sent=SendMessageTimeoutW(s.window,probe_message,(WPARAM)request,0,SMTO_BLOCK,60000,&result)!=0;
        error=GetLastError();
        InterlockedExchange(&current_request,0);
        /* A timeout does not cancel a callback already running on the game
           thread. Never change its action or launch another while it runs. */
        for(uint32_t wait=0;InterlockedCompareExchange(&callback_active,0,0)&&wait<2000u;wait++)Sleep(1);
        if(InterlockedCompareExchange(&callback_active,0,0)){{runtime_failure_kind=404;ok=0;break;}}
        LONG complete=InterlockedCompareExchange(&callback_complete,0,0);
        if(complete==1){{
            if(layouts_ready&&runtime_capture_index<=before){{runtime_failure_kind=408;ok=0;break;}}
            layouts_ready=1;retries=0;continue;
        }}
        if(complete<0||runtime_failure_kind){{if(!runtime_failure_kind)runtime_failure_kind=405;ok=0;break;}}
        if(!sent&&retries++<16u){{Sleep(250);continue;}}
        runtime_failure_kind=401;runtime_failure_index=error;ok=0;
    }}
    InterlockedExchange(&current_request,0);
    SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_window_proc);
    /* Keep procedure pointer and collector storage alive on failure, even
       while an already-running callback is unwinding. */
    return ok;
}}

static void write_status(
    const char *status, const char *observed_hash,
    uint64_t completed, uint64_t names, uint64_t namespaces,
    uint64_t modules, uint64_t declaring, uint64_t enum_count,
    uint64_t value_count, uint32_t handle_qword, uint64_t failure_index
) {{
    FILE *output = _wfopen(status_output, L"wb");
    if (!output) return;
    fprintf(output,
        "{{\n"
        "  \"schema\": \"{RUNTIME_TYPE_IDENTITY_STATUS_SCHEMA}\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"expected_type_count\": %llu,\n"
        "  \"completed_type_count\": %llu,\n"
        "  \"nonempty_name_count\": %llu,\n"
        "  \"nonempty_namespace_count\": %llu,\n"
        "  \"module_count_observations\": %llu,\n"
        "  \"declaring_type_count\": %llu,\n"
        "  \"enum_count\": %llu,\n"
        "  \"value_type_count\": %llu,\n"
        "  \"synthetic_empty_name_count\": %llu,\n"
        "  \"runtime_metadata_token_match_count\": %llu,\n"
        "  \"runtime_metadata_token_rid_base\": %u,\n"
        "  \"runtime_type_handle_qword_owner_only\": %u,\n"
        "  \"runtime_type_handle_sample_count_owner_only\": %ld,\n"
        "  \"runtime_type_handle_exact_candidate_count_owner_only\": %ld,\n"
        "  \"runtime_type_handle_max_support_owner_only\": %ld,\n"
        "  \"runtime_type_descriptor_readable_count_owner_only\": %ld,\n"
        "  \"runtime_type_from_handle_nonzero_count_owner_only\": %ld,\n"
        "  \"runtime_type_from_handle_readable_count_owner_only\": %ld,\n"
        "  \"warmup_descriptor_readable_count_owner_only\": %ld,\n"
        "  \"warmup_from_handle_nonzero_count_owner_only\": %ld,\n"
        "  \"warmup_from_handle_readable_count_owner_only\": %ld,\n"
        "  \"warmup_runtime_type_count_owner_only\": %ld,\n"
        "  \"failure_index_owner_only\": %llu,\n"
        "  \"failure_kind_owner_only\": %u,\n"
        "  \"failure_observed_token_owner_only\": %u,\n"
        "  \"failure_expected_token_owner_only\": %u,\n"
        "  \"failure_name_bytes_owner_only\": %u,\n"
        "  \"failure_name_is_module_owner_only\": %u,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"saved_type_identity_used\": false,\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_offset_used\": false,\n"
        "  \"external_runtime_component_used\": false\n"
        "}}\n",
        status, (unsigned long)GetCurrentProcessId(),
        (unsigned long)expected_process_id, expected_executable_sha256,
        observed_hash ? observed_hash : "",
        (unsigned long long)expected_type_count,
        (unsigned long long)completed,
        (unsigned long long)names, (unsigned long long)namespaces,
        (unsigned long long)modules, (unsigned long long)declaring,
        (unsigned long long)enum_count, (unsigned long long)value_count,
        (unsigned long long)runtime_synthetic_name_count,
        (unsigned long long)runtime_metadata_token_match_count,
        runtime_metadata_token_rid_base,
        handle_qword,
        InterlockedCompareExchange(&diagnostic_handle_samples, 0, 0),
        InterlockedCompareExchange(
            &diagnostic_handle_exact_candidates, 0, 0),
        InterlockedCompareExchange(&diagnostic_handle_max_support, 0, 0),
        InterlockedCompareExchange(&diagnostic_descriptor_readable, 0, 0),
        InterlockedCompareExchange(&diagnostic_from_handle_nonzero, 0, 0),
        InterlockedCompareExchange(
            &diagnostic_from_handle_object_readable, 0, 0),
        InterlockedCompareExchange(
            &diagnostic_warmup_descriptor_readable, 0, 0),
        InterlockedCompareExchange(&diagnostic_warmup_nonzero, 0, 0),
        InterlockedCompareExchange(
            &diagnostic_warmup_object_readable, 0, 0),
        InterlockedCompareExchange(&diagnostic_warmup_runtime_type, 0, 0),
        (unsigned long long)failure_index, runtime_failure_kind,
        runtime_failure_observed_token, runtime_failure_expected_token,
        runtime_failure_name_bytes, runtime_failure_name_is_module);
    fclose(output);
}}

static DWORD WINAPI worker(void *unused) {{
    (void)unused;
    SetThreadPriority(GetCurrentThread(), THREAD_PRIORITY_BELOW_NORMAL);
    char observed_hash[65] = {{0}}, inventory_hash[65] = {{0}};
    if (GetCurrentProcessId() != expected_process_id ||
        (uintptr_t)GetModuleHandleW(NULL) != expected_image_base ||
        !executable_identity(observed_hash) ||
        strcmp(observed_hash, expected_executable_sha256) ||
        !sha256_file(native_inventory_input, inventory_hash) ||
        strcmp(inventory_hash, expected_native_inventory_sha256)) {{
        write_status("identity-binding-rejected", observed_hash,
            0, 0, 0, 0, 0, 0, 0, 0, 0);
        return 1;
    }}
    FILE *input = _wfopen(native_inventory_input, L"rb");
    alpha_native_inventory_header native_header;
    if (!input || fread(&native_header, 1, sizeof(native_header), input)
            != sizeof(native_header) ||
        memcmp(native_header.magic, "ALPHANI1", 8) ||
        native_header.version != {_NATIVE_INVENTORY_VERSION}u ||
        native_header.type_record_bytes != sizeof(alpha_native_type_record) ||
        native_header.method_record_bytes != {_NATIVE_METHOD_RECORD.size}u ||
        native_header.reserved ||
        native_header.type_count != expected_type_count ||
        native_header.image_bytes != expected_image_bytes ||
        memcmp(native_header.executable_sha256,
            expected_executable_sha256, 64)) {{
        if (input) fclose(input);
        write_status("native-inventory-rejected", observed_hash,
            0, 0, 0, 0, 0, 0, 0, 0, 0);
        return 2;
    }}
    if (expected_type_count > SIZE_MAX / sizeof(alpha_native_type_record)) {{
        fclose(input);
        write_status("allocation-bound-rejected", observed_hash,
            0, 0, 0, 0, 0, 0, 0, 0, 0);
        return 2;
    }}
    alpha_native_type_record *types = (alpha_native_type_record *)calloc(
        (SIZE_T)expected_type_count, sizeof(*types));
    alpha_identity_record *records = (alpha_identity_record *)calloc(
        (SIZE_T)expected_type_count, sizeof(*records));
    char **names = (char **)calloc((SIZE_T)expected_type_count, sizeof(char *));
    char **namespaces = (char **)calloc(
        (SIZE_T)expected_type_count, sizeof(char *));
    if (!types || !records || !names || !namespaces ||
        fread(types, sizeof(*types), (SIZE_T)expected_type_count, input)
            != expected_type_count) {{
        fclose(input);
        free(types); free(records); free(names); free(namespaces);
        write_status("inventory-read-failed", observed_hash,
            0, 0, 0, 0, 0, 0, 0, 0, 0);
        return 3;
    }}
    fclose(input);
    runtime_types = types;
    runtime_records = records;
    runtime_names = names;
    runtime_namespaces = namespaces;
    runtime_handle_qword = 0;
    runtime_capture_index = 0;
    runtime_completed = 0;
    runtime_name_count = 0;
    runtime_namespace_count = 0;
    runtime_module_count = 0;
    runtime_declaring_count = 0;
    runtime_enum_count = 0;
    runtime_value_count = 0;
    runtime_synthetic_name_count = 0;
    runtime_metadata_token_match_count = 0;
    runtime_metadata_token_rid_base = 0;
    runtime_string_bytes = 0;
    runtime_failure_index = 0;
    runtime_failure_kind = 0;
    runtime_failure_observed_token = 0;
    runtime_failure_expected_token = 0;
    runtime_failure_name_bytes = 0;
    runtime_failure_name_is_module = 0;
    int complete = dispatch_managed_capture();
    uint32_t handle_qword = runtime_handle_qword;
    uint64_t completed = runtime_completed;
    uint64_t name_count = runtime_name_count;
    uint64_t namespace_count = runtime_namespace_count;
    uint64_t module_count = runtime_module_count;
    uint64_t declaring_count = runtime_declaring_count;
    uint64_t enum_count = runtime_enum_count;
    uint64_t value_count = runtime_value_count;
    uint64_t string_bytes = runtime_string_bytes;
    uint64_t failure_index = runtime_failure_index;
    uint64_t strings_start = sizeof(alpha_identity_header) +
        expected_type_count * sizeof(alpha_identity_record);
    uint64_t cursor = strings_start;
    if (cursor < sizeof(alpha_identity_header) ||
        cursor + string_bytes < cursor) complete = 0;
    for (uint64_t index = 0; complete && index < expected_type_count; index++) {{
        records[index].name_offset = cursor;
        cursor += records[index].name_bytes;
        records[index].namespace_offset = cursor;
        cursor += records[index].namespace_bytes;
    }}
    FILE *output = complete ? _wfopen(identity_output, L"wb") : NULL;
    if (!output) complete = 0;
    alpha_identity_header header;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHATI1", 8);
    header.version = {_IDENTITY_VERSION}u;
    header.header_bytes = sizeof(header);
    header.record_bytes = sizeof(alpha_identity_record);
    header.type_count = expected_type_count;
    header.image_base = expected_image_base;
    header.image_bytes = expected_image_bytes;
    header.string_bytes = string_bytes;
    memcpy(header.executable_sha256, expected_executable_sha256, 64);
    memcpy(header.native_inventory_sha256,
        expected_native_inventory_sha256, 64);
    memcpy(header.reflection_semantics_sha256,
        expected_reflection_semantics_sha256, 64);
    if (complete && fwrite(&header, 1, sizeof(header), output) != sizeof(header))
        complete = 0;
    if (complete && fwrite(records, sizeof(*records),
            (SIZE_T)expected_type_count, output) != expected_type_count)
        complete = 0;
    for (uint64_t index = 0; complete && index < expected_type_count; index++) {{
        if (records[index].name_bytes && fwrite(
                names[index], 1, records[index].name_bytes, output)
                != records[index].name_bytes) complete = 0;
        if (records[index].namespace_bytes && fwrite(
                namespaces[index], 1, records[index].namespace_bytes, output)
                != records[index].namespace_bytes) complete = 0;
    }}
    if (output && fclose(output)) complete = 0;
    if (complete && !write_string_io_probe()) complete = 0;
    /* A failed dispatch may still be unwinding on the game thread. The DLL
       and its buffers remain resident until that callback is quiescent. */
    if (!InterlockedCompareExchange(&callback_active, 0, 0)) {{
        for (uint64_t index = 0; index < expected_type_count; index++) {{
            free(names[index]);
            free(namespaces[index]);
        }}
        free(types); free(records); free(names); free(namespaces);
    }}
    if (!complete) _wremove(identity_output);
    else _wchmod(identity_output, 0600);
    write_status(
        complete && completed == expected_type_count ? "complete" :
            "capture-mismatch",
        observed_hash, completed, name_count, namespace_count, module_count,
        declaring_count, enum_count, value_count, handle_qword, failure_index);
    return complete && completed == expected_type_count ? 0 : 5;
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


def prepare_runtime_type_identity_inventory(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    native_inventory: Path,
    ancestry_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
    string_layout_model: Path | None = None,
) -> dict[str, Any]:
    current_process = current_runtime_process_binding()
    if current_process is None:
        raise AcquisitionError("lossless type-name capture requires current process binding; use capture-fresh-inventory")
    output_dir = _owner_directory(output_dir)
    binding = _identity_binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        native_inventory=native_inventory,
        ancestry_model=ancestry_model,
        string_layout_model=string_layout_model,
    )
    if (binding["process_id"] != current_process[0] or
        not same_executable_path(binary, current_process[2])):
        raise AcquisitionError("type identity source process differs from current binding")
    status_path = output_dir / "runtime-type-identity-status.private.json"
    inventory_path = output_dir / "runtime-type-identity.private.bin"
    model_path = output_dir / "runtime-type-identity.private.json"
    plan_path = output_dir / "runtime-type-identity-plan.private.json"
    raw_type_path = output_dir / "runtime-type-raw-observation.private.bin"
    raw_names_path = output_dir / "runtime-type-raw-names.private.bin"
    string_io_path = output_dir / "runtime-string-layout-io.private.json"
    build_dir = _owner_directory(output_dir / "build-type-identity")
    source_path = build_dir / "runtime-type-identity.c"
    injector_source_path = build_dir / "runtime-type-identity-injector.c"
    injector_path = build_dir / "alpha-runtime-type-identity-injector.exe"
    for path in (status_path, inventory_path, model_path, plan_path, raw_type_path, raw_names_path, string_io_path):
        if path.exists():
            raise AcquisitionError("type identity capture requires a new output directory")
    _private_text(
        source_path,
        attach_raw_type_names(runtime_type_identity_inventory_source(
            binding=binding,
            native_inventory_path=Path(native_inventory).expanduser().resolve(),
            output_path=inventory_path,
            status_path=status_path,
        ), binding=binding, creation_filetime=current_process[1], output_path=raw_type_path)[0],
    )
    _private_text(injector_source_path, runtime_injector_source())


    load_identity = secrets.token_hex(8)
    collector_path = build_dir / (
        "alpha-runtime-type-identity-"
        + file_identity(source_path)["sha256"][:12]
        + "-" + load_identity
        + ".dll"
    )
    selected_compiler = _compiler(compiler)
    _build(
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
        label="runtime type identity collector",
    )


    cached_windows_build(
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
        label="runtime type identity injector",
        source_path=injector_source_path,
        output_path=injector_path,
    )
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_TYPE_IDENTITY_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(Path(binary).expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "creation_filetime": current_process[1],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            "reflection_semantics": binding["semantics"],
            "behavior_plan": binding["behavior_plan"],
            "behavior_receipt": binding["behavior_receipt"],
            "class_model": binding["class_model"],
            "bootstrap_model": binding["bootstrap_model"],
            "snapshot": binding["snapshot"],
            "materializer_model": binding["materializer_model"],
            "native_inventory": binding["native_inventory"],
            "ancestry_model": binding["ancestry_model"],
            "ancestry_inventory": binding["ancestry_inventory"],
            "string_layout_model": binding["string_layout_model"],
        },
        "collector": {**file_identity(collector_path), "load_identity": load_identity},
        "injector": file_identity(injector_path),
        "status_path": str(status_path),
        "inventory_path": str(inventory_path),
        "raw_type_names_path": str(raw_type_path), "raw_names_output_path": str(raw_names_path),
        "string_layout_io_path": str(string_io_path),
        "string_layout_contract_owner_only": {key: value.hex() if isinstance(value, bytes) else value
            for key, value in binding["string_layout_contract"].items()},
        "model_path": str(model_path),
        "contract": {
            "lossless_raw_names_required": True,
            "type_count": binding["type_count"],
            "record_bytes": _IDENTITY_RECORD.size,
            "all_type_names_required": True,
            "all_modules_required": True,
            "native_name_agreement_required": True,
        },
        "operations_owner_only": binding["operations_owner_only"],
        "runtime_classes_owner_only": {
            "runtime_type": binding["runtime_type_class"],
            "string": binding["string_class"],
        },
        "embedded_type_descriptor_offset_owner_only": binding[
            "embedded_type_descriptor_offset_owner_only"
        ],
        "policy": {
            "same_process_required": True,
            "current_executable_sha256_embedded": True,
            "reflection_operations_current_runtime_derived": True,
            "runtime_type_handle_layout_live_derived": True,
            "raw_pointers_owner_only": True,
            "saved_type_identity_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_TYPE_IDENTITY_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "type_count": binding["type_count"],
        "policy": plan["policy"],
    }


def _validate_type_identity_capture(
    *,
    plan: dict[str, Any],
    status: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = Path(plan["inventory_path"])
    native_path = Path(plan["inputs"]["native_inventory"]["path"])
    raw = output_path.read_bytes()
    native = native_path.read_bytes()
    if len(raw) < _IDENTITY_HEADER.size or len(
        native
    ) < _NATIVE_INVENTORY_HEADER.size:
        raise AcquisitionError("runtime type identity output is truncated")
    header = _IDENTITY_HEADER.unpack_from(raw, 0)
    native_header = _NATIVE_INVENTORY_HEADER.unpack_from(native, 0)
    type_count = plan["contract"]["type_count"]
    records_end = _IDENTITY_HEADER.size + type_count * _IDENTITY_RECORD.size
    native_type_start = _NATIVE_INVENTORY_HEADER.size
    native_method_start = (
        native_type_start + type_count * _NATIVE_TYPE_RECORD.size
    )
    native_names_start = (
        native_method_start + native_header[6] * _NATIVE_METHOD_RECORD.size
    )
    expected_size = records_end + header[8]
    header_valid = (
        header[0] == _IDENTITY_MAGIC
        and header[1] == _IDENTITY_VERSION
        and header[2] == _IDENTITY_HEADER.size
        and header[3] == _IDENTITY_RECORD.size
        and header[4] == 0
        and header[5] == type_count
        and header[6] == plan["target"]["image_base_owner_only"]
        and header[7] == plan["target"]["image_bytes"]
        and _ascii_digest(header[9], label="output executable")
        == plan["target"]["executable_sha256"]
        and _ascii_digest(header[10], label="output native inventory")
        == plan["inputs"]["native_inventory"]["sha256"]
        and _ascii_digest(header[11], label="output semantics")
        == plan["inputs"]["reflection_semantics"]["sha256"]
        and expected_size == len(raw)
        and native_names_start <= len(native)
    )
    module_pointers: set[int] = set()
    metadata_tokens: set[int] = set()
    metadata_token_rid_base: int | None = None
    descriptor_pointers: set[int] = set()
    declaring_descriptors: list[int] = []
    names: set[tuple[int, str, str, int]] = set()
    captured_nonempty_name_count = 0
    record_relations_valid = True
    strings_valid = True
    native_nonempty_name_count = 0
    native_name_match_count = 0
    native_name_mismatch_count = 0
    protected_empty_name_count = 0
    protected_empty_name_match_count = 0
    nonempty_namespace_count = 0
    declaring_count = 0
    enum_count = 0
    value_type_count = 0
    interface_count = 0


    native_available = max(
        0, (len(native) - native_type_start) // _NATIVE_TYPE_RECORD.size
    )
    native_rows = _NATIVE_TYPE_RECORD.iter_unpack(
        memoryview(native)[
            native_type_start :
            native_type_start
            + min(type_count, native_available) * _NATIVE_TYPE_RECORD.size
        ]
    )
    identity_available = max(0, (len(raw) - _IDENTITY_HEADER.size) // _IDENTITY_RECORD.size)
    identity_rows = _IDENTITY_RECORD.iter_unpack(
        memoryview(raw)[
            _IDENTITY_HEADER.size :
            _IDENTITY_HEADER.size
            + min(type_count, identity_available) * _IDENTITY_RECORD.size
        ]
    )
    index = -1
    for index, (native_row, record) in enumerate(
        zip(native_rows, identity_rows)
    ):
        (
            definition_index,
            flags,
            descriptor,
            class_pointer,
            module_pointer,
            declaring_descriptor,
            type_object,
            attributes,
            name_bytes,
            namespace_bytes,
            metadata_token,
            name_offset,
            namespace_offset,
        ) = record
        candidate_rid_base = (metadata_token & 0x00FFFFFF) - index
        if index == 0:
            metadata_token_rid_base = candidate_rid_base
        metadata_token_relation_valid = (
            metadata_token_rid_base in (0, 1)
            and candidate_rid_base == metadata_token_rid_base
        )
        expected_descriptor = (
            native_row[4]
            + plan["embedded_type_descriptor_offset_owner_only"]
        )
        if (
            definition_index != index
            or flags & ~0x7F
            or not flags & 1
            or not flags & 2
            or (bool(namespace_bytes) != bool(flags & 4))
            or not flags & 8
            or bool(declaring_descriptor) != bool(flags & 16)
            or descriptor != expected_descriptor
            or class_pointer != native_row[4]
            or not module_pointer
            or not type_object
            or metadata_token >> 24 != 0x02
            or not metadata_token_relation_valid
            or metadata_token in metadata_tokens
            or name_offset < records_end
            or name_offset + name_bytes > len(raw)
            or namespace_offset != name_offset + name_bytes
            or namespace_offset + namespace_bytes > len(raw)
        ):
            record_relations_valid = False
            break
        try:
            name = raw[name_offset : name_offset + name_bytes].decode("utf-8")
            namespace = raw[
                namespace_offset : namespace_offset + namespace_bytes
            ].decode("utf-8")
        except UnicodeDecodeError:
            strings_valid = False
            break
        if (
            "\x00" in name
            or "\x00" in namespace
            or any(ord(character) < 0x20 for character in name + namespace)
        ):
            strings_valid = False
            break
        native_name = native[
            native_row[10] : native_row[10] + native_row[1]
        ].decode("utf-8")
        if native_name:
            native_nonempty_name_count += 1
            if native_name == name:
                native_name_match_count += 1
            else:
                native_name_mismatch_count += 1
        else:
            protected_empty_name_count += 1
            if name == f"EmptyType_{metadata_token:X}":
                protected_empty_name_match_count += 1
        if name:
            captured_nonempty_name_count += 1
        module_pointers.add(module_pointer)
        metadata_tokens.add(metadata_token)
        descriptor_pointers.add(descriptor)
        if declaring_descriptor:
            declaring_descriptors.append(declaring_descriptor)
            declaring_count += 1
        if namespace:
            nonempty_namespace_count += 1
        if flags & 32:
            enum_count += 1
        if flags & 64:
            value_type_count += 1
        if attributes & 0x20:
            interface_count += 1
        names.add((module_pointer, namespace, name, declaring_descriptor))
    else:
        if index != type_count - 1:


            _NATIVE_TYPE_RECORD.unpack_from(
                native, native_type_start + (index + 1) * _NATIVE_TYPE_RECORD.size
            )
            _IDENTITY_RECORD.unpack_from(
                raw, _IDENTITY_HEADER.size + (index + 1) * _IDENTITY_RECORD.size
            )
    known_declaring_count = sum(
        descriptor in descriptor_pointers
        for descriptor in declaring_descriptors
    )
    counts = {
        "type_count": type_count,
        "nonempty_name_count": captured_nonempty_name_count,
        "unique_type_identity_count": len(names),
        "nonempty_namespace_count": nonempty_namespace_count,
        "module_group_count": len(module_pointers),
        "declaring_type_count": declaring_count,
        "known_declaring_type_count": known_declaring_count,
        "enum_count": enum_count,
        "value_type_count": value_type_count,
        "interface_count": interface_count,
        "native_nonempty_name_count": native_nonempty_name_count,
        "native_name_match_count": native_name_match_count,
        "native_name_mismatch_count": native_name_mismatch_count,
        "metadata_token_count": len(metadata_tokens),
        "metadata_token_rid_base": metadata_token_rid_base,
        "protected_empty_name_count": protected_empty_name_count,
        "protected_empty_name_match_count": protected_empty_name_match_count,
    }
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_TYPE_IDENTITY_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "same_process": status.get("process_id")
        == plan["target"]["process_id"]
        and status.get("expected_process_id")
        == plan["target"]["process_id"],
        "executable_identity_bound": status.get(
            "observed_executable_sha256"
        )
        == plan["target"]["executable_sha256"],
        "binary_header_bound": header_valid,
        "all_types_captured": status.get("completed_type_count")
        == type_count,
        "record_relations_valid": record_relations_valid,
        "utf8_strings_valid": strings_valid,
        "all_type_names_nonempty": captured_nonempty_name_count == type_count,
        "native_names_exact": native_name_match_count
        == native_nonempty_name_count
        and native_name_mismatch_count == 0,


        "metadata_token_domain_complete": len(metadata_tokens) == type_count,
        "runtime_metadata_tokens_cross_checked":
        status.get("runtime_metadata_token_match_count", 0) == type_count,
        "metadata_token_rid_base_current_runtime_derived":
        metadata_token_rid_base in (0, 1)
        and status.get("runtime_metadata_token_rid_base")
        == metadata_token_rid_base,
        "protected_empty_names_materialized":
        protected_empty_name_match_count == protected_empty_name_count
        and status.get("synthetic_empty_name_count")
        == protected_empty_name_count,
        "module_domain_substantial": 10 <= len(module_pointers) < type_count,
        "declaring_references_known": known_declaring_count == declaring_count,
        "enum_subset_value_type": enum_count <= value_type_count,
        "type_shape_domains_nonempty": enum_count > 0
        and value_type_count > 0
        and interface_count > 0,
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        )
        is True,
        "saved_type_identity_absent": status.get(
            "saved_type_identity_used"
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


def capture_runtime_type_identity_inventory(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    native_inventory: Path,
    ancestry_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 300.0,
    string_layout_model: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_type_identity_inventory(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        native_inventory=native_inventory,
        ancestry_model=ancestry_model,
        output_dir=output_dir,
        compiler=compiler,
        string_layout_model=string_layout_model,
    )
    plan = read_json(output_dir / "runtime-type-identity-plan.private.json")
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError("runtime type identity Wine is unavailable")
    with RuntimeProcessLifetimeGuard(identity=plan["target"], wine=wine, wineprefix=wineprefix,
            compiler=compiler, build_dir=output_dir / "build-process-lifetime") as lifetime:
        return _capture_prepared_type_identity(plan=plan, output_dir=output_dir, wine=wine,
                                              wineprefix=wineprefix, timeout=timeout, lifetime=lifetime)


def _capture_prepared_type_identity(*, plan, output_dir, wine, wineprefix, timeout, lifetime):
    lifetime.assert_alive()
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
            "runtime type identity injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-type-identity-injector.private.log",
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
        detail = injected.stderr.strip().splitlines()
        raise AcquisitionError(
            f"runtime type identity injection failed ({injected.returncode})"
            + (f": {detail[-1]}" if detail else "")
        )
    lifetime.assert_alive()
    status_path = Path(plan["status_path"])
    deadline = time.monotonic() + max(1.0, timeout)
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        lifetime.assert_alive()
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
        raise AcquisitionError("runtime type identity capture timed out")
    _seal_runtime_output(status_path)
    inventory_path = Path(plan["inventory_path"])
    if inventory_path.is_file():
        _seal_runtime_output(inventory_path)
    if not inventory_path.is_file():
        raise AcquisitionError(
            "runtime type identity output is unavailable "
            f"(status={status.get('status')})"
        )
    lifetime.assert_alive()
    result = _finalize_type_identity(plan=plan, status=status)
    lifetime.assert_alive()
    return result


def _finalize_type_identity(*, plan, status):
    if plan.get("contract", {}).get("lossless_raw_names_required") is not True:
        raise AcquisitionError("type identity plan has no lossless raw-name contract")
    if not isinstance(plan.get("string_layout_contract_owner_only"), dict) or not plan.get("string_layout_io_path"):
        raise AcquisitionError("type identity plan has no String native I/O contract")
    def verify_inputs():
        for record in plan["inputs"].values():
            path = _owner_file(Path(record["path"]), label="capture input")
            if file_identity(path) != record:
                raise AcquisitionError("type identity input changed during capture")
    verify_inputs()
    inventory_path = Path(plan["inventory_path"])
    _seal_runtime_output(Path(plan["raw_type_names_path"]))
    counts, checks = _validate_type_identity_capture(
        plan=plan,
        status=status,
    )
    validated = all(checks.values())
    raw_names = None
    string_io = None
    if validated:
        raw_names = finalize_raw_type_names(plan=plan, output_path=Path(plan["raw_names_output_path"]))
        checks.update(raw_names["checks"])
        counts.update({key: value for key, value in raw_names["counts"].items()
                       if key not in ("type", "type_namespace")})
        replay_inputs = {role: plan["inputs"][role] for role in RAW_TYPE_ROLES}
        replay_inputs.update(type_identity_inventory=file_identity(inventory_path),
                             raw_type_observation=file_identity(Path(plan["raw_type_names_path"])))
        names, _ = load_raw_type_names(model=raw_names, inventory_path=Path(plan["raw_names_output_path"]),
            expected_identity=dict(plan["target"], image_base=plan["target"]["image_base_owner_only"]),
            expected_inputs=replay_inputs, expected_count=plan["contract"]["type_count"])
        io_path = Path(plan["string_layout_io_path"])
        if not _seal_runtime_output(io_path):
            raise AcquisitionError("type identity String native I/O output is absent")
        io_identity = file_identity(io_path)
        string_io = validate_string_layout_io(observation=read_json(io_path), names=names,
            expected_process_id=plan["target"]["process_id"], contract=plan["string_layout_contract_owner_only"])
        if file_identity(io_path) != io_identity:
            raise AcquisitionError("type identity String I/O output changed during replay")
        string_io["inventory"] = io_identity
        string_io["all_collectors_use_derived_string_layout"] = False
        checks.update(string_io["checks"])
    verify_inputs()
    model = {
        "schema": RUNTIME_TYPE_IDENTITY_SCHEMA,
        "status": "runtime-validated" if validated else "rejected",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"]
        },
        "inputs": plan["inputs"],
        "identity_inventory": file_identity(inventory_path),
        "counts": counts,
        "checks": checks,
        "owner_only": True,
        "raw_names": raw_names, "string_layout_io": string_io, "metadata_complete": False,
    }
    _private_json(Path(plan["model_path"]), model)
    return {
        "schema": RUNTIME_TYPE_IDENTITY_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "raw_pointers_exposed": False,
    }


import hashlib
import tempfile
from pathlib import Path
from typing import Any, Callable

from alpha.p12 import capture_runtime_snapshot, _reachable_heap_limit_bytes
from alpha.p16 import inspect_reflection_semantics
from alpha.p13 import RuntimeCaptureSession, RuntimeProcessProbe
from alpha.p15 import inspect_runtime_class_model
from alpha.p16 import capture_runtime_native_helper_validation, inspect_runtime_native_helpers
from alpha.c07 import capture_runtime_reflection_behavior
from alpha.p18 import merge_runtime_reflection_semantics
from alpha.p16 import inspect_runtime_type_materializer
from alpha.p17 import capture_runtime_type_materializer_validation


def _implementation_digest() -> str:


    global _IMPLEMENTATION_DIGEST_CACHE
    try:
        cached = _IMPLEMENTATION_DIGEST_CACHE
    except NameError:
        cached = None
    parent = Path(__file__).parent
    names: list[str] = []
    fingerprints: list[tuple[int, int, int, int, int]] = []
    try:
        with os.scandir(parent) as entries:
            measured = sorted(
                (entry.name, entry.stat())
                for entry in entries
                if entry.name.endswith(".py")
            )
        for name, status in measured:
            names.append(name)
            fingerprints.append((
                status.st_dev, status.st_ino, status.st_size,
                status.st_mtime_ns, status.st_ctime_ns,
            ))
    except OSError:

        digest = hashlib.sha256()
        for path in sorted(parent.glob("*.py")):
            digest.update(path.name.encode() + b"\0" + path.read_bytes() + b"\0")
        return digest.hexdigest()
    key = tuple(fingerprints)
    if cached is not None and cached[0] == key:
        return cached[1]
    digest = hashlib.sha256()
    for name in names:
        digest.update(name.encode() + b"\0" + (parent / name).read_bytes() + b"\0")
    result = digest.hexdigest()
    _IMPLEMENTATION_DIGEST_CACHE = (key, result)
    return result


_IMPLEMENTATION_DIGEST_CACHE: tuple[tuple[tuple[int, int, int, int, int], ...], str] | None = None


def capture_fresh_runtime_bootstrap(
    *, binary: Path, output_dir: Path, wine: Path, wineprefix: Path,
    compiler: Path | None = None, timeout: float = 1800.0, resume: bool = False,
    repair_resume: bool = False,
    carry_forward: bool = False,
    allow_process_rebind: bool = False,
    salvage_restart: bool = False,
    partial_proto_without_field_encrypt: bool = False,
    progress: Callable[[str], None] | None = None,
    include_inventory: bool = False,
    proto_output_dir: Path | None = None,
    metadata_output_dir: Path | None = None,
    metadata_reconstruct: bool = True,
    metadata_domain_observations: tuple[Path, ...] = (),
    reachable_heap_limit_mib: int = 0,
) -> dict[str, Any]:
    _reachable_heap_limit_bytes(reachable_heap_limit_mib)


    binary = binary.expanduser()


    def current_implementation():
        return hashlib.sha256(
            (
                f"{_implementation_digest()}\0"
                f"reachable_heap_limit_mib={reachable_heap_limit_mib}"
            ).encode()
        ).hexdigest()
    implementation = current_implementation()


    with tempfile.TemporaryDirectory(prefix="alpha-process-probe-") as temporary:
        probe = RuntimeProcessProbe(binary=binary, wine=wine, wineprefix=wineprefix,
                                    compiler=compiler, build_dir=Path(temporary).resolve())
        with RuntimeCaptureSession(output_dir, probe=probe, implementation=implementation,
                                   implementation_probe=current_implementation,
                                   resume=resume, repair_resume=repair_resume,
                                   carry_forward=carry_forward,
                                   allow_process_rebind=allow_process_rebind,
                                   salvage_restart=salvage_restart) as session:
            session.set_stage_plan(
                "acquisition",
                acquisition_stage_plan(
                    include_inventory=include_inventory,
                    proto_only=proto_output_dir is not None,
                    include_metadata=metadata_output_dir is not None,
                ),
            )
            root = session.root
            memory = root / "memory"
            snapshot = memory / "runtime-memory.private.bin"
            bootstrap = memory / "memory-reflection-bootstrap.private.json"
            classes = root / "classes/runtime-class-model.private.json"
            helpers = root / "helpers/runtime-native-helpers.private.json"
            validated_helpers = root / "helpers-live/runtime-native-helpers.validated.private.json"
            materializer = root / "materializer/runtime-type-materializer.private.json"
            validated_materializer = root / "materializer-live/runtime-type-materializer.validated.private.json"
            semantics = root / "semantics/runtime-reflection-semantics.private.json"
            live = dict(binary=binary, wine=wine, wineprefix=wineprefix,
                        compiler=compiler, timeout=timeout)

            def run(name, callback, **options):
                if progress:
                    progress(name)
                session.register_planned_stage("acquisition", name)
                return session.run(name, callback, **options)

            run("memory", lambda out: capture_runtime_snapshot(
                game_dir=binary.parent, executable=binary, output_dir=out,
                wine=wine, wineprefix=wineprefix, compiler=compiler,
                timeout=None if reachable_heap_limit_mib == 0 else timeout,
                reachable_heap_limit_mib=reachable_heap_limit_mib,
                process_check=session.assert_current),
                accepted_statuses=("complete", "captured-unattested"),
                validate=lambda result: bool(result.get("capture_checks"))
                and all(value is True for value in result["capture_checks"].values()))
            run("classes", lambda out: inspect_runtime_class_model(
                snapshot=snapshot, bootstrap_model=bootstrap,
                owner_roots=memory / "runtime-owner-roots.private.json",
                output=out / classes.name), dependencies=("memory",))
            run("helpers", lambda out: inspect_runtime_native_helpers(
                binary=binary, bootstrap_model=bootstrap, class_model=classes,
                output=out / helpers.name), dependencies=("memory", "classes"))
            run("helpers-live", lambda out: capture_runtime_native_helper_validation(
                **live, bootstrap_model=bootstrap, class_model=classes,
                native_helper_model=helpers, output_dir=out),
                dependencies=("memory", "classes", "helpers"))
            run("materializer", lambda out: inspect_runtime_type_materializer(
                binary=binary, snapshot=snapshot, bootstrap_model=bootstrap,
                class_model=classes, output=out / materializer.name),
                dependencies=("memory", "classes"))
            run("materializer-live", lambda out: capture_runtime_type_materializer_validation(
                **live, bootstrap_model=bootstrap, class_model=classes,
                materializer_model=materializer, native_helper_model=validated_helpers,
                output_dir=out), dependencies=("memory", "classes", "helpers-live", "materializer"))
            run("semantics", lambda out: inspect_reflection_semantics(
                binary=binary, snapshot=snapshot, bootstrap_model=bootstrap,
                class_model=classes, output=out / semantics.name),
                dependencies=("memory", "classes"), accepted_statuses=("partially-resolved",))
            run("semantics-live", lambda out: capture_runtime_reflection_behavior(
                **live, snapshot=snapshot, bootstrap_model=bootstrap, class_model=classes,
                semantics_model=semantics, materializer_model=validated_materializer,
                native_helper_model=validated_helpers, output_dir=out),
                dependencies=("memory", "classes", "semantics", "materializer-live", "helpers-live"))
            result = run("semantics-complete", lambda out: merge_runtime_reflection_semantics(
                semantics_model=semantics,
                behavior_plan=root / "semantics-live/runtime-reflection-behavior-plan.private.json",
                behavior_receipt=root / "semantics-live/runtime-reflection-behavior-receipt.private.json",
                output=out / "runtime-reflection-semantics.private.json"),
                dependencies=("semantics", "semantics-live"),
                accepted_statuses=("resolved",))
            if (
                include_inventory
                or proto_output_dir is not None
                or metadata_output_dir is not None
            ):
                from alpha.p40 import capture_session_inventories
                capture_session_inventories(
                    session=session,
                    live=live,
                    progress=progress,
                    proto_only=(
                        proto_output_dir is not None
                        and metadata_output_dir is None
                        and not include_inventory
                    ),
                )
            proto_result: dict[str, Any] | None = None
            if proto_output_dir is not None:
                from alpha.p44 import capture_proto_stages
                proto_result = capture_proto_stages(
                    session=session, live=live,
                    output_dir=proto_output_dir, progress=progress,
                    partial_proto_without_field_encrypt=partial_proto_without_field_encrypt,
                )
            if metadata_output_dir is not None:
                from alpha.p53 import capture_metadata_stages
                result = capture_metadata_stages(
                    session=session,
                    live=live,
                    output_dir=metadata_output_dir,
                    progress=progress,
                    reconstruct=metadata_reconstruct,
                    domain_observations=tuple(metadata_domain_observations),
                )
                if proto_result is not None:
                    result = {
                        "schema": "alpha.combined-proto-metadata-output/v1",
                        "status": "proto-and-metadata-artifacts-complete",
                        "proto_output": proto_result,
                        "metadata_output": result,
                        "metadata_complete": False,
                        "target": {
                            "executable_sha256": session.journal["identity"][
                                "executable_sha256"
                            ],
                        },
                    }
                session.finalize(terminal_stage="metadata-publish", published=True)
                return result
            if proto_result is not None:
                result = proto_result
                session.finalize(terminal_stage="proto-publish", published=True)
                return result
            session.assert_current()
            return {"schema": "alpha.fresh-runtime-bootstrap/v1",
                    "status": "inventory-captured" if include_inventory else "bootstrap-complete",
                    "metadata_complete": False, "published": False,
                    "official_runtime_attested": False,
                    "stage_count": len(session.journal["stages"]),
                    "executable_sha256": session.journal["identity"]["executable_sha256"],
                    "session": str(root / "session.private.json"), "reflection": result}
