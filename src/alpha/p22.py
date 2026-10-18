from alpha.h02 import windows_run as _host_run

import json
import os
import stat
import struct
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import (
    AcquisitionError,
    owner_only_path_bits,
    owner_uid,
    same_executable_path,
)
from alpha.c01 import current_runtime_process_binding
from alpha.c02 import attach_raw_parameter_name_capture, finalize_raw_method_parameter_names
from alpha.p16 import (
    METHOD_NAME_DECODE_OPERATION_CODES,
    REFLECTION_SEMANTICS_SCHEMA,
)
from alpha.p18 import RUNTIME_METHOD_NAME_HEADER, RUNTIME_METHOD_NAME_MAGIC, RUNTIME_METHOD_NAME_OBSERVATION_SCHEMA, RUNTIME_METHOD_NAME_RECORD, RUNTIME_METHOD_NAME_VERSION
from alpha.p13 import derive_concrete_method_operations
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA, _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json


RUNTIME_METHOD_DETAIL_PLAN_SCHEMA = (
    "alpha.runtime-method-detail-inventory-plan/v1"
)
RUNTIME_METHOD_DETAIL_STATUS_SCHEMA = (
    "alpha.runtime-method-detail-inventory-status/v1"
)
RUNTIME_METHOD_DETAIL_SCHEMA = "alpha.runtime-method-detail-inventory/v1"
RUNTIME_METHOD_DETAIL_MAGIC = b"ALPHADM1"
RUNTIME_METHOD_DETAIL_VERSION = 1
RUNTIME_METHOD_DETAIL_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQ64s64s64s64s"
)
RUNTIME_METHOD_DETAIL_METHOD = struct.Struct("<IIQQQIIIIIIQQ")
RUNTIME_METHOD_DETAIL_PARAMETER = struct.Struct("<IIQIIIIQ")

METHOD_DETAIL_CONSTRUCTOR = 1 << 0
PARAMETER_DETAIL_IN = 1 << 0
PARAMETER_DETAIL_OUT = 1 << 1
PARAMETER_DETAIL_OPTIONAL = 1 << 2

_REQUIRED_OPERATIONS = (
    "method.from_handle",
    "method.parameters",
    "method.return_type",
    "method.attributes",
    "member.metadata_token",
    "parameter.name",
    "parameter.type",
    "parameter.is_in",
    "parameter.is_out",
    "parameter.is_optional",
)


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime method detail {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime method detail {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime method detail {label} digest is invalid"
        )
    return value


def _binding(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    native_inventory: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    method_name_receipt: Path,
    method_name_observation: Path,
    runtime_inventory_dispatch: Path | None,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    identity = file_identity(binary)
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantic model"
    )
    native_path = _owner_file(native_inventory, label="native inventory")
    type_model_path = _owner_file(
        type_identity_model, label="type identity model"
    )
    type_inventory_path = _owner_file(
        type_identity_inventory, label="type identity inventory"
    )
    method_receipt_path = _owner_file(
        method_name_receipt, label="method-name receipt"
    )
    method_names_path = _owner_file(
        method_name_observation, label="method-name observation"
    )
    semantics = read_json(semantics_path)
    type_model = read_json(type_model_path)
    method_receipt_model = read_json(method_receipt_path)
    if (
        not isinstance(semantics, dict)
        or semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary", {}).get("sha256") != identity["sha256"]
        or semantics.get("checks", {}).get("all_operations_resolved")
        is not True
        or semantics.get("behavior_evidence", {}).get(
            "fresh_runtime_observation"
        )
        is not True
    ):
        raise AcquisitionError(
            "runtime method detail reflection binding is stale"
        )
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
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
            "runtime method detail operation binding is incomplete"
        )
    arity_offset = semantics.get("method_parameter_count", {}).get(
        "selected_byte_offset"
    )
    parameter_flag_evidence = semantics.get("parameter_flag_evidence")
    parameter_attribute_offset = (
        parameter_flag_evidence.get("attribute_byte_offset")
        if isinstance(parameter_flag_evidence, dict)
        else None
    )
    parameter_masks = (
        parameter_flag_evidence.get("semantic_masks")
        if isinstance(parameter_flag_evidence, dict)
        else None
    )
    parameter_set_counts = (
        parameter_flag_evidence.get("set_counts")
        if isinstance(parameter_flag_evidence, dict)
        else None
    )
    parameter_clear_counts = (
        parameter_flag_evidence.get("clear_counts")
        if isinstance(parameter_flag_evidence, dict)
        else None
    )
    if not isinstance(arity_offset, int) or not 0 <= arity_offset < 256:
        raise AcquisitionError(
            "runtime method detail arity layout is unavailable"
        )
    if (
        not isinstance(parameter_attribute_offset, int)
        or not 16 <= parameter_attribute_offset < 256
        or parameter_masks
        != {
            "parameter.is_in": 1,
            "parameter.is_optional": 16,
            "parameter.is_out": 2,
        }
        or not isinstance(parameter_set_counts, dict)
        or not isinstance(parameter_clear_counts, dict)
        or type(parameter_flag_evidence.get("object_reference_count")) is not int
        or parameter_flag_evidence["object_reference_count"] < 8
        or any(
            type(parameter_set_counts.get(key)) is not int
            or parameter_set_counts[key] < 0
            or type(parameter_clear_counts.get(key)) is not int
            or parameter_clear_counts[key] < 0
            or parameter_set_counts[key] + parameter_clear_counts[key]
            != parameter_flag_evidence["object_reference_count"]
            for key in (
                "parameter.is_in",
                "parameter.is_out",
                "parameter.is_optional",
            )
        )
    ):
        raise AcquisitionError(
            "runtime method detail parameter flag layout is unavailable"
        )
    if (
        not isinstance(type_model, dict)
        or type_model.get("schema") != RUNTIME_TYPE_IDENTITY_SCHEMA
        or type_model.get("status") != "runtime-validated"
        or type_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or not all(type_model.get("checks", {}).values())
        or type_model.get("identity_inventory", {}).get("sha256")
        != file_identity(type_inventory_path)["sha256"]
    ):
        raise AcquisitionError(
            "runtime method detail type identity binding is stale"
        )
    type_plan_path = _owner_file(
        type_model_path.parent / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    type_status_path = _owner_file(
        type_model_path.parent / "runtime-type-identity-status.private.json",
        label="type identity status",
    )
    type_plan = read_json(type_plan_path)
    type_status = read_json(type_status_path)
    process_id = type_plan.get("target", {}).get("process_id")
    image_base = type_plan.get("target", {}).get("image_base_owner_only")
    image_bytes = type_plan.get("target", {}).get("image_bytes")
    descriptor_offset = type_plan.get(
        "embedded_type_descriptor_offset_owner_only"
    )
    classes = type_plan.get("runtime_classes_owner_only", {})
    handle_qword = type_status.get(
        "runtime_type_handle_qword_owner_only"
    )
    type_token_rid_base = type_model.get("counts", {}).get(
        "metadata_token_rid_base"
    )
    if (
        type_plan.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or type_status.get("status") != "complete"
        or type_status.get("process_id") != process_id
        or type_status.get("observed_executable_sha256")
        != identity["sha256"]
        or not isinstance(process_id, int)
        or process_id <= 0
        or not isinstance(image_base, int)
        or image_base <= 0
        or not isinstance(image_bytes, int)
        or image_bytes <= 0
        or not isinstance(descriptor_offset, int)
        or descriptor_offset <= 0
        or not isinstance(handle_qword, int)
        or not 2 <= handle_qword < 16
        or type_token_rid_base not in (0, 1)
        or type_status.get("runtime_metadata_token_rid_base")
        != type_token_rid_base
        or not isinstance(classes.get("runtime_type"), int)
        or not classes["runtime_type"]
        or not isinstance(classes.get("string"), int)
        or not classes["string"]
    ):
        raise AcquisitionError(
            "runtime method detail live type binding is invalid"
        )
    behavior_plan_record = type_model.get("inputs", {}).get("behavior_plan")
    if not isinstance(behavior_plan_record, dict):
        raise AcquisitionError(
            "runtime method detail behavior plan is absent"
        )
    behavior_plan_path = _owner_file(
        Path(behavior_plan_record["path"]), label="behavior plan"
    )
    behavior_plan = read_json(behavior_plan_path)
    class_record = behavior_plan.get("inputs", {}).get("classes")
    if not isinstance(class_record, dict):
        raise AcquisitionError(
            "runtime method detail class model is absent"
        )
    class_model_path = _owner_file(
        Path(class_record["path"]), label="class model"
    )
    class_model = read_json(class_model_path)
    snapshot_record = type_plan.get("inputs", {}).get("snapshot")
    if not isinstance(snapshot_record, dict):
        raise AcquisitionError(
            "runtime method detail current snapshot binding is absent"
        )
    snapshot_path = _owner_file(
        Path(snapshot_record["path"]), label="memory snapshot"
    )
    if file_identity(snapshot_path) != snapshot_record:
        raise AcquisitionError(
            "runtime method detail current snapshot binding is stale"
        )
    concrete_model = derive_concrete_method_operations(
        semantics=semantics,
        class_model=class_model,
        snapshot_path=snapshot_path,
        arity_offset=arity_offset,
        expected_executable_sha256=identity["sha256"],
        binary=binary,
    )
    concrete_operations = {
        key: concrete_model["operations"].get(key)
        for key in (
            "constructor.parameters",
            "constructor.attributes",
            "constructor.impl_attributes",
            "method.impl_attributes",
        )
    }
    if any(
        not isinstance(operation, dict)
        or operation.get("semantic_identity_resolved") is not True
        or not isinstance(operation.get("method_pointer"), int)
        or operation["method_pointer"] <= 0
        or not isinstance(operation.get("metadata_pointer"), int)
        or operation["metadata_pointer"] <= 0
        for operation in concrete_operations.values()
    ):
        raise AcquisitionError(
            "runtime method/constructor concrete operations are unavailable"
        )
    class_pointers = {
        row.get("runtime_owner"): row.get("class_pointer")
        for row in class_model.get("classes", [])
        if isinstance(row, dict)
    }
    method_class = class_pointers.get("System.Reflection.MonoMethod")
    constructor_class = class_pointers.get("System.Reflection.MonoCMethod")
    parameter_class = class_pointers.get(
        "System.Reflection.MonoParameterInfo"
    )
    if (
        not isinstance(method_class, int)
        or not method_class
        or not isinstance(constructor_class, int)
        or not constructor_class
        or not isinstance(parameter_class, int)
        or not parameter_class
    ):
        raise AcquisitionError(
            "runtime method detail required classes are unavailable"
        )
    native_raw = native_path.read_bytes()
    type_raw = type_inventory_path.read_bytes()
    method_name_raw = method_names_path.read_bytes()
    if (
        len(native_raw) < _NATIVE_INVENTORY_HEADER.size
        or len(type_raw) < _IDENTITY_HEADER.size
        or len(method_name_raw) < RUNTIME_METHOD_NAME_HEADER.size
    ):
        raise AcquisitionError("runtime method detail input is truncated")
    native_header = _NATIVE_INVENTORY_HEADER.unpack_from(native_raw)
    type_header = _IDENTITY_HEADER.unpack_from(type_raw)
    name_header = RUNTIME_METHOD_NAME_HEADER.unpack_from(method_name_raw)
    type_count = native_header[5]
    method_count = native_header[6]
    native_records_end = (
        _NATIVE_INVENTORY_HEADER.size
        + type_count * _NATIVE_TYPE_RECORD.size
        + method_count * _NATIVE_METHOD_RECORD.size
    )
    if (
        native_header[0] != _NATIVE_INVENTORY_MAGIC
        or native_header[1] != _NATIVE_INVENTORY_VERSION
        or native_header[2] != _NATIVE_TYPE_RECORD.size
        or native_header[3] != _NATIVE_METHOD_RECORD.size
        or native_header[4]
        or native_header[7] != image_bytes
        or _digest(native_header[8], label="native executable")
        != identity["sha256"]
        or native_records_end > len(native_raw)
        or type_header[0] != _IDENTITY_MAGIC
        or type_header[1] != _IDENTITY_VERSION
        or type_header[2] != _IDENTITY_HEADER.size
        or type_header[3] != _IDENTITY_RECORD.size
        or type_header[5] != type_count
        or type_header[6] != image_base
        or type_header[7] != image_bytes
        or _digest(type_header[9], label="type executable")
        != identity["sha256"]
        or name_header[0] != RUNTIME_METHOD_NAME_MAGIC
        or name_header[1] != RUNTIME_METHOD_NAME_VERSION
        or name_header[2] != RUNTIME_METHOD_NAME_HEADER.size
        or name_header[3] != RUNTIME_METHOD_NAME_RECORD.size
        or name_header[4]
        or name_header[5] != method_count
        or name_header[14]
        not in METHOD_NAME_DECODE_OPERATION_CODES.values()
        or name_header[15]
        or not name_header[16]
        or not name_header[17]
        or _digest(name_header[9], label="method-name executable")
        != identity["sha256"]
        or _digest(name_header[10], label="method-name native inventory")
        != file_identity(native_path)["sha256"]
    ):
        raise AcquisitionError(
            "runtime method detail input binding is invalid"
        )
    if (
        not isinstance(method_receipt_model, dict)
        or method_receipt_model.get("schema")
        != RUNTIME_METHOD_NAME_OBSERVATION_SCHEMA
        or method_receipt_model.get("status") != "validated"
        or method_receipt_model.get("target", {}).get(
            "executable_sha256"
        )
        != identity["sha256"]
        or not all(method_receipt_model.get("checks", {}).values())
        or method_receipt_model.get("observation", {})
        .get("identity", {})
        .get("sha256")
        != file_identity(method_names_path)["sha256"]
        or method_receipt_model.get("observation", {}).get("method_count")
        != method_count
        or type(
            method_receipt_model.get("observation", {}).get(
                "decode_operation"
            )
        )
        is not str
        or method_receipt_model.get("observation", {}).get(
            "decode_operation"
        ) not in METHOD_NAME_DECODE_OPERATION_CODES
        or METHOD_NAME_DECODE_OPERATION_CODES[
            method_receipt_model.get("observation", {}).get(
                "decode_operation"
            )
        ]
        != name_header[14]
        or type(
            method_receipt_model.get("observation", {}).get("decode_key")
        )
        is not int
        or method_receipt_model.get("observation", {}).get("decode_key")
        != name_header[17]
    ):
        raise AcquisitionError(
            "runtime method detail method-name binding is stale"
        )
    return {
        "binary": identity,
        "semantics": file_identity(semantics_path),
        "native_inventory": file_identity(native_path),
        "type_identity_model": file_identity(type_model_path),
        "type_identity_inventory": file_identity(type_inventory_path),
        "type_identity_plan": file_identity(type_plan_path),
        "type_identity_status": file_identity(type_status_path),
        "method_name_receipt": file_identity(method_receipt_path),
        "method_name_observation": file_identity(method_names_path),
        "concrete_semantics_evidence": concrete_model["evidence"],
        "snapshot": file_identity(snapshot_path),
        "class_model": file_identity(class_model_path),
        "process_id": process_id,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "type_count": type_count,
        "method_count": method_count,
        "descriptor_offset": descriptor_offset,
        "handle_qword": handle_qword,
        "type_token_rid_base": type_token_rid_base,
        "runtime_type_class": classes["runtime_type"],
        "string_class": classes["string"],
        "method_class": method_class,
        "constructor_class": constructor_class,
        "parameter_class": parameter_class,
        "arity_offset": arity_offset,
        "parameter_attribute_offset": parameter_attribute_offset,
        "operations": {
            key: {
                "pointer": operations[key]["method_pointer"],
                "metadata": operations[key]["metadata_pointer"],
            }
            for key in _REQUIRED_OPERATIONS
        },
        "concrete_operations": {
            key: {
                "pointer": operation["method_pointer"],
                "metadata": operation["metadata_pointer"],
            }
            for key, operation in concrete_operations.items()
        },
    }


_COLLECTOR_TEMPLATE = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <io.h>
#include <fcntl.h>
#include <sys/stat.h>

#define ALPHA_MAX_TEXT 16384u
#define ALPHA_PARAMETER_LAYOUT_BYTES 128u
#define ALPHA_PARAMETER_CAPTURE_BYTES 56u
#define ALPHA_CAPTURE_BATCH 64u
#define ALPHA_SAMPLE_METHODS 65536u

typedef struct alpha_native_inventory_header {
    char magic[8];
    uint32_t version, type_record_bytes, method_record_bytes, reserved;
    uint64_t type_count, method_count, image_bytes;
    char executable_sha256[64], materializer_model_sha256[64];
    uint32_t layout[8];
} alpha_native_inventory_header;

typedef struct alpha_native_type_record {
    uint32_t definition_index, name_bytes;
    uint64_t type_flags, descriptor_rva, class_pointer, parent_pointer;
    uint64_t declaring_pointer;
    uint32_t method_count, reserved;
    uint64_t method_start, name_offset;
} alpha_native_type_record;

typedef struct alpha_native_method_record {
    uint32_t definition_index, method_index;
    uint64_t metadata_pointer, method_pointer;
} alpha_native_method_record;

typedef struct alpha_method_name_header {
    char magic[8];
    uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t method_count, nonempty_name_count, name_bytes, image_bytes;
    char executable_sha256[64], native_inventory_sha256[64];
    char reflection_semantics_sha256[64];
    uint32_t name_node_qword, encoded_name_qword;
    uint32_t decode_operation, reserved_layout_two;
    uint64_t lazy_initializer_rva, decode_key;
} alpha_method_name_header;

typedef struct alpha_method_name_record {
    uint32_t definition_index, method_index;
    uint64_t metadata_pointer, name_offset;
    uint32_t name_bytes, flags;
} alpha_method_name_record;

typedef struct alpha_detail_header {
    char magic[8];
    uint32_t version, header_bytes, method_record_bytes;
    uint32_t parameter_record_bytes;
    uint64_t method_count, parameter_count, string_bytes;
    uint64_t image_base, image_bytes, runtime_type_handle_qword, reserved;
    char executable_sha256[64], native_inventory_sha256[64];
    char type_identity_sha256[64], method_names_sha256[64];
} alpha_detail_header;

typedef struct alpha_detail_method {
    uint32_t definition_index, method_index;
    uint64_t metadata_pointer, function_pointer, return_descriptor;
    uint32_t attributes, impl_attributes, metadata_token, slot;
    uint32_t flags, parameter_count;
    uint64_t parameter_start, name_offset;
} alpha_detail_method;

typedef struct alpha_detail_parameter {
    uint32_t method_index, position;
    uint64_t type_descriptor;
    uint32_t attributes, flags, name_bytes, reserved;
    uint64_t name_offset;
} alpha_detail_parameter;

_Static_assert(sizeof(alpha_native_inventory_header) == $native_header_bytes,
    "native header layout mismatch");
_Static_assert(sizeof(alpha_native_type_record) == $native_type_bytes,
    "native type layout mismatch");
_Static_assert(sizeof(alpha_native_method_record) == $native_method_bytes,
    "native method layout mismatch");
_Static_assert(sizeof(alpha_method_name_header) == $name_header_bytes,
    "name header layout mismatch");
_Static_assert(sizeof(alpha_method_name_record) == $name_record_bytes,
    "name record layout mismatch");
_Static_assert(sizeof(alpha_detail_header) == $detail_header_bytes,
    "detail header layout mismatch");
_Static_assert(sizeof(alpha_detail_method) == $detail_method_bytes,
    "detail method layout mismatch");
_Static_assert(sizeof(alpha_detail_parameter) == $detail_parameter_bytes,
    "detail parameter layout mismatch");

static const char expected_executable_sha256[] = "$executable_sha256";
static const char expected_native_inventory_sha256[] = "$native_sha256";
static const char expected_type_identity_sha256[] = "$type_identity_sha256";
static const char expected_method_names_sha256[] = "$method_names_sha256";
static const DWORD expected_process_id = ${process_id}u;
static const uintptr_t expected_image_base = ${image_base}ull;
static const uint64_t expected_image_bytes = ${image_bytes}ull;
static const uint64_t expected_type_count = ${type_count}ull;
static const uint64_t expected_method_count = ${method_count}ull;
static const uint32_t embedded_descriptor_offset = ${descriptor_offset}u;
static const uint32_t method_parameter_count_offset = ${arity_offset}u;
static const uint32_t semantic_parameter_attribute_offset =
    ${parameter_attribute_offset}u;
static const uint32_t runtime_type_handle_qword = ${handle_qword}u;
static const uint32_t expected_metadata_token_rid_base =
    ${type_token_rid_base}u;
static const uintptr_t runtime_type_class = ${runtime_type_class}ull;
static const uintptr_t string_class = ${string_class}ull;
static const uintptr_t method_class = ${method_class}ull;
static const uintptr_t constructor_class = ${constructor_class}ull;
static const uintptr_t parameter_class = ${parameter_class}ull;
static const wchar_t native_inventory_input[] = $native_path;
static const wchar_t method_names_input[] = $method_names_path;
static const wchar_t detail_output[] = $output_path;
static const wchar_t status_output[] = $status_path;

typedef uintptr_t (*alpha_static_threearg)(
    uintptr_t, uintptr_t, uintptr_t, uintptr_t);
typedef uintptr_t (*alpha_instance_noarg)(uintptr_t, uintptr_t);
typedef uint32_t (*alpha_instance_dword)(uintptr_t, uintptr_t);
typedef uint8_t (*alpha_instance_bool)(uintptr_t, uintptr_t);

static const uintptr_t method_from_handle_pointer =
    ${method_from_handle_pointer}ull;
static const uintptr_t method_from_handle_metadata =
    ${method_from_handle_metadata}ull;
static const uintptr_t method_parameters_pointer =
    ${method_parameters_pointer}ull;
static const uintptr_t method_parameters_metadata =
    ${method_parameters_metadata}ull;
static const uintptr_t method_return_pointer = ${method_return_pointer}ull;
static const uintptr_t method_return_metadata = ${method_return_metadata}ull;
static const uintptr_t method_attributes_pointer =
    ${method_attributes_pointer}ull;
static const uintptr_t method_attributes_metadata =
    ${method_attributes_metadata}ull;
static const uintptr_t method_impl_attributes_pointer =
    ${method_impl_attributes_pointer}ull;
static const uintptr_t method_impl_attributes_metadata =
    ${method_impl_attributes_metadata}ull;
static const uintptr_t constructor_parameters_pointer =
    ${constructor_parameters_pointer}ull;
static const uintptr_t constructor_parameters_metadata =
    ${constructor_parameters_metadata}ull;
static const uintptr_t constructor_attributes_pointer =
    ${constructor_attributes_pointer}ull;
static const uintptr_t constructor_attributes_metadata =
    ${constructor_attributes_metadata}ull;
static const uintptr_t constructor_impl_attributes_pointer =
    ${constructor_impl_attributes_pointer}ull;
static const uintptr_t constructor_impl_attributes_metadata =
    ${constructor_impl_attributes_metadata}ull;
static const uintptr_t metadata_token_pointer = ${metadata_token_pointer}ull;
static const uintptr_t metadata_token_metadata = ${metadata_token_metadata}ull;
static const uintptr_t parameter_name_pointer = ${parameter_name_pointer}ull;
static const uintptr_t parameter_name_metadata = ${parameter_name_metadata}ull;
static const uintptr_t parameter_type_pointer = ${parameter_type_pointer}ull;
static const uintptr_t parameter_type_metadata = ${parameter_type_metadata}ull;
static const uintptr_t parameter_in_pointer = ${parameter_in_pointer}ull;
static const uintptr_t parameter_in_metadata = ${parameter_in_metadata}ull;
static const uintptr_t parameter_out_pointer = ${parameter_out_pointer}ull;
static const uintptr_t parameter_out_metadata = ${parameter_out_metadata}ull;
static const uintptr_t parameter_optional_pointer =
    ${parameter_optional_pointer}ull;
static const uintptr_t parameter_optional_metadata =
    ${parameter_optional_metadata}ull;

static alpha_native_type_record *native_types;
static alpha_native_method_record *native_methods;
static alpha_method_name_header *name_header;
static alpha_method_name_record *name_records;
static unsigned char *native_input_data, *name_input_data;
static alpha_detail_method *detail_methods;
static alpha_detail_parameter *detail_parameters;
static uint64_t expected_parameter_count, completed_method_count;
static uint64_t completed_parameter_count, string_bytes;
static char *strings;
static uint64_t string_capacity;
static uint64_t capture_index, failure_index;
static uint32_t failure_kind;
static uint32_t array_length_qword, array_vector_qword;
static uint32_t parameter_name_qword, parameter_type_qword;
static uint32_t parameter_attribute_offset;
static uint32_t method_return_qword, method_attribute_offset;
static uint32_t method_function_qword, method_slot_offset;
static uint32_t method_impl_attribute_offset;
static uint32_t method_attribute_support_count;
static uint32_t method_impl_attribute_support_count;
static uint32_t method_parameter_count_support_count;
static uint32_t slot_absent_sample_count, slot_present_sample_count;
static uint32_t method_slot_layout_resolved;
static uint32_t method_token_rid_base;
static volatile LONG probe_stage;
static volatile LONG diagnostic_method_samples;
static volatile LONG diagnostic_parameter_samples;
static volatile LONG diagnostic_named_parameter_samples;
static volatile LONG diagnostic_flag_samples;
static UINT capture_message;
static WNDPROC original_window_proc;
static volatile LONG callback_action, callback_complete;

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

static int executable(uintptr_t value) {
    MEMORY_BASIC_INFORMATION region;
    if (!value || !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD) return 0;
    DWORD protect = region.Protect & 0xffu;
    return protect == PAGE_EXECUTE || protect == PAGE_EXECUTE_READ ||
        protect == PAGE_EXECUTE_READWRITE ||
        protect == PAGE_EXECUTE_WRITECOPY;
}

static int object_class(uintptr_t object, uintptr_t expected) {
    uintptr_t observed = 0;
    if (!readable(object, sizeof(observed))) return 0;
    memcpy(&observed, (const void *)object, sizeof(observed));
    return observed == expected;
}

static int descriptor_from_type(uintptr_t object, uintptr_t *descriptor) {
    *descriptor = 0;
    if (!object_class(object, runtime_type_class)) return 0;
    uintptr_t address = object +
        (uintptr_t)runtime_type_handle_qword * sizeof(uintptr_t);
    if (address < object || !readable(address, sizeof(*descriptor))) return 0;
    memcpy(descriptor, (const void *)address, sizeof(*descriptor));
    return readable(*descriptor, 16u);
}

static int descriptors_equal(uintptr_t left, uintptr_t right) {
    unsigned char left_value[16], right_value[16];
    if (!readable(left, sizeof(left_value)) ||
        !readable(right, sizeof(right_value))) return 0;
    memcpy(left_value, (const void *)left, sizeof(left_value));
    memcpy(right_value, (const void *)right, sizeof(right_value));
    return !memcmp(left_value, right_value, sizeof(left_value));
}

static int managed_utf8(
    uintptr_t object, int allow_null, char **output, uint32_t *bytes
) {
    *output = NULL;
    *bytes = 0;
    if (!object) return allow_null;
    if (!object_class(object, string_class) ||
        !readable(object + 16u, sizeof(int32_t))) return 0;
    int32_t length = 0;
    memcpy(&length, (const void *)(object + 16u), sizeof(length));
    if (length < 0 || (uint32_t)length > ALPHA_MAX_TEXT ||
        (length && !readable(
            object + 20u, (SIZE_T)length * sizeof(wchar_t)))) return 0;
    if (!length) return 1;
    int required = WideCharToMultiByte(
        CP_UTF8, WC_ERR_INVALID_CHARS, (const wchar_t *)(object + 20u),
        length, NULL, 0, NULL, NULL);
    if (required <= 0 || required > 4 * (int)ALPHA_MAX_TEXT) return 0;
    char *value = (char *)malloc((SIZE_T)required);
    if (!value || WideCharToMultiByte(
            CP_UTF8, WC_ERR_INVALID_CHARS,
            (const wchar_t *)(object + 20u), length,
            value, required, NULL, NULL) != required) {
        free(value);
        return 0;
    }
    if (memchr(value, 0, (SIZE_T)required)) {
        free(value);
        return 0;
    }
    *output = value;
    *bytes = (uint32_t)required;
    return 1;
}

static int append_text(
    const char *value, uint32_t bytes, uint64_t *offset
) {
    if (!value || !bytes || string_bytes + bytes < string_bytes) return 0;
    uint64_t required = string_bytes + bytes;
    if (required > string_capacity) {
        uint64_t capacity = string_capacity ? string_capacity : 1024u * 1024u;
        while (capacity < required) {
            if (capacity > UINT64_MAX / 2u) return 0;
            capacity *= 2u;
        }
        if (capacity > (uint64_t)SIZE_MAX) return 0;
        char *grown = (char *)realloc(strings, (SIZE_T)capacity);
        if (!grown) return 0;
        strings = grown;
        string_capacity = capacity;
    }
    *offset = string_bytes;
    memcpy(strings + string_bytes, value, bytes);
    string_bytes = required;
    return 1;
}

static int read_file(const wchar_t *path, unsigned char **data, SIZE_T *bytes) {
    *data = NULL;
    *bytes = 0;
    FILE *input = _wfopen(path, L"rb");
    if (!input || _fseeki64(input, 0, SEEK_END) ||
        (*bytes = (SIZE_T)_ftelli64(input)) == (SIZE_T)-1 ||
        _fseeki64(input, 0, SEEK_SET)) {
        if (input) fclose(input);
        return 0;
    }
    unsigned char *value = (unsigned char *)malloc(*bytes ? *bytes : 1u);
    int ok = value && fread(value, 1, *bytes, input) == *bytes;
    fclose(input);
    if (!ok) {
        free(value);
        return 0;
    }
    *data = value;
    return 1;
}

static void digest_hex(const unsigned char digest[32], char output[65]) {
    static const char alphabet[] = "0123456789abcdef";
    for (int index = 0; index < 32; index++) {
        output[index * 2] = alphabet[digest[index] >> 4];
        output[index * 2 + 1] = alphabet[digest[index] & 15];
    }
    output[64] = 0;
}

static int sha256_file(const wchar_t *path, char output[65]) {
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
    while (ok) {
        DWORD count = 0;
        if (!ReadFile(input, buffer, 1024u * 1024u, &count, NULL)) {
            ok = 0;
            break;
        }
        if (!count) break;
        if (BCryptHashData(hash, buffer, count, 0) < 0) ok = 0;
    }
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) < 0) ok = 0;
    if (ok) digest_hex(digest, output);
    if (hash) BCryptDestroyHash(hash);
    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);
    if (object) HeapFree(GetProcessHeap(), 0, object);
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    CloseHandle(input);
    return ok;
}

static int executable_identity(char output[65]) {
    wchar_t path[32768];
    DWORD length = GetModuleFileNameW(
        NULL, path, (DWORD)(sizeof(path) / sizeof(path[0])));
    return length && length < sizeof(path) / sizeof(path[0]) &&
        sha256_file(path, output);
}

static int typed_parameter_array(
    uintptr_t array, uintptr_t **elements, uint32_t *count, int derive
) {
    *elements = NULL;
    *count = 0;
    if (!array || !readable(
            array, (derive ? 10u : 5u) * sizeof(uintptr_t))) return 0;
    uint32_t selected_length = array_length_qword;
    uint32_t selected_vector = array_vector_qword;
    if (derive) {
        selected_length = selected_vector = 0;
        for (uint32_t length_qword = 1; length_qword < 8; length_qword++) {
            uintptr_t length = 0;
            memcpy(&length, (const void *)(array +
                (uintptr_t)length_qword * sizeof(uintptr_t)), sizeof(length));
            if (!length || length > 65536u) continue;
            for (uint32_t vector_qword = length_qword + 1;
                 vector_qword < 10; vector_qword++) {
                uintptr_t vector = array +
                    (uintptr_t)vector_qword * sizeof(uintptr_t);
                if (!readable(vector, (SIZE_T)length * sizeof(uintptr_t)))
                    continue;
                uint64_t valid = 0;
                for (; valid < length; valid++) {
                    uintptr_t element = 0;
                    memcpy(&element, (const void *)(vector +
                        (uintptr_t)valid * sizeof(uintptr_t)), sizeof(element));
                    if (!object_class(element, parameter_class)) break;
                }
                if (valid == length) {
                    if (selected_length) return 0;
                    selected_length = length_qword;
                    selected_vector = vector_qword;
                }
            }
        }
        if (!selected_length || !selected_vector) return 0;
        array_length_qword = selected_length;
        array_vector_qword = selected_vector;
    }
    if (!selected_length || selected_vector <= selected_length ||
        selected_vector >= 10) return 0;
    uintptr_t length = 0;
    memcpy(&length, (const void *)(array +
        (uintptr_t)selected_length * sizeof(uintptr_t)), sizeof(length));
    if (length > 65536u) return 0;
    uintptr_t vector = array +
        (uintptr_t)selected_vector * sizeof(uintptr_t);
    if (length && !readable(vector, (SIZE_T)length * sizeof(uintptr_t)))
        return 0;
    for (uint64_t index = 0; index < length; index++) {
        uintptr_t element = 0;
        memcpy(&element, (const void *)(vector +
            (uintptr_t)index * sizeof(uintptr_t)), sizeof(element));
        if (derive) {
            if (!object_class(element, parameter_class)) return 0;
        } else if (!readable(element, ALPHA_PARAMETER_CAPTURE_BYTES)) {
            return 0;
        }
    }
    *elements = (uintptr_t *)vector;
    *count = (uint32_t)length;
    return 1;
}

static uintptr_t method_object(uint64_t index) {
    alpha_native_method_record *method = &native_methods[index];
    if (method->definition_index >= expected_type_count ||
        !method->metadata_pointer) return 0;
    uintptr_t owner = native_types[method->definition_index].class_pointer +
        embedded_descriptor_offset;
    alpha_static_threearg from_handle =
        (alpha_static_threearg)method_from_handle_pointer;
    uintptr_t object = from_handle(
        method->metadata_pointer, owner, 1u, method_from_handle_metadata);
    uintptr_t observed_metadata = 0;
    if (!readable(object, 3u * sizeof(uintptr_t))) return 0;
    memcpy(&observed_metadata,
        (const void *)(object + 2u * sizeof(uintptr_t)),
        sizeof(observed_metadata));
    return observed_metadata == method->metadata_pointer ? object : 0;
}

static int derive_layouts(void) {
    alpha_instance_noarg get_parameters =
        (alpha_instance_noarg)method_parameters_pointer;
    alpha_instance_dword get_attributes =
        (alpha_instance_dword)method_attributes_pointer;
    alpha_instance_dword get_impl_attributes =
        (alpha_instance_dword)method_impl_attributes_pointer;
    alpha_instance_noarg get_parameter_name =
        (alpha_instance_noarg)parameter_name_pointer;
    alpha_instance_noarg get_parameter_type =
        (alpha_instance_noarg)parameter_type_pointer;
    alpha_instance_bool get_in = (alpha_instance_bool)parameter_in_pointer;
    alpha_instance_bool get_out = (alpha_instance_bool)parameter_out_pointer;
    alpha_instance_bool get_optional =
        (alpha_instance_bool)parameter_optional_pointer;
    uint32_t attribute_support[64] = {0};
    uint32_t impl_attribute_support[64] = {0};
    uint32_t parameter_count_support[64] = {0};
    uint32_t slot_absent_support[64] = {0};
    uint32_t slot_present_support[64] = {0};
    uint32_t name_support[16] = {0}, type_support[16] = {0};
    uint32_t parameter_attribute_support[ALPHA_PARAMETER_LAYOUT_BYTES] = {0};
    uint32_t method_samples = 0, named_parameter_samples = 0;
    uint32_t parameter_samples = 0, flag_samples = 0;
    for (uint64_t index = 0;
         index < expected_method_count && index < ALPHA_SAMPLE_METHODS;
         index++) {
        InterlockedExchange(&probe_stage, 10);
        uint8_t native_count = 0;
        memcpy(&native_count, (const void *)(
            native_methods[index].metadata_pointer +
            method_parameter_count_offset), sizeof(native_count));
        uintptr_t object = method_object(index);
        if (!object) continue;
        uintptr_t observed_class = 0;
        memcpy(&observed_class, (const void *)object,
            sizeof(observed_class));
        if (observed_class == constructor_class) continue;
        if (observed_class != method_class) continue;
        InterlockedExchange(&probe_stage, 11);
        uintptr_t parameter_array = get_parameters(
            object, method_parameters_metadata);
        InterlockedExchange(&probe_stage, 12);
        uintptr_t *parameters = NULL;
        uint32_t parameter_count = 0;
        if (parameter_array && !array_length_qword) {
            if (!typed_parameter_array(
                    parameter_array, &parameters, &parameter_count, 1))
                continue;
        } else if (!typed_parameter_array(
                parameter_array, &parameters, &parameter_count, 0)) {
            if (parameter_array) continue;
            parameter_count = 0;
        }
        InterlockedExchange(&probe_stage, 13);
        if (native_count != parameter_count) continue;
        uint32_t attributes = get_attributes(
            object, method_attributes_metadata);
        InterlockedExchange(&probe_stage, 14);
        InterlockedExchange(&probe_stage, 15);
        uintptr_t metadata = native_methods[index].metadata_pointer;
        if (!readable(metadata, 64u)) continue;
        for (uint32_t offset = 0; offset + 2u <= 64u; offset++) {
            uint16_t value = 0;
            memcpy(&value, (const void *)(metadata + offset), sizeof(value));
            if (value == (uint16_t)attributes) attribute_support[offset]++;
        }
        /*
         * The same live-value procedure derives the remaining method layout
         * fields: the runtime reports both the implementation attributes and
         * the parameter count, so each offset is confirmed by current-process
         * evidence instead of assuming the previous build's field adjacency.
         */
        uint32_t impl_attributes_value = 0;
        if (method_impl_attributes_pointer &&
            method_impl_attributes_metadata) {
            impl_attributes_value = get_impl_attributes(
                object, method_impl_attributes_metadata);
        }
        if (method_impl_attributes_pointer &&
            method_impl_attributes_metadata &&
            impl_attributes_value <= UINT16_MAX) {
            for (uint32_t offset = 0; offset + 2u <= 64u; offset++) {
                uint16_t value = 0;
                memcpy(&value, (const void *)(metadata + offset),
                    sizeof(value));
                if (value == (uint16_t)impl_attributes_value)
                    impl_attribute_support[offset]++;
            }
        }
        if (parameter_count <= UINT16_MAX) {
            for (uint32_t offset = 0; offset + 2u <= 64u; offset++) {
                uint16_t value = 0;
                memcpy(&value, (const void *)(metadata + offset),
                    sizeof(value));
                if (value == (uint16_t)parameter_count)
                    parameter_count_support[offset]++;
            }
        }
        /*
         * The runtime marks a method without a vtable slot with 0xFFFF and a
         * slotted method with a small index.  Recording both halves of that
         * convention for every candidate offset keeps the slot derivation
         * evidence-based even when the surrounding fields are reordered.
         */
        for (uint32_t offset = 0; offset + 2u <= 64u; offset++) {
            uint16_t value = 0;
            memcpy(&value, (const void *)(metadata + offset), sizeof(value));
            if (value == 0xFFFFu) slot_absent_support[offset]++;
            else slot_present_support[offset]++;
        }
        method_samples++;
        for (uint32_t parameter_index = 0;
             parameter_index < parameter_count && parameter_samples < 16384u;
             parameter_index++) {
            uintptr_t parameter = parameters[parameter_index];
            uintptr_t name_object = get_parameter_name(
                parameter, parameter_name_metadata);
            InterlockedExchange(&probe_stage, 16);
            uintptr_t type_object = get_parameter_type(
                parameter, parameter_type_metadata);
            InterlockedExchange(&probe_stage, 17);
            if (!object_class(type_object, runtime_type_class)) continue;
            uint8_t is_in = get_in(parameter, parameter_in_metadata);
            uint8_t is_out = get_out(parameter, parameter_out_metadata);
            uint8_t is_optional = get_optional(
                parameter, parameter_optional_metadata);
            InterlockedExchange(&probe_stage, 18);
            if (is_in > 1u || is_out > 1u || is_optional > 1u) continue;
            if (!readable(parameter, ALPHA_PARAMETER_LAYOUT_BYTES))
                continue;
            InterlockedExchange(&probe_stage, 19);
            for (uint32_t qword = 2; qword < 16; qword++) {
                uintptr_t value = 0;
                memcpy(&value, (const void *)(parameter +
                    (uintptr_t)qword * sizeof(uintptr_t)), sizeof(value));
                if (value == type_object) type_support[qword]++;
                if (name_object && value == name_object) name_support[qword]++;
            }
            if (name_object) named_parameter_samples++;
            if (is_in || is_out || is_optional) flag_samples++;
            for (uint32_t offset = 16;
                 offset < ALPHA_PARAMETER_LAYOUT_BYTES; offset++) {
                uint8_t value = 0;
                memcpy(&value, (const void *)(parameter + offset), 1u);
                if (!!(value & 1u) == is_in &&
                    !!(value & 2u) == is_out &&
                    !!(value & 16u) == is_optional)
                    parameter_attribute_support[offset]++;
            }
            parameter_samples++;
        }
        if (method_samples >= 64u && parameter_samples >= 128u &&
            named_parameter_samples >= 64u) break;
    }
    InterlockedExchange(&diagnostic_method_samples, (LONG)method_samples);
    InterlockedExchange(
        &diagnostic_parameter_samples, (LONG)parameter_samples);
    InterlockedExchange(
        &diagnostic_named_parameter_samples,
        (LONG)named_parameter_samples);
    InterlockedExchange(&diagnostic_flag_samples, (LONG)flag_samples);
    uint32_t matches = 0;
    for (uint32_t offset = 0; offset + 2u <= 64u; offset++)
        if (attribute_support[offset] == method_samples) {
            method_attribute_offset = offset;
            matches++;
        }
    if (matches != 1u) {
        failure_kind = 202u;
        return 0;
    }
    method_attribute_support_count = method_samples;
    matches = 0;
    for (uint32_t offset = 0; offset + 2u <= 64u; offset++)
        if (impl_attribute_support[offset] == method_samples) {
            method_impl_attribute_offset = offset;
            matches++;
        }
    if (matches != 1u) {
        failure_kind = 203u;
        return 0;
    }
    method_impl_attribute_support_count = method_samples;
    matches = 0;
    for (uint32_t qword = 2; qword < 16; qword++)
        if (type_support[qword] == parameter_samples) {
            parameter_type_qword = qword;
            matches++;
        }
    if (matches != 1u) {
        failure_kind = 204u;
        return 0;
    }
    matches = 0;
    for (uint32_t qword = 2; qword < 16; qword++)
        if (name_support[qword] == named_parameter_samples) {
            parameter_name_qword = qword;
            matches++;
        }
    if (matches != 1u) {
        failure_kind = 205u;
        return 0;
    }
    parameter_attribute_offset = semantic_parameter_attribute_offset;
    if (parameter_attribute_offset >= ALPHA_PARAMETER_LAYOUT_BYTES ||
        parameter_attribute_support[parameter_attribute_offset] !=
            parameter_samples ||
        method_parameter_count_offset + 2u > 64u ||
        parameter_count_support[method_parameter_count_offset] !=
            method_samples) {
        failure_kind = 206u;
        return 0;
    }
    method_parameter_count_support_count = method_samples;
    /*
     * The slot field has no runtime getter, so it is captured only while the
     * current process still exposes the legacy adjacency layout
     * {slot, impl attributes, attributes, parameter count}.  When a newer
     * build rearranges the fields the slot is recorded as explicitly not
     * captured instead of silently reading a neighbouring field.
     */
    if (method_attribute_offset >= 6u &&
        method_impl_attribute_offset == method_attribute_offset - 2u &&
        method_parameter_count_offset == method_attribute_offset + 2u) {
        method_slot_offset = method_attribute_offset - 4u;
        method_slot_layout_resolved = 1u;
    } else if (
        method_parameter_count_offset >= 2u &&
        method_impl_attribute_offset == method_attribute_offset + 2u &&
        method_parameter_count_offset == method_attribute_offset + 6u &&
        slot_absent_support[method_parameter_count_offset - 2u] > 0u &&
        slot_present_support[method_parameter_count_offset - 2u] > 0u) {
        /*
         * Reordered layout observed on newer clients:
         * {attributes, implementation attributes, slot, parameter count}.
         * The candidate is confirmed by the runtime's own slot convention
         * (both slotted and unslotted methods present).
         */
        method_slot_offset = method_parameter_count_offset - 2u;
        method_slot_layout_resolved = 1u;
    } else {
        method_slot_offset = 0u;
        method_slot_layout_resolved = 0u;
    }
    if (!method_slot_layout_resolved) {
        /*
         * The method slot is consumed by the module/ancestry derivation, so a
         * layout this capture cannot confirm must stop here instead of
         * publishing a placeholder slot value.
         */
        failure_kind = 208u;
        return 0;
    }
    slot_absent_sample_count = slot_absent_support[method_slot_offset];
    slot_present_sample_count = slot_present_support[method_slot_offset];
    if (method_samples < 16u || parameter_samples < 32u ||
        named_parameter_samples < 16u) {
        failure_kind = 207u;
        return 0;
    }
    return 1;
}

static int capture_batch(void) {
    alpha_instance_noarg get_method_parameters =
        (alpha_instance_noarg)method_parameters_pointer;
    alpha_instance_noarg get_constructor_parameters =
        (alpha_instance_noarg)constructor_parameters_pointer;
    alpha_instance_noarg get_return =
        (alpha_instance_noarg)method_return_pointer;
    alpha_instance_dword get_method_attributes =
        (alpha_instance_dword)method_attributes_pointer;
    alpha_instance_dword get_constructor_attributes =
        (alpha_instance_dword)constructor_attributes_pointer;
    alpha_instance_dword get_method_impl_attributes =
        (alpha_instance_dword)method_impl_attributes_pointer;
    alpha_instance_dword get_constructor_impl_attributes =
        (alpha_instance_dword)constructor_impl_attributes_pointer;
    alpha_instance_dword get_metadata_token =
        (alpha_instance_dword)metadata_token_pointer;
    uint64_t end = capture_index + ALPHA_CAPTURE_BATCH;
    if (end < capture_index || end > expected_method_count)
        end = expected_method_count;
    for (; capture_index < end; capture_index++) {
        uint64_t index = capture_index;
        InterlockedExchange(&probe_stage, 100);
        uintptr_t object = method_object(index);
        if (!object) {
            failure_index = index + 1u;
            failure_kind = 1u;
            return 0;
        }
        InterlockedExchange(&probe_stage, 101);
        alpha_method_name_record *name = &name_records[index];
        uintptr_t metadata = native_methods[index].metadata_pointer;
        if (name->definition_index !=
                native_methods[index].definition_index ||
            name->method_index != native_methods[index].method_index ||
            name->metadata_pointer != metadata ||
            name->name_offset + name->name_bytes < name->name_offset) {
            failure_index = index + 1u;
            failure_kind = 5u;
            return 0;
        }
        uintptr_t observed_class = 0;
        memcpy(&observed_class, (const void *)object,
            sizeof(observed_class));
        int is_constructor = observed_class == constructor_class;
        if (!is_constructor && observed_class != method_class) {
            failure_index = index + 1u;
            failure_kind = 14u;
            return 0;
        }
        alpha_instance_noarg get_parameters = is_constructor
            ? get_constructor_parameters : get_method_parameters;
        uintptr_t parameters_metadata = is_constructor
            ? constructor_parameters_metadata : method_parameters_metadata;
        uintptr_t array = get_parameters(object, parameters_metadata);
        InterlockedExchange(&probe_stage, 102);
        uintptr_t *parameters = NULL;
        uint32_t parameter_count = 0;
        if (!typed_parameter_array(
                array, &parameters, &parameter_count, 0)) {
            if (array) {
                failure_index = index + 1u;
                failure_kind = 2u;
                return 0;
            }
        }
        InterlockedExchange(&probe_stage, 103);
        uint8_t native_count = 0;
        memcpy(&native_count, (const void *)(metadata +
            method_parameter_count_offset), sizeof(native_count));
        if (native_count != parameter_count ||
            completed_parameter_count + parameter_count >
                expected_parameter_count) {
            failure_index = index + 1u;
            failure_kind = 3u;
            return 0;
        }
        InterlockedExchange(&probe_stage, 104);
        alpha_detail_method *method = &detail_methods[index];
        method->definition_index = native_methods[index].definition_index;
        method->method_index = (uint32_t)index;
        method->metadata_pointer = metadata;
        method->function_pointer = native_methods[index].method_pointer;
        InterlockedExchange(&probe_stage, 105);
        InterlockedExchange(&probe_stage, 106);
        if (is_constructor) {
            method->flags |= 1u;
        } else {
            uintptr_t return_object = get_return(
                object, method_return_metadata);
            if (!descriptor_from_type(
                    return_object, &method->return_descriptor)) {
                failure_index = index + 1u;
                failure_kind = 12u;
                return 0;
            }
        }
        InterlockedExchange(&probe_stage, 107);
        uint32_t slot = 0xFFFFFFFFu;
        if (method_slot_layout_resolved) {
            uint16_t raw_slot = 0;
            memcpy(&raw_slot, (const void *)(metadata + method_slot_offset),
                sizeof(raw_slot));
            slot = raw_slot;
        }
        uint16_t attributes = 0;
        memcpy(&attributes, (const void *)(metadata +
            method_attribute_offset), sizeof(attributes));
        alpha_instance_dword get_attributes = is_constructor
            ? get_constructor_attributes : get_method_attributes;
        uintptr_t attributes_metadata = is_constructor
            ? constructor_attributes_metadata : method_attributes_metadata;
        uint32_t observed_attributes = get_attributes(
            object, attributes_metadata);
        if (observed_attributes > UINT16_MAX ||
            observed_attributes != attributes) {
            failure_index = index + 1u;
            failure_kind = 15u;
            return 0;
        }
        method->attributes = attributes;
        alpha_instance_dword get_impl_attributes = is_constructor
            ? get_constructor_impl_attributes : get_method_impl_attributes;
        uintptr_t impl_attributes_metadata = is_constructor
            ? constructor_impl_attributes_metadata
            : method_impl_attributes_metadata;
        uint32_t impl_attributes = get_impl_attributes(
            object, impl_attributes_metadata);
        uint16_t raw_impl_attributes = 0;
        memcpy(&raw_impl_attributes,
            (const void *)(metadata + method_impl_attribute_offset),
            sizeof(raw_impl_attributes));
        if (impl_attributes > UINT16_MAX ||
            impl_attributes != raw_impl_attributes) {
            failure_index = index + 1u;
            failure_kind = 13u;
            return 0;
        }
        method->impl_attributes = impl_attributes;
        method->slot = slot;
        InterlockedExchange(&probe_stage, 108);
        uint32_t metadata_token = get_metadata_token(
            object, metadata_token_metadata);
        uint32_t metadata_token_rid = metadata_token & 0x00ffffffu;
        if (!index) method_token_rid_base = metadata_token_rid;
        uint64_t expected_metadata_token_rid =
            index + (uint64_t)method_token_rid_base;
        if ((metadata_token & 0xff000000u) != 0x06000000u ||
            method_token_rid_base > 1u ||
            method_token_rid_base != expected_metadata_token_rid_base ||
            expected_metadata_token_rid > 0x00ffffffu ||
            metadata_token_rid != expected_metadata_token_rid) {
            failure_index = index + 1u;
            failure_kind = 16u;
            return 0;
        }
        method->metadata_token = metadata_token;
        method->parameter_start = completed_parameter_count;
        method->parameter_count = parameter_count;
        InterlockedExchange(&probe_stage, 109);
        if (name->name_bytes) {
            if (!append_text(
                    (const char *)(name_input_data + name->name_offset),
                    name->name_bytes, &method->name_offset)) {
                failure_index = index + 1u;
                failure_kind = 6u;
                return 0;
            }
            const char *value = (const char *)(
                name_input_data + name->name_offset);
        } else {
            char synthetic[40];
            int bytes = snprintf(synthetic, sizeof(synthetic),
                "EmptyMethod_%X", method->metadata_token);
            if (bytes <= 0 || bytes >= (int)sizeof(synthetic) ||
                !append_text(synthetic, (uint32_t)bytes,
                    &method->name_offset)) {
                failure_index = index + 1u;
                failure_kind = 7u;
                return 0;
            }
        }
        InterlockedExchange(&probe_stage, 110);
        for (uint32_t position = 0; position < parameter_count; position++) {
            uintptr_t parameter = parameters[position];
            uintptr_t name_object = 0, type_object = 0, descriptor = 0;
            memcpy(&name_object, (const void *)(parameter +
                (uintptr_t)parameter_name_qword * sizeof(uintptr_t)),
                sizeof(name_object));
            memcpy(&type_object, (const void *)(parameter +
                (uintptr_t)parameter_type_qword * sizeof(uintptr_t)),
                sizeof(type_object));
            if (!descriptor_from_type(type_object, &descriptor)) {
                failure_index = index + 1u;
                failure_kind = 8u;
                return 0;
            }
            uint16_t raw_attributes = 0;
            memcpy(&raw_attributes, (const void *)(parameter +
                parameter_attribute_offset), sizeof(raw_attributes));
            alpha_detail_parameter *output =
                &detail_parameters[completed_parameter_count];
            output->method_index = (uint32_t)index;
            output->position = position;
            output->type_descriptor = descriptor;
            output->attributes = raw_attributes;
            output->flags =
                (raw_attributes & 1u ? 1u : 0u) |
                (raw_attributes & 2u ? 2u : 0u) |
                (raw_attributes & 16u ? 4u : 0u);
            uint64_t parameter_token_rid = completed_parameter_count +
                (uint64_t)method_token_rid_base;
            if (parameter_token_rid > 0x00ffffffu) {
                failure_index = index + 1u;
                failure_kind = 17u;
                return 0;
            }
            output->reserved = 0x08000000u |
                (uint32_t)parameter_token_rid;
            char *text = NULL;
            uint32_t bytes = 0;
            if (!managed_utf8(name_object, 1, &text, &bytes)) {
                failure_index = index + 1u;
                failure_kind = 9u;
                return 0;
            }
            if (bytes) {
                output->name_bytes = bytes;
                if (!append_text(text, bytes, &output->name_offset)) {
                    free(text);
                    failure_index = index + 1u;
                    failure_kind = 10u;
                    return 0;
                }
            } else {
                char synthetic[40];
                int synthetic_bytes = snprintf(
                    synthetic, sizeof(synthetic),
                    "EmptyParameter_%u", position);
                if (synthetic_bytes <= 0 ||
                    synthetic_bytes >= (int)sizeof(synthetic) ||
                    !append_text(synthetic, (uint32_t)synthetic_bytes,
                        &output->name_offset)) {
                    free(text);
                    failure_index = index + 1u;
                    failure_kind = 11u;
                    return 0;
                }
                output->name_bytes = (uint32_t)synthetic_bytes;
            }
            free(text);
            completed_parameter_count++;
            InterlockedExchange(&probe_stage, 111);
        }
        completed_method_count++;
        InterlockedExchange(&probe_stage, 112);
    }
    return 1;
}

static void write_status(const char *status, int output_written);
static volatile LONG current_request, request_sequence, callback_active;
static LRESULT CALLBACK capture_window_proc(
    HWND window, UINT message, WPARAM wparam, LPARAM lparam
) {
    if (message != capture_message)
        return CallWindowProcW(
            original_window_proc, window, message, wparam, lparam);
    LONG request = (LONG)wparam;
    if (!request || InterlockedCompareExchange(&current_request, 0, 0) != request ||
        InterlockedCompareExchange(&callback_active, 1, 0)) return 0;

    if (InterlockedCompareExchange(&current_request, 0, request) != request) {
        InterlockedExchange(&callback_active, 0);
        return 0;
    }
    LONG action = InterlockedCompareExchange(&callback_action, 0, 0);
    int ok = action == 1 ? derive_layouts() :
        action == 2 ? capture_batch() : 0;
    InterlockedExchange(&callback_complete, ok ? 1 : -1);
    InterlockedExchange(&callback_active, 0);
    return ok;
}

typedef struct alpha_window {
    DWORD process_id;
    HWND selected;
    DWORD thread_id;
    uint32_t count;
} alpha_window;

static BOOL CALLBACK select_window(HWND window, LPARAM parameter) {
    alpha_window *selection = (alpha_window *)(uintptr_t)parameter;
    DWORD process_id = 0;
    RECT bounds;
    if (!selection || !IsWindowVisible(window) ||
        GetWindow(window, GW_OWNER) ||
        !GetWindowRect(window, &bounds) || bounds.right <= bounds.left ||
        bounds.bottom <= bounds.top) return TRUE;
    DWORD thread_id = GetWindowThreadProcessId(window, &process_id);
    if (process_id != selection->process_id || !thread_id) return TRUE;
    selection->selected = window;
    selection->thread_id = thread_id;
    selection->count++;
    return TRUE;
}

static int dispatch_capture(void) {
    alpha_window selection = {0};
    selection.process_id = GetCurrentProcessId();
    if (!EnumWindows(select_window, (LPARAM)(uintptr_t)&selection) ||
        selection.count != 1 || !selection.selected || !selection.thread_id) {
        failure_kind = 300; failure_index = selection.count;
        return 0;
    }
    capture_message = RegisterWindowMessageW(
        L"ALPHA v2 current runtime method detail inventory");
    if (!capture_message) {
        failure_kind = 302; failure_index = GetLastError(); return 0;
    }
    SetLastError(0);
    original_window_proc = (WNDPROC)(uintptr_t)SetWindowLongPtrW(
        selection.selected, GWLP_WNDPROC,
        (LONG_PTR)(uintptr_t)capture_window_proc);
    DWORD subclass_error = GetLastError();
    if (!original_window_proc || subclass_error != ERROR_SUCCESS) {
        failure_kind = 303; failure_index = subclass_error; return 0;
    }
    int ok = 1, layouts_ready = 0;
    uint32_t transient_failures = 0;
    while (ok && (!layouts_ready || capture_index < expected_method_count)) {
        DWORD_PTR result = 0;
        uint64_t before = capture_index;
        LONG request = InterlockedIncrement(&request_sequence);
        InterlockedExchange(&callback_action, layouts_ready ? 2 : 1);
        InterlockedExchange(&callback_complete, 0);
        InterlockedExchange(&current_request, request);
        SetLastError(0);
        int dispatched = SendMessageTimeoutW(
            selection.selected, capture_message, (WPARAM)request, 0,
            SMTO_BLOCK, 60000, &result) != 0;
        DWORD dispatch_error = GetLastError();
        InterlockedExchange(&current_request, 0);


        for (uint32_t wait = 0;
             InterlockedCompareExchange(&callback_active, 0, 0) && wait < 2000u;
             wait++) Sleep(1);
        if (InterlockedCompareExchange(&callback_active, 0, 0)) {
            failure_kind = 304; ok = 0; break;
        }
        LONG callback = InterlockedCompareExchange(
            &callback_complete, 0, 0);
        if (callback == 1) {
            if (layouts_ready && capture_index <= before) {
                failure_kind = 308; ok = 0; break;
            }
            if (!layouts_ready || capture_index == expected_method_count ||
                capture_index / 16384u != before / 16384u)
                write_status("capturing", 0);
            layouts_ready = 1; transient_failures = 0; continue;
        }
        if (callback < 0 || failure_kind) {
            if (!failure_kind) failure_kind = 305;
            ok = 0; break;
        }
        if (!dispatched && transient_failures++ < 16u) {
            write_status("waiting_for_main_thread", 0); Sleep(250); continue;
        }
        failure_kind = 301; failure_index = dispatch_error; ok = 0;
    }
    InterlockedExchange(&current_request, 0);
    if (original_window_proc)
        SetWindowLongPtrW(selection.selected, GWLP_WNDPROC,
            (LONG_PTR)(uintptr_t)original_window_proc);


    return ok;
}

static void write_status(const char *status, int output_written) {

    wchar_t pending[sizeof(status_output) / sizeof(*status_output) + 9];
    memcpy(pending, status_output, sizeof(status_output));
    wcscat(pending, L".pending");
    int fd = _wopen(pending, _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY,
                   _S_IREAD | _S_IWRITE);
    if (fd < 0) return;
    FILE *output = _fdopen(fd, "wb");
    if (!output) { _close(fd); _wremove(pending); return; }
    fprintf(output,
        "{\n"
        "  \"schema\": \"$status_schema\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_process_id\": %lu,\n"
        "  \"completed_method_count\": %llu,\n"
        "  \"completed_parameter_count\": %llu,\n"
        "  \"expected_method_count\": %llu,\n"
        "  \"expected_parameter_count\": %llu,\n"
        "  \"failure_index_owner_only\": %llu,\n"
        "  \"failure_kind_owner_only\": %u,\n"
        "  \"probe_stage_owner_only\": %ld,\n"
        "  \"method_layout_sample_count_owner_only\": %ld,\n"
        "  \"parameter_layout_sample_count_owner_only\": %ld,\n"
        "  \"named_parameter_sample_count_owner_only\": %ld,\n"
        "  \"parameter_flag_sample_count_owner_only\": %ld,\n"
        "  \"array_length_qword_owner_only\": %u,\n"
        "  \"array_vector_qword_owner_only\": %u,\n"
        "  \"parameter_name_qword_owner_only\": %u,\n"
        "  \"parameter_type_qword_owner_only\": %u,\n"
        "  \"parameter_attribute_offset_owner_only\": %u,\n"
        "  \"method_return_qword_owner_only\": %u,\n"
        "  \"method_attribute_offset_owner_only\": %u,\n"
        "  \"method_impl_attribute_offset_owner_only\": %u,\n"
        "  \"method_attribute_support_count_owner_only\": %u,\n"
        "  \"method_impl_attribute_support_count_owner_only\": %u,\n"
        "  \"method_parameter_count_support_count_owner_only\": %u,\n"
        "  \"method_slot_layout_resolved\": %s,\n"
        "  \"method_slot_absent_sample_count_owner_only\": %u,\n"
        "  \"method_slot_present_sample_count_owner_only\": %u,\n"
        "  \"method_function_qword_owner_only\": %u,\n"
        "  \"method_slot_offset_owner_only\": %u,\n"
        "  \"method_token_rid_base\": %u,\n"
        "  \"method_impl_attributes_captured\": true,\n"
        "  \"output_written\": %s,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"saved_member_detail_used\": false,\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_offset_used\": false,\n"
        "  \"external_runtime_component_used\": false\n"
        "}\n",
        status, (unsigned long)GetCurrentProcessId(),
        (unsigned long)expected_process_id,
        (unsigned long long)completed_method_count,
        (unsigned long long)completed_parameter_count,
        (unsigned long long)expected_method_count,
        (unsigned long long)expected_parameter_count,
        (unsigned long long)failure_index, failure_kind,
        InterlockedCompareExchange(&probe_stage, 0, 0),
        InterlockedCompareExchange(&diagnostic_method_samples, 0, 0),
        InterlockedCompareExchange(&diagnostic_parameter_samples, 0, 0),
        InterlockedCompareExchange(
            &diagnostic_named_parameter_samples, 0, 0),
        InterlockedCompareExchange(&diagnostic_flag_samples, 0, 0),
        array_length_qword, array_vector_qword,
        parameter_name_qword, parameter_type_qword,
        parameter_attribute_offset, method_return_qword,
        method_attribute_offset, method_impl_attribute_offset,
        method_attribute_support_count,
        method_impl_attribute_support_count,
        method_parameter_count_support_count,
        method_slot_layout_resolved ? "true" : "false",
        slot_absent_sample_count, slot_present_sample_count,
        method_function_qword,
        method_slot_offset, method_token_rid_base,
        output_written ? "true" : "false");
    int ok = !ferror(output);
    if (fclose(output)) ok = 0;
    if (ok) ok = MoveFileExW(pending, status_output,
                            MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH) != 0;
    if (!ok) _wremove(pending);
}

static int write_output(void) {
    uint64_t records_bytes = sizeof(alpha_detail_header) +
        expected_method_count * sizeof(alpha_detail_method) +
        expected_parameter_count * sizeof(alpha_detail_parameter);
    if (records_bytes < sizeof(alpha_detail_header)) return 0;
    for (uint64_t index = 0; index < expected_method_count; index++)
        detail_methods[index].name_offset += records_bytes;
    for (uint64_t index = 0; index < expected_parameter_count; index++)
        detail_parameters[index].name_offset += records_bytes;
    alpha_detail_header header;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHADM1", 8);
    header.version = ${detail_version}u;
    header.header_bytes = sizeof(header);
    header.method_record_bytes = sizeof(alpha_detail_method);
    header.parameter_record_bytes = sizeof(alpha_detail_parameter);
    header.method_count = expected_method_count;
    header.parameter_count = expected_parameter_count;
    header.string_bytes = string_bytes;
    header.image_base = expected_image_base;
    header.image_bytes = expected_image_bytes;
    header.runtime_type_handle_qword = runtime_type_handle_qword;
    memcpy(header.executable_sha256, expected_executable_sha256, 64);
    memcpy(header.native_inventory_sha256,
        expected_native_inventory_sha256, 64);
    memcpy(header.type_identity_sha256, expected_type_identity_sha256, 64);
    memcpy(header.method_names_sha256, expected_method_names_sha256, 64);
    FILE *output = _wfopen(detail_output, L"wb");
    if (!output) return 0;
    int ok = fwrite(&header, 1, sizeof(header), output) == sizeof(header) &&
        fwrite(detail_methods, sizeof(alpha_detail_method),
            expected_method_count, output) == expected_method_count &&
        fwrite(detail_parameters, sizeof(alpha_detail_parameter),
            expected_parameter_count, output) == expected_parameter_count &&
        fwrite(strings, 1, string_bytes, output) == string_bytes;
    if (fclose(output)) ok = 0;
    if (!ok) _wremove(detail_output);
    return ok;
}

static DWORD WINAPI worker(LPVOID unused) {
    (void)unused;
    _wremove(detail_output);
    _wremove(status_output);
    write_status("starting", 0);
    char executable_hash[65], native_hash[65], name_hash[65];
    if (GetCurrentProcessId() != expected_process_id ||
        !executable_identity(executable_hash) ||
        strcmp(executable_hash, expected_executable_sha256) ||
        !sha256_file(native_inventory_input, native_hash) ||
        strcmp(native_hash, expected_native_inventory_sha256) ||
        !sha256_file(method_names_input, name_hash) ||
        strcmp(name_hash, expected_method_names_sha256)) {
        failure_kind = 100u;
        write_status("identity_mismatch", 0);
        return 0;
    }
    SIZE_T native_bytes = 0, name_bytes = 0;
    if (!read_file(native_inventory_input, &native_input_data, &native_bytes) ||
        !read_file(method_names_input, &name_input_data, &name_bytes) ||
        native_bytes < sizeof(alpha_native_inventory_header) ||
        name_bytes < sizeof(alpha_method_name_header)) {
        failure_kind = 101u;
        write_status("input_unavailable", 0);
        return 0;
    }
    alpha_native_inventory_header *native_header =
        (alpha_native_inventory_header *)native_input_data;
    name_header = (alpha_method_name_header *)name_input_data;
    uint64_t native_required = sizeof(*native_header) +
        expected_type_count * sizeof(alpha_native_type_record) +
        expected_method_count * sizeof(alpha_native_method_record);
    uint64_t names_required = sizeof(*name_header) +
        expected_method_count * sizeof(alpha_method_name_record);
    if (memcmp(native_header->magic, "ALPHANI1", 8) ||
        native_header->type_count != expected_type_count ||
        native_header->method_count != expected_method_count ||
        native_required > native_bytes ||
        memcmp(name_header->magic, "ALPHANN2", 8) ||
        name_header->version != $name_version ||
        name_header->header_bytes != sizeof(*name_header) ||
        name_header->record_bytes != sizeof(alpha_method_name_record) ||
        name_header->reserved ||
        (name_header->decode_operation != $decode_xor_code &&
         name_header->decode_operation != $decode_add_code) ||
        name_header->reserved_layout_two ||
        !name_header->lazy_initializer_rva || !name_header->decode_key ||
        name_header->image_bytes != $image_bytes ||
        name_header->method_count != expected_method_count ||
        names_required > name_bytes) {
        failure_kind = 102u;
        write_status("input_invalid", 0);
        return 0;
    }
    write_status("inputs_verified", 0);
    native_types = (alpha_native_type_record *)(
        native_input_data + sizeof(*native_header));
    native_methods = (alpha_native_method_record *)(
        native_input_data + sizeof(*native_header) +
        expected_type_count * sizeof(alpha_native_type_record));
    name_records = (alpha_method_name_record *)(
        name_input_data + sizeof(*name_header));
    for (uint64_t index = 0; index < expected_method_count; index++) {
        uint8_t count = 0;
        uintptr_t metadata = native_methods[index].metadata_pointer;
        if (!readable(metadata + method_parameter_count_offset, 1u)) {
            failure_index = index + 1u;
            failure_kind = 103u;
            write_status("arity_unreadable", 0);
            return 0;
        }
        memcpy(&count, (const void *)(metadata +
            method_parameter_count_offset), 1u);
        expected_parameter_count += count;
    }
    if (!expected_parameter_count ||
        expected_parameter_count > 16000000ull ||
        expected_method_count > SIZE_MAX / sizeof(alpha_detail_method) ||
        expected_parameter_count >
            SIZE_MAX / sizeof(alpha_detail_parameter)) {
        failure_kind = 104u;
        write_status("count_invalid", 0);
        return 0;
    }
    detail_methods = (alpha_detail_method *)calloc(
        (SIZE_T)expected_method_count, sizeof(*detail_methods));
    detail_parameters = (alpha_detail_parameter *)calloc(
        (SIZE_T)expected_parameter_count, sizeof(*detail_parameters));
    if (!detail_methods || !detail_parameters) {
        failure_kind = 105u;
        write_status("allocation_failed", 0);
        return 0;
    }
    write_status("capturing", 0);
    int ok = dispatch_capture();
    if (!ok || completed_method_count != expected_method_count ||
        completed_parameter_count != expected_parameter_count) {
        if (!failure_kind) failure_kind = 106u;
        write_status("capture_failed", 0);
        return 0;
    }
    write_status("writing", 0);
    ok = write_output();
    write_status(ok ? "complete" : "write_failed", ok);
    return 0;
}

BOOL WINAPI DllMain(HINSTANCE module, DWORD reason, LPVOID reserved) {
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(module);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }
    return TRUE;
}
''')


def runtime_method_detail_inventory_source(
    *, binding: dict[str, Any], output_path: Path, status_path: Path
) -> str:
    operations = binding["operations"]
    values: dict[str, Any] = {
        "native_header_bytes": _NATIVE_INVENTORY_HEADER.size,
        "native_type_bytes": _NATIVE_TYPE_RECORD.size,
        "native_method_bytes": _NATIVE_METHOD_RECORD.size,
        "name_header_bytes": RUNTIME_METHOD_NAME_HEADER.size,
        "name_record_bytes": RUNTIME_METHOD_NAME_RECORD.size,
        "name_version": RUNTIME_METHOD_NAME_VERSION,
        "decode_xor_code": METHOD_NAME_DECODE_OPERATION_CODES["xor"],
        "decode_add_code": METHOD_NAME_DECODE_OPERATION_CODES["add"],
        "detail_header_bytes": RUNTIME_METHOD_DETAIL_HEADER.size,
        "detail_method_bytes": RUNTIME_METHOD_DETAIL_METHOD.size,
        "detail_parameter_bytes": RUNTIME_METHOD_DETAIL_PARAMETER.size,
        "detail_version": RUNTIME_METHOD_DETAIL_VERSION,
        "status_schema": RUNTIME_METHOD_DETAIL_STATUS_SCHEMA,
        "executable_sha256": binding["binary"]["sha256"],
        "native_sha256": binding["native_inventory"]["sha256"],
        "type_identity_sha256": binding["type_identity_inventory"]["sha256"],
        "method_names_sha256": binding["method_name_observation"]["sha256"],
        "process_id": binding["process_id"],
        "image_base": binding["image_base"],
        "image_bytes": binding["image_bytes"],
        "type_count": binding["type_count"],
        "method_count": binding["method_count"],
        "descriptor_offset": binding["descriptor_offset"],
        "arity_offset": binding["arity_offset"],
        "parameter_attribute_offset": binding[
            "parameter_attribute_offset"
        ],
        "handle_qword": binding["handle_qword"],
        "type_token_rid_base": binding["type_token_rid_base"],
        "runtime_type_class": binding["runtime_type_class"],
        "string_class": binding["string_class"],
        "method_class": binding["method_class"],
        "constructor_class": binding["constructor_class"],
        "parameter_class": binding["parameter_class"],
        "native_path": _wide_literal(
            _windows_z_path(Path(binding["native_inventory"]["path"]))
        ),
        "method_names_path": _wide_literal(
            _windows_z_path(Path(binding["method_name_observation"]["path"]))
        ),
        "output_path": _wide_literal(_windows_z_path(output_path)),
        "status_path": _wide_literal(_windows_z_path(status_path)),
    }
    for key, prefix in (
        ("constructor.parameters", "constructor_parameters"),
        ("constructor.attributes", "constructor_attributes"),
        ("constructor.impl_attributes", "constructor_impl_attributes"),
        ("method.impl_attributes", "method_impl_attributes"),
    ):
        operation = binding["concrete_operations"][key]
        values[f"{prefix}_pointer"] = operation["pointer"]
        values[f"{prefix}_metadata"] = operation["metadata"]
    for key, prefix in (
        ("method.from_handle", "method_from_handle"),
        ("method.parameters", "method_parameters"),
        ("method.return_type", "method_return"),
        ("method.attributes", "method_attributes"),
        ("member.metadata_token", "metadata_token"),
        ("parameter.name", "parameter_name"),
        ("parameter.type", "parameter_type"),
        ("parameter.is_in", "parameter_in"),
        ("parameter.is_out", "parameter_out"),
        ("parameter.is_optional", "parameter_optional"),
    ):
        values[f"{prefix}_pointer"] = operations[key]["pointer"]
        values[f"{prefix}_metadata"] = operations[key]["metadata"]
    return attach_raw_parameter_name_capture(
        _COLLECTOR_TEMPLATE.substitute(values),
        creation_filetime=binding.get("creation_filetime"),
        output_path=output_path.with_name("runtime-method-raw-parameters.private.bin"),
    )


def prepare_runtime_method_detail_inventory(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    native_inventory: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    method_name_receipt: Path,
    method_name_observation: Path,
    runtime_inventory_dispatch: Path | None,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    current_process = current_runtime_process_binding()
    if current_process is None:
        raise AcquisitionError(
            "lossless method-name capture requires current process binding; "
            "use capture-fresh-inventory"
        )
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        native_inventory=native_inventory,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        method_name_receipt=method_name_receipt,
        method_name_observation=method_name_observation,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
    )
    if (binding["process_id"] != current_process[0] or
        not same_executable_path(binary, current_process[2])):
        raise AcquisitionError("method detail source process differs from current binding")
    binding["creation_filetime"] = current_process[1]
    output_path = output_dir / "runtime-method-detail.private.bin"
    raw_parameter_path = output_dir / "runtime-method-raw-parameters.private.bin"
    raw_names_path = output_dir / "runtime-method-raw-names.private.bin"
    status_path = output_dir / "runtime-method-detail-status.private.json"
    model_path = output_dir / "runtime-method-detail.private.json"
    plan_path = output_dir / "runtime-method-detail-plan.private.json"
    build_dir = _owner_directory(output_dir / "build-method-detail")
    source_path = build_dir / "runtime-method-detail.c"
    injector_source_path = build_dir / "runtime-method-detail-injector.c"
    injector_path = build_dir / "alpha-runtime-method-detail-injector.exe"
    for stale in (output_path, status_path, model_path, raw_parameter_path, raw_names_path):
        stale.unlink(missing_ok=True)
    _private_text(
        source_path,
        runtime_method_detail_inventory_source(
            binding=binding,
            output_path=output_path,
            status_path=status_path,
        ),
    )
    _private_text(injector_source_path, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-method-detail-"
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
            label="runtime method detail collector",
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
            label="runtime method detail injector",
            source_path=injector_source_path,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_METHOD_DETAIL_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(Path(binary).expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "creation_filetime": binding["creation_filetime"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            "reflection_semantics": binding["semantics"],
            "native_inventory": binding["native_inventory"],
            "type_identity_model": binding["type_identity_model"],
            "type_identity_inventory": binding["type_identity_inventory"],
            "type_identity_plan": binding["type_identity_plan"],
            "type_identity_status": binding["type_identity_status"],
            "method_name_receipt": binding["method_name_receipt"],
            "method_name_observation": binding[
                "method_name_observation"
            ],
            "snapshot": binding["snapshot"],
            "class_model": binding["class_model"],
        },
        "concrete_semantics": binding["concrete_semantics_evidence"],
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "raw_parameter_names_path": str(raw_parameter_path),
        "raw_names_output_path": str(raw_names_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "contract": {
            "type_count": binding["type_count"],
            "method_count": binding["method_count"],
            "method_record_bytes": RUNTIME_METHOD_DETAIL_METHOD.size,
            "parameter_record_bytes": RUNTIME_METHOD_DETAIL_PARAMETER.size,
            "metadata_token_rid_base": binding["type_token_rid_base"],
            "method_parameter_count_byte_offset_owner_only": binding[
                "arity_offset"
            ],
            "all_parameters_required": True,
            "all_names_required": True,
            "lossless_raw_names_required": True,
            "all_method_tokens_runtime_observed": True,
            "parameter_tokens_reconstructed_from_definition_order": True,
            "parameter_token_rid_base_cross_table_validated": True,
            "all_method_implementation_attributes_required": True,
            "runtime_layout_revalidation_required": True,
        },
        "policy": {
            "same_process_required": True,
            "current_executable_sha256_embedded": True,
            "current_runtime_semantics_embedded": True,
            "runtime_object_layout_live_derived": True,
            "raw_pointers_owner_only": True,
            "saved_member_detail_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_METHOD_DETAIL_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "method_count": binding["method_count"],
        "policy": plan["policy"],
    }


def _validate_capture(
    *, plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = Path(plan["output_path"])
    raw = output_path.read_bytes()
    if len(raw) < RUNTIME_METHOD_DETAIL_HEADER.size:
        raise AcquisitionError("runtime method detail output is truncated")
    header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(raw)
    method_count = plan["contract"]["method_count"]
    parameter_count = header[6]
    string_bytes = header[7]
    records_end = (
        RUNTIME_METHOD_DETAIL_HEADER.size
        + method_count * RUNTIME_METHOD_DETAIL_METHOD.size
        + parameter_count * RUNTIME_METHOD_DETAIL_PARAMETER.size
    )
    header_valid = (
        header[0] == RUNTIME_METHOD_DETAIL_MAGIC
        and header[1] == RUNTIME_METHOD_DETAIL_VERSION
        and header[2] == RUNTIME_METHOD_DETAIL_HEADER.size
        and header[3] == RUNTIME_METHOD_DETAIL_METHOD.size
        and header[4] == RUNTIME_METHOD_DETAIL_PARAMETER.size
        and header[5] == method_count
        and parameter_count > 0
        and header[8] == plan["target"]["image_base_owner_only"]
        and header[9] == plan["target"]["image_bytes"]
        and 2 <= header[10] < 16
        and header[11] == 0
        and _digest(header[12], label="output executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[13], label="output native inventory")
        == plan["inputs"]["native_inventory"]["sha256"]
        and _digest(header[14], label="output type identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(header[15], label="output method names")
        == plan["inputs"]["method_name_observation"]["sha256"]
        and records_end + string_bytes == len(raw)
    )
    methods_position = RUNTIME_METHOD_DETAIL_HEADER.size
    parameters_position = (
        methods_position + method_count * RUNTIME_METHOD_DETAIL_METHOD.size
    )
    method_rows_valid = header_valid
    parameter_total = 0
    tokens: set[int] = set()
    method_token_rid_base: int | None = None
    synthetic_method_names = 0
    nonzero_impl_attributes = 0


    method_available = max(
        0,
        (len(raw) - methods_position) // RUNTIME_METHOD_DETAIL_METHOD.size,
    )
    method_rows = RUNTIME_METHOD_DETAIL_METHOD.iter_unpack(
        memoryview(raw)[
            methods_position :
            methods_position
            + min(method_count, method_available)
            * RUNTIME_METHOD_DETAIL_METHOD.size
        ]
    )
    method_starts: list[int] = []
    method_counts: list[int] = []
    index = -1
    for index, row in enumerate(method_rows):
        (
            definition_index,
            method_index,
            metadata_pointer,
            function_pointer,
            return_descriptor,
            attributes,
            impl_attributes,
            token,
            slot,
            flags,
            count,
            start,
            name_offset,
        ) = row
        candidate_rid_base = (token & 0x00FFFFFF) - index
        if method_token_rid_base is None:
            method_token_rid_base = candidate_rid_base
        token_relation_valid = (
            method_token_rid_base in (0, 1)
            and candidate_rid_base == method_token_rid_base
        )
        if (
            definition_index >= plan["contract"]["type_count"]
            or method_index != index
            or not metadata_pointer
            or (not return_descriptor and not flags & METHOD_DETAIL_CONSTRUCTOR)
            or (return_descriptor and flags & METHOD_DETAIL_CONSTRUCTOR)
            or attributes > 0xFFFF
            or impl_attributes > 0xFFFF
            or token >> 24 != 0x06
            or not token_relation_valid
            or token in tokens
            or (
                slot > 0xFFFF
                and not (
                    slot == 0xFFFFFFFF
                    and status.get("method_slot_layout_resolved") is False
                )
            )
            or flags & ~METHOD_DETAIL_CONSTRUCTOR
            or start != parameter_total
            or name_offset < records_end
            or name_offset >= len(raw)
        ):
            method_rows_valid = False
            break
        tokens.add(token)
        nonzero_impl_attributes += bool(impl_attributes)
        parameter_total += count
        method_starts.append(start)
        method_counts.append(count)
        end = raw.find(b"\x00", name_offset, min(len(raw), name_offset + 80))
        if end < 0:
            end = min(len(raw), name_offset + 80)
        if raw[name_offset:end].startswith(b"EmptyMethod_"):
            synthetic_method_names += 1
        if function_pointer and function_pointer & 1:
            method_rows_valid = False
            break
    else:
        if index != method_count - 1:


            RUNTIME_METHOD_DETAIL_METHOD.unpack_from(
                raw,
                methods_position + (index + 1) * RUNTIME_METHOD_DETAIL_METHOD.size,
            )
    parameter_rows_valid = method_rows_valid and parameter_total == parameter_count
    synthetic_parameter_names = 0
    parameter_tokens: set[int] = set()
    if parameter_rows_valid:


        parameter_available = max(
            0,
            (len(raw) - parameters_position)
            // RUNTIME_METHOD_DETAIL_PARAMETER.size,
        )
        parameter_rows = RUNTIME_METHOD_DETAIL_PARAMETER.iter_unpack(
            memoryview(raw)[
                parameters_position :
                parameters_position
                + min(parameter_count, parameter_available)
                * RUNTIME_METHOD_DETAIL_PARAMETER.size
            ]
        )
        expected_method = 0
        expected_position = 0
        index = -1
        for index, row in enumerate(parameter_rows):
            (
                method_index,
                position,
                descriptor,
                attributes,
                flags,
                name_bytes,
                reserved,
                name_offset,
            ) = row
            while expected_method < method_count:
                if index < method_starts[expected_method] + method_counts[expected_method]:
                    break
                expected_method += 1
                expected_position = 0
            if (
                method_index != expected_method
                or position != expected_position
                or not descriptor
                or attributes > 0xFFFF
                or bool(attributes & 0x1) != bool(flags & PARAMETER_DETAIL_IN)
                or bool(attributes & 0x2) != bool(flags & PARAMETER_DETAIL_OUT)
                or bool(attributes & 0x10) != bool(
                    flags & PARAMETER_DETAIL_OPTIONAL
                )
                or flags & ~(
                    PARAMETER_DETAIL_IN
                    | PARAMETER_DETAIL_OUT
                    | PARAMETER_DETAIL_OPTIONAL
                )
                or not name_bytes
                or name_bytes > 16_384
                or reserved >> 24 != 0x08
                or method_token_rid_base not in (0, 1)
                or (reserved & 0x00FFFFFF)
                != index + method_token_rid_base
                or reserved in parameter_tokens
                or name_offset < records_end
                or name_offset + name_bytes > len(raw)
            ):
                parameter_rows_valid = False
                break
            parameter_tokens.add(reserved)
            name = raw[name_offset : name_offset + name_bytes]
            try:
                name.decode("utf-8")
            except UnicodeDecodeError:
                parameter_rows_valid = False
                break
            if name.startswith(b"EmptyParameter_"):
                synthetic_parameter_names += 1
            expected_position += 1
        else:
            if index != parameter_count - 1:


                RUNTIME_METHOD_DETAIL_PARAMETER.unpack_from(
                    raw,
                    parameters_position
                    + (index + 1) * RUNTIME_METHOD_DETAIL_PARAMETER.size,
                )
    counts = {
        "method_count": method_count,
        "parameter_count": parameter_count,
        "string_bytes": string_bytes,
        "display_placeholder_prefix_method_count": synthetic_method_names,
        "display_placeholder_prefix_parameter_count": synthetic_parameter_names,
        "metadata_token_count": len(tokens),
        "parameter_metadata_token_count": len(parameter_tokens),
        "metadata_token_rid_base": method_token_rid_base,
        "nonzero_impl_attribute_count": nonzero_impl_attributes,
    }
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_METHOD_DETAIL_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "same_process": status.get("process_id")
        == plan["target"]["process_id"],
        "header_bound": header_valid,
        "all_methods_captured": status.get("completed_method_count")
        == method_count,
        "all_parameters_captured": status.get(
            "completed_parameter_count"
        )
        == parameter_count,
        "method_rows_valid": method_rows_valid,
        "parameter_rows_valid": parameter_rows_valid,
        "metadata_tokens_unique": len(tokens) == method_count,
        "metadata_token_rid_base_current_runtime_derived": (
            method_token_rid_base in (0, 1)
            and status.get("method_token_rid_base")
            == method_token_rid_base
            and plan["contract"]["metadata_token_rid_base"]
            == method_token_rid_base
        ),
        "parameter_metadata_tokens_unique": len(parameter_tokens)
        == parameter_count,
        "parameter_metadata_tokens_definition_order_exact": (
            len(parameter_tokens) == parameter_count
            and method_token_rid_base in (0, 1)
        ),
        "all_method_implementation_attributes_captured": status.get(
            "method_impl_attributes_captured"
        ) is True,
        "method_layout_offsets_bound_to_current_runtime": (
            type(status.get("method_attribute_offset_owner_only")) is int
            and type(status.get("method_impl_attribute_offset_owner_only"))
            is int
            and type(status.get("method_slot_offset_owner_only")) is int
            and type(status.get("method_layout_sample_count_owner_only")) is int
            and status["method_layout_sample_count_owner_only"] >= 16
            and (
                (
                    status.get("method_slot_layout_resolved", True) is True
                    and plan["contract"][
                        "method_parameter_count_byte_offset_owner_only"
                    ] >= 6
                    and status["method_attribute_offset_owner_only"]
                    == plan["contract"][
                        "method_parameter_count_byte_offset_owner_only"
                    ] - 2
                    and status["method_impl_attribute_offset_owner_only"]
                    == plan["contract"][
                        "method_parameter_count_byte_offset_owner_only"
                    ] - 4
                    and status["method_slot_offset_owner_only"]
                    == plan["contract"][
                        "method_parameter_count_byte_offset_owner_only"
                    ] - 6
                )
                or (
                    status.get("method_slot_layout_resolved") is False
                    and status.get(
                        "method_attribute_support_count_owner_only"
                    )
                    == status["method_layout_sample_count_owner_only"]
                    and status.get(
                        "method_impl_attribute_support_count_owner_only"
                    )
                    == status["method_layout_sample_count_owner_only"]
                    and status.get(
                        "method_parameter_count_support_count_owner_only"
                    )
                    == status["method_layout_sample_count_owner_only"]
                    and status["method_impl_attribute_offset_owner_only"]
                    == status["method_attribute_offset_owner_only"] + 2
                )
                or (
                    status.get("method_slot_layout_resolved") is True
                    and status.get(
                        "method_attribute_support_count_owner_only"
                    )
                    == status["method_layout_sample_count_owner_only"]
                    and status.get(
                        "method_impl_attribute_support_count_owner_only"
                    )
                    == status["method_layout_sample_count_owner_only"]
                    and status.get(
                        "method_parameter_count_support_count_owner_only"
                    )
                    == status["method_layout_sample_count_owner_only"]
                    and status["method_impl_attribute_offset_owner_only"]
                    == status["method_attribute_offset_owner_only"] + 2
                    and status["method_slot_offset_owner_only"]
                    == plan["contract"][
                        "method_parameter_count_byte_offset_owner_only"
                    ] - 2
                    and type(status.get(
                        "method_slot_absent_sample_count_owner_only"
                    )) is int
                    and type(status.get(
                        "method_slot_present_sample_count_owner_only"
                    )) is int
                    and status[
                        "method_slot_absent_sample_count_owner_only"
                    ] > 0
                    and status[
                        "method_slot_present_sample_count_owner_only"
                    ] > 0
                    and status[
                        "method_slot_absent_sample_count_owner_only"
                    ] + status[
                        "method_slot_present_sample_count_owner_only"
                    ] == status["method_layout_sample_count_owner_only"]
                )
            )
        ),
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        )
        is True,
        "saved_member_detail_absent": status.get(
            "saved_member_detail_used"
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


def finalize_runtime_method_detail_inventory(
    *, output_dir: Path
) -> dict[str, Any]:

    output_dir = _owner_directory(output_dir)
    plan_path = output_dir / "runtime-method-detail-plan.private.json"
    status_path = output_dir / "runtime-method-detail-status.private.json"
    if not plan_path.is_file() or not status_path.is_file():
        raise AcquisitionError(
            "runtime method detail completed capture is unavailable"
        )
    plan = read_json(plan_path)
    status = read_json(status_path)
    if (
        plan.get("schema") != RUNTIME_METHOD_DETAIL_PLAN_SCHEMA
        or status.get("status") != "complete"
    ):
        raise AcquisitionError(
            "runtime method detail completed capture is invalid "
            f"(status={status.get('status')})"
        )
    output_path = Path(plan["output_path"])
    if not output_path.is_file():
        raise AcquisitionError("runtime method detail output is unavailable")
    counts, checks = _validate_capture(plan=plan, status=status)
    if not all(checks.values()):
        failed = sorted(key for key, value in checks.items() if not value)
        raise AcquisitionError(
            "runtime method detail validation failed: " + ", ".join(failed)
        )
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    if (plan.get("contract", {}).get("lossless_raw_names_required") is not True or
        not isinstance(plan.get("raw_parameter_names_path"), str) or
        not isinstance(plan.get("raw_names_output_path"), str)):
        raise AcquisitionError("method detail capture has no lossless raw-name evidence")
    _seal_runtime_output(Path(plan["raw_parameter_names_path"]))
    raw_names = finalize_raw_method_parameter_names(
        plan=plan, output_path=Path(plan["raw_names_output_path"])
    )
    checks.update(raw_names["checks"])
    counts.update({key: value for key, value in raw_names["counts"].items()
                   if key not in ("method", "parameter")})
    model = {
        "schema": RUNTIME_METHOD_DETAIL_SCHEMA,
        "status": "runtime-validated",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"],
            "process_id": plan["target"]["process_id"],
            "creation_filetime": plan["target"]["creation_filetime"],
        },
        "inputs": plan["inputs"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "runtime_layout_owner_only": {
            key: value
            for key, value in status.items()
            if key.endswith("_owner_only")
        },
        "checks": checks,
        "raw_names": raw_names,
        "metadata_complete": False,
        "owner_only": True,
    }
    model_path = Path(plan["model_path"])
    _private_json(model_path, model)
    return {
        "schema": RUNTIME_METHOD_DETAIL_SCHEMA,
        "status": "runtime-validated",
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "inventory": model["inventory"],
    }


def capture_runtime_method_detail_inventory(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    native_inventory: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    method_name_receipt: Path,
    method_name_observation: Path,
    runtime_inventory_dispatch: Path | None,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 1800.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_method_detail_inventory(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        native_inventory=native_inventory,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        method_name_receipt=method_name_receipt,
        method_name_observation=method_name_observation,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-method-detail-plan.private.json"
    plan = read_json(plan_path)
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError("runtime method detail Wine is unavailable")
    from alpha.c04 import RuntimeProcessLifetimeGuard
    with RuntimeProcessLifetimeGuard(
        identity=plan["target"], wine=wine, wineprefix=wineprefix,
        build_dir=output_dir / "build-process-lifetime", compiler=compiler,
    ) as guard:
        return _capture_prepared_runtime_method_details(
            plan=plan, output_dir=output_dir, wine=wine, wineprefix=wineprefix,
            timeout=timeout, guard=guard,
        )


def _capture_prepared_runtime_method_details(*, plan, output_dir, wine, wineprefix, timeout, guard):
    guard.assert_alive()
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
            "runtime method detail injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-method-detail-injector.private.log",
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
        raise AcquisitionError("runtime method detail injection failed")
    guard.assert_alive()
    deadline = time.monotonic() + timeout
    status_path = Path(plan["status_path"])
    status: dict[str, Any] | None = None
    stall_seconds = 180.0
    last_progress = time.monotonic()
    last_stamp = None
    while time.monotonic() < deadline:
        guard.assert_alive()
        if status_path.is_file():
            stamp = status_path.stat().st_mtime
            if last_stamp != stamp:
                last_stamp = stamp
                last_progress = time.monotonic()
            from alpha.p14 import read_runtime_progress
            candidate = read_runtime_progress(status_path)
            if (isinstance(candidate, dict) and candidate.get("status") and
                candidate["status"] not in {"starting", "inputs_verified", "capturing",
                                             "waiting_for_main_thread", "writing"}):
                status = candidate
                break
            if time.monotonic() - last_progress > stall_seconds:
                raise AcquisitionError("runtime method detail capture timed out")
        time.sleep(0.2)
    if status is None:
        raise AcquisitionError("runtime method detail capture timed out")
    _seal_runtime_output(status_path)
    if isinstance(plan.get("raw_parameter_names_path"), str):
        _seal_runtime_output(Path(plan["raw_parameter_names_path"]))
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime method detail capture failed "
            f"(status={status.get('status')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    guard.assert_alive()
    result = finalize_runtime_method_detail_inventory(output_dir=output_dir)
    guard.assert_alive()
    return result
