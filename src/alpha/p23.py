from alpha.h02 import windows_run as _host_run

import json
import os
import stat
import struct
import subprocess
import time
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
from alpha.h04 import MemorySnapshot
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p02 import derive_current_store
from alpha.p16 import derive_member_attribute_fill_operations
from alpha.c07 import RUNTIME_NATIVE_SEMANTICS_SCHEMA, _load_types_and_methods
from alpha.c01 import current_runtime_process_binding
from alpha.c04 import RuntimeProcessLifetimeGuard
from alpha.p14 import read_runtime_progress
from alpha.c04 import attach_raw_member_names, finalize_raw_member_names
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_MEMBER_HEADER, _NATIVE_MEMBER_MAGIC, _NATIVE_MEMBER_RECORD, _NATIVE_MEMBER_VERSION, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json


RUNTIME_NATIVE_MEMBER_DETAIL_PLAN_SCHEMA = (
    "alpha.runtime-native-member-detail-plan/v1"
)
RUNTIME_NATIVE_MEMBER_DETAIL_STATUS_SCHEMA = (
    "alpha.runtime-native-member-detail-status/v1"
)
RUNTIME_NATIVE_MEMBER_DETAIL_SCHEMA = (
    "alpha.runtime-native-member-detail-inventory/v1"
)
RUNTIME_NATIVE_MEMBER_DETAIL_MAGIC = b"ALPHAND1"
RUNTIME_NATIVE_MEMBER_DETAIL_VERSION = 1
RUNTIME_NATIVE_MEMBER_DETAIL_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQ64s64s64s64s"
)
RUNTIME_NATIVE_MEMBER_DETAIL_FIELD = struct.Struct("<IIQQqIIIIQ")
RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY = struct.Struct("<IIQQQIIIIQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime native member detail {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime native member detail {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime native member detail {label} digest is invalid"
        )
    return value


def _codec(model: dict[str, Any], *path: str) -> dict[str, Any]:
    value: Any = model
    for key in path:
        value = value.get(key) if isinstance(value, dict) else None
    if not isinstance(value, dict):
        raise AcquisitionError(
            "runtime native member detail codec is unavailable"
        )
    return value


def _field_type_object_qword(
    semantics: dict[str, Any],
    current_store: dict[str, Any],
    *,
    attribute_offset: int,
) -> int:

    offset = current_store.get("candidate", {}).get("object_field_offset")
    if (
        current_store.get("candidate_count") != 1
        or type(offset) is not int
        or offset < 0
        or offset % 8
        or offset // 8 > 0xFFFFFFFF
        or current_store.get("attributes", {}).get("object_attribute_offset")
        != attribute_offset
    ):
        raise AcquisitionError("runtime native member detail field accessor code differs")
    evidence = [
        row for row in semantics.get("object_field_evidence", [])
        if isinstance(row, dict) and row.get("operation_key") == "field.type"
    ]
    support = (
        evidence[0].get("support_by_field", {}).get(str(offset // 8))
        if len(evidence) == 1 else None
    )
    if type(support) is not int or support <= 0:
        raise AcquisitionError(
            "runtime native member detail code-derived field type slot is unobserved"
        )
    return offset // 8


def _replay_field_type_object_layout(plan: dict[str, Any]) -> dict[str, Any]:
    from alpha.c04 import _verify_files

    inputs = plan["inputs"]
    binary = Path(plan["target"]["executable_path"])
    sources = dict(inputs, binary=file_identity(binary))
    if sources["binary"]["sha256"] != plan["target"]["executable_sha256"]:
        raise AcquisitionError("member field accessor executable changed")
    _verify_files(sources)
    semantics = read_json(Path(inputs["semantics"]["path"]))
    types, _ = _load_types_and_methods(
        Path(inputs["native_inventory"]["path"]),
        executable_sha256=plan["target"]["executable_sha256"],
        expected_identity=inputs["native_inventory"],
    )
    with MemorySnapshot(Path(inputs["runtime_snapshot"]["path"])) as snapshot:
        current = derive_current_store(
            binary=binary, semantics=semantics, types=types, snapshot=snapshot,
        )
    if json.dumps(current, sort_keys=True) != json.dumps(
        plan.get("field_type_store_current_code"), sort_keys=True
    ):
        raise AcquisitionError("member field accessor code replay differs")
    slot = _field_type_object_qword(
        semantics, current, attribute_offset=plan["contract"].get("field_attribute_offset"),
    )
    if slot != plan["contract"].get("field_type_object_qword"):
        raise AcquisitionError("member field accessor collector slot differs")
    _verify_files(sources)
    return current


def _binding(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    native_semantics_model: Path,
    native_inventory: Path,
    native_member_inventory: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    runtime_inventory_dispatch: Path | None,
) -> dict[str, Any]:


    del runtime_inventory_dispatch
    binary = binary.expanduser().resolve()
    identity = file_identity(binary)
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantics"
    )
    native_semantics_path = _owner_file(
        native_semantics_model, label="native semantics"
    )
    native_path = _owner_file(native_inventory, label="native inventory")
    member_path = _owner_file(
        native_member_inventory, label="native member inventory"
    )
    type_model_path = _owner_file(
        type_identity_model, label="type identity model"
    )
    type_inventory_path = _owner_file(
        type_identity_inventory, label="type identity inventory"
    )
    semantics = read_json(semantics_path)
    native_semantics = read_json(native_semantics_path)
    type_model = read_json(type_model_path)
    if (
        not isinstance(semantics, dict)
        or semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary", {}).get("sha256") != identity["sha256"]
        or semantics.get("checks", {}).get("all_operations_resolved")
        is not True
        or semantics.get("checks", {}).get(
            "direct_dword_getters_semantically_unique"
        )
        is not True
        or semantics.get("checks", {}).get(
            "parameter_flag_observations_complete"
        )
        is not True
        or semantics.get("behavior_evidence", {}).get(
            "fresh_runtime_observation"
        )
        is not True
    ):
        raise AcquisitionError(
            "runtime native member detail reflection binding is stale"
        )
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
    }
    field_from_handle = operations.get("field.from_handle")
    if (
        not isinstance(field_from_handle, dict)
        or field_from_handle.get("semantic_identity_resolved") is not True
        or not isinstance(field_from_handle.get("method_pointer"), int)
        or field_from_handle["method_pointer"] <= 0
        or not isinstance(field_from_handle.get("metadata_pointer"), int)
        or field_from_handle["metadata_pointer"] <= 0
    ):
        raise AcquisitionError(
            "runtime native member detail field resolver is unavailable"
        )
    field_type_operation = operations.get("field.type")
    type_handle_operation = operations.get("type.handle")
    type_from_handle_operation = operations.get("type.from_handle")
    property_from_handle_operation = operations.get("property.from_handle")
    property_name_operation = operations.get("property.name")
    property_getter_operation = operations.get("property.getter")
    property_setter_operation = operations.get("property.setter")
    metadata_token_operation = operations.get("member.metadata_token")
    if any(
        not isinstance(operation, dict)
        or operation.get("semantic_identity_resolved") is not True
        or not isinstance(operation.get("method_pointer"), int)
        or operation["method_pointer"] <= 0
        or not isinstance(operation.get("metadata_pointer"), int)
        or operation["metadata_pointer"] <= 0
        for operation in (
            field_type_operation,
            type_handle_operation,
            type_from_handle_operation,
            property_from_handle_operation,
            property_name_operation,
            property_getter_operation,
            property_setter_operation,
            metadata_token_operation,
        )
    ):
        raise AcquisitionError(
            "runtime native member detail direct field type operations are unavailable"
        )
    type_handle_evidence = next(
        (
            row
            for row in semantics.get("native_type_descriptor_evidence", [])
            if isinstance(row, dict)
            and row.get("operation_key") == "type.handle"
        ),
        None,
    )
    type_handle_object_qword = (
        type_handle_evidence.get("selected_field_qword")
        if isinstance(type_handle_evidence, dict)
        else None
    )
    if (
        not isinstance(type_handle_object_qword, int)
        or not 2 <= type_handle_object_qword < 64
        or type_handle_evidence.get("selected_field_support", 0) < 128
    ):
        raise AcquisitionError(
            "runtime native member detail type handle object layout is unavailable"
        )
    direct_fields = [
        row
        for row in semantics.get("direct_dword_evidence", [])
        if isinstance(row, dict)
        and row.get("operation_key") == "field.attributes"
    ]
    if len(direct_fields) != 1:
        raise AcquisitionError(
            "runtime native member detail field attribute layout is absent"
        )
    field_attribute_offset = direct_fields[0].get("attribute_byte_offset")
    if (
        not isinstance(field_attribute_offset, int)
        or not 16 <= field_attribute_offset < 256
        or direct_fields[0].get("distinct_value_count", 0) < 8
    ):
        raise AcquisitionError(
            "runtime native member detail field attribute layout is invalid"
        )
    if (
        not isinstance(native_semantics, dict)
        or native_semantics.get("schema") != RUNTIME_NATIVE_SEMANTICS_SCHEMA
        or native_semantics.get("binary", {}).get("sha256")
        != identity["sha256"]
        or native_semantics.get("status") != "partially-resolved"
        or native_semantics.get("checks", {}).get(
            "field_name_codec_structurally_unique"
        )
        is not True
        or native_semantics.get("checks", {}).get(
            "property_name_codec_structurally_unique"
        )
        is not True
        or native_semantics.get("checks", {}).get(
            "field_offset_decoder_closes_over_all_records"
        )
        is not True
        or native_semantics.get("checks", {}).get(
            "property_accessor_codecs_close_over_all_records"
        )
        is not True
        or native_semantics.get("checks", {}).get(
            "property_accessor_codecs_semantically_labeled"
        )
        is not True
        or native_semantics.get("checks", {}).get(
            "saved_reference_values_used"
        )
        is not False
        or native_semantics.get("inputs", {}).get("native_inventory", {}).get(
            "sha256"
        )
        != file_identity(native_path)["sha256"]
        or native_semantics.get("inputs", {})
        .get("native_member_inventory", {})
        .get("sha256")
        != file_identity(member_path)["sha256"]
    ):
        raise AcquisitionError(
            "runtime native member detail native semantics are stale"
        )
    field_name = _codec(native_semantics, "name_codecs", "field")
    property_name = _codec(native_semantics, "name_codecs", "property")
    field_offset = _codec(native_semantics, "field_offset_decoder")
    property_accessors = native_semantics.get("accessor_codecs", {}).get(
        "property"
    )
    property_accessor_by_role = {
        row.get("role"): row
        for row in property_accessors
        if isinstance(row, dict)
    } if isinstance(property_accessors, list) else {}
    if (
        field_name.get("operation") != "xor"
        or property_name.get("operation") not in {"xor", "add", "subtract"}
        or field_offset.get("operation", "xor")
        not in {"xor", "add", "subtract"}
        or set(property_accessor_by_role) != {"getter", "setter"}
        or any(
            row.get("operation") not in {"xor", "add", "subtract"}
            for row in property_accessor_by_role.values()
        )
    ):
        raise AcquisitionError(
            "runtime native member detail codec family is invalid"
        )
    numeric_codec_values = (
        field_name.get("slot"),
        field_name.get("key"),
        property_name.get("slot"),
        property_name.get("key"),
        property_accessor_by_role["getter"].get("slot"),
        property_accessor_by_role["getter"].get("key"),
        property_accessor_by_role["setter"].get("slot"),
        property_accessor_by_role["setter"].get("key"),
        field_offset.get("raw_dword_offset"),
        field_offset.get("xor_key"),
        field_offset.get("mask"),
        field_offset.get("adjustment"),
    )
    if any(not isinstance(value, int) for value in numeric_codec_values):
        raise AcquisitionError(
            "runtime native member detail codec values are invalid"
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
            "runtime native member detail type identity is stale"
        )
    type_plan_path = _owner_file(
        type_model_path.parent / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    type_plan = read_json(type_plan_path)
    process_id = type_plan.get("target", {}).get("process_id")
    image_base = type_plan.get("target", {}).get("image_base_owner_only")
    image_bytes = type_plan.get("target", {}).get("image_bytes")
    descriptor_offset = type_plan.get(
        "embedded_type_descriptor_offset_owner_only"
    )
    behavior_plan_record = type_model.get("inputs", {}).get("behavior_plan")
    if not isinstance(behavior_plan_record, dict):
        raise AcquisitionError(
            "runtime native member detail behavior plan is absent"
        )
    behavior_plan_path = _owner_file(
        Path(behavior_plan_record["path"]), label="behavior plan"
    )
    behavior_plan = read_json(behavior_plan_path)
    class_record = behavior_plan.get("inputs", {}).get("classes")
    if not isinstance(class_record, dict):
        raise AcquisitionError(
            "runtime native member detail class model is absent"
        )
    class_model_path = _owner_file(
        Path(class_record["path"]), label="class model"
    )
    class_model = read_json(class_model_path)
    snapshot_record = semantics.get("snapshot")
    if not isinstance(snapshot_record, dict) or not isinstance(
        snapshot_record.get("path"), str
    ):
        raise AcquisitionError(
            "runtime native member detail current snapshot is absent"
        )
    snapshot_path = _owner_file(
        Path(snapshot_record["path"]), label="runtime snapshot"
    )
    attribute_semantics = derive_member_attribute_fill_operations(
        semantics=semantics,
        class_model=class_model,
        snapshot_path=snapshot_path,
        expected_executable_sha256=identity["sha256"],
    )
    property_info_fill = attribute_semantics["operations"][
        "property.info_fill"
    ]
    arity_offset = semantics.get("method_parameter_count", {}).get(
        "selected_byte_offset"
    )
    expected_arities = {
        "field.from_handle": 2,
        "property.from_handle": 2,
        "property.name": 0,
        "property.getter": 1,
        "property.setter": 1,
        "member.metadata_token": 0,
    }
    operation_arities: dict[str, int] = {}
    if not isinstance(arity_offset, int) or arity_offset < 6:
        raise AcquisitionError(
            "runtime native member detail operation arity layout is unavailable"
        )
    native_types, _ = _load_types_and_methods(
        native_path,
        executable_sha256=identity["sha256"],
        expected_identity=native_semantics["inputs"]["native_inventory"],
    )
    with MemorySnapshot(snapshot_path) as snapshot:
        field_type_store = derive_current_store(
            binary=binary, semantics=semantics, types=native_types,
            snapshot=snapshot,
        )
        field_type_object_qword = _field_type_object_qword(
            semantics, field_type_store, attribute_offset=field_attribute_offset,
        )
        for key, expected_arity in expected_arities.items():
            operation = operations.get(key)
            metadata_pointer = (
                operation.get("metadata_pointer")
                if isinstance(operation, dict) else None
            )
            raw = snapshot.read(metadata_pointer, arity_offset + 1) if (
                isinstance(metadata_pointer, int) and metadata_pointer > 0
            ) else None
            if raw is None or raw[arity_offset] != expected_arity:
                raise AcquisitionError(
                    "runtime native member detail operation arity differs "
                    f"(operation={key})"
                )
            operation_arities[key] = raw[arity_offset]
    field_class = next(
        (
            row.get("class_pointer")
            for row in class_model.get("classes", [])
            if isinstance(row, dict)
            and row.get("runtime_owner") == "System.Reflection.MonoField"
        ),
        None,
    )
    property_class = next(
        (
            row.get("class_pointer")
            for row in class_model.get("classes", [])
            if isinstance(row, dict)
            and row.get("runtime_owner") == "System.Reflection.MonoProperty"
        ),
        None,
    )
    method_class = next(
        (
            row.get("class_pointer")
            for row in class_model.get("classes", [])
            if isinstance(row, dict)
            and row.get("runtime_owner") == "System.Reflection.MonoMethod"
        ),
        None,
    )
    type_class = next(
        (
            row.get("class_pointer")
            for row in class_model.get("classes", [])
            if isinstance(row, dict)
            and row.get("runtime_owner") == "System.RuntimeType"
        ),
        None,
    )
    if (
        not isinstance(process_id, int)
        or process_id <= 0
        or not isinstance(image_base, int)
        or image_base <= 0
        or not isinstance(image_bytes, int)
        or image_bytes <= 0
        or not isinstance(descriptor_offset, int)
        or descriptor_offset <= 0
        or not isinstance(field_class, int)
        or field_class <= 0
        or not isinstance(property_class, int)
        or property_class <= 0
        or not isinstance(method_class, int)
        or method_class <= 0
        or not isinstance(type_class, int)
        or type_class <= 0
        or not image_base <= property_info_fill["method_pointer"]
        < image_base + image_bytes
        or property_info_fill.get("semantic_identity_resolved") is not True
        or not isinstance(property_info_fill.get("request_mask"), int)
        or not 0 < property_info_fill["request_mask"] <= 0xFFFF
    ):
        raise AcquisitionError(
            "runtime native member detail live binding is invalid"
        )
    native_raw = native_path.read_bytes()
    member_raw = member_path.read_bytes()
    if (
        len(native_raw) < _NATIVE_INVENTORY_HEADER.size
        or len(member_raw) < _NATIVE_MEMBER_HEADER.size
    ):
        raise AcquisitionError(
            "runtime native member detail inventory is truncated"
        )
    native_header = _NATIVE_INVENTORY_HEADER.unpack_from(native_raw)
    member_header = _NATIVE_MEMBER_HEADER.unpack_from(member_raw)
    type_count = native_header[5]
    method_count = native_header[6]
    field_count, property_count, event_count = member_header[5:8]
    metadata_token_rid_base = type_model.get("counts", {}).get(
        "metadata_token_rid_base"
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
        or member_header[0] != _NATIVE_MEMBER_MAGIC
        or member_header[1] != _NATIVE_MEMBER_VERSION
        or member_header[2] != _NATIVE_MEMBER_RECORD.size
        or member_header[3] != type_count
        or member_header[4]
        or member_header[8] != image_bytes
        or _digest(member_header[9], label="member executable")
        != identity["sha256"]
        or field_count <= 0
        or property_count <= 0
        or event_count <= 0
        or metadata_token_rid_base not in (0, 1)
        or len(member_raw)
        != _NATIVE_MEMBER_HEADER.size
        + (field_count + property_count + event_count)
        * _NATIVE_MEMBER_RECORD.size
    ):
        raise AcquisitionError(
            "runtime native member detail inventory binding is invalid"
        )
    return {
        "binary": identity,
        "semantics": file_identity(semantics_path),
        "native_semantics": file_identity(native_semantics_path),
        "native_inventory": file_identity(native_path),
        "native_member_inventory": file_identity(member_path),
        "type_identity_model": file_identity(type_model_path),
        "type_identity_inventory": file_identity(type_inventory_path),
        "attribute_semantics": attribute_semantics,
        "field_type_store_current_code": field_type_store,
        "runtime_snapshot": file_identity(snapshot_path),
        "type_identity_plan": file_identity(type_plan_path),
        "class_model": file_identity(class_model_path),
        "process_id": process_id,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "descriptor_offset": descriptor_offset,
        "field_class": field_class,
        "property_class": property_class,
        "method_class": method_class,
        "type_class": type_class,
        "type_count": type_count,
        "method_count": method_count,
        "field_count": field_count,
        "property_count": property_count,
        "event_count": event_count,
        "metadata_token_rid_base": metadata_token_rid_base,
        "field_attribute_offset": field_attribute_offset,
        "field_from_handle": {
            "pointer": field_from_handle["method_pointer"],
            "metadata": field_from_handle["metadata_pointer"],
        },
        "field_type": {
            "pointer": field_type_operation["method_pointer"],
            "metadata": field_type_operation["metadata_pointer"],
            "object_qword": field_type_object_qword,
        },
        "type_handle": {
            "pointer": type_handle_operation["method_pointer"],
            "metadata": type_handle_operation["metadata_pointer"],
            "object_qword": type_handle_object_qword,
        },
        "type_from_handle": {
            "pointer": type_from_handle_operation["method_pointer"],
            "metadata": type_from_handle_operation["metadata_pointer"],
        },
        "property_from_handle": {
            "pointer": property_from_handle_operation["method_pointer"],
            "metadata": property_from_handle_operation["metadata_pointer"],
        },
        "property_name": {
            "pointer": property_name_operation["method_pointer"],
            "metadata": property_name_operation["metadata_pointer"],
        },
        "property_info_fill": {
            "pointer": property_info_fill["method_pointer"],
            "metadata": property_info_fill["metadata_pointer"],
            "request_mask": property_info_fill["request_mask"],
        },
        "operation_arities": operation_arities,
        "operation_arity_offset_owner_only": arity_offset,
        "property_getter": {
            "pointer": property_getter_operation["method_pointer"],
            "metadata": property_getter_operation["metadata_pointer"],
        },
        "property_setter": {
            "pointer": property_setter_operation["method_pointer"],
            "metadata": property_setter_operation["metadata_pointer"],
        },
        "metadata_token": {
            "pointer": metadata_token_operation["method_pointer"],
            "metadata": metadata_token_operation["metadata_pointer"],
        },
        "field_name": field_name,
        "property_name_codec": property_name,
        "property_accessors": property_accessor_by_role,
        "field_offset": field_offset,
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ALPHA_MAX_TEXT 16384u
#define ALPHA_FIELD_BATCH 2048u

typedef struct native_header {
    char magic[8];
    uint32_t version, type_record_bytes, method_record_bytes, reserved;
    uint64_t type_count, method_count, image_bytes;
    char executable_sha256[64], model_sha256[64];
    uint32_t layout[8];
} native_header;
typedef struct native_type {
    uint32_t definition_index, name_bytes;
    uint64_t flags, descriptor_rva, class_pointer, parent, declaring;
    uint32_t method_count, reserved;
    uint64_t method_start, name_offset;
} native_type;
typedef struct native_method {
    uint32_t definition_index, method_index;
    uint64_t metadata_pointer, method_pointer;
} native_method;
typedef struct member_header {
    char magic[8];
    uint32_t version, record_bytes, type_count, reserved;
    uint64_t field_count, property_count, event_count, image_bytes;
    char executable_sha256[64], materializer_sha256[64], helper_sha256[64];
    uint64_t field_rva;
    uint32_t field_offset, field_stride;
    uint64_t property_rva;
    uint32_t property_offset, property_stride;
    uint64_t event_rva;
    uint32_t event_offset, event_stride;
} member_header;
typedef struct member_record {
    uint32_t type_index, member_index;
    uint64_t pointer;
    uint32_t kind, stride;
    unsigned char payload[48];
} member_record;
typedef struct detail_header {
    char magic[8];
    uint32_t version, header_bytes, field_record_bytes, property_record_bytes;
    uint64_t field_count, property_count, string_bytes;
    uint64_t image_base, image_bytes, type_count, reserved;
    char executable_sha256[64], member_inventory_sha256[64];
    char type_identity_sha256[64], native_semantics_sha256[64];
} detail_header;
typedef struct detail_field {
    uint32_t type_index, member_index;
    uint64_t member_pointer, type_descriptor;
    int64_t offset;
    uint32_t attributes, metadata_token, name_bytes, flags;
    uint64_t name_offset;
} detail_field;
typedef struct detail_property {
    uint32_t type_index, member_index;
    uint64_t member_pointer, getter_pointer, setter_pointer;
    uint32_t metadata_token, name_bytes, flags, reserved;
    uint64_t name_offset;
} detail_property;

_Static_assert(sizeof(native_header) == $native_header_bytes, "native header");
_Static_assert(sizeof(native_type) == $native_type_bytes, "native type");
_Static_assert(sizeof(member_header) == $member_header_bytes, "member header");
_Static_assert(sizeof(member_record) == $member_record_bytes, "member record");
_Static_assert(sizeof(detail_header) == $detail_header_bytes, "detail header");
_Static_assert(sizeof(detail_field) == $detail_field_bytes, "detail field");
_Static_assert(sizeof(detail_property) == $detail_property_bytes, "detail property");

static const char executable_sha256[] = "$executable_sha256";
static const char member_inventory_sha256[] = "$member_sha256";
static const char type_identity_sha256[] = "$type_identity_sha256";
static const char native_semantics_sha256[] = "$native_semantics_sha256";
static const DWORD expected_process_id = ${process_id}u;
static const uintptr_t expected_image_base = ${image_base}ull;
static const uint64_t expected_image_bytes = ${image_bytes}ull;
static const uint64_t expected_type_count = ${type_count}ull;
static const uint64_t expected_field_count = ${field_count}ull;
static const uint64_t expected_property_count = ${property_count}ull;
static const uint64_t expected_method_count = ${method_count}ull;
static const uint32_t expected_metadata_token_rid_base =
    ${metadata_token_rid_base}u;
static const uint32_t descriptor_offset = ${descriptor_offset}u;
static const uintptr_t field_class = ${field_class}ull;
static const uintptr_t property_class = ${property_class}ull;
static const uintptr_t method_class = ${method_class}ull;
static const uintptr_t type_class = ${type_class}ull;
static const uint32_t field_attribute_offset = ${field_attribute_offset}u;
static const uintptr_t field_from_handle_pointer = ${field_from_handle_pointer}ull;
static const uintptr_t field_from_handle_metadata = ${field_from_handle_metadata}ull;
static const uint32_t field_name_slot = ${field_name_slot}u;
static const uint64_t field_name_key = ${field_name_key}ull;
static const uint32_t property_name_slot = ${property_name_slot}u;
static const uint64_t property_name_key = ${property_name_key}ull;
static const uint32_t property_name_operation = ${property_name_operation}u;
static const uint32_t property_getter_slot = ${property_getter_slot}u;
static const uint64_t property_getter_key = ${property_getter_key}ull;
static const uint32_t property_getter_operation = ${property_getter_operation}u;
static const uint32_t property_setter_slot = ${property_setter_slot}u;
static const uint64_t property_setter_key = ${property_setter_key}ull;
static const uint32_t property_setter_operation = ${property_setter_operation}u;
static const uintptr_t field_type_pointer = ${field_type_pointer}ull;
static const uintptr_t field_type_metadata = ${field_type_metadata}ull;
static const uint32_t field_type_object_qword = ${field_type_object_qword}u;
static const uintptr_t type_handle_pointer = ${type_handle_pointer}ull;
static const uintptr_t type_handle_metadata = ${type_handle_metadata}ull;
static const uint32_t type_handle_object_qword = ${type_handle_object_qword}u;
static const uintptr_t type_from_handle_pointer = ${type_from_handle_pointer}ull;
static const uintptr_t type_from_handle_metadata = ${type_from_handle_metadata}ull;
static const uintptr_t property_from_handle_pointer = ${property_from_handle_pointer}ull;
static const uintptr_t property_from_handle_metadata = ${property_from_handle_metadata}ull;
static const uintptr_t property_name_pointer = ${property_name_pointer}ull;
static const uintptr_t property_name_metadata = ${property_name_metadata}ull;
static const uintptr_t property_info_fill_pointer =
    ${property_info_fill_pointer}ull;
static const uintptr_t property_info_fill_metadata =
    ${property_info_fill_metadata}ull;
static const uint32_t property_info_request_mask =
    ${property_info_request_mask}u;
static const uintptr_t property_getter_pointer = ${property_getter_pointer}ull;
static const uintptr_t property_getter_metadata = ${property_getter_metadata}ull;
static const uintptr_t property_setter_pointer = ${property_setter_pointer}ull;
static const uintptr_t property_setter_metadata = ${property_setter_metadata}ull;
static const uintptr_t metadata_token_pointer = ${metadata_token_pointer}ull;
static const uintptr_t metadata_token_metadata = ${metadata_token_metadata}ull;
static const uint32_t field_offset_raw_offset = ${field_offset_raw_offset}u;
static const uint32_t field_offset_key = ${field_offset_key}u;
static const uint32_t field_offset_mask = ${field_offset_mask}u;
static const int32_t field_offset_adjustment = ${field_offset_adjustment};
static const uint32_t field_offset_operation = ${field_offset_operation}u;
static const wchar_t native_input_path[] = $native_path;
static const wchar_t member_input_path[] = $member_path;
static const wchar_t output_path[] = $output_path;
static const wchar_t status_path[] = $status_path;

typedef uintptr_t (*static_twoarg)(uintptr_t, uintptr_t, uintptr_t);
typedef uintptr_t (*static_onearg)(uintptr_t, uintptr_t);
typedef uintptr_t (*instance_noarg)(uintptr_t, uintptr_t);
typedef uintptr_t (*instance_boolarg)(uintptr_t, uint32_t, uintptr_t);
typedef uint32_t (*instance_dword)(uintptr_t, uintptr_t);
typedef void (*property_info_fill_fn)(
    uintptr_t, uintptr_t *, uint32_t, uintptr_t);
static unsigned char *native_data, *member_data;
static native_type *types;
static native_method *methods;
static member_record *members;
static detail_field *fields;
static detail_property *properties;
static char *strings;
static uint64_t string_bytes, string_capacity, field_index, property_index;
static uint64_t completed_fields, completed_properties;
static uint64_t synthetic_fields, synthetic_properties;
static uintptr_t *method_metadata;
static uint32_t property_info_name_qword = UINT32_MAX;
static uint32_t property_info_flags_offset = UINT32_MAX;
static uint64_t failure_index;
static uint32_t failure_kind;
static UINT message_id;
static WNDPROC original_proc;
static volatile LONG callback_complete;

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
static int object_class(uintptr_t object, uintptr_t expected) {
    uintptr_t observed = 0;
    if (!readable(object, sizeof(observed))) return 0;
    memcpy(&observed, (const void *)object, sizeof(observed));
    return observed == expected;
}
static uint32_t text_bytes(uintptr_t value) {
    if (!value) return 0;
    for (uint32_t index = 0; index <= ALPHA_MAX_TEXT; index++) {
        if (!readable(value + index, 1u)) return UINT32_MAX;
        if (!*(const unsigned char *)(value + index)) return index;
    }
    return UINT32_MAX;
}
static int append_text(const char *value, uint32_t bytes, uint64_t *offset) {
    if (!value || !bytes || string_bytes + bytes < string_bytes) return 0;
    uint64_t required = string_bytes + bytes;
    if (required > string_capacity) {
        uint64_t capacity = string_capacity ? string_capacity : 1024u * 1024u;
        while (capacity < required) capacity *= 2u;
        char *grown = (char *)realloc(strings, (SIZE_T)capacity);
        if (!grown) return 0;
        strings = grown;
        string_capacity = capacity;
    }
    *offset = string_bytes;
    memcpy(strings + string_bytes, value, bytes);
    string_bytes += bytes;
    return 1;
}
static int append_synthetic_name(
    uint32_t token, const char *prefix, uint32_t *bytes,
    uint64_t *offset, uint64_t *synthetic
) {
    char value[48];
    int written = snprintf(value, sizeof(value), "%s%X", prefix, token);
    if (written <= 0 || written >= (int)sizeof(value)) return 0;
    *bytes = (uint32_t)written;
    (*synthetic)++;
    return append_text(value, (uint32_t)written, offset);
}
static int append_native_name(
    uintptr_t pointer, uint32_t token, const char *prefix,
    uint32_t *bytes, uint64_t *offset, uint64_t *synthetic
) {
    uint32_t count = text_bytes(pointer);
    if (count == UINT32_MAX) return 0;
    if (count) {
        *bytes = count;
        return append_text((const char *)pointer, count, offset);
    }
    return append_synthetic_name(token, prefix, bytes, offset, synthetic);
}
static int append_managed_name(
    uintptr_t object, uint32_t token, const char *prefix,
    uint32_t *bytes, uint64_t *offset, uint64_t *synthetic
) {
    int32_t units = 0;
    if (!readable(object, 20u)) return 0;
    memcpy(&units, (const void *)(object + 16u), sizeof(units));
    if (!units)
        return append_synthetic_name(
            token, prefix, bytes, offset, synthetic);
    if (units < 0 || units > (int32_t)ALPHA_MAX_TEXT ||
        !readable(object + 20u, (SIZE_T)(uint32_t)units * 2u)) return 0;
    int required = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS,
        (const wchar_t *)(object + 20u), units, NULL, 0, NULL, NULL);
    if (required <= 0 || required > (int)ALPHA_MAX_TEXT) return 0;
    char *text = (char *)malloc((SIZE_T)required);
    if (!text) return 0;
    int written = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS,
        (const wchar_t *)(object + 20u), units, text, required, NULL, NULL);
    int ok = written == required && append_text(text, (uint32_t)required, offset);
    free(text); if (ok) *bytes = (uint32_t)required; return ok;
}
static int compare_pointer(const void *left, const void *right) {
    uintptr_t a = *(const uintptr_t *)left, b = *(const uintptr_t *)right;
    return a < b ? -1 : a > b ? 1 : 0;
}
static int known_method_metadata(uintptr_t value) {
    return value && bsearch(&value, method_metadata,
        (SIZE_T)expected_method_count, sizeof(uintptr_t), compare_pointer) != NULL;
}
static uint64_t decode_protected_value(
    uint64_t raw, uint64_t key, uint32_t operation
) {
    if (operation == 1u) return raw ^ key;
    if (operation == 2u) return raw - key;
    if (operation == 3u) return key - raw;
    return 0;
}
static uintptr_t method_object_metadata(uintptr_t object) {
    if (!object) return 0;
    instance_dword get_token = (instance_dword)metadata_token_pointer;
    uint32_t token = get_token(object, metadata_token_metadata);
    uint32_t rid = token & 0x00ffffffu;
    if ((token & 0xff000000u) != 0x06000000u ||
        rid < expected_metadata_token_rid_base ||
        (uint64_t)(rid - expected_metadata_token_rid_base) >=
            expected_method_count) return 0;
    return methods[rid - expected_metadata_token_rid_base].metadata_pointer;
}
static int managed_string_equal(uintptr_t left, uintptr_t right) {
    if (!left || !right || !readable(left + 16u, 4u) ||
        !readable(right + 16u, 4u)) return 0;
    int32_t a = 0, b = 0;
    memcpy(&a, (const void *)(left + 16u), 4u);
    memcpy(&b, (const void *)(right + 16u), 4u);
    return a >= 0 && a == b && a <= (int32_t)ALPHA_MAX_TEXT &&
        (!a || (readable(left + 20u, (SIZE_T)a * 2u) &&
        readable(right + 20u, (SIZE_T)a * 2u) &&
        !memcmp((const void *)(left + 20u), (const void *)(right + 20u),
            (SIZE_T)a * 2u)));
}
static int method_object_equal(uintptr_t left, uintptr_t right) {
    if (!left || !right || !readable(left, 8u) || !readable(right, 8u))
        return left == right;
    uintptr_t a = 0, b = 0;
    memcpy(&a, (const void *)left, 8u);
    memcpy(&b, (const void *)right, 8u);
    if (a != b) return 0;
    uintptr_t lm = method_object_metadata(left);
    return lm && lm == method_object_metadata(right);
}
static int property_info(
    uintptr_t object, uintptr_t name_object, uintptr_t getter_object,
    uintptr_t setter_object, uint32_t *attributes
) {
    property_info_fill_fn fill =
        (property_info_fill_fn)property_info_fill_pointer;
    uintptr_t info[16];
    memset(info, 0, sizeof(info));
    fill(object, info, property_info_request_mask, property_info_fill_metadata);
    if (property_info_name_qword == UINT32_MAX) {
        uint32_t candidate = UINT32_MAX, count = 0;
        for (uint32_t qword = 0; qword + 3u < 16u; qword++) {
            if (managed_string_equal(info[qword], name_object) &&
                method_object_equal(info[qword + 1u], getter_object) &&
                method_object_equal(info[qword + 2u], setter_object) &&
                (getter_object || setter_object)) {
                candidate = qword;
                count++;
            }
        }
        if (count != 1u) return 0;
        property_info_name_qword = candidate;
        property_info_flags_offset = (candidate + 3u) * sizeof(uintptr_t);
    }


    if (property_info_flags_offset + sizeof(uint32_t) > sizeof(info)) return 0;
    memcpy(attributes,
        (const unsigned char *)info + property_info_flags_offset,
        sizeof(*attributes));
    return *attributes <= UINT16_MAX;
}
static int read_file(const wchar_t *path, unsigned char **data, SIZE_T *bytes) {
    FILE *input = _wfopen(path, L"rb");
    if (!input || _fseeki64(input, 0, SEEK_END)) return 0;
    *bytes = (SIZE_T)_ftelli64(input);
    if (_fseeki64(input, 0, SEEK_SET)) { fclose(input); return 0; }
    *data = (unsigned char *)malloc(*bytes ? *bytes : 1u);
    int ok = *data && fread(*data, 1, *bytes, input) == *bytes;
    fclose(input);
    return ok;
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
    DWORD object_size = 0, received = 0;
    unsigned char *object = NULL, *buffer = NULL, digest[32];
    int ok = BCryptOpenAlgorithmProvider(&algorithm,
        BCRYPT_SHA256_ALGORITHM, NULL, 0) >= 0 &&
        BCryptGetProperty(algorithm, BCRYPT_OBJECT_LENGTH,
            (PUCHAR)&object_size, sizeof(object_size), &received, 0) >= 0;
    if (ok) object = HeapAlloc(GetProcessHeap(), 0, object_size);
    if (ok) buffer = HeapAlloc(GetProcessHeap(), 0, 1024u * 1024u);
    if (ok && (!object || !buffer)) ok = 0;
    if (ok && BCryptCreateHash(algorithm, &hash, object, object_size,
            NULL, 0, 0) < 0) ok = 0;
    while (ok) { DWORD count = 0;
        if (!ReadFile(input, buffer, 1024u * 1024u, &count, NULL)) { ok = 0; break; }
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

static int capture_field_batch(void) {
    static_twoarg from_handle = (static_twoarg)field_from_handle_pointer;
    instance_dword get_metadata_token =
        (instance_dword)metadata_token_pointer;
    uint64_t end = field_index + ALPHA_FIELD_BATCH;
    if (end > expected_field_count) end = expected_field_count;
    for (; field_index < end; field_index++) {
        member_record *source = &members[field_index];
        if (source->kind != 0u || source->type_index >= expected_type_count ||
            !source->pointer || !readable(source->pointer, 48u)) {
            failure_index = field_index + 1u; failure_kind = 1u; return 0;
        }
        uintptr_t owner = types[source->type_index].class_pointer + descriptor_offset;
        uintptr_t object = from_handle(
            source->pointer, owner, field_from_handle_metadata);
        if (!object_class(object, field_class) ||
            !readable(object, field_attribute_offset + sizeof(uint32_t))) {
            failure_index = field_index + 1u; failure_kind = 2u; return 0;
        }
        detail_field *target = &fields[field_index];
        target->type_index = source->type_index;
        target->member_index = source->member_index;
        target->member_pointer = source->pointer;
        uintptr_t raw_name = 0;
        memcpy(&raw_name, (const void *)(source->pointer +
            (uintptr_t)field_name_slot * sizeof(uintptr_t)), sizeof(raw_name));
        uintptr_t name_pointer = raw_name ^ field_name_key;
        uintptr_t type_object = 0;
        memcpy(&type_object, (const void *)(object +
            (uintptr_t)field_type_object_qword * sizeof(uintptr_t)),
            sizeof(type_object));
        if (!object_class(type_object, type_class)) {
            failure_index = field_index + 1u; failure_kind = 6u; return 0;
        }
        memcpy(&target->type_descriptor, (const void *)(type_object +
            (uintptr_t)type_handle_object_qword * sizeof(uintptr_t)),
            sizeof(target->type_descriptor));
        if (!readable(target->type_descriptor, 16u)) {
            failure_index = field_index + 1u; failure_kind = 3u; return 0;
        }
        uint32_t raw_offset = 0;
        memcpy(&raw_offset, (const void *)(source->pointer +
            field_offset_raw_offset), sizeof(raw_offset));
        uint32_t protected_offset = 0;
        if (field_offset_operation == 1u)
            protected_offset = (raw_offset ^ field_offset_key) &
                field_offset_mask;
        else if (field_offset_operation == 2u)
            protected_offset = (raw_offset + field_offset_key) &
                field_offset_mask;
        else if (field_offset_operation == 3u)
            protected_offset = (raw_offset - field_offset_key) &
                field_offset_mask;
        else {
            failure_index = field_index + 1u; failure_kind = 6u; return 0;
        }
        target->offset = (int64_t)protected_offset +
            field_offset_adjustment;
        memcpy(&target->attributes, (const void *)(object +
            field_attribute_offset), sizeof(target->attributes));
        target->metadata_token = get_metadata_token(
            object, metadata_token_metadata);
        uint32_t rid = target->metadata_token & 0x00ffffffu;
        if ((target->metadata_token & 0xff000000u) != 0x04000000u ||
            rid != field_index + expected_metadata_token_rid_base ||
            (uint64_t)rid > 0x00ffffffu) {
            failure_index = field_index + 1u; failure_kind = 7u; return 0;
        }
        if (!append_native_name(name_pointer, target->metadata_token,
                "EmptyField_", &target->name_bytes, &target->name_offset,
                &synthetic_fields)) {
            failure_index = field_index + 1u; failure_kind = 4u; return 0;
        }
        completed_fields++;
    }
    return 1;
}

static int capture_property_batch(void);
static volatile LONG current_request, request_sequence, callback_active;
static LRESULT CALLBACK window_proc(
    HWND window, UINT message, WPARAM wparam, LPARAM lparam
) {
    if (message != message_id) return CallWindowProcW(
        original_proc, window, message, wparam, lparam);
    LONG request = (LONG)wparam;
    if (!request || InterlockedCompareExchange(&current_request, 0, 0) != request ||
        InterlockedCompareExchange(&callback_active, 1, 0)) return 0;
    if (InterlockedCompareExchange(&current_request, 0, request) != request) {
        InterlockedExchange(&callback_active, 0); return 0;
    }
    int ok = field_index < expected_field_count
        ? capture_field_batch() : capture_property_batch();
    InterlockedExchange(&callback_complete, ok ? 1 : -1);
    InterlockedExchange(&callback_active, 0);
    return ok;
}
typedef struct window_selection { DWORD pid; HWND window; uint32_t count; } window_selection;
static BOOL CALLBACK select_window(HWND window, LPARAM value) {
    window_selection *selected = (window_selection *)(uintptr_t)value;
    DWORD pid = 0; RECT bounds;
    if (!IsWindowVisible(window) || GetWindow(window, GW_OWNER) ||
        !GetWindowRect(window, &bounds) || bounds.right <= bounds.left ||
        bounds.bottom <= bounds.top) return TRUE;
    GetWindowThreadProcessId(window, &pid);
    if (pid == selected->pid) { selected->window = window; selected->count++; }
    return TRUE;
}
static int dispatch_members(void) {
    window_selection selected = {0}; selected.pid = GetCurrentProcessId();
    SetLastError(0);
    if (!EnumWindows(select_window, (LPARAM)(uintptr_t)&selected)) {
        failure_kind = 10401u; failure_index = GetLastError(); return 0;
    }
    if (selected.count != 1 || !selected.window) {
        failure_kind = 10402u; failure_index = selected.count; return 0;
    }
    SetLastError(0);
    message_id = RegisterWindowMessageW(status_path);
    if (!message_id) {
        failure_kind = 10403u; failure_index = GetLastError(); return 0;
    }
    SetLastError(0); original_proc = (WNDPROC)(uintptr_t)SetWindowLongPtrW(
        selected.window, GWLP_WNDPROC, (LONG_PTR)(uintptr_t)window_proc);
    DWORD subclass_error = GetLastError();
    int ok = original_proc && subclass_error == ERROR_SUCCESS;
    if (!ok) { failure_kind = 10404u; failure_index = subclass_error; }
    uint32_t transient_failures = 0;
    while (ok && (field_index < expected_field_count ||
                  property_index < expected_property_count)) {
        DWORD_PTR result = 0; InterlockedExchange(&callback_complete, 0);
        uint64_t before_fields = field_index, before_properties = property_index;
        LONG request = InterlockedIncrement(&request_sequence);
        InterlockedExchange(&current_request, request);
        SetLastError(0);
        int dispatched = SendMessageTimeoutW(selected.window, message_id, (WPARAM)request, 0,
            SMTO_BLOCK, 60000, &result) != 0;
        DWORD dispatch_error = GetLastError();
        InterlockedExchange(&current_request, 0);


        for (uint32_t wait = 0;
             InterlockedCompareExchange(&callback_active, 0, 0) && wait < 2000u;
             wait++) Sleep(1);
        if (InterlockedCompareExchange(&callback_active, 0, 0)) {
            failure_kind = 10407u; ok = 0; break;
        }
        LONG callback = InterlockedCompareExchange(&callback_complete, 0, 0);
        if (callback == 1) {
            if (field_index <= before_fields && property_index <= before_properties) {
                failure_kind = 10408u; ok = 0; break;
            }
            transient_failures = 0;
        }
        else if (!dispatched && !callback && !failure_kind && transient_failures++ < 16u) {
            Sleep(250); continue;
        }
        else {
            if (!failure_kind) {
                failure_kind = dispatched ? 10406u : 10405u;
                failure_index = dispatched ? (uint64_t)(uint32_t)callback : dispatch_error;
            }
            ok = 0;
        }
    }
    InterlockedExchange(&current_request, 0);
    if (original_proc) SetWindowLongPtrW(selected.window, GWLP_WNDPROC,
        (LONG_PTR)(uintptr_t)original_proc);
    return ok;
}

static int capture_property_batch(void) {
    static_twoarg from_handle = (static_twoarg)property_from_handle_pointer;
    instance_noarg get_name = (instance_noarg)property_name_pointer;
    instance_boolarg get_getter =
        (instance_boolarg)property_getter_pointer;
    instance_boolarg get_setter =
        (instance_boolarg)property_setter_pointer;
    instance_dword get_metadata_token =
        (instance_dword)metadata_token_pointer;
    uint64_t end = property_index + ALPHA_FIELD_BATCH;
    if (end > expected_property_count) end = expected_property_count;
    for (; property_index < end; property_index++) {
        uint64_t index = property_index;
        member_record *source = members + expected_field_count + index;
        if (source->kind != 1u || source->type_index >= expected_type_count ||
            !source->pointer || !readable(source->pointer, 48u)) {
            failure_index = index + 1u; failure_kind = 10u; return 0;
        }
        detail_property *target = &properties[index];
        target->type_index = source->type_index;
        target->member_index = source->member_index;
        target->member_pointer = source->pointer;
        uintptr_t owner = types[source->type_index].class_pointer +
            descriptor_offset;
        uintptr_t object = from_handle(
            source->pointer, owner, property_from_handle_metadata);
        if (!object_class(object, property_class)) {
            failure_index = index + 1u; failure_kind = 14u; return 0;
        }
        uintptr_t name_object = get_name(object, property_name_metadata);
        uintptr_t getter_object = get_getter(
            object, 1u, property_getter_metadata);
        uintptr_t setter_object = get_setter(
            object, 1u, property_setter_metadata);
        uint64_t raw_name = 0, raw_getter = 0, raw_setter = 0;
        memcpy(&raw_name, source->payload +
            (uintptr_t)property_name_slot * sizeof(uint64_t),
            sizeof(raw_name));
        memcpy(&raw_getter, source->payload +
            (uintptr_t)property_getter_slot * sizeof(uint64_t),
            sizeof(raw_getter));
        memcpy(&raw_setter, source->payload +
            (uintptr_t)property_setter_slot * sizeof(uint64_t),
            sizeof(raw_setter));
        uintptr_t name_pointer = (uintptr_t)decode_protected_value(
            raw_name, property_name_key, property_name_operation);
        target->getter_pointer = (uintptr_t)decode_protected_value(
            raw_getter, property_getter_key, property_getter_operation);
        target->setter_pointer = (uintptr_t)decode_protected_value(
            raw_setter, property_setter_key, property_setter_operation);
        if ((target->getter_pointer &&
             !known_method_metadata(target->getter_pointer)) ||
            (target->setter_pointer &&
             !known_method_metadata(target->setter_pointer)) ||
            (!target->getter_pointer && !target->setter_pointer)) {
            failure_index = index + 1u; failure_kind = 13u; return 0;
        }
        if (!property_info(object, name_object, getter_object, setter_object,
                &target->flags)) {
            failure_index = index + 1u; failure_kind = 15u; return 0;
        }
        target->metadata_token = get_metadata_token(
            object, metadata_token_metadata);
        uint32_t rid = target->metadata_token & 0x00ffffffu;
        if ((target->metadata_token & 0xff000000u) != 0x17000000u ||
            rid != index + expected_metadata_token_rid_base ||
            (uint64_t)rid > 0x00ffffffu) {
            failure_index = index + 1u; failure_kind = 16u; return 0;
        }
        if (!append_native_name(name_pointer, target->metadata_token,
                "EmptyProperty_", &target->name_bytes,
                &target->name_offset, &synthetic_properties)) {
            failure_index = index + 1u; failure_kind = 11u; return 0;
        }
        completed_properties++;
    }
    return 1;
}

static void write_status(const char *status, int written) {
    FILE *out = _wfopen(status_path, L"wb"); if (!out) return;
    fprintf(out,
        "{\n  \"schema\": \"$status_schema\",\n"
        "  \"status\": \"%s\",\n  \"process_id\": %lu,\n"
        "  \"completed_field_count\": %llu,\n"
        "  \"completed_property_count\": %llu,\n"
        "  \"expected_field_count\": %llu,\n"
        "  \"expected_property_count\": %llu,\n"
        "  \"synthetic_field_name_count\": %llu,\n"
        "  \"synthetic_property_name_count\": %llu,\n"
        "  \"metadata_token_rid_base\": %u,\n"
        "  \"property_info_name_qword_owner_only\": %u,\n"
        "  \"property_info_flags_offset_owner_only\": %u,\n"
        "  \"failure_index_owner_only\": %llu,\n"
        "  \"failure_kind_owner_only\": %u,\n"
        "  \"output_written\": %s,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"property_flags_live_info_structure_derived\": true,\n"
        "  \"legacy_property_attribute_dispatch_used\": false,\n"
        "  \"saved_member_detail_used\": false,\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_offset_used\": false,\n"
        "  \"external_runtime_component_used\": false\n}\n",
        status, (unsigned long)GetCurrentProcessId(),
        (unsigned long long)completed_fields,
        (unsigned long long)completed_properties,
        (unsigned long long)expected_field_count,
        (unsigned long long)expected_property_count,
        (unsigned long long)synthetic_fields,
        (unsigned long long)synthetic_properties,
        expected_metadata_token_rid_base,
        property_info_name_qword, property_info_flags_offset,
        (unsigned long long)failure_index, failure_kind,
        written ? "true" : "false"); fclose(out);
}
static int write_output(void) {
    uint64_t records_end = sizeof(detail_header) +
        expected_field_count * sizeof(detail_field) +
        expected_property_count * sizeof(detail_property);
    for (uint64_t i = 0; i < expected_field_count; i++) fields[i].name_offset += records_end;
    for (uint64_t i = 0; i < expected_property_count; i++) properties[i].name_offset += records_end;
    detail_header header; memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHAND1", 8); header.version = $detail_version;
    header.header_bytes = sizeof(header); header.field_record_bytes = sizeof(detail_field);
    header.property_record_bytes = sizeof(detail_property);
    header.field_count = expected_field_count; header.property_count = expected_property_count;
    header.string_bytes = string_bytes; header.image_base = expected_image_base;
    header.image_bytes = expected_image_bytes; header.type_count = expected_type_count;
    memcpy(header.executable_sha256, executable_sha256, 64);
    memcpy(header.member_inventory_sha256, member_inventory_sha256, 64);
    memcpy(header.type_identity_sha256, type_identity_sha256, 64);
    memcpy(header.native_semantics_sha256, native_semantics_sha256, 64);
    FILE *out = _wfopen(output_path, L"wb"); if (!out) return 0;
    int ok = fwrite(&header, 1, sizeof(header), out) == sizeof(header) &&
        fwrite(fields, sizeof(detail_field), expected_field_count, out) == expected_field_count &&
        fwrite(properties, sizeof(detail_property), expected_property_count, out) == expected_property_count &&
        fwrite(strings, 1, string_bytes, out) == string_bytes;
    if (fclose(out)) ok = 0; if (!ok) _wremove(output_path); return ok;
}
static DWORD WINAPI worker(LPVOID unused) {
    (void)unused; _wremove(output_path); _wremove(status_path);
    char executable_hash[65], member_hash[65];
    if (GetCurrentProcessId() != expected_process_id ||
        !executable_identity(executable_hash) || strcmp(executable_hash, executable_sha256) ||
        !sha256_file(member_input_path, member_hash) || strcmp(member_hash, member_inventory_sha256)) {
        failure_kind = 100u; write_status("identity_mismatch", 0); return 0;
    }
    SIZE_T native_bytes = 0, member_bytes = 0;
    if (!read_file(native_input_path, &native_data, &native_bytes) ||
        !read_file(member_input_path, &member_data, &member_bytes)) {
        failure_kind = 101u; write_status("input_unavailable", 0); return 0;
    }
    native_header *nh = (native_header *)native_data;
    member_header *mh = (member_header *)member_data;
    if (native_bytes < sizeof(*nh) || member_bytes < sizeof(*mh) ||
        memcmp(nh->magic, "ALPHANI1", 8) || memcmp(mh->magic, "ALPHANM1", 8) ||
        nh->type_count != expected_type_count || mh->field_count != expected_field_count ||
        mh->property_count != expected_property_count) {
        failure_kind = 102u; write_status("input_invalid", 0); return 0;
    }
    types = (native_type *)(native_data + sizeof(*nh));
    methods = (native_method *)(native_data + sizeof(*nh) +
        expected_type_count * sizeof(native_type));
    members = (member_record *)(member_data + sizeof(*mh));
    fields = calloc(expected_field_count, sizeof(*fields));
    properties = calloc(expected_property_count, sizeof(*properties));
    method_metadata = malloc((SIZE_T)expected_method_count * sizeof(uintptr_t));
    if (!fields || !properties || !method_metadata) { failure_kind = 103u; write_status("allocation_failed", 0); return 0; }
    for (uint64_t index = 0; index < expected_method_count; index++)
        method_metadata[index] = methods[index].metadata_pointer;
    qsort(method_metadata, (SIZE_T)expected_method_count,
        sizeof(uintptr_t), compare_pointer);
    int ok = dispatch_members();
    if (!ok || completed_fields != expected_field_count ||
        completed_properties != expected_property_count) {
        if (!failure_kind) failure_kind = 104u;
        write_status("capture_failed", 0); return 0;
    }
    ok = write_output(); write_status(ok ? "complete" : "write_failed", ok); return 0;
}
BOOL WINAPI DllMain(HINSTANCE module, DWORD reason, LPVOID reserved) {
    (void)reserved; if (reason == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(module); HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    } return TRUE;
}
''')


def runtime_native_member_detail_source(
    *, binding: dict[str, Any], output_path: Path, status_path: Path
) -> str:
    values = {
        "native_header_bytes": _NATIVE_INVENTORY_HEADER.size,
        "native_type_bytes": _NATIVE_TYPE_RECORD.size,
        "member_header_bytes": _NATIVE_MEMBER_HEADER.size,
        "member_record_bytes": _NATIVE_MEMBER_RECORD.size,
        "detail_header_bytes": RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size,
        "detail_field_bytes": RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        "detail_property_bytes": RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size,
        "detail_version": RUNTIME_NATIVE_MEMBER_DETAIL_VERSION,
        "status_schema": RUNTIME_NATIVE_MEMBER_DETAIL_STATUS_SCHEMA,
        "executable_sha256": binding["binary"]["sha256"],
        "member_sha256": binding["native_member_inventory"]["sha256"],
        "type_identity_sha256": binding["type_identity_inventory"]["sha256"],
        "native_semantics_sha256": binding["native_semantics"]["sha256"],
        "process_id": binding["process_id"],
        "image_base": binding["image_base"],
        "image_bytes": binding["image_bytes"],
        "type_count": binding["type_count"],
        "field_count": binding["field_count"],
        "property_count": binding["property_count"],
        "method_count": binding["method_count"],
        "metadata_token_rid_base": binding["metadata_token_rid_base"],
        "descriptor_offset": binding["descriptor_offset"],
        "field_class": binding["field_class"],
        "property_class": binding["property_class"],
        "method_class": binding["method_class"],
        "type_class": binding["type_class"],
        "field_attribute_offset": binding["field_attribute_offset"],
        "field_from_handle_pointer": binding["field_from_handle"]["pointer"],
        "field_from_handle_metadata": binding["field_from_handle"]["metadata"],
        "field_name_slot": binding["field_name"]["slot"],
        "field_name_key": binding["field_name"]["key"],
        "property_name_slot": binding["property_name_codec"]["slot"],
        "property_name_key": binding["property_name_codec"]["key"],
        "property_name_operation": {
            "xor": 1, "add": 2, "subtract": 3,
        }[binding["property_name_codec"]["operation"]],
        "property_getter_slot": binding["property_accessors"]["getter"]["slot"],
        "property_getter_key": binding["property_accessors"]["getter"]["key"],
        "property_getter_operation": {
            "xor": 1, "add": 2, "subtract": 3,
        }[binding["property_accessors"]["getter"]["operation"]],
        "property_setter_slot": binding["property_accessors"]["setter"]["slot"],
        "property_setter_key": binding["property_accessors"]["setter"]["key"],
        "property_setter_operation": {
            "xor": 1, "add": 2, "subtract": 3,
        }[binding["property_accessors"]["setter"]["operation"]],
        "field_type_pointer": binding["field_type"]["pointer"],
        "field_type_metadata": binding["field_type"]["metadata"],
        "field_type_object_qword": binding["field_type"]["object_qword"],
        "type_handle_pointer": binding["type_handle"]["pointer"],
        "type_handle_metadata": binding["type_handle"]["metadata"],
        "type_handle_object_qword": binding["type_handle"]["object_qword"],
        "type_from_handle_pointer": binding["type_from_handle"]["pointer"],
        "type_from_handle_metadata": binding["type_from_handle"]["metadata"],
        "property_from_handle_pointer": binding["property_from_handle"]["pointer"],
        "property_from_handle_metadata": binding["property_from_handle"]["metadata"],
        "property_name_pointer": binding["property_name"]["pointer"],
        "property_name_metadata": binding["property_name"]["metadata"],
        "property_info_fill_pointer": binding[
            "property_info_fill"
        ]["pointer"],
        "property_info_fill_metadata": binding[
            "property_info_fill"
        ]["metadata"],
        "property_info_request_mask": binding[
            "property_info_fill"
        ]["request_mask"],
        "property_getter_pointer": binding["property_getter"]["pointer"],
        "property_getter_metadata": binding["property_getter"]["metadata"],
        "property_setter_pointer": binding["property_setter"]["pointer"],
        "property_setter_metadata": binding["property_setter"]["metadata"],
        "metadata_token_pointer": binding["metadata_token"]["pointer"],
        "metadata_token_metadata": binding["metadata_token"]["metadata"],
        "field_offset_raw_offset": binding["field_offset"]["raw_dword_offset"],
        "field_offset_key": binding["field_offset"]["xor_key"],
        "field_offset_mask": binding["field_offset"]["mask"],
        "field_offset_adjustment": binding["field_offset"]["adjustment"],
        "field_offset_operation": {
            "xor": 1,
            "add": 2,
            "subtract": 3,
        }[binding["field_offset"].get("operation", "xor")],
        "native_path": _wide_literal(_windows_z_path(Path(binding["native_inventory"]["path"]))),
        "member_path": _wide_literal(_windows_z_path(Path(binding["native_member_inventory"]["path"]))),
        "output_path": _wide_literal(_windows_z_path(output_path)),
        "status_path": _wide_literal(_windows_z_path(status_path)),
    }
    return _COLLECTOR.substitute(values)


def prepare_runtime_native_member_detail_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    native_semantics_model: Path, native_inventory: Path,
    native_member_inventory: Path, type_identity_model: Path,
    type_identity_inventory: Path, runtime_inventory_dispatch: Path | None,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    current_process = current_runtime_process_binding()
    if current_process is None:
        raise AcquisitionError(
            "lossless member-name capture requires current process binding; use capture-fresh-inventory")
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary, reflection_semantics_model=reflection_semantics_model,
        native_semantics_model=native_semantics_model,
        native_inventory=native_inventory,
        native_member_inventory=native_member_inventory,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
    )
    if (binding["process_id"] != current_process[0] or
        not same_executable_path(binary, current_process[2])):
        raise AcquisitionError("member detail source process differs from current binding")
    output_path = output_dir / "runtime-native-member-detail.private.bin"
    raw_member_path = output_dir / "runtime-member-raw-observation.private.bin"
    raw_names_path = output_dir / "runtime-member-raw-names.private.bin"
    status_path = output_dir / "runtime-native-member-detail-status.private.json"
    model_path = output_dir / "runtime-native-member-detail.private.json"
    plan_path = output_dir / "runtime-native-member-detail-plan.private.json"
    build_dir = _owner_directory(output_dir / "build-native-member-detail")
    source_path = build_dir / "runtime-native-member-detail.c"
    injector_source_path = build_dir / "runtime-native-member-detail-injector.c"
    for path in (output_path, status_path, model_path, raw_member_path, raw_names_path, plan_path):
        if path.exists():
            raise AcquisitionError("member capture requires a new output directory")
    source, _, _ = attach_raw_member_names(runtime_native_member_detail_source(
        binding=binding, output_path=output_path, status_path=status_path),
        binding=binding, creation_filetime=current_process[1], output_path=raw_member_path)
    _private_text(source_path, source)
    _private_text(injector_source_path, runtime_injector_source())
    collector_path = build_dir / ("alpha-runtime-native-member-detail-" +
        file_identity(source_path)["sha256"][:12] + ".dll")
    injector_path = build_dir / "alpha-runtime-native-member-detail-injector.exe"
    cc = _compiler(compiler)
    _build([str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra", "-Wformat=2",
        "-Werror=format", str(source_path), "-o", str(collector_path), "-lbcrypt"],
        label="runtime native member detail collector")


    cached_windows_build([str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
        "-Wformat=2", "-Werror=format", str(injector_source_path), "-o", str(injector_path)],
        label="runtime native member detail injector",
        source_path=injector_source_path, output_path=injector_path)
    for artifact in (collector_path, injector_path): artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_NATIVE_MEMBER_DETAIL_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_path": str(Path(binary).expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "creation_filetime": current_process[1],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"]},
        "inputs": {key: binding[key] for key in (
            "semantics", "native_semantics", "native_inventory",
            "native_member_inventory", "type_identity_model",
            "type_identity_inventory", "runtime_snapshot",
            "type_identity_plan", "class_model")},
        "attribute_semantics": binding["attribute_semantics"],
        "field_type_store_current_code": binding["field_type_store_current_code"],
        "operation_arities_current_snapshot": binding["operation_arities"],
        "operation_arity_offset_owner_only": binding[
            "operation_arity_offset_owner_only"
        ],
        "collector": file_identity(collector_path), "injector": file_identity(injector_path),
        "output_path": str(output_path), "status_path": str(status_path),
        "raw_member_names_path": str(raw_member_path), "raw_names_output_path": str(raw_names_path),
        "model_path": str(model_path),
        "contract": {"type_count": binding["type_count"],
            "lossless_raw_names_required": True,
            "field_normalization_replay_required": True,
            "field_type_object_qword": binding["field_type"]["object_qword"],
            "field_attribute_offset": binding["field_attribute_offset"],
            "field_count": binding["field_count"],
            "property_count": binding["property_count"],
            "field_record_bytes": RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
            "property_record_bytes": RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size,
            "metadata_token_rid_base": binding["metadata_token_rid_base"],
            "all_metadata_tokens_runtime_observed": True,
            "all_table_rids_definition_order_validated": True,
            "all_property_flags_live_info_structure_observed": True},
        "policy": {"same_process_required": True,
            "current_executable_sha256_embedded": True,
            "runtime_codecs_current_code_derived": True,
            "legacy_runtime_dispatch_used": False,
            "property_attribute_getter_invented": False,
            "member_attribute_fill_operations_current_structure_derived": True,
            "raw_pointers_owner_only": True, "saved_member_detail_used": False,
            "fixed_address_used": False, "fixed_offset_used": False,
            "external_runtime_component_used": False},
    }
    _private_json(plan_path, plan)
    return {"schema": RUNTIME_NATIVE_MEMBER_DETAIL_PLAN_SCHEMA,
        "status": "prepared", "target": {"executable_sha256": binding["binary"]["sha256"]},
        "counts": {"field": binding["field_count"], "property": binding["property_count"]},
        "policy": plan["policy"]}


def _validate_capture(plan: dict[str, Any], status: dict[str, Any]) -> tuple[dict[str, int], dict[str, bool]]:
    raw = Path(plan["output_path"]).read_bytes()
    if len(raw) < RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size:
        raise AcquisitionError("runtime native member detail output is truncated")
    header = RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.unpack_from(raw)
    fields = plan["contract"]["field_count"]
    properties = plan["contract"]["property_count"]
    type_count = plan["contract"]["type_count"]
    metadata_token_rid_base = plan["contract"]["metadata_token_rid_base"]
    string_bytes = header[7]
    records_end = RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size + fields * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size + properties * RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size
    header_valid = (header[0] == RUNTIME_NATIVE_MEMBER_DETAIL_MAGIC and
        header[1] == RUNTIME_NATIVE_MEMBER_DETAIL_VERSION and
        header[2] == RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size and
        header[3] == RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size and
        header[4] == RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size and
        header[5] == fields and header[6] == properties and
        header[8] == plan["target"]["image_base_owner_only"] and
        header[9] == plan["target"]["image_bytes"] and
        header[10] == type_count and header[11] == 0 and
        _digest(header[12], label="output executable") == plan["target"]["executable_sha256"] and
        _digest(header[13], label="output members") == plan["inputs"]["native_member_inventory"]["sha256"] and
        _digest(header[14], label="output identity") == plan["inputs"]["type_identity_inventory"]["sha256"] and
        _digest(header[15], label="output semantics") == plan["inputs"]["native_semantics"]["sha256"] and
        records_end + string_bytes == len(raw))


    field_available = max(0, (len(raw) - RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size)
        // RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size)
    field_rows = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.iter_unpack(memoryview(raw)[
        RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
        : RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
        + min(fields, field_available) * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size])
    field_rows_valid = header_valid
    synthetic_fields = 0
    tokens: set[int] = set()
    index = -1
    for index, row in enumerate(field_rows):
        type_index, member_index, pointer, descriptor, offset, attributes, token, name_bytes, flags, name_offset = row
        if (type_index >= type_count or not pointer or not descriptor or
            token >> 24 != 0x04 or
            (token & 0x00FFFFFF) != index + metadata_token_rid_base or
            token in tokens or not name_bytes or flags or
            name_offset < records_end or name_offset + name_bytes > len(raw) or
            not -(1 << 31) <= offset < (1 << 31)):
            field_rows_valid = False; break
        tokens.add(token)
        name = raw[name_offset:name_offset + name_bytes]
        try: name.decode("utf-8")
        except UnicodeDecodeError: field_rows_valid = False; break
        synthetic_fields += name.startswith(b"EmptyField_")
    else:
        if index != fields - 1:
            RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(raw,
                RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size + (index + 1) * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size)
    property_rows_valid = field_rows_valid
    synthetic_properties = 0
    property_tokens: set[int] = set()
    property_start = RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size + fields * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size
    if property_rows_valid:
        property_available = max(0, (len(raw) - property_start)
            // RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size)
        property_rows = RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.iter_unpack(memoryview(raw)[
            property_start
            : property_start + min(properties, property_available) * RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size])
        index = -1
        for index, row in enumerate(property_rows):
            type_index, member_index, pointer, getter, setter, token, name_bytes, flags, reserved, name_offset = row
            if (type_index >= type_count or not pointer or not (getter or setter) or
                token >> 24 != 0x17
                or (token & 0x00FFFFFF)
                != index + metadata_token_rid_base
                or
                token in property_tokens or not name_bytes or
                flags > 0xFFFF or reserved or
                name_offset < records_end or name_offset + name_bytes > len(raw)):
                property_rows_valid = False; break
            property_tokens.add(token)
            name = raw[name_offset:name_offset + name_bytes]
            try: name.decode("utf-8")
            except UnicodeDecodeError: property_rows_valid = False; break
            synthetic_properties += name.startswith(b"EmptyProperty_")
        else:
            if index != properties - 1:
                RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.unpack_from(raw,
                    property_start + (index + 1) * RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size)
    counts = {"field_count": fields, "property_count": properties,
        "string_bytes": string_bytes, "display_placeholder_prefix_field_count": synthetic_fields,
        "display_placeholder_prefix_property_count": synthetic_properties,
        "field_metadata_token_count": len(tokens),
        "property_metadata_token_count": len(property_tokens)}
    checks = {"status_schema": status.get("schema") == RUNTIME_NATIVE_MEMBER_DETAIL_STATUS_SCHEMA,
        "status_process_bound": status.get("process_id") == plan["target"]["process_id"],
        "status_complete": status.get("status") == "complete", "header_bound": header_valid,
        "all_fields_captured": status.get("completed_field_count") == fields,
        "all_properties_captured": status.get("completed_property_count")
        == properties,
        "field_rows_valid": field_rows_valid, "property_rows_valid": property_rows_valid,
        "field_metadata_tokens_unique": len(tokens) == fields,
        "property_metadata_tokens_unique": len(property_tokens) == properties,
        "metadata_token_rid_base_matches_current_runtime": status.get(
            "metadata_token_rid_base"
        ) == plan["contract"]["metadata_token_rid_base"],
        "all_table_rids_definition_order_exact": field_rows_valid
        and property_rows_valid,
        "property_info_layout_runtime_derived": (
            status.get("property_info_name_qword_owner_only")
            not in (None, 0xFFFFFFFF)
            and status.get("property_info_flags_offset_owner_only")
            not in (None, 0xFFFFFFFF)
            and status.get("property_flags_live_info_structure_derived") is True
            and status.get("legacy_property_attribute_dispatch_used") is False
        ),
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_member_detail_absent": status.get("saved_member_detail_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get("external_runtime_component_used") is False}
    return counts, checks


def capture_runtime_native_member_detail_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    native_semantics_model: Path, native_inventory: Path,
    native_member_inventory: Path, type_identity_model: Path,
    type_identity_inventory: Path, runtime_inventory_dispatch: Path | None,
    output_dir: Path, wine: Path,
    wineprefix: Path, compiler: Path | None = None, timeout: float = 1200.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_native_member_detail_inventory(binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        native_semantics_model=native_semantics_model, native_inventory=native_inventory,
        native_member_inventory=native_member_inventory,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
        output_dir=output_dir, compiler=compiler)
    plan = read_json(output_dir / "runtime-native-member-detail-plan.private.json")
    with RuntimeProcessLifetimeGuard(identity=plan["target"], wine=wine, wineprefix=wineprefix,
            compiler=compiler, build_dir=output_dir / "build-process-lifetime") as lifetime:
        return _capture_prepared_native_member_details(plan=plan, output_dir=output_dir,
            wine=wine, wineprefix=wineprefix, timeout=timeout, lifetime=lifetime)


def _capture_prepared_native_member_details(*, plan, output_dir, wine, wineprefix, timeout, lifetime):
    lifetime.assert_alive()
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(_host_run(str(wine.expanduser().resolve()), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name), env=environment,
            check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace", timeout=90)
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError("runtime native member detail injector could not run") from error
    _private_text(output_dir / "runtime-native-member-detail-injector.private.log",
        json.dumps({"returncode": injected.returncode, "stdout": injected.stdout,
            "stderr": injected.stderr}, ensure_ascii=False, indent=2) + "\n")
    if injected.returncode: raise AcquisitionError("runtime native member detail injection failed")
    lifetime.assert_alive()
    deadline = time.monotonic() + timeout; status_path = Path(plan["status_path"]); status = None
    while time.monotonic() < deadline:
        lifetime.assert_alive()
        if status_path.is_file():
            candidate = read_runtime_progress(status_path)
            if isinstance(candidate, dict) and candidate.get("status"):
                status = candidate; break
        time.sleep(0.2)
    if status is None: raise AcquisitionError("runtime native member detail capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError("runtime native member detail capture failed "
            f"(status={status.get('status')}, index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})")
    lifetime.assert_alive()
    result = _finalize_native_member_details(plan=plan, status=status)
    lifetime.assert_alive()
    return result


def _finalize_native_member_details(*, plan, status):
    if plan.get("contract", {}).get("lossless_raw_names_required") is not True:
        raise AcquisitionError("member detail plan has no lossless raw-name contract")
    if plan["contract"].get("field_normalization_replay_required") is not True:
        raise AcquisitionError("member detail plan has no field normalization replay contract")
    output_path = Path(plan["output_path"])
    status_path = Path(plan["status_path"])
    _seal_runtime_output(output_path); _seal_runtime_output(status_path)
    _seal_runtime_output(Path(plan["raw_member_names_path"]))
    counts, checks = _validate_capture(plan, status)
    if not all(checks.values()):
        raise AcquisitionError("runtime native member detail validation failed: " +
            ", ".join(sorted(key for key, value in checks.items() if not value)))
    field_type_store = _replay_field_type_object_layout(plan)
    checks["field_type_object_slot_current_code_replayed"] = True
    from alpha.p18 import derive_field_normalization
    normalization = derive_field_normalization(binary=Path(plan["target"]["executable_path"]),
        inputs=plan["inputs"], inventory=file_identity(output_path), target=plan["target"])
    checks.update(normalization["checks"])
    raw_names = finalize_raw_member_names(plan=plan, output_path=Path(plan["raw_names_output_path"]))
    checks.update(raw_names["checks"])
    for domain in ("field", "property"):
        empty, null = (raw_names["counts"][f"{kind}_{domain}_names"] for kind in ("empty", "null"))
        counts.update({f"empty_{domain}_names": empty, f"null_{domain}_names": null})
        checks[f"synthetic_{domain}_names_accounted_from_originals"] = (
            status.get(f"synthetic_{domain}_name_count") == empty + null)
    if not all(checks.values()):
        raise AcquisitionError("member raw name counts differ from native status")
    model = {"schema": RUNTIME_NATIVE_MEMBER_DETAIL_SCHEMA,
        "status": "runtime-validated", "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": plan["inputs"], "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path), "counts": counts,
        "checks": checks, "raw_names": raw_names, "field_offset_normalization": normalization,
        "field_type_store_current_code": field_type_store,
        "owner_only": True, "metadata_complete": False}
    _private_json(Path(plan["model_path"]), model)
    return {"schema": RUNTIME_NATIVE_MEMBER_DETAIL_SCHEMA,
        "status": "runtime-validated", "target": model["target"],
        "counts": counts, "checks": checks, "inventory": model["inventory"]}
