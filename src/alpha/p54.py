import json
import os
import stat
import struct
import subprocess
import time
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import (
    _build,
    _compiler,
    _owner_directory,
    _private_json,
    _private_text,
    _seal_runtime_output,
    _wide_literal,
    _windows_z_path,
    runtime_injector_source,
)
from alpha.h01 import AcquisitionError
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p13 import derive_concrete_method_operations
from alpha.p27 import (
    RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER,
    RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC,
    RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD,
    RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA,
    RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION,
)
from alpha.p44 import (
    CONSTANT_BOOLEAN,
    CONSTANT_CHAR,
    CONSTANT_DOUBLE,
    CONSTANT_NULL,
    CONSTANT_SIGNED,
    CONSTANT_SINGLE,
    CONSTANT_STRING,
    CONSTANT_TYPED_ENUM,
    _PRIMITIVE,
    _UNDERLYING,
)
from alpha.c06 import LiveRuntimeInventory, rebind_method
from alpha.p29 import _runtime
from alpha.p38 import _binding as _proto_inventory_binding
from alpha.p42 import _field_rows
from alpha.h02 import file_identity, read_json


RUNTIME_PARAMETER_DEFAULT_PLAN_SCHEMA = (
    "alpha.runtime-parameter-default-plan/v1"
)
RUNTIME_PARAMETER_DEFAULT_STATUS_SCHEMA = (
    "alpha.runtime-parameter-default-status/v1"
)
RUNTIME_PARAMETER_DEFAULT_SCHEMA = (
    "alpha.runtime-parameter-default-inventory/v1"
)
RUNTIME_PARAMETER_DEFAULT_MAGIC = b"BALV2PD1"
RUNTIME_PARAMETER_DEFAULT_VERSION = 1
RUNTIME_PARAMETER_DEFAULT_HEADER = struct.Struct("<8sIIIIQQQ64s64s")


RUNTIME_PARAMETER_DEFAULT_RECORD = struct.Struct("<IIIIQQQQ")

PARAMETER_HAS_DEFAULT = 0x1000
PARAMETER_DEFAULT_REFERENCE_NULL_ONLY = 1 << 20
PARAMETER_DEFAULT_DYNAMIC_OBJECT = 1 << 21
PARAMETER_DEFAULT_MISSING = 1 << 22
PARAMETER_DEFAULT_RUNTIME_OBJECT = 1 << 23
PARAMETER_DEFAULT_BOXED_NULL_CONTRACT = 1 << 24
PARAMETER_DEFAULT_NORMALIZED_BOXED_NULL = 1 << 25


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or path.stat().st_uid != os.getuid()
        or stat.S_IMODE(path.stat().st_mode) & 0o077
    ):
        raise AcquisitionError(
            f"runtime parameter default {label} is not owner-only"
        )
    return path


def _operation(semantics: dict[str, Any], key: str) -> dict[str, int]:
    rows = [
        row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
        and row.get("key") == key
        and row.get("semantic_identity_resolved") is True
        and isinstance(row.get("method_pointer"), int)
        and isinstance(row.get("metadata_pointer"), int)
    ]
    if len(rows) != 1:
        raise AcquisitionError(
            f"runtime parameter default operation is unavailable: {key}"
        )
    return {
        "pointer": int(rows[0]["method_pointer"]),
        "metadata": int(rows[0]["metadata_pointer"]),
    }


def _constant_flags(
    *, width: int, signed: bool = False, kind: str = "integer",
    typed_enum: bool = False,
) -> int:
    value = width
    value |= CONSTANT_SIGNED if signed else 0
    value |= CONSTANT_STRING if kind == "string" else 0
    value |= CONSTANT_SINGLE if kind == "single" else 0
    value |= CONSTANT_DOUBLE if kind == "double" else 0
    value |= CONSTANT_BOOLEAN if kind == "boolean" else 0
    value |= CONSTANT_CHAR if kind == "char" else 0
    value |= CONSTANT_TYPED_ENUM if typed_enum else 0
    return value


def _sentinel_evidence(
    semantics: dict[str, Any], key: str,
) -> dict[str, int]:
    rows = [
        row
        for row in semantics.get("sentinel_field_evidence", [])
        if isinstance(row, dict) and row.get("operation_key") == key
    ]
    if len(rows) != 1:
        raise AcquisitionError(
            "runtime parameter default cache evidence is unavailable"
        )
    row = rows[0]
    qword = row.get("selected_field_qword")
    parameter_class = row.get("class_pointer")
    sentinel_class = row.get("target_class_pointer")
    if (
        not isinstance(qword, int)
        or not 2 <= qword < 64
        or not isinstance(parameter_class, int)
        or parameter_class <= 0
        or not isinstance(sentinel_class, int)
        or sentinel_class <= 0
        or row.get("candidate_field_count") != 1
    ):
        raise AcquisitionError(
            "runtime parameter default cache evidence is ambiguous"
        )
    return {
        "qword": qword,
        "parameter_class": parameter_class,
        "sentinel_class": sentinel_class,
    }


def _root_index(runtime: Any, descriptor: int) -> int | None:
    node_index = runtime.renderer.node_by_descriptor.get(descriptor)
    if node_index is None:
        return None
    row = runtime.renderer.reference_row(node_index)
    return runtime.renderer._root_alias(descriptor, row[1])


def _binding(
    *, native_output_receipt: Path, runtime_materializer_model: Path,
    runtime_inventory_dispatch: Path | None,
) -> dict[str, Any]:


    del runtime_inventory_dispatch
    receipt, paths, runtime = _runtime(native_output_receipt)
    proto = _proto_inventory_binding(native_output_receipt)
    semantics_path = _owner_file(
        Path(proto["reflection_semantics"]["path"]),
        label="reflection semantics",
    )
    if file_identity(semantics_path) != proto["reflection_semantics"]:
        raise AcquisitionError(
            "runtime parameter default reflection semantics are stale"
        )
    semantics = read_json(semantics_path)
    if (
        semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary", {}).get("sha256")
        != receipt["target"]["executable_sha256"]
        or semantics.get("checks", {}).get("all_operations_resolved")
        is not True
    ):
        raise AcquisitionError(
            "runtime parameter default reflection binding is incomplete"
        )
    output_model = read_json(_owner_file(paths["model"], label="runtime model"))
    member_model_record = output_model.get("inputs", {}).get(
        "native_member_detail_model"
    )
    if not isinstance(member_model_record, dict) or not isinstance(
        member_model_record.get("path"), str
    ):
        raise AcquisitionError(
            "runtime parameter default native member model is unavailable"
        )
    member_model_path = _owner_file(
        Path(member_model_record["path"]), label="native member model"
    )
    if file_identity(member_model_path) != member_model_record:
        raise AcquisitionError(
            "runtime parameter default native member model is stale"
        )
    member_model = read_json(member_model_path)
    class_model_path = _owner_file(
        Path(member_model["inputs"]["class_model"]["path"]),
        label="class model",
    )
    class_model = read_json(class_model_path)
    snapshot_path = _owner_file(
        Path(semantics["snapshot"]["path"]), label="runtime snapshot"
    )
    arity_offset = semantics.get("method_parameter_count", {}).get(
        "selected_byte_offset"
    )
    if not isinstance(arity_offset, int):
        raise AcquisitionError(
            "runtime parameter default method arity layout is unavailable"
        )
    concrete_result = derive_concrete_method_operations(
        semantics=semantics,
        class_model=class_model,
        snapshot_path=snapshot_path,
        arity_offset=arity_offset,
        expected_executable_sha256=receipt["target"]["executable_sha256"],
    )
    concrete = concrete_result["operations"]

    method_status_path = _owner_file(
        paths["method_detail_inventory"].parent
        / "runtime-method-detail-status.private.json",
        label="method detail status",
    )
    method_status = read_json(method_status_path)
    parameter_attribute_offset = method_status.get(
        "parameter_attribute_offset_owner_only"
    )
    parameter_type_qword = method_status.get(
        "parameter_type_qword_owner_only"
    )
    type_handle_rows = [
        row
        for row in semantics.get("native_type_descriptor_evidence", [])
        if isinstance(row, dict) and row.get("operation_key") == "type.handle"
    ]
    if len(type_handle_rows) != 1:
        raise AcquisitionError(
            "runtime parameter default type handle layout is ambiguous"
        )
    type_handle_qword = type_handle_rows[0].get("selected_field_qword")
    if (
        not isinstance(parameter_attribute_offset, int)
        or parameter_attribute_offset < 16
        or not isinstance(parameter_type_qword, int)
        or parameter_type_qword < 2
        or not isinstance(type_handle_qword, int)
        or type_handle_qword < 2
    ):
        raise AcquisitionError(
            "runtime parameter default parameter layout is unavailable"
        )

    parameter_token_rid_bases = {
        (int(runtime.parameter_row(index)[6]) & 0x00FFFFFF) - index
        for index in range(runtime.parameter_count)
        if int(runtime.parameter_row(index)[6]) >> 24 == 0x08
    }
    type_identity_record = member_model["inputs"]["type_identity_model"]
    type_identity_path = _owner_file(
        Path(type_identity_record["path"]), label="type identity model"
    )
    type_identity = read_json(type_identity_path)
    type_rid_base = type_identity.get("counts", {}).get(
        "metadata_token_rid_base"
    )
    if (
        len(parameter_token_rid_bases) != 1
        or type_rid_base not in (0, 1)
        or next(iter(parameter_token_rid_bases)) != type_rid_base
        or any(
            int(runtime.parameter_row(index)[6])
            != 0x08000000 | (index + type_rid_base)
            for index in range(runtime.parameter_count)
        )
    ):
        raise AcquisitionError(
            "runtime parameter default definition-order token identity differs"
        )

    cache = _sentinel_evidence(semantics, "parameter.default_value")
    live = LiveRuntimeInventory(
        materializer_model=runtime_materializer_model,
        binary=paths["binary"],
    )
    try:
        if live.process_id != proto["process_id"]:
            raise AcquisitionError(
                "runtime parameter default process binding differs"
            )
        rebound = {
            "method_from_handle": rebind_method(
                runtime, live, _operation(semantics, "method.from_handle")
            ),
            "default_getter": rebind_method(
                runtime, live, _operation(semantics, "parameter.default_value")
            ),
            "method_parameters": rebind_method(
                runtime, live, concrete["method.parameters"]
            ),
            "constructor_parameters": rebind_method(
                runtime, live, concrete["constructor.parameters"]
            ),
        }
        if len({value["image_delta"] for value in rebound.values()}) != 1:
            raise AcquisitionError(
                "runtime parameter default image rebasing differs"
            )

        constructed_model_path = _owner_file(
            paths["constructed_generic_layout_model"],
            label="constructed generic model",
        )
        constructed_inventory_path = _owner_file(
            paths["constructed_generic_layout_inventory"],
            label="constructed generic inventory",
        )
        constructed_model = read_json(constructed_model_path)
        constructed_raw = constructed_inventory_path.read_bytes()
        if len(constructed_raw) < RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size:
            raise AcquisitionError(
                "runtime parameter default constructed generic inventory "
                "is truncated"
            )
        constructed_header = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.unpack_from(
            constructed_raw
        )
        from alpha.p20 import bind_constructed_extent
        extent_sources = {}
        instance_size_offset, instance_size_width = bind_constructed_extent(constructed_model, source_records=extent_sources)
        constructed_count = int(constructed_header[5])
        if (
            constructed_model.get("schema")
            != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA
            or constructed_model.get("status") != "runtime-validated"
            or any(
                value is not True
                for value in constructed_model.get("checks", {}).values()
            )
            or constructed_model.get("target", {}).get("executable_sha256")
            != receipt["target"]["executable_sha256"]
            or constructed_model.get("target", {}).get("process_id")
            != live.process_id
            or constructed_header[0]
            != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC
            or constructed_header[1]
            != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
            or constructed_header[2]
            != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
            or constructed_header[3]
            != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
            or constructed_header[7] != live.process_id
            or constructed_count
            != constructed_model.get("counts", {}).get(
                "constructed_generic_class_count"
            )
            or not isinstance(instance_size_offset, int)
            or not isinstance(instance_size_width, int)
            or instance_size_width not in (1, 2, 4, 8)
        ):
            raise AcquisitionError(
                "runtime parameter default constructed generic binding differs"
            )
        constructed_classes: dict[int, tuple[int, int, int]] = {}
        reference_instance_sizes: list[int] = []
        for constructed_index in range(constructed_count):
            constructed_row = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.unpack_from(
                constructed_raw,
                RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
                + constructed_index
                * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size,
            )
            descriptor = int(constructed_row[0])
            definition_index = int(constructed_row[3])
            class_pointer = int(constructed_row[6])
            class_header = constructed_row[9]
            if (
                not 0 <= definition_index < runtime.type_count
                or instance_size_offset + instance_size_width
                > len(class_header)
            ):
                raise AcquisitionError(
                    "runtime parameter default constructed generic row differs"
                )
            instance_size = int.from_bytes(
                class_header[
                    instance_size_offset:
                    instance_size_offset + instance_size_width
                ],
                "little",
            )
            constructed_classes[descriptor] = (
                class_pointer, definition_index, instance_size,
            )
            if not runtime.renderer.identity_row(definition_index)[1] & 0x40:
                reference_instance_sizes.append(instance_size)
        if not reference_instance_sizes:
            raise AcquisitionError(
                "runtime parameter default reference object header is absent"
            )
        object_header_size = min(reference_instance_sizes)
        if (
            object_header_size <= 0
            or object_header_size & 7
            or reference_instance_sizes.count(object_header_size) < 2
        ):
            raise AcquisitionError(
                "runtime parameter default object header is ambiguous"
            )

        primitive_rows: dict[str, dict[str, int]] = {}
        for name, (width, signed, kind) in _PRIMITIVE.items():
            matches = [
                index
                for index in range(runtime.type_count)
                if runtime.renderer.root_name(index) == name
            ]
            if len(matches) != 1:
                raise AcquisitionError(
                    "runtime parameter default primitive type is ambiguous: "
                    + name
                )
            index = matches[0]
            descriptor = runtime.renderer.identity_row(index)[2]
            primitive_rows[name] = {
                "class": live.type_row(index).class_pointer,
                "descriptor": descriptor,
                "flags": _constant_flags(
                    width=width, signed=signed, kind=kind
                ),
            }
        string_matches = [
            index
            for index in range(runtime.type_count)
            if runtime.renderer.root_name(index) == "System.String"
        ]
        object_matches = [
            index
            for index in range(runtime.type_count)
            if runtime.renderer.root_name(index) == "System.Object"
        ]
        if len(string_matches) != 1 or len(object_matches) != 1:
            raise AcquisitionError(
                "runtime parameter default reference roots are ambiguous"
            )
        string_index = string_matches[0]
        string_descriptor = runtime.renderer.identity_row(string_index)[2]
        string_class = live.type_row(string_index).class_pointer

        field_by_index, fields_by_owner = _field_rows(runtime)
        enum_contracts: dict[int, tuple[int, int, int]] = {}
        for owner in range(runtime.type_count):
            if not runtime.renderer.identity_row(owner)[1] & 0x20:
                continue
            fields = [
                field_by_index[index]
                for index in fields_by_owner.get(owner, [])
            ]
            underlying = [
                field for field in fields
                if runtime.renderer.render(field["descriptor"]) in _UNDERLYING
                and (field["attributes"] & 0x600) == 0x600
                and not field["attributes"] & 0x50
            ]
            if len(underlying) != 1:
                raise AcquisitionError(
                    "runtime parameter default enum underlying type is ambiguous"
                )
            name = runtime.renderer.render(underlying[0]["descriptor"])
            primitive = primitive_rows[name]
            enum_contracts[owner] = (
                live.type_row(owner).class_pointer,
                primitive["class"],
                primitive["flags"] | CONSTANT_TYPED_ENUM,
            )

        rows: list[dict[str, int]] = []
        for parameter_index in range(runtime.parameter_count):
            parameter = runtime.parameter_row(parameter_index)
            attributes = int(parameter[3])
            if not attributes & PARAMETER_HAS_DEFAULT:
                continue
            method_index = int(parameter[0])
            method = runtime.method_row(method_index)
            descriptor = int(parameter[2])
            name = runtime.renderer.render(descriptor)
            root = _root_index(runtime, descriptor)
            flags = 0
            expected_class = 0
            alternate_class = 0
            if name in primitive_rows:
                primitive = primitive_rows[name]
                flags = primitive["flags"]
                expected_class = primitive["class"]
            elif name == "System.String":
                flags = CONSTANT_STRING
                expected_class = string_class
            elif (
                descriptor in constructed_classes
                and constructed_classes[descriptor][1] in enum_contracts
            ):
                constructed_class, definition_index, _instance_size = (
                    constructed_classes[descriptor]
                )
                _definition_class, alternate_class, flags = enum_contracts[
                    definition_index
                ]
                expected_class = constructed_class
            elif root in enum_contracts:
                expected_class, alternate_class, flags = enum_contracts[root]
            elif name == "System.Object":
                flags = PARAMETER_DEFAULT_DYNAMIC_OBJECT
            else:


                flags = PARAMETER_DEFAULT_REFERENCE_NULL_ONLY
                constructed = constructed_classes.get(descriptor)
                if (
                    constructed is not None
                    and not runtime.renderer.identity_row(constructed[1])[1]
                    & 0x40
                    and constructed[2] == object_header_size
                    and runtime.renderer.contains_generic_parameter(descriptor)
                ):


                    flags |= PARAMETER_DEFAULT_BOXED_NULL_CONTRACT
                    expected_class = constructed[0]
            current_method = live.method_row(
                method_index, expected_owner=int(method[0])
            )
            owner = live.type_row(int(method[0])).embedded_descriptor(
                live.embedded_descriptor_byte_offset
            )
            token = int(parameter[6])
            if (
                token >> 24 != 0x08
                or (token & 0x00FFFFFF)
                != parameter_index + type_rid_base
            ):
                raise AcquisitionError(
                    "runtime parameter default token domain is invalid"
                )
            rows.append(
                {
                    "method_index": method_index,
                    "parameter_index": parameter_index,
                    "position": int(parameter[1]),
                    "flags": flags,
                    "method_metadata": current_method.metadata_pointer,
                    "owner_descriptor": owner,
                    "expected_token": token,
                    "expected_attributes": attributes,
                    "declared_descriptor": descriptor,
                    "expected_class": expected_class,
                    "alternate_class": alternate_class,
                }
            )
        if not rows:
            raise AcquisitionError(
                "runtime parameter default domain is unexpectedly empty"
            )
        from alpha.c04 import _verify_files
        _verify_files(extent_sources)
        return {
            "extent_operation_sources": extent_sources,
            "receipt": file_identity(native_output_receipt.expanduser().resolve()),
            "runtime_materializer_model": file_identity(
                runtime_materializer_model.expanduser().resolve()
            ),
            "reflection_semantics": file_identity(semantics_path),
            "class_model": file_identity(class_model_path),
            "runtime_snapshot": file_identity(snapshot_path),
            "method_detail_status": file_identity(method_status_path),
            "type_identity_model": file_identity(type_identity_path),
            "concrete_method_semantics": concrete_result,
            "method_detail_inventory": file_identity(
                paths["method_detail_inventory"]
            ),
            "constructed_generic_layout_model": file_identity(
                constructed_model_path
            ),
            "constructed_generic_layout_inventory": file_identity(
                constructed_inventory_path
            ),
            "object_header_size_owner_only": object_header_size,
            "target": receipt["target"],
            "binary": file_identity(paths["binary"]),
            "process_id": live.process_id,
            "parameter_class": cache["parameter_class"],
            "sentinel_class": cache["sentinel_class"],
            "runtime_type_class": proto["type_class"],
            "default_field_qword": cache["qword"],
            "parameter_attribute_offset": parameter_attribute_offset,
            "parameter_type_qword": parameter_type_qword,
            "type_handle_qword": type_handle_qword,
            "metadata_token_rid_base": type_rid_base,
            "method_class": concrete["method.parameters"]["class_pointer"],
            "constructor_class": concrete["constructor.parameters"]["class_pointer"],
            "string_class": string_class,
            "string_descriptor": string_descriptor,
            "operations": rebound,
            "primitive_rows": list(primitive_rows.values()),
            "rows": rows,
        }
    finally:
        live.close()


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#define BATCH 512u
typedef struct input_record {uint32_t method_index,parameter_index,position,flags;uintptr_t method_metadata,owner_descriptor;uint32_t expected_token,expected_attributes;uintptr_t declared_descriptor,expected_class,alternate_class;} input_record;
typedef struct primitive_record {uintptr_t class_pointer,descriptor;uint32_t flags,reserved;} primitive_record;
typedef struct output_header {char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t count,string_bytes,process_id;char executable[64],methods[64];} output_header;
typedef struct output_record {uint32_t parameter_index,method_index,position,flags;uint64_t descriptor,raw_value,string_offset,string_units;} output_record;
_Static_assert(sizeof(output_header)==$header_bytes,"parameter default header");
_Static_assert(sizeof(output_record)==$record_bytes,"parameter default record");
static const DWORD expected_pid=$process_id;
static const char executable_sha[]="$executable_sha";
static const char method_sha[]="$method_sha";
static const uintptr_t parameter_class=$parameter_class,sentinel_class=$sentinel_class,string_class=$string_class,string_descriptor=$string_descriptor,runtime_type_class=$runtime_type_class;
static const uintptr_t method_class=$method_class,constructor_class=$constructor_class;
static const uint32_t default_field_qword=$default_field_qword;
static const uint32_t parameter_attribute_offset=$parameter_attribute_offset;
static const uint32_t parameter_type_qword=$parameter_type_qword;
static const uint32_t type_handle_qword=$type_handle_qword;
static const uint32_t metadata_token_rid_base=$metadata_token_rid_base;
static const uintptr_t from_handle_pointer=$from_handle_pointer,from_handle_metadata=$from_handle_metadata;
static const uintptr_t method_parameters_pointer=$method_parameters_pointer,method_parameters_metadata=$method_parameters_metadata;
static const uintptr_t constructor_parameters_pointer=$constructor_parameters_pointer,constructor_parameters_metadata=$constructor_parameters_metadata;
static const uintptr_t default_getter_pointer=$default_getter_pointer,default_getter_metadata=$default_getter_metadata;
static const input_record inputs[]={$input_rows};
static const primitive_record primitives[]={$primitive_rows};
static const uint64_t input_count=$input_count,primitive_count=$primitive_count;
static const wchar_t output_path[]=$output_path,status_path[]=$status_path;
typedef uintptr_t(*static_threearg)(uintptr_t,uintptr_t,uintptr_t,uintptr_t);
typedef uintptr_t(*instance_noarg)(uintptr_t,uintptr_t);
typedef uint32_t(*instance_dword)(uintptr_t,uintptr_t);
static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_complete;static uint64_t cursor,completed,string_bytes,string_capacity,failure_cursor,transient_retry_count,missing_count,runtime_object_count;static uintptr_t observed_default_class,observed_default_object,missing_class,missing_object;static uint32_t failure_kind,observed_parameter_count;static output_record*records;static unsigned char*strings;static uint32_t array_length_qword,array_vector_qword,default_getter_offset_candidate_count;static int observations_match,managed_default_getter_invoked;
static int readable(uintptr_t v,SIZE_T n){MEMORY_BASIC_INFORMATION r;if(!v||!n||v+n<v||!VirtualQuery((const void*)v,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t e=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&e>=v&&v+n<=e;}
static int object_class(uintptr_t o,uintptr_t c){uintptr_t v=0;if(!readable(o,8u))return 0;memcpy(&v,(const void*)o,8u);return v==c;}
static uintptr_t follow_jump(uintptr_t p){for(uint32_t n=0;n<4u;n++){if(!readable(p,16u))return 0;const unsigned char*b=(const unsigned char*)p;if(b[0]==0xe9){int32_t d=0;memcpy(&d,b+1u,4u);p+=5u+(intptr_t)d;continue;}if(b[0]==0xeb){int8_t d=0;memcpy(&d,b+1u,1u);p+=2u+(intptr_t)d;continue;}if(b[0]==0x48&&b[1]==0xff&&b[2]==0x25){int32_t d=0;uintptr_t q=0;memcpy(&d,b+3u,4u);uintptr_t a=p+7u+(intptr_t)d;if(!readable(a,8u))return 0;memcpy(&q,(const void*)a,8u);p=q;continue;}break;}return p;}
static int verify_default_getter(void){uintptr_t p=follow_jump(default_getter_pointer);if(!p||!readable(p,512u))return 0;const unsigned char*b=(const unsigned char*)p;uint32_t offset=default_field_qword*8u;default_getter_offset_candidate_count=0;for(uint32_t i=0;i+7u<256u;i++){uint32_t d=UINT32_MAX;if(b[i]==0x48&&b[i+1]==0x8b&&(b[i+2]&0xc0u)==0x40u&&(b[i+2]&7u)!=4u)d=b[i+3];else if(b[i]==0x48&&b[i+1]==0x8b&&(b[i+2]&0xc0u)==0x80u&&(b[i+2]&7u)!=4u)memcpy(&d,b+i+3u,4u);if(d==offset)default_getter_offset_candidate_count++;}return default_getter_offset_candidate_count==1u&&memchr(b,0xc3,512u)!=NULL;}
static int array_elements(uintptr_t a,uintptr_t**elements,uint32_t*count){*elements=NULL;*count=0;if(!a||!readable(a,10u*8u))return 0;if(!array_length_qword){for(uint32_t l=1;l<8u;l++){uintptr_t n=0;memcpy(&n,(const void*)(a+(uintptr_t)l*8u),8u);if(!n||n>65536u)continue;for(uint32_t v=l+1u;v<10u;v++){uintptr_t p=a+(uintptr_t)v*8u;if(!readable(p,n*8u))continue;uint64_t i=0;for(;i<n;i++){uintptr_t o=0;memcpy(&o,(const void*)(p+i*8u),8u);if(!object_class(o,parameter_class))break;}if(i==n){if(array_length_qword)return 0;array_length_qword=l;array_vector_qword=v;}}}}if(!array_length_qword)return 0;uintptr_t n=0;memcpy(&n,(const void*)(a+(uintptr_t)array_length_qword*8u),8u);uintptr_t p=a+(uintptr_t)array_vector_qword*8u;if(n>65536u||!readable(p,n*8u))return 0;for(uint64_t i=0;i<n;i++){uintptr_t o=0;memcpy(&o,(const void*)(p+i*8u),8u);if(!object_class(o,parameter_class))return 0;}*elements=(uintptr_t*)p;*count=(uint32_t)n;return 1;}
static int append_utf16(uintptr_t object,uint64_t*offset,uint64_t*units){if(!object_class(object,string_class)||!readable(object+16u,4u))return 0;int32_t n=0;memcpy(&n,(const void*)(object+16u),4u);if(n<0||(uint32_t)n>16777216u||(n&&!readable(object+20u,(SIZE_T)n*2u)))return 0;uint64_t bytes=(uint64_t)(uint32_t)n*2u,required=string_bytes+bytes;if(required<string_bytes)return 0;if(required>string_capacity){uint64_t capacity=string_capacity?string_capacity:1048576u;while(capacity<required){if(capacity>UINT64_MAX/2u)return 0;capacity*=2u;}unsigned char*grown=(unsigned char*)realloc(strings,(SIZE_T)capacity);if(!grown)return 0;strings=grown;string_capacity=capacity;}*offset=string_bytes;*units=(uint32_t)n;if(bytes)memcpy(strings+string_bytes,(const void*)(object+20u),(SIZE_T)bytes);string_bytes=required;return 1;}
static const primitive_record*primitive(uintptr_t c){for(uint64_t i=0;i<primitive_count;i++)if(primitives[i].class_pointer==c)return &primitives[i];return NULL;}
static int capture_one(const input_record*in,output_record*out){static_threearg from_handle=(static_threearg)from_handle_pointer;uintptr_t method=from_handle(in->method_metadata,in->owner_descriptor,1u,from_handle_metadata);instance_noarg parameters=NULL;uintptr_t parameters_metadata=0;if(object_class(method,method_class)){parameters=(instance_noarg)method_parameters_pointer;parameters_metadata=method_parameters_metadata;}else if(object_class(method,constructor_class)){parameters=(instance_noarg)constructor_parameters_pointer;parameters_metadata=constructor_parameters_metadata;}else return 1;uintptr_t array=parameters(method,parameters_metadata),*elements=NULL;uint32_t count=0;if(!array_elements(array,&elements,&count))return 2;observed_parameter_count=count;if(in->position>=count)return 15;uintptr_t parameter=elements[in->position];if(in->expected_token!=(0x08000000u|(in->parameter_index+metadata_token_rid_base)))return 3;uint32_t observed_attributes=0;uintptr_t type_object=0,type_descriptor=0;if(!readable(parameter+parameter_attribute_offset,sizeof(observed_attributes))||!readable(parameter+(uintptr_t)parameter_type_qword*8u,8u))return 12;memcpy(&observed_attributes,(const void*)(parameter+parameter_attribute_offset),sizeof(observed_attributes));memcpy(&type_object,(const void*)(parameter+(uintptr_t)parameter_type_qword*8u),8u);if(observed_attributes!=in->expected_attributes||!object_class(type_object,runtime_type_class)||!readable(type_object+(uintptr_t)type_handle_qword*8u,8u))return 13;memcpy(&type_descriptor,(const void*)(type_object+(uintptr_t)type_handle_qword*8u),8u);if(type_descriptor!=in->declared_descriptor)return 14;instance_noarg get_default=(instance_noarg)default_getter_pointer;uintptr_t first=get_default(parameter,default_getter_metadata),second=get_default(parameter,default_getter_metadata);managed_default_getter_invoked=1;if(first!=second)return 4;uint32_t flags=in->flags;uint64_t descriptor=in->declared_descriptor,raw=0,offset=0,units=0;if(!first){flags=(flags&~($dynamic_object|$reference_null_only|$boxed_null_contract))|$constant_null;}else{uintptr_t observed_class=0;memcpy(&observed_class,(const void*)first,8u);observed_default_class=observed_class;observed_default_object=first;if(observed_class==sentinel_class)return 5;if(observed_class==string_class){if(!(flags&($constant_string|$dynamic_object)))return 6;flags=(flags&~($dynamic_object|$reference_null_only|$boxed_null_contract))|$constant_string;descriptor=string_descriptor;if(!append_utf16(first,&offset,&units))return 7;}else{const primitive_record*p=primitive(observed_class);if((flags&$boxed_null_contract)&&observed_class==in->expected_class){flags=$constant_null|$normalized_boxed_null;}else if(observed_class==in->expected_class){;}else if(observed_class==in->alternate_class&&in->alternate_class){;}else if(p){flags=p->flags;descriptor=p->descriptor;}else if(!missing_class||(observed_class==missing_class&&first==missing_object)){if(!missing_class){missing_class=observed_class;missing_object=first;}flags=$missing_value;missing_count++;}else{flags=$runtime_object;raw=first;offset=observed_class;runtime_object_count++;}if(!(flags&($missing_value|$runtime_object|$constant_null))){uint32_t width=flags&0xffu;if(!width||width>8u||!readable(first+16u,width))return 11;memcpy(&raw,(const void*)(first+16u),width);}}}*out=(output_record){in->parameter_index,in->method_index,in->position,flags,descriptor,raw,offset,units};return 0;}
static int capture_batch(void){uint64_t end=cursor+BATCH;if(end>input_count)end=input_count;for(;cursor<end;cursor++){uint32_t error=0,retries=0;do{error=capture_one(&inputs[cursor],&records[cursor]);if(error!=1u&&error!=2u&&error!=15u)break;if(retries++>=8u)break;MemoryBarrier();}while(1);transient_retry_count+=retries;if(error){failure_kind=error;failure_cursor=cursor;return 0;}completed++;}return 1;}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);int ok=capture_batch();InterlockedExchange(&callback_complete,ok?1:-1);return ok;}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;static BOOL CALLBACK select_window(HWND w,LPARAM v){selection*s=(selection*)(uintptr_t)v;DWORD pid=0;RECT b;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){s->window=w;s->count++;}return TRUE;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1u||!s.window)return 0;message_id=RegisterWindowMessageW(status_path);SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);int ok=message_id&&(original_proc||GetLastError()==ERROR_SUCCESS);while(ok&&cursor<input_count){DWORD_PTR result=0;InterlockedExchange(&callback_complete,0);ok=SendMessageTimeoutW(s.window,message_id,0,0,SMTO_BLOCK,60000,&result)!=0&&InterlockedCompareExchange(&callback_complete,0,0)==1;}if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);return ok;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE f=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL,*buffer=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,os);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(a,&h,object,os,NULL,0,0)<0)ok=0;while(ok){DWORD n=0;if(!ReadFile(f,buffer,1048576u,&n,NULL)){ok=0;break;}if(!n)break;if(BCryptHashData(h,buffer,n,0)<0)ok=0;}if(ok&&BCryptFinishHash(h,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,output);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(f);return ok;}
static int sha256_payload(unsigned char output[32]){BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL;int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,os);if(ok&&!object)ok=0;if(ok&&BCryptCreateHash(a,&h,object,os,NULL,0,0)<0)ok=0;if(ok&&input_count&&BCryptHashData(h,(PUCHAR)records,(ULONG)(input_count*sizeof(*records)),0)<0)ok=0;if(ok&&string_bytes&&BCryptHashData(h,(PUCHAR)strings,(ULONG)string_bytes,0)<0)ok=0;if(ok&&BCryptFinishHash(h,output,32u,0)<0)ok=0;if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(object)HeapFree(GetProcessHeap(),0,object);return ok;}
static int executable_identity(char output[65]){wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,(DWORD)(sizeof(p)/sizeof(p[0])));return n&&n<sizeof(p)/sizeof(p[0])&&sha256_file(p,output);}
static int write_output(void){output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"BALV2PD1",8);h.version=1;h.header_bytes=sizeof(h);h.record_bytes=sizeof(output_record);h.count=input_count;h.string_bytes=string_bytes;h.process_id=expected_pid;memcpy(h.executable,executable_sha,64);memcpy(h.methods,method_sha,64);FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;int ok=fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(records,sizeof(*records),(SIZE_T)input_count,f)==input_count&&fwrite(strings,1,(SIZE_T)string_bytes,f)==string_bytes;if(fclose(f))ok=0;if(!ok)_wremove(output_path);return ok;}
static void write_status(const char*status,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"expected_count\": %llu,\n  \"completed_count\": %llu,\n  \"string_bytes\": %llu,\n  \"missing_value_count\": %llu,\n  \"runtime_object_count\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"failure_cursor_owner_only\": %llu,\n  \"transient_retry_count\": %llu,\n  \"observed_parameter_count_owner_only\": %u,\n  \"observed_default_class_owner_only\": %llu,\n  \"observed_default_object_owner_only\": %llu,\n  \"missing_class_owner_only\": %llu,\n  \"missing_object_owner_only\": %llu,\n  \"array_length_qword_owner_only\": %u,\n  \"array_vector_qword_owner_only\": %u,\n  \"default_field_qword_owner_only\": %u,\n  \"default_getter_offset_candidate_count\": %u,\n  \"parameter_attribute_offset_owner_only\": %u,\n  \"parameter_type_qword_owner_only\": %u,\n  \"type_handle_qword_owner_only\": %u,\n  \"metadata_token_rid_base\": %u,\n  \"output_written\": %s,\n  \"two_observations_match\": %s,\n  \"fresh_runtime_observation\": true,\n  \"default_cache_contract_derived_from_current_runtime\": true,\n  \"parameter_identity_definition_order_derived\": true,\n  \"constructor_classification_from_returned_object_class\": true,\n  \"member_info_token_getter_invoked_on_parameter\": false,\n  \"managed_default_getter_invoked\": %s,\n  \"legacy_runtime_dispatch_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)input_count,(unsigned long long)completed,(unsigned long long)string_bytes,(unsigned long long)missing_count,(unsigned long long)runtime_object_count,failure_kind,(unsigned long long)failure_cursor,(unsigned long long)transient_retry_count,observed_parameter_count,(unsigned long long)observed_default_class,(unsigned long long)observed_default_object,(unsigned long long)missing_class,(unsigned long long)missing_object,array_length_qword,array_vector_qword,default_field_qword,default_getter_offset_candidate_count,parameter_attribute_offset,parameter_type_qword,type_handle_qword,metadata_token_rid_base,written?"true":"false",observations_match?"true":"false",managed_default_getter_invoked?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char executable[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(executable)||strcmp(executable,executable_sha)){failure_kind=100u;write_status("identity_mismatch",0);return 0;}if(!verify_default_getter()){failure_kind=101u;write_status("contract_mismatch",0);return 0;}records=(output_record*)calloc((SIZE_T)input_count,sizeof(*records));if(!records){failure_kind=102u;write_status("allocation_failed",0);return 0;}int ok=dispatch();unsigned char first[32],second[32];if(!ok||completed!=input_count||!sha256_payload(first)){if(!failure_kind)failure_kind=103u;write_status("capture_failed",0);return 0;}uint64_t first_missing_count=missing_count,first_runtime_object_count=runtime_object_count;cursor=0;completed=0;string_bytes=0;missing_count=0;runtime_object_count=0;memset(records,0,(SIZE_T)input_count*sizeof(*records));failure_kind=0;ok=dispatch();if(!ok||completed!=input_count||missing_count!=first_missing_count||runtime_object_count!=first_runtime_object_count||!sha256_payload(second)||memcmp(first,second,sizeof(first))){if(!failure_kind)failure_kind=104u;write_status("repeat_observation_mismatch",0);return 0;}observations_match=1;ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def _source(binding: dict[str, Any], output: Path, status: Path) -> str:
    inputs = ",".join(
        "{%du,%du,%du,%du,%dull,%dull,%du,%du,%dull,%dull,%dull}"
        % (
            row["method_index"], row["parameter_index"], row["position"],
            row["flags"], row["method_metadata"], row["owner_descriptor"],
            row["expected_token"], row["expected_attributes"],
            row["declared_descriptor"], row["expected_class"],
            row["alternate_class"],
        )
        for row in binding["rows"]
    )
    primitives = ",".join(
        "{%dull,%dull,%du,0u}" % (
            row["class"], row["descriptor"], row["flags"]
        )
        for row in binding["primitive_rows"]
    )
    operations = binding["operations"]
    return _COLLECTOR.substitute(
        header_bytes=RUNTIME_PARAMETER_DEFAULT_HEADER.size,
        record_bytes=RUNTIME_PARAMETER_DEFAULT_RECORD.size,
        process_id=binding["process_id"],
        executable_sha=binding["binary"]["sha256"],
        method_sha=binding["method_detail_inventory"]["sha256"],
        parameter_class=binding["parameter_class"],
        sentinel_class=binding["sentinel_class"],
        runtime_type_class=binding["runtime_type_class"],
        string_class=binding["string_class"],
        string_descriptor=binding["string_descriptor"],
        method_class=binding["method_class"],
        constructor_class=binding["constructor_class"],
        default_field_qword=binding["default_field_qword"],
        parameter_attribute_offset=binding["parameter_attribute_offset"],
        parameter_type_qword=binding["parameter_type_qword"],
        type_handle_qword=binding["type_handle_qword"],
        metadata_token_rid_base=binding["metadata_token_rid_base"],
        from_handle_pointer=operations["method_from_handle"]["pointer"],
        from_handle_metadata=operations["method_from_handle"]["metadata"],
        method_parameters_pointer=operations["method_parameters"]["pointer"],
        method_parameters_metadata=operations["method_parameters"]["metadata"],
        constructor_parameters_pointer=operations["constructor_parameters"]["pointer"],
        constructor_parameters_metadata=operations["constructor_parameters"]["metadata"],
        default_getter_pointer=operations["default_getter"]["pointer"],
        default_getter_metadata=operations["default_getter"]["metadata"],
        input_rows=inputs,
        primitive_rows=primitives,
        input_count=len(binding["rows"]),
        primitive_count=len(binding["primitive_rows"]),
        output_path=_wide_literal(_windows_z_path(output)),
        status_path=_wide_literal(_windows_z_path(status)),
        status_schema=RUNTIME_PARAMETER_DEFAULT_STATUS_SCHEMA,
        constant_null=CONSTANT_NULL,
        constant_string=CONSTANT_STRING,
        dynamic_object=PARAMETER_DEFAULT_DYNAMIC_OBJECT,
        reference_null_only=PARAMETER_DEFAULT_REFERENCE_NULL_ONLY,
        missing_value=PARAMETER_DEFAULT_MISSING,
        runtime_object=PARAMETER_DEFAULT_RUNTIME_OBJECT,
        boxed_null_contract=PARAMETER_DEFAULT_BOXED_NULL_CONTRACT,
        normalized_boxed_null=PARAMETER_DEFAULT_NORMALIZED_BOXED_NULL,
    )


def prepare_runtime_parameter_defaults(
    *, native_output_receipt: Path, runtime_materializer_model: Path,
    runtime_inventory_dispatch: Path | None, output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        native_output_receipt=native_output_receipt,
        runtime_materializer_model=runtime_materializer_model,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
    )
    output = output_dir / "runtime-parameter-defaults.private.bin"
    status = output_dir / "runtime-parameter-defaults-status.private.json"
    model = output_dir / "runtime-parameter-defaults.private.json"
    plan_path = output_dir / "runtime-parameter-defaults-plan.private.json"
    build = _owner_directory(output_dir / "build-runtime-parameter-defaults")
    source = build / "runtime-parameter-defaults.c"
    injector_source = build / "runtime-parameter-defaults-injector.c"
    injector = build / "alpha-runtime-parameter-defaults-injector.exe"
    for stale in (output, status, model):
        stale.unlink(missing_ok=True)
    _private_text(source, _source(binding, output, status))
    _private_text(injector_source, runtime_injector_source())
    collector = build / (
        "alpha-runtime-parameter-defaults-"
        + file_identity(source)["sha256"][:12]
        + ".dll"
    )
    cc = _compiler(compiler)
    _build(
        [str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra",
         "-Wformat=2", "-Werror=format", str(source), "-o",
         str(collector), "-lbcrypt"],
        label="runtime parameter default collector",
    )
    _build(
        [str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
         "-Wformat=2", "-Werror=format", str(injector_source), "-o",
         str(injector)],
        label="runtime parameter default injector",
    )
    for artifact in (collector, injector):
        artifact.chmod(0o600)
    contract_rows = [
        {key: int(row[key]) for key in (
            "parameter_index", "method_index", "position", "flags",
            "expected_token", "expected_attributes", "declared_descriptor",
        )}
        for row in binding["rows"]
    ]
    plan = {
        "schema": RUNTIME_PARAMETER_DEFAULT_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": binding["binary"]["path"],
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
        },
        "inputs": {
            **{"constructed_extent_" + key: value for key, value in binding["extent_operation_sources"].items()},
            "native_output_receipt": binding["receipt"],
            "runtime_materializer_model": binding["runtime_materializer_model"],
            "reflection_semantics": binding["reflection_semantics"],
            "class_model": binding["class_model"],
            "runtime_snapshot": binding["runtime_snapshot"],
            "method_detail_status": binding["method_detail_status"],
            "type_identity_model": binding["type_identity_model"],
            "method_detail_inventory": binding["method_detail_inventory"],
            "constructed_generic_layout_model": binding[
                "constructed_generic_layout_model"
            ],
            "constructed_generic_layout_inventory": binding[
                "constructed_generic_layout_inventory"
            ],
        },
        "concrete_method_semantics": binding["concrete_method_semantics"],
        "contract": {
            "default_count": len(contract_rows),
            "metadata_token_rid_base": binding["metadata_token_rid_base"],
            "parameter_attribute_offset_owner_only": binding[
                "parameter_attribute_offset"
            ],
            "parameter_type_qword_owner_only": binding["parameter_type_qword"],
            "type_handle_qword_owner_only": binding["type_handle_qword"],
            "object_header_size_owner_only": binding[
                "object_header_size_owner_only"
            ],
            "rows": contract_rows,
        },
        "collector": file_identity(collector),
        "injector": file_identity(injector),
        "output_path": str(output),
        "status_path": str(status),
        "model_path": str(model),
        "policy": {
            "all_has_default_parameters_included": True,
            "parameter_tokens_reconstructed_from_exact_definition_order": True,
            "parameter_token_rid_base_current_runtime_cross_table_validated": True,
            "parameter_default_cache_field_runtime_derived": True,
            "managed_default_getter_invoked": True,
            "member_info_token_getter_invoked_on_parameter": False,
            "constructor_classification_from_returned_object_class": True,
            "concrete_method_semantics_current_structure_derived": True,
            "legacy_runtime_dispatch_used": False,
            "strings_captured_as_exact_utf16": True,
            "payload_free_open_reference_defaults_normalized": True,
            "two_observations_required": True,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
            "owner_only": True,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_PARAMETER_DEFAULT_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "counts": {"default_count": len(contract_rows)},
        "collector": plan["collector"],
        "policy": plan["policy"],
    }


def _validate(plan: dict[str, Any], status: dict[str, Any]) -> dict[str, Any]:
    path = _owner_file(Path(plan["output_path"]), label="inventory")
    raw = path.read_bytes()
    if len(raw) < RUNTIME_PARAMETER_DEFAULT_HEADER.size:
        raise AcquisitionError(
            "runtime parameter default inventory is truncated"
        )
    header = RUNTIME_PARAMETER_DEFAULT_HEADER.unpack_from(raw)
    expected_rows = plan["contract"]["rows"]
    expected = len(expected_rows)
    records_end = (
        RUNTIME_PARAMETER_DEFAULT_HEADER.size
        + expected * RUNTIME_PARAMETER_DEFAULT_RECORD.size
    )
    header_ok = (
        header[0] == RUNTIME_PARAMETER_DEFAULT_MAGIC
        and header[1] == RUNTIME_PARAMETER_DEFAULT_VERSION
        and header[2] == RUNTIME_PARAMETER_DEFAULT_HEADER.size
        and header[3] == RUNTIME_PARAMETER_DEFAULT_RECORD.size
        and header[4] == 0
        and header[5] == expected
        and header[7] == plan["target"]["process_id"]
        and header[8].decode("ascii") == plan["target"]["executable_sha256"]
        and header[9].decode("ascii")
        == plan["inputs"]["method_detail_inventory"]["sha256"]
        and len(raw) == records_end + header[6]
    )
    defaults: list[dict[str, Any]] = []
    records_ok = header_ok
    string_cursor = 0
    observed: set[int] = set()
    missing_count = 0
    runtime_object_count = 0
    normalized_boxed_null_count = 0
    for index in range(expected if header_ok else 0):
        (
            parameter_index, method_index, position, flags, descriptor,
            raw_value, string_offset, string_units,
        ) = RUNTIME_PARAMETER_DEFAULT_RECORD.unpack_from(
            raw,
            RUNTIME_PARAMETER_DEFAULT_HEADER.size
            + index * RUNTIME_PARAMETER_DEFAULT_RECORD.size,
        )
        expected_row = expected_rows[index]
        is_string = bool(flags & CONSTANT_STRING)
        is_null = bool(flags & CONSTANT_NULL)
        is_missing = bool(flags & PARAMETER_DEFAULT_MISSING)
        is_runtime_object = bool(flags & PARAMETER_DEFAULT_RUNTIME_OBJECT)
        is_normalized_boxed_null = bool(
            flags & PARAMETER_DEFAULT_NORMALIZED_BOXED_NULL
        )
        width = flags & 0xFF
        string_value: str | None = None
        if is_string and not is_null:
            end = string_offset + string_units * 2
            valid_string = (
                string_offset == string_cursor
                and end >= string_offset
                and end <= header[6]
            )
            if valid_string:
                try:
                    string_value = raw[
                        records_end + string_offset:records_end + end
                    ].decode("utf-16-le", errors="surrogatepass")
                except UnicodeDecodeError:
                    valid_string = False
            string_cursor = end
        elif is_runtime_object:
            valid_string = (
                raw_value > 0 and string_offset > 0 and string_units == 0
            )
        else:
            valid_string = string_offset == 0 and string_units == 0
        if is_missing:
            valid_value = (
                raw_value == 0 and width == 0 and not is_string and not is_null
            )
        elif is_runtime_object:
            valid_value = (
                width == 0 and not is_string and not is_null
                and not is_missing and raw_value > 0 and string_offset > 0
            )
        elif is_null:
            valid_value = raw_value == 0 and (is_string or width == 0)
        elif is_string:
            valid_value = width == 0 and raw_value == 0
        else:
            valid_value = width in (1, 2, 4, 8) and not (
                raw_value & ~((1 << (width * 8)) - 1)
            )
        contract_flags = int(expected_row["flags"])
        contract_kind = contract_flags & (
            PARAMETER_DEFAULT_DYNAMIC_OBJECT
            | PARAMETER_DEFAULT_REFERENCE_NULL_ONLY
        )
        if (
            parameter_index != expected_row["parameter_index"]
            or method_index != expected_row["method_index"]
            or position != expected_row["position"]
            or parameter_index in observed
            or not descriptor and not is_null
            or flags & (
                PARAMETER_DEFAULT_DYNAMIC_OBJECT
                | PARAMETER_DEFAULT_REFERENCE_NULL_ONLY
            )
            or (is_missing and flags != PARAMETER_DEFAULT_MISSING)
            or (
                is_runtime_object
                and flags != PARAMETER_DEFAULT_RUNTIME_OBJECT
            )
            or (
                is_normalized_boxed_null
                and (
                    flags
                    != (
                        CONSTANT_NULL
                        | PARAMETER_DEFAULT_NORMALIZED_BOXED_NULL
                    )
                    or not contract_flags
                    & PARAMETER_DEFAULT_BOXED_NULL_CONTRACT
                )
            )
            or not valid_string
            or not valid_value
            or (not contract_kind and not is_null and not is_missing
                and not contract_flags & CONSTANT_STRING
                and (flags & ~CONSTANT_NULL) != contract_flags)
        ):
            records_ok = False
            break
        observed.add(parameter_index)
        missing_count += is_missing
        runtime_object_count += is_runtime_object
        normalized_boxed_null_count += is_normalized_boxed_null
        kind = (
            "missing" if is_missing else "null" if is_null
            else "runtime_object" if is_runtime_object
            else "string" if is_string
            else "single" if flags & CONSTANT_SINGLE
            else "double" if flags & CONSTANT_DOUBLE
            else "boolean" if flags & CONSTANT_BOOLEAN
            else "char" if flags & CONSTANT_CHAR
            else "integer"
        )
        defaults.append({
            "parameter_index": parameter_index,
            "method_index": method_index,
            "position": position,
            "metadata_token": expected_row["expected_token"],
            "declared_descriptor": expected_row["declared_descriptor"],
            "value_type_descriptor": descriptor,
            "width": width,
            "signed": bool(flags & CONSTANT_SIGNED),
            "value_kind": kind,
            "typed_enum": bool(flags & CONSTANT_TYPED_ENUM),
            "raw_value": raw_value,
            "string_value": string_value,
            "payload_free_open_reference_box_normalized": (
                is_normalized_boxed_null
            ),
            "runtime_object_pointer_owner_only": (
                raw_value if is_runtime_object else None
            ),
            "runtime_object_class_owner_only": (
                string_offset if is_runtime_object else None
            ),
        })
    records_ok = records_ok and string_cursor == header[6]
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_PARAMETER_DEFAULT_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete"
        and status.get("output_written") is True,
        "header_bound": header_ok,
        "record_domain_closed": records_ok and len(defaults) == expected,
        "all_has_default_parameters_captured": status.get("completed_count")
        == expected,
        "missing_defaults_explicitly_classified": status.get(
            "missing_value_count"
        ) == missing_count,
        "runtime_objects_explicitly_classified": status.get(
            "runtime_object_count"
        ) == runtime_object_count,
        "no_unserializable_runtime_objects": runtime_object_count == 0,
        "missing_singleton_has_multiple_observations": (
            missing_count == 0 or missing_count >= 2
        ),
        "payload_free_open_reference_boxes_normalized": (
            plan.get("policy", {}).get(
                "payload_free_open_reference_defaults_normalized"
            )
            is True
            and normalized_boxed_null_count
            <= sum(
                bool(
                    int(row["flags"])
                    & PARAMETER_DEFAULT_BOXED_NULL_CONTRACT
                )
                for row in expected_rows
            )
        ),
        "string_payload_bound": status.get("string_bytes") == header[6],
        "two_observations_match": status.get("two_observations_match") is True,
        "definition_order_tokens_exact": all(
            int(row["expected_token"])
            == 0x08000000
            | (index + plan["contract"]["metadata_token_rid_base"])
            for index, row in (
                (int(row["parameter_index"]), row)
                for row in expected_rows
            )
        )
        and status.get("metadata_token_rid_base")
        == plan["contract"]["metadata_token_rid_base"],
        "parameter_layout_matches_method_detail": (
            status.get("parameter_attribute_offset_owner_only")
            == plan["contract"]["parameter_attribute_offset_owner_only"]
            and status.get("parameter_type_qword_owner_only")
            == plan["contract"]["parameter_type_qword_owner_only"]
            and status.get("type_handle_qword_owner_only")
            == plan["contract"]["type_handle_qword_owner_only"]
        ),
        "parameter_identity_runtime_validated_without_memberinfo_getter": (
            status.get("parameter_identity_definition_order_derived") is True
            and status.get(
                "constructor_classification_from_returned_object_class"
            ) is True
            and status.get("member_info_token_getter_invoked_on_parameter")
            is False
            and status.get("legacy_runtime_dispatch_used") is False
        ),
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
        is True,
        "runtime_cache_contract_derived": status.get(
            "default_cache_contract_derived_from_current_runtime"
        ) is True,
        "default_getter_layout_candidate_unique": status.get(
            "default_getter_offset_candidate_count"
        ) == 1,
        "managed_default_getter_runtime_observed": status.get(
            "managed_default_getter_invoked"
        ) is True,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime parameter default validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    from alpha.c04 import _verify_files
    _verify_files({key: value for key, value in plan["inputs"].items() if key.startswith("constructed_extent_")})
    return {
        "schema": RUNTIME_PARAMETER_DEFAULT_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": plan["inputs"],
        "inventory": file_identity(path),
        "status_receipt": file_identity(Path(plan["status_path"])),
        "counts": {
            "default_count": expected,
            "missing_default_count": missing_count,
            "runtime_object_default_count": runtime_object_count,
            "normalized_boxed_null_count": normalized_boxed_null_count,
            "materialized_default_count": (
                expected - missing_count - runtime_object_count
            ),
            "string_bytes": header[6],
        },
        "defaults": defaults,
        "checks": checks,
        "policy": plan["policy"],
    }


def capture_runtime_parameter_defaults(
    *, native_output_receipt: Path, runtime_materializer_model: Path,
    runtime_inventory_dispatch: Path | None, output_dir: Path, wine: Path,
    wineprefix: Path, compiler: Path | None = None, timeout: float = 300.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_parameter_defaults(
        native_output_receipt=native_output_receipt,
        runtime_materializer_model=runtime_materializer_model,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-parameter-defaults-plan.private.json"
    plan = read_json(plan_path)
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            [str(wine.expanduser().resolve()),
             _windows_z_path(Path(plan["injector"]["path"])),
             _windows_z_path(Path(plan["collector"]["path"])),
             Path(plan["target"]["executable_path"]).name],
            env=environment, check=False, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True, timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "runtime parameter default injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-parameter-defaults-injector.private.log",
        json.dumps({"returncode": injected.returncode,
                    "stdout": injected.stdout,
                    "stderr": injected.stderr},
                   ensure_ascii=False, indent=2) + "\n",
    )
    if injected.returncode:
        raise AcquisitionError("runtime parameter default injection failed")
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
        raise AcquisitionError("runtime parameter default capture timed out")
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime parameter default capture failed "
            f"(kind={status.get('failure_kind_owner_only')}, "
            f"completed={status.get('completed_count')})"
        )
    _seal_runtime_output(Path(plan["output_path"]))
    model = _validate(plan, status)
    model_path = Path(plan["model_path"])
    _private_json(
        model_path,
        {key: value for key, value in model.items() if key != "defaults"},
    )
    return {
        "schema": model["schema"], "status": model["status"],
        "target": model["target"], "counts": model["counts"],
        "checks": model["checks"], "policy": model["policy"],
        "model": file_identity(model_path), "inventory": model["inventory"],
    }


def load_runtime_parameter_defaults(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    plan_path = _owner_file(
        model_path.parent / "runtime-parameter-defaults-plan.private.json",
        label="plan",
    )
    status_path = _owner_file(
        model_path.parent / "runtime-parameter-defaults-status.private.json",
        label="status",
    )
    model, plan, status = (
        read_json(model_path), read_json(plan_path), read_json(status_path)
    )
    if (
        model.get("schema") != RUNTIME_PARAMETER_DEFAULT_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("inventory") != file_identity(inventory_path)
        or model.get("status_receipt") != file_identity(status_path)
        or plan.get("schema") != RUNTIME_PARAMETER_DEFAULT_PLAN_SCHEMA
        or Path(plan.get("output_path", "")).expanduser().resolve()
        != inventory_path
        or Path(plan.get("model_path", "")).expanduser().resolve()
        != model_path
        or (expected_executable_sha256 is not None
            and model.get("target", {}).get("executable_sha256")
            != expected_executable_sha256.lower())
    ):
        raise AcquisitionError("runtime parameter default binding is stale")
    current = _validate(plan, status)
    if (
        current["counts"] != model.get("counts")
        or current["checks"] != model.get("checks")
        or current["policy"] != model.get("policy")
    ):
        raise AcquisitionError(
            "runtime parameter default validation is stale"
        )
    return current
