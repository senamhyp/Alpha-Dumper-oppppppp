from alpha.h02 import windows_run as _host_run

import json
import os
import stat
import struct
import subprocess
import time
from collections import defaultdict
from itertools import permutations
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.p44 import load_runtime_enum_constants
from alpha.c06 import LiveRuntimeInventory
from alpha.p29 import _runtime
from alpha.p42 import _field_rows
from alpha.c04 import MappedPE
from alpha.p25 import TYPE_REFERENCE_ARRAY
from alpha.h02 import file_identity, read_json


RUNTIME_ASSEMBLY_IDENTITY_PLAN_SCHEMA = (
    "alpha.runtime-assembly-identity-plan/v1"
)
RUNTIME_ASSEMBLY_IDENTITY_STATUS_SCHEMA = (
    "alpha.runtime-assembly-identity-status/v1"
)
RUNTIME_ASSEMBLY_IDENTITY_SCHEMA = (
    "alpha.runtime-assembly-identity-inventory/v1"
)
RUNTIME_ASSEMBLY_IDENTITY_MAGIC = b"ALPHAAI1"
RUNTIME_ASSEMBLY_IDENTITY_VERSION = 1
RUNTIME_ASSEMBLY_IDENTITY_HEADER = struct.Struct("<8sIIIIQQQ64s64s")


RUNTIME_ASSEMBLY_IDENTITY_RECORD = struct.Struct("<IIIIIIIIiiiiIIIIQQQQQ")

_OPERATIONS = (
    "domain.current", "domain.assemblies", "assembly.name",
    "assembly_name.simple", "assembly_name.full",
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
            f"runtime assembly identity {label} is not owner-only"
        )
    return path


def _root_index(runtime: Any, descriptor: int) -> int | None:
    node_index = runtime.renderer.node_by_descriptor.get(descriptor)
    if node_index is None:
        return None
    row = runtime.renderer.reference_row(node_index)
    return runtime.renderer._root_alias(descriptor, row[1])


def _direct_reference_load(image: MappedPE, pointer: int) -> int | None:

    rva = pointer - image.image_base
    offset = image.rva_to_offset(rva)
    if offset is None:
        return None
    code = bytes(image._mapping[offset:offset + 16])
    if len(code) >= 5 and code[:3] == b"\x48\x8b\x41" and code[4] == 0xC3:
        return code[3]
    if len(code) >= 8 and code[:3] == b"\x48\x8b\x81" and code[7] == 0xC3:
        return int.from_bytes(code[3:7], "little")
    return None


def _binding(
    *, native_output_receipt: Path, runtime_materializer_model: Path,
    runtime_inventory_dispatch: Path | None,
) -> dict[str, Any]:


    del runtime_inventory_dispatch
    receipt, paths, runtime = _runtime(native_output_receipt)
    output_model = read_json(_owner_file(paths["model"], label="runtime model"))
    member_model_record = output_model.get("inputs", {}).get(
        "native_member_detail_model"
    )
    if not isinstance(member_model_record, dict):
        raise AcquisitionError(
            "runtime assembly identity native member model is unavailable"
        )
    member_model = read_json(_owner_file(
        Path(member_model_record["path"]), label="native member model"
    ))
    class_model_path = _owner_file(
        Path(member_model["inputs"]["class_model"]["path"]),
        label="class model",
    )
    class_model = read_json(class_model_path)
    class_checks = class_model.get("checks", {})
    if (
        class_model.get("status") != "discovered"
        or any(
            class_checks.get(key) is not True
            for key in (
                "all_contract_owner_classes_present",
                "all_observed_contract_owners_enumerated",
                "method_layout_semantically_unique",
                "method_pointer_field_unique",
                "snapshot_image_binding_matches",
                "vtable_boundary_derived",
            )
        )
        or any(
            class_checks.get(key) is not False
            for key in (
                "external_runtime_component_used", "fixed_address_used",
                "fixed_offset_used", "fixed_version_used",
                "saved_reference_values_used",
            )
        )
    ):
        raise AcquisitionError(
            "runtime assembly identity class model is incomplete"
        )

    live = LiveRuntimeInventory(
        materializer_model=runtime_materializer_model,
        binary=paths["binary"],
    )
    try:
        if live.process_id != receipt["target"].get("process_id", live.process_id):
            raise AcquisitionError(
                "runtime assembly identity process binding differs"
            )
        classes = {
            row["runtime_owner"]: int(row["class_pointer"])
            for row in class_model["classes"]
        }
        required_owners = (
            "System.AppDomain", "System.Reflection.Assembly",
            "System.Reflection.MonoAssembly", "System.Reflection.AssemblyName",
        )
        if any(owner not in classes for owner in required_owners):
            raise AcquisitionError(
                "runtime assembly identity owner classes are incomplete"
            )
        type_by_class = {
            live.type_row(index).class_pointer: index
            for index in range(runtime.type_count)
        }
        if any(classes[owner] not in type_by_class for owner in required_owners):
            raise AcquisitionError(
                "runtime assembly identity owner class binding differs"
            )
        appdomain_index = type_by_class[classes[required_owners[0]]]
        assembly_index = type_by_class[classes[required_owners[1]]]
        assembly_name_index = type_by_class[classes[required_owners[3]]]

        module_names = sorted(runtime.module_names.values())
        simple_module_names = [name.rsplit(".", 1)[0] for name in module_names]
        string_indexes = [
            index for index in range(runtime.type_count)
            if runtime.renderer.root_name(index) == "System.String"
        ]
        if (
            not module_names
            or len(module_names) != runtime.module_count
            or len(set(simple_module_names)) != len(simple_module_names)
            or len(string_indexes) != 1
        ):
            raise AcquisitionError(
                "runtime assembly identity module/string domain is ambiguous"
            )
        string_index = string_indexes[0]
        appdomain_descriptor = runtime.renderer.identity_row(appdomain_index)[2]
        assembly_name_descriptor = runtime.renderer.identity_row(
            assembly_name_index
        )[2]
        string_descriptor = runtime.renderer.identity_row(string_index)[2]

        def derives_from(index: int, base: int) -> bool:
            visited: set[int] = set()
            current = index
            while current not in visited:
                if current == base:
                    return True
                visited.add(current)
                parent_descriptor = int(runtime.renderer.graph_row(current)[3])
                if not parent_descriptor:
                    return False
                parent = _root_index(runtime, parent_descriptor)
                if parent is None:
                    return False
                current = parent
            return False

        assembly_classes = sorted({
            live.type_row(index).class_pointer
            for index in range(runtime.type_count)
            if derives_from(index, assembly_index)
        })
        if (
            len(assembly_classes) < 2
            or classes["System.Reflection.Assembly"] not in assembly_classes
            or classes["System.Reflection.MonoAssembly"] not in assembly_classes
        ):
            raise AcquisitionError(
                "runtime assembly identity concrete class closure is ambiguous"
            )

        def methods(owner: int) -> list[tuple[int, tuple[int, ...]]]:
            live_type = live.type_row(owner)
            return [
                (index, runtime.method_row(index))
                for index in range(
                    live_type.method_start,
                    live_type.method_start + live_type.method_count,
                )
            ]

        def operation(index: int) -> dict[str, int]:
            current = live.method_row(index)
            return {
                "method_index_owner_only": index,
                "method_pointer": current.function_pointer,
                "metadata_pointer": current.metadata_pointer,
            }

        current_candidates = [
            operation(index)
            for index, row in methods(appdomain_index)
            if row[10] == 0
            and row[5] & 0x10
            and _root_index(runtime, row[4]) == appdomain_index
        ]
        assembly_array_candidates: list[dict[str, int]] = []
        for index, row in methods(appdomain_index):
            if row[10] or row[5] & 0x10:
                continue
            reference_index = runtime.renderer.node_by_descriptor.get(row[4])
            if reference_index is None:
                continue
            reference = runtime.renderer.reference_row(reference_index)
            if (
                reference[4] & TYPE_REFERENCE_ARRAY
                and _root_index(runtime, reference[13]) == assembly_index
            ):
                assembly_array_candidates.append(operation(index))
        assembly_name_candidates = [
            operation(index)
            for index, row in methods(assembly_index)
            if row[10] == 0
            and not row[5] & 0x10
            and _root_index(runtime, row[4]) == assembly_name_index
        ]
        assembly_name_string_methods = [
            (index, row)
            for index, row in methods(assembly_name_index)
            if row[10] == 0
            and not row[5] & 0x10
            and _root_index(runtime, row[4]) == string_index
        ]
        with MappedPE(paths["binary"]) as image:
            direct_simple = [
                (index, _direct_reference_load(image, int(row[3])))
                for index, row in assembly_name_string_methods
                if _direct_reference_load(image, int(row[3])) is not None
            ]
        if (
            len(current_candidates) < 2
            or len(assembly_array_candidates) != 1
            or len(assembly_name_candidates) != 1
            or len(direct_simple) != 1
        ):
            raise AcquisitionError(
                "runtime assembly identity operation candidates are ambiguous: "
                f"current={len(current_candidates)}, "
                f"assemblies={len(assembly_array_candidates)}, "
                f"name={len(assembly_name_candidates)}, "
                f"simple={len(direct_simple)}"
            )
        simple_index, simple_load_offset = direct_simple[0]
        full_candidates = [
            operation(index)
            for index, _row in assembly_name_string_methods
            if index != simple_index
        ]
        if not full_candidates:
            raise AcquisitionError(
                "runtime assembly identity full-name behavior is absent"
            )

        field_by_index, fields_by_owner = _field_rows(runtime)
        assembly_fields = sorted(
            (
                field_by_index[index]
                for index in fields_by_owner[assembly_name_index]
                if not field_by_index[index]["attributes"] & 0x10
                and field_by_index[index]["managed_offset"] >= 0
            ),
            key=lambda row: int(row["managed_offset"]),
        )

        def is_enum(descriptor: int) -> bool:
            root = _root_index(runtime, descriptor)
            return root is not None and bool(
                runtime.renderer.identity_row(root)[1] & 0x20
            )

        def is_array(descriptor: int) -> bool:
            node = runtime.renderer.node_by_descriptor.get(descriptor)
            return node is not None and bool(
                runtime.renderer.reference_row(node)[4] & TYPE_REFERENCE_ARRAY
            )

        layout_candidates: list[list[dict[str, Any]]] = []
        for start in range(max(0, len(assembly_fields) - 15)):
            rows = assembly_fields[start:start + 16]
            if (
                len(rows) == 16
                and rows[0]["descriptor"] == rows[1]["descriptor"]
                and len({rows[index]["descriptor"] for index in range(2, 6)})
                == 1
                and all(is_enum(int(rows[index]["descriptor"]))
                        for index in (7, 8, 12, 14, 15))
                and rows[10]["descriptor"] == rows[11]["descriptor"]
                and is_array(int(rows[10]["descriptor"]))
                and all(
                    int(left["managed_offset"])
                    < int(right["managed_offset"])
                    for left, right in zip(rows, rows[1:])
                )
            ):
                layout_candidates.append(rows)
        if len(layout_candidates) != 1:
            raise AcquisitionError(
                "runtime assembly identity field topology is ambiguous"
            )
        layout = layout_candidates[0]
        object_header_size = int(simple_load_offset) - int(
            layout[0]["managed_offset"]
        )
        if object_header_size <= 0 or object_header_size & 7:
            raise AcquisitionError(
                "runtime assembly identity object header is ambiguous"
            )

        string_fields = sorted(
            (
                field_by_index[index]
                for index in fields_by_owner[string_index]
                if not field_by_index[index]["attributes"] & 0x10
                and field_by_index[index]["managed_offset"] >= 0
            ),
            key=lambda row: int(row["managed_offset"]),
        )
        string_layout_candidates = [
            pair
            for pair in zip(string_fields, string_fields[1:])
            if pair[0]["descriptor"] == layout[2]["descriptor"]
            and int(pair[1]["managed_offset"])
            > int(pair[0]["managed_offset"])
        ]
        if len(string_layout_candidates) != 1:
            raise AcquisitionError(
                "runtime assembly identity string layout is ambiguous"
            )
        string_length_field, string_data_field = string_layout_candidates[0]

        enum_model = paths.get("enum_constant_model")
        enum_inventory = paths.get("enum_constant_inventory")
        if enum_model is None or enum_inventory is None:
            raise AcquisitionError(
                "runtime assembly identity enum domain is unavailable"
            )
        constants = load_runtime_enum_constants(
            model_path=enum_model,
            inventory_path=enum_inventory,
            expected_executable_sha256=receipt["target"]["executable_sha256"],
        )
        enum_values: dict[int, list[int]] = defaultdict(list)
        for constant in constants["constants"]:
            if constant["enum_owner"]:
                enum_values[int(constant["owner_type_index"])].append(
                    int(constant["raw_value"])
                )
        flag_hash_fields = layout[7:9]
        hash_candidates = [
            field
            for field in flag_hash_fields
            if any(
                value > 0 and value & (value - 1) != 0
                for value in enum_values.get(
                    _root_index(runtime, int(field["descriptor"])), []
                )
            )
        ]
        if len(hash_candidates) != 1:
            raise AcquisitionError(
                "runtime assembly identity hash field is ambiguous"
            )
        hash_field = hash_candidates[0]
        flags_field = next(
            field for field in flag_hash_fields if field is not hash_field
        )

        def actual_offset(field: dict[str, Any]) -> int:
            return object_header_size + int(field["managed_offset"])

        operations = {
            "domain.current": current_candidates,
            "domain.assemblies": assembly_array_candidates,
            "assembly.name": assembly_name_candidates,
            "assembly_name.simple": [operation(simple_index)],
            "assembly_name.full": full_candidates,
        }
        return {
            "receipt": file_identity(native_output_receipt.expanduser().resolve()),
            "runtime_materializer_model": file_identity(
                runtime_materializer_model.expanduser().resolve()
            ),
            "class_model": file_identity(class_model_path),
            "enum_constant_model": file_identity(enum_model),
            "enum_constant_inventory": file_identity(enum_inventory),
            "event_module_inventory": file_identity(paths["event_module_inventory"]),
            "binary": file_identity(paths["binary"]),
            "target": receipt["target"],
            "process_id": live.process_id,
            "expected_count": runtime.module_count,
            "module_names": module_names,
            "operations": operations,
            "appdomain_class": classes["System.AppDomain"],
            "assembly_classes": assembly_classes,
            "assembly_name_class": classes["System.Reflection.AssemblyName"],
            "string_class": live.type_row(string_index).class_pointer,
            "layout": {
                "candidate_count": len(layout_candidates),
                "object_header_size_owner_only": object_header_size,
                "string_length_offset": object_header_size
                + int(string_length_field["managed_offset"]),
                "string_data_offset": object_header_size
                + int(string_data_field["managed_offset"]),
                "version_offsets": [actual_offset(field) for field in layout[2:6]],
                "flags_offset": actual_offset(flags_field),
                "hash_algorithm_offset": actual_offset(hash_field),
                "version_compatibility_offset": actual_offset(layout[12]),
                "key_candidate_offsets": [
                    actual_offset(layout[10]), actual_offset(layout[11]),
                ],
            },
            "evidence": {
                "current_domain_candidate_count": len(current_candidates),
                "assembly_array_candidate_count": len(assembly_array_candidates),
                "assembly_name_candidate_count": len(assembly_name_candidates),
                "simple_name_candidate_count": len(direct_simple),
                "full_name_candidate_count": len(full_candidates),
                "hash_field_candidate_count": len(hash_candidates),
                "field_layout_candidate_count": len(layout_candidates),
                "assembly_class_closure_count": len(assembly_classes),
            },
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
typedef struct output_header{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t count,payload_bytes,process_id;char executable[64],modules[64];}output_header;
typedef struct output_record{uint32_t name_bytes,culture_bytes,full_name_bytes,name_flags,hash_algorithm,version_compatibility,reserved0,reserved1;int32_t major,minor,build,revision;uint32_t token_bytes,key_bytes,reserved2,reserved3;uint64_t name_offset,culture_offset,full_name_offset,token_offset,key_offset;}output_record;
_Static_assert(sizeof(output_header)==$header_bytes,"assembly identity header");
_Static_assert(sizeof(output_record)==$record_bytes,"assembly identity record");
static const DWORD expected_pid=$process_id;static const uint64_t expected_count=$expected_count;
static const char executable_sha[]="$executable_sha",module_sha[]="$module_sha";
static const uintptr_t appdomain_class=$appdomain_class,assembly_name_class=$assembly_name_class,string_class=$string_class;
static const uintptr_t assembly_classes[]={$assembly_classes};static const uint32_t assembly_class_count=$assembly_class_count;
static const uint32_t string_length_offset=$string_length_offset,string_data_offset=$string_data_offset;
static const uint32_t version_offsets[4]={$version_offsets};
static const uint32_t flags_offset=$flags_offset,hash_algorithm_offset=$hash_algorithm_offset,version_compatibility_offset=$version_compatibility_offset;
static const uint32_t key_candidate_offsets[2]={$key_candidate_offsets};
$operation_constants
static const wchar_t output_path[]=$output_path,status_path[]=$status_path;
typedef uintptr_t(*static_noarg)(uintptr_t);typedef uintptr_t(*instance_noarg)(uintptr_t,uintptr_t);typedef uint32_t(*instance_dword)(uintptr_t,uintptr_t);
static output_record*records;static unsigned char*payload;static uint64_t payload_bytes,payload_capacity,completed;static uintptr_t unexpected_assembly_class;static uint32_t failure_kind,array_length_qword,array_vector_qword;static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_complete;static int two_observations_match;
static int readable(uintptr_t v,SIZE_T n){MEMORY_BASIC_INFORMATION r;if(!v||!n||v+n<v||!VirtualQuery((const void*)v,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t e=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&e>=v&&v+n<=e;}
static int object_class(uintptr_t o,uintptr_t c){uintptr_t v=0;if(!readable(o,8u))return 0;memcpy(&v,(const void*)o,8u);return v==c;}
static int assembly_object(uintptr_t o){uintptr_t c=0;if(!readable(o,8u))return 0;memcpy(&c,(const void*)o,8u);for(uint32_t i=0;i<assembly_class_count;i++)if(c==assembly_classes[i])return 1;if(!unexpected_assembly_class)unexpected_assembly_class=c;return 0;}
static int append(const void*value,uint32_t bytes,uint64_t*offset){if(!bytes){*offset=0;return 1;}uint64_t required=payload_bytes+bytes;if(required<payload_bytes)return 0;if(required>payload_capacity){uint64_t capacity=payload_capacity?payload_capacity:65536u;while(capacity<required){if(capacity>UINT64_MAX/2u)return 0;capacity*=2u;}unsigned char*grown=(unsigned char*)realloc(payload,(SIZE_T)capacity);if(!grown)return 0;payload=grown;payload_capacity=capacity;}*offset=payload_bytes;memcpy(payload+payload_bytes,value,bytes);payload_bytes=required;return 1;}
static int managed_utf8(uintptr_t object,int allow_empty,char**output,uint32_t*bytes){*output=NULL;*bytes=0;if(!object)return allow_empty;if(!object_class(object,string_class)||!readable(object+string_length_offset,4u))return 0;int32_t length=0;memcpy(&length,(const void*)(object+string_length_offset),4u);if(length<0||(!allow_empty&&!length)||(uint32_t)length>16777216u||(length&&!readable(object+string_data_offset,(SIZE_T)length*2u)))return 0;if(!length)return 1;int n=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,(const wchar_t*)(object+string_data_offset),length,NULL,0,NULL,NULL);if(n<=0)return 0;char*value=(char*)malloc((SIZE_T)n);if(!value||WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,(const wchar_t*)(object+string_data_offset),length,value,n,NULL,NULL)!=n){free(value);return 0;}*output=value;*bytes=(uint32_t)n;return 1;}
static int managed_string_equal(uintptr_t a,uintptr_t b){if(a==b)return object_class(a,string_class);if(!object_class(a,string_class)||!object_class(b,string_class)||!readable(a+string_length_offset,4u)||!readable(b+string_length_offset,4u))return 0;int32_t an=0,bn=0;memcpy(&an,(const void*)(a+string_length_offset),4u);memcpy(&bn,(const void*)(b+string_length_offset),4u);return an>=0&&an==bn&&(!an||(readable(a+string_data_offset,(SIZE_T)an*2u)&&readable(b+string_data_offset,(SIZE_T)bn*2u)&&memcmp((const void*)(a+string_data_offset),(const void*)(b+string_data_offset),(SIZE_T)an*2u)==0));}
static int object_array(uintptr_t array,uintptr_t**items,uint32_t*count,int derive){*items=NULL;*count=0;if(!array||!readable(array,80u))return 0;if(derive&&!array_length_qword){for(uint32_t l=1;l<8u;l++){uintptr_t n=0;memcpy(&n,(const void*)(array+(uintptr_t)l*8u),8u);if(n!=expected_count)continue;for(uint32_t v=l+1u;v<10u;v++){uintptr_t p=array+(uintptr_t)v*8u;if(!readable(p,n*8u))continue;uint64_t i=0;for(;i<n;i++){uintptr_t o=0;memcpy(&o,(const void*)(p+i*8u),8u);if(!assembly_object(o))break;}if(i==n){if(array_length_qword)return 0;array_length_qword=l;array_vector_qword=v;}}}}if(!array_length_qword)return 0;uintptr_t n=0;memcpy(&n,(const void*)(array+(uintptr_t)array_length_qword*8u),8u);uintptr_t p=array+(uintptr_t)array_vector_qword*8u;if(n!=expected_count||!readable(p,n*8u))return 0;for(uint64_t i=0;i<n;i++){uintptr_t o=0;memcpy(&o,(const void*)(p+i*8u),8u);if(!assembly_object(o))return 0;}*items=(uintptr_t*)p;*count=(uint32_t)n;return 1;}
static int byte_array(uintptr_t array,const unsigned char**value,uint32_t*bytes){*value=NULL;*bytes=0;if(!array)return 1;if(!array_length_qword||!readable(array,((SIZE_T)array_vector_qword+1u)*8u))return 0;uintptr_t n=0;memcpy(&n,(const void*)(array+(uintptr_t)array_length_qword*8u),8u);uintptr_t p=array+(uintptr_t)array_vector_qword*8u;if(n>16777216u||(n&&!readable(p,n)))return 0;*value=(const unsigned char*)p;*bytes=(uint32_t)n;return 1;}
static int capture(void){uintptr_t domain=0;for(uint32_t i=0;i<domain_current_operation_count;i++){static_noarg call=(static_noarg)domain_current_operations[i].pointer;uintptr_t current=call(domain_current_operations[i].metadata);if(!object_class(current,appdomain_class))return 1;if(!domain)domain=current;else if(domain!=current)return 2;}if(!domain)return 3;instance_noarg assemblies=(instance_noarg)domain_assemblies_operations[0].pointer;uintptr_t array=assemblies(domain,domain_assemblies_operations[0].metadata),*items=NULL;uint32_t count=0;if(!object_array(array,&items,&count,1)||count!=expected_count)return 4;records=(output_record*)calloc(count,sizeof(*records));if(!records)return 5;for(uint32_t i=0;i<count;i++){uintptr_t assembly=items[i];instance_noarg get_name=(instance_noarg)assembly_name_operations[0].pointer;uintptr_t name_object=get_name(assembly,assembly_name_operations[0].metadata);if(!object_class(name_object,assembly_name_class))return 6;instance_noarg get_simple=(instance_noarg)assembly_name_simple_operations[0].pointer;uintptr_t simple_object=get_simple(name_object,assembly_name_simple_operations[0].metadata),full_object=0;for(uint32_t j=0;j<assembly_name_full_operation_count;j++){instance_noarg get_full=(instance_noarg)assembly_name_full_operations[j].pointer;uintptr_t candidate=get_full(name_object,assembly_name_full_operations[j].metadata);if(!object_class(candidate,string_class))return 7;if(!full_object)full_object=candidate;else if(!managed_string_equal(full_object,candidate))return 8;}char*simple=NULL,*full=NULL;uint32_t simple_bytes=0,full_bytes=0;if(!managed_utf8(simple_object,0,&simple,&simple_bytes)||!managed_utf8(full_object,0,&full,&full_bytes))return 9;output_record*r=&records[i];if(!readable(name_object+version_offsets[0],4u)||!readable(name_object+version_offsets[1],4u)||!readable(name_object+version_offsets[2],4u)||!readable(name_object+version_offsets[3],4u)||!readable(name_object+flags_offset,4u)||!readable(name_object+hash_algorithm_offset,4u)||!readable(name_object+version_compatibility_offset,4u)||!readable(name_object+key_candidate_offsets[0],8u)||!readable(name_object+key_candidate_offsets[1],8u)){free(simple);free(full);return 10;}memcpy(&r->major,(const void*)(name_object+version_offsets[0]),4u);memcpy(&r->minor,(const void*)(name_object+version_offsets[1]),4u);memcpy(&r->build,(const void*)(name_object+version_offsets[2]),4u);memcpy(&r->revision,(const void*)(name_object+version_offsets[3]),4u);memcpy(&r->name_flags,(const void*)(name_object+flags_offset),4u);memcpy(&r->hash_algorithm,(const void*)(name_object+hash_algorithm_offset),4u);memcpy(&r->version_compatibility,(const void*)(name_object+version_compatibility_offset),4u);uintptr_t key_objects[2]={0,0};memcpy(&key_objects[0],(const void*)(name_object+key_candidate_offsets[0]),8u);memcpy(&key_objects[1],(const void*)(name_object+key_candidate_offsets[1]),8u);const unsigned char*key_values[2]={NULL,NULL};uint32_t key_bytes[2]={0,0};if(!byte_array(key_objects[0],&key_values[0],&key_bytes[0])||!byte_array(key_objects[1],&key_values[1],&key_bytes[1])){free(simple);free(full);return 11;}r->name_bytes=simple_bytes;r->culture_bytes=0;r->full_name_bytes=full_bytes;r->token_bytes=key_bytes[0];r->key_bytes=key_bytes[1];if(!append(simple,simple_bytes,&r->name_offset)||!append(NULL,0,&r->culture_offset)||!append(full,full_bytes,&r->full_name_offset)||!append(key_values[0],key_bytes[0],&r->token_offset)||!append(key_values[1],key_bytes[1],&r->key_offset)){free(simple);free(full);return 12;}free(simple);free(full);completed++;}return 0;}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);failure_kind=capture();InterlockedExchange(&callback_complete,failure_kind?-1:1);return failure_kind?0:1;}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;static BOOL CALLBACK select_window(HWND w,LPARAM v){selection*s=(selection*)(uintptr_t)v;DWORD pid=0;RECT b;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){s->window=w;s->count++;}return TRUE;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1u||!s.window)return 0;message_id=RegisterWindowMessageW(status_path);SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);int ok=message_id&&(original_proc||GetLastError()==ERROR_SUCCESS);DWORD_PTR result=0;InterlockedExchange(&callback_complete,0);ok=ok&&SendMessageTimeoutW(s.window,message_id,0,0,SMTO_BLOCK,60000,&result)!=0&&InterlockedCompareExchange(&callback_complete,0,0)==1;if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);return ok;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_blocks(const void*a,SIZE_T an,const void*b,SIZE_T bn,unsigned char d[32]){BCRYPT_ALG_HANDLE p=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL;int ok=BCryptOpenAlgorithmProvider(&p,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(p,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=(unsigned char*)HeapAlloc(GetProcessHeap(),0,os);if(ok&&!object)ok=0;if(ok&&BCryptCreateHash(p,&h,object,os,NULL,0,0)<0)ok=0;if(ok&&an&&BCryptHashData(h,(PUCHAR)a,(ULONG)an,0)<0)ok=0;if(ok&&bn&&BCryptHashData(h,(PUCHAR)b,(ULONG)bn,0)<0)ok=0;if(ok&&BCryptFinishHash(h,d,32u,0)<0)ok=0;if(h)BCryptDestroyHash(h);if(p)BCryptCloseAlgorithmProvider(p,0);if(object)HeapFree(GetProcessHeap(),0,object);return ok;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE f=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL,*buffer=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,os);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(a,&h,object,os,NULL,0,0)<0)ok=0;while(ok){DWORD n=0;if(!ReadFile(f,buffer,1048576u,&n,NULL)){ok=0;break;}if(!n)break;if(BCryptHashData(h,buffer,n,0)<0)ok=0;}if(ok&&BCryptFinishHash(h,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,output);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(f);return ok;}
static int executable_identity(char output[65]){wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,(DWORD)(sizeof(p)/sizeof(p[0])));return n&&n<sizeof(p)/sizeof(p[0])&&sha256_file(p,output);}
static int write_output(void){uint64_t base=sizeof(output_header)+expected_count*sizeof(output_record);for(uint64_t i=0;i<expected_count;i++){output_record*r=&records[i];if(r->name_bytes)r->name_offset+=base;if(r->culture_bytes)r->culture_offset+=base;if(r->full_name_bytes)r->full_name_offset+=base;if(r->token_bytes)r->token_offset+=base;if(r->key_bytes)r->key_offset+=base;}output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"ALPHAAI1",8);h.version=1;h.header_bytes=sizeof(h);h.record_bytes=sizeof(output_record);h.count=expected_count;h.payload_bytes=payload_bytes;h.process_id=expected_pid;memcpy(h.executable,executable_sha,64);memcpy(h.modules,module_sha,64);FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;int ok=fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(records,sizeof(*records),(SIZE_T)expected_count,f)==expected_count&&fwrite(payload,1,(SIZE_T)payload_bytes,f)==payload_bytes;if(fclose(f))ok=0;if(!ok)_wremove(output_path);return ok;}
static void write_status(const char*status,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"expected_count\": %llu,\n  \"completed_count\": %llu,\n  \"payload_bytes\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"unexpected_assembly_class_owner_only\": %llu,\n  \"output_written\": %s,\n  \"two_observations_match\": %s,\n  \"fresh_runtime_observation\": true,\n  \"all_identity_operations_current_runtime_derived\": true,\n  \"operation_candidate_sets_structurally_closed\": true,\n  \"field_layout_current_runtime_derived\": true,\n  \"legacy_runtime_dispatch_used\": false,\n  \"saved_assembly_identity_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)expected_count,(unsigned long long)completed,(unsigned long long)payload_bytes,failure_kind,(unsigned long long)unexpected_assembly_class,written?"true":"false",two_observations_match?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char executable[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(executable)||strcmp(executable,executable_sha)){failure_kind=100u;write_status("identity_mismatch",0);return 0;}unsigned char first[32],second[32];int ok=dispatch();if(!ok||completed!=expected_count||!sha256_blocks(records,(SIZE_T)expected_count*sizeof(*records),payload,(SIZE_T)payload_bytes,first)){if(!failure_kind)failure_kind=101u;write_status("capture_failed",0);return 0;}free(records);records=NULL;free(payload);payload=NULL;payload_bytes=0;payload_capacity=0;completed=0;failure_kind=0;ok=dispatch();if(!ok||completed!=expected_count||!sha256_blocks(records,(SIZE_T)expected_count*sizeof(*records),payload,(SIZE_T)payload_bytes,second)||memcmp(first,second,sizeof(first))){if(!failure_kind)failure_kind=102u;write_status("repeat_observation_mismatch",0);return 0;}two_observations_match=1;ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def _source(binding: dict[str, Any], output: Path, status: Path) -> str:
    constants = [
        "typedef struct operation{uintptr_t pointer,metadata;}operation;"
    ]
    for key in _OPERATIONS:
        symbol = key.replace(".", "_")
        operations = binding["operations"][key]
        constants.append(
            f"static const operation {symbol}_operations[]={{"
            + ",".join(
                "{%dull,%dull}" % (
                    operation["method_pointer"],
                    operation["metadata_pointer"],
                )
                for operation in operations
            )
            + "};"
            + f"static const uint32_t {symbol}_operation_count="
            + f"{len(operations)}u;"
        )
    layout = binding["layout"]
    return _COLLECTOR.substitute(
        header_bytes=RUNTIME_ASSEMBLY_IDENTITY_HEADER.size,
        record_bytes=RUNTIME_ASSEMBLY_IDENTITY_RECORD.size,
        process_id=binding["process_id"],
        expected_count=binding["expected_count"],
        executable_sha=binding["binary"]["sha256"],
        module_sha=binding["event_module_inventory"]["sha256"],
        appdomain_class=binding["appdomain_class"],
        assembly_classes=",".join(
            f"{value}ull" for value in binding["assembly_classes"]
        ),
        assembly_class_count=len(binding["assembly_classes"]),
        assembly_name_class=binding["assembly_name_class"],
        string_class=binding["string_class"],
        string_length_offset=layout["string_length_offset"],
        string_data_offset=layout["string_data_offset"],
        version_offsets=",".join(
            f"{value}u" for value in layout["version_offsets"]
        ),
        flags_offset=layout["flags_offset"],
        hash_algorithm_offset=layout["hash_algorithm_offset"],
        version_compatibility_offset=layout[
            "version_compatibility_offset"
        ],
        key_candidate_offsets=",".join(
            f"{value}u" for value in layout["key_candidate_offsets"]
        ),
        operation_constants="\n".join(constants),
        output_path=_wide_literal(_windows_z_path(output)),
        status_path=_wide_literal(_windows_z_path(status)),
        status_schema=RUNTIME_ASSEMBLY_IDENTITY_STATUS_SCHEMA,
    )


def prepare_runtime_assembly_identities(
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
    output = output_dir / "runtime-assembly-identities.private.bin"
    status = output_dir / "runtime-assembly-identities-status.private.json"
    model = output_dir / "runtime-assembly-identities.private.json"
    plan_path = output_dir / "runtime-assembly-identities-plan.private.json"
    build = _owner_directory(output_dir / "build-runtime-assembly-identities")
    source = build / "runtime-assembly-identities.c"
    injector_source = build / "runtime-assembly-identities-injector.c"
    injector = build / "alpha-runtime-assembly-identities-injector.exe"
    for stale in (output, status, model):
        stale.unlink(missing_ok=True)
    _private_text(source, _source(binding, output, status))
    _private_text(injector_source, runtime_injector_source())
    collector = build / (
        "alpha-runtime-assembly-identities-"
        + file_identity(source)["sha256"][:12] + ".dll"
    )
    cc = _compiler(compiler)
    _build([str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(source), "-o",
            str(collector), "-lbcrypt"],
           label="runtime assembly identity collector")
    _build([str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(injector_source), "-o",
            str(injector)], label="runtime assembly identity injector")
    for artifact in (collector, injector):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_ASSEMBLY_IDENTITY_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_path": binding["binary"]["path"],
                   "executable_sha256": binding["binary"]["sha256"],
                   "process_id": binding["process_id"]},
        "inputs": {key: binding[key] for key in (
            "receipt", "runtime_materializer_model",
            "class_model", "enum_constant_model", "enum_constant_inventory",
            "event_module_inventory",
        )},
        "contract": {"assembly_count": binding["expected_count"],
                     "module_names": binding["module_names"],
                     "layout_owner_only": binding["layout"],
                     "derivation_evidence": binding["evidence"]},
        "collector": file_identity(collector),
        "injector": file_identity(injector),
        "output_path": str(output), "status_path": str(status),
        "model_path": str(model),
        "policy": {
            "all_loaded_assemblies_included": True,
            "assembly_name_properties_runtime_observed": True,
            "two_independent_observations_required": True,
            "module_mapping_by_exact_unique_simple_name": True,
            "operations_current_structure_and_behavior_derived": True,
            "assembly_name_field_topology_current_runtime_derived": True,
            "legacy_runtime_dispatch_used": False,
            "fixed_address_used": False, "fixed_offset_used": False,
            "external_runtime_component_used": False, "owner_only": True,
        },
    }
    _private_json(plan_path, plan)
    return {"schema": RUNTIME_ASSEMBLY_IDENTITY_PLAN_SCHEMA,
            "status": "prepared", "target": binding["target"],
            "counts": {"assembly_count": binding["expected_count"]},
            "policy": plan["policy"]}


def _slice(raw: bytes, start: int, bytes_: int, end: int) -> bytes | None:
    if not bytes_:
        return b""
    if start < end or start + bytes_ < start or start + bytes_ > len(raw):
        return None
    return raw[start:start + bytes_]


def _validate(plan: dict[str, Any], status: dict[str, Any]) -> dict[str, Any]:
    path = _owner_file(Path(plan["output_path"]), label="inventory")
    raw = path.read_bytes()
    if len(raw) < RUNTIME_ASSEMBLY_IDENTITY_HEADER.size:
        raise AcquisitionError("runtime assembly identity output is truncated")
    header = RUNTIME_ASSEMBLY_IDENTITY_HEADER.unpack_from(raw)
    count = plan["contract"]["assembly_count"]
    end = RUNTIME_ASSEMBLY_IDENTITY_HEADER.size + count * RUNTIME_ASSEMBLY_IDENTITY_RECORD.size
    header_ok = (
        header[0] == RUNTIME_ASSEMBLY_IDENTITY_MAGIC
        and header[1] == RUNTIME_ASSEMBLY_IDENTITY_VERSION
        and header[2] == RUNTIME_ASSEMBLY_IDENTITY_HEADER.size
        and header[3] == RUNTIME_ASSEMBLY_IDENTITY_RECORD.size
        and header[4] == 0 and header[5] == count
        and header[7] == plan["target"]["process_id"]
        and header[8].decode("ascii") == plan["target"]["executable_sha256"]
        and header[9].decode("ascii")
        == plan["inputs"]["event_module_inventory"]["sha256"]
        and end + header[6] == len(raw)
    )
    assemblies: list[dict[str, Any]] = []
    records_ok = header_ok
    payload_ranges: list[tuple[int, int]] = []
    simple_names: set[str] = set()
    module_names = set(plan["contract"]["module_names"])
    version_permutations = set(permutations(range(4)))
    key_roles_ok = True
    for index in range(count if header_ok else 0):
        row = RUNTIME_ASSEMBLY_IDENTITY_RECORD.unpack_from(
            raw, RUNTIME_ASSEMBLY_IDENTITY_HEADER.size
            + index * RUNTIME_ASSEMBLY_IDENTITY_RECORD.size,
        )
        (name_bytes, culture_bytes, full_bytes, flags, hash_algorithm,
         compatibility, reserved0, reserved1, major, minor, build, revision,
         token_bytes, key_bytes, reserved2, reserved3, name_offset,
         culture_offset, full_offset, token_offset, key_offset) = row
        chunks = [
            _slice(raw, name_offset, name_bytes, end),
            _slice(raw, culture_offset, culture_bytes, end),
            _slice(raw, full_offset, full_bytes, end),
            _slice(raw, token_offset, token_bytes, end),
            _slice(raw, key_offset, key_bytes, end),
        ]
        if any(chunk is None for chunk in chunks):
            records_ok = False
            break
        assert all(chunk is not None for chunk in chunks)
        try:
            name, captured_culture, full_name = (
                chunks[0].decode("utf-8"), chunks[1].decode("utf-8"),
                chunks[2].decode("utf-8"),
            )
        except UnicodeDecodeError:
            records_ok = False
            break
        for offset, size in ((name_offset, name_bytes),
                             (culture_offset, culture_bytes),
                             (full_offset, full_bytes),
                             (token_offset, token_bytes),
                             (key_offset, key_bytes)):
            if size:
                payload_ranges.append((offset, offset + size))
        module_matches = [
            module for module in module_names
            if module.rsplit(".", 1)[0] == name
        ]
        identity_parts = [part.strip() for part in full_name.split(",")]
        identity_values: dict[str, str] = {}
        for part in identity_parts[1:]:
            if "=" not in part:
                records_ok = False
                break
            key_name, value = part.split("=", 1)
            if not key_name or key_name in identity_values:
                records_ok = False
                break
            identity_values[key_name] = value
        if not records_ok:
            break
        version_text = identity_values.get("Version", "")
        culture_text = identity_values.get("Culture", "")
        token_text = identity_values.get("PublicKeyToken", "").casefold()
        try:
            semantic_version = tuple(int(value) for value in version_text.split("."))
        except ValueError:
            semantic_version = ()
        if len(semantic_version) != 4:
            records_ok = False
            break
        physical_version = (major, minor, build, revision)
        version_permutations = {
            permutation
            for permutation in version_permutations
            if tuple(physical_version[position] for position in permutation)
            == semantic_version
        }
        culture = "" if culture_text.casefold() == "neutral" else culture_text
        key_candidates = (chunks[3], chunks[4])
        if token_text == "null":
            empty = [
                candidate_index
                for candidate_index, value in enumerate(key_candidates)
                if not value
            ]
            if not empty:
                key_roles_ok = False
                records_ok = False
                break
            if len(empty) == 2:
                token = key = b""
            else:
                token_index = empty[0]
                token = key_candidates[token_index]
                key = key_candidates[1 - token_index]
        else:
            token_matches = [
                candidate_index
                for candidate_index, value in enumerate(key_candidates)
                if value.hex() == token_text
            ]
            if len(token_matches) != 1:
                key_roles_ok = False
                records_ok = False
                break
            token_index = token_matches[0]
            token = key_candidates[token_index]
            key = key_candidates[1 - token_index]
        if (
            not name or not full_name or name in simple_names
            or len(module_matches) != 1
            or identity_parts[0] != name
            or not culture_text or not token_text
            or captured_culture not in ("", culture, culture_text)
            or len(token) not in (0, 8)
            or reserved0 or reserved1 or reserved2 or reserved3
            or semantic_version[0] < 0 or semantic_version[1] < 0
            or semantic_version[2] < -1 or semantic_version[3] < -1
            or (token and token.hex() != token_text)
        ):
            records_ok = False
            break
        simple_names.add(name)
        assemblies.append({
            "assembly_index": index, "module_name": module_matches[0],
            "name": name, "culture": culture, "full_name": full_name,
            "flags": flags, "hash_algorithm": hash_algorithm,
            "version_compatibility": compatibility,
            "version": list(semantic_version),
            "public_key_token": token.hex(), "public_key": key.hex(),
        })
    version_order_ok = records_ok and len(version_permutations) == 1
    payload_ranges.sort()
    payload_ok = (
        records_ok
        and (not payload_ranges or payload_ranges[0][0] == end)
        and all(left[1] == right[0]
                for left, right in zip(payload_ranges, payload_ranges[1:]))
        and (not payload_ranges or payload_ranges[-1][1] == len(raw))
    )
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_ASSEMBLY_IDENTITY_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete"
        and status.get("output_written") is True,
        "header_bound": header_ok, "records_valid": records_ok,
        "payload_fully_accounted": payload_ok,
        "all_assemblies_captured": status.get("completed_count") == count,
        "two_observations_match": status.get("two_observations_match")
        is True,
        "all_modules_mapped": len(assemblies) == len(module_names) == count,
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
        is True,
        "current_runtime_operations_derived": (
            status.get("all_identity_operations_current_runtime_derived")
            is True
            and status.get("operation_candidate_sets_structurally_closed")
            is True
            and status.get("field_layout_current_runtime_derived") is True
            and status.get("legacy_runtime_dispatch_used") is False
        ),
        "operation_candidates_structurally_unique_or_equivalent": (
            plan["contract"].get("derivation_evidence", {}).get(
                "current_domain_candidate_count", 0
            ) >= 2
            and plan["contract"]["derivation_evidence"].get(
                "assembly_array_candidate_count"
            ) == 1
            and plan["contract"]["derivation_evidence"].get(
                "assembly_name_candidate_count"
            ) == 1
            and plan["contract"]["derivation_evidence"].get(
                "simple_name_candidate_count"
            ) == 1
            and plan["contract"]["derivation_evidence"].get(
                "full_name_candidate_count", 0
            ) >= 1
            and plan["contract"]["derivation_evidence"].get(
                "hash_field_candidate_count"
            ) == 1
            and plan["contract"]["derivation_evidence"].get(
                "field_layout_candidate_count"
            ) == 1
        ),
        "version_component_order_behaviorally_unique": version_order_ok,
        "key_and_token_roles_full_name_validated": key_roles_ok,
        "saved_identity_absent": status.get("saved_assembly_identity_used")
        is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime assembly identity validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    return {"schema": RUNTIME_ASSEMBLY_IDENTITY_SCHEMA,
            "status": "runtime-validated", "target": {
                "executable_sha256": plan["target"]["executable_sha256"]},
            "inputs": plan["inputs"], "inventory": file_identity(path),
            "status_receipt": file_identity(Path(plan["status_path"])),
            "counts": {"assembly_count": count,
                       "payload_bytes": header[6]},
            "assemblies": assemblies, "checks": checks,
            "policy": plan["policy"]}


def capture_runtime_assembly_identities(
    *, native_output_receipt: Path, runtime_materializer_model: Path,
    runtime_inventory_dispatch: Path | None, output_dir: Path, wine: Path,
    wineprefix: Path, compiler: Path | None = None, timeout: float = 300.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_assembly_identities(
        native_output_receipt=native_output_receipt,
        runtime_materializer_model=runtime_materializer_model,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
        output_dir=output_dir, compiler=compiler,
    )
    plan = read_json(output_dir / "runtime-assembly-identities-plan.private.json")
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine.expanduser().resolve()), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name),
            env=environment, check=False, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="replace", timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "runtime assembly identity injector could not run"
        ) from error
    _private_text(output_dir / "runtime-assembly-identities-injector.private.log",
                  json.dumps({"returncode": injected.returncode,
                              "stdout": injected.stdout,
                              "stderr": injected.stderr},
                             ensure_ascii=False, indent=2) + "\n")
    if injected.returncode:
        raise AcquisitionError("runtime assembly identity injection failed")
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
        raise AcquisitionError("runtime assembly identity capture timed out")
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime assembly identity capture failed "
            f"(kind={status.get('failure_kind_owner_only')})"
        )
    _seal_runtime_output(Path(plan["output_path"]))
    model = _validate(plan, status)
    model_path = Path(plan["model_path"])
    _private_json(model_path,
                  {key: value for key, value in model.items()
                   if key != "assemblies"})
    return {"schema": model["schema"], "status": model["status"],
            "target": model["target"], "counts": model["counts"],
            "checks": model["checks"], "policy": model["policy"],
            "model": file_identity(model_path),
            "inventory": model["inventory"]}


def load_runtime_assembly_identities(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    plan_path = _owner_file(
        model_path.parent / "runtime-assembly-identities-plan.private.json",
        label="plan")
    status_path = _owner_file(
        model_path.parent / "runtime-assembly-identities-status.private.json",
        label="status")
    model, plan, status = read_json(model_path), read_json(plan_path), read_json(status_path)
    if (model.get("schema") != RUNTIME_ASSEMBLY_IDENTITY_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("inventory") != file_identity(inventory_path)
        or model.get("status_receipt") != file_identity(status_path)
        or plan.get("schema") != RUNTIME_ASSEMBLY_IDENTITY_PLAN_SCHEMA
        or Path(plan.get("output_path", "")).expanduser().resolve() != inventory_path
        or Path(plan.get("model_path", "")).expanduser().resolve() != model_path
        or (expected_executable_sha256 is not None
            and model.get("target", {}).get("executable_sha256")
            != expected_executable_sha256.lower())):
        raise AcquisitionError("runtime assembly identity binding is stale")
    current = _validate(plan, status)
    if (current["counts"] != model.get("counts")
        or current["checks"] != model.get("checks")
        or current["policy"] != model.get("policy")):
        raise AcquisitionError("runtime assembly identity validation is stale")
    return current
