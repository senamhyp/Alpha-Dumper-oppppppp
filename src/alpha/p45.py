from alpha.h02 import windows_run as _host_run

import json
import os
import secrets
import stat
import struct
import subprocess
import time
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.c06 import LiveRuntimeInventory, rebind_method
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER
from alpha.p29 import _runtime
from alpha.p38 import _binding as _proto_inventory_binding
from alpha.p42 import RUNTIME_PROTO_ENUM_CONSTANT_SCHEMA, _field_rows, build_runtime_proto_static_model
from alpha.h02 import file_identity, read_json


RUNTIME_PROTO_ENUM_PLAN_SCHEMA = "alpha.runtime-proto-enum-plan/v5"
RUNTIME_PROTO_ENUM_STATUS_SCHEMA = "alpha.runtime-proto-enum-status/v5"
RUNTIME_PROTO_ENUM_MAGIC = b"ALPHAEN4"
RUNTIME_PROTO_ENUM_VERSION = 4
RUNTIME_PROTO_ENUM_HEADER = struct.Struct("<8sIIIIQQ64s")
RUNTIME_PROTO_ENUM_RECORD = struct.Struct("<IIQIIII")

ENUM_VALUE_KINDS = {
    "System.SByte": 1,
    "System.Byte": 2,
    "System.Int16": 3,
    "System.UInt16": 4,
    "System.Int32": 5,
    "System.UInt32": 6,
    "System.Int64": 7,
    "System.UInt64": 8,
}
SIGNED_ENUM_VALUE_KINDS = {1, 3, 5, 7}


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime proto enum {label} is not owner-only")
    return path


def _operation(semantics: dict[str, Any], key: str) -> dict[str, Any]:
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
        raise AcquisitionError(f"runtime proto enum operation is unavailable: {key}")
    return {
        "pointer": int(rows[0]["method_pointer"]),
        "metadata": int(rows[0]["metadata_pointer"]),
        "runtime_owner": rows[0].get("runtime_owner"),
    }


def _enum_fields(runtime, fields, by_owner):

    selected: dict[int, tuple[int, str]] = {}
    for owner in range(runtime.type_count):
        if not runtime.renderer.identity_row(owner)[1] & 0x20:
            continue
        rows = [fields[index] for index in by_owner.get(owner, [])]


        underlying = [row for row in rows if not row["attributes"] & (0x10 | 0x40)]
        if len(underlying) != 1:
            raise AcquisitionError("runtime enum underlying field domain is ambiguous")
        underlying_type = runtime.renderer.render(underlying[0]["descriptor"])
        value_kind = ENUM_VALUE_KINDS.get(underlying_type)
        if value_kind is None:
            raise AcquisitionError(
                f"runtime enum underlying type is unsupported: {underlying_type}"
            )
        for row in rows:
            if row["name"] != "value__" and row["attributes"] & 0x40:
                selected[row["field_index"]] = (value_kind, underlying_type)
    return selected


def _binding(
    *,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    runtime_materializer_model: Path,
) -> dict[str, Any]:
    receipt, paths, runtime = _runtime(native_output_receipt)
    inventory = _proto_inventory_binding(native_output_receipt)
    semantics_path = _owner_file(
        Path(inventory["reflection_semantics"]["path"]),
        label="reflection semantics",
    )
    if file_identity(semantics_path) != inventory["reflection_semantics"]:
        raise AcquisitionError("runtime proto enum reflection semantics are stale")
    semantics = read_json(semantics_path)
    raw_constant = _operation(semantics, "field.raw_constant")
    type_from_handle = _operation(semantics, "type.from_handle")
    model = build_runtime_proto_static_model(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
    )
    field_by_index, fields_by_owner = _field_rows(runtime)
    required: set[int] = set()
    oneof_enum_names: set[str] = set()
    for row in model["unresolved_owner_only"]:
        if row.get("kind") == "enum-value":
            required.add(int(row["field_index_owner_only"]))
        elif row.get("kind") == "oneof-case-numbers":
            oneof_enum_names.add(str(row["enum"]))
    enum_index_by_name = {
        runtime.renderer.root_name(index): index
        for index in range(runtime.type_count)
        if runtime.renderer.identity_row(index)[1] & 0x20
    }
    for name in oneof_enum_names:
        type_index = enum_index_by_name.get(name)
        if type_index is None:
            raise AcquisitionError("runtime proto oneof enum identity differs")
        for field_index in fields_by_owner.get(type_index, []):
            field = field_by_index[field_index]
            if field["name"] != "value__" and field["attributes"] & 0x40:
                required.add(field_index)


    complete_domain = _enum_fields(runtime, field_by_index, fields_by_owner)
    if not required <= set(complete_domain):
        raise AcquisitionError(
            "required proto enum is outside the validated integral literal domain"
        )
    required = set(complete_domain)
    live = LiveRuntimeInventory(
        materializer_model=runtime_materializer_model,
        binary=paths["binary"],
    )
    try:
        field_class_indexes = [
            index
            for index in range(runtime.type_count)
            if runtime.renderer.identity_row(index)[3] == inventory["field_class"]
        ]
        if len(field_class_indexes) != 1:
            raise AcquisitionError("runtime proto enum FieldInfo class is ambiguous")
        field_class = live.type_row(field_class_indexes[0]).class_pointer
        custom_attribute_candidates = []
        for method_index in range(runtime.method_count):
            method = runtime.method_row(method_index)
            if (
                int(method[0]) == field_class_indexes[0]
                and not method[5] & 0x10
                and method[3]
                and runtime.method_return(method_index) == "System.Object[]"
                and [row[1] for row in runtime.method_parameters(method_index)]
                == ["System.Boolean"]
            ):
                custom_attribute_candidates.append(
                    {
                        "pointer": int(method[3]),
                        "metadata": int(method[2]),
                    }
                )
        if len(custom_attribute_candidates) != 1:
            raise AcquisitionError(
                "runtime proto enum custom attribute operation is ambiguous"
            )
        runtime_type_indexes = [
            index
            for index in range(runtime.type_count)
            if runtime.renderer.root_name(index) == "System.RuntimeType"
        ]
        if len(runtime_type_indexes) != 1:
            raise AcquisitionError(
                "runtime proto enum concrete Type class is ambiguous"
            )
        type_custom_attribute_candidates = []
        for method_index in range(runtime.method_count):
            method = runtime.method_row(method_index)
            if (
                int(method[0]) == runtime_type_indexes[0]
                and not method[5] & 0x10
                and method[3]
                and runtime.method_return(method_index) == "System.Object[]"
                and [row[1] for row in runtime.method_parameters(method_index)]
                == ["System.Boolean"]
            ):
                type_custom_attribute_candidates.append(
                    {
                        "pointer": int(method[3]),
                        "metadata": int(method[2]),
                    }
                )
        if len(type_custom_attribute_candidates) != 1:
            raise AcquisitionError(
                "runtime proto enum Type custom attribute operation is ambiguous"
            )
        field_from_handle = rebind_method(
            runtime, live, inventory["field_from_handle"]
        )
        current_raw_constant = rebind_method(runtime, live, raw_constant)
        current_custom_attributes = rebind_method(
            runtime, live, custom_attribute_candidates[0]
        )
        current_type_from_handle = rebind_method(runtime, live, type_from_handle)
        current_type_custom_attributes = rebind_method(
            runtime, live, type_custom_attribute_candidates[0]
        )
        if (
            len(
                {
                    field_from_handle["image_delta"],
                    current_raw_constant["image_delta"],
                    current_custom_attributes["image_delta"],
                    current_type_from_handle["image_delta"],
                    current_type_custom_attributes["image_delta"],
                }
            )
            != 1
        ):
            raise AcquisitionError("runtime proto enum image rebasing differs")
        class_rows = sorted(
            (
                live.type_row(index).class_pointer,
                index,
            )
            for index in range(runtime.type_count)
        )
        if (
            any(not pointer for pointer, _index in class_rows)
            or len({pointer for pointer, _index in class_rows})
            != len(class_rows)
        ):
            raise AcquisitionError(
                "runtime proto enum class pointer domain is ambiguous"
            )
        graph_status_path = (
            paths["type_graph_inventory"].parent
            / "runtime-type-graph-status.private.json"
        )
        graph_status = read_json(_owner_file(graph_status_path, label="type graph status"))
        array_length_qword = graph_status.get("array_length_qword_owner_only")
        array_vector_qword = graph_status.get("array_vector_qword_owner_only")
        if (
            not isinstance(array_length_qword, int)
            or not isinstance(array_vector_qword, int)
            or not 2 <= array_length_qword < array_vector_qword
            or array_vector_qword > ((1 << 32) - 1) // 8
        ):
            raise AcquisitionError(
                "runtime proto enum managed array layout is unavailable"
            )
        rows: list[dict[str, int]] = []
        for field_index in sorted(required):
            field = field_by_index.get(field_index)
            if (
                field is None
                or not field["metadata"]
                or not field["attributes"] & 0x40
            ):
                raise AcquisitionError("runtime proto enum literal field differs")
            owner = int(field["owner_type_index"])
            if not runtime.renderer.identity_row(owner)[1] & 0x20:
                raise AcquisitionError("runtime proto enum literal owner differs")
            current_field = live.field_row(field_index, expected_owner=owner)
            current_owner = live.type_row(owner)
            rows.append(
                {
                    "field_index": field_index,
                    "value_kind": complete_domain[field_index][0],
                    "underlying_type": complete_domain[field_index][1],
                    "metadata": current_field.pointer,
                    "owner_descriptor": current_owner.embedded_descriptor(
                        live.embedded_descriptor_byte_offset
                    ),
                }
            )
        if not rows or {row["field_index"] for row in rows} != set(complete_domain):
            raise AcquisitionError("runtime proto enum literal domain is incomplete")
        return {
            "receipt": file_identity(native_output_receipt.expanduser().resolve()),
            "proto_field_type_model": file_identity(
                proto_field_type_model.expanduser().resolve()
            ),
            "runtime_materializer_model": file_identity(
                runtime_materializer_model.expanduser().resolve()
            ),
            "target": receipt["target"],
            "binary": inventory["binary"],
            "process_id": live.process_id,
            "field_class": field_class,
            "field_from_handle": field_from_handle,
            "field_raw_constant": current_raw_constant,
            "field_custom_attributes": current_custom_attributes,
            "type_from_handle": current_type_from_handle,
            "type_custom_attributes": current_type_custom_attributes,
            "class_rows": class_rows,
            "array_length_qword": array_length_qword,
            "array_vector_qword": array_vector_qword,
            "type_graph_status": file_identity(graph_status_path),
            "reflection_semantics": inventory["reflection_semantics"],
            "rows": rows,
            "static_counts": model["counts"],
        }
    finally:
        live.close()


_COLLECTOR = Template(
    r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
typedef struct input_record { uint32_t field_index,value_kind; uintptr_t metadata,owner; } input_record;
typedef struct output_header { char magic[8]; uint32_t version,header_bytes,record_bytes,count; uint64_t process_id,attribute_count; char executable[64]; } output_header;
typedef struct output_record { uint32_t field_index,attribute_complete; uint64_t value_bits; uint32_t value_kind,attribute_start,attribute_count,reserved; } output_record;
typedef struct class_record { uintptr_t class_pointer; uint32_t type_index,reserved; } class_record;
_Static_assert(sizeof(output_header)==$header_bytes,"enum header");
_Static_assert(sizeof(output_record)==$record_bytes,"enum record");
static const DWORD expected_pid=$process_id;
static const char executable_sha[]="$executable_sha";
static const uintptr_t field_class=$field_class;
static const uintptr_t field_from_handle_pointer=$field_from_handle_pointer;
static const uintptr_t field_from_handle_metadata=$field_from_handle_metadata;
static const uintptr_t field_raw_constant_pointer=$field_raw_constant_pointer;
static const uintptr_t field_raw_constant_metadata=$field_raw_constant_metadata;
static const uintptr_t field_custom_attributes_pointer=$field_custom_attributes_pointer;
static const uintptr_t field_custom_attributes_metadata=$field_custom_attributes_metadata;
static const uintptr_t type_from_handle_pointer=$type_from_handle_pointer;
static const uintptr_t type_from_handle_metadata=$type_from_handle_metadata;
static const uintptr_t type_custom_attributes_pointer=$type_custom_attributes_pointer;
static const uintptr_t type_custom_attributes_metadata=$type_custom_attributes_metadata;
static const uint32_t array_length_qword=$array_length_qword;
static const uint32_t array_vector_qword=$array_vector_qword;
static const input_record inputs[]={$input_rows};
static const class_record classes[]={$class_rows};
static const wchar_t output_path[]=$output_path;
static const wchar_t status_path[]=$status_path;
typedef uintptr_t(*static_twoarg)(uintptr_t,uintptr_t,uintptr_t);
typedef uintptr_t(*instance_noarg)(uintptr_t,uintptr_t);
typedef uintptr_t(*instance_boolarg)(uintptr_t,uint32_t,uintptr_t);
static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_complete;
static volatile LONG probe_stage;static uint32_t failure_kind,completed_count,attribute_failure_count,attribute_retry_count;
static output_record *records;static uint32_t *attributes;static uint64_t attribute_count,attribute_capacity;
static int readable(uintptr_t value,SIZE_T bytes){MEMORY_BASIC_INFORMATION r;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t end=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}
static int object_class(uintptr_t object,uintptr_t expected){uintptr_t observed=0;if(!readable(object,sizeof(observed)))return 0;memcpy(&observed,(const void*)object,sizeof(observed));return observed==expected;}
static int class_type_index(uintptr_t klass,uint32_t*out){uint32_t low=0,high=$class_count;while(low<high){uint32_t middle=low+(high-low)/2u;if(classes[middle].class_pointer<klass)low=middle+1u;else high=middle;}if(low>=$class_count||classes[low].class_pointer!=klass)return 0;*out=classes[low].type_index;return 1;}
static int append_attribute(uint32_t start,uint32_t type_index){for(uint64_t i=start;i<attribute_count;i++)if(attributes[i]==type_index)return 1;if(attribute_count==attribute_capacity){uint64_t capacity=attribute_capacity?attribute_capacity*2u:4096u;if(capacity>UINT32_MAX)return 0;uint32_t*grown=(uint32_t*)realloc(attributes,(SIZE_T)capacity*sizeof(uint32_t));if(!grown)return 0;attributes=grown;attribute_capacity=capacity;}attributes[attribute_count++]=type_index;return 1;}
static int capture_attribute_array(uintptr_t member,uintptr_t pointer,uintptr_t metadata,uint32_t start){instance_boolarg get_attributes=(instance_boolarg)pointer;uintptr_t array=get_attributes(member,0u,metadata);if(!array||!readable(array,((SIZE_T)array_vector_qword+1u)*8u))return 0;uint64_t count=0;memcpy(&count,(const void*)(array+(uintptr_t)array_length_qword*8u),8u);if(count>SIZE_MAX/8u||count>UINT32_MAX||attribute_count>UINT32_MAX-count)return 0;uintptr_t vector=array+(uintptr_t)array_vector_qword*8u;if(count&&!readable(vector,(SIZE_T)count*8u))return 0;for(uint64_t i=0;i<count;i++){uintptr_t object=0,klass=0;uint32_t type_index=0;memcpy(&object,(const void*)(vector+i*8u),8u);if(!readable(object,8u))return 0;memcpy(&klass,(const void*)object,8u);if(!class_type_index(klass,&type_index)||!append_attribute(start,type_index))return 0;}return 1;}
static int capture_attributes_once(uintptr_t field,uintptr_t owner,output_record*record){static_twoarg get_type=(static_twoarg)type_from_handle_pointer;uint32_t start=(uint32_t)attribute_count;record->attribute_start=start;record->attribute_count=0;if(!capture_attribute_array(field,field_custom_attributes_pointer,field_custom_attributes_metadata,start)){attribute_count=start;return 0;}uintptr_t type=get_type(owner,0u,type_from_handle_metadata);if(!type||!capture_attribute_array(type,type_custom_attributes_pointer,type_custom_attributes_metadata,start)){attribute_count=start;return 0;}record->attribute_count=(uint32_t)attribute_count-start;return 1;}
static int capture_attributes(uintptr_t field,uintptr_t owner,output_record*record){for(uint32_t attempt=0;attempt<4u;attempt++){if(capture_attributes_once(field,owner,record))return 1;attribute_retry_count++;SwitchToThread();}return 0;}
static int read_constant(uintptr_t boxed,uint32_t kind,uint64_t*out){uintptr_t payload=boxed+16u;if(!boxed||!out)return 0;switch(kind){case 1:{int8_t v;if(!readable(payload,sizeof(v)))return 0;memcpy(&v,(const void*)payload,sizeof(v));*out=(uint64_t)(int64_t)v;return 1;}case 2:{uint8_t v;if(!readable(payload,sizeof(v)))return 0;memcpy(&v,(const void*)payload,sizeof(v));*out=v;return 1;}case 3:{int16_t v;if(!readable(payload,sizeof(v)))return 0;memcpy(&v,(const void*)payload,sizeof(v));*out=(uint64_t)(int64_t)v;return 1;}case 4:{uint16_t v;if(!readable(payload,sizeof(v)))return 0;memcpy(&v,(const void*)payload,sizeof(v));*out=v;return 1;}case 5:{int32_t v;if(!readable(payload,sizeof(v)))return 0;memcpy(&v,(const void*)payload,sizeof(v));*out=(uint64_t)(int64_t)v;return 1;}case 6:{uint32_t v;if(!readable(payload,sizeof(v)))return 0;memcpy(&v,(const void*)payload,sizeof(v));*out=v;return 1;}case 7:{int64_t v;if(!readable(payload,sizeof(v)))return 0;memcpy(&v,(const void*)payload,sizeof(v));*out=(uint64_t)v;return 1;}case 8:{uint64_t v;if(!readable(payload,sizeof(v)))return 0;memcpy(&v,(const void*)payload,sizeof(v));*out=v;return 1;}default:return 0;}}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE f=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL,*buffer=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,os);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(a,&h,object,os,NULL,0,0)<0)ok=0;while(ok){DWORD n=0;if(!ReadFile(f,buffer,1048576u,&n,NULL)){ok=0;break;}if(!n)break;if(BCryptHashData(h,buffer,n,0)<0)ok=0;}if(ok&&BCryptFinishHash(h,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,output);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(f);return ok;}
static int executable_identity(char output[65]){wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,(DWORD)(sizeof(p)/sizeof(p[0])));return n&&n<sizeof(p)/sizeof(p[0])&&sha256_file(p,output);}
static int collect_batch(void){static_twoarg from_handle=(static_twoarg)field_from_handle_pointer;instance_noarg raw_constant=(instance_noarg)field_raw_constant_pointer;if(!records){records=(output_record*)calloc($row_count,sizeof(output_record));if(!records)return failure_kind=1,0;}uint32_t end=completed_count+512u;if(end<completed_count)return failure_kind=1,0;if(end>$row_count)end=$row_count;for(uint32_t i=completed_count;i<end;i++){InterlockedExchange(&probe_stage,(LONG)(1000u+i));uintptr_t field=from_handle(inputs[i].metadata,inputs[i].owner,field_from_handle_metadata);if(!object_class(field,field_class))return failure_kind=2,0;uintptr_t boxed=raw_constant(field,field_raw_constant_metadata);records[i].field_index=inputs[i].field_index;records[i].value_kind=inputs[i].value_kind;if(!read_constant(boxed,inputs[i].value_kind,&records[i].value_bits))return failure_kind=3,0;if(capture_attributes(field,inputs[i].owner,&records[i]))records[i].attribute_complete=1u;else{records[i].attribute_complete=0u;attribute_failure_count++;}completed_count=i+1u;}if(completed_count==$row_count)InterlockedExchange(&probe_stage,2);return 1;}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);int ok=collect_batch();InterlockedExchange(&callback_complete,ok?1:-1);return ok;}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;
static BOOL CALLBACK select_window(HWND w,LPARAM v){selection*s=(selection*)(uintptr_t)v;DWORD pid=0;RECT b;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){s->window=w;s->count++;}return TRUE;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window)return failure_kind=4,0;message_id=RegisterWindowMessageW(status_path);SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);int ok=message_id&&(original_proc||GetLastError()==ERROR_SUCCESS);while(ok&&completed_count<$row_count){DWORD_PTR result=0;InterlockedExchange(&callback_complete,0);ok=SendMessageTimeoutW(s.window,message_id,0,0,SMTO_BLOCK,60000,&result)&&InterlockedCompareExchange(&callback_complete,0,0)==1;}if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);if(!ok&&!failure_kind)failure_kind=5;return ok;}
static int write_output(void){output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"ALPHAEN4",8);h.version=4;h.header_bytes=sizeof(h);h.record_bytes=sizeof(output_record);h.count=$row_count;h.process_id=GetCurrentProcessId();h.attribute_count=attribute_count;memcpy(h.executable,executable_sha,64);FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;int ok=fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(records,sizeof(output_record),$row_count,f)==$row_count&&fwrite(attributes,sizeof(uint32_t),(size_t)attribute_count,f)==attribute_count;if(fclose(f))ok=0;if(!ok)_wremove(output_path);else _wchmod(output_path,0600);return ok;}
static void write_status(const char*status,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"expected_count\": %u,\n  \"completed_count\": %u,\n  \"attribute_failure_count\": %u,\n  \"attribute_retry_count\": %u,\n  \"failure_kind_owner_only\": %u,\n  \"probe_stage_owner_only\": %ld,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"saved_reference_generation_seed_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned)$row_count,completed_count,attribute_failure_count,attribute_retry_count,failure_kind,InterlockedCompareExchange(&probe_stage,0,0),written?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char digest[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(digest)||strcmp(digest,executable_sha)){failure_kind=100;write_status("identity_mismatch",0);return 0;}int ok=dispatch();if(!ok){write_status("capture_failed",0);return 0;}ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
'''
)


def _source(binding: dict[str, Any], output: Path, status: Path) -> str:
    rows = ",".join(
        "{%du,%du,%dull,%dull}"
        % (
            row["field_index"],
            row["value_kind"],
            row["metadata"],
            row["owner_descriptor"],
        )
        for row in binding["rows"]
    )
    class_rows = ",".join(
        "{%dull,%du,0u}" % (pointer, index)
        for pointer, index in binding["class_rows"]
    )
    return _COLLECTOR.substitute(
        header_bytes=RUNTIME_PROTO_ENUM_HEADER.size,
        record_bytes=RUNTIME_PROTO_ENUM_RECORD.size,
        process_id=binding["process_id"],
        executable_sha=binding["binary"]["sha256"],
        field_class=binding["field_class"],
        field_from_handle_pointer=binding["field_from_handle"]["pointer"],
        field_from_handle_metadata=binding["field_from_handle"]["metadata"],
        field_raw_constant_pointer=binding["field_raw_constant"]["pointer"],
        field_raw_constant_metadata=binding["field_raw_constant"]["metadata"],
        field_custom_attributes_pointer=binding["field_custom_attributes"]["pointer"],
        field_custom_attributes_metadata=binding["field_custom_attributes"]["metadata"],
        type_from_handle_pointer=binding["type_from_handle"]["pointer"],
        type_from_handle_metadata=binding["type_from_handle"]["metadata"],
        type_custom_attributes_pointer=binding["type_custom_attributes"]["pointer"],
        type_custom_attributes_metadata=binding["type_custom_attributes"]["metadata"],
        array_length_qword=binding["array_length_qword"],
        array_vector_qword=binding["array_vector_qword"],
        input_rows=rows,
        class_rows=class_rows,
        class_count=len(binding["class_rows"]),
        row_count=len(binding["rows"]),
        output_path=_wide_literal(_windows_z_path(output)),
        status_path=_wide_literal(_windows_z_path(status)),
        status_schema=RUNTIME_PROTO_ENUM_STATUS_SCHEMA,
    )


def prepare_runtime_proto_enum_constants(
    *,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    runtime_materializer_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        runtime_materializer_model=runtime_materializer_model,
    )
    output = output_dir / "runtime-proto-enum-constants.private.bin"
    status = output_dir / "runtime-proto-enum-status.private.json"
    plan_path = output_dir / "runtime-proto-enum-plan.private.json"
    build = _owner_directory(output_dir / "build-runtime-proto-enum")
    source = build / "runtime-proto-enum.c"
    injector_source = build / "runtime-proto-enum-injector.c"
    for stale in (output, status):
        stale.unlink(missing_ok=True)
    _private_text(source, _source(binding, output, status))
    _private_text(injector_source, runtime_injector_source())


    load_identity = secrets.token_hex(8)
    collector = build / (
        "alpha-runtime-proto-enum-"
        + file_identity(source)["sha256"][:12]
        + "-" + load_identity
        + ".dll"
    )
    injector = build / "alpha-runtime-proto-enum-injector.exe"
    cc = _compiler(compiler)
    _build(
        [
            str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(source), "-o",
            str(collector), "-lbcrypt",
        ],
        label="runtime proto enum collector",
    )
    _build(
        [
            str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(injector_source), "-o",
            str(injector),
        ],
        label="runtime proto enum injector",
    )
    for artifact in (collector, injector):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_PROTO_ENUM_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": binding["binary"]["path"],
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
        },
        "inputs": {
            "native_output_receipt": binding["receipt"],
            "proto_field_type_model": binding["proto_field_type_model"],
            "runtime_materializer_model": binding[
                "runtime_materializer_model"
            ],
            "reflection_semantics": binding["reflection_semantics"],
            "type_graph_status": binding["type_graph_status"],
        },
        "contract": {
            "constant_count": len(binding["rows"]),
            "field_indexes_owner_only": [row["field_index"] for row in binding["rows"]],
            "value_kinds_owner_only": [row["value_kind"] for row in binding["rows"]],
            "underlying_types_owner_only": [
                row["underlying_type"] for row in binding["rows"]
            ],
        },
        "collector": {**file_identity(collector), "load_identity": load_identity},
        "injector": file_identity(injector),
        "output_path": str(output),
        "status_path": str(status),
        "policy": {
            "all_current_integral_enum_literals_planned": True,
            "all_clr_enum_underlying_types_supported": True,
            "preliminary_unresolved_list_is_not_collection_domain": True,
            "field_info_get_raw_constant_value_used": True,
            "field_info_custom_attributes_captured": True,
            "enum_type_custom_attributes_captured": True,
            "attribute_capture_failure_is_recorded_per_literal": True,
            "transient_attribute_capture_is_retried_per_literal": True,
            "incomplete_attribute_evidence_cannot_promote_enum": True,
            "custom_attribute_types_resolved_from_current_runtime_classes": True,
            "current_runtime_handles_used": True,
            "all_runtime_addresses_rebound_from_current_process_inventory": True,
            "saved_runtime_pointer_used": False,
            "saved_reference_generation_seed_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
            "raw_pointers_owner_only": True,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_PROTO_ENUM_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "counts": {"constant_count": len(binding["rows"])},
        "policy": plan["policy"],
    }


def _decode_enum_value(value_kind: int, value_bits: int) -> int:
    if value_kind not in ENUM_VALUE_KINDS.values() or not 0 <= value_bits < 1 << 64:
        raise AcquisitionError("runtime proto enum value encoding is invalid")
    if value_kind in SIGNED_ENUM_VALUE_KINDS and value_bits & (1 << 63):
        return value_bits - (1 << 64)
    return value_bits


def _validate(plan: dict[str, Any], status: dict[str, Any]) -> dict[str, Any]:
    path = _owner_file(Path(plan["output_path"]), label="output")
    raw = path.read_bytes()
    if len(raw) < RUNTIME_PROTO_ENUM_HEADER.size:
        raise AcquisitionError("runtime proto enum output is truncated")
    header = RUNTIME_PROTO_ENUM_HEADER.unpack_from(raw)
    expected = int(plan["contract"]["constant_count"])
    indexes = plan["contract"]["field_indexes_owner_only"]
    value_kinds = plan["contract"]["value_kinds_owner_only"]
    underlying_types = plan["contract"]["underlying_types_owner_only"]
    contract_closed = (
        isinstance(indexes, list)
        and isinstance(value_kinds, list)
        and isinstance(underlying_types, list)
        and len(indexes) == len(value_kinds) == len(underlying_types) == expected
        and all(
            ENUM_VALUE_KINDS.get(name) == kind
            for name, kind in zip(underlying_types, value_kinds)
        )
    )
    checks = {
        "status_complete": status.get("status") == "complete",
        "header_bound": (
            header[0] == RUNTIME_PROTO_ENUM_MAGIC
            and header[1] == RUNTIME_PROTO_ENUM_VERSION
            and header[2] == RUNTIME_PROTO_ENUM_HEADER.size
            and header[3] == RUNTIME_PROTO_ENUM_RECORD.size
            and header[4] == expected
            and header[5] == plan["target"]["process_id"]
            and header[7].decode("ascii") == plan["target"]["executable_sha256"]
            and len(raw)
            == RUNTIME_PROTO_ENUM_HEADER.size
            + expected * RUNTIME_PROTO_ENUM_RECORD.size
            + header[6] * 4
        ),
        "all_constants_captured": status.get("completed_count") == expected,
        "integral_enum_contract_closed": contract_closed,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_reference_generation_seed_absent": status.get(
            "saved_reference_generation_seed_used"
        ) is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    constants: list[dict[str, Any]] = []
    incomplete_attribute_count = 0
    observed: set[int] = set()
    attribute_start = (
        RUNTIME_PROTO_ENUM_HEADER.size
        + expected * RUNTIME_PROTO_ENUM_RECORD.size
    )
    attribute_indexes = (
        list(struct.unpack_from(f"<{header[6]}I", raw, attribute_start))
        if checks["header_bound"] and header[6]
        else []
    )
    if checks["header_bound"] and contract_closed:
        for offset in range(expected):
            (
                field_index,
                attribute_complete,
                value_bits,
                value_kind,
                first_attribute,
                attribute_count,
                reserved,
            ) = RUNTIME_PROTO_ENUM_RECORD.unpack_from(
                raw,
                RUNTIME_PROTO_ENUM_HEADER.size
                + offset * RUNTIME_PROTO_ENUM_RECORD.size,
            )
            if (
                attribute_complete not in (0, 1)
                or reserved
                or field_index != indexes[offset]
                or value_kind != value_kinds[offset]
                or field_index in observed
                or first_attribute + attribute_count > len(attribute_indexes)
                or (not attribute_complete and attribute_count)
            ):
                checks["record_domain_closed"] = False
                break
            observed.add(field_index)
            if not attribute_complete:
                incomplete_attribute_count += 1
            constants.append(
                {
                    "field_index": field_index,
                    "number": _decode_enum_value(value_kind, value_bits),
                    "underlying_type": underlying_types[offset],
                    "custom_attribute_capture_complete": bool(attribute_complete),
                    "custom_attribute_type_indexes_owner_only": (
                        attribute_indexes[
                            first_attribute : first_attribute + attribute_count
                        ]
                        if attribute_complete
                        else None
                    ),
                }
            )
        else:
            checks["record_domain_closed"] = len(constants) == expected
    else:
        checks["record_domain_closed"] = False
    checks["attribute_failures_accounted"] = (
        type(status.get("attribute_failure_count")) is int
        and status["attribute_failure_count"] == incomplete_attribute_count
    )
    checks["attribute_retries_accounted"] = (
        type(status.get("attribute_retry_count", 0)) is int
        and status.get("attribute_retry_count", 0) >= 0
    )
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime proto enum validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    return {
        "schema": RUNTIME_PROTO_ENUM_CONSTANT_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": plan["inputs"],
        "inventory": file_identity(path),
        "status_receipt": file_identity(Path(plan["status_path"])),
        "counts": {
            "constant_count": expected,
            "underlying_type_counts": {
                name: underlying_types.count(name)
                for name in sorted(set(underlying_types))
            },
            "custom_attribute_reference_count": len(attribute_indexes),
            "complete_attribute_capture_count": expected - incomplete_attribute_count,
            "incomplete_attribute_capture_count": incomplete_attribute_count,
            "attribute_retry_count": status.get("attribute_retry_count", 0),
        },
        "constants": constants,
        "checks": checks,
        "policy": plan["policy"],
        "owner_only": True,
    }


def capture_runtime_proto_enum_constants(
    *,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    runtime_materializer_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 180.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_proto_enum_constants(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        runtime_materializer_model=runtime_materializer_model,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan = read_json(output_dir / "runtime-proto-enum-plan.private.json")
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
        raise AcquisitionError("runtime proto enum injector could not run") from error
    _private_text(
        output_dir / "runtime-proto-enum-injector.private.log",
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
            "runtime proto enum injection failed"
            + (f": {detail[-1]}" if detail else "")
        )
    deadline = time.monotonic() + timeout
    status_path = Path(plan["status_path"])
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        if status_path.is_file():
            candidate = read_json(status_path)
            if isinstance(candidate, dict) and candidate.get("status"):
                status = candidate
                break
        time.sleep(0.2)
    if status is None:
        raise AcquisitionError("runtime proto enum capture timed out")
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime proto enum capture failed "
            f"(kind={status.get('failure_kind_owner_only')})"
        )
    _seal_runtime_output(Path(plan["output_path"]))
    model = _validate(plan, status)
    model_path = output_dir / "runtime-proto-enum-constants.private.json"
    _private_json(model_path, model)
    return {
        "schema": model["schema"],
        "status": model["status"],
        "target": model["target"],
        "counts": model["counts"],
        "checks": model["checks"],
        "policy": model["policy"],
        "model": file_identity(model_path),
    }
