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

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.p22 import METHOD_DETAIL_CONSTRUCTOR
from alpha.p29 import _bounded_code, _message_types, _runtime, analyze_runtime_proto
from alpha.p38 import _binding as _proto_inventory_binding
from alpha.c04 import MappedPE
from alpha.h02 import file_identity, read_json


RUNTIME_PROTO_ROUNDTRIP_PLAN_SCHEMA = (
    "alpha.runtime-proto-roundtrip-plan/v1"
)
RUNTIME_PROTO_ROUNDTRIP_STATUS_SCHEMA = (
    "alpha.runtime-proto-roundtrip-status/v1"
)
RUNTIME_PROTO_ROUNDTRIP_SCHEMA = "alpha.runtime-proto-roundtrip/v1"
RUNTIME_PROTO_ROUNDTRIP_MAGIC = b"ALPHAPR1"
RUNTIME_PROTO_ROUNDTRIP_VERSION = 1
RUNTIME_PROTO_ROUNDTRIP_HEADER = struct.Struct("<8sIIIIIII64s")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime proto roundtrip {label} is not owner-only")
    return path


def _call_target(code: bytes, method_pointer: int, call_offset: int) -> int:
    if call_offset < 0 or call_offset + 5 > len(code) or code[call_offset] != 0xE8:
        raise AcquisitionError("runtime proto roundtrip direct call is invalid")
    return (
        method_pointer
        + call_offset
        + 5
        + int.from_bytes(
            code[call_offset + 1 : call_offset + 5], "little", signed=True
        )
    )


def _rip_slot(code: bytes, method_pointer: int, instruction: int) -> int:
    if (
        instruction < 0
        or instruction + 7 > len(code)
        or code[instruction : instruction + 3] != b"\x48\x8b\x0d"
    ):
        raise AcquisitionError("runtime proto roundtrip class slot is invalid")
    return (
        method_pointer
        + instruction
        + 7
        + int.from_bytes(
            code[instruction + 3 : instruction + 7], "little", signed=True
        )
    )


def _serializer_shape(code: bytes, method_pointer: int) -> dict[str, int] | None:

    if len(code) < 128 or code.count(b"\xff\x90") < 2:
        return None
    array_pattern = b"\x48\x8b\x0d"
    array_site = -1
    for cursor in range(0, len(code) - 14):
        if (
            code[cursor : cursor + 3] == array_pattern
            and code[cursor + 7 : cursor + 10] == b"\x89\xc2\xe8"
        ):
            array_site = cursor
            break
    if array_site < 0:
        return None
    object_site = -1
    for cursor in range(array_site + 14, min(len(code) - 12, array_site + 96)):
        if (
            code[cursor : cursor + 3] == array_pattern
            and code[cursor + 7] == 0xE8
        ):
            object_site = cursor
            break
    if object_site < 0:
        return None
    vtable_count = code.find(b"\x0f\xb7\x88")
    virtual_calls: list[int] = []
    for cursor in range(0, len(code) - 6):
        if code[cursor : cursor + 2] == b"\xff\x90":
            virtual_calls.append(
                int.from_bytes(code[cursor + 2 : cursor + 6], "little")
            )
    stream_array = code.find(b"\x48\x89\x7b")
    stream_null = code.find(b"\x48\xc7\x43")
    stream_bool = code.find(b"\xc6\x43")
    stream_zero = code.find(b"\xc7\x43", max(0, stream_bool - 16))
    stream_length = code.find(b"\x89\x43", max(0, stream_bool - 16))
    if (
        vtable_count < 0
        or vtable_count + 7 > len(code)
        or len(virtual_calls) != 2
        or min(stream_array, stream_null, stream_bool, stream_zero, stream_length) < 0
        or stream_array + 4 > len(code)
        or stream_null + 4 > len(code)
        or stream_bool + 4 > len(code)
        or stream_zero + 7 > len(code)
        or stream_length + 4 > len(code)
    ):
        return None
    return {
        "array_new_pointer": _call_target(code, method_pointer, array_site + 9),
        "byte_array_class_slot": _rip_slot(code, method_pointer, array_site),
        "object_new_pointer": _call_target(code, method_pointer, object_site + 7),
        "coded_output_class_slot": _rip_slot(code, method_pointer, object_site),
        "class_vtable_count_offset": int.from_bytes(
            code[vtable_count + 3 : vtable_count + 7], "little"
        ),
        "calculate_slot_offset": virtual_calls[0],
        "write_slot_offset": virtual_calls[1],
        "stream_array_offset": code[stream_array + 3],
        "stream_null_offset": code[stream_null + 3],
        "stream_bool_offset": code[stream_bool + 2],
        "stream_zero_offset": code[stream_zero + 2],
        "stream_length_offset": code[stream_length + 2],
    }


def _runtime_extensions(
    runtime: Any, *, binary: Path, message_base_descriptor: int
) -> dict[str, int]:
    base_name = runtime.renderer.render(message_base_descriptor)
    serializers: list[dict[str, int]] = []
    merges: list[dict[str, int]] = []
    with MappedPE(binary) as image:
        for method_index in range(runtime.method_count):
            row = runtime.method_row(method_index)
            if not row[3] or not row[5] & 0x10:
                continue
            parameters = runtime.method_parameters(method_index)
            if (
                len(parameters) == 1
                and parameters[0][1] == base_name
                and runtime.method_return(method_index) == "System.Byte[]"
            ):
                code = _bounded_code(image, row[3])
                shape = _serializer_shape(code, row[3]) if code is not None else None
                if shape is not None:
                    serializers.append(
                        {
                            "method_index": method_index,
                            "owner_type_index": row[0],
                            "method_pointer": row[3],
                            "method_metadata": row[2],
                            **shape,
                        }
                    )
            elif (
                len(parameters) == 2
                and [item[1] for item in parameters]
                == [base_name, "System.Byte[]"]
                and runtime.method_return(method_index) == "System.Void"
            ):
                code = _bounded_code(image, row[3])


                if code is not None:
                    merges.append(
                        {
                            "method_index": method_index,
                            "owner_type_index": row[0],
                            "method_pointer": row[3],
                            "method_metadata": row[2],
                        }
                    )
    if len(serializers) != 1:
        raise AcquisitionError(
            "runtime proto serializer extension is ambiguous "
            f"(candidates={len(serializers)})"
        )
    serializer = serializers[0]
    merges = [
        item
        for item in merges
        if item["owner_type_index"] == serializer["owner_type_index"]
    ]
    if len(merges) != 1:
        raise AcquisitionError(
            "runtime proto merge extension is ambiguous "
            f"(candidates={len(merges)})"
        )
    return {
        **{f"serializer_{key}": value for key, value in serializer.items()},
        **{f"merge_{key}": value for key, value in merges[0].items()},
    }


def _varint(value: int) -> bytes:
    if value < 0:
        raise AcquisitionError("runtime proto roundtrip varint is negative")
    output = bytearray()
    while value >= 0x80:
        output.append((value & 0x7F) | 0x80)
        value >>= 7
    output.append(value)
    return bytes(output)


def _probe_payload(field_number: int, wire: int) -> bytes:
    tag = _varint(field_number << 3 | wire)
    if wire == 0:
        return tag + b"\x01"
    if wire == 1:
        return tag + b"\x01\x00\x00\x00\x00\x00\x00\x00"
    if wire == 2:
        return tag + b"\x00"
    if wire == 5:
        return tag + b"\x01\x00\x00\x00"
    raise AcquisitionError("runtime proto roundtrip wire type is unsupported")


def _message_constructor(runtime: Any, type_index: int) -> dict[str, int]:
    candidates: list[dict[str, int]] = []
    for method_index in range(runtime.method_count):
        row = runtime.method_row(method_index)
        if (
            row[0] == type_index
            and row[9] & METHOD_DETAIL_CONSTRUCTOR
            and not row[5] & 0x10
            and row[10] == 0
            and row[3]
            and row[2]
        ):
            candidates.append(
                {
                    "method_index": method_index,
                    "pointer": row[3],
                    "metadata": row[2],
                }
            )
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime proto message constructor is ambiguous "
            f"(type={type_index}, candidates={len(candidates)})"
        )
    return candidates[0]


def _runtime_message_factory(runtime: Any) -> dict[str, int]:
    owners = [
        index
        for index in range(runtime.type_count)
        if runtime.renderer.root_name(index) == "System.Activator"
    ]
    if len(owners) != 1:
        raise AcquisitionError("runtime proto Activator owner is ambiguous")
    candidates: list[dict[str, int]] = []
    for method_index in range(runtime.method_count):
        row = runtime.method_row(method_index)
        if row[0] != owners[0] or not row[3] or not row[2] or not row[5] & 0x10:
            continue
        if (
            runtime.method_return(method_index) == "System.Object"
            and [item[1] for item in runtime.method_parameters(method_index)]
            == ["System.Type"]
        ):
            candidates.append(
                {
                    "method_index": method_index,
                    "pointer": row[3],
                    "metadata": row[2],
                }
            )
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime proto message factory is ambiguous "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def _roundtrip_binding(
    *, native_output_receipt: Path, proto_field_type_model: Path
) -> dict[str, Any]:
    receipt, paths, runtime = _runtime(native_output_receipt)
    inventory_binding = _proto_inventory_binding(native_output_receipt)
    analysis = analyze_runtime_proto(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
    )
    base, message_types = _message_types(runtime)
    if len(message_types) != analysis["counts"]["message_count"]:
        raise AcquisitionError("runtime proto roundtrip message domain differs")
    extensions = _runtime_extensions(
        runtime, binary=paths["binary"], message_base_descriptor=base
    )
    selected = None
    for message in analysis["messages_owner_only"]:
        if (
            len(message["fields"]) != 1
            or len(message["candidate_tags"]) != 1
            or len(message["mappings"]) != 1
        ):
            continue
        candidate = message["candidate_tags"][0]
        mapping = message["mappings"][0]
        if (
            candidate["wire"] not in (0, 1, 5)
            or mapping["primary_field_index"]
            != message["fields"][0]["field_index"]
        ):
            continue
        selected = message
        break
    if selected is None:
        raise AcquisitionError("runtime proto roundtrip probe message is unavailable")
    type_index = selected["type_index"]
    identity = runtime.renderer.identity_row(type_index)
    constructor = _message_constructor(runtime, type_index)
    factory = _runtime_message_factory(runtime)
    candidate = selected["candidate_tags"][0]
    payload = _probe_payload(candidate["field_number"], candidate["wire"])
    if not identity[3] or not identity[2] or not identity[6]:
        raise AcquisitionError("runtime proto roundtrip message identity is incomplete")
    return {
        "receipt": file_identity(native_output_receipt.expanduser().resolve()),
        "field_type_model": file_identity(proto_field_type_model.expanduser().resolve()),
        "binary": file_identity(paths["binary"]),
        "process_id": inventory_binding["process_id"],
        "type_index": type_index,
        "type_name": selected["name"],
        "class_pointer": identity[3],
        "type_descriptor": identity[2],
        "type_object": identity[6],
        "constructor": constructor,
        "message_factory": factory,
        "field_index": selected["fields"][0]["field_index"],
        "field_number": candidate["field_number"],
        "wire": candidate["wire"],
        "raw_tag": candidate["raw_tag"],
        "payload": payload,
        "extensions": extensions,
        "analysis_counts": analysis["counts"],
        "writer_family_descriptor": analysis[
            "writer_family_descriptor_owner_only"
        ],
        "object_header_bytes": analysis["object_header_bytes"],
    }


_COLLECTOR = Template(
    r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
typedef struct output_header {
    char magic[8]; uint32_t version,header_bytes,type_index,field_number,wire;
    uint32_t input_bytes,output_bytes; char executable[64];
} output_header;
_Static_assert(sizeof(output_header)==$header_bytes,"roundtrip header");
static const DWORD expected_pid=$process_id;
static const char executable_sha[]="$executable_sha";
static const uintptr_t message_class=$message_class;
static const uintptr_t constructor_pointer=$constructor_pointer;
static const uintptr_t constructor_metadata=$constructor_metadata;
static const uintptr_t message_type_object=$message_type_object;
static const uintptr_t message_factory_pointer=$message_factory_pointer;
static const uintptr_t message_factory_metadata=$message_factory_metadata;
static const uintptr_t serializer_pointer=$serializer_pointer;
static const uintptr_t serializer_metadata=$serializer_metadata;
static const uintptr_t merge_pointer=$merge_pointer;
static const uintptr_t merge_metadata=$merge_metadata;
static const uintptr_t array_new_pointer=$array_new_pointer;
static const uintptr_t object_new_pointer=$object_new_pointer;
static const uintptr_t byte_array_class_slot=$byte_array_class_slot;
static const uintptr_t coded_output_class_slot=$coded_output_class_slot;
static const uint32_t class_vtable_count_offset=$class_vtable_count_offset;
static const uint32_t calculate_slot_offset=$calculate_slot_offset;
static const uint32_t write_slot_offset=$write_slot_offset;
static const uint32_t stream_array_offset=$stream_array_offset;
static const uint32_t stream_null_offset=$stream_null_offset;
static const uint32_t stream_bool_offset=$stream_bool_offset;
static const uint32_t stream_zero_offset=$stream_zero_offset;
static const uint32_t stream_length_offset=$stream_length_offset;
static const uint32_t type_index=$type_index;
static const uint32_t field_number=$field_number;
static const uint32_t wire=$wire;
static const unsigned char input_data[]={$input_data};
static const wchar_t output_path[]=$output_path;
static const wchar_t status_path[]=$status_path;
typedef uintptr_t(*onearg_object)(uintptr_t);
typedef uintptr_t(*twoarg_object)(uintptr_t,uintptr_t);
typedef void(*instance_ctor)(uintptr_t,uintptr_t);
typedef uintptr_t(*static_onearg)(uintptr_t,uintptr_t);
typedef void(*static_twoarg_void)(uintptr_t,uintptr_t,uintptr_t);
typedef int32_t(*instance_size)(uintptr_t,uintptr_t);
typedef void(*instance_write)(uintptr_t,uintptr_t,uintptr_t);
static UINT message_id; static WNDPROC original_proc;
static volatile LONG callback_complete; static uint32_t failure_kind;
static volatile LONG probe_stage;
static uint32_t output_bytes; static unsigned char *output_copy;
static int readable(uintptr_t value,SIZE_T bytes){MEMORY_BASIC_INFORMATION r;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t end=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE f=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL,*buffer=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,os);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(a,&h,object,os,NULL,0,0)<0)ok=0;while(ok){DWORD n=0;if(!ReadFile(f,buffer,1048576u,&n,NULL)){ok=0;break;}if(!n)break;if(BCryptHashData(h,buffer,n,0)<0)ok=0;}if(ok&&BCryptFinishHash(h,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,output);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(f);return ok;}
static int executable_identity(char output[65]){wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,(DWORD)(sizeof(p)/sizeof(p[0])));return n&&n<sizeof(p)/sizeof(p[0])&&sha256_file(p,output);}
static int run_probe(void){
    InterlockedExchange(&probe_stage,1);
    uintptr_t byte_array_class=0;
    if(!readable(byte_array_class_slot,sizeof(byte_array_class)))return failure_kind=1,0;
    memcpy(&byte_array_class,(const void*)byte_array_class_slot,sizeof(byte_array_class));
    if(!byte_array_class)return failure_kind=2,0;
    onearg_object object_new=(onearg_object)object_new_pointer;
    twoarg_object array_new=(twoarg_object)array_new_pointer;
    (void)constructor_pointer;(void)constructor_metadata;
    static_onearg create_message=(static_onearg)message_factory_pointer;
    static_twoarg_void merge=(static_twoarg_void)merge_pointer;
    (void)serializer_pointer;(void)serializer_metadata;
    InterlockedExchange(&probe_stage,2);
    uintptr_t message=create_message(message_type_object,message_factory_metadata);
    if(!message)return failure_kind=3,0;
    InterlockedExchange(&probe_stage,3);
    uintptr_t observed_message_class=0;
    if(!readable(message,sizeof(observed_message_class)))return failure_kind=19,0;
    memcpy(&observed_message_class,(const void*)message,sizeof(observed_message_class));
    if(observed_message_class!=message_class)return failure_kind=20,0;
    InterlockedExchange(&probe_stage,4);
    uintptr_t input=array_new(byte_array_class,(uintptr_t)sizeof(input_data));
    if(!input||!readable(input,0x20u+sizeof(input_data)))return failure_kind=4,0;
    uint64_t observed_length=0;memcpy(&observed_length,(const void*)(input+0x18u),8u);
    if(observed_length!=sizeof(input_data))return failure_kind=5,0;
    memcpy((void*)(input+0x20u),input_data,sizeof(input_data));
    InterlockedExchange(&probe_stage,5);
    merge(message,input,merge_metadata);
    InterlockedExchange(&probe_stage,6);
    uintptr_t message_runtime_class=0;
    if(!readable(message,sizeof(message_runtime_class)))return failure_kind=6,0;
    memcpy(&message_runtime_class,(const void*)message,sizeof(message_runtime_class));
    if(!readable(message_runtime_class+class_vtable_count_offset,2u)||
       !readable(message_runtime_class+calculate_slot_offset,sizeof(uintptr_t))||
       !readable(message_runtime_class+write_slot_offset,sizeof(uintptr_t)))return failure_kind=7,0;
    uint16_t vtable_count=0;uintptr_t calculate_pointer=0,calculate_metadata=0;
    memcpy(&vtable_count,(const void*)(message_runtime_class+class_vtable_count_offset),2u);
    uintptr_t calculate_metadata_address=message_runtime_class+
        (uintptr_t)vtable_count*8u+calculate_slot_offset;
    if(!vtable_count||!readable(calculate_metadata_address,sizeof(uintptr_t)))return failure_kind=8,0;
    memcpy(&calculate_pointer,(const void*)(message_runtime_class+calculate_slot_offset),sizeof(calculate_pointer));
    memcpy(&calculate_metadata,(const void*)calculate_metadata_address,sizeof(calculate_metadata));
    if(!calculate_pointer||!calculate_metadata)return failure_kind=9,0;
    int32_t calculated=((instance_size)calculate_pointer)(message,calculate_metadata);
    if(calculated<=0||calculated>1048576)return failure_kind=10,0;
    InterlockedExchange(&probe_stage,7);
    uintptr_t output=array_new(byte_array_class,(uintptr_t)(uint32_t)calculated);
    uintptr_t coded_output_class=0;
    if(!readable(coded_output_class_slot,sizeof(coded_output_class)))return failure_kind=11,0;
    memcpy(&coded_output_class,(const void*)coded_output_class_slot,sizeof(coded_output_class));
    if(!output||!coded_output_class)return failure_kind=12,0;
    uintptr_t stream=object_new(coded_output_class);
    if(!stream||!readable(stream,0x80u))return failure_kind=13,0;
    uintptr_t zero=0;uint32_t zero32=0,length32=(uint32_t)calculated;unsigned char one=1u;
    memcpy((void*)(stream+stream_null_offset),&zero,sizeof(zero));
    memcpy((void*)(stream+stream_array_offset),&output,sizeof(output));
    memcpy((void*)(stream+stream_zero_offset),&zero32,sizeof(zero32));
    memcpy((void*)(stream+stream_length_offset),&length32,sizeof(length32));
    memcpy((void*)(stream+stream_bool_offset),&one,sizeof(one));
    uintptr_t write_pointer=0,write_metadata=0;
    uintptr_t write_metadata_address=message_runtime_class+
        (uintptr_t)vtable_count*8u+write_slot_offset;
    if(!readable(write_metadata_address,sizeof(uintptr_t)))return failure_kind=14,0;
    memcpy(&write_pointer,(const void*)(message_runtime_class+write_slot_offset),sizeof(write_pointer));
    memcpy(&write_metadata,(const void*)write_metadata_address,sizeof(write_metadata));
    if(!write_pointer||!write_metadata)return failure_kind=15,0;
    InterlockedExchange(&probe_stage,8);
    ((instance_write)write_pointer)(message,stream,write_metadata);
    InterlockedExchange(&probe_stage,9);
    if(!readable(output,0x20u))return failure_kind=16,0;
    uint64_t length=0;memcpy(&length,(const void*)(output+0x18u),8u);
    if(!length||length>1048576u||!readable(output+0x20u,(SIZE_T)length))return failure_kind=17,0;
    output_copy=(unsigned char*)malloc((SIZE_T)length);
    if(!output_copy)return failure_kind=18,0;
    memcpy(output_copy,(const void*)(output+0x20u),(SIZE_T)length);
    InterlockedExchange(&probe_stage,7);
    output_bytes=(uint32_t)length;return 1;
}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);int ok=run_probe();InterlockedExchange(&callback_complete,ok?1:-1);return ok;}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;
static BOOL CALLBACK select_window(HWND w,LPARAM v){selection*s=(selection*)(uintptr_t)v;DWORD pid=0;RECT b;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){s->window=w;s->count++;}return TRUE;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window)return failure_kind=20,0;message_id=RegisterWindowMessageW(status_path);SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);int ok=message_id&&(original_proc||GetLastError()==ERROR_SUCCESS);if(ok){DWORD_PTR result=0;InterlockedExchange(&callback_complete,0);ok=SendMessageTimeoutW(s.window,message_id,0,0,SMTO_BLOCK,60000,&result)&&InterlockedCompareExchange(&callback_complete,0,0)==1;}if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);if(!ok&&!failure_kind)failure_kind=21;return ok;}
static int write_output(void){output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"ALPHAPR1",8);h.version=1;h.header_bytes=sizeof(h);h.type_index=type_index;h.field_number=field_number;h.wire=wire;h.input_bytes=sizeof(input_data);h.output_bytes=output_bytes;memcpy(h.executable,executable_sha,64);FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;int ok=fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(input_data,1,sizeof(input_data),f)==sizeof(input_data)&&fwrite(output_copy,1,output_bytes,f)==output_bytes;if(fclose(f))ok=0;if(!ok)_wremove(output_path);else _wchmod(output_path,0600);return ok;}
static void write_status(const char*status,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"type_index_owner_only\": %u,\n  \"field_number\": %u,\n  \"wire\": %u,\n  \"input_bytes\": %u,\n  \"output_bytes\": %u,\n  \"failure_kind_owner_only\": %u,\n  \"probe_stage_owner_only\": %ld,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"saved_reference_generation_seed_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),type_index,field_number,wire,(unsigned)sizeof(input_data),output_bytes,failure_kind,InterlockedCompareExchange(&probe_stage,0,0),written?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char digest[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(digest)||strcmp(digest,executable_sha)){failure_kind=100;write_status("identity_mismatch",0);return 0;}int ok=dispatch();if(!ok){write_status("probe_failed",0);return 0;}ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
'''
)


def _source(binding: dict[str, Any], output: Path, status: Path) -> str:
    extensions = binding["extensions"]
    return _COLLECTOR.substitute(
        header_bytes=RUNTIME_PROTO_ROUNDTRIP_HEADER.size,
        process_id=binding["process_id"],
        executable_sha=binding["binary"]["sha256"],
        message_class=binding["class_pointer"],
        constructor_pointer=binding["constructor"]["pointer"],
        constructor_metadata=binding["constructor"]["metadata"],
        message_type_object=binding["type_object"],
        message_factory_pointer=binding["message_factory"]["pointer"],
        message_factory_metadata=binding["message_factory"]["metadata"],
        serializer_pointer=extensions["serializer_method_pointer"],
        serializer_metadata=extensions["serializer_method_metadata"],
        merge_pointer=extensions["merge_method_pointer"],
        merge_metadata=extensions["merge_method_metadata"],
        array_new_pointer=extensions["serializer_array_new_pointer"],
        object_new_pointer=extensions["serializer_object_new_pointer"],
        byte_array_class_slot=extensions["serializer_byte_array_class_slot"],
        coded_output_class_slot=extensions["serializer_coded_output_class_slot"],
        class_vtable_count_offset=extensions[
            "serializer_class_vtable_count_offset"
        ],
        calculate_slot_offset=extensions["serializer_calculate_slot_offset"],
        write_slot_offset=extensions["serializer_write_slot_offset"],
        stream_array_offset=extensions["serializer_stream_array_offset"],
        stream_null_offset=extensions["serializer_stream_null_offset"],
        stream_bool_offset=extensions["serializer_stream_bool_offset"],
        stream_zero_offset=extensions["serializer_stream_zero_offset"],
        stream_length_offset=extensions["serializer_stream_length_offset"],
        type_index=binding["type_index"],
        field_number=binding["field_number"],
        wire=binding["wire"],
        input_data=",".join(f"0x{value:02x}" for value in binding["payload"]),
        output_path=_wide_literal(_windows_z_path(output)),
        status_path=_wide_literal(_windows_z_path(status)),
        status_schema=RUNTIME_PROTO_ROUNDTRIP_STATUS_SCHEMA,
    )


def prepare_runtime_proto_roundtrip_probe(
    *,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _roundtrip_binding(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
    )
    output = output_dir / "runtime-proto-roundtrip.private.bin"
    status = output_dir / "runtime-proto-roundtrip-status.private.json"
    plan_path = output_dir / "runtime-proto-roundtrip-plan.private.json"
    build = _owner_directory(output_dir / "build-runtime-proto-roundtrip")
    source = build / "runtime-proto-roundtrip.c"
    injector_source = build / "runtime-proto-roundtrip-injector.c"
    for stale in (output, status):
        stale.unlink(missing_ok=True)
    _private_text(source, _source(binding, output, status))
    _private_text(injector_source, runtime_injector_source())
    collector = build / (
        "alpha-runtime-proto-roundtrip-"
        + file_identity(source)["sha256"][:12]
        + ".dll"
    )
    injector = build / "alpha-runtime-proto-roundtrip-injector.exe"
    cc = _compiler(compiler)
    _build(
        [
            str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(source), "-o",
            str(collector), "-lbcrypt",
        ],
        label="runtime proto roundtrip collector",
    )
    _build(
        [
            str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(injector_source), "-o",
            str(injector),
        ],
        label="runtime proto roundtrip injector",
    )
    for artifact in (collector, injector):
        artifact.chmod(0o600)
    private_binding = dict(binding)
    private_binding["payload_owner_only"] = list(private_binding.pop("payload"))
    private_binding["class_pointer_owner_only"] = private_binding.pop(
        "class_pointer"
    )
    private_binding["type_descriptor_owner_only"] = private_binding.pop(
        "type_descriptor"
    )
    private_binding["type_object_owner_only"] = private_binding.pop("type_object")
    private_binding["constructor_owner_only"] = private_binding.pop("constructor")
    private_binding["message_factory_owner_only"] = private_binding.pop(
        "message_factory"
    )
    private_binding["extensions_owner_only"] = private_binding.pop("extensions")
    plan = {
        "schema": RUNTIME_PROTO_ROUNDTRIP_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": binding["binary"]["path"],
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
        },
        "binding": private_binding,
        "collector": file_identity(collector),
        "injector": file_identity(injector),
        "output_path": str(output),
        "status_path": str(status),
        "policy": {
            "runtime_merge_from_used": True,
            "runtime_write_to_used": True,
            "runtime_message_constructor_used": True,
            "runtime_roles_structurally_derived": True,
            "saved_reference_generation_seed_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
            "raw_pointers_owner_only": True,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_PROTO_ROUNDTRIP_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "probe": {
            "message": binding["type_name"],
            "field_number": binding["field_number"],
            "wire": binding["wire"],
        },
        "policy": plan["policy"],
    }


def _validate_roundtrip(plan: dict[str, Any], status: dict[str, Any]) -> dict[str, Any]:
    path = _owner_file(Path(plan["output_path"]), label="output")
    raw = path.read_bytes()
    if len(raw) < RUNTIME_PROTO_ROUNDTRIP_HEADER.size:
        raise AcquisitionError("runtime proto roundtrip output is truncated")
    header = RUNTIME_PROTO_ROUNDTRIP_HEADER.unpack_from(raw)
    expected = plan["binding"]
    input_start = RUNTIME_PROTO_ROUNDTRIP_HEADER.size
    input_end = input_start + header[6]
    output_end = input_end + header[7]
    checks = {
        "status_complete": status.get("status") == "complete",
        "header_bound": (
            header[0] == RUNTIME_PROTO_ROUNDTRIP_MAGIC
            and header[1] == RUNTIME_PROTO_ROUNDTRIP_VERSION
            and header[2] == RUNTIME_PROTO_ROUNDTRIP_HEADER.size
            and header[3] == expected["type_index"]
            and header[4] == expected["field_number"]
            and header[5] == expected["wire"]
            and header[8].decode("ascii")
            == plan["target"]["executable_sha256"]
            and output_end == len(raw)
        ),
        "input_matches_probe": (
            raw[input_start:input_end]
            == bytes(expected["payload_owner_only"])
        ),
        "runtime_output_nonempty": header[7] > 0,
        "runtime_echoes_exact_probe": raw[input_end:output_end]
        == raw[input_start:input_end],
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_reference_generation_seed_absent": status.get(
            "saved_reference_generation_seed_used"
        )
        is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime proto roundtrip validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    return {
        "schema": RUNTIME_PROTO_ROUNDTRIP_SCHEMA,
        "status": "runtime-validated",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"]
        },
        "probe": {
            "message": expected["type_name"],
            "field_number": header[4],
            "wire": header[5],
            "input_bytes": header[6],
            "output_bytes": header[7],
        },
        "inventory": file_identity(path),
        "status_receipt": file_identity(Path(plan["status_path"])),
        "checks": checks,
        "policy": plan["policy"],
        "owner_only": True,
    }


def capture_runtime_proto_roundtrip_probe(
    *,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 120.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_proto_roundtrip_probe(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-proto-roundtrip-plan.private.json"
    plan = read_json(plan_path)
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
            "runtime proto roundtrip injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-proto-roundtrip-injector.private.log",
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
        raise AcquisitionError("runtime proto roundtrip injection failed")
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
        raise AcquisitionError("runtime proto roundtrip capture timed out")
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime proto roundtrip capture failed "
            f"(kind={status.get('failure_kind_owner_only')})"
        )
    _seal_runtime_output(Path(plan["output_path"]))
    model = _validate_roundtrip(plan, status)
    _private_json(output_dir / "runtime-proto-roundtrip.private.json", model)
    return model


from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.p18 import capture_runtime_native_semantics
from alpha.p18 import capture_runtime_type_ancestry
from alpha.p19 import capture_runtime_type_identity_inventory
from alpha.p18 import inspect_runtime_string_layout_candidates
from alpha.p21 import capture_runtime_type_graph_inventory
from alpha.p18 import capture_runtime_method_name_materialization
from alpha.p22 import capture_runtime_method_detail_inventory
from alpha.p23 import capture_runtime_native_member_detail_inventory
from alpha.p24 import capture_runtime_event_module_inventory
from alpha.p25 import capture_runtime_base_type_reference_inventory, capture_runtime_type_reference_inventory
from alpha.p20 import capture_runtime_string_literal_inventory
from alpha.p26 import capture_runtime_method_generic_inventory
from alpha.p28 import capture_runtime_generic_parameter_detail_inventory
from alpha.p39 import capture_runtime_type_descriptor_values
from alpha.p27 import capture_runtime_constructed_generic_layout
from alpha.p26 import capture_runtime_class_extents
from alpha.p28 import capture_runtime_field_type_store
from alpha.p32 import capture_runtime_vtable_interfaces
from alpha.p34 import capture_runtime_constructed_vtables
from alpha.p30 import capture_runtime_constructed_methods
from alpha.p36 import capture_runtime_interface_method_maps
from alpha.p37 import capture_runtime_encoded_vtables
from alpha.p29 import capture_runtime_vtable_declarations
from alpha.p34 import capture_field_reference_fixed_point
from alpha.p35 import verify_runtime_nominal_field_aliases


def capture_session_inventories(*, session, live, progress=None, proto_only=False):
    root = session.root
    snapshot = root / "memory/runtime-memory.private.bin"
    classes = root / "classes/runtime-class-model.private.json"
    materializer = root / "materializer-live/runtime-type-materializer.validated.private.json"
    native = root / "materializer-live/runtime-native-inventory.private.bin"
    members = root / "materializer-live/runtime-native-members.private.bin"
    reflection = root / "semantics-complete/runtime-reflection-semantics.private.json"
    native_semantics = root / "native-semantics/runtime-native-semantics.private.json"
    helper = root / "helpers-live/runtime-native-helpers.validated.private.json"
    ancestry = root / "ancestry/runtime-type-ancestry.private.bin"

    def pair(stage, stem, prefix):
        return {prefix + "_model": root / stage / (stem + ".private.json"),
                prefix + "_inventory": root / stage / (stem + ".private.bin")}

    def run(name, function, inputs, *, static=False, filename=None,
            statuses=("runtime-validated", "validated", "complete"),
            require_constraint_closure=False):
        dependencies = tuple(sorted({
            value.relative_to(root).parts[0] for value in inputs.values()
            if isinstance(value, Path) and value.is_relative_to(root)
        }))
        if progress:
            progress(name)
        session.register_planned_stage("acquisition", name)
        def capture(out):
            if static:
                return function(binary=live["binary"], **inputs, output=out / filename)
            result = function(**live, **inputs, output_dir=out)
            if require_constraint_closure:
                remaining = result.get("counts", {}).get("new_constraint_descriptor_count")
                if type(remaining) is not int or remaining != 0:
                    raise AcquisitionError("full generic parameter constraints are not closed in current type references")
            return result
        return session.run(name, capture, dependencies=dependencies, accepted_statuses=statuses)

    run("native-semantics", capture_runtime_native_semantics, dict(
        snapshot=snapshot, reflection_semantics_model=reflection,
        materializer_model=materializer, native_inventory=native, native_member_inventory=members),
        statuses=("partially-resolved",))
    run("ancestry", capture_runtime_type_ancestry, dict(
        snapshot=snapshot, native_semantics_model=native_semantics, native_inventory=native))
    run("string-layout", inspect_runtime_string_layout_candidates,
        dict(snapshot=snapshot, native_inventory=native), static=True,
        filename="runtime-string-layout.private.json", statuses=("candidate-derived",))
    run("identity", capture_runtime_type_identity_inventory, dict(
        reflection_semantics_model=reflection, native_inventory=native,
        string_layout_model=root / "string-layout/runtime-string-layout.private.json",
        ancestry_model=root / "ancestry/runtime-type-ancestry.private.json"))
    identity = pair("identity", "runtime-type-identity", "type_identity")
    run("method-names", capture_runtime_method_name_materialization, dict(
        reflection_semantics_model=reflection, materializer_model=materializer, native_inventory=native))
    run("methods", capture_runtime_method_detail_inventory, dict(
        **identity, reflection_semantics_model=reflection, native_inventory=native,
        method_name_receipt=root / "method-names/runtime-method-name-receipt.private.json",
        method_name_observation=root / "method-names/runtime-method-names.private.bin",
        runtime_inventory_dispatch=None))
    methods = pair("methods", "runtime-method-detail", "method_detail")
    member_inputs = dict(**identity, reflection_semantics_model=reflection,
        native_semantics_model=native_semantics, native_inventory=native,
        native_member_inventory=members, runtime_inventory_dispatch=None)
    run("members", capture_runtime_native_member_detail_inventory, member_inputs)
    run("events", capture_runtime_event_module_inventory, dict(member_inputs, **methods, ancestry_inventory=ancestry,
        string_layout_model=root / "string-layout/runtime-string-layout.private.json"))
    run("type-graph", capture_runtime_type_graph_inventory, dict(
        **identity, reflection_semantics_model=reflection, ancestry_inventory=ancestry))
    graph = pair("type-graph", "runtime-type-graph", "type_graph")
    reference_inputs = dict(**identity, **methods, **graph,
        **pair("members", "runtime-native-member-detail", "native_member_detail"),
        **pair("events", "runtime-event-module", "event_module"),
        reflection_semantics_model=reflection, ancestry_inventory=ancestry)
    run("base-references", capture_runtime_base_type_reference_inventory, reference_inputs)
    base_references = pair("base-references", "runtime-type-reference", "type_reference")
    run("strings", capture_runtime_string_literal_inventory, identity)
    run("method-generics", capture_runtime_method_generic_inventory, dict(
        **identity, **methods, **base_references, reflection_semantics_model=reflection,
        **pair("strings", "runtime-metadata-usage-members", "metadata_usage_member")))
    generics = pair("method-generics", "runtime-method-generics", "method_generic")
    run("generic-parameters", capture_runtime_generic_parameter_detail_inventory, dict(
        **identity, **methods, **generics, **base_references, reflection_semantics_model=reflection,
        type_graph_inventory=graph["type_graph_inventory"]))
    run("references", capture_runtime_type_reference_inventory, dict(
        **reference_inputs, **generics,
        **pair("base-references", "runtime-type-reference", "base_type_reference"),
        **pair("generic-parameters", "runtime-generic-parameter-detail", "generic_parameter_detail")))
    references = pair("references", "runtime-type-reference", "type_reference")
    if proto_only:
        return
    closure = capture_field_reference_fixed_point(root=root, run=run, pair=pair, identity=identity,
        references=references, materializer=materializer, helper=helper, native_semantics=native_semantics,
        method_pair=methods, generic_pair=generics, graph_pair=graph,
        reflection_semantics_model=reflection)
    references, constructed = closure["references"], closure["constructed"]
    run("field-type-aliases", verify_runtime_nominal_field_aliases, dict(
        field_type_store_model=closure["field_type_store_model"], **references), static=True,
        filename="runtime-nominal-field-aliases.private.json", statuses=("observed-aliases-agree",))
    run("class-extents", capture_runtime_class_extents, dict(**constructed,
        event_capture_plan=root / "events/runtime-event-module-plan.private.json"), statuses=("runtime-observed",))
    run("vtables", capture_runtime_vtable_interfaces, dict(
        **identity, **graph, **references, **methods, **constructed, class_model=classes))
    vtables = pair("vtables", "runtime-vtable-interface", "vtable_interface")
    run("constructed-vtables", capture_runtime_constructed_vtables, dict(
        **constructed, **references, **vtables))
    run("constructed-methods", capture_runtime_constructed_methods, dict(
        **constructed, **methods, native_helper_model=helper, class_model=classes))
    interface_inputs = dict(
        **identity, **graph, **references, **methods, **vtables,
        **pair("constructed-methods", "runtime-constructed-method", "constructed_method"),
        reflection_semantics_model=reflection)
    run("encoded-vtables", capture_runtime_encoded_vtables, interface_inputs,
        statuses=("runtime-observed",))
    run("vtable-declarations", capture_runtime_vtable_declarations, dict(
        **interface_inputs, **pair("encoded-vtables", "runtime-encoded-vtables", "encoded_vtable")),
        statuses=("runtime-declarations-validated",))
    run("interface-method-maps", capture_runtime_interface_method_maps, dict(
        **interface_inputs, **pair("encoded-vtables", "runtime-encoded-vtables", "encoded_vtable"),
        **pair("vtable-declarations", "runtime-vtable-declarations", "vtable_declaration")),
        statuses=("runtime-slot-projected",))
