from alpha.h02 import windows_run as _host_run

import json
import os
import stat
import struct
import subprocess
import time
from pathlib import Path
from string import Template
from typing import Any, Mapping

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, runtime_injector_source
from alpha.h01 import (
    AcquisitionError,
    owner_only_path_bits,
    owner_uid,
    same_executable_path,
)
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p22 import RUNTIME_METHOD_DETAIL_HEADER, RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_METHOD, RUNTIME_METHOD_DETAIL_SCHEMA, RUNTIME_METHOD_DETAIL_VERSION
from alpha.p26 import RUNTIME_METHOD_GENERIC_HEADER, RUNTIME_METHOD_GENERIC_MAGIC, RUNTIME_METHOD_GENERIC_RECORD, RUNTIME_METHOD_GENERIC_SCHEMA, RUNTIME_METHOD_GENERIC_VERSION, _select_generic_arguments_candidate, _validated_model
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA, _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION
from alpha.h02 import file_identity, read_json


RUNTIME_REFLECTION_METHOD_GENERIC_PLAN_SCHEMA = (
    "alpha.runtime-reflection-method-generic-plan/v1"
)
RUNTIME_REFLECTION_METHOD_GENERIC_STATUS_SCHEMA = (
    "alpha.runtime-reflection-method-generic-status/v1"
)
_EMPTY_INPUT_SHA256 = "0" * 64


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime reflection method generic {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime reflection method generic {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime reflection method generic {label} digest is invalid"
        )
    return value


def _binding(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    binary_identity = file_identity(binary)
    target = binary_identity["sha256"]
    identity_model_path, identity_path, identity_model, _ = _validated_model(
        model_path=type_identity_model,
        inventory_path=type_identity_inventory,
        schema=RUNTIME_TYPE_IDENTITY_SCHEMA,
        inventory_key="identity_inventory",
        executable_sha256=target,
        label="type identity",
    )
    reference_model_path, reference_path, reference_model, _ = (
        _validated_model(
            model_path=type_reference_model,
            inventory_path=type_reference_inventory,
            schema=RUNTIME_TYPE_REFERENCE_SCHEMA,
            inventory_key="inventory",
            executable_sha256=target,
            label="type reference",
        )
    )
    method_model_path, method_path, _method_model, _ = _validated_model(
        model_path=method_detail_model,
        inventory_path=method_detail_inventory,
        schema=RUNTIME_METHOD_DETAIL_SCHEMA,
        inventory_key="inventory",
        executable_sha256=target,
        label="method detail",
    )
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantics"
    )
    semantics = read_json(semantics_path)
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
    } if isinstance(semantics, dict) else {}
    from_handle = operations.get("method.from_handle", {})
    if (
        semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary", {}).get("sha256") != target
        or semantics.get("checks", {}).get("all_operations_resolved")
        is not True
        or from_handle.get("semantic_identity_resolved") is not True
        or not isinstance(from_handle.get("method_pointer"), int)
        or not isinstance(from_handle.get("metadata_pointer"), int)
        or from_handle["method_pointer"] <= 0
        or from_handle["metadata_pointer"] <= 0
    ):
        raise AcquisitionError(
            "runtime reflection method generic semantics are stale"
        )
    identity_plan_path = _owner_file(
        identity_model_path.parent / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    identity_status_path = _owner_file(
        identity_model_path.parent
        / "runtime-type-identity-status.private.json",
        label="type identity status",
    )
    identity_plan = read_json(identity_plan_path)
    identity_status = read_json(identity_status_path)
    process_id = identity_plan.get("target", {}).get("process_id")
    embedded_offset = identity_plan.get(
        "embedded_type_descriptor_offset_owner_only"
    )
    graph_status_record = reference_model.get("inputs", {}).get(
        "type_graph_status"
    )
    graph_status_path = _owner_file(
        Path(graph_status_record.get("path", "")),
        label="type graph status",
    ) if isinstance(graph_status_record, dict) else None
    graph_status = read_json(graph_status_path) if graph_status_path else {}
    array_length_qword = graph_status.get("array_length_qword_owner_only")
    array_vector_qword = graph_status.get("array_vector_qword_owner_only")
    if (
        identity_plan.get("status") != "prepared"
        or identity_plan.get("target", {}).get("executable_sha256")
        != target
        or identity_status.get("status") != "complete"
        or identity_status.get("process_id") != process_id
        or not isinstance(process_id, int)
        or process_id <= 0
        or not isinstance(embedded_offset, int)
        or not 0 < embedded_offset < 512
        or not isinstance(array_length_qword, int)
        or not isinstance(array_vector_qword, int)
        or not 1 <= array_length_qword < array_vector_qword < 10
    ):
        raise AcquisitionError(
            "runtime reflection method generic process binding is stale"
        )
    identity = identity_path.read_bytes()
    methods = method_path.read_bytes()
    references = reference_path.read_bytes()
    if (
        len(identity) < _IDENTITY_HEADER.size
        or len(methods) < RUNTIME_METHOD_DETAIL_HEADER.size
        or len(references) < RUNTIME_TYPE_REFERENCE_HEADER.size
    ):
        raise AcquisitionError(
            "runtime reflection method generic input is truncated"
        )
    identity_header = _IDENTITY_HEADER.unpack_from(identity)
    method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(methods)
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(references)
    type_count = identity_header[5]
    image_base, image_bytes = identity_header[6:8]
    if (
        identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or method_header[0] != RUNTIME_METHOD_DETAIL_MAGIC
        or method_header[1] != RUNTIME_METHOD_DETAIL_VERSION
        or reference_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or reference_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or method_header[5] <= 0
        or method_header[8] != image_base
        or method_header[9] != image_bytes
        or reference_header[10] != image_base
        or reference_header[11] != image_bytes
    ):
        raise AcquisitionError(
            "runtime reflection method generic input headers conflict"
        )
    candidate = _select_generic_arguments_candidate(
        identity=identity,
        methods=methods,
        references=references,
    )
    return {
        "binary": binary_identity,
        "semantics": file_identity(semantics_path),
        "type_identity_model": file_identity(identity_model_path),
        "type_identity_inventory": file_identity(identity_path),
        "type_identity_plan": file_identity(identity_plan_path),
        "type_identity_status": file_identity(identity_status_path),
        "type_reference_model": file_identity(reference_model_path),
        "type_reference_inventory": file_identity(reference_path),
        "type_graph_status": file_identity(graph_status_path),
        "method_detail_model": file_identity(method_model_path),
        "method_detail_inventory": file_identity(method_path),
        "process_id": process_id,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "type_count": type_count,
        "method_count": method_header[5],
        "handle_qword": method_header[10],
        "embedded_descriptor_offset": embedded_offset,
        "array_length_qword": array_length_qword,
        "array_vector_qword": array_vector_qword,
        "candidate": candidate,
        "from_handle": {
            "pointer": from_handle["method_pointer"],
            "metadata": from_handle["metadata_pointer"],
        },
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define ALPHA_BATCH_METHODS 128u
#define ALPHA_MAX_GENERIC_ARGUMENTS 64u
typedef struct{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t type_count,image_base,image_bytes,string_bytes;char executable[64],native[64],semantics[64];}identity_header;
typedef struct{uint32_t definition_index,flags;uint64_t descriptor,class_pointer,module_pointer,declaring_descriptor,type_object;uint32_t attributes,name_bytes,namespace_bytes,reserved;uint64_t name_offset,namespace_offset;}identity_record;
typedef struct{char magic[8];uint32_t version,header_bytes,method_bytes,parameter_bytes;uint64_t method_count,parameter_count,string_bytes,image_base,image_bytes,handle_qword,reserved;char executable[64],native[64],identity[64],names[64];}method_header;
typedef struct{uint32_t definition_index,method_index;uint64_t metadata,function,return_descriptor;uint32_t attributes,impl_attributes,token,slot,flags,parameter_count;uint64_t parameter_start,name_offset;}method_record;
typedef struct{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t method_count,generic_method_count,generic_argument_count,image_base,image_bytes,candidate_method_index;char executable[64],identity[64],methods[64],references[64],semantics[64],members[64];}output_header;
typedef struct{uint32_t method_index,argument_count;uint64_t argument_start;}output_record;
_Static_assert(sizeof(identity_header)==$identity_header_bytes,"identity header");
_Static_assert(sizeof(identity_record)==$identity_record_bytes,"identity record");
_Static_assert(sizeof(method_header)==$method_header_bytes,"method header");
_Static_assert(sizeof(method_record)==$method_record_bytes,"method record");
_Static_assert(sizeof(output_header)==$output_header_bytes,"output header");
_Static_assert(sizeof(output_record)==$output_record_bytes,"output record");
static const char executable_sha256[]="$executable_sha256",identity_sha256[]="$identity_sha256",method_sha256[]="$method_sha256",reference_sha256[]="$reference_sha256",semantics_sha256[]="$semantics_sha256",member_sha256[]="$member_sha256";
static const DWORD expected_pid=${process_id}u;static const uint64_t expected_type_count=${type_count}ull,expected_method_count=${method_count}ull,expected_image_base=${image_base}ull,expected_image_bytes=${image_bytes}ull,expected_candidate_method=${candidate_method}ull;
static const uint32_t handle_qword=${handle_qword}u,embedded_descriptor_offset=${embedded_descriptor_offset}u,array_length_qword=${array_length_qword}u,array_vector_qword=${array_vector_qword}u;
static const uintptr_t runtime_type_class=${runtime_type_class}ull,from_handle_pointer=${from_handle_pointer}ull,from_handle_metadata=${from_handle_metadata}ull,generic_arguments_pointer=${generic_arguments_pointer}ull,generic_arguments_metadata=${generic_arguments_metadata}ull;
static const wchar_t identity_path[]=$identity_path,method_path[]=$method_path,output_path[]=$output_path,status_path[]=$status_path;
static unsigned char*identity_data,*method_data;static identity_record*types;static method_record*methods;static output_record*records;static uint64_t*arguments;static uint64_t argument_count,argument_capacity,generic_count,capture_index,verify_index,completed_count,verified_count,failure_index;static uint32_t failure_kind;static UINT message_id;static WNDPROC original_proc;static volatile LONG action,complete;
typedef uintptr_t(*static_threearg)(uintptr_t,uintptr_t,uintptr_t,uintptr_t);typedef uintptr_t(*instance_noarg)(uintptr_t,uintptr_t);
static int readable(uintptr_t value,SIZE_T bytes){MEMORY_BASIC_INFORMATION r;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t end=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}
static int read_file(const wchar_t*path,unsigned char**data,SIZE_T*bytes){*data=NULL;*bytes=0;FILE*f=_wfopen(path,L"rb");if(!f||_fseeki64(f,0,SEEK_END))return 0;__int64 size=_ftelli64(f);if(size<0||_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*bytes=(SIZE_T)size;*data=malloc(*bytes?*bytes:1u);int ok=*data&&fread(*data,1,*bytes,f)==*bytes;fclose(f);if(!ok){free(*data);*data=NULL;}return ok;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE input=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(input==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char*object=NULL,*buffer=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;while(ok){DWORD count=0;if(!ReadFile(input,buffer,1048576u,&count,NULL)){ok=0;break;}if(!count)break;if(BCryptHashData(hash,buffer,count,0)<0)ok=0;}if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)<0)ok=0;if(ok)digest_hex(digest,output);if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(input);return ok;}
static int executable_identity(char output[65]){wchar_t path[32768];DWORD n=GetModuleFileNameW(NULL,path,32768);return n&&n<32768&&sha256_file(path,output);}
static int append_argument(uint64_t value){if(!value||value&7u||argument_count>=expected_method_count*ALPHA_MAX_GENERIC_ARGUMENTS)return 0;if(argument_count==argument_capacity){uint64_t next=argument_capacity?argument_capacity*2u:4096u;if(next>expected_method_count*ALPHA_MAX_GENERIC_ARGUMENTS)next=expected_method_count*ALPHA_MAX_GENERIC_ARGUMENTS;uint64_t*grown=realloc(arguments,(SIZE_T)next*8u);if(!grown)return 0;arguments=grown;argument_capacity=next;}arguments[argument_count++]=value;return 1;}
static uintptr_t method_object(uint64_t index){method_record*m=&methods[index];if(m->definition_index>=expected_type_count||!m->metadata)return 0;uintptr_t owner=types[m->definition_index].class_pointer+embedded_descriptor_offset;uintptr_t object=((static_threearg)from_handle_pointer)(m->metadata,owner,1u,from_handle_metadata);uintptr_t observed=0;if(!readable(object,24u))return 0;memcpy(&observed,(const void*)(object+16u),8u);return observed==m->metadata?object:0;}
static int generic_arguments(uint64_t index,uintptr_t values[ALPHA_MAX_GENERIC_ARGUMENTS],uint32_t*count){*count=0;uintptr_t object=method_object(index);if(!object)return 0;uintptr_t array=((instance_noarg)generic_arguments_pointer)(object,generic_arguments_metadata);if(!readable(array,((SIZE_T)array_vector_qword+1u)*8u))return 0;uintptr_t length=0;memcpy(&length,(const void*)(array+(uintptr_t)array_length_qword*8u),8u);if(length>ALPHA_MAX_GENERIC_ARGUMENTS)return 0;uintptr_t vector=array+(uintptr_t)array_vector_qword*8u;if(length&&!readable(vector,(SIZE_T)length*8u))return 0;for(uint32_t i=0;i<(uint32_t)length;i++){uintptr_t type=0,klass=0,descriptor=0;memcpy(&type,(const void*)(vector+(uintptr_t)i*8u),8u);if(!readable(type,((SIZE_T)handle_qword+1u)*8u))return 0;memcpy(&klass,(const void*)type,8u);memcpy(&descriptor,(const void*)(type+(uintptr_t)handle_qword*8u),8u);if(klass!=runtime_type_class||!readable(descriptor,16u)||descriptor&7u)return 0;for(uint32_t j=0;j<i;j++)if(values[j]==descriptor)return 0;values[i]=descriptor;}*count=(uint32_t)length;return 1;}
static int capture_batch(void){uint64_t end=capture_index+ALPHA_BATCH_METHODS;if(end>expected_method_count)end=expected_method_count;for(;capture_index<end;capture_index++){output_record*out=&records[capture_index];out->method_index=(uint32_t)capture_index;out->argument_start=argument_count;uintptr_t values[ALPHA_MAX_GENERIC_ARGUMENTS]={0};uint32_t count=0;if(!generic_arguments(capture_index,values,&count)){failure_index=capture_index+1u;failure_kind=20u;return 0;}out->argument_count=count;for(uint32_t i=0;i<count;i++)if(!append_argument(values[i])){failure_index=capture_index+1u;failure_kind=21u;return 0;}generic_count+=!!count;completed_count++;}return 1;}
static int verify_batch(void){uint64_t end=verify_index+ALPHA_BATCH_METHODS;if(end>expected_method_count)end=expected_method_count;for(;verify_index<end;verify_index++){output_record*out=&records[verify_index];uintptr_t values[ALPHA_MAX_GENERIC_ARGUMENTS]={0};uint32_t count=0;if(!generic_arguments(verify_index,values,&count)||count!=out->argument_count){failure_index=verify_index+1u;failure_kind=30u;return 0;}for(uint32_t i=0;i<count;i++)if(values[i]!=arguments[out->argument_start+i]){failure_index=verify_index+1u;failure_kind=31u;return 0;}verified_count++;}return 1;}
static LRESULT CALLBACK window_proc(HWND window,UINT message,WPARAM wparam,LPARAM lparam){if(message!=message_id)return CallWindowProcW(original_proc,window,message,wparam,lparam);LONG selected=InterlockedCompareExchange(&action,0,0);int ok=selected==1?capture_batch():selected==2?verify_batch():0;InterlockedExchange(&complete,ok?1:-1);return ok;}
typedef struct{DWORD pid;HWND window;uint32_t count;}selection;static BOOL CALLBACK select_window(HWND window,LPARAM value){selection*s=(selection*)(uintptr_t)value;DWORD pid=0;RECT b;if(!IsWindowVisible(window)||GetWindow(window,GW_OWNER)||!GetWindowRect(window,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(window,&pid);if(pid==s->pid){s->window=window;s->count++;}return TRUE;}
static int send_action(HWND window,LONG selected){DWORD_PTR result=0;InterlockedExchange(&action,selected);InterlockedExchange(&complete,0);return SendMessageTimeoutW(window,message_id,0,0,SMTO_BLOCK,60000,&result)&&InterlockedCompareExchange(&complete,0,0)==1;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window){failure_kind=100u;failure_index=s.count;return 0;}message_id=RegisterWindowMessageW(L"ALPHA v2 reflection method generic inventory");SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);DWORD error=GetLastError();int ok=message_id&&(original_proc||error==ERROR_SUCCESS);while(ok&&capture_index<expected_method_count)ok=send_action(s.window,1);while(ok&&verify_index<expected_method_count)ok=send_action(s.window,2);if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);original_proc=NULL;if(!ok&&!failure_kind)failure_kind=101u;return ok;}
static void write_status(const char*status,int written){FILE*out=_wfopen(status_path,L"wb");if(!out)return;fprintf(out,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"completed_method_count\": %llu,\n  \"generic_method_count\": %llu,\n  \"generic_argument_count\": %llu,\n  \"second_observation_method_count\": %llu,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"reflection_generic_arguments_semantically_resolved\": true,\n  \"second_generic_observation\": true,\n  \"saved_method_generic_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)completed_count,(unsigned long long)generic_count,(unsigned long long)argument_count,(unsigned long long)verified_count,(unsigned long long)failure_index,failure_kind,written?"true":"false");fclose(out);}
static int write_output(void){output_header header;memset(&header,0,sizeof(header));memcpy(header.magic,"ALPHAMG1",8);header.version=$output_version;header.header_bytes=sizeof(header);header.record_bytes=sizeof(output_record);header.method_count=expected_method_count;header.generic_method_count=generic_count;header.generic_argument_count=argument_count;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;header.candidate_method_index=expected_candidate_method;memcpy(header.executable,executable_sha256,64);memcpy(header.identity,identity_sha256,64);memcpy(header.methods,method_sha256,64);memcpy(header.references,reference_sha256,64);memcpy(header.semantics,semantics_sha256,64);memcpy(header.members,member_sha256,64);FILE*out=_wfopen(output_path,L"wb");if(!out)return 0;int ok=fwrite(&header,1,sizeof(header),out)==sizeof(header)&&fwrite(records,sizeof(*records),expected_method_count,out)==expected_method_count&&fwrite(arguments,8u,argument_count,out)==argument_count;if(fclose(out))ok=0;if(!ok)_wremove(output_path);return ok;}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char executable[65],identity[65],method[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(executable)||strcmp(executable,executable_sha256)||!sha256_file(identity_path,identity)||strcmp(identity,identity_sha256)||!sha256_file(method_path,method)||strcmp(method,method_sha256)){failure_kind=200u;write_status("identity_mismatch",0);return 0;}SIZE_T identity_bytes=0,method_bytes=0;if(!read_file(identity_path,&identity_data,&identity_bytes)||!read_file(method_path,&method_data,&method_bytes)||identity_bytes<sizeof(identity_header)+expected_type_count*sizeof(identity_record)||method_bytes<sizeof(method_header)+expected_method_count*sizeof(method_record)){failure_kind=201u;write_status("input_unavailable",0);return 0;}identity_header*ih=(identity_header*)identity_data;method_header*mh=(method_header*)method_data;if(memcmp(ih->magic,"ALPHATI1",8)||ih->version!=1u||ih->type_count!=expected_type_count||ih->image_base!=expected_image_base||ih->image_bytes!=expected_image_bytes||memcmp(mh->magic,"ALPHADM1",8)||mh->version!=1u||mh->method_count!=expected_method_count||mh->image_base!=expected_image_base||mh->image_bytes!=expected_image_bytes||mh->handle_qword!=handle_qword){failure_kind=202u;write_status("input_invalid",0);return 0;}types=(identity_record*)(identity_data+sizeof(*ih));methods=(method_record*)(method_data+sizeof(*mh));records=calloc((SIZE_T)expected_method_count,sizeof(*records));if(!records){failure_kind=203u;write_status("allocation_failed",0);return 0;}if(!dispatch()||completed_count!=expected_method_count||verified_count!=expected_method_count||!generic_count){if(!failure_kind)failure_kind=204u;write_status("capture_failed",0);return 0;}int ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def _source(
    *, binding: dict[str, Any], output_path: Path, status_path: Path,
) -> str:
    candidate = binding["candidate"]
    return _COLLECTOR.substitute(
        identity_header_bytes=_IDENTITY_HEADER.size,
        identity_record_bytes=_IDENTITY_RECORD.size,
        method_header_bytes=RUNTIME_METHOD_DETAIL_HEADER.size,
        method_record_bytes=RUNTIME_METHOD_DETAIL_METHOD.size,
        output_header_bytes=RUNTIME_METHOD_GENERIC_HEADER.size,
        output_record_bytes=RUNTIME_METHOD_GENERIC_RECORD.size,
        output_version=RUNTIME_METHOD_GENERIC_VERSION,
        status_schema=RUNTIME_REFLECTION_METHOD_GENERIC_STATUS_SCHEMA,
        executable_sha256=binding["binary"]["sha256"],
        identity_sha256=binding["type_identity_inventory"]["sha256"],
        method_sha256=binding["method_detail_inventory"]["sha256"],
        reference_sha256=binding["type_reference_inventory"]["sha256"],
        semantics_sha256=binding["semantics"]["sha256"],
        member_sha256=_EMPTY_INPUT_SHA256,
        process_id=binding["process_id"],
        type_count=binding["type_count"],
        method_count=binding["method_count"],
        image_base=binding["image_base"],
        image_bytes=binding["image_bytes"],
        candidate_method=candidate["method_index"],
        handle_qword=binding["handle_qword"],
        embedded_descriptor_offset=binding["embedded_descriptor_offset"],
        array_length_qword=binding["array_length_qword"],
        array_vector_qword=binding["array_vector_qword"],
        runtime_type_class=candidate["runtime_type_class"],
        from_handle_pointer=binding["from_handle"]["pointer"],
        from_handle_metadata=binding["from_handle"]["metadata"],
        generic_arguments_pointer=candidate["pointer"],
        generic_arguments_metadata=candidate["metadata"],
        identity_path=_wide_literal(
            _windows_z_path(Path(binding["type_identity_inventory"]["path"]))
        ),
        method_path=_wide_literal(
            _windows_z_path(Path(binding["method_detail_inventory"]["path"]))
        ),
        output_path=_wide_literal(_windows_z_path(output_path)),
        status_path=_wide_literal(_windows_z_path(status_path)),
    )


def prepare_runtime_reflection_method_generic_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
    output_dir: Path, compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
    )
    output_path = output_dir / "runtime-method-generics.private.bin"
    status_path = output_dir / "runtime-method-generics-status.private.json"
    model_path = output_dir / "runtime-method-generics.private.json"
    plan_path = output_dir / "runtime-method-generics-plan.private.json"
    build_dir = _owner_directory(output_dir / "build-method-generics")
    source_path = build_dir / "runtime-method-generics.c"
    injector_source = build_dir / "runtime-method-generics-injector.c"
    injector_path = build_dir / "alpha-runtime-method-generics-injector.exe"
    for stale in (output_path, status_path, model_path):
        stale.unlink(missing_ok=True)
    _private_text(
        source_path,
        _source(
            binding=binding,
            output_path=output_path,
            status_path=status_path,
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-reflection-method-generics-"
        + file_identity(source_path)["sha256"][:12]
        + f"-{time.time_ns():x}.dll"
    )
    cc = _compiler(compiler)
    _build(
        [
            str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(source_path), "-o",
            str(collector_path), "-lbcrypt",
        ],
        label="runtime reflection method generic collector",
    )
    _build(
        [
            str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(injector_source), "-o",
            str(injector_path),
        ],
        label="runtime reflection method generic injector",
    )
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_REFLECTION_METHOD_GENERIC_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            key: binding[key]
            for key in (
                "semantics", "type_identity_model",
                "type_identity_inventory", "type_identity_plan",
                "type_identity_status", "type_reference_model",
                "type_reference_inventory", "type_graph_status",
                "method_detail_model", "method_detail_inventory",
            )
        },
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "contract": {
            "method_count": binding["method_count"],
            "candidate_method_index_owner_only": binding["candidate"][
                "method_index"
            ],
            "generic_arguments_operation": {
                "pointer_owner_only": binding["candidate"]["pointer"],
                "metadata_owner_only": binding["candidate"]["metadata"],
            },
            "all_methods_reflected": True,
            "two_observations_required": True,
        },
        "policy": {
            "same_process_required": True,
            "reflection_semantic_discovery": True,
            "saved_method_generic_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_REFLECTION_METHOD_GENERIC_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "method_count": binding["method_count"],
    }


def _validate(
    *, plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, int], dict[str, bool]]:
    raw = Path(plan["output_path"]).read_bytes()
    if len(raw) < RUNTIME_METHOD_GENERIC_HEADER.size:
        raise AcquisitionError(
            "runtime reflection method generic output is truncated"
        )
    header = RUNTIME_METHOD_GENERIC_HEADER.unpack_from(raw)
    method_count, generic_count, argument_count = header[5:8]
    records_start = RUNTIME_METHOD_GENERIC_HEADER.size
    arguments_start = (
        records_start + method_count * RUNTIME_METHOD_GENERIC_RECORD.size
    )
    header_valid = (
        header[0] == RUNTIME_METHOD_GENERIC_MAGIC
        and header[1] == RUNTIME_METHOD_GENERIC_VERSION
        and header[2] == RUNTIME_METHOD_GENERIC_HEADER.size
        and header[3] == RUNTIME_METHOD_GENERIC_RECORD.size
        and header[4] == 0
        and method_count == plan["contract"]["method_count"]
        and 0 < generic_count <= method_count
        and argument_count >= generic_count
        and header[8] == plan["target"]["image_base_owner_only"]
        and header[9] == plan["target"]["image_bytes"]
        and header[10]
        == plan["contract"]["candidate_method_index_owner_only"]
        and _digest(header[11], label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[12], label="identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(header[13], label="methods")
        == plan["inputs"]["method_detail_inventory"]["sha256"]
        and _digest(header[14], label="references")
        == plan["inputs"]["type_reference_inventory"]["sha256"]
        and _digest(header[15], label="semantics")
        == plan["inputs"]["semantics"]["sha256"]
        and _digest(header[16], label="unused member input")
        == _EMPTY_INPUT_SHA256
        and arguments_start + argument_count * 8 == len(raw)
    )
    arguments = (
        struct.unpack_from(f"<{argument_count}Q", raw, arguments_start)
        if header_valid and argument_count
        else ()
    )
    rows_valid = header_valid
    cursor = 0
    observed_generic = 0
    for index in range(method_count if header_valid else 0):
        method_index, count, start = RUNTIME_METHOD_GENERIC_RECORD.unpack_from(
            raw,
            records_start + index * RUNTIME_METHOD_GENERIC_RECORD.size,
        )
        values = arguments[start : start + count]
        if (
            method_index != index
            or start != cursor
            or count > 64
            or start + count > argument_count
            or any(not value or value & 7 for value in values)
            or len(set(values)) != count
        ):
            rows_valid = False
            break
        observed_generic += bool(count)
        cursor += count
    rows_valid = (
        rows_valid
        and cursor == argument_count
        and observed_generic == generic_count
    )
    counts = {
        "method_count": method_count,
        "generic_method_count": generic_count,
        "generic_argument_count": argument_count,
        "metadata_usage_method_spec_count": 0,
        "metadata_usage_unique_method_count": 0,
    }
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_REFLECTION_METHOD_GENERIC_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "same_process": status.get("process_id")
        == plan["target"]["process_id"],
        "header_bound": header_valid,
        "all_methods_captured": status.get("completed_method_count")
        == method_count,
        "generic_rows_valid": rows_valid,
        "generic_count_matches": status.get("generic_method_count")
        == generic_count,
        "argument_count_matches": status.get("generic_argument_count")
        == argument_count,
        "second_generic_observation_complete": status.get(
            "second_generic_observation"
        ) is True
        and status.get("second_observation_method_count") == method_count,
        "reflection_generic_arguments_semantically_resolved": status.get(
            "reflection_generic_arguments_semantically_resolved"
        ) is True
        and plan.get("policy", {}).get(
            "reflection_semantic_discovery"
        ) is True,
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        ) is True,
        "saved_method_generic_absent": status.get(
            "saved_method_generic_used"
        ) is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    return counts, checks


def capture_runtime_reflection_method_generic_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
    output_dir: Path, wine: Path, wineprefix: Path,
    compiler: Path | None = None, timeout: float = 1800.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_reflection_method_generic_inventory(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan = read_json(output_dir / "runtime-method-generics-plan.private.json")
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
            "runtime reflection method generic injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-method-generics-injector.private.log",
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
        raise AcquisitionError(
            "runtime reflection method generic injection failed"
        )
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
        raise AcquisitionError(
            "runtime reflection method generic capture timed out"
        )
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime reflection method generic capture failed "
            f"(status={status.get('status')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    counts, checks = _validate(plan=plan, status=status)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime reflection method generic validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    model = {
        "schema": RUNTIME_METHOD_GENERIC_SCHEMA,
        "status": "runtime-validated",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"]
        },
        "inputs": plan["inputs"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "discovery": "semantically-resolved-System.Reflection.MonoMethod.GetGenericArguments",
        "owner_only": True,
    }
    _private_json(Path(plan["model_path"]), model)
    return {
        "schema": RUNTIME_METHOD_GENERIC_SCHEMA,
        "status": "runtime-validated",
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "inventory": model["inventory"],
    }


import hashlib
import json
import os
import struct
from collections import defaultdict
from pathlib import Path

from alpha.p12 import _owner_directory, _private_bytes, _private_json
from alpha.h01 import AcquisitionError
from alpha.p13 import _safe_path, _file_record
from alpha.p37 import _INPUT_KEYS, load_runtime_encoded_vtables, _replay_words
from alpha.p15 import coalesce_ranges
from alpha.c01 import current_runtime_process_binding
from alpha.p14 import RuntimeRangeView, read_current_runtime_ranges, load_runtime_range_observation
from alpha.c01 import MethodDeclaration, InterfaceContract, project_vtable_declarations
from alpha.h02 import file_identity
from alpha import p36 as source


_HEADER = struct.Struct('<8sIIIIQQQQ64s64s')
_SLOT = struct.Struct('<IIBB')
_MAGIC = b'ALPHAVD1'
_SCHEMA = 'alpha.runtime-vtable-declarations/v1'


def _semantic_inputs(inputs, binding):
    def data(key):
        return Path(inputs[key]['path']).read_bytes()
    _, methods, _ = source._method_rows(data('method_detail_inventory'))
    iraw, graw = data('type_identity_inventory'), data('type_graph_inventory')
    identities = [source._IDENTITY_RECORD.unpack_from(iraw, source._IDENTITY_HEADER.size + i * source._IDENTITY_RECORD.size)
                  for i in range(binding['type_count'])]
    graph = [source.RUNTIME_TYPE_GRAPH_RECORD.unpack_from(graw, source.RUNTIME_TYPE_GRAPH_HEADER.size + i * source.RUNTIME_TYPE_GRAPH_RECORD.size)
             for i in range(binding['type_count'])]
    _, references = source._reference_rows(data('type_reference_inventory'))
    lineages = source._definition_lineages(identities, graph, references)
    own_virtual = defaultdict(list)
    for index, row in enumerate(methods):
        if row[8] != 0xFFFF:
            own_virtual[row[0]].append(index)
    contracts = [InterfaceContract(pair[3], pair[2], pair[4], pair[5], tuple(own_virtual[pair[4]])) for pair in binding['pairs']]
    return methods, lineages, contracts


def _serialize_projection(projection, *, identity, inputs, type_count):
    count = len(projection.source_method_indexes)
    if not (count == len(projection.declaration_method_indexes) == len(projection.unimplemented) == len(projection.declaration_roles)):
        raise AcquisitionError('vtable declaration projection arrays differ')
    digest = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    payload = bytearray(_HEADER.pack(_MAGIC, 1, _HEADER.size, _SLOT.size, 0, type_count, count,
        identity['process_id'], identity['creation_filetime'], identity['executable_sha256'].encode(), digest.encode()))
    payload.extend(bytes(count * _SLOT.size))
    for index, row in enumerate(zip(projection.source_method_indexes, projection.declaration_method_indexes,
                                    projection.unimplemented, projection.declaration_roles)):
        _SLOT.pack_into(payload, _HEADER.size + index * _SLOT.size, *row)
    for index, row in enumerate(zip(projection.source_method_indexes, projection.declaration_method_indexes,
                                    projection.unimplemented, projection.declaration_roles)):
        if _SLOT.unpack_from(payload, _HEADER.size + index * _SLOT.size) != row:
            raise AcquisitionError('vtable declaration slot roundtrip differs')
    return payload


def load_runtime_vtable_declarations(*, model_path: Path, inventory_path: Path,
                                    expected_identity: dict, expected_inputs: dict):

    model_path, inventory_path = _safe_path(model_path), _safe_path(inventory_path)
    model_id, inventory_id = _file_record(model_path), _file_record(inventory_path)
    model = json.loads(model_path.read_text(encoding="utf-8"))
    identity = {key: expected_identity[key] for key in
        ('process_id', 'creation_filetime', 'executable_path', 'executable_sha256', 'executable_bytes')}
    inputs = model.get('inputs', {})
    if (model.get('schema') != _SCHEMA or model.get('status') != 'runtime-declarations-validated'
        or model.get('target') != identity or set(inputs) != set(expected_inputs) | {'current_observation'}
        or any(inputs.get(key) != value for key, value in expected_inputs.items())
        or model.get('inventory') != {'path': str(inventory_path), **inventory_id}
        or model.get('slot_declaration_projection_complete') is not True
        or not model.get('checks') or any(value is not True for value in model['checks'].values())):
        raise AcquisitionError('vtable declaration receipt identity/checks differ')
    def verify():
        for key, record in inputs.items():
            path = _safe_path(Path(record['path']))
            if key != 'binary':
                _file_record(path)
                if path.stat().st_mtime_ns // 100 + 116444736000000000 < identity['creation_filetime']:
                    raise AcquisitionError('vtable declaration input predates the process instance')
            if file_identity(path) != record:
                raise AcquisitionError('vtable declaration input identity changed: ' + key)
        if _file_record(model_path) != model_id or _file_record(inventory_path) != inventory_id:
            raise AcquisitionError('vtable declaration artifacts changed during replay')
    verify()
    base_inputs = {key: value for key, value in expected_inputs.items() if key not in
        {'encoded_vtable_model', 'encoded_vtable_inventory'}}
    loaded = load_runtime_encoded_vtables(model_path=Path(expected_inputs['encoded_vtable_model']['path']),
        inventory_path=Path(expected_inputs['encoded_vtable_inventory']['path']),
        expected_identity=expected_identity, expected_inputs=base_inputs)
    methods, lineages, contracts = _semantic_inputs(base_inputs, loaded['binding'])
    observation = load_runtime_range_observation(Path(inputs['current_observation']['path']), expected_identity=identity)
    _replay_words(loaded['contract'], loaded['records'], loaded['words'], observation)
    cmodel = json.loads(Path(inputs['constructed_method_model']['path']).read_text(encoding="utf-8"))
    with Path(inputs['constructed_method_inventory']['path']).open('rb') as current:
        cheader = source.RUNTIME_CONSTRUCTED_METHOD_HEADER.unpack(current.read(source.RUNTIME_CONSTRUCTED_METHOD_HEADER.size))
    qword = cheader[10]
    candidate_count = (source.RUNTIME_CONSTRUCTED_METHOD_RECORD.size - struct.calcsize('<QIIQ')) // 8
    if qword >= candidate_count or qword != cmodel.get('runtime_contract_owner_only', {}).get('method_pointer_qword'):
        raise AcquisitionError('vtable declaration MethodInfo field derivation differs')
    vmodel = json.loads(Path(inputs['vtable_interface_model']['path']).read_text(encoding="utf-8"))
    vstart = vmodel.get('layout_owner_only', {}).get('vtable_start_byte')
    if type(vstart) is not int or vstart < 0:
        raise AcquisitionError('vtable declaration native array field derivation differs')
    native = []
    for row in loaded['records']:
        if row[6]:
            data = observation.read(row[4] + vstart, row[6] * 8)
            if data is None:
                raise AcquisitionError('vtable declaration native executable array is absent')
            native.extend(struct.unpack(f'<{row[6]}Q', data))
    if tuple(native) != tuple(loaded['vtables']['vtable_entries']):
        raise AcquisitionError('vtable declaration native executable arrays differ')
    indexes = {pointer: index for pointer, index, owner in loaded['binding']['metadata_map']}
    pointers = {loaded['words'][row[5] + slot] for row in loaded['records'] if row[2] == 2 for slot in range(row[6])}
    native_methods = {}
    for pointer in pointers:
        data = observation.read(pointer + qword * 8, 8)
        if data is None:
            raise AcquisitionError('vtable declaration MethodInfo code field is absent')
        native_methods[pointer] = (indexes[pointer], int.from_bytes(data, 'little'))
    projection = project_vtable_declarations(records=loaded['records'], words=loaded['words'], native_entries=native,
        methods=[MethodDeclaration(row[0], row[2], row[3], row[5], row[8], bool(row[9] & 1)) for row in methods],
        lineages=lineages, dispatch=vars(loaded['contract'].dispatch), native_methods=native_methods, interface_contracts=contracts)
    payload = _serialize_projection(projection, identity=identity, inputs=inputs, type_count=len(loaded['records']))
    if (hashlib.sha256(payload).hexdigest() != inventory_id['sha256'] or payload != inventory_path.read_bytes()
        or projection.counts != model.get('counts')
        or json.loads(json.dumps(projection.interface_only_contexts)) != model.get('interface_only_contexts_owner_only')):
        raise AcquisitionError('vtable declaration full native-byte/semantic roundtrip differs')
    verify()
    return {'projection': projection, 'encoded': loaded, 'methods': methods, 'lineages': lineages,
            'metadata_indexes': indexes, 'interface_contracts': contracts,
            'model': {'path': str(model_path), **model_id}, 'inventory': {'path': str(inventory_path), **inventory_id}}


def capture_runtime_vtable_declarations(*, binary: Path, output_dir: Path, wine: Path, wineprefix: Path,
    encoded_vtable_model: Path, encoded_vtable_inventory: Path, compiler: Path | None = None,
    timeout: float = 900, **inputs):
    del timeout
    if set(inputs) != _INPUT_KEYS:
        raise AcquisitionError('vtable declaration inputs are incomplete or unexpected')
    binary = _safe_path(binary)
    current = current_runtime_process_binding()
    if current is None or not same_executable_path(current[2], binary):
        raise AcquisitionError('vtable declaration capture requires current process binding')
    output_dir = _owner_directory(_safe_path(output_dir))
    if any(output_dir.iterdir()):
        raise AcquisitionError('vtable declaration output directory is not empty')
    binary_id = file_identity(binary)
    identity = dict(process_id=current[0], creation_filetime=current[1], executable_path=str(binary),
                    executable_sha256=binary_id['sha256'], executable_bytes=binary_id['bytes'])
    expected_inputs = {'binary': binary_id, **{
        'reflection_semantics' if key == 'reflection_semantics_model' else key: file_identity(_safe_path(path)) for key, path in inputs.items()}}
    loaded = load_runtime_encoded_vtables(model_path=encoded_vtable_model, inventory_path=encoded_vtable_inventory,
        expected_identity=identity, expected_inputs=expected_inputs)
    binding = loaded['binding']
    methods, lineages, contracts = _semantic_inputs(expected_inputs, binding)
    craw = Path(expected_inputs['constructed_method_inventory']['path']).read_bytes()
    cheader = source.RUNTIME_CONSTRUCTED_METHOD_HEADER.unpack_from(craw)
    cmodel = json.loads(Path(expected_inputs['constructed_method_model']['path']).read_text(encoding="utf-8"))
    qword = cheader[10]
    if qword >= 8 or qword != cmodel.get('runtime_contract_owner_only', {}).get('method_pointer_qword'):
        raise AcquisitionError('vtable declaration MethodInfo code field is not bound to current derivation')
    vmodel = json.loads(Path(expected_inputs['vtable_interface_model']['path']).read_text(encoding="utf-8"))
    vstart = vmodel.get('layout_owner_only', {}).get('vtable_start_byte')
    if type(vstart) is not int or vstart < 0:
        raise AcquisitionError('vtable declaration native executable array offset is absent')
    records, words, old = loaded['records'], loaded['words'], loaded['observation']
    pointers = {words[row[5] + slot] for row in records if row[2] == 2 for slot in range(row[6])}


    ranges = list(zip(old.starts, (len(payload) for payload in old.payloads)))
    ranges.extend((pointer + qword * 8, 8) for pointer in pointers)
    ranges.extend((row[4] + vstart, row[6] * 8) for row in records if row[6])
    ranges = coalesce_ranges(ranges, max_gap=256)
    plan_inputs = {**expected_inputs, 'encoded_vtable_model': loaded['model'], 'encoded_vtable_inventory': loaded['inventory']}
    _private_json(output_dir / 'runtime-vtable-declaration-plan.private.json', {
        'schema': 'alpha.runtime-vtable-declaration-plan/v1', 'identity': identity, 'inputs': plan_inputs,
        'method_code_qword_owner_only': qword, 'native_vtable_start_owner_only': vstart,
        'range_count': len(ranges), 'byte_count': sum(size for address, size in ranges),
        'metadata_complete': False})
    observed = read_current_runtime_ranges(binary=binary, ranges=ranges, output_dir=output_dir / 'observation',
        wine=wine, wineprefix=wineprefix, compiler=compiler)
    view = RuntimeRangeView(observed)
    _replay_words(loaded['contract'], records, words, view)
    native = []
    for row in records:
        if row[6]:
            data = view.read(row[4] + vstart, row[6] * 8)
            if data is None:
                raise AcquisitionError('vtable declaration executable array is absent')
            native.extend(struct.unpack(f'<{row[6]}Q', data))
    if tuple(native) != tuple(loaded['vtables']['vtable_entries']):
        raise AcquisitionError('vtable executable arrays changed since source capture')
    indexes = {pointer: index for pointer, index, owner in binding['metadata_map']}
    native_methods = {}
    for pointer in pointers:
        data = view.read(pointer + qword * 8, 8)
        if data is None:
            raise AcquisitionError('vtable declaration MethodInfo code field is absent')
        native_methods[pointer] = (indexes[pointer], int.from_bytes(data, 'little'))
    projection = project_vtable_declarations(records=records, words=words, native_entries=native,
        methods=[MethodDeclaration(row[0], row[2], row[3], row[5], row[8], bool(row[9] & 1)) for row in methods],
        lineages=lineages, dispatch=vars(loaded['contract'].dispatch), native_methods=native_methods,
        interface_contracts=contracts)
    plan_inputs['current_observation'] = file_identity(output_dir / 'observation/runtime-ranges.private.json')
    for key, record in plan_inputs.items():
        path = _safe_path(Path(record['path']))
        if key != 'binary':
            _file_record(path)
        if file_identity(path) != record:
            raise AcquisitionError('vtable declaration input changed: ' + key)
    payload = _serialize_projection(projection, identity=identity, inputs=plan_inputs, type_count=len(records))
    path = output_dir / 'runtime-vtable-declarations.private.bin'
    with os.fdopen(os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600), 'wb') as output:
        output.write(payload)
        output.flush()
        os.fsync(output.fileno())
    if path.read_bytes() != payload:
        raise AcquisitionError('vtable declaration output byte roundtrip differs')
    model = {'schema': _SCHEMA, 'status': 'runtime-declarations-validated', 'target': identity,
        'inputs': plan_inputs, 'inventory': file_identity(path), 'counts': projection.counts,
        'interface_only_contexts_owner_only': projection.interface_only_contexts,
        'checks': {'current_code_rederived': True, 'encoded_source_native_byte_replay_exact': True,
            'all_current_native_executable_arrays_exact': True, 'all_pointer_source_code_fields_observed': True,
            'all_declarations_proven': True, 'unimplemented_separate_from_runtime_fallback': True,
            'no_synthetic_class_methods': True, 'byte_and_slot_roundtrip_exact': True,
            'source_identities_unchanged': True},
        'metadata_complete': False, 'slot_declaration_projection_complete': True,
        'pending_domains': ['MethodSpec/GenericInst context closure', 'standard metadata vtable encoding/reconstruction']}
    _private_json(output_dir / 'runtime-vtable-declarations.private.json', model)
    return model


import struct
from collections import Counter
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError
from alpha.p37 import validated_proto_receipt as _validated_native_receipt
from alpha.p31 import load_runtime_direct_interfaces
from alpha.p22 import METHOD_DETAIL_CONSTRUCTOR
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER
from alpha.p33 import _MetadataUsageTypeRenderer, _RuntimeOutput, _text
from alpha.p38 import RUNTIME_PROTO_FIELD_TYPE_HEADER, RUNTIME_PROTO_FIELD_TYPE_MAGIC, RUNTIME_PROTO_FIELD_TYPE_RECORD, RUNTIME_PROTO_FIELD_TYPE_SCHEMA, RUNTIME_PROTO_FIELD_TYPE_VERSION
from alpha.c04 import MappedPE
from alpha.p20 import load_runtime_metadata_usage_value_inventory
from alpha.h02 import file_identity, read_json


RUNTIME_PROTO_ANALYSIS_SCHEMA = "alpha.runtime-proto-analysis/v9"


_DETAIL_DECODER: Any = None
from functools import lru_cache


@lru_cache(maxsize=32)
def _linear_parser_instructions(code: bytes, decoder: Any) -> tuple[Any, ...]:
    return tuple(decoder.disasm(code, 0))


@lru_cache(maxsize=16384)
def _instruction_register_access(instruction: Any) -> tuple[tuple[int, ...], tuple[int, ...]]:
    reads, writes = instruction.regs_access()
    return tuple(reads), tuple(writes)


@lru_cache(maxsize=16384)
def _instruction_written_registers(instruction: Any) -> frozenset[int | None]:
    _, writes = _instruction_register_access(instruction)
    return frozenset(_native_register_index(instruction.reg_name(register)) for register in writes)


def _shared_detail_decoder() -> Any:
    global _DETAIL_DECODER
    if _DETAIL_DECODER is None:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64

        _DETAIL_DECODER = Cs(CS_ARCH_X86, CS_MODE_64)
        _DETAIL_DECODER.detail = True
    return _DETAIL_DECODER


def _instruction_starts(code: bytes) -> set[int]:
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64


    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    return {address for address, size, mnemonic, operands in decoder.disasm_lite(code, 0)}


def _reachable_instruction_map(
    code: bytes, *, roots: list[int] | None = None, decoder: Any | None = None,
) -> dict[int, Any]:
    engine = _shared_detail_decoder() if decoder is None else decoder
    if engine is _shared_detail_decoder():
        return dict(_cached_reachable_instructions(code, tuple(roots or ()), engine))
    return _reachable_instruction_map_uncached(code, roots=roots, decoder=engine)


@lru_cache(maxsize=32)
def _cached_reachable_instructions(code: bytes, roots: tuple[int, ...], decoder: Any):
    return tuple(_reachable_instruction_map_uncached(code, roots=list(roots), decoder=decoder).items())


def _reachable_instruction_map_uncached(
    code: bytes,
    *,
    roots: list[int] | None = None,
    decoder: Any | None = None,
) -> dict[int, Any]:
    from capstone import CS_GRP_CALL, CS_GRP_JUMP
    from capstone.x86_const import X86_OP_IMM

    if decoder is None:
        decoder = _shared_detail_decoder()
    linear: dict[int, Any] = {}
    instructions = (_linear_parser_instructions(code, decoder)
                    if decoder is _shared_detail_decoder() else decoder.disasm(code, 0))
    for instruction in instructions:
        linear[int(instruction.address)] = instruction
    pending = [0, *(roots or [])]
    reached: dict[int, Any] = {}
    while pending:
        offset = pending.pop()
        if offset in reached or not 0 <= offset < len(code):
            continue
        instruction = linear.get(offset)
        if instruction is None:
            instruction = next(
                decoder.disasm(code[offset:], offset, count=1), None
            )
        if instruction is None or int(instruction.address) != offset:
            continue
        reached[offset] = instruction
        next_offset = offset + int(instruction.size)
        mnemonic = instruction.mnemonic.lower()
        if mnemonic in {
            "ret", "retf", "iret", "iretq", "sysret", "ud2", "hlt", "int3"
        }:
            continue
        if instruction.group(CS_GRP_CALL):
            pending.append(next_offset)
            continue
        if instruction.group(CS_GRP_JUMP):
            if (
                instruction.operands
                and instruction.operands[0].type == X86_OP_IMM
            ):
                pending.append(int(instruction.operands[0].imm))
            if mnemonic not in {"jmp", "ljmp"}:
                pending.append(next_offset)
            continue
        pending.append(next_offset)
    return reached


def _tag_cases(code: bytes) -> list[dict[str, Any]]:

    cases: list[dict[str, Any]] = []
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64, CS_GRP_CALL, CS_GRP_JUMP
    from capstone.x86_const import (
        X86_INS_ADD,
        X86_INS_CMP,
        X86_INS_JMP,
        X86_INS_LEA,
        X86_INS_MOVSXD,
        X86_INS_ROL,
        X86_INS_ROR,
        X86_OP_IMM,
        X86_OP_MEM,
        X86_OP_REG,
    )

    decoder = _shared_detail_decoder()
    instructions = list(_linear_parser_instructions(code, decoder))

    initially_reachable = _reachable_instruction_map(code, decoder=decoder)
    instruction_starts = set(initially_reachable)

    def branch(offset: int) -> tuple[int | None, str | None]:
        instruction = next(
            decoder.disasm(code[offset:], offset, count=1), None
        ) if 0 <= offset < len(code) else None
        if instruction is None or not instruction.operands:
            return None, None
        mnemonic = instruction.mnemonic.lower()
        target = int(instruction.operands[0].imm) if instruction.operands[0].type == X86_OP_IMM else -1
        if mnemonic in {"je", "jz"}:
            case_start = target
        elif mnemonic in {"jne", "jnz"}:
            case_start = instruction.address + instruction.size
        else:
            return None, None
        if case_start not in instruction_starts or not 0 <= case_start < len(code):
            return None, None
        return case_start, f"{mnemonic}-capstone"

    def range_jump(offset: int) -> bool:
        instruction = next(
            decoder.disasm(code[offset:], offset, count=1), None
        ) if 0 <= offset < len(code) else None
        return bool(
            instruction is not None
            and instruction.mnemonic.lower()
            in {"ja", "jae", "jb", "jbe"}
        )

    def add(offset: int, raw_tag: int, source: str, size: int) -> None:
        if offset not in instruction_starts:
            return
        wire = raw_tag & 7
        field = raw_tag >> 3


        if raw_tag <= 0 or not 0 < field <= 0x1FFFFFFF or wire not in range(8):
            return
        case_start, branch_kind = branch(offset + size)
        if case_start is None:
            return
        cases.append(
            {
                "compare_offset": offset,
                "raw_tag": raw_tag,
                "field_number": field,
                "wire": wire,
                "case_start": case_start,
                "branch": branch_kind,
                "source": source,
                "wire_evidence": "exact-tag",
            }
        )


    def register_index(instruction: Any, register: int) -> int | None:
        return _native_register_index(instruction.reg_name(register))

    def normalized_field_number(rotate: Any) -> bool:
        if rotate.id not in {X86_INS_ROR, X86_INS_ROL} or len(rotate.operands) != 2:
            return False
        destination, amount = rotate.operands
        if destination.type != X86_OP_REG or destination.size != 4 or amount.type != X86_OP_IMM:
            return False
        immediate = int(amount.imm) & 31


        return (rotate.id == X86_INS_ROR and immediate == 3) or (
            rotate.id == X86_INS_ROL and immediate == 29
        )

    normalized_comparisons: set[int] = set()

    def jump_table_cases(anchor: Any, *, normalized: bool) -> list[dict[str, Any]]:
        selector = register_index(anchor, anchor.operands[0].reg)
        if selector is None:
            return []
        anchor_position = instructions.index(anchor)
        comparison: Any | None = None
        maximum: int | None = None
        guard: Any | None = None


        candidates = (
            instructions[anchor_position + 1 : anchor_position + 12]
            if normalized else [anchor]
        )
        for candidate in candidates:
            if candidate.id == X86_INS_CMP and len(candidate.operands) == 2:
                left, right = candidate.operands
                if (
                    left.type == X86_OP_REG
                    and register_index(candidate, left.reg) == selector
                    and left.size == 4
                    and right.type == X86_OP_IMM
                    and 0 < int(right.imm) <= 0x1FFFFFFF
                ):
                    position = instructions.index(candidate)
                    possible_guard = (
                        instructions[position + 1]
                        if position + 1 < len(instructions)
                        else None
                    )
                    if (
                        possible_guard is not None
                        and possible_guard.mnemonic.lower() in {"ja", "jae"}
                    ):
                        comparison = candidate
                        maximum = int(right.imm) & 0xFFFFFFFF
                        guard = possible_guard
                    break
            if candidate.group(CS_GRP_CALL) or candidate.group(CS_GRP_JUMP):
                break
            try:
                _reads, writes = candidate.regs_access()
            except Exception:
                return []
            if any(register_index(candidate, value) == selector for value in writes):
                return []
        if comparison is None or guard is None or maximum is None:
            return []
        guard_target = (
            int(guard.operands[0].imm)
            if guard.operands and guard.operands[0].type == X86_OP_IMM
            else -1
        )
        if (
            guard_target < 0
            or guard_target >= len(code)
            or not next(
                decoder.disasm(
                    code[guard_target:],
                    guard_target,
                    count=1,
                ),
                None,
            )
        ):
            return []
        max_key = maximum - 1 if guard.mnemonic.lower() == "jae" else maximum
        if not 0 < max_key <= 0x1FFFFFFF or max_key > len(code) // 4:
            return []

        resolved: list[tuple[Any, int, int]] = []
        for jump_position, jump in enumerate(instructions):
            if (
                jump.id != X86_INS_JMP
                or len(jump.operands) != 1
                or jump.operands[0].type != X86_OP_REG
            ):
                continue
            target_register = register_index(jump, jump.operands[0].reg)
            if target_register is None:
                continue


            for add_position in range(max(0, jump_position - 3), jump_position):
                add = instructions[add_position]
                if add.id != X86_INS_ADD or len(add.operands) != 2:
                    continue
                destination, base_operand = add.operands
                if (
                    destination.type != X86_OP_REG
                    or base_operand.type != X86_OP_REG
                    or register_index(add, destination.reg) != target_register
                ):
                    continue
                base_register = register_index(add, base_operand.reg)
                if base_register is None:
                    continue
                for load_position in range(max(0, add_position - 3), add_position):
                    load = instructions[load_position]
                    if (
                        load.id != X86_INS_MOVSXD
                        or len(load.operands) != 2
                        or load.operands[0].type != X86_OP_REG
                        or load.operands[1].type != X86_OP_MEM
                        or register_index(load, load.operands[0].reg) != target_register
                    ):
                        continue
                    memory = load.operands[1].mem
                    if (
                        register_index(load, memory.base) != base_register
                        or register_index(load, memory.index) != selector
                        or int(memory.scale) != 4
                    ):
                        continue
                    table_bases = []
                    for lea in instructions[max(0, load_position - 128) : load_position]:
                        if (
                            lea.id != X86_INS_LEA
                            or len(lea.operands) != 2
                            or lea.operands[0].type != X86_OP_REG
                            or lea.operands[1].type != X86_OP_MEM
                            or register_index(lea, lea.operands[0].reg) != base_register
                            or lea.reg_name(lea.operands[1].mem.base).lower() != "rip"
                            or _native_register_index(
                                lea.reg_name(lea.operands[1].mem.index)
                            ) is not None
                        ):
                            continue
                        table_bases.append(
                            int(lea.address)
                            + int(lea.size)
                            + int(lea.operands[1].mem.disp)
                        )
                    if len(set(table_bases)) != 1:
                        continue
                    table = table_bases[0] + int(memory.disp)
                    table_end = table + (max_key + 1) * 4
                    if table < 0 or table_end > len(code):
                        continue
                    resolved.append((jump, table, max_key))


        unique_tables = {
            (int(jump.address), table, count)
            for jump, table, count in resolved
        }
        if len(unique_tables) != 1:
            return []
        jump_address, table, max_key = next(iter(unique_tables))
        jump_position = next(
            index for index, item in enumerate(instructions)
            if int(item.address) == jump_address
        )
        table_loads = [
            instruction
            for instruction in instructions[max(0, jump_position - 6) : jump_position]
            if instruction.id == X86_INS_MOVSXD
            and len(instruction.operands) == 2
            and instruction.operands[1].type == X86_OP_MEM
            and register_index(instruction, instruction.operands[1].mem.index) == selector
        ]
        if len(table_loads) != 1:
            return []
        first_case_offset = int(table_loads[0].address) + int(table_loads[0].size)
        table_end = table + (max_key + 1) * 4
        zero_entry = table + int.from_bytes(
            code[table : table + 4], "little", signed=True
        )
        default_targets = {guard_target, zero_entry}
        output: list[dict[str, Any]] = []
        for key in range(1, max_key + 1):
            entry = table + key * 4
            case_start = table + int.from_bytes(
                code[entry : entry + 4], "little", signed=True
            )
            if case_start in default_targets:
                continue
            field = key if normalized else key >> 3
            wire = 0 if normalized else key & 7
            if not 0 < field <= 0x1FFFFFFF:
                continue
            if (
                not first_case_offset <= case_start < len(code)
                or table <= case_start < table_end
                or not next(
                    decoder.disasm(code[case_start:], case_start, count=1), None
                )
            ):


                return []
            output.append(
                {
                    "compare_offset": int(anchor.address),
                    "raw_tag": field << 3 if normalized else key,
                    "field_number": field,
                    "wire": wire,
                    "case_start": case_start,
                    "branch": "normalized-field-number-jumptable" if normalized else "raw-tag-jumptable",
                    "source": "normalized-field-number-jumptable" if normalized else "raw-tag-jumptable",
                    "wire_evidence": "field-number-only" if normalized else "exact-tag",
                }
            )
        if normalized and output:
            normalized_comparisons.add(int(comparison.address))
        return output

    jump_table_case_starts: list[int] = []
    for instruction in instructions:
        if (
            instruction.address in initially_reachable
            and normalized_field_number(instruction)
        ):
            discovered = jump_table_cases(instruction, normalized=True)
            cases.extend(discovered)
            jump_table_case_starts.extend(
                int(item["case_start"])
                for item in discovered
                if item.get("case_start") is not None
            )
        elif (
            instruction.address in initially_reachable
            and instruction.id == X86_INS_CMP
            and len(instruction.operands) == 2
            and instruction.operands[0].type == X86_OP_REG
            and instruction.operands[0].size == 4
            and instruction.operands[1].type == X86_OP_IMM
            and instruction.address not in normalized_comparisons
        ):
            discovered = jump_table_cases(instruction, normalized=False)
            cases.extend(discovered)
            jump_table_case_starts.extend(
                int(item["case_start"])
                for item in discovered
                if item.get("case_start") is not None
            )
    reachable_code = _reachable_instruction_map(
        code, roots=jump_table_case_starts, decoder=decoder
    )
    instruction_starts = set(reachable_code)

    for instruction in reachable_code.values():
        if instruction.id != X86_INS_CMP or len(instruction.operands) != 2:
            continue
        left, right = instruction.operands
        if (
            left.type != X86_OP_REG
            or _native_register_index(instruction.reg_name(left.reg)) is None
            or left.size not in (4, 8)
            or right.type != X86_OP_IMM
        ):
            continue
        next_offset = instruction.address + instruction.size
        if range_jump(next_offset):
            continue
        raw_tag = int(right.imm) & 0xFFFFFFFF
        add(
            instruction.address,
            raw_tag,
            f"capstone-cmp-{instruction.reg_name(left.reg).lower()}-imm{right.size * 8}",
            instruction.size,
        )
    unique: dict[tuple[int, int, int], dict[str, Any]] = {}
    for item in cases:
        unique[
            (
                int(item["field_number"]),
                int(item["wire"]),
                int(item.get("case_start") or -1),
            )
        ] = item
    return sorted(
        unique.values(),
        key=lambda item: (
            int(item["field_number"]),
            int(item["wire"]),
            int(item.get("case_start") or -1),
        ),
    )


def _this_register(code: bytes) -> int:
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64, CS_GRP_CALL, CS_GRP_JUMP
    from capstone.x86_const import X86_INS_LEA, X86_INS_MOV, X86_OP_MEM, X86_OP_REG

    decoder = _shared_detail_decoder()
    aliases = {1}
    preserved: dict[int, int] = {}
    preserved_registers = {3, 5, 6, 7, 12, 13, 14, 15}
    prologue_limit = min(len(code), 96)


    prologue_bytes = code[:min(len(code), prologue_limit + 15)]
    prologue = list(decoder.disasm(prologue_bytes, 0))
    if not prologue:
        raise AcquisitionError("runtime protocol method has no decodable prologue")
    cursor = 0
    stopped_at_control_flow = False
    for instruction in prologue:
        if int(instruction.address) != cursor:
            raise AcquisitionError(
                "runtime protocol method prologue has an undecoded gap at "
                + f"0x{cursor:x}"
            )
        cursor += int(instruction.size)


        if instruction.group(CS_GRP_CALL) or instruction.mnemonic.lower() in {
            "jmp", "ljmp"
        }:
            stopped_at_control_flow = True
            break
        operands = instruction.operands
        copied_from_alias: int | None = None
        destination: int | None = None
        if len(operands) >= 2 and operands[0].type == X86_OP_REG:
            destination = _native_register_index(
                instruction.reg_name(operands[0].reg)
            )
            if (
                instruction.id == X86_INS_MOV
                and operands[1].type == X86_OP_REG
                and operands[0].size == operands[1].size == 8
            ):
                source = _native_register_index(
                    instruction.reg_name(operands[1].reg)
                )
                if source in aliases:
                    copied_from_alias = source
            elif (
                instruction.id == X86_INS_LEA
                and operands[1].type == X86_OP_MEM
                and operands[0].size == 8
            ):
                memory = operands[1].mem
                source = _native_register_index(instruction.reg_name(memory.base))
                index = _native_register_index(instruction.reg_name(memory.index))
                if source in aliases and index is None and memory.disp == 0:
                    copied_from_alias = source
        if destination is not None:
            if copied_from_alias is not None:
                aliases.add(destination)
                if destination in preserved_registers:
                    preserved[destination] = int(instruction.address)
                if cursor >= prologue_limit:
                    break
                continue
            try:
                _reads, writes = instruction.regs_access()
            except Exception:
                writes = ()
            for register in writes:
                written = _native_register_index(instruction.reg_name(register))
                if written is not None:
                    aliases.discard(written)
                    preserved.pop(written, None)
        if cursor >= prologue_limit:
            break
    if not stopped_at_control_flow and cursor < prologue_limit:
        raise AcquisitionError(
            "runtime protocol method prologue ends inside an undecoded instruction "
            + f"at 0x{cursor:x}"
        )
    candidates = sorted(
        preserved_register
        for preserved_register in preserved
        if preserved_register in aliases
    )
    if len(candidates) == 1:
        return candidates[0]
    if len(candidates) > 1:
        access_counts = {
            register: len(
                _memory_accesses(code, 0, len(code), base_register=register)
            )
            for register in candidates
        }
        maximum = max(access_counts.values())
        strongest = [
            register for register, count in access_counts.items()
            if count == maximum
        ]
        if maximum and len(strongest) == 1:
            return strongest[0]
        raise AcquisitionError(
            "runtime protocol method instance register is ambiguous: "
            + repr(access_counts)
        )
    if 1 in aliases:
        return 1
    raise AcquisitionError(
        "runtime protocol method instance argument is not structurally resolved"
    )


def _early_this_aliases(code: bytes) -> set[int]:
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64, CS_GRP_CALL, CS_GRP_JUMP
    from capstone.x86_const import X86_INS_LEA, X86_INS_MOV, X86_OP_MEM, X86_OP_REG

    decoder = _shared_detail_decoder()
    aliases: set[int] = set()
    for instruction in decoder.disasm(code[:min(len(code), 111)], 0):
        if int(instruction.address) >= 96:
            break
        if instruction.group(CS_GRP_CALL) or instruction.group(CS_GRP_JUMP):
            break
        operands = instruction.operands
        if len(operands) != 2 or operands[0].type != X86_OP_REG or operands[0].size != 8:
            continue
        destination = _native_register_index(instruction.reg_name(operands[0].reg))
        if destination not in {3, 5, 6, 7, 12, 13, 14, 15}:
            continue
        copied = (
            instruction.id == X86_INS_MOV
            and operands[1].type == X86_OP_REG
            and operands[1].size == 8
            and _native_register_index(instruction.reg_name(operands[1].reg)) == 1
        )
        addressed = (
            instruction.id == X86_INS_LEA
            and operands[1].type == X86_OP_MEM
            and operands[1].size == 8
            and _native_register_index(instruction.reg_name(operands[1].mem.base)) == 1
            and _native_register_index(instruction.reg_name(operands[1].mem.index)) is None
            and int(operands[1].mem.disp) == 0
        )
        if copied or addressed:
            aliases.add(destination)
    return aliases


def _direct_tag_writes(code: bytes) -> list[dict[str, int]]:
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64, CS_GRP_CALL, CS_GRP_JUMP
    from capstone.x86_const import X86_INS_MOV, X86_OP_IMM, X86_OP_MEM

    decoder = _shared_detail_decoder()
    reachable = _reachable_instruction_map(code, decoder=decoder)
    byte_writes: list[tuple[int, str, int, int]] = []
    indexed_writes: list[tuple[int, tuple[str, str, int, int], int, int]] = []
    for instruction in reachable.values():
        if instruction.id != X86_INS_MOV or len(instruction.operands) != 2:
            continue
        destination, source = instruction.operands
        if (
            destination.type != X86_OP_MEM
            or destination.size != 1
            or source.type != X86_OP_IMM
        ):
            continue
        base = (instruction.reg_name(destination.mem.base) or "").lower()
        index_register = (instruction.reg_name(destination.mem.index) or "").lower()
        if (
            base not in {"rsp", "rbp", "rip"}
            and index_register
            and destination.mem.scale == 1
            and 0 <= destination.mem.disp <= 4096
        ):
            indexed_writes.append((
                int(instruction.address),
                (base, index_register, int(destination.mem.scale), int(destination.mem.disp)),
                int(source.imm) & 0xFF,
                int(instruction.size),
            ))
        if base not in {"rsp", "rbp"}:
            continue


        byte_writes.append((
            int(instruction.address),
            instruction.reg_name(destination.mem.base).lower(),
            int(destination.mem.disp),
            int(source.imm) & 0xFF,
        ))
    byte_writes.sort()

    def straight_line_between(left: int, right: int) -> bool:
        return not any(
            left < int(instruction.address) < right
            and (
                instruction.group(CS_GRP_CALL)
                or instruction.group(CS_GRP_JUMP)
                or instruction.mnemonic.lower()
                in {"ret", "retf", "iret", "iretq", "sysret", "ud2", "hlt", "int3"}
            )
            for instruction in reachable.values()
        )

    output: list[dict[str, int]] = []
    index = 0
    while index < len(byte_writes):
        start, stack_base, stack_offset, first = byte_writes[index]
        value = 0
        shift = 0
        end = start
        current = index
        complete = False
        while current < len(byte_writes) and current < index + 5:
            offset, current_base, current_stack_offset, byte = byte_writes[current]
            if current > index:
                if (
                    offset - end > 160
                    or current_base != stack_base
                    or current_stack_offset != stack_offset + current - index
                    or not straight_line_between(end, offset)
                ):
                    break
            value |= (byte & 0x7F) << shift
            shift += 7
            end = offset
            if not byte & 0x80:
                complete = True
                break
            current += 1
        wire = value & 7
        field = value >> 3
        if complete and 0 < field <= 0x1FFFFFFF and wire in range(8):
            output.append(
                {
                    "field_number": field,
                    "wire": wire,
                    "raw_tag": value,
                    "start": start,
                    "end": end + 5,
                    "byte_count": current - index + 1,
                }
            )
            index = current + 1
        elif complete:


            index = current + 1
        else:
            index += 1
    unique: dict[tuple[int, int, int], dict[str, int]] = {}


    indexed_writes.sort()
    for position, (start, destination, first, size) in enumerate(indexed_writes):
        if position and indexed_writes[position - 1][1] == destination:
            previous = indexed_writes[position - 1]
            if previous[2] & 0x80 and start - previous[0] <= 160:
                continue
        value = 0
        shift = 0
        end = start + size
        complete = False
        for following in indexed_writes[position:position + 5]:
            offset, current_destination, byte, width = following
            if current_destination != destination or offset - end > 160:
                break
            value |= (byte & 0x7F) << shift
            shift += 7
            end = offset + width
            if not byte & 0x80:
                complete = True
                break
        field, wire = value >> 3, value & 7
        if complete and 0 < field <= 0x1FFFFFFF and wire in range(8):
            output.append({
                "field_number": field,
                "wire": wire,
                "raw_tag": value,
                "start": start,
                "end": end,
                "byte_count": shift // 7,
            })
    for item in output:
        unique[(item["field_number"], item["wire"], item["start"])] = item
    return sorted(unique.values(), key=lambda item: item["start"])


def _reject_unsupported_wire_tags(
    *, message_name: str, rows: list[dict[str, Any]], source: str,
) -> None:
    unsupported = [
        {
            "field_number": int(row["field_number"]),
            "wire": int(row["wire"]),
            "raw_tag": int(row.get("raw_tag", (int(row["field_number"]) << 3) | int(row["wire"]))),
        }
        for row in rows
        if int(row.get("wire", -1)) in (3, 4, 6, 7)
    ]
    if unsupported:
        group_rows = [row for row in unsupported if row["wire"] in (3, 4)]
        reserved_rows = [row for row in unsupported if row["wire"] in (6, 7)]
        reasons = []
        if group_rows:
            reasons.append("legacy group wire types 3/4")
        if reserved_rows:
            reasons.append("reserved or unsupported wire types 6/7")
        raise AcquisitionError(
            "unsupported protobuf wire tag evidence ("
            + " and ".join(reasons)
            + "); refusing to omit runtime tags from "
            + f"{source} for {message_name}: "
            + repr(unsupported)
        )


def _formatter_tag_slots(code: bytes) -> dict[int, int]:

    from alpha.p01 import allocation_codec_slots
    output = allocation_codec_slots(code)
    instruction_starts = set(_reachable_instruction_map(code))


    for cursor in range(0, max(0, len(code) - 10)):
        if cursor not in instruction_starts or code[cursor] != 0xB9:
            continue
        tag = int.from_bytes(code[cursor + 1 : cursor + 5], "little")
        if not 0 < tag >> 3 <= 0x1FFFFFFF or tag & 7 not in range(8):
            continue
        call = cursor + 5
        while (
            call + 3 <= len(code)
            and 0x40 <= code[call] <= 0x4F
            and code[call + 1] == 0x89
            and code[call + 2] >> 6 == 3
        ):
            call += 3
        if call not in instruction_starts or call + 5 > len(code) or code[call] != 0xE8:
            continue
        call_end = call + 5


        load = call_end
        load_rex = code[load] if load < len(code) else 0
        if (
            load + 14 > len(code)
            or not 0x48 <= load_rex <= 0x4F
            or code[load + 1] != 0x8B
            or code[load + 2] >> 6 != 0
            or code[load + 2] & 7 != 5
        ):
            continue
        base_register = (code[load + 2] >> 3 & 7) | (
            8 if load_rex & 4 else 0
        )
        for probe in range(load + 7, min(len(code), load + 24) - 6):
                if probe not in instruction_starts:
                    continue
                rex = code[probe]
                if not 0x48 <= rex <= 0x4F or code[probe + 1] != 0x89:
                    continue
                modrm = code[probe + 2]
                store_base = (modrm & 7) | (8 if rex & 1 else 0)


                if (
                    modrm >> 6 != 2
                    or modrm >> 3 & 7 != 0
                    or rex & 4
                    or store_base != base_register
                ):
                    continue
                slot = int.from_bytes(code[probe + 3 : probe + 7], "little")
                if slot < 0x1000:
                    continue
                previous = output.get(slot)
                if previous is not None and previous != tag:
                    raise AcquisitionError(
                        "runtime protocol formatter slot has conflicting tags"
                    )
                output[slot] = tag
                break
    unsupported = [
        {"slot": slot, "raw_tag": tag, "field_number": tag >> 3, "wire": tag & 7}
        for slot, tag in output.items()
        if tag & 7 in (3, 4, 6, 7)
    ]
    if unsupported:
        raise AcquisitionError(
            "runtime protocol formatter exposes unsupported protobuf wire tags: "
            + repr(unsupported)
        )
    return output


def _static_slot_loads(code: bytes) -> list[tuple[int, int]]:
    output: list[tuple[int, int]] = []
    for cursor in range(0, max(0, len(code) - 7)):
        rex = code[cursor]
        if not 0x48 <= rex <= 0x4F or code[cursor + 1] != 0x8B:
            continue
        modrm = code[cursor + 2]
        if modrm >> 6 != 2 or modrm & 7 != 0:
            continue
        output.append(
            (
                cursor,
                int.from_bytes(code[cursor + 3 : cursor + 7], "little"),
            )
        )
    return output


def _memory_accesses(
    code: bytes, start: int, end: int, *, base_register: int
) -> list[dict[str, Any]]:
    from capstone import (
        Cs, CS_ARCH_X86, CS_MODE_64, CS_AC_READ, CS_AC_WRITE,
        CS_GRP_CALL, CS_GRP_JUMP,
    )
    from capstone.x86_const import X86_INS_LEA, X86_OP_IMM, X86_OP_MEM, X86_OP_REG

    if (
        type(start) is not int or type(end) is not int
        or type(base_register) is not int or not 0 <= start < end <= len(code)
        or base_register not in range(16)
    ):
        return []
    decoder = _shared_detail_decoder()
    reachable: dict[int, Any] = {}
    pending = [start]
    while pending:
        offset = pending.pop()
        if offset in reachable or not start <= offset < end:
            continue
        instruction = next(
            decoder.disasm(code[offset:end], offset, count=1), None
        )
        if instruction is None or int(instruction.address) != offset:
            raise AcquisitionError(
                "reachable runtime object-field code cannot be decoded at "
                + f"0x{offset:x}"
            )
        next_offset = offset + int(instruction.size)
        if next_offset > end:
            raise AcquisitionError(
                "reachable runtime object-field instruction crosses its bound at "
                + f"0x{offset:x}"
            )
        reachable[offset] = instruction
        mnemonic = instruction.mnemonic.lower()
        if mnemonic in {
            "ret", "retf", "iret", "iretq", "sysret", "ud2", "hlt", "int3"
        }:
            continue
        if instruction.group(CS_GRP_CALL):
            pending.append(next_offset)
            continue
        if instruction.group(CS_GRP_JUMP):
            if (
                instruction.operands
                and instruction.operands[0].type == X86_OP_IMM
            ):
                target = int(instruction.operands[0].imm)
                if start <= target < end:
                    pending.append(target)
            if mnemonic not in {"jmp", "ljmp"}:
                pending.append(next_offset)
            continue
        pending.append(next_offset)
    instructions = [reachable[address] for address in sorted(reachable)]
    if not instructions:
        raise AcquisitionError(
            "runtime object-field access range has no reachable decodable instructions"
        )
    output: list[dict[str, Any]] = []
    volatile = {0, 1, 2, 8, 9, 10, 11}
    for instruction in instructions:
        if instruction.group(CS_GRP_CALL) and base_register in volatile:
            break
        try:
            _reads, writes = _instruction_register_access(instruction)
        except Exception:
            break
        stop_after_instruction = False
        if any(
            _native_register_index(instruction.reg_name(register)) == base_register
            for register in writes
        ):
            operands = instruction.operands
            initialize_this = (
                start == 0 and base_register != 1
                and len(operands) == 2
                and (
                    instruction.mnemonic.lower() == "mov"
                    and all(operand.type == X86_OP_REG for operand in operands)
                    and operands[0].size == operands[1].size == 8
                    and _native_register_index(instruction.reg_name(operands[0].reg))
                    == base_register
                    and _native_register_index(instruction.reg_name(operands[1].reg))
                    == 1
                    or instruction.id == X86_INS_LEA
                    and operands[0].type == X86_OP_REG
                    and operands[1].type == X86_OP_MEM
                    and operands[0].size == 8
                    and _native_register_index(instruction.reg_name(operands[0].reg))
                    == base_register
                    and _native_register_index(
                        instruction.reg_name(operands[1].mem.base)
                    ) == 1
                    and _native_register_index(
                        instruction.reg_name(operands[1].mem.index)
                    ) is None
                    and int(operands[1].mem.disp) == 0
                )
            )
            self_move = (
                instruction.mnemonic.lower() == "mov"
                and len(operands) == 2
                and all(operand.type == X86_OP_REG for operand in operands)
                and _native_register_index(instruction.reg_name(operands[0].reg))
                == base_register
                and _native_register_index(instruction.reg_name(operands[1].reg))
                == base_register
            )
            self_lea = (
                instruction.id == X86_INS_LEA
                and len(operands) == 2
                and operands[0].type == X86_OP_REG
                and operands[1].type == X86_OP_MEM
                and _native_register_index(instruction.reg_name(operands[0].reg))
                == base_register
                and _native_register_index(
                    instruction.reg_name(operands[1].mem.base)
                ) == base_register
                and _native_register_index(
                    instruction.reg_name(operands[1].mem.index)
                ) is None
                and int(operands[1].mem.disp) == 0
            )
            if not (initialize_this or self_move or self_lea):


                stop_after_instruction = True
            if initialize_this:
                continue
        if instruction.id == X86_INS_LEA:
            if stop_after_instruction:
                break
            continue
        for operand in instruction.operands:
            if operand.type != X86_OP_MEM:
                continue
            memory = operand.mem
            base = _native_register_index(instruction.reg_name(memory.base))
            index = _native_register_index(instruction.reg_name(memory.index))
            if (
                base != base_register or index is not None
                or memory.segment != 0
                or instruction.addr_size != 8
                or not 0 <= int(memory.disp) <= 0x7FFFFFFF
            ):
                continue
            access = int(operand.access)
            read = bool(access & CS_AC_READ)
            write = bool(access & CS_AC_WRITE)
            if not read and not write:
                continue
            output.append(
                {
                    "code_offset": int(instruction.address),
                    "object_offset": int(memory.disp),
                    "access": (
                        "read_write" if read and write
                        else "read" if read
                        else "write"
                    ),
                    "width": int(operand.size),
                }
            )
        if stop_after_instruction:
            break
    return output


def _hoisted_parser_field_addresses(
    code: bytes, start: int, end: int, *, first_case_start: int,
    base_register: int,
) -> list[dict[str, Any]]:
    from capstone import (
        Cs, CS_ARCH_X86, CS_MODE_64, CS_AC_READ, CS_AC_WRITE,
        CS_GRP_CALL, CS_GRP_JUMP,
    )
    from capstone.x86_const import (
        X86_INS_ADD, X86_INS_LEA, X86_INS_MOV,
        X86_OP_IMM, X86_OP_MEM, X86_OP_REG,
    )

    if not 0 <= first_case_start <= start < end <= len(code):
        return []
    decoder = _shared_detail_decoder()
    reachable = _reachable_instruction_map(code, decoder=decoder)
    if start not in reachable:
        return []
    ordered = [reachable[offset] for offset in sorted(reachable)]
    saved = {3, 5, 6, 7, 12, 13, 14, 15}
    arguments = {1, 2, 8, 9}
    aliases: dict[int, tuple[int, int]] = {}
    for instruction in ordered:
        offset = int(instruction.address)
        if offset >= start:
            break
        try:
            written = _instruction_written_registers(instruction)
        except Exception:
            return []
        for register in written:
            aliases.pop(register, None)
        if offset >= first_case_start:
            continue
        operands = instruction.operands
        if len(operands) != 2 or operands[0].type != X86_OP_REG:
            continue
        destination = _native_register_index(instruction.reg_name(operands[0].reg))
        if (
            instruction.id == X86_INS_ADD
            and destination == base_register
            and destination in saved
            and operands[0].size == 8
            and operands[1].type == X86_OP_IMM
            and 0 < int(operands[1].imm) <= 0x7FFFFFFF
        ):
            aliases[destination] = (int(operands[1].imm), offset)
            continue
        if instruction.id != X86_INS_LEA or operands[1].type != X86_OP_MEM:
            continue
        memory = operands[1].mem
        if (
            destination not in saved
            or _native_register_index(instruction.reg_name(memory.base)) != base_register
            or _native_register_index(instruction.reg_name(memory.index)) is not None
            or memory.segment != 0
            or not 0 <= int(memory.disp) <= 0x7FFFFFFF
        ):
            continue
        aliases[destination] = (int(memory.disp), offset)
    if not aliases:
        return []
    case = [instruction for instruction in ordered if start <= int(instruction.address) < end]
    output: list[dict[str, Any]] = []
    active_aliases = dict(aliases)
    for position, instruction in enumerate(case):
        operands = instruction.operands
        for operand in operands:
            if operand.type != X86_OP_MEM or instruction.addr_size != 8:
                continue
            memory = operand.mem
            source = _native_register_index(instruction.reg_name(memory.base))
            if (
                source not in active_aliases
                or _native_register_index(instruction.reg_name(memory.index)) is not None
                or memory.segment != 0
                or int(memory.disp) != 0
            ):
                continue
            access = int(operand.access)
            read = bool(access & CS_AC_READ)
            write = bool(access & CS_AC_WRITE)
            if read or write:
                output.append({
                    "code_offset": int(instruction.address),
                    "object_offset": active_aliases[source][0],
                    "access": (
                        "read_write" if read and write
                        else "read" if read else "write"
                    ),
                    "width": int(operand.size),
                })
        if (
            instruction.id == X86_INS_MOV
            and len(operands) == 2
            and operands[0].type == X86_OP_REG
            and operands[1].type == X86_OP_REG
        ):
            destination = _native_register_index(instruction.reg_name(operands[0].reg))
            source = _native_register_index(instruction.reg_name(operands[1].reg))
            if destination in arguments and source in active_aliases:
                for following in case[position + 1:]:
                    distance = int(following.address) - int(instruction.address)
                    if distance > 32 or following.group(CS_GRP_JUMP):
                        break
                    if following.group(CS_GRP_CALL):
                        output.append({
                            "code_offset": int(instruction.address),
                            "object_offset": active_aliases[source][0],
                            "access": "read",
                            "width": 8,
                        })
                        break
                    try:
                        _reads, writes = _instruction_register_access(following)
                    except Exception:
                        break
                    if any(
                        _native_register_index(following.reg_name(register)) == destination
                        for register in writes
                    ):
                        break
        try:
            _reads, writes = _instruction_register_access(instruction)
        except Exception:
            return output
        for register in writes:
            active_aliases.pop(
                _native_register_index(instruction.reg_name(register)), None
            )
    return output


def _native_register_index(name: str | None) -> int | None:
    if not isinstance(name, str):
        return None
    aliases = {
        "rax": 0, "eax": 0, "ax": 0, "al": 0,
        "rcx": 1, "ecx": 1, "cx": 1, "cl": 1,
        "rdx": 2, "edx": 2, "dx": 2, "dl": 2,
        "rbx": 3, "ebx": 3, "bx": 3, "bl": 3,
        "rsp": 4, "esp": 4, "sp": 4, "spl": 4,
        "rbp": 5, "ebp": 5, "bp": 5, "bpl": 5,
        "rsi": 6, "esi": 6, "si": 6, "sil": 6,
        "rdi": 7, "edi": 7, "di": 7, "dil": 7,
    }
    for index in range(8, 16):
        aliases.update({
            f"r{index}": index,
            f"r{index}d": index,
            f"r{index}w": index,
            f"r{index}b": index,
        })
    return aliases.get(name.lower())


_COLLECTION_RUNTIME_WIDTHS = {
    "System.Boolean": 8, "System.Byte": 8, "System.SByte": 8,
    "System.Int16": 16, "System.UInt16": 16, "System.Char": 16,
    "System.Int32": 32, "System.UInt32": 32, "System.Single": 32,
    "System.Int64": 64, "System.UInt64": 64, "System.Double": 64,
}


def _collection_element_widths(
    runtime: Any, descriptor: int
) -> list[tuple[str, int]]:
    if type(descriptor) is not int or descriptor <= 0:
        return []
    try:
        name = runtime.renderer.render(descriptor)
    except Exception:
        return []
    if not isinstance(name, str):
        return []
    open_angle = name.find("<")
    if open_angle <= 0 or not name.endswith(">"):
        return []
    parts = [part.strip() for part in name[open_angle + 1:-1].split(",")]


    if len(parts) == 1:
        roles = ("element",)
    elif len(parts) == 2:
        roles = ("key", "value")
    else:
        return []
    if len(parts) != len(roles):
        return []
    widths: list[tuple[str, int]] = []
    for role, part in zip(roles, parts):
        width = _COLLECTION_RUNTIME_WIDTHS.get(part)
        if width is None:
            return []
        widths.append((role, width))
    return widths


def _parser_scalar_transfer(
    code: bytes,
    start: int,
    end: int,
    *,
    base_register: int,
    object_offset: int,
    width: int,
    allow_call_terminus: bool = False,
) -> dict[str, Any]:
    from capstone import (
        Cs, CS_ARCH_X86, CS_MODE_64, CS_GRP_CALL, CS_GRP_JUMP, CS_GRP_RET,
        CS_AC_WRITE,
    )
    from capstone.x86_const import X86_INS_CALL, X86_OP_IMM, X86_OP_MEM, X86_OP_REG

    MAX_EXPLORED_STATES = 4096
    MAX_EXPLORED_STEPS = 200000
    call_candidates: list[dict[str, Any]] = []
    call_candidate_signatures: set[tuple[Any, ...]] = set()

    def unproven(reason: str) -> dict[str, Any]:
        return {
            "status": "unproven",
            "reason": reason,
            "proof": "bounded-parser-body-path-analysis",
        }

    if (
        type(start) is not int or type(end) is not int or start < 0 or end <= start
        or end > len(code) or type(base_register) is not int
        or base_register not in range(16) or type(object_offset) is not int
        or object_offset < 0 or width not in (32, 64)
    ):
        return unproven("invalid-analysis-domain")

    decoder = _shared_detail_decoder()
    body = code[start:end]
    instruction_map: dict[int, Any] = {}
    for instruction in decoder.disasm(body, start):
        instruction_map[int(instruction.address)] = instruction
    if not instruction_map or start not in instruction_map:
        return unproven("case-entry-is-not-an-instruction")


    def new_state() -> dict[str, Any]:
        return {
            "values": {},
            "vector_values": {},
            "stack_values": {},
            "call_targets": {},
            "stored": None,
        }

    volatile = {0, 1, 2, 8, 9, 10, 11}
    width_bytes = width // 8
    mask = (1 << width) - 1

    def register_index(instruction: Any, register: int) -> int | None:
        return _native_register_index(instruction.reg_name(register))

    def vector_index(instruction: Any, register: int) -> int | None:
        name = instruction.reg_name(register).lower()
        for prefix in ("xmm", "ymm", "zmm"):
            if name.startswith(prefix) and name[len(prefix):].isdigit():
                return int(name[len(prefix):])
        return None

    def register_move_preserves_width(
        mnemonic: str, destination: Any, source: Any,
        destination_index: int | None, source_index: int | None,
        destination_vector: int | None, source_vector: int | None,
    ) -> bool:
        if destination_index is not None and source_index is not None:
            return (
                mnemonic == "mov"
                and destination.size >= width_bytes
                and source.size >= width_bytes
            )
        if destination_vector is not None and source_vector is not None:
            copied_bytes = {
                "movss": 4, "movsd": 8, "movaps": 16, "movups": 16,
            }.get(mnemonic, 0)
            return copied_bytes >= width_bytes
        if (
            (destination_vector is not None and source_index is not None)
            or (destination_index is not None and source_vector is not None)
        ):
            copied_bytes = {"movd": 4, "movq": 8}.get(mnemonic, 0)
            return copied_bytes >= width_bytes
        return False

    def invalidate_stack_write(stack_values, instruction: Any) -> None:
        for operand in instruction.operands:
            if operand.type != X86_OP_MEM or not operand.access & CS_AC_WRITE:
                continue
            base = register_index(instruction, operand.mem.base)
            index = (
                register_index(instruction, operand.mem.index)
                if operand.mem.index else None
            )
            size = int(operand.size)
            if (
                base not in (4, 5) or index is not None or size <= 0
                or operand.mem.segment != 0 or instruction.addr_size != 8
            ):
                stack_values.clear()
                continue
            displacement = int(operand.mem.disp)
            write_end = displacement + size
            for (slot_base, slot_offset), slot_value in list(stack_values.items()):
                slot_size = slot_value[4]
                if (
                    slot_base != base
                    or displacement < slot_offset + slot_size
                    and slot_offset < write_end
                ):
                    stack_values.pop((slot_base, slot_offset), None)

    def canonical(ops: list[tuple[str, int]]) -> list[list[int | str]]:
        result: list[list[int | str]] = []
        for operation, constant in ops:
            constant &= mask
            if operation == "sub":
                operation, constant = "add", (-constant) & mask
            if operation not in {"add", "xor"}:
                raise ValueError("unsupported operation")
            if not constant:
                continue
            if result and result[-1][0] == operation:
                previous = int(result[-1][1])
                result[-1][1] = (
                    previous ^ constant if operation == "xor"
                    else (previous + constant) & mask
                )
                if result[-1][1] == 0:
                    result.pop()
            else:
                result.append([operation, constant])
        return result

    def step(state: dict[str, Any], instruction: Any) -> tuple[str, Any]:
        values = state["values"]
        vector_values = state["vector_values"]
        stack_values = state["stack_values"]
        call_targets = state["call_targets"]
        stored_transfer = state["stored"]
        if instruction.id == X86_INS_CALL:
            if base_register in volatile:
                return "unproven", "instance-register-is-volatile-across-reader-call"
            call_target = (
                int(instruction.operands[0].imm)
                if instruction.operands
                and instruction.operands[0].type == X86_OP_IMM
                else None
            )


            if stored_transfer is None:
                argument_locations = (
                    *((index, "gpr", register) for index, register in enumerate((1, 2, 8, 9))),
                    *((index, "xmm", index) for index in range(1, 4)),
                )
                for argument_index, argument_bank, argument_register in argument_locations:
                    argument_value = (
                        values.get(argument_register)
                        if argument_bank == "gpr"
                        else vector_values.get(argument_register)
                    )
                    if argument_value is None:
                        continue
                    source_call, ops, value_width, return_bank = argument_value
                    if value_width != width:
                        continue
                    try:
                        argument_ops = canonical(ops)
                    except ValueError:
                        continue
                    candidate_record = {
                        "status": "proven",
                        "proof": "bounded-parser-body-path-analysis",
                        "source_call_offset": source_call,
                        "source_call_target_offset": call_targets.get(source_call),
                        "source_call_return_bank": return_bank,
                        "store_offset": int(instruction.address),
                        "store_kind": "call-argument",
                        "call_target_offset": call_target,
                        "argument_index": argument_index,
                        "argument_register": argument_register,
                        "argument_bank": argument_bank,
                        "object_offset": object_offset,
                        "width": width,
                        "ops": argument_ops,
                    }
                    signature = (
                        tuple(tuple(item) for item in argument_ops),
                        width,
                        return_bank,
                        call_target,
                        argument_index,
                        argument_bank,
                    )
                    if signature not in call_candidate_signatures:
                        call_candidate_signatures.add(signature)
                        call_candidates.append(candidate_record)


            if stored_transfer is None and stack_values:


                interrupted_target = (
                    call_target if call_target is not None else 0
                )
                preserved_registers = ",".join(
                    str(index) for index in sorted(set(values) - volatile)
                )
                return "unproven", (
                    "nested-call-after-preserved-scalar-value"
                    f"@0x{int(instruction.address):x}"
                    f":target=0x{interrupted_target:x}"
                    f":regs={preserved_registers or '-'}"
                )


            for register in volatile:
                values.pop(register, None)
            for register in range(6):
                vector_values.pop(register, None)
            call_targets[int(instruction.address)] = (
                int(instruction.operands[0].imm)
                if instruction.operands
                and instruction.operands[0].type == X86_OP_IMM
                else None
            )
            values[0] = (int(instruction.address), [], width, "rax")
            vector_values[0] = (int(instruction.address), [], width, "xmm0")
            return "next", None
        if instruction.group(CS_GRP_JUMP):
            target = (
                int(instruction.operands[0].imm)
                if instruction.operands
                and instruction.operands[0].type == X86_OP_IMM
                else None
            )
            return "jump", target
        if instruction.group(CS_GRP_RET) or instruction.mnemonic.lower() in {
            "ret", "retf", "iret", "iretq", "hlt", "ud2", "int3", "int",
        }:
            return "exit", None

        try:
            _reads, writes = instruction.regs_access()
        except Exception:
            return "unproven", "instruction-register-effects-are-unknown"
        if (
            instruction.mnemonic.lower() in {"enter", "insb", "insw", "insd"}
            or any(register_index(instruction, register) in (4, 5) for register in writes)
        ):


            stack_values.clear()
        for register in writes:
            if register_index(instruction, register) == base_register:
                operands = instruction.operands
                initialize_this = (
                    start == 0 and base_register != 1
                    and len(operands) == 2
                    and (
                        instruction.mnemonic.lower() == "mov"
                        and all(operand.type == X86_OP_REG for operand in operands)
                        and operands[0].size == operands[1].size == 8
                        and register_index(instruction, operands[0].reg) == base_register
                        and register_index(instruction, operands[1].reg) == 1
                        or instruction.mnemonic.lower() == "lea"
                        and operands[0].type == X86_OP_REG
                        and operands[1].type == X86_OP_MEM
                        and operands[0].size == 8
                        and register_index(instruction, operands[0].reg) == base_register
                        and register_index(instruction, operands[1].mem.base) == 1
                        and register_index(instruction, operands[1].mem.index) is None
                        and int(operands[1].mem.disp) == 0
                    )
                )
                self_move = (
                    instruction.mnemonic.lower() == "mov"
                    and len(operands) == 2
                    and all(operand.type == X86_OP_REG for operand in operands)
                    and register_index(instruction, operands[0].reg) == base_register
                    and register_index(instruction, operands[1].reg) == base_register
                )
                if not (initialize_this or self_move):
                    return "unproven", "instance-register-is-overwritten-in-parser-case"

        operands = instruction.operands
        mnemonic = instruction.mnemonic.lower()
        invalidate_stack_write(stack_values, instruction)
        if mnemonic in {
            "mov", "movd", "movq", "movss", "movsd", "movaps", "movups",
        } and len(operands) == 2:
            destination, source = operands
            if destination.type == X86_OP_REG:
                destination_index = register_index(instruction, destination.reg)
                destination_vector = vector_index(instruction, destination.reg)
                value = None
                preserves_width = False
                if source.type == X86_OP_REG:
                    source_index = register_index(instruction, source.reg)
                    source_vector = vector_index(instruction, source.reg)
                    preserves_width = register_move_preserves_width(
                        mnemonic, destination, source,
                        destination_index, source_index,
                        destination_vector, source_vector,
                    )
                    if destination_index is not None:
                        value = (
                            values.get(source_index)
                            if source_index is not None
                            else vector_values.get(source_vector)
                            if source_vector is not None and mnemonic in {"movd", "movq"}
                            else None
                        )
                    elif destination_vector is not None:
                        value = (
                            vector_values.get(source_vector)
                            if source_vector is not None
                            else values.get(source_index)
                            if source_index is not None and mnemonic in {"movd", "movq"}
                            else None
                        )
                elif source.type == X86_OP_MEM:
                    source_base = register_index(instruction, source.mem.base)
                    if (
                        source_base in (4, 5) and not source.mem.index
                        and source.mem.segment == 0 and instruction.addr_size == 8
                        and source.size == width_bytes
                    ):
                        stack_value = stack_values.get(
                            (source_base, int(source.mem.disp))
                        )
                        if stack_value is not None and stack_value[4] == source.size:
                            value = stack_value[:4]
                        preserves_width = (
                            value is not None
                            and destination.size >= width_bytes
                        )
                if value is not None and preserves_width:
                    if destination_index is not None:
                        values[destination_index] = value
                    elif destination_vector is not None:
                        vector_values[destination_vector] = value
                else:
                    if destination_index is not None:
                        values.pop(destination_index, None)
                    if destination_vector is not None:
                        vector_values.pop(destination_vector, None)
                return "next", None
            if destination.type == X86_OP_MEM and source.type == X86_OP_REG:
                source_index = register_index(instruction, source.reg)
                source_vector = vector_index(instruction, source.reg)
                value = (
                    values.get(source_index)
                    if source_index is not None
                    else vector_values.get(source_vector)
                    if source_vector is not None
                    else None
                )
                base = register_index(instruction, destination.mem.base)
                index = register_index(instruction, destination.mem.index) if destination.mem.index else None
                displacement = int(destination.mem.disp)
                if (
                    base == base_register and index is None
                    and destination.mem.segment == 0 and instruction.addr_size == 8
                    and displacement == object_offset
                ):
                    vector_store_width_matches = (
                        mnemonic == "movss" and width == 32
                        or mnemonic == "movsd" and width == 64
                        or mnemonic == "movd" and width == 32
                        or mnemonic == "movq" and width == 64
                    )
                    source_width_matches = (
                        destination.size == width_bytes
                        and (
                            source.size == width_bytes
                            if source_vector is None
                            else vector_store_width_matches
                        )
                    )
                    if value is None or not source_width_matches:
                        return "unproven", "target-field-store-source-is-not-proven"
                    source_call, ops, value_width, return_bank = value
                    if value_width != width:
                        return "unproven", "target-field-store-width-differs"
                    try:
                        normalized = canonical(ops)
                    except ValueError:
                        return "unproven", "target-field-store-operation-is-unsupported"
                    record = {
                        "status": "proven",
                        "proof": "bounded-parser-body-path-analysis",
                        "source_call_offset": source_call,
                        "source_call_target_offset": call_targets.get(source_call),
                        "source_call_return_bank": return_bank,
                        "store_offset": int(instruction.address),
                        "object_offset": object_offset,
                        "width": width,
                        "ops": normalized,
                    }
                    state["stored"] = record
                    return "store", record
                if stored_transfer is not None:
                    if base in (4, 5) and index is None:
                        return "next", None
                    if base != base_register or index is not None:
                        return "unproven", "unknown-memory-write-after-target-store"
                if (
                    base in (4, 5) and index is None
                    and destination.mem.segment == 0 and instruction.addr_size == 8
                ):
                    if value is None:
                        stack_values.pop((base, displacement), None)
                    else:
                        vector_store_width_matches = (
                            mnemonic == "movss" and width == 32
                            or mnemonic == "movsd" and width == 64
                            or mnemonic == "movd" and width == 32
                            or mnemonic == "movq" and width == 64
                        )
                        source_width_matches = (
                            destination.size == width_bytes
                            and (
                                source.size == width_bytes
                                if source_vector is None
                                else vector_store_width_matches
                            )
                            and value[2] == width
                        )
                        if source_width_matches:
                            stack_values[(base, displacement)] = (
                                value[0], value[1], value[2], value[3],
                                destination.size,
                            )
                return "next", None

        if stored_transfer is not None and any(
            operand.type == X86_OP_MEM and operand.access & CS_AC_WRITE
            for operand in operands
        ):
            return "unproven", "unknown-memory-write-after-target-store"

        if mnemonic in {"add", "sub", "xor"} and len(operands) == 2:
            destination, source = operands
            if destination.type != X86_OP_REG:
                return "next", None
            destination_index = register_index(instruction, destination.reg)
            if destination_index is None:
                return "next", None
            value = values.get(destination_index)
            if value is None:
                return "next", None
            if (
                source.type != X86_OP_IMM or destination.size != width_bytes
                or value[2] != width
            ):
                values.pop(destination_index, None)
                return "next", None
            values[destination_index] = (
                value[0], [*value[1], (mnemonic, int(source.imm) & mask)],
                value[2], value[3],
            )
            return "next", None

        if mnemonic in {"inc", "dec", "not"} and len(operands) == 1:
            operand = operands[0]
            if operand.type == X86_OP_REG:
                destination_index = register_index(instruction, operand.reg)
                value = values.get(destination_index) if destination_index is not None else None
                if value is not None and operand.size == width_bytes:
                    operation, constant = (
                        ("add", 1) if mnemonic == "inc" else
                        ("sub", 1) if mnemonic == "dec" else
                        ("xor", mask)
                    )
                    values[destination_index] = (
                        value[0], [*value[1], (operation, constant)],
                        value[2], value[3],
                    )
                elif destination_index is not None:
                    values.pop(destination_index, None)
            return "next", None

        if mnemonic == "lea" and len(operands) == 2:
            destination, source = operands
            if destination.type == X86_OP_REG and source.type == X86_OP_MEM:
                destination_index = register_index(instruction, destination.reg)
                source_base = register_index(instruction, source.mem.base)
                value = values.get(source_base) if source_base is not None else None
                if (
                    destination_index is not None and value is not None
                    and not source.mem.index and destination.size >= width_bytes
                ):
                    displacement = int(source.mem.disp)
                    operation = "add" if displacement >= 0 else "sub"
                    values[destination_index] = (
                        value[0], [*value[1], (operation, abs(displacement))],
                        value[2], value[3],
                    )
                elif destination_index is not None:
                    values.pop(destination_index, None)
                return "next", None


        try:
            _reads, writes = instruction.regs_access()
        except Exception:
            return "unproven", "instruction-register-effects-are-unknown"
        for register in writes:
            index = register_index(instruction, register)
            if index is not None:
                values.pop(index, None)
            vector = vector_index(instruction, register)
            if vector is not None:
                vector_values.pop(vector, None)
        return "next", None

    def clone_state(state: dict[str, Any]) -> dict[str, Any]:
        return {
            "values": dict(state["values"]),
            "vector_values": dict(state["vector_values"]),
            "stack_values": dict(state["stack_values"]),
            "call_targets": dict(state["call_targets"]),
            "stored": None if state["stored"] is None else dict(state["stored"]),
        }

    def state_signature(state: dict[str, Any]) -> tuple:
        return (
            tuple(sorted(
                (key, value[0], tuple(value[1]), value[2], value[3])
                for key, value in state["values"].items()
            )),
            tuple(sorted(
                (key, value[0], tuple(value[1]), value[2], value[3])
                for key, value in state["vector_values"].items()
            )),
            tuple(sorted(
                (key[0], key[1], value[0], tuple(value[1]), value[2], value[3], value[4])
                for key, value in state["stack_values"].items()
            )),
            tuple(sorted(state["call_targets"].items())),
            None if state["stored"] is None else (
                state["stored"]["source_call_offset"],
                tuple(tuple(item) for item in state["stored"]["ops"]),
                state["stored"]["width"],
                state["stored"]["source_call_return_bank"],
                state["stored"]["source_call_target_offset"],
            ),
        )

    pending: list[tuple[int, dict[str, Any]]] = [(start, new_state())]
    seen_states: set[tuple[int, tuple]] = set()
    explored_steps = 0
    stored_chain: dict[str, Any] | None = None
    stored_signature: tuple | None = None
    while pending:
        address, state = pending.pop()
        while True:
            explored_steps += 1
            if explored_steps > MAX_EXPLORED_STEPS:
                return unproven("parser-case-exploration-bound-exceeded")
            instruction = instruction_map.get(address)
            if instruction is None:
                if start <= address < end:


                    return unproven("undecoded-gap-in-parser-case")
                break
            action, payload = step(state, instruction)
            if action == "unproven":
                return unproven(str(payload))
            if action == "exit":
                break
            if action == "jump":
                target = payload
                if target is None:
                    return unproven("indirect-control-flow-in-parser-case")
                successors: list[int] = []
                if start <= int(target) < end:
                    successors.append(int(target))
                fallthrough = int(instruction.address) + int(instruction.size)
                if (
                    instruction.mnemonic.lower() not in {"jmp", "ljmp"}
                    and start <= fallthrough < end
                ):
                    successors.append(fallthrough)
                for successor in successors:
                    signature = (successor, state_signature(state))
                    if signature in seen_states:
                        continue
                    if len(seen_states) >= MAX_EXPLORED_STATES:
                        return unproven("parser-case-exploration-bound-exceeded")
                    seen_states.add(signature)
                    pending.append((successor, clone_state(state)))
                break
            if action in {"store", "call-store"}:
                record = payload
                signature = (
                    tuple(tuple(item) for item in record["ops"]),
                    record["width"],
                    record["source_call_return_bank"],
                    record.get("store_kind"),
                    record.get("call_target_offset"),
                    record.get("argument_index"),
                )
                if stored_signature is None:
                    stored_chain = dict(record)
                    reader_target = record.get("source_call_target_offset")
                    stored_chain["reader_call_offsets_owner_only"] = (
                        [reader_target] if type(reader_target) is int else []
                    )
                    stored_chain["indirect_reader_call_owner_only"] = (
                        type(reader_target) is not int
                    )
                    stored_signature = signature
                elif signature != stored_signature:
                    return unproven("conflicting-target-field-stores")
                else:
                    offsets = set(
                        stored_chain.get("reader_call_offsets_owner_only") or ()
                    )
                    reader_target = record.get("source_call_target_offset")
                    if type(reader_target) is int:
                        offsets.add(reader_target)
                    else:
                        stored_chain["indirect_reader_call_owner_only"] = True
                    stored_chain["reader_call_offsets_owner_only"] = sorted(offsets)
                address = int(instruction.address) + int(instruction.size)
                continue
            address = int(instruction.address) + int(instruction.size)
    if allow_call_terminus and len(call_candidates) == 1:


        return dict(call_candidates[0])
    if stored_chain is None:
        return unproven("no-proven-scalar-store-in-case")
    if call_candidates:
        stored_chain["call_candidates_owner_only"] = [
            dict(candidate) for candidate in call_candidates
        ]
    return stored_chain

def _parser_case_callee_rows(
    *,
    image: MappedPE,
    parser_code: bytes,
    start: int,
    end: int,
    base_register: int,
    parser_method_pointer: int,
    by_object_offset: Mapping[int, list[dict[str, Any]]],
    covered_offsets: set[int],
    method_indexes_by_code_pointer: Mapping[int, list[int]],
    runtime: Any,
) -> list[dict[str, Any]]:
    import struct as _struct
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64, CS_GRP_JUMP
    from capstone.x86_const import X86_INS_CALL, X86_OP_IMM, X86_OP_MEM, X86_OP_REG

    decoder = _shared_detail_decoder()
    rows: list[dict[str, Any]] = []
    argument_registers = {1, 2, 8, 9}
    volatile = {0, 1, 2, 8, 9, 10, 11}
    aliases = {base_register}
    for instruction in decoder.disasm(parser_code[start:end], start):
        mnemonic = instruction.mnemonic.lower()
        if instruction.id == X86_INS_CALL:
            operands = instruction.operands
            target = (
                int(operands[0].imm)
                if operands and operands[0].type == X86_OP_IMM
                else None
            )
            if target is not None:
                candidates = sorted(aliases & argument_registers)
                method_indexes = method_indexes_by_code_pointer.get(target, [])
                if len(method_indexes) == 1 and candidates:
                    callee_code = _bounded_code(image, target)
                    if callee_code:
                        accesses = _memory_accesses(
                            callee_code, 0, len(callee_code),
                            base_register=candidates[0] if len(candidates) == 1 else None,
                        ) if len(candidates) == 1 else []
                        for argument in candidates:
                            if len(candidates) > 1:
                                accesses = _memory_accesses(
                                    callee_code, 0, len(callee_code),
                                    base_register=argument,
                                )
                            for access in accesses:
                                if access["access"] not in {"write", "read_write"}:
                                    continue
                                offset = int(access["object_offset"])
                                if offset in covered_offsets:
                                    continue
                                fields = by_object_offset.get(offset)
                                if not fields:
                                    continue
                                width_bits = int(access["width"]) * 8
                                if width_bits not in (32, 64):
                                    continue
                                transfer = _parser_scalar_transfer(
                                    callee_code, 0, len(callee_code),
                                    base_register=argument,
                                    object_offset=offset,
                                    width=width_bits,
                                )
                                if transfer.get("status") != "proven":
                                    continue
                                callee_pointer = target
                                call_target_offset = transfer.get(
                                    "source_call_target_offset"
                                )
                                if type(call_target_offset) is not int:
                                    continue
                                reader_indexes = method_indexes_by_code_pointer.get(
                                    callee_pointer + call_target_offset, []
                                )
                                if len(reader_indexes) != 1:
                                    continue
                                reader_index = reader_indexes[0]
                                reader_row = runtime.method_row(reader_index)
                                store_method = runtime.method_row(method_indexes[0])
                                field = fields[0]
                                rows.append(
                                    {
                                        "access_row": {
                                            "field_index": int(field["field_index"]),
                                            "access": "write",
                                            "width": int(access["width"]),
                                            "code_offset": int(instruction.address),
                                            "object_offset": offset,
                                            "object_base_owner_only": argument,
                                        },
                                        "transfer": {
                                            **transfer,
                                            "parser_method_code_pointer_owner_only": callee_pointer,
                                            "store_method_owner_only": {
                                                "method_index_owner_only": method_indexes[0],
                                                "code_pointer_owner_only": callee_pointer,
                                                "name_owner_only": runtime.method_name(
                                                    method_indexes[0], store_method
                                                ),
                                                "owner_type_index_owner_only": store_method[0],
                                                "call_site_offset_owner_only": int(
                                                    instruction.address
                                                ),
                                                "parser_code_pointer_owner_only": (
                                                    parser_method_pointer
                                                ),
                                                "argument_register_owner_only": argument,
                                            },
                                            "reader_method_owner_only": {
                                                "method_index_owner_only": reader_index,
                                                "owner_type_index_owner_only": reader_row[0],
                                                "call_target_owner_only": (
                                                    callee_pointer + call_target_offset
                                                ),
                                                "code_pointer_owner_only": reader_row[3],
                                                "name_owner_only": runtime.method_name(
                                                    reader_index, reader_row
                                                ),
                                                "return_type_owner_only": runtime.method_return(
                                                    reader_index
                                                ),
                                                "parameter_count_owner_only": reader_row[10],
                                            },
                                        },
                                    }
                                )
            for register in volatile:
                aliases.discard(register)
            continue
        if instruction.group(CS_GRP_JUMP) or mnemonic in {
            "ret", "retf", "iret", "iretq", "jmp", "hlt", "ud2", "int3", "int",
        }:
            break
        operands = instruction.operands
        if mnemonic == "mov" and len(operands) == 2 and all(
            operand.type == X86_OP_REG for operand in operands
        ):
            destination = _native_register_index(
                instruction.reg_name(operands[0].reg)
            )
            source = _native_register_index(
                instruction.reg_name(operands[1].reg)
            )
            if destination is not None:
                aliases.discard(destination)
                if source is not None and source in aliases and (
                    operands[0].size == operands[1].size == 8
                ):
                    aliases.add(destination)
            continue
        if mnemonic == "lea" and len(operands) == 2 and (
            operands[0].type == X86_OP_REG and operands[1].type == X86_OP_MEM
        ):
            destination = _native_register_index(
                instruction.reg_name(operands[0].reg)
            )
            source = _native_register_index(
                instruction.reg_name(operands[1].mem.base)
            )
            if destination is not None:
                aliases.discard(destination)
                if (
                    source is not None and source in aliases
                    and not operands[1].mem.index
                    and int(operands[1].mem.disp) == 0
                    and operands[0].size == 8
                ):
                    aliases.add(destination)
            continue
        try:
            _reads, writes = instruction.regs_access()
        except Exception:
            break
        for register in writes:
            index = _native_register_index(instruction.reg_name(register))
            if index is not None:
                aliases.discard(index)
    return rows


def _bounded_code(image: MappedPE, pointer: int) -> bytes | None:


    cache = image.__dict__.setdefault("_p29_bounded_code_cache", {})
    if pointer in cache:
        return cache[pointer]
    rva = pointer - image.image_base
    if rva <= 0 or not image.executable_rva(rva):
        result = None
    else:
        function = image.containing_function(rva)
        if function is None or function.begin_rva != rva:
            result = None
        else:
            bounds = image.bounded_code(rva, function.end_rva)
            if bounds is None:
                result = None
            else:
                start, end = bounds
                result = bytes(image._mapping[start:end])
    cache[pointer] = result
    return result


def _runtime(receipt_path: Path) -> tuple[dict[str, Any], dict[str, Path], _RuntimeOutput]:
    receipt, paths = _validated_native_receipt(
        receipt_path, allow_type_method_metadata=True
    )
    runtime = _RuntimeOutput(
        binary=paths["binary"],
        type_identity=paths["type_identity_inventory"].read_bytes(),
        type_graph=paths["type_graph_inventory"].read_bytes(),
        type_references=paths["type_reference_inventory"].read_bytes(),
        methods=paths["method_detail_inventory"].read_bytes(),
        native_members=paths["native_member_detail_inventory"].read_bytes(),
        event_modules=paths["event_module_inventory"].read_bytes(),
        method_generics=paths["method_generic_inventory"].read_bytes(),
        generic_parameter_details=paths[
            "generic_parameter_detail_inventory"
        ].read_bytes(),
    )
    direct_model = paths.get("direct_interface_model")
    direct_inventory = paths.get("direct_interface_inventory")
    if (direct_model is None) != (direct_inventory is None):
        raise AcquisitionError(
            "runtime native receipt has an incomplete direct-interface binding"
        )
    if direct_model is not None and direct_inventory is not None:
        direct = load_runtime_direct_interfaces(
            model_path=direct_model,
            inventory_path=direct_inventory,
            expected_executable_sha256=receipt["target"]["executable_sha256"],
            expected_type_identity_inventory_sha256=receipt["inputs"][
                "type_identity_inventory"
            ]["sha256"],
            expected_type_graph_inventory_sha256=receipt["inputs"][
                "type_graph_inventory"
            ]["sha256"],
        )
        if direct["type_count"] != runtime.type_count:
            raise AcquisitionError(
                "runtime native receipt direct-interface domain differs"
            )
        runtime.renderer.direct_interface_rows = direct["rows"]
        runtime.renderer.direct_interface_descriptors = direct["descriptors"]
    return receipt, paths, runtime


def _message_types(runtime: _RuntimeOutput) -> tuple[int, list[int]]:
    bases: Counter[int] = Counter()
    for index in range(runtime.type_count):
        identity = runtime.renderer.identity_row(index)
        graph = runtime.renderer.graph_row(index)
        if (
            identity[7] & 0x100
            and not identity[1] & 0x60
            and not identity[7] & 0x20
            and graph[6] >= 2
            and graph[3]
        ):
            bases[graph[3]] += 1
    ranked = bases.most_common(2)
    if len(ranked) < 2 or ranked[0][1] < max(128, ranked[1][1] * 4):
        raise AcquisitionError("runtime protocol message base is ambiguous")
    base = ranked[0][0]
    family = [
        index
        for index in range(runtime.type_count)
        if runtime.renderer.graph_row(index)[3] == base
        and runtime.renderer.identity_row(index)[7] & 0x100
        and runtime.renderer.graph_row(index)[6] >= 2
        and runtime.renderer.graph_row(index)[7] == 0
    ]
    if len(family) != ranked[0][1]:
        raise AcquisitionError("runtime protocol self-message family differs")


    selected = [
        index
        for index in family
        if "System.Collections.Generic.IEnumerable<System.Byte>"
        not in runtime.renderer.root_interfaces(index)
    ]
    if not selected:
        raise AcquisitionError("runtime protocol message family is empty")
    return base, selected


_ANALYSIS_MEMO: dict[tuple[str, str], bytes] = {}


_ANALYSIS_MEMO_DIR: Path | None = None
_ANALYSIS_MEMO_SCHEMA = "alpha.proto-analysis-memo/v1"
_ANALYSIS_MEMO_KEEP = 6
_ANALYSIS_MEMO_IMPLEMENTATION: str | None = None


def set_analysis_memo_dir(path: Path | None) -> None:
    global _ANALYSIS_MEMO_DIR
    _ANALYSIS_MEMO_DIR = (
        Path(path).expanduser().resolve() if path is not None else None
    )


def _analysis_memo_implementation() -> str:
    global _ANALYSIS_MEMO_IMPLEMENTATION
    if _ANALYSIS_MEMO_IMPLEMENTATION is None:
        from alpha.p19 import _implementation_digest
        try:
            from alpha.computation_identity import computation_digest
            _ANALYSIS_MEMO_IMPLEMENTATION = computation_digest((
                ("alpha.p29", "_analyze_runtime_proto_uncached"),
            ))
        except (OSError, ValueError, SyntaxError, ImportError):

            _ANALYSIS_MEMO_IMPLEMENTATION = _implementation_digest()
    return _ANALYSIS_MEMO_IMPLEMENTATION


def _analysis_memo_paths(key: tuple[str, str]) -> tuple[Path, Path] | None:
    if _ANALYSIS_MEMO_DIR is None:
        return None
    digest = hashlib.sha256()
    for part in (*key, _analysis_memo_implementation()):
        digest.update(part.encode("utf-8") + b"\0")
    stem = _ANALYSIS_MEMO_DIR / f"analysis-{digest.hexdigest()[:32]}"
    return stem.with_suffix(".payload"), stem.with_suffix(".meta.json")


def _load_analysis_memo_file(key: tuple[str, str]) -> bytes | None:
    paths = _analysis_memo_paths(key)
    if paths is None:
        return None
    payload_path, meta_path = paths
    if not meta_path.exists():
        return _load_legacy_analysis_memo(key)
    try:
        meta = read_json(meta_path, maximum_bytes=1 << 20)
        if (
            meta.get("schema") != _ANALYSIS_MEMO_SCHEMA
            or meta.get("key") != list(key)
            or meta.get("implementation") != _analysis_memo_implementation()
            or type(meta.get("payload_bytes")) is not int
        ):
            return None
        raw = payload_path.read_bytes()
        if len(raw) != meta["payload_bytes"]:
            return None
        if hashlib.sha256(raw).hexdigest() != meta.get("payload_sha256"):
            return None
        return raw
    except (AcquisitionError, OSError, ValueError, TypeError, KeyError):

        return None


def _load_legacy_analysis_memo(key: tuple[str, str]) -> bytes | None:
    if _ANALYSIS_MEMO_DIR is None:
        return None
    from alpha.computation_identity import legacy_source_matches
    roots = (("alpha.p29", "_analyze_runtime_proto_uncached"),)
    for meta_path in sorted(_ANALYSIS_MEMO_DIR.glob("analysis-*.meta.json"), reverse=True):
        try:
            meta = read_json(meta_path, maximum_bytes=1 << 20)
            if (meta.get("schema") != _ANALYSIS_MEMO_SCHEMA
                    or meta.get("key") != list(key)
                    or type(meta.get("payload_bytes")) is not int):
                continue
            payload_path = meta_path.with_name(meta_path.name[:-len(".meta.json")] + ".payload")
            raw = payload_path.read_bytes()
            if (len(raw) != meta["payload_bytes"]
                    or hashlib.sha256(raw).hexdigest() != meta.get("payload_sha256")):
                continue
            if not legacy_source_matches(_ANALYSIS_MEMO_DIR.parent,
                    str(meta.get("implementation", "")), roots, _analysis_memo_implementation()):
                continue
            _store_analysis_memo_file(key, raw)
            return raw
        except (AcquisitionError, OSError, ValueError, TypeError, KeyError):
            continue
    return None


def _store_analysis_memo_file(key: tuple[str, str], encoded: bytes) -> None:
    paths = _analysis_memo_paths(key)
    if paths is None:
        return
    payload_path, meta_path = paths
    try:


        _private_bytes(payload_path, encoded)
        _private_json(meta_path, {
            "schema": _ANALYSIS_MEMO_SCHEMA,
            "key": list(key),
            "implementation": _analysis_memo_implementation(),
            "payload_bytes": len(encoded),
            "payload_sha256": hashlib.sha256(encoded).hexdigest(),
        })
    except (OSError, TypeError, ValueError):
        return
    if _ANALYSIS_MEMO_DIR is None:
        return
    try:
        rows = []
        for stale_meta in _ANALYSIS_MEMO_DIR.glob("analysis-*.meta.json"):
            stale_payload = stale_meta.with_name(
                stale_meta.name[: -len(".meta.json")] + ".payload"
            )
            if stale_payload.is_file():
                rows.append((stale_meta.stat().st_mtime_ns, stale_meta, stale_payload))
        for _, stale_meta, stale_payload in sorted(rows, reverse=True)[
            _ANALYSIS_MEMO_KEEP:
        ]:
            stale_meta.unlink(missing_ok=True)
            stale_payload.unlink(missing_ok=True)
    except OSError:
        return


def analyze_runtime_proto(
    *, native_output_receipt: Path, proto_field_type_model: Path
) -> dict[str, Any]:
    receipt_key = json.dumps(
        file_identity(native_output_receipt.expanduser().resolve()),
        ensure_ascii=False, sort_keys=True,
    )
    model_key = json.dumps(
        file_identity(proto_field_type_model.expanduser().resolve()),
        ensure_ascii=False, sort_keys=True,
    )
    key = (receipt_key, model_key)
    encoded = _ANALYSIS_MEMO.get(key)
    if encoded is None:
        encoded = _load_analysis_memo_file(key)
    if encoded is None:
        analysis = _analyze_runtime_proto_uncached(
            native_output_receipt=native_output_receipt,
            proto_field_type_model=proto_field_type_model,
        )
        encoded = json.dumps(
            analysis, ensure_ascii=False, allow_nan=False,
            separators=(",", ":"),
        ).encode("utf-8")
        _store_analysis_memo_file(key, encoded)
    _ANALYSIS_MEMO[key] = encoded
    return json.loads(encoded)


def _analyze_runtime_proto_uncached(
    *, native_output_receipt: Path, proto_field_type_model: Path
) -> dict[str, Any]:
    receipt, paths, runtime = _runtime(native_output_receipt)
    model_path = proto_field_type_model.expanduser().resolve()
    model = read_json(model_path)
    if (
        model.get("schema") != RUNTIME_PROTO_FIELD_TYPE_SCHEMA
        or model.get("status") != "runtime-validated"
        or not all(model.get("checks", {}).values())
        or model.get("target", {}).get("executable_sha256")
        != receipt["target"]["executable_sha256"]
    ):
        raise AcquisitionError("runtime protocol field type model is stale")
    inventory_path = Path(model["inventory"]["path"])
    if file_identity(inventory_path) != model["inventory"]:
        raise AcquisitionError("runtime protocol field type inventory is stale")
    proto_types = inventory_path.read_bytes()
    header = RUNTIME_PROTO_FIELD_TYPE_HEADER.unpack_from(proto_types)
    if (
        header[0] != RUNTIME_PROTO_FIELD_TYPE_MAGIC
        or header[1] != RUNTIME_PROTO_FIELD_TYPE_VERSION
        or header[5] != model["counts"]["field_count"]
    ):
        raise AcquisitionError("runtime protocol field type inventory is invalid")

    base, selected_types = _message_types(runtime)
    selected = set(selected_types)
    fields_by_type: dict[int, list[dict[str, Any]]] = {
        index: [] for index in selected_types
    }
    for index in range(header[5]):
        type_index, field_index, pointer, descriptor = (
            RUNTIME_PROTO_FIELD_TYPE_RECORD.unpack_from(
                proto_types,
                RUNTIME_PROTO_FIELD_TYPE_HEADER.size
                + index * RUNTIME_PROTO_FIELD_TYPE_RECORD.size,
            )
        )
        field = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + field_index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        if (
            field[0] != type_index
            or field[2] != pointer
            or not descriptor
            or field[5] & 0x10
        ):
            raise AcquisitionError("runtime protocol field identity differs")
        if type_index not in selected:
            if (
                not 0 <= type_index < runtime.type_count
                or runtime.renderer.graph_row(type_index)[3] != base
                or "System.Collections.Generic.IEnumerable<System.Byte>"
                not in runtime.renderer.root_interfaces(type_index)
            ):
                raise AcquisitionError(
                    "runtime protocol field inventory contains a foreign type"
                )
            continue
        fields_by_type[type_index].append(
            {
                "field_index": field_index,
                "member_index": field[1],
                "descriptor": descriptor,
                "managed_offset": field[4],
                "attributes": field[5],
                "name": _text(
                    runtime.native, field[9], field[7], label="proto field name"
                ),
            }
        )

    methods_by_type: dict[int, list[int]] = {index: [] for index in selected_types}
    method_indexes_by_code_pointer: dict[int, list[int]] = {}
    family_counts: Counter[int] = Counter()
    void_descriptor = None
    for index in range(runtime.method_count):
        method = runtime.method_row(index)
        if method[3] > 0:
            method_indexes_by_code_pointer.setdefault(method[3], []).append(index)
        if method[0] not in selected:
            continue
        methods_by_type[method[0]].append(index)
        if method[10] != 1 or method[9] & METHOD_DETAIL_CONSTRUCTOR:
            continue
        if runtime.method_return(index) != "System.Void":
            continue
        parameter = runtime.parameter_row(method[11])
        family_counts[parameter[2]] += 1
        void_descriptor = method[4]
    families = family_counts.most_common()
    if len(families) < 2 or families[1][1] < 128:
        raise AcquisitionError("runtime protocol stream families are unavailable")

    family_metrics: dict[int, Counter[str]] = {
        descriptor: Counter() for descriptor, _count in families
    }
    method_code: dict[int, bytes] = {}
    parser_candidates: dict[int, tuple[int, list[dict[str, Any]]]] = {}
    writer_candidates: dict[int, tuple[int, list[dict[str, int]]]] = {}
    writer_code: dict[int, bytes] = {}
    formatter_candidates: dict[int, list[dict[str, int]]] = {}
    with MappedPE(paths["binary"]) as image:
        binary_image_base = image.image_base
        for type_index in selected_types:
            for method_index in methods_by_type[type_index]:
                method = runtime.method_row(method_index)
                if method[10] != 1 or method[4] != void_descriptor:
                    continue
                parameter = runtime.parameter_row(method[11])[2]
                if parameter not in family_metrics:
                    continue
                code = _bounded_code(image, method[3])
                if code is None:
                    family_metrics[parameter]["unbounded"] += 1
                    continue
                cases = _tag_cases(code)
                direct_tags = _direct_tag_writes(code)
                family_metrics[parameter]["bounded"] += 1
                family_metrics[parameter]["tag_cases"] += len(cases)
                family_metrics[parameter]["direct_tags"] += len(direct_tags)
                if cases:
                    family_metrics[parameter]["tag_methods"] += 1
                if direct_tags:
                    family_metrics[parameter]["direct_tag_methods"] += 1

        ranked_parser = sorted(
            family_metrics,
            key=lambda descriptor: (
                family_metrics[descriptor]["tag_methods"],
                family_metrics[descriptor]["tag_cases"],
            ),
            reverse=True,
        )
        parser_family = ranked_parser[0]
        if (
            family_metrics[parser_family]["tag_methods"] < 128
            or len(ranked_parser) > 1
            and family_metrics[parser_family]["tag_methods"]
            <= family_metrics[ranked_parser[1]]["tag_methods"] * 4
        ):
            raise AcquisitionError("runtime protocol parser family is ambiguous")
        ranked_writer = sorted(
            (
                descriptor
                for descriptor in family_metrics
                if descriptor != parser_family
            ),
            key=lambda descriptor: (
                family_metrics[descriptor]["direct_tag_methods"],
                family_metrics[descriptor]["direct_tags"],
            ),
            reverse=True,
        )
        if (
            not ranked_writer
            or family_metrics[ranked_writer[0]]["direct_tag_methods"] < 128
            or len(ranked_writer) > 1
            and family_metrics[ranked_writer[0]]["direct_tag_methods"]
            <= family_metrics[ranked_writer[1]]["direct_tag_methods"] * 4
        ):
            raise AcquisitionError("runtime protocol writer family is ambiguous")
        writer_family = ranked_writer[0]


        parser_candidates.clear()
        method_code.clear()
        for type_index in selected_types:
            candidates: list[tuple[int, list[dict[str, Any]], bytes]] = []
            for method_index in methods_by_type[type_index]:
                method = runtime.method_row(method_index)
                if method[10] != 1 or method[4] != void_descriptor:
                    continue
                if runtime.parameter_row(method[11])[2] != parser_family:
                    continue
                code = _bounded_code(image, method[3])
                if code is None:
                    continue
                cases = _tag_cases(code)
                if cases:
                    candidates.append((method_index, cases, code))
            if candidates:
                candidates.sort(key=lambda item: (-len(item[1]), item[0]))
                best_count = len(candidates[0][1])
                best = [item for item in candidates if len(item[1]) == best_count]
                signatures = {
                    tuple(
                        sorted(
                            (
                                int(case["field_number"]),
                                int(case["wire"]),
                                int(case["raw_tag"]),
                            )
                            for case in item[1]
                        )
                    )
                    for item in best
                }
                if len(signatures) != 1:
                    raise AcquisitionError(
                        "runtime protocol parser method is ambiguous for type "
                        f"{type_index}: equal-size candidates disagree"
                    )
                method_index, cases, code = best[0]
                _reject_unsupported_wire_tags(
                    message_name=runtime.renderer.root_name(type_index),
                    rows=cases,
                    source="bounded runtime parser",
                )
                parser_candidates[type_index] = (method_index, cases)
                method_code[method_index] = code
            writer_options: list[
                tuple[int, list[dict[str, int]], bytes]
            ] = []
            for method_index in methods_by_type[type_index]:
                method = runtime.method_row(method_index)
                if method[10] != 1 or method[4] != void_descriptor:
                    continue
                if runtime.parameter_row(method[11])[2] != writer_family:
                    continue
                code = _bounded_code(image, method[3])
                if code is None:
                    continue
                direct_tags = _direct_tag_writes(code)
                if not direct_tags:
                    continue
                writer_options.append((method_index, direct_tags, code))
            if writer_options:
                writer_options.sort(key=lambda item: (-len(item[1]), item[0]))
                best_count = len(writer_options[0][1])
                best = [
                    item for item in writer_options if len(item[1]) == best_count
                ]
                signatures = {
                    tuple(
                        sorted(
                            (
                                int(tag["field_number"]),
                                int(tag["wire"]),
                                int(tag["raw_tag"]),
                            )
                            for tag in item[1]
                        )
                    )
                    for item in best
                }
                if len(signatures) != 1:
                    raise AcquisitionError(
                        "runtime protocol writer method is ambiguous for type "
                        f"{type_index}: equal-size candidates disagree"
                    )
                method_index, direct_tags, code = best[0]
                _reject_unsupported_wire_tags(
                    message_name=runtime.renderer.root_name(type_index),
                    rows=direct_tags,
                    source="bounded runtime writer",
                )
                writer_candidates[type_index] = (method_index, direct_tags)
                writer_code[method_index] = code

        for type_index in selected_types:
            static_constructors: list[bytes] = []
            for method_index in methods_by_type[type_index]:
                method = runtime.method_row(method_index)
                if (
                    method[9] & METHOD_DETAIL_CONSTRUCTOR
                    and method[5] & 0x10
                ):
                    code = _bounded_code(image, method[3])
                    if code is not None:
                        static_constructors.append(code)
            slots: dict[int, int] = {}
            for constructor in static_constructors:
                for slot, tag in _formatter_tag_slots(constructor).items():
                    previous = slots.get(slot)
                    if previous is not None and previous != tag:
                        raise AcquisitionError(
                            "runtime protocol class codec slots conflict"
                        )
                    slots[slot] = tag
            if not slots:
                continue


            bodies: list[tuple[int, int, list[dict[str, int]]]] = []
            for method_index in methods_by_type[type_index]:
                method = runtime.method_row(method_index)
                if (
                    method[9] & METHOD_DETAIL_CONSTRUCTOR
                    or method[5] & 0x10
                    or not method[3]
                ):
                    continue
                body = writer_code.get(method_index)
                if body is None:
                    body = _bounded_code(image, method[3])
                if body is None:
                    continue
                relevant_loads = [
                    (load_offset, slot)
                    for load_offset, slot in _static_slot_loads(body)
                    if slot in slots
                ]
                if not relevant_loads:
                    continue
                try:
                    base_registers = {_this_register(body), 1}
                except AcquisitionError as error:
                    if str(error) != (
                        "runtime protocol method instance argument is not structurally resolved"
                    ):
                        raise
                    base_registers = {1}
                base_registers.update(_early_this_aliases(body))
                whole_accesses: list[dict[str, Any]] = []
                for base_register in sorted(base_registers):
                    for access in _memory_accesses(
                        body, 0, len(body), base_register=base_register
                    ):
                        if access not in whole_accesses:
                            whole_accesses.append(access)
                whole_accesses.sort(key=lambda item: int(item["code_offset"]))
                rows: list[dict[str, int]] = []
                for load_offset, slot in relevant_loads:
                    tag = slots.get(slot)
                    if tag is None:
                        continue
                    preceding = [
                        item
                        for item in whole_accesses
                        if 0 <= load_offset - int(item["code_offset"]) <= 128
                        and item["access"] in {"read", "read_write"}


                        and (tag & 7 != 2 or int(item["width"]) == 8)
                    ]
                    if not preceding:
                        continue
                    field_access = preceding[-1]
                    row = {
                        "field_number": tag >> 3,
                        "wire": tag & 7,
                        "raw_tag": tag,
                        "object_offset": int(field_access["object_offset"]),
                        "code_offset": int(field_access["code_offset"]),
                    }
                    if row not in rows:
                        rows.append(row)
                if rows:
                    is_writer = int(
                        type_index in writer_candidates
                        and writer_candidates[type_index][0] == method_index
                    )
                    bodies.append((len(rows), is_writer, rows))
            if bodies:
                bodies.sort(key=lambda item: (-item[0], -item[1]))
                best_score = bodies[0][:2]
                best = [item for item in bodies if item[:2] == best_score]


                merged: list[dict[str, int]] = []
                for _count, _is_writer, rows in best:
                    for row in rows:
                        if row not in merged:
                            merged.append(row)
                formatter_candidates[type_index] = sorted(
                    merged,
                    key=lambda row: (
                        int(row["field_number"]),
                        int(row["wire"]),
                        int(row["object_offset"]),
                        int(row["code_offset"]),
                    ),
                )

    header_deltas: Counter[int] = Counter()
    access_cache: dict[tuple[int, int], list[dict[str, Any]]] = {}
    for type_index, (method_index, cases) in parser_candidates.items():
        code = method_code[method_index]
        base_register = _this_register(code)
        starts = sorted(
            {int(item["case_start"]) for item in cases if item["case_start"] is not None}
        )
        native_offsets = {
            int(field["managed_offset"])
            for field in fields_by_type[type_index]
            if 0 <= int(field["managed_offset"]) <= 0xFFFFFFFF
        }
        for case in cases:
            start = case.get("case_start")
            if start is None:
                continue
            following = [value for value in starts if value > start]
            end = following[0] if following else len(code)
            accesses = _memory_accesses(
                code, start, end, base_register=base_register
            )
            if not any(
                0 <= int(access["object_offset"]) - native_offset <= 64
                for access in accesses for native_offset in native_offsets
            ):
                for hoisted in _hoisted_parser_field_addresses(
                    code, start, end, first_case_start=starts[0],
                    base_register=base_register,
                ):
                    if hoisted not in accesses:
                        accesses.append(hoisted)
            access_cache[(type_index, int(start))] = accesses
            for access in accesses:
                for native_offset in native_offsets:
                    delta = int(access["object_offset"]) - native_offset
                    if 0 <= delta <= 64:
                        header_deltas[delta] += 1
    ranked_deltas = header_deltas.most_common(2)
    if (
        not ranked_deltas
        or ranked_deltas[0][1] < 128
        or len(ranked_deltas) > 1
        and ranked_deltas[0][1] * 2 <= ranked_deltas[1][1] * 3
    ):
        raise AcquisitionError(
            "runtime protocol object header size is ambiguous: "
            + repr(header_deltas.most_common(16))
        )
    object_header = ranked_deltas[0][0]

    mapped_tags = 0
    ambiguous_tags = 0
    writer_mapped_tags = 0
    formatter_mapped_tags = 0
    cross_source_conflicts = 0
    mapped_field_indexes: set[int] = set()
    messages_with_parser = len(parser_candidates)
    messages_with_writer = len(writer_candidates)
    parserless_type_indexes = sorted(set(selected_types) - set(parser_candidates))
    candidate_tag_count = 0
    message_rows: list[dict[str, Any]] = []
    for type_index in selected_types:
        fields = fields_by_type[type_index]
        by_object_offset: dict[int, list[dict[str, Any]]] = {}
        for field in fields:
            by_object_offset.setdefault(
                int(field["managed_offset"]) + object_header, []
            ).append(field)

        def match_field_accesses(
            accesses: list[dict[str, Any]],
        ) -> list[dict[str, Any]]:
            matched: list[dict[str, Any]] = []
            seen: set[tuple[int, int, str, int, int]] = set()
            for access in accesses:
                for field in by_object_offset.get(
                    int(access["object_offset"]), []
                ):
                    key = (
                        int(field["field_index"]),
                        int(access["code_offset"]),
                        str(access["access"]),
                        int(access["width"]),
                        int(access["object_offset"]),
                    )
                    if key in seen:
                        continue
                    seen.add(key)
                    matched.append({**access, **field})
            return matched
        candidate_tags: dict[tuple[int, int], dict[str, Any]] = {}

        def add_candidate_tag(
            *, field_number: int, wire: int, source: str,
            wire_evidence: str = "exact-tag",
        ) -> None:
            key = (int(field_number), int(wire))
            item = candidate_tags.setdefault(
                key,
                {
                    "field_number": key[0],
                    "wire": key[1],
                    "raw_tag": key[0] << 3 | key[1],
                    "sources": [],
                    "wire_evidence_sources": [],
                },
            )
            if source not in item["sources"]:
                item["sources"].append(source)
            if wire_evidence not in item["wire_evidence_sources"]:
                item["wire_evidence_sources"].append(wire_evidence)

        parser = parser_candidates.get(type_index)
        if parser:
            for case in parser[1]:
                add_candidate_tag(
                    field_number=case["field_number"],
                    wire=case["wire"],
                    source="bounded-parser-tag-case",
                    wire_evidence=str(case.get("wire_evidence", "exact-tag")),
                )
        writer = writer_candidates.get(type_index)
        if writer:
            for tag in writer[1]:
                add_candidate_tag(
                    field_number=tag["field_number"],
                    wire=tag["wire"],
                    source="bounded-writer-varint-tag",
                )
        for formatter in formatter_candidates.get(type_index, []):
            add_candidate_tag(
                field_number=formatter["field_number"],
                wire=formatter["wire"],
                source="bounded-static-formatter-tag",
            )

        mappings: list[dict[str, Any]] = []
        candidate = parser_candidates.get(type_index)
        if candidate:
            _method_index, cases = candidate
            case_starts = sorted(
                {
                    int(item["case_start"])
                    for item in cases
                    if item.get("case_start") is not None
                }
            )
            parser_code = method_code[_method_index]
            base_register = _this_register(parser_code)
            for case in cases:
                start = case.get("case_start")
                if start is None:
                    continue
                following = [value for value in case_starts if value > int(start)]
                case_end = following[0] if following else len(parser_code)
                accesses = access_cache.get((type_index, int(start)), [])
                matched = match_field_accesses(accesses)
                covered_offsets = {
                    int(item["object_offset"]) for item in matched
                }
                case_element_rows: list[dict[str, Any]] = []


                for field in fields:
                    for element_role, element_width in (
                        _collection_element_widths(
                            runtime, int(field["descriptor"])
                        )
                    ):
                        element_transfer = _parser_scalar_transfer(
                            parser_code,
                            int(start),
                            case_end,
                            base_register=base_register,
                            object_offset=(
                                int(field["managed_offset"]) + object_header
                            ),
                            width=element_width,
                            allow_call_terminus=True,
                        )
                        if (
                            element_transfer.get("status") != "proven"
                            or element_transfer.get("store_kind")
                            != "call-argument"
                        ):
                            continue
                        element_parser_pointer = runtime.method_row(
                            _method_index
                        )[3]
                        element_target_offset = element_transfer.get(
                            "call_target_offset"
                        )
                        element_target = (
                            element_parser_pointer
                            + int(element_target_offset)
                            if type(element_target_offset) is int
                            else None
                        )
                        element_store_indexes = (
                            method_indexes_by_code_pointer.get(
                                element_target, []
                            )
                            if element_target is not None
                            else []
                        )
                        if len(element_store_indexes) != 1:
                            continue
                        element_store_row = runtime.method_row(
                            element_store_indexes[0]
                        )
                        element_owner_type_index = int(element_store_row[0])
                        element_owner_name = (
                            runtime.renderer.root_name(
                                element_owner_type_index
                            )
                            if 0 <= element_owner_type_index
                            < runtime.type_count
                            else ""
                        )
                        try:
                            element_field_type_name = runtime.renderer.render(
                                int(field["descriptor"])
                            )
                        except Exception:
                            continue
                        if (
                            "<" not in element_owner_name
                            or "<" not in element_field_type_name
                            or element_owner_name.split("<", 1)[0]
                            != element_field_type_name.split("<", 1)[0]
                        ):
                            continue
                        element_transfer["store_method_owner_only"] = {
                            "method_index_owner_only": (
                                element_store_indexes[0]
                            ),
                            "owner_type_index_owner_only": (
                                element_owner_type_index
                            ),
                            "owner_type_name_owner_only": (
                                element_owner_name
                            ),
                            "field_type_name_owner_only": (
                                element_field_type_name
                            ),
                            "name_owner_only": runtime.method_name(
                                element_store_indexes[0], element_store_row
                            ),
                            "call_target_owner_only": element_target,
                            "argument_index_owner_only": int(
                                element_transfer.get("argument_index", -1)
                            ),
                        }
                        element_transfer[
                            "collection_element_role_owner_only"
                        ] = element_role
                        case_element_rows.append(
                            {
                                "field_index": int(field["field_index"]),
                                "access": "write",
                                "width": element_width // 8,
                                "code_offset": int(start),
                                "collection_element_role_owner_only": (
                                    element_role
                                ),
                                "parser_body_transfer_owner_only": (
                                    element_transfer
                                ),
                            }
                        )
                callee_rows = _parser_case_callee_rows(
                    image=image,
                    parser_code=parser_code,
                    start=int(start),
                    end=case_end,
                    base_register=base_register,
                    parser_method_pointer=runtime.method_row(_method_index)[3],
                    by_object_offset=by_object_offset,
                    covered_offsets=covered_offsets,
                    method_indexes_by_code_pointer=method_indexes_by_code_pointer,
                    runtime=runtime,
                )


                grouped_rows: dict[int, list[dict[str, Any]]] = defaultdict(list)
                for row in callee_rows:
                    grouped_rows[int(row["access_row"]["field_index"])].append(row)
                for field_index, rows_for_field in grouped_rows.items():
                    signatures = {
                        (
                            tuple(tuple(op) for op in row["transfer"]["ops"]),
                            int(row["transfer"]["width"]),
                            int(row["transfer"]["source_call_target_offset"]),
                        )
                        for row in rows_for_field
                    }
                    already_proven = any(
                        int(item["field_index"]) == field_index
                        and item["access"] in {"write", "read_write"}
                        and isinstance(
                            item.get("parser_body_transfer_owner_only"), Mapping
                        )
                        and item["parser_body_transfer_owner_only"].get("status")
                        == "proven"
                        for item in matched
                    )
                    if already_proven:
                        continue
                    if len(signatures) > 1:
                        matched.append(
                            {
                                **rows_for_field[0]["access_row"],
                                "callee_transfer_owner_only": {
                                    "status": "unproven",
                                    "reason": "ambiguous-callee-transfer",
                                    "proof": "bounded-parser-body-path-analysis",
                                },
                            }
                        )
                        continue
                    row = rows_for_field[0]
                    matched.append(
                        {
                            **row["access_row"],
                            "callee_transfer_owner_only": row["transfer"],
                        }
                    )
                if not matched:
                    continue
                first = matched[0]
                field_access_rows = []
                field_access_rows.extend(case_element_rows)
                for item in matched:
                    access_row = {
                        "field_index": item["field_index"],
                        "access": item["access"],
                        "width": item["width"],
                        "code_offset": item["code_offset"],
                    }
                    if item["access"] in {"write", "read_write"}:
                        if "callee_transfer_owner_only" in item:
                            access_row["parser_body_transfer_owner_only"] = (
                                item["callee_transfer_owner_only"]
                            )
                            field_access_rows.append(access_row)
                            continue
                        if item["width"] in (4, 8):
                            transfer = _parser_scalar_transfer(
                                parser_code,
                                int(start),
                                case_end,
                                base_register=base_register,
                                object_offset=(
                                    int(item["managed_offset"]) + object_header
                                ),
                                width=int(item["width"]) * 8,
                            )
                            if transfer.get("status") == "proven":
                                parser_pointer = runtime.method_row(
                                    _method_index
                                )[3]
                                transfer[
                                    "parser_method_code_pointer_owner_only"
                                ] = parser_pointer
                                offsets = transfer.get(
                                    "reader_call_offsets_owner_only"
                                )
                                if not isinstance(offsets, list) or not offsets:
                                    single = transfer.get("source_call_target_offset")
                                    offsets = [single] if type(single) is int else []
                                readers: list[dict[str, Any]] = []
                                unresolved_readers: list[dict[str, Any]] = []
                                for call_target_offset in offsets:
                                    if type(call_target_offset) is not int:
                                        continue
                                    call_target = parser_pointer + call_target_offset
                                    called_indexes = method_indexes_by_code_pointer.get(
                                        call_target, []
                                    )
                                    if len(called_indexes) == 1:
                                        called_index = called_indexes[0]
                                        called_row = runtime.method_row(called_index)
                                        readers.append({
                                            "method_index_owner_only": called_index,
                                            "owner_type_index_owner_only": called_row[0],
                                            "call_target_owner_only": call_target,
                                            "code_pointer_owner_only": called_row[3],
                                            "name_owner_only": runtime.method_name(
                                                called_index, called_row
                                            ),
                                            "return_type_owner_only": runtime.method_return(
                                                called_index
                                            ),
                                            "parameter_count_owner_only": called_row[10],
                                        })
                                    else:
                                        unresolved_readers.append({
                                            "status": "unresolved",
                                            "candidate_count": len(called_indexes),
                                            "call_target_owner_only": call_target,
                                        })
                                if readers:
                                    transfer["reader_method_owner_only"] = readers[0]
                                    transfer["reader_methods_owner_only"] = readers
                                if unresolved_readers:
                                    transfer["reader_method_resolution"] = (
                                        unresolved_readers[0]
                                    )
                                if transfer.get("store_kind") == "call-argument":
                                    store_target_offset = transfer.get(
                                        "call_target_offset"
                                    )
                                    store_target = (
                                        parser_pointer + int(store_target_offset)
                                        if type(store_target_offset) is int
                                        else None
                                    )
                                    store_indexes = (
                                        method_indexes_by_code_pointer.get(
                                            store_target, []
                                        )
                                        if store_target is not None
                                        else []
                                    )
                                    if len(store_indexes) != 1:
                                        transfer = {
                                            "status": "unproven",
                                            "reason": (
                                                "collection-store-callee-unresolved"
                                            ),
                                            "proof": (
                                                "bounded-parser-body-path-analysis"
                                            ),
                                        }
                                    else:
                                        store_row = runtime.method_row(
                                            store_indexes[0]
                                        )
                                        owner_type_index = int(store_row[0])
                                        owner_name = (
                                            runtime.renderer.root_name(
                                                owner_type_index
                                            )
                                            if 0 <= owner_type_index
                                            < runtime.type_count
                                            else ""
                                        )
                                        field_type_name = ""
                                        try:
                                            field_type_name = (
                                                runtime.renderer.render(
                                                    int(item["descriptor"])
                                                )
                                            )
                                        except Exception:
                                            field_type_name = ""


                                        if (
                                            "<" not in owner_name
                                            or "<" not in field_type_name
                                            or owner_name.split("<", 1)[0]
                                            != field_type_name.split("<", 1)[0]
                                        ):
                                            transfer = {
                                                "status": "unproven",
                                                "reason": (
                                                    "collection-store-callee-"
                                                    "is-not-a-collection"
                                                ),
                                                "proof": (
                                                    "bounded-parser-body-path-"
                                                    "analysis"
                                                ),
                                            }
                                        else:
                                            transfer["store_method_owner_only"] = {
                                                "method_index_owner_only": (
                                                    store_indexes[0]
                                                ),
                                                "owner_type_index_owner_only": (
                                                    owner_type_index
                                                ),
                                                "owner_type_name_owner_only": (
                                                    owner_name
                                                ),
                                                "field_type_name_owner_only": (
                                                    field_type_name
                                                ),
                                                "name_owner_only": (
                                                    runtime.method_name(
                                                        store_indexes[0],
                                                        store_row,
                                                    )
                                                ),
                                                "call_target_owner_only": (
                                                    store_target
                                                ),
                                                "argument_index_owner_only": int(
                                                    transfer.get(
                                                        "argument_index", -1
                                                    )
                                                ),
                                            }
                            access_row["parser_body_transfer_owner_only"] = transfer
                        else:
                            access_row["parser_body_transfer_owner_only"] = {
                                "status": "unproven",
                                "reason": (
                                    "non-scalar-store-width"
                                    f":{int(item['width'])}"
                                    f"@0x{int(item['code_offset']):x}"
                                ),
                                "proof": "bounded-parser-body-path-analysis",
                            }


                    if item["access"] in {"write", "read_write"}:
                        for element_role, element_width in (
                            _collection_element_widths(
                                runtime, int(item.get("descriptor", 0))
                            )
                        ):
                            element_transfer = _parser_scalar_transfer(
                                parser_code,
                                int(start),
                                case_end,
                                base_register=base_register,
                                object_offset=(
                                    int(item["managed_offset"]) + object_header
                                ),
                                width=element_width,
                                allow_call_terminus=True,
                            )
                            if (
                                element_transfer.get("status") != "proven"
                                or element_transfer.get("store_kind")
                                != "call-argument"
                            ):
                                continue
                            element_transfer[
                                "collection_element_role_owner_only"
                            ] = element_role
                            field_access_rows.append(
                                {
                                    "field_index": int(item["field_index"]),
                                    "access": "write",
                                    "width": element_width // 8,
                                    "code_offset": int(item["code_offset"]),
                                    "collection_element_role_owner_only": (
                                        element_role
                                    ),
                                    "parser_body_transfer_owner_only": (
                                        element_transfer
                                    ),
                                }
                            )
                    field_access_rows.append(access_row)
                mappings.append(
                    {
                        "field_number": case["field_number"],
                        "wire": case["wire"],
                        "wire_evidence": str(
                            case.get("wire_evidence", "exact-tag")
                        ),
                        "primary_field_index": first["field_index"],
                        "source": "bounded-parser-tag-case",
                        "field_accesses": field_access_rows,
                    }
                )
                mapped_tags += 1
                mapped_field_indexes.add(first["field_index"])
                ambiguous_tags += len(
                    {int(item["field_index"]) for item in matched}
                ) > 2
        writer = writer_candidates.get(type_index)
        if writer:
            writer_method, tags = writer
            code = writer_code[writer_method]
            base_register = _this_register(code)
            existing = {
                (int(item["field_number"]), int(item["wire"])): item
                for item in mappings
            }
            for tag_index, tag in enumerate(tags):
                start = int(tag["end"])
                end = min(
                    len(code),
                    int(tags[tag_index + 1]["start"])
                    if tag_index + 1 < len(tags)
                    else len(code),
                )
                accesses = _memory_accesses(
                    code, start, end, base_register=base_register
                )
                matched = match_field_accesses(accesses)
                if not matched:
                    continue
                first = matched[0]
                key = (int(tag["field_number"]), int(tag["wire"]))
                previous = existing.get(key)
                if previous is not None:
                    if previous["primary_field_index"] != first["field_index"]:
                        cross_source_conflicts += 1
                        if previous.get("source") == "bounded-writer-varint-tag":
                            mappings.append(
                                {
                                    "field_number": tag["field_number"],
                                    "wire": tag["wire"],
                                    "primary_field_index": first["field_index"],
                                    "source": "bounded-writer-varint-tag",
                                    "field_accesses": [
                                        {
                                            "field_index": value["field_index"],
                                            "access": value["access"],
                                            "width": value["width"],
                                            "code_offset": value["code_offset"],
                                        }
                                        for value in matched
                                    ],
                                }
                            )
                    continue
                item = {
                    "field_number": tag["field_number"],
                    "wire": tag["wire"],
                    "primary_field_index": first["field_index"],
                    "source": "bounded-writer-varint-tag",
                    "field_accesses": [
                        {
                            "field_index": value["field_index"],
                            "access": value["access"],
                            "width": value["width"],
                            "code_offset": value["code_offset"],
                        }
                        for value in matched
                    ],
                }
                mappings.append(item)
                existing[key] = item
                mapped_tags += 1
                writer_mapped_tags += 1
                mapped_field_indexes.add(first["field_index"])
                ambiguous_tags += len(
                    {int(item["field_index"]) for item in matched}
                ) > 2
        existing = {
            (int(item["field_number"]), int(item["wire"])): item
            for item in mappings
        }
        for formatter in formatter_candidates.get(type_index, []):
            fields_at_offset = by_object_offset.get(
                int(formatter["object_offset"]), []
            )
            if not fields_at_offset:
                continue
            field = fields_at_offset[0]
            key = (
                int(formatter["field_number"]),
                int(formatter["wire"]),
            )
            previous = existing.get(key)
            if previous is not None:
                if previous["primary_field_index"] != field["field_index"]:
                    cross_source_conflicts += 1
                    if previous.get("source") == "bounded-static-formatter-tag":
                        mappings.append(
                            {
                                "field_number": formatter["field_number"],
                                "wire": formatter["wire"],
                                "primary_field_index": field["field_index"],
                                "source": "bounded-static-formatter-tag",
                                "field_accesses": [
                                    {
                                        "field_index": field_at_offset["field_index"],
                                        "access": "read",
                                        "width": 8,
                                        "code_offset": formatter["code_offset"],
                                    }
                                    for field_at_offset in fields_at_offset
                                ],
                            }
                        )
                continue
            item = {
                "field_number": formatter["field_number"],
                "wire": formatter["wire"],
                "primary_field_index": field["field_index"],
                "source": "bounded-static-formatter-tag",
                "field_accesses": [
                    {
                        "field_index": field_at_offset["field_index"],
                        "access": "read",
                        "width": 8,
                        "code_offset": formatter["code_offset"],
                    }
                    for field_at_offset in fields_at_offset
                ],
            }
            mappings.append(item)
            existing[key] = item
            mapped_tags += 1
            formatter_mapped_tags += 1
            mapped_field_indexes.update(
                int(field_at_offset["field_index"])
                for field_at_offset in fields_at_offset
            )
        message_rows.append(
            {
                "type_index": type_index,
                "name": runtime.renderer.root_name(type_index),
                "merge_from_method_index": (
                    parser_candidates[type_index][0]
                    if type_index in parser_candidates
                    else None
                ),
                "merge_from_rva": (
                    runtime.method_row(parser_candidates[type_index][0])[3]
                    - binary_image_base
                    if type_index in parser_candidates
                    else None
                ),
                "write_to_method_index": (
                    writer_candidates[type_index][0]
                    if type_index in writer_candidates
                    else None
                ),
                "write_to_rva": (
                    runtime.method_row(writer_candidates[type_index][0])[3]
                    - binary_image_base
                    if type_index in writer_candidates
                    else None
                ),
                "field_count": len(fields),
                "tag_count": len(mappings),
                "candidate_tag_count": len(candidate_tags),
                "fields": fields,
                "mappings": mappings,
                "candidate_tags": sorted(
                    candidate_tags.values(),
                    key=lambda item: (
                        int(item["field_number"]), int(item["wire"])
                    ),
                ),
            }
        )
        candidate_tag_count += len(candidate_tags)

    return {
        "schema": RUNTIME_PROTO_ANALYSIS_SCHEMA,
        "status": "analyzed",
        "target": receipt["target"],
        "inputs": {
            "native_output_receipt": file_identity(
                native_output_receipt.expanduser().resolve()
            ),
            "proto_field_type_model": file_identity(model_path),
            "proto_field_type_inventory": file_identity(inventory_path),
        },
        "counts": {
            "message_count": len(selected_types),
            "instance_field_count": header[5],
            "messages_with_bounded_parser": messages_with_parser,
            "messages_with_bounded_writer": messages_with_writer,
            "mapped_tag_count": mapped_tags,
            "candidate_tag_count": candidate_tag_count,
            "writer_only_mapped_tag_count": writer_mapped_tags,
            "formatter_mapped_tag_count": formatter_mapped_tags,
            "mapped_serialized_field_count": len(mapped_field_indexes),
            "ambiguous_tag_count": ambiguous_tags,
            "cross_source_mapping_conflict_count": cross_source_conflicts,
            "group_wire_tag_count_in_selected_bounded_parsers": 0,
        },
        "group_wire_audit": {
            "wire_types_checked": [3, 4, 6, 7],
            "selected_message_count": len(selected_types),
            "selected_bounded_parser_count": len(parser_candidates),
            "parserless_message_type_indexes_owner_only": parserless_type_indexes,
            "observed_group_wire_tag_count": 0,
            "disposition": "fail-closed-if-observed-or-uncovered-serialized-message",
        },
        "stream_families_owner_only": [
            {
                "descriptor": descriptor,
                "method_count": count,
                "metrics": dict(family_metrics.get(descriptor, {})),
            }
            for descriptor, count in families
        ],
        "parser_family_descriptor_owner_only": parser_family,
        "writer_family_descriptor_owner_only": writer_family,
        "object_header_bytes": object_header,
        "object_header_support": ranked_deltas[0][1],
        "messages_owner_only": message_rows,
        "policy": {
            "dominant_base_runtime_derived": True,
            "stream_role_code_derived": True,
            "object_header_runtime_code_derived": True,
            "bounded_pe_functions_only": True,
            "saved_reference_generation_seed_used": False,
            "fixed_class_name_used": False,
            "fixed_stream_type_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
            "raw_method_and_type_descriptors_owner_only": True,
        },
    }
