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

from concurrent.futures import ThreadPoolExecutor

from alpha.p12 import _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.h04 import MemorySnapshot
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p18 import _ANCESTRY_HEADER, _ANCESTRY_MAGIC, _ANCESTRY_RECORD, _ANCESTRY_VERSION
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA, _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.h02 import file_identity, read_json


RUNTIME_TYPE_GRAPH_PLAN_SCHEMA = "alpha.runtime-type-graph-plan/v1"
RUNTIME_TYPE_GRAPH_STATUS_SCHEMA = "alpha.runtime-type-graph-status/v1"
RUNTIME_TYPE_GRAPH_SCHEMA = "alpha.runtime-type-graph-inventory/v1"
RUNTIME_TYPE_GRAPH_MAGIC = b"ALPHATG1"
RUNTIME_TYPE_GRAPH_VERSION = 1


RUNTIME_TYPE_GRAPH_BATCH_TYPES = 512
RUNTIME_TYPE_GRAPH_HEADER = struct.Struct(
    "<8sIIIIQQQQQ64s64s64s64s"
)
RUNTIME_TYPE_GRAPH_RECORD = struct.Struct("<IIQQQQIIQQ")
_GRAPH_POOL_QWORD = struct.Struct("<Q")

_REQUIRED_OPERATIONS = (
    "type.base_type",
    "type.interfaces",
    "type.is_generic",
    "type.generic_definition",
    "type.is_generic_definition",
    "type.generic_arguments",
    "type.element_type",
)


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime type graph {label} is not owner-only")
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime type graph {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(f"runtime type graph {label} digest is invalid")
    return value


def _binding(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    ancestry_inventory: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    identity = file_identity(binary)
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantics"
    )
    type_model_path = _owner_file(
        type_identity_model, label="type identity model"
    )
    type_inventory_path = _owner_file(
        type_identity_inventory, label="type identity inventory"
    )
    ancestry_path = _owner_file(ancestry_inventory, label="ancestry inventory")
    semantics = read_json(semantics_path)
    type_model = read_json(type_model_path)
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
    } if isinstance(semantics, dict) else {}
    if (
        semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary", {}).get("sha256") != identity["sha256"]
        or semantics.get("checks", {}).get("all_operations_resolved") is not True
        or semantics.get("behavior_evidence", {}).get(
            "fresh_runtime_observation"
        ) is not True
        or set(_REQUIRED_OPERATIONS) - set(operations)
        or any(
            operations[key].get("semantic_identity_resolved") is not True
            or not isinstance(operations[key].get("method_pointer"), int)
            or operations[key]["method_pointer"] <= 0
            or not isinstance(operations[key].get("metadata_pointer"), int)
            or operations[key]["metadata_pointer"] <= 0
            for key in _REQUIRED_OPERATIONS
        )
    ):
        raise AcquisitionError("runtime type graph reflection binding is stale")
    type_inventory_identity = file_identity(type_inventory_path)
    ancestry_identity = file_identity(ancestry_path)
    snapshot_record = type_model.get("inputs", {}).get("snapshot")
    snapshot_path = _owner_file(
        Path(snapshot_record["path"]), label="bound memory snapshot"
    ) if isinstance(snapshot_record, dict) and isinstance(
        snapshot_record.get("path"), str
    ) else None
    if (
        not isinstance(type_model, dict)
        or type_model.get("schema") != RUNTIME_TYPE_IDENTITY_SCHEMA
        or type_model.get("status") != "runtime-validated"
        or type_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or not all(type_model.get("checks", {}).values())
        or type_model.get("identity_inventory", {}).get("sha256")
        != type_inventory_identity["sha256"]
        or type_model.get("inputs", {}).get("ancestry_inventory", {}).get(
            "sha256"
        )
        != ancestry_identity["sha256"]
        or type_model.get("inputs", {}).get("reflection_semantics", {}).get(
            "sha256"
        )
        != file_identity(semantics_path)["sha256"]
        or snapshot_path is None
        or file_identity(snapshot_path)["sha256"]
        != snapshot_record.get("sha256")
    ):
        raise AcquisitionError("runtime type graph identity binding is stale")
    plan_path = _owner_file(
        type_model_path.parent / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    status_path = _owner_file(
        type_model_path.parent / "runtime-type-identity-status.private.json",
        label="type identity status",
    )
    type_plan = read_json(plan_path)
    type_status = read_json(status_path)
    process_id = type_plan.get("target", {}).get("process_id")
    image_base = type_plan.get("target", {}).get("image_base_owner_only")
    image_bytes = type_plan.get("target", {}).get("image_bytes")
    runtime_type_class = type_plan.get("runtime_classes_owner_only", {}).get(
        "runtime_type"
    )
    handle_qword = type_status.get("runtime_type_handle_qword_owner_only")
    if (
        type_status.get("status") != "complete"
        or type_status.get("fresh_runtime_observation") is not True
        or not isinstance(process_id, int)
        or process_id <= 0
        or not isinstance(image_base, int)
        or image_base <= 0
        or not isinstance(image_bytes, int)
        or image_bytes <= 0
        or not isinstance(runtime_type_class, int)
        or runtime_type_class <= 0
        or not isinstance(handle_qword, int)
        or not 2 <= handle_qword < 16
    ):
        raise AcquisitionError("runtime type graph live binding is invalid")
    identity_raw = type_inventory_path.read_bytes()
    ancestry_raw = ancestry_path.read_bytes()
    if (
        len(identity_raw) < _IDENTITY_HEADER.size
        or len(ancestry_raw) < _ANCESTRY_HEADER.size
    ):
        raise AcquisitionError("runtime type graph input is truncated")
    identity_header = _IDENTITY_HEADER.unpack_from(identity_raw)
    ancestry_header = _ANCESTRY_HEADER.unpack_from(ancestry_raw)
    type_count = identity_header[5]
    if (
        identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or identity_header[2] != _IDENTITY_HEADER.size
        or identity_header[3] != _IDENTITY_RECORD.size
        or identity_header[4]
        or identity_header[6] != image_base
        or identity_header[7] != image_bytes
        or _digest(identity_header[9], label="identity executable")
        != identity["sha256"]
        or ancestry_header[0] != _ANCESTRY_MAGIC
        or ancestry_header[1] != _ANCESTRY_VERSION
        or ancestry_header[2] != _ANCESTRY_RECORD.size
        or ancestry_header[3]
        or ancestry_header[4] != type_count
        or ancestry_header[5] != image_base
        or ancestry_header[6] != image_bytes
        or _digest(ancestry_header[7], label="ancestry executable")
        != identity["sha256"]
        or _IDENTITY_HEADER.size + type_count * _IDENTITY_RECORD.size
        > len(identity_raw)
        or _ANCESTRY_HEADER.size + type_count * _ANCESTRY_RECORD.size
        != len(ancestry_raw)
    ):
        raise AcquisitionError("runtime type graph input binding is invalid")
    return {
        "binary": identity,
        "semantics": file_identity(semantics_path),
        "type_identity_model": file_identity(type_model_path),
        "type_identity_inventory": type_inventory_identity,
        "type_identity_plan": file_identity(plan_path),
        "type_identity_status": file_identity(status_path),
        "ancestry_inventory": ancestry_identity,
        "snapshot": file_identity(snapshot_path),
        "process_id": process_id,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "type_count": type_count,
        "runtime_type_class": runtime_type_class,
        "handle_qword": handle_qword,
        "operations": {
            key: {
                "pointer": operations[key]["method_pointer"],
                "metadata": operations[key]["metadata_pointer"],
            }
            for key in _REQUIRED_OPERATIONS
        },
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ALPHA_BATCH_TYPES ${batch_types}u
#define ALPHA_ARRAY_QWORD_LIMIT 10u
#define ALPHA_MAX_RELATIONS 1048576u

typedef struct identity_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t type_count, image_base, image_bytes, string_bytes;
    char executable_sha256[64], native_sha256[64], semantics_sha256[64];
} identity_header;
typedef struct identity_record {
    uint32_t definition_index, flags;
    uint64_t descriptor, class_pointer, module_pointer, declaring_descriptor;
    uint64_t type_object;
    uint32_t attributes, name_bytes, namespace_bytes, reserved;
    uint64_t name_offset, namespace_offset;
} identity_record;
typedef struct graph_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t type_count, interface_count, generic_argument_count;
    uint64_t image_base, image_bytes;
    char executable_sha256[64], identity_sha256[64];
    char ancestry_sha256[64], semantics_sha256[64];
} graph_header;
typedef struct graph_record {
    uint32_t definition_index, flags;
    uint64_t descriptor, base_descriptor, element_descriptor;
    uint64_t generic_definition_descriptor;
    uint32_t interface_count, generic_argument_count;
    uint64_t interface_start, generic_argument_start;
} graph_record;

_Static_assert(sizeof(identity_header) == $identity_header_bytes, "identity header");
_Static_assert(sizeof(identity_record) == $identity_record_bytes, "identity record");
_Static_assert(sizeof(graph_header) == $graph_header_bytes, "graph header");
_Static_assert(sizeof(graph_record) == $graph_record_bytes, "graph record");

static const char executable_sha256[] = "$executable_sha256";
static const char identity_sha256[] = "$identity_sha256";
static const char ancestry_sha256[] = "$ancestry_sha256";
static const char semantics_sha256[] = "$semantics_sha256";
static const DWORD expected_pid = ${process_id}u;
static const uintptr_t expected_image_base = ${image_base}ull;
static const uint64_t expected_image_bytes = ${image_bytes}ull;
static const uint64_t expected_type_count = ${type_count}ull;
static const uintptr_t runtime_type_class = ${runtime_type_class}ull;
static const uint32_t handle_qword = ${handle_qword}u;
static const uintptr_t base_pointer = ${base_pointer}ull;
static const uintptr_t base_metadata = ${base_metadata}ull;
static const uintptr_t interfaces_pointer = ${interfaces_pointer}ull;
static const uintptr_t interfaces_metadata = ${interfaces_metadata}ull;
static const uintptr_t is_generic_pointer = ${is_generic_pointer}ull;
static const uintptr_t is_generic_metadata = ${is_generic_metadata}ull;
static const uintptr_t generic_definition_pointer = ${generic_definition_pointer}ull;
static const uintptr_t generic_definition_metadata = ${generic_definition_metadata}ull;
static const uintptr_t is_generic_definition_pointer = ${is_generic_definition_pointer}ull;
static const uintptr_t is_generic_definition_metadata = ${is_generic_definition_metadata}ull;
static const uintptr_t generic_arguments_pointer = ${generic_arguments_pointer}ull;
static const uintptr_t generic_arguments_metadata = ${generic_arguments_metadata}ull;
static const uintptr_t element_pointer = ${element_pointer}ull;
static const uintptr_t element_metadata = ${element_metadata}ull;
static const wchar_t identity_path[] = $identity_path;
static const wchar_t ancestry_path[] = $ancestry_path;
static const wchar_t semantics_path[] = $semantics_path;
static const wchar_t output_path[] = $output_path;
static const wchar_t status_path[] = $status_path;

typedef uintptr_t (*instance_noarg)(uintptr_t, uintptr_t);
typedef uint8_t (*instance_bool)(uintptr_t, uintptr_t);
static unsigned char *identity_data;
static identity_record *types;
static graph_record *records;
static uint64_t *interfaces, *generic_arguments;
static uint64_t interface_count, interface_capacity;
static uint64_t generic_argument_count, generic_argument_capacity;
static uint64_t capture_index, completed_types, base_count, element_count;
static uint64_t generic_type_count, generic_definition_count;
static uint32_t array_length_qword, array_vector_qword;
static uint64_t failure_index; static uint32_t failure_kind;
static UINT message_id; static WNDPROC original_proc;
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
static int object_class(uintptr_t object, uintptr_t expected) {
    uintptr_t observed = 0;
    if (!readable(object, sizeof(observed))) return 0;
    memcpy(&observed, (const void *)object, sizeof(observed));
    return observed == expected;
}
static int descriptor_from_type(uintptr_t object, uintptr_t *descriptor) {
    *descriptor = 0;
    if (!object) return 1;
    if (!object_class(object, runtime_type_class)) return 0;
    memcpy(descriptor, (const void *)(object + (uintptr_t)handle_qword * 8u), 8u);
    return readable(*descriptor, 16u);
}
static int derive_type_array(uintptr_t array) {
    if (!array || !readable(array, 80u)) return 0;
    uint32_t found_length = 0, found_vector = 0, matches = 0;
    for (uint32_t l = 1; l < 8; l++) {
        uintptr_t length = 0;
        memcpy(&length, (const void *)(array + (uintptr_t)l * 8u), 8u);
        if (!length || length > 4096u) continue;
        for (uint32_t v = l + 1; v < ALPHA_ARRAY_QWORD_LIMIT; v++) {
            uintptr_t vector = array + (uintptr_t)v * 8u;
            if (!readable(vector, (SIZE_T)length * 8u)) continue;
            uint64_t valid = 0;
            for (; valid < length; valid++) {
                uintptr_t item = 0;
                memcpy(&item, (const void *)(vector + valid * 8u), 8u);
                if (!object_class(item, runtime_type_class)) break;
            }
            if (valid == length) {
                found_length = l; found_vector = v; matches++;
            }
        }
    }
    if (matches != 1) return 0;
    array_length_qword = found_length;
    array_vector_qword = found_vector;
    return 1;
}
static int type_array(uintptr_t array, uintptr_t **items, uint32_t *count) {
    *items = NULL; *count = 0;
    if (!array || !array_length_qword || !array_vector_qword ||
        !readable(array, ((SIZE_T)array_vector_qword + 1u) * 8u)) return 0;
    uintptr_t length = 0;
    memcpy(&length, (const void *)(array + (uintptr_t)array_length_qword * 8u), 8u);
    if (length > 65536u) return 0;
    uintptr_t vector = array + (uintptr_t)array_vector_qword * 8u;
    if (length && !readable(vector, (SIZE_T)length * 8u)) return 0;
    for (uint64_t index = 0; index < length; index++) {
        uintptr_t item = 0;
        memcpy(&item, (const void *)(vector + index * 8u), 8u);
        if (!object_class(item, runtime_type_class)) return 0;
    }
    *items = (uintptr_t *)vector; *count = (uint32_t)length; return 1;
}
static int append_descriptor(
    uint64_t **pool, uint64_t *count, uint64_t *capacity, uint64_t value
) {
    if (!value || *count >= ALPHA_MAX_RELATIONS) return 0;
    if (*count == *capacity) {
        uint64_t next = *capacity ? *capacity * 2u : 65536u;
        if (next > ALPHA_MAX_RELATIONS) next = ALPHA_MAX_RELATIONS;
        uint64_t *grown = realloc(*pool, (SIZE_T)next * sizeof(**pool));
        if (!grown) return 0;
        *pool = grown; *capacity = next;
    }
    (*pool)[(*count)++] = value; return 1;
}
static int read_file(const wchar_t *path, unsigned char **data, SIZE_T *bytes) {
    FILE *input = _wfopen(path, L"rb");
    if (!input || _fseeki64(input, 0, SEEK_END)) return 0;
    *bytes = (SIZE_T)_ftelli64(input);
    if (_fseeki64(input, 0, SEEK_SET)) { fclose(input); return 0; }
    *data = malloc(*bytes ? *bytes : 1u);
    int ok = *data && fread(*data, 1, *bytes, input) == *bytes;
    fclose(input); return ok;
}
static void digest_hex(const unsigned char digest[32], char output[65]) {
    static const char alphabet[] = "0123456789abcdef";
    for (int i=0;i<32;i++){output[i*2]=alphabet[digest[i]>>4];output[i*2+1]=alphabet[digest[i]&15];}
    output[64]=0;
}
static int sha256_file(const wchar_t *path, char output[65]) {
    HANDLE input=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);
    if(input==INVALID_HANDLE_VALUE)return 0;
    BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char *object=NULL,*buffer=NULL,digest[32];
    int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0;
    if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;
    if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;
    while(ok){DWORD count=0;if(!ReadFile(input,buffer,1048576u,&count,NULL)){ok=0;break;}if(!count)break;if(BCryptHashData(hash,buffer,count,0)<0)ok=0;}
    if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)<0)ok=0;if(ok)digest_hex(digest,output);
    if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(input);return ok;
}
static int executable_identity(char output[65]) {
    wchar_t path[32768]; DWORD length=GetModuleFileNameW(NULL,path,32768);
    return length&&length<32768&&sha256_file(path,output);
}

static int derive_layouts(void) {
    instance_noarg get_interfaces = (instance_noarg)interfaces_pointer;
    for (uint64_t index = 0; index < expected_type_count; index++) {
        uintptr_t array = get_interfaces(types[index].type_object, interfaces_metadata);
        if (!array || !readable(array, 80u)) { failure_kind=10;failure_index=index+1u;return 0; }
        if (derive_type_array(array)) return 1;
    }
    failure_kind=11;return 0;
}
static int capture_batch(void) {
    instance_noarg get_base=(instance_noarg)base_pointer;
    instance_noarg get_interfaces=(instance_noarg)interfaces_pointer;
    instance_bool get_is_generic=(instance_bool)is_generic_pointer;
    instance_noarg get_generic_definition=(instance_noarg)generic_definition_pointer;
    instance_bool get_is_generic_definition=(instance_bool)is_generic_definition_pointer;
    instance_noarg get_generic_arguments=(instance_noarg)generic_arguments_pointer;
    instance_noarg get_element=(instance_noarg)element_pointer;
    uint64_t end=capture_index+ALPHA_BATCH_TYPES;if(end>expected_type_count)end=expected_type_count;
    for(;capture_index<end;capture_index++){
        identity_record *source=&types[capture_index];graph_record *target=&records[capture_index];
        if(source->definition_index!=capture_index||!source->descriptor||!object_class(source->type_object,runtime_type_class)){failure_index=capture_index+1u;failure_kind=1;return 0;}
        target->definition_index=(uint32_t)capture_index;target->descriptor=source->descriptor;
        uintptr_t base=get_base(source->type_object,base_metadata);uintptr_t element=get_element(source->type_object,element_metadata);
        uint8_t is_generic=get_is_generic(source->type_object,is_generic_metadata);uint8_t is_definition=get_is_generic_definition(source->type_object,is_generic_definition_metadata);
        uintptr_t definition=is_generic?get_generic_definition(source->type_object,generic_definition_metadata):0;
        uintptr_t interface_array=get_interfaces(source->type_object,interfaces_metadata);uintptr_t argument_array=get_generic_arguments(source->type_object,generic_arguments_metadata);
        uintptr_t *interface_items=NULL,*argument_items=NULL;uint32_t interfaces_here=0,arguments_here=0;
        if(!descriptor_from_type(base,&target->base_descriptor)||!descriptor_from_type(element,&target->element_descriptor)||!descriptor_from_type(definition,&target->generic_definition_descriptor)||!type_array(interface_array,&interface_items,&interfaces_here)||!type_array(argument_array,&argument_items,&arguments_here)){failure_index=capture_index+1u;failure_kind=2;return 0;}
        if((!is_generic&&(is_definition||definition||arguments_here))||(is_definition&&!is_generic)||is_generic&&!definition||is_generic&&!arguments_here){failure_index=capture_index+1u;failure_kind=3;return 0;}
        target->interface_start=interface_count;target->interface_count=interfaces_here;
        for(uint32_t i=0;i<interfaces_here;i++){uintptr_t descriptor=0;if(!descriptor_from_type(interface_items[i],&descriptor)||!append_descriptor(&interfaces,&interface_count,&interface_capacity,descriptor)){failure_index=capture_index+1u;failure_kind=4;return 0;}}
        target->generic_argument_start=generic_argument_count;target->generic_argument_count=arguments_here;
        for(uint32_t i=0;i<arguments_here;i++){uintptr_t descriptor=0;if(!descriptor_from_type(argument_items[i],&descriptor)||!append_descriptor(&generic_arguments,&generic_argument_count,&generic_argument_capacity,descriptor)){failure_index=capture_index+1u;failure_kind=5;return 0;}}
        target->flags=(target->base_descriptor?1u:0u)|(target->element_descriptor?2u:0u)|(is_generic?4u:0u)|(is_definition?8u:0u)|(target->generic_definition_descriptor?16u:0u)|(interfaces_here?32u:0u)|(arguments_here?64u:0u);
        if(target->base_descriptor)base_count++;if(target->element_descriptor)element_count++;if(is_generic)generic_type_count++;if(is_definition)generic_definition_count++;completed_types++;
    }
    return 1;
}
static volatile LONG current_request, request_sequence, callback_active;
static LRESULT CALLBACK window_proc(HWND window,UINT message,WPARAM wparam,LPARAM lparam){
    if(message!=message_id)return CallWindowProcW(original_proc,window,message,wparam,lparam);
    LONG request=(LONG)wparam;
    if(!request||InterlockedCompareExchange(&current_request,0,0)!=request||
       InterlockedCompareExchange(&callback_active,1,0))return 0;


    if(InterlockedCompareExchange(&current_request,0,request)!=request){
        InterlockedExchange(&callback_active,0);return 0;
    }
    LONG action=InterlockedCompareExchange(&callback_action,0,0);
    int ok=action==1?derive_layouts():action==2?capture_batch():0;
    InterlockedExchange(&callback_complete,ok?1:-1);
    InterlockedExchange(&callback_active,0);
    return ok;
}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;
static BOOL CALLBACK select_window(HWND window,LPARAM value){selection*s=(selection*)(uintptr_t)value;DWORD pid=0;RECT bounds;if(!IsWindowVisible(window)||GetWindow(window,GW_OWNER)||!GetWindowRect(window,&bounds)||bounds.right<=bounds.left||bounds.bottom<=bounds.top)return TRUE;GetWindowThreadProcessId(window,&pid);if(pid==s->pid){s->window=window;s->count++;}return TRUE;}
static int dispatch_capture(void){
    selection s={0};s.pid=GetCurrentProcessId();
    if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window){failure_kind=100;failure_index=s.count;return 0;}
    message_id=RegisterWindowMessageW(L"ALPHA v2 current runtime type graph inventory");
    if(!message_id){failure_kind=102;failure_index=GetLastError();return 0;}
    SetLastError(0);
    original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);
    DWORD error=GetLastError();
    if(!original_proc||error!=ERROR_SUCCESS){failure_kind=103;failure_index=error;return 0;}
    int ok=1,layouts_ready=0;uint32_t retries=0;
    while(ok&&(!layouts_ready||capture_index<expected_type_count)){
        DWORD_PTR result=0;uint64_t before=capture_index;
        LONG request=InterlockedIncrement(&request_sequence);
        InterlockedExchange(&callback_action,layouts_ready?2:1);
        InterlockedExchange(&callback_complete,0);
        InterlockedExchange(&current_request,request);
        SetLastError(0);
        int sent=SendMessageTimeoutW(s.window,message_id,(WPARAM)request,0,SMTO_BLOCK,60000,&result)!=0;
        error=GetLastError();
        InterlockedExchange(&current_request,0);


        for(uint32_t wait=0;InterlockedCompareExchange(&callback_active,0,0)&&wait<2000u;wait++)Sleep(1);
        if(InterlockedCompareExchange(&callback_active,0,0)){failure_kind=104;ok=0;break;}
        LONG complete=InterlockedCompareExchange(&callback_complete,0,0);
        if(complete==1){
            if(layouts_ready&&capture_index<=before){failure_kind=108;ok=0;break;}
            layouts_ready=1;retries=0;continue;
        }
        if(complete<0||failure_kind){if(!failure_kind)failure_kind=105;ok=0;break;}
        if(!sent&&retries++<16u){Sleep(250);continue;}
        failure_kind=101;failure_index=error;ok=0;
    }
    InterlockedExchange(&current_request,0);
    SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);


    return ok;
}
static void write_status(const char*status,int written){FILE*out=_wfopen(status_path,L"wb");if(!out)return;fprintf(out,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"completed_type_count\": %llu,\n  \"base_type_count\": %llu,\n  \"element_type_count\": %llu,\n  \"interface_reference_count\": %llu,\n  \"generic_type_count\": %llu,\n  \"generic_definition_count\": %llu,\n  \"generic_argument_reference_count\": %llu,\n  \"array_length_qword_owner_only\": %u,\n  \"array_vector_qword_owner_only\": %u,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"saved_type_graph_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)completed_types,(unsigned long long)base_count,(unsigned long long)element_count,(unsigned long long)interface_count,(unsigned long long)generic_type_count,(unsigned long long)generic_definition_count,(unsigned long long)generic_argument_count,array_length_qword,array_vector_qword,(unsigned long long)failure_index,failure_kind,written?"true":"false");fclose(out);}
static int write_output(void){graph_header header;memset(&header,0,sizeof(header));memcpy(header.magic,"ALPHATG1",8);header.version=$output_version;header.header_bytes=sizeof(header);header.record_bytes=sizeof(graph_record);header.type_count=expected_type_count;header.interface_count=interface_count;header.generic_argument_count=generic_argument_count;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;memcpy(header.executable_sha256,executable_sha256,64);memcpy(header.identity_sha256,identity_sha256,64);memcpy(header.ancestry_sha256,ancestry_sha256,64);memcpy(header.semantics_sha256,semantics_sha256,64);FILE*out=_wfopen(output_path,L"wb");if(!out)return 0;int ok=fwrite(&header,1,sizeof(header),out)==sizeof(header)&&fwrite(records,sizeof(*records),expected_type_count,out)==expected_type_count&&fwrite(interfaces,sizeof(*interfaces),interface_count,out)==interface_count&&fwrite(generic_arguments,sizeof(*generic_arguments),generic_argument_count,out)==generic_argument_count;if(fclose(out))ok=0;if(!ok)_wremove(output_path);return ok;}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char executable[65],identity[65],ancestry[65],semantics[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(executable)||strcmp(executable,executable_sha256)||!sha256_file(identity_path,identity)||strcmp(identity,identity_sha256)||!sha256_file(ancestry_path,ancestry)||strcmp(ancestry,ancestry_sha256)||!sha256_file(semantics_path,semantics)||strcmp(semantics,semantics_sha256)){failure_kind=200;write_status("identity_mismatch",0);return 0;}SIZE_T bytes=0;if(!read_file(identity_path,&identity_data,&bytes)||bytes<sizeof(identity_header)+expected_type_count*sizeof(identity_record)){failure_kind=201;write_status("input_unavailable",0);return 0;}identity_header*header=(identity_header*)identity_data;if(memcmp(header->magic,"ALPHATI1",8)||header->version!=1u||header->type_count!=expected_type_count||header->image_base!=expected_image_base||header->image_bytes!=expected_image_bytes){failure_kind=202;write_status("input_invalid",0);return 0;}types=(identity_record*)(identity_data+sizeof(*header));records=calloc(expected_type_count,sizeof(*records));if(!records){failure_kind=203;write_status("allocation_failed",0);return 0;}if(!dispatch_capture()||completed_types!=expected_type_count){if(!failure_kind)failure_kind=204;write_status("capture_failed",0);return 0;}int ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def runtime_type_graph_source(
    *, binding: dict[str, Any], output_path: Path, status_path: Path
) -> str:
    operations = binding["operations"]
    return _COLLECTOR.substitute(
        {
            "identity_header_bytes": _IDENTITY_HEADER.size,
            "identity_record_bytes": _IDENTITY_RECORD.size,
            "graph_header_bytes": RUNTIME_TYPE_GRAPH_HEADER.size,
            "graph_record_bytes": RUNTIME_TYPE_GRAPH_RECORD.size,
            "batch_types": RUNTIME_TYPE_GRAPH_BATCH_TYPES,
            "output_version": RUNTIME_TYPE_GRAPH_VERSION,
            "status_schema": RUNTIME_TYPE_GRAPH_STATUS_SCHEMA,
            "executable_sha256": binding["binary"]["sha256"],
            "identity_sha256": binding["type_identity_inventory"]["sha256"],
            "ancestry_sha256": binding["ancestry_inventory"]["sha256"],
            "semantics_sha256": binding["semantics"]["sha256"],
            "process_id": binding["process_id"],
            "image_base": binding["image_base"],
            "image_bytes": binding["image_bytes"],
            "type_count": binding["type_count"],
            "runtime_type_class": binding["runtime_type_class"],
            "handle_qword": binding["handle_qword"],
            "base_pointer": operations["type.base_type"]["pointer"],
            "base_metadata": operations["type.base_type"]["metadata"],
            "interfaces_pointer": operations["type.interfaces"]["pointer"],
            "interfaces_metadata": operations["type.interfaces"]["metadata"],
            "is_generic_pointer": operations["type.is_generic"]["pointer"],
            "is_generic_metadata": operations["type.is_generic"]["metadata"],
            "generic_definition_pointer": operations[
                "type.generic_definition"
            ]["pointer"],
            "generic_definition_metadata": operations[
                "type.generic_definition"
            ]["metadata"],
            "is_generic_definition_pointer": operations[
                "type.is_generic_definition"
            ]["pointer"],
            "is_generic_definition_metadata": operations[
                "type.is_generic_definition"
            ]["metadata"],
            "generic_arguments_pointer": operations[
                "type.generic_arguments"
            ]["pointer"],
            "generic_arguments_metadata": operations[
                "type.generic_arguments"
            ]["metadata"],
            "element_pointer": operations["type.element_type"]["pointer"],
            "element_metadata": operations["type.element_type"]["metadata"],
            "identity_path": _wide_literal(
                _windows_z_path(Path(binding["type_identity_inventory"]["path"]))
            ),
            "ancestry_path": _wide_literal(
                _windows_z_path(Path(binding["ancestry_inventory"]["path"]))
            ),
            "semantics_path": _wide_literal(
                _windows_z_path(Path(binding["semantics"]["path"]))
            ),
            "output_path": _wide_literal(_windows_z_path(output_path)),
            "status_path": _wide_literal(_windows_z_path(status_path)),
        }
    )


def prepare_runtime_type_graph_inventory(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    ancestry_inventory: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        ancestry_inventory=ancestry_inventory,
    )
    output_path = output_dir / "runtime-type-graph.private.bin"
    status_path = output_dir / "runtime-type-graph-status.private.json"
    model_path = output_dir / "runtime-type-graph.private.json"
    plan_path = output_dir / "runtime-type-graph-plan.private.json"
    build_dir = _owner_directory(output_dir / "build-type-graph")
    source_path = build_dir / "runtime-type-graph.c"
    injector_source = build_dir / "runtime-type-graph-injector.c"
    injector_path = build_dir / "alpha-runtime-type-graph-injector.exe"
    for stale in (output_path, status_path, model_path):
        stale.unlink(missing_ok=True)
    _private_text(
        source_path,
        runtime_type_graph_source(
            binding=binding, output_path=output_path, status_path=status_path
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-type-graph-"
        + file_identity(source_path)["sha256"][:12]
        + ".dll"
    )
    selected_compiler = _compiler(compiler)


    with ThreadPoolExecutor(max_workers=2) as executor:
        collector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler), "-O2", "-s", "-shared", "-Wall",
                "-Wextra", "-Wformat=2", "-Werror=format",
                str(source_path), "-o", str(collector_path), "-lbcrypt",
            ],
            label="runtime type graph collector",
            source_path=source_path,
            output_path=collector_path,
        )
        injector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler), "-O2", "-s", "-municode", "-Wall",
                "-Wextra", "-Wformat=2", "-Werror=format",
                str(injector_source), "-o", str(injector_path),
            ],
            label="runtime type graph injector",
            source_path=injector_source,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        if not artifact.is_file() or not artifact.stat().st_size:
            raise AcquisitionError(
                f"runtime type graph build did not produce {artifact.name}"
            )
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_TYPE_GRAPH_PLAN_SCHEMA,
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
                "semantics", "type_identity_model", "type_identity_inventory",
                "type_identity_plan", "type_identity_status",
                "ancestry_inventory", "snapshot",
            )
        },
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "contract": {
            "type_count": binding["type_count"],
            "record_bytes": RUNTIME_TYPE_GRAPH_RECORD.size,
        },
        "policy": {
            "same_process_required": True,
            "runtime_array_layout_live_derived": True,
            "ancestry_cross_validation_required": True,
            "raw_pointers_owner_only": True,
            "saved_type_graph_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_TYPE_GRAPH_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "type_count": binding["type_count"],
        "policy": plan["policy"],
    }


def _validate(
    plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, int], dict[str, bool]]:
    output = Path(plan["output_path"]).read_bytes()
    identity = Path(plan["inputs"]["type_identity_inventory"]["path"]).read_bytes()
    ancestry = Path(plan["inputs"]["ancestry_inventory"]["path"]).read_bytes()
    if len(output) < RUNTIME_TYPE_GRAPH_HEADER.size:
        raise AcquisitionError("runtime type graph output is truncated")
    header = RUNTIME_TYPE_GRAPH_HEADER.unpack_from(output)
    type_count, interface_count, argument_count = header[5:8]
    record_start = RUNTIME_TYPE_GRAPH_HEADER.size
    interface_start = record_start + type_count * RUNTIME_TYPE_GRAPH_RECORD.size
    argument_start = interface_start + interface_count * 8
    expected_bytes = argument_start + argument_count * 8
    header_ok = (
        header[0] == RUNTIME_TYPE_GRAPH_MAGIC
        and header[1] == RUNTIME_TYPE_GRAPH_VERSION
        and header[2] == RUNTIME_TYPE_GRAPH_HEADER.size
        and header[3] == RUNTIME_TYPE_GRAPH_RECORD.size
        and header[4] == 0
        and type_count == plan["contract"]["type_count"]
        and header[8] == plan["target"]["image_base_owner_only"]
        and header[9] == plan["target"]["image_bytes"]
        and _digest(header[10], label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[11], label="identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(header[12], label="ancestry")
        == plan["inputs"]["ancestry_inventory"]["sha256"]
        and _digest(header[13], label="semantics")
        == plan["inputs"]["semantics"]["sha256"]
        and expected_bytes == len(output)
    )
    records_ok = header_ok
    ancestry_exact = header_ok
    ancestry_pairs: list[tuple[int, int]] = []
    base_count = element_count = generic_count = generic_definition_count = 0
    observed_interfaces = observed_arguments = 0
    if header_ok:


        output_view = memoryview(output)
        graph_rows = RUNTIME_TYPE_GRAPH_RECORD.iter_unpack(
            output_view[
                record_start
                : record_start + type_count * RUNTIME_TYPE_GRAPH_RECORD.size
            ]
        )
        identity_region = memoryview(identity)[_IDENTITY_HEADER.size :]
        identity_rows = _IDENTITY_RECORD.iter_unpack(
            identity_region[
                : (len(identity_region) // _IDENTITY_RECORD.size)
                * _IDENTITY_RECORD.size
            ]
        )
        ancestry_region = memoryview(ancestry)[_ANCESTRY_HEADER.size :]
        ancestry_rows = _ANCESTRY_RECORD.iter_unpack(
            ancestry_region[
                : (len(ancestry_region) // _ANCESTRY_RECORD.size)
                * _ANCESTRY_RECORD.size
            ]
        )
        interface_values = _GRAPH_POOL_QWORD.iter_unpack(
            output_view[interface_start : interface_start + interface_count * 8]
        )
        argument_values = _GRAPH_POOL_QWORD.iter_unpack(
            output_view[argument_start : argument_start + argument_count * 8]
        )
        for index in range(type_count):
            (
                definition_index, flags, descriptor, base, element, generic_definition,
                interfaces_here, arguments_here, interfaces_at, arguments_at,
            ) = next(graph_rows)
            try:
                identity_row = next(identity_rows)
            except StopIteration:
                raise struct.error(
                    "unpack_from requires a buffer of at least "
                    f"{_IDENTITY_HEADER.size + (index + 1) * _IDENTITY_RECORD.size}"
                    f" bytes for unpacking {_IDENTITY_RECORD.size} bytes at offset "
                    f"{_IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size}"
                    f" (actual buffer size is {len(identity)})"
                ) from None
            try:
                ancestry_row = next(ancestry_rows)
            except StopIteration:
                raise struct.error(
                    "unpack_from requires a buffer of at least "
                    f"{_ANCESTRY_HEADER.size + (index + 1) * _ANCESTRY_RECORD.size}"
                    f" bytes for unpacking {_ANCESTRY_RECORD.size} bytes at offset "
                    f"{_ANCESTRY_HEADER.size + index * _ANCESTRY_RECORD.size}"
                    f" (actual buffer size is {len(ancestry)})"
                ) from None
            if (
                definition_index != index
                or descriptor != identity_row[2]
                or bool(base) != bool(flags & 1)
                or bool(element) != bool(flags & 2)
                or bool(flags & 4) != bool(generic_definition)
                or bool(flags & 8) and not bool(flags & 4)
                or bool(generic_definition) != bool(flags & 16)
                or bool(interfaces_here) != bool(flags & 32)
                or bool(arguments_here) != bool(flags & 64)
                or bool(flags & 4) != bool(arguments_here)
                or interfaces_at != observed_interfaces
                or arguments_at != observed_arguments
                or interfaces_at + interfaces_here > interface_count
                or arguments_at + arguments_here > argument_count
                or flags & ~0x7F
            ):
                records_ok = False
                break
            if base != ancestry_row[4]:
                ancestry_pairs.append((base, ancestry_row[4]))
            for _ in range(interfaces_here):
                if not next(interface_values)[0]:
                    records_ok = False
                    break
            for _ in range(arguments_here):
                if not next(argument_values)[0]:
                    records_ok = False
                    break
            if not records_ok:
                break
            base_count += bool(base)
            element_count += bool(element)
            generic_count += bool(flags & 4)
            generic_definition_count += bool(flags & 8)
            observed_interfaces += interfaces_here
            observed_arguments += arguments_here
    pool_counts_ok = (
        records_ok
        and observed_interfaces == interface_count
        and observed_arguments == argument_count
    )
    if ancestry_exact and ancestry_pairs:
        try:
            with MemorySnapshot(Path(plan["inputs"]["snapshot"]["path"])) as memory:
                ancestry_exact = all(
                    memory.read(runtime_descriptor, 16)
                    == memory.read(native_descriptor, 16)
                    for runtime_descriptor, native_descriptor in ancestry_pairs
                )
        except (OSError, ValueError, KeyError):
            ancestry_exact = False
    counts = {
        "type_count": type_count,
        "base_type_count": base_count,
        "element_type_count": element_count,
        "interface_reference_count": interface_count,
        "generic_type_count": generic_count,
        "generic_definition_count": generic_definition_count,
        "generic_argument_reference_count": argument_count,
    }
    checks = {
        "status_schema": status.get("schema") == RUNTIME_TYPE_GRAPH_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "header_bound": header_ok,
        "records_valid": records_ok,
        "relation_pools_complete": pool_counts_ok,
        "ancestry_exact": ancestry_exact,
        "all_types_captured": status.get("completed_type_count") == type_count,
        "status_base_count_matches": status.get("base_type_count") == base_count,
        "status_element_count_matches": status.get("element_type_count") == element_count,
        "status_interface_count_matches": status.get("interface_reference_count") == interface_count,
        "status_generic_count_matches": status.get("generic_type_count") == generic_count,
        "status_generic_definition_count_matches": status.get("generic_definition_count") == generic_definition_count,
        "status_generic_argument_count_matches": status.get("generic_argument_reference_count") == argument_count,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_type_graph_absent": status.get("saved_type_graph_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get("external_runtime_component_used") is False,
    }
    return counts, checks


def capture_runtime_type_graph_inventory(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    ancestry_inventory: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 900.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_type_graph_inventory(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        ancestry_inventory=ancestry_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan = read_json(output_dir / "runtime-type-graph-plan.private.json")
    env = os.environ.copy()
    env["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    env["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine.expanduser().resolve()), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name),
            env=env,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError("runtime type graph injector could not run") from error
    _private_text(
        output_dir / "runtime-type-graph-injector.private.log",
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
        raise AcquisitionError("runtime type graph injection failed")
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
        raise AcquisitionError("runtime type graph capture timed out")
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime type graph capture failed "
            f"(status={status.get('status')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    _seal_runtime_output(output_path)
    counts, checks = _validate(plan, status)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime type graph validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    model = {
        "schema": RUNTIME_TYPE_GRAPH_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": plan["inputs"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "owner_only": True,
    }
    _private_json(Path(plan["model_path"]), model)
    return {
        "schema": RUNTIME_TYPE_GRAPH_SCHEMA,
        "status": "runtime-validated",
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "inventory": model["inventory"],
    }
