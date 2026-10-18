from alpha.h02 import windows_run as _host_run

import hashlib
import json
import os
import stat
import struct
import subprocess
import time
from collections import defaultdict
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.p15 import RUNTIME_CLASS_SCHEMA
from alpha.p27 import RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
from alpha.p22 import RUNTIME_METHOD_DETAIL_HEADER, RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_METHOD, RUNTIME_METHOD_DETAIL_SCHEMA, RUNTIME_METHOD_DETAIL_VERSION
from alpha.p19 import _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.h02 import atomic_write_json, file_identity, read_json


RUNTIME_CONSTRUCTED_METHOD_SCHEMA = (
    "alpha.runtime-constructed-method-inventory/v2"
)
RUNTIME_CONSTRUCTED_METHOD_STATUS_SCHEMA = (
    "alpha.runtime-constructed-method-inventory-status/v2"
)
RUNTIME_CONSTRUCTED_METHOD_MAGIC = b"ALPHACM2"
RUNTIME_CONSTRUCTED_METHOD_VERSION = 2
RUNTIME_CONSTRUCTED_METHOD_HEADER = struct.Struct(
    "<8sIIIIQQQQQQ64s64s64s64s"
)
RUNTIME_CONSTRUCTED_METHOD_CLASS = struct.Struct("<QQIIIIQ")
RUNTIME_CONSTRUCTED_METHOD_CANDIDATE_QWORDS = 8
RUNTIME_CONSTRUCTED_METHOD_RECORD = struct.Struct(
    f"<QIIQ{RUNTIME_CONSTRUCTED_METHOD_CANDIDATE_QWORDS}Q"
)

_SEED_MAGIC = b"ALPHACX1"
_SEED_VERSION = 1
_SEED_HEADER = struct.Struct("<8sIIIIQQQQQQQQQ64s64s64s64s")
_SEED_CLASS = struct.Struct("<QQIIIIQ")
_SEED_DEFINITION = struct.Struct("<QIIIIQ")
_SEED_METHOD = struct.Struct("<IIQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime constructed method {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime constructed method {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime constructed method {label} digest is invalid"
        )
    return value


def _binding(
    *,
    binary: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    native_helper_model: Path,
    class_model: Path,
) -> dict[str, Any]:
    binary_identity = file_identity(binary.expanduser().resolve())
    constructed_model_path = _owner_file(
        constructed_generic_model, label="constructed generic model"
    )
    constructed_path = _owner_file(
        constructed_generic_inventory, label="constructed generic inventory"
    )
    method_model_path = _owner_file(
        method_detail_model, label="method detail model"
    )
    method_path = _owner_file(
        method_detail_inventory, label="method detail inventory"
    )
    helper_path = _owner_file(native_helper_model, label="native helper model")
    class_path = _owner_file(class_model, label="class model")
    constructed_model_data = read_json(constructed_model_path)
    method_model_data = read_json(method_model_path)
    helper_data = read_json(helper_path)
    class_data = read_json(class_path)
    constructed_identity = file_identity(constructed_path)
    method_identity = file_identity(method_path)
    class_identity = file_identity(class_path)
    get_methods = (
        helper_data.get("helpers", {}).get("class_get_methods", {})
        if isinstance(helper_data, dict)
        else {}
    )
    method_pointer_qword = (
        class_data.get("layout", {}).get("method_pointer_qword")
        if isinstance(class_data, dict)
        else None
    )
    if (
        not isinstance(constructed_model_data, dict)
        or constructed_model_data.get("schema")
        != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA
        or constructed_model_data.get("status") != "runtime-validated"
        or constructed_model_data.get("target", {}).get("executable_sha256")
        != binary_identity["sha256"]
        or constructed_model_data.get("inventory") != constructed_identity
        or not constructed_model_data.get("checks")
        or not all(constructed_model_data["checks"].values())
        or not isinstance(method_model_data, dict)
        or method_model_data.get("schema") != RUNTIME_METHOD_DETAIL_SCHEMA
        or method_model_data.get("status") != "runtime-validated"
        or method_model_data.get("target", {}).get("executable_sha256")
        != binary_identity["sha256"]
        or method_model_data.get(
            "inventory", method_model_data.get("method_detail_inventory")
        )
        != method_identity
        or not method_model_data.get("checks")
        or not all(method_model_data["checks"].values())
        or method_model_data.get("inputs", {}).get("class_model")
        != class_identity
        or not isinstance(helper_data, dict)
        or helper_data.get("binary", {}).get("sha256")
        != binary_identity["sha256"]
        or helper_data.get("checks", {}).get(
            "class_method_iterator_runtime_validated"
        )
        is not True
        or helper_data.get("checks", {}).get(
            "class_method_iterator_structurally_unique"
        )
        is not True
        or not isinstance(get_methods.get("function_rva"), int)
        or not 0 < get_methods["function_rva"] < binary_identity["bytes"]
        or not isinstance(class_data, dict)
        or class_data.get("schema") != RUNTIME_CLASS_SCHEMA
        or class_data.get("status") != "discovered"
        or class_data.get("checks", {}).get("method_layout_semantically_unique")
        is not True
        or class_data.get("checks", {}).get("method_pointer_field_unique")
        is not True
        or not isinstance(method_pointer_qword, int)
        or not 0 <= method_pointer_qword
        < RUNTIME_CONSTRUCTED_METHOD_CANDIDATE_QWORDS
    ):
        raise AcquisitionError("runtime constructed method bindings are stale")

    constructed_raw = constructed_path.read_bytes()
    method_raw = method_path.read_bytes()
    if (
        len(constructed_raw) < RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        or len(method_raw) < RUNTIME_METHOD_DETAIL_HEADER.size
    ):
        raise AcquisitionError("runtime constructed method input is truncated")
    constructed_header = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.unpack_from(
        constructed_raw
    )
    method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(method_raw)
    process_id = constructed_header[7]
    if (
        constructed_header[0] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC
        or constructed_header[1] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
        or constructed_header[2]
        != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        or constructed_header[3]
        != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
        or _digest(constructed_header[12], label="constructed executable")
        != binary_identity["sha256"]
        or method_header[0] != RUNTIME_METHOD_DETAIL_MAGIC
        or method_header[1] != RUNTIME_METHOD_DETAIL_VERSION
        or method_header[2] != RUNTIME_METHOD_DETAIL_HEADER.size
        or method_header[3] != RUNTIME_METHOD_DETAIL_METHOD.size
        or method_header[8] != constructed_header[8]
        or method_header[9] != constructed_header[9]
        or _digest(method_header[12], label="method executable")
        != binary_identity["sha256"]
        or process_id <= 0
        or process_id
        != constructed_model_data.get("target", {}).get("process_id")
    ):
        raise AcquisitionError(
            "runtime constructed method input headers are inconsistent"
        )
    identity_value = method_model_data.get("inputs", {}).get(
        "type_identity_inventory"
    )
    if not isinstance(identity_value, dict) or not isinstance(
        identity_value.get("path"), str
    ):
        raise AcquisitionError(
            "runtime constructed method type identity binding is absent"
        )
    identity_path = _owner_file(
        Path(identity_value["path"]), label="type identity inventory"
    )
    if file_identity(identity_path) != identity_value:
        raise AcquisitionError(
            "runtime constructed method type identity binding is stale"
        )
    identity_raw = identity_path.read_bytes()
    if len(identity_raw) < _IDENTITY_HEADER.size:
        raise AcquisitionError(
            "runtime constructed method type identity is truncated"
        )
    identity_header = _IDENTITY_HEADER.unpack_from(identity_raw)
    if (
        identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or identity_header[2] != _IDENTITY_HEADER.size
        or identity_header[3] != _IDENTITY_RECORD.size
        or identity_header[5] != method_model_data.get("counts", {}).get(
            "type_count", identity_header[5]
        )
        or identity_header[6] != method_header[8]
        or identity_header[7] != method_header[9]
        or _digest(identity_header[9], label="identity executable")
        != binary_identity["sha256"]
    ):
        raise AcquisitionError(
            "runtime constructed method type identity header is invalid"
        )
    type_classes = [
        _IDENTITY_RECORD.unpack_from(
            identity_raw,
            _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size,
        )[3]
        for index in range(identity_header[5])
    ]
    if any(not value or value & 7 for value in type_classes):
        raise AcquisitionError(
            "runtime constructed method TypeDef class domain is invalid"
        )

    owner_methods: dict[int, list[tuple[int, int]]] = defaultdict(list)
    for method_index in range(method_header[5]):
        row = RUNTIME_METHOD_DETAIL_METHOD.unpack_from(
            method_raw,
            RUNTIME_METHOD_DETAIL_HEADER.size
            + method_index * RUNTIME_METHOD_DETAIL_METHOD.size,
        )
        if (
            row[0] >= identity_header[5]
            or row[1] != method_index
            or not row[2]
        ):
            raise AcquisitionError(
                "runtime constructed method MethodDef row is invalid"
            )
        owner_methods[row[0]].append((method_index, row[2]))

    constructed_end = (
        RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        + constructed_header[5]
        * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
    )
    if constructed_end > len(constructed_raw):
        raise AcquisitionError(
            "runtime constructed method class records are truncated"
        )
    classes: list[tuple[int, int, int, int, int, int, int]] = []
    definition_indexes: set[int] = set()
    constructed_class_pointers: set[int] = set()
    instance_method_count = 0
    for index in range(constructed_header[5]):
        row = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.unpack_from(
            constructed_raw,
            RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
            + index * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size,
        )
        descriptor, generic_index, definition_index, klass = (
            row[0],
            row[2],
            row[3],
            row[6],
        )
        methods = owner_methods.get(definition_index, [])
        if (
            generic_index >> 32
            or definition_index >= identity_header[5]
            or not klass
            or klass & 7
            or klass in constructed_class_pointers
            or len(methods) > 0xFFFF
        ):
            raise AcquisitionError(
                "runtime constructed method class row is invalid"
            )
        constructed_class_pointers.add(klass)
        definition_indexes.add(definition_index)
        classes.append(
            (
                descriptor,
                klass,
                generic_index,
                definition_index,
                len(methods),
                0,
                0,
            )
        )
        instance_method_count += len(methods)
    definitions: list[tuple[int, int, int, int, int, int]] = []
    expected_methods: list[tuple[int, int, int]] = []
    definition_starts: dict[int, int] = {}
    for definition_index in sorted(definition_indexes):
        start = len(expected_methods)
        definition_starts[definition_index] = start
        methods = owner_methods.get(definition_index, [])
        definitions.append(
            (
                type_classes[definition_index],
                definition_index,
                len(methods),
                0,
                0,
                start,
            )
        )
        expected_methods.extend(
            (method_index, 0, metadata)
            for method_index, metadata in methods
        )
    classes = [
        (*row[:6], definition_starts[row[3]])
        for row in classes
    ]
    if not classes or not definitions or not instance_method_count:
        raise AcquisitionError(
            "runtime constructed method domain is unexpectedly empty"
        )
    return {
        "binary": binary_identity,
        "constructed_generic_model": file_identity(constructed_model_path),
        "constructed_generic_inventory": constructed_identity,
        "method_detail_model": file_identity(method_model_path),
        "method_detail_inventory": method_identity,
        "native_helper_model": file_identity(helper_path),
        "class_model": class_identity,
        "type_identity_inventory": file_identity(identity_path),
        "process_id": process_id,
        "image_base": method_header[8],
        "image_bytes": method_header[9],
        "class_get_methods_rva": get_methods["function_rva"],
        "method_pointer_qword": method_pointer_qword,
        "classes": classes,
        "definitions": definitions,
        "expected_methods": expected_methods,
        "instance_method_count": instance_method_count,
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define HASH_CHUNK (1024u * 1024u)
typedef struct seed_header { char magic[8]; uint32_t version,header_bytes,class_bytes,reserved; uint64_t class_count,definition_count,instance_method_count,definition_method_count,process_id,image_base,image_bytes,class_get_methods_rva,method_pointer_qword; char executable[64],constructed[64],methods[64],helper[64]; } seed_header;
typedef struct seed_class { uint64_t descriptor,klass; uint32_t generic_index,definition_index,method_count,reserved; uint64_t definition_method_start; } seed_class;
typedef struct seed_definition { uint64_t klass; uint32_t definition_index,method_count,reserved0,reserved1; uint64_t method_start; } seed_definition;
typedef struct seed_method { uint32_t method_index,reserved; uint64_t metadata; } seed_method;
typedef struct output_header { char magic[8]; uint32_t version,header_bytes,class_bytes,method_bytes; uint64_t class_count,method_count,process_id,image_base,image_bytes,method_pointer_qword; char executable[64],constructed[64],methods[64],helper[64]; } output_header;
typedef struct output_class { uint64_t descriptor,klass; uint32_t generic_index,definition_index,method_count,reserved; uint64_t method_start; } output_class;
typedef struct output_method { uint64_t metadata; uint32_t method_index,ordinal; uint64_t executable_mask,candidates[$candidate_qwords]; } output_method;
typedef struct observation { output_class*classes; output_method*methods; uint64_t empty_candidate_methods,nonempty_candidate_methods,executable_candidate_count; } observation;
_Static_assert(sizeof(seed_header)==$seed_header_bytes,"seed header");
_Static_assert(sizeof(seed_class)==$seed_class_bytes,"seed class");
_Static_assert(sizeof(seed_definition)==$seed_definition_bytes,"seed definition");
_Static_assert(sizeof(seed_method)==$seed_method_bytes,"seed method");
_Static_assert(sizeof(output_header)==$output_header_bytes,"output header");
_Static_assert(sizeof(output_class)==$output_class_bytes,"output class");
_Static_assert(sizeof(output_method)==$output_method_bytes,"output method");
static const char expected_seed_sha256[]="$seed_sha256";static const wchar_t seed_path[]=$seed_path,output_path[]=$output_path,status_path[]=$status_path;static seed_header*h;static seed_class*classes;static seed_definition*definitions;static seed_method*expected_methods;static uint64_t failure_index;static uint32_t failure_kind;
typedef uintptr_t(*class_get_methods_fn)(uintptr_t,uintptr_t*);
static int readable(uintptr_t p,SIZE_T n){MEMORY_BASIC_INFORMATION m;if(!p||!n||p+n<p||!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||(m.Protect&(PAGE_NOACCESS|PAGE_GUARD)))return 0;DWORD q=m.Protect&0xffu;if(q!=PAGE_READONLY&&q!=PAGE_READWRITE&&q!=PAGE_WRITECOPY&&q!=PAGE_EXECUTE_READ&&q!=PAGE_EXECUTE_READWRITE&&q!=PAGE_EXECUTE_WRITECOPY)return 0;return p+n<=(uintptr_t)m.BaseAddress+m.RegionSize;}
static int executable(uintptr_t p){MEMORY_BASIC_INFORMATION m;if(!p)return 0;if(!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||(m.Protect&(PAGE_NOACCESS|PAGE_GUARD)))return 0;DWORD q=m.Protect&0xffu;return q==PAGE_EXECUTE||q==PAGE_EXECUTE_READ||q==PAGE_EXECUTE_READWRITE||q==PAGE_EXECUTE_WRITECOPY;}
static void digest_hex(const unsigned char digest[32],char output[65]){static const char alphabet[]="0123456789abcdef";for(int i=0;i<32;i++){output[i*2]=alphabet[digest[i]>>4];output[i*2+1]=alphabet[digest[i]&15];}output[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE input=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(input==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char digest[32],*object=NULL,*buffer=NULL;int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,HASH_CHUNK);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;while(ok){DWORD count=0;if(!ReadFile(input,buffer,HASH_CHUNK,&count,NULL)){ok=0;break;}if(!count)break;if(BCryptHashData(hash,buffer,count,0)<0)ok=0;}if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)<0)ok=0;if(ok)digest_hex(digest,output);if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(input);return ok;}
static int executable_identity(char output[65]){wchar_t path[32768];DWORD length=GetModuleFileNameW(NULL,path,(DWORD)(sizeof(path)/sizeof(path[0])));return length&&length<sizeof(path)/sizeof(path[0])&&sha256_file(path,output);}
static int validate_definitions(void){class_get_methods_fn get_methods=(class_get_methods_fn)(h->image_base+h->class_get_methods_rva);for(uint64_t i=0;i<h->definition_count;i++){seed_definition*d=&definitions[i];uintptr_t iterator=0;for(uint32_t j=0;j<d->method_count;j++){uintptr_t method=get_methods((uintptr_t)d->klass,&iterator);if(method!=expected_methods[d->method_start+j].metadata){failure_index=i+1u;failure_kind=1u;return 0;}}if(get_methods((uintptr_t)d->klass,&iterator)){failure_index=i+1u;failure_kind=2u;return 0;}}return 1;}
static void free_observation(observation*o){free(o->classes);free(o->methods);memset(o,0,sizeof(*o));}
static int observe(observation*o){class_get_methods_fn get_methods=(class_get_methods_fn)(h->image_base+h->class_get_methods_rva);o->classes=calloc((SIZE_T)h->class_count,sizeof(*o->classes));o->methods=calloc((SIZE_T)h->instance_method_count,sizeof(*o->methods));if(!o->classes||!o->methods){failure_kind=3u;free_observation(o);return 0;}uint64_t cursor=0;for(uint64_t i=0;i<h->class_count;i++){seed_class*s=&classes[i];output_class*c=&o->classes[i];c->descriptor=s->descriptor;c->klass=s->klass;c->generic_index=s->generic_index;c->definition_index=s->definition_index;c->method_count=s->method_count;c->method_start=cursor;uintptr_t iterator=0;for(uint32_t j=0;j<s->method_count;j++){seed_method*expected=&expected_methods[s->definition_method_start+j];uintptr_t method=get_methods((uintptr_t)s->klass,&iterator);if(!readable(method,(SIZE_T)$candidate_qwords*8u)){failure_index=i+1u;failure_kind=4u;free_observation(o);return 0;}output_method*m=&o->methods[cursor++];m->metadata=method;m->method_index=expected->method_index;m->ordinal=j;for(uint32_t q=0;q<$candidate_qwords;q++){uint64_t value=0;memcpy(&value,(const void*)(method+(uintptr_t)q*8u),8u);if(value&&executable((uintptr_t)value)){m->executable_mask|=1ull<<q;m->candidates[q]=value;o->executable_candidate_count++;}}o->empty_candidate_methods+=m->executable_mask==0;o->nonempty_candidate_methods+=m->executable_mask!=0;}if(get_methods((uintptr_t)s->klass,&iterator)){failure_index=i+1u;failure_kind=6u;free_observation(o);return 0;}}if(cursor!=h->instance_method_count){failure_kind=7u;free_observation(o);return 0;}return 1;}
static int same_observation(const observation*a,const observation*b){return a->empty_candidate_methods==b->empty_candidate_methods&&a->nonempty_candidate_methods==b->nonempty_candidate_methods&&a->executable_candidate_count==b->executable_candidate_count&&!memcmp(a->classes,b->classes,(SIZE_T)h->class_count*sizeof(output_class))&&!memcmp(a->methods,b->methods,(SIZE_T)h->instance_method_count*sizeof(output_method));}
static int read_all(const wchar_t*p,uint8_t**data,SIZE_T*n){FILE*f=_wfopen(p,L"rb");if(!f)return 0;if(_fseeki64(f,0,SEEK_END)||(*n=(SIZE_T)_ftelli64(f))==0||_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*data=malloc(*n);int ok=*data&&fread(*data,1,*n,f)==*n&&!fclose(f);if(!ok){free(*data);*data=NULL;}return ok;}
static void write_status(const char*state,const observation*o,int definitions_ok,int match,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"class_count\": %llu,\n  \"definition_count\": %llu,\n  \"method_count\": %llu,\n  \"empty_candidate_method_count\": %llu,\n  \"nonempty_candidate_method_count\": %llu,\n  \"executable_candidate_count\": %llu,\n  \"candidate_qword_count\": %u,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"definition_iterator_order_matches\": %s,\n  \"two_observations_match\": %s,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"class_method_iterator_current_code_derived\": true,\n  \"executable_candidates_structurally_classified\": true,\n  \"saved_layout_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"fixed_rva_used\": false,\n  \"external_runtime_component_used\": false\n}\n",state,(unsigned long)GetCurrentProcessId(),(unsigned long long)h->class_count,(unsigned long long)h->definition_count,(unsigned long long)h->instance_method_count,(unsigned long long)(o?o->empty_candidate_methods:0u),(unsigned long long)(o?o->nonempty_candidate_methods:0u),(unsigned long long)(o?o->executable_candidate_count:0u),$candidate_qwords,(unsigned long long)failure_index,failure_kind,definitions_ok?"true":"false",match?"true":"false",written?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);uint8_t*seed=NULL;SIZE_T bytes=0;char seed_digest[65],executable_digest[65];if(!sha256_file(seed_path,seed_digest)||strcmp(seed_digest,expected_seed_sha256)||!read_all(seed_path,&seed,&bytes)||bytes<sizeof(seed_header))return 0;h=(seed_header*)seed;SIZE_T required=sizeof(*h)+(SIZE_T)h->class_count*sizeof(seed_class)+(SIZE_T)h->definition_count*sizeof(seed_definition)+(SIZE_T)h->definition_method_count*sizeof(seed_method);if(memcmp(h->magic,"ALPHACX1",8)||h->version!=$seed_version||h->header_bytes!=sizeof(*h)||h->class_bytes!=sizeof(seed_class)||h->reserved||h->process_id!=GetCurrentProcessId()||!executable_identity(executable_digest)||memcmp(h->executable,executable_digest,64)||!h->class_count||!h->definition_count||!h->instance_method_count||h->class_count>2000000ull||h->instance_method_count>50000000ull||h->method_pointer_qword>=$candidate_qwords||bytes!=required){failure_kind=100u;write_status("identity_mismatch",NULL,0,0,0);free(seed);return 0;}classes=(seed_class*)(seed+sizeof(*h));definitions=(seed_definition*)((uint8_t*)classes+(SIZE_T)h->class_count*sizeof(seed_class));expected_methods=(seed_method*)((uint8_t*)definitions+(SIZE_T)h->definition_count*sizeof(seed_definition));int definitions_ok=validate_definitions();observation first={0},second={0};if(!definitions_ok||!observe(&first)){if(!failure_kind)failure_kind=101u;write_status("capture_failed",&first,definitions_ok,0,0);free_observation(&first);free(seed);return 0;}Sleep(250u);if(!observe(&second)){if(!failure_kind)failure_kind=102u;write_status("capture_failed",&first,definitions_ok,0,0);free_observation(&first);free_observation(&second);free(seed);return 0;}int match=same_observation(&first,&second),written=0;if(match){FILE*f=_wfopen(output_path,L"wb");output_header out={0};memcpy(out.magic,"ALPHACM2",8);out.version=$output_version;out.header_bytes=sizeof(out);out.class_bytes=sizeof(output_class);out.method_bytes=sizeof(output_method);out.class_count=h->class_count;out.method_count=h->instance_method_count;out.process_id=h->process_id;out.image_base=h->image_base;out.image_bytes=h->image_bytes;out.method_pointer_qword=h->method_pointer_qword;memcpy(out.executable,h->executable,64);memcpy(out.constructed,h->constructed,64);memcpy(out.methods,h->methods,64);memcpy(out.helper,h->helper,64);written=f&&fwrite(&out,1,sizeof(out),f)==sizeof(out)&&fwrite(first.classes,sizeof(output_class),(SIZE_T)h->class_count,f)==h->class_count&&fwrite(first.methods,sizeof(output_method),(SIZE_T)h->instance_method_count,f)==h->instance_method_count;if(f&&fclose(f))written=0;if(written)_wchmod(output_path,0600);else _wremove(output_path);}write_status(written?"complete":(match?"write_failed":"observation_unstable"),&first,definitions_ok,match,written);free_observation(&first);free_observation(&second);free(seed);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def prepare_runtime_constructed_methods(
    *,
    binary: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    native_helper_model: Path,
    class_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        constructed_generic_model=constructed_generic_model,
        constructed_generic_inventory=constructed_generic_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        native_helper_model=native_helper_model,
        class_model=class_model,
    )
    seed_path = output_dir / "runtime-constructed-method-seed.private.bin"
    output_path = output_dir / "runtime-constructed-method.private.bin"
    status_path = output_dir / "runtime-constructed-method-status.private.json"
    model_path = output_dir / "runtime-constructed-method.private.json"
    for path in (output_path, status_path, model_path):
        path.unlink(missing_ok=True)
    seed = bytearray(
        _SEED_HEADER.pack(
            _SEED_MAGIC,
            _SEED_VERSION,
            _SEED_HEADER.size,
            _SEED_CLASS.size,
            0,
            len(binding["classes"]),
            len(binding["definitions"]),
            binding["instance_method_count"],
            len(binding["expected_methods"]),
            binding["process_id"],
            binding["image_base"],
            binding["image_bytes"],
            binding["class_get_methods_rva"],
            binding["method_pointer_qword"],
            binding["binary"]["sha256"].encode("ascii"),
            binding["constructed_generic_inventory"]["sha256"].encode(
                "ascii"
            ),
            binding["method_detail_inventory"]["sha256"].encode("ascii"),
            binding["native_helper_model"]["sha256"].encode("ascii"),
        )
    )
    for row in binding["classes"]:
        seed.extend(_SEED_CLASS.pack(*row))
    for row in binding["definitions"]:
        seed.extend(_SEED_DEFINITION.pack(*row))
    for row in binding["expected_methods"]:
        seed.extend(_SEED_METHOD.pack(*row))
    seed_path.write_bytes(seed)
    seed_path.chmod(0o600)
    seed_identity = file_identity(seed_path)
    build_dir = _owner_directory(output_dir / "build-constructed-method")
    source_path = build_dir / "runtime-constructed-method.c"
    injector_source_path = build_dir / "runtime-constructed-method-injector.c"
    collector_path = build_dir / (
        f"alpha-runtime-constructed-method-{time.time_ns():x}.dll"
    )
    injector_path = build_dir / "alpha-runtime-constructed-method-injector.exe"
    source = _COLLECTOR.substitute(
        seed_header_bytes=_SEED_HEADER.size,
        seed_class_bytes=_SEED_CLASS.size,
        seed_definition_bytes=_SEED_DEFINITION.size,
        seed_method_bytes=_SEED_METHOD.size,
        output_header_bytes=RUNTIME_CONSTRUCTED_METHOD_HEADER.size,
        output_class_bytes=RUNTIME_CONSTRUCTED_METHOD_CLASS.size,
        output_method_bytes=RUNTIME_CONSTRUCTED_METHOD_RECORD.size,
        candidate_qwords=RUNTIME_CONSTRUCTED_METHOD_CANDIDATE_QWORDS,
        seed_sha256=seed_identity["sha256"],
        seed_path=_wide_literal(_windows_z_path(seed_path)),
        output_path=_wide_literal(_windows_z_path(output_path)),
        status_path=_wide_literal(_windows_z_path(status_path)),
        status_schema=RUNTIME_CONSTRUCTED_METHOD_STATUS_SCHEMA,
        seed_version=_SEED_VERSION,
        output_version=RUNTIME_CONSTRUCTED_METHOD_VERSION,
    )
    _private_text(source_path, source)
    _private_text(injector_source_path, runtime_injector_source())
    cc = _compiler(compiler)
    _build(
        [
            str(cc),
            "-shared",
            "-O2",
            "-s",
            "-Wall",
            "-Wextra",
            "-Wformat=2",
            "-Werror",
            str(source_path),
            "-o",
            str(collector_path),
            "-lbcrypt",
        ],
        label="runtime constructed method collector",
    )
    _build(
        [
            str(cc),
            "-O2",
            "-s",
            "-municode",
            "-Wall",
            "-Wextra",
            "-Wformat=2",
            "-Werror",
            str(injector_source_path),
            "-o",
            str(injector_path),
        ],
        label="runtime constructed method injector",
    )
    input_keys = (
        "constructed_generic_model",
        "constructed_generic_inventory",
        "method_detail_model",
        "method_detail_inventory",
        "native_helper_model",
        "class_model",
        "type_identity_inventory",
    )
    plan = {
        "schema": "alpha.runtime-constructed-method-plan/v1",
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {key: binding[key] for key in input_keys},
        "contract": {
            "constructed_class_count": len(binding["classes"]),
            "constructed_method_count": binding["instance_method_count"],
            "generic_definition_count": len(binding["definitions"]),
            "definition_method_count": len(binding["expected_methods"]),
            "executable_candidate_qword_count": (
                RUNTIME_CONSTRUCTED_METHOD_CANDIDATE_QWORDS
            ),
        },
        "runtime_contract_owner_only": {
            "class_get_methods_rva": binding["class_get_methods_rva"],
            "method_pointer_qword": binding["method_pointer_qword"],
        },
        "seed": seed_identity,
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "policy": {
            "definition_iterator_order_must_match_methoddef_order": True,
            "all_constructed_class_methods_observed": True,
            "two_observations_required": True,
            "saved_layout_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "fixed_rva_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(
        output_dir / "runtime-constructed-method-plan.private.json", plan
    )
    return plan


def _validate(
    plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = _owner_file(Path(plan["output_path"]), label="inventory")
    seed_path = _owner_file(Path(plan["seed"]["path"]), label="seed")
    raw = output_path.read_bytes()
    seed = seed_path.read_bytes()
    if (
        len(raw) < RUNTIME_CONSTRUCTED_METHOD_HEADER.size
        or len(seed) < _SEED_HEADER.size
    ):
        raise AcquisitionError("runtime constructed method output is truncated")
    header = RUNTIME_CONSTRUCTED_METHOD_HEADER.unpack_from(raw)
    seed_header = _SEED_HEADER.unpack_from(seed)
    class_count, method_count = header[5:7]
    classes_end = (
        RUNTIME_CONSTRUCTED_METHOD_HEADER.size
        + class_count * RUNTIME_CONSTRUCTED_METHOD_CLASS.size
    )
    seed_classes_end = _SEED_HEADER.size + class_count * _SEED_CLASS.size
    seed_definitions_end = (
        seed_classes_end + seed_header[6] * _SEED_DEFINITION.size
    )
    seed_end = seed_definitions_end + seed_header[8] * _SEED_METHOD.size
    header_ok = (
        header[0] == RUNTIME_CONSTRUCTED_METHOD_MAGIC
        and header[1] == RUNTIME_CONSTRUCTED_METHOD_VERSION
        and header[2] == RUNTIME_CONSTRUCTED_METHOD_HEADER.size
        and header[3] == RUNTIME_CONSTRUCTED_METHOD_CLASS.size
        and header[4] == RUNTIME_CONSTRUCTED_METHOD_RECORD.size
        and class_count == plan["contract"]["constructed_class_count"]
        and method_count == plan["contract"]["constructed_method_count"]
        and header[7] == plan["target"]["process_id"]
        and header[8] == plan["target"]["image_base_owner_only"]
        and header[9] == plan["target"]["image_bytes"]
        and header[10]
        == plan["runtime_contract_owner_only"]["method_pointer_qword"]
        and _digest(header[11], label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[12], label="constructed")
        == plan["inputs"]["constructed_generic_inventory"]["sha256"]
        and _digest(header[13], label="methods")
        == plan["inputs"]["method_detail_inventory"]["sha256"]
        and _digest(header[14], label="helper")
        == plan["inputs"]["native_helper_model"]["sha256"]
        and classes_end
        + method_count * RUNTIME_CONSTRUCTED_METHOD_RECORD.size
        == len(raw)
    )
    seed_ok = (
        hashlib.sha256(seed).hexdigest() == plan["seed"]["sha256"]
        and seed_header[0] == _SEED_MAGIC
        and seed_header[1] == _SEED_VERSION
        and seed_header[2] == _SEED_HEADER.size
        and seed_header[3] == _SEED_CLASS.size
        and seed_header[4] == 0
        and seed_header[5] == class_count
        and seed_header[6] == plan["contract"]["generic_definition_count"]
        and seed_header[7] == method_count
        and seed_header[8] == plan["contract"]["definition_method_count"]
        and seed_header[9] == plan["target"]["process_id"]
        and seed_header[10] == plan["target"]["image_base_owner_only"]
        and seed_header[11] == plan["target"]["image_bytes"]
        and seed_header[12]
        == plan["runtime_contract_owner_only"]["class_get_methods_rva"]
        and seed_header[13]
        == plan["runtime_contract_owner_only"]["method_pointer_qword"]
        and _digest(seed_header[14], label="seed executable")
        == plan["target"]["executable_sha256"]
        and _digest(seed_header[15], label="seed constructed")
        == plan["inputs"]["constructed_generic_inventory"]["sha256"]
        and _digest(seed_header[16], label="seed methods")
        == plan["inputs"]["method_detail_inventory"]["sha256"]
        and _digest(seed_header[17], label="seed helper")
        == plan["inputs"]["native_helper_model"]["sha256"]
        and seed_end == len(seed)
    )
    rows_ok = header_ok and seed_ok
    cursor = empty_candidate_methods = nonempty_candidate_methods = 0
    executable_candidate_count = 0
    metadata_pointers: set[int] = set()
    for index in range(class_count if rows_ok else 0):
        expected = _SEED_CLASS.unpack_from(
            seed, _SEED_HEADER.size + index * _SEED_CLASS.size
        )
        row = RUNTIME_CONSTRUCTED_METHOD_CLASS.unpack_from(
            raw,
            RUNTIME_CONSTRUCTED_METHOD_HEADER.size
            + index * RUNTIME_CONSTRUCTED_METHOD_CLASS.size,
        )
        if (
            row[:5] != expected[:5]
            or row[5]
            or row[6] != cursor
            or cursor + row[4] > method_count
        ):
            rows_ok = False
            break
        for ordinal in range(row[4]):
            method = RUNTIME_CONSTRUCTED_METHOD_RECORD.unpack_from(
                raw,
                classes_end
                + (cursor + ordinal) * RUNTIME_CONSTRUCTED_METHOD_RECORD.size,
            )
            expected_method = _SEED_METHOD.unpack_from(
                seed,
                seed_definitions_end
                + (expected[6] + ordinal) * _SEED_METHOD.size,
            )
            if (
                not method[0]
                or method[0] & 7
                or method[1] != expected_method[0]
                or method[2] != ordinal
                or method[0] in metadata_pointers
            ):
                rows_ok = False
                break
            metadata_pointers.add(method[0])
            mask = method[3]
            candidates = method[4:]
            if (
                mask >> RUNTIME_CONSTRUCTED_METHOD_CANDIDATE_QWORDS
                or any(
                    bool(mask & (1 << candidate_index)) != bool(value)
                    for candidate_index, value in enumerate(candidates)
                )
            ):
                rows_ok = False
                break
            empty_candidate_methods += mask == 0
            nonempty_candidate_methods += mask != 0
            executable_candidate_count += mask.bit_count()
        if not rows_ok:
            break
        cursor += row[4]
    rows_ok = rows_ok and cursor == method_count
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_CONSTRUCTED_METHOD_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "header_bound": header_ok,
        "seed_bound": seed_ok,
        "definition_iterator_order_matches": status.get(
            "definition_iterator_order_matches"
        )
        is True,
        "all_constructed_class_rows_valid": rows_ok,
        "all_constructed_methods_accounted": rows_ok
        and status.get("method_count") == method_count,
        "inflated_method_metadata_unique": rows_ok
        and len(metadata_pointers) == method_count,
        "executable_candidate_domain_nontrivial": nonempty_candidate_methods
        > empty_candidate_methods,
        "two_observations_match": status.get("two_observations_match") is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
        is True,
        "class_method_iterator_current_code_derived": status.get(
            "class_method_iterator_current_code_derived"
        )
        is True,
        "executable_candidates_structurally_classified": status.get(
            "executable_candidates_structurally_classified"
        )
        is True,
        "candidate_qword_count_bound": status.get("candidate_qword_count")
        == RUNTIME_CONSTRUCTED_METHOD_CANDIDATE_QWORDS,
        "saved_layout_absent": status.get("saved_layout_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "fixed_rva_absent": status.get("fixed_rva_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    counts = {
        "constructed_class_count": class_count,
        "constructed_method_count": method_count,
        "empty_candidate_method_count": empty_candidate_methods,
        "nonempty_candidate_method_count": nonempty_candidate_methods,
        "executable_candidate_count": executable_candidate_count,
        "unique_inflated_method_metadata_count": len(metadata_pointers),
        "inventory_sha256": hashlib.sha256(raw).hexdigest(),
    }
    return counts, checks


def capture_runtime_constructed_methods(
    *,
    binary: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    native_helper_model: Path,
    class_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 900.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    plan = prepare_runtime_constructed_methods(
        binary=binary,
        constructed_generic_model=constructed_generic_model,
        constructed_generic_inventory=constructed_generic_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        native_helper_model=native_helper_model,
        class_model=class_model,
        output_dir=output_dir,
        compiler=compiler,
    )
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
            "runtime constructed method injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-constructed-method-injector.private.log",
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
        raise AcquisitionError("runtime constructed method injection failed")
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
        raise AcquisitionError("runtime constructed method capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime constructed method capture failed "
            f"(status={status.get('status')}, "
            f"kind={status.get('failure_kind_owner_only')}, "
            f"index={status.get('failure_index_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    counts, checks = _validate(plan, status)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime constructed method validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    model = {
        "schema": RUNTIME_CONSTRUCTED_METHOD_SCHEMA,
        "status": "runtime-validated",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"],
            "process_id": plan["target"]["process_id"],
        },
        "inputs": plan["inputs"],
        "seed": plan["seed"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "runtime_contract_owner_only": plan["runtime_contract_owner_only"],
        "policy": plan["policy"],
        "owner_only": True,
    }
    atomic_write_json(Path(plan["model_path"]), model)
    Path(plan["model_path"]).chmod(0o600)
    return model
