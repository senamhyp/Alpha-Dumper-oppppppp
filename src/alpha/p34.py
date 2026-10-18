from alpha.h02 import windows_run as _host_run

import hashlib
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
from alpha.p27 import RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
from alpha.p19 import _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_RECORD, RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION, TYPE_REFERENCE_INTERFACE
from alpha.p32 import RUNTIME_VTABLE_INTERFACE_HEADER, RUNTIME_VTABLE_INTERFACE_MAGIC, RUNTIME_VTABLE_INTERFACE_SCHEMA, RUNTIME_VTABLE_INTERFACE_VERSION
from alpha.h02 import atomic_write_json, file_identity, read_json


RUNTIME_CONSTRUCTED_VTABLE_SCHEMA = (
    "alpha.runtime-constructed-vtable-inventory/v1"
)
RUNTIME_CONSTRUCTED_VTABLE_STATUS_SCHEMA = (
    "alpha.runtime-constructed-vtable-inventory-status/v1"
)
RUNTIME_CONSTRUCTED_VTABLE_MAGIC = b"ALPHACV1"
RUNTIME_CONSTRUCTED_VTABLE_VERSION = 1
RUNTIME_CONSTRUCTED_VTABLE_HEADER = struct.Struct(
    "<8sIIIIQQQQQQ64s64s64s64s"
)
RUNTIME_CONSTRUCTED_VTABLE_RECORD = struct.Struct("<QQIIIIQQ")
RUNTIME_CONSTRUCTED_VTABLE_INTERFACE = struct.Struct("<QII")

_SEED_MAGIC = b"ALPHACW1"
_SEED_VERSION = 1
_SEED_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQIIIIII64s64s64s64s"
)
_SEED_RECORD = struct.Struct("<QQIIIIQ")
_SEED_ALIAS = struct.Struct("<QQII")
_SEED_CLASS_ALIAS = struct.Struct("<QQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime constructed vtable {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime constructed vtable {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime constructed vtable {label} digest is invalid"
        )
    return value


def _binding(
    *,
    binary: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    vtable_interface_model: Path,
    vtable_interface_inventory: Path,
) -> dict[str, Any]:
    binary_identity = file_identity(binary.expanduser().resolve())
    constructed_model_path = _owner_file(
        constructed_generic_model, label="constructed generic model"
    )
    constructed_path = _owner_file(
        constructed_generic_inventory, label="constructed generic inventory"
    )
    reference_model_path = _owner_file(
        type_reference_model, label="type reference model"
    )
    reference_path = _owner_file(
        type_reference_inventory, label="type reference inventory"
    )
    vtable_model_path = _owner_file(
        vtable_interface_model, label="vtable/interface model"
    )
    vtable_path = _owner_file(
        vtable_interface_inventory, label="vtable/interface inventory"
    )
    constructed_model_data = read_json(constructed_model_path)
    reference_model_data = read_json(reference_model_path)
    vtable_model_data = read_json(vtable_model_path)
    constructed_identity = file_identity(constructed_path)
    reference_identity = file_identity(reference_path)
    vtable_identity = file_identity(vtable_path)
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
        or not isinstance(reference_model_data, dict)
        or reference_model_data.get("schema") != RUNTIME_TYPE_REFERENCE_SCHEMA
        or reference_model_data.get("status") != "runtime-validated"
        or reference_model_data.get("target", {}).get("executable_sha256")
        != binary_identity["sha256"]
        or reference_model_data.get("inventory") != reference_identity
        or not reference_model_data.get("checks")
        or not all(reference_model_data["checks"].values())
        or not isinstance(vtable_model_data, dict)
        or vtable_model_data.get("schema") != RUNTIME_VTABLE_INTERFACE_SCHEMA
        or vtable_model_data.get("status") != "runtime-validated"
        or vtable_model_data.get("target", {}).get("executable_sha256")
        != binary_identity["sha256"]
        or vtable_model_data.get("inventory") != vtable_identity
        or not vtable_model_data.get("checks")
        or not all(vtable_model_data["checks"].values())
        or vtable_model_data.get("inputs", {}).get(
            "constructed_generic_inventory"
        )
        != constructed_identity
        or vtable_model_data.get("inputs", {}).get("type_reference_inventory")
        != reference_identity
        or constructed_model_data.get("inputs", {}).get(
            "type_reference_inventory"
        )
        != reference_identity
    ):
        raise AcquisitionError("runtime constructed vtable bindings are stale")

    identity_value = vtable_model_data.get("inputs", {}).get(
        "type_identity_inventory"
    )
    if not isinstance(identity_value, dict) or not isinstance(
        identity_value.get("path"), str
    ):
        raise AcquisitionError(
            "runtime constructed vtable type identity binding is absent"
        )
    identity_path = _owner_file(
        Path(identity_value["path"]), label="type identity inventory"
    )
    if file_identity(identity_path) != identity_value:
        raise AcquisitionError(
            "runtime constructed vtable type identity binding is stale"
        )

    constructed_raw = constructed_path.read_bytes()
    reference_raw = reference_path.read_bytes()
    vtable_raw = vtable_path.read_bytes()
    identity_raw = identity_path.read_bytes()
    if (
        len(constructed_raw) < RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        or len(reference_raw) < RUNTIME_TYPE_REFERENCE_HEADER.size
        or len(vtable_raw) < RUNTIME_VTABLE_INTERFACE_HEADER.size
        or len(identity_raw) < _IDENTITY_HEADER.size
    ):
        raise AcquisitionError("runtime constructed vtable input is truncated")
    constructed_header = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.unpack_from(
        constructed_raw
    )
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
    vtable_header = RUNTIME_VTABLE_INTERFACE_HEADER.unpack_from(vtable_raw)
    identity_header = _IDENTITY_HEADER.unpack_from(identity_raw)
    process_id = vtable_header[8]
    if (
        constructed_header[0] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC
        or constructed_header[1] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
        or constructed_header[2]
        != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        or constructed_header[3]
        != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
        or constructed_header[7] != process_id
        or _digest(constructed_header[12], label="constructed executable")
        != binary_identity["sha256"]
        or reference_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or reference_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or reference_header[2] != RUNTIME_TYPE_REFERENCE_HEADER.size
        or reference_header[3] != RUNTIME_TYPE_REFERENCE_RECORD.size
        or reference_header[10] != vtable_header[9]
        or reference_header[11] != vtable_header[10]
        or _digest(reference_header[12], label="reference executable")
        != binary_identity["sha256"]
        or vtable_header[0] != RUNTIME_VTABLE_INTERFACE_MAGIC
        or vtable_header[1] != RUNTIME_VTABLE_INTERFACE_VERSION
        or vtable_header[2] != RUNTIME_VTABLE_INTERFACE_HEADER.size
        or _digest(vtable_header[11], label="vtable executable")
        != binary_identity["sha256"]
        or identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or identity_header[2] != _IDENTITY_HEADER.size
        or identity_header[3] != _IDENTITY_RECORD.size
        or identity_header[5] != vtable_header[5]
        or identity_header[6] != vtable_header[9]
        or identity_header[7] != vtable_header[10]
        or _digest(identity_header[9], label="identity executable")
        != binary_identity["sha256"]
        or process_id <= 0
        or process_id
        != constructed_model_data.get("target", {}).get("process_id")
        or process_id != vtable_model_data.get("target", {}).get("process_id")
    ):
        raise AcquisitionError(
            "runtime constructed vtable input headers are inconsistent"
        )

    record_start = RUNTIME_TYPE_REFERENCE_HEADER.size
    interface_start = (
        record_start
        + reference_header[5] * RUNTIME_TYPE_REFERENCE_RECORD.size
    )
    argument_start = interface_start + reference_header[7] * 8
    string_start = argument_start + reference_header[8] * 8
    if string_start + reference_header[9] != len(reference_raw):
        raise AcquisitionError(
            "runtime constructed vtable type reference ranges are invalid"
        )
    aliases: list[tuple[int, int, int, int]] = []
    nodes: dict[int, tuple[int, tuple[int, ...]]] = {}
    for index in range(reference_header[5]):
        row = RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
            reference_raw,
            record_start + index * RUNTIME_TYPE_REFERENCE_RECORD.size,
        )
        descriptor, canonical, shape = row[0], row[1], row[4]
        if (
            not descriptor
            or descriptor & 7
            or not canonical
            or canonical & 7
            or descriptor in nodes
            or row[15] + row[7] > reference_header[7]
        ):
            raise AcquisitionError(
                "runtime constructed vtable type reference row is invalid"
            )
        interfaces = tuple(
            struct.unpack_from(
                "<Q",
                reference_raw,
                interface_start + (row[15] + offset) * 8,
            )[0]
            for offset in range(row[7])
        )
        nodes[descriptor] = (shape, interfaces)
        aliases.append((descriptor, canonical, shape, 0))
    aliases.sort()

    class_aliases: dict[int, int] = {}
    for index in range(identity_header[5]):
        row = _IDENTITY_RECORD.unpack_from(
            identity_raw, _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size
        )
        descriptor, klass = row[2], row[3]
        if not descriptor or not klass or klass & 7:
            raise AcquisitionError(
                "runtime constructed vtable TypeDef class alias is invalid"
            )
        prior = class_aliases.setdefault(klass, descriptor)
        if prior != descriptor:
            raise AcquisitionError(
                "runtime constructed vtable TypeDef class alias conflicts"
            )

    constructed_records_end = (
        RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        + constructed_header[5]
        * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
    )
    if constructed_records_end > len(constructed_raw):
        raise AcquisitionError(
            "runtime constructed vtable constructed rows are truncated"
        )
    rows: list[tuple[int, int, int, int, int, int, int]] = []
    interfaces: list[int] = []
    constructed_classes: set[int] = set()
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
        node = nodes.get(descriptor)
        if (
            node is None
            or generic_index >> 32
            or definition_index >> 32
            or not klass
            or klass & 7
            or klass in constructed_classes
        ):
            raise AcquisitionError(
                "runtime constructed vtable constructed class row is invalid"
            )
        constructed_classes.add(klass)
        class_aliases[klass] = descriptor
        shape, expected = node
        if shape & TYPE_REFERENCE_INTERFACE:
            expected = ()
        if len(expected) > 0xFFFF:
            raise AcquisitionError(
                "runtime constructed vtable interface closure is too large"
            )
        start = len(interfaces)
        interfaces.extend(expected)
        rows.append(
            (
                descriptor,
                klass,
                generic_index,
                definition_index,
                len(expected),
                1 if shape & TYPE_REFERENCE_INTERFACE else 0,
                start,
            )
        )
    if not rows or len(rows) != constructed_header[5]:
        raise AcquisitionError(
            "runtime constructed vtable class domain is incomplete"
        )

    layout = vtable_model_data.get("layout_owner_only")
    if not isinstance(layout, dict):
        raise AcquisitionError(
            "runtime constructed vtable upstream layout is absent"
        )
    layout_values = tuple(
        layout.get(key)
        for key in (
            "vtable_start_byte",
            "vtable_count_byte_offset",
            "interface_count_byte_offset",
            "interface_array_byte_offset",
            "interface_item_encoding",
            "interface_pair_encoding",
        )
    )
    if (
        any(not isinstance(value, int) for value in layout_values)
        or not 64 <= layout_values[0] <= 512
        or layout_values[0] & 7
        or not 0 <= layout_values[1] + 2 <= layout_values[0]
        or layout_values[1] & 1
        or not 0 <= layout_values[2] + 2 <= layout_values[0]
        or layout_values[2] & 1
        or not 0 <= layout_values[3] + 8 <= layout_values[0]
        or layout_values[3] & 7
        or layout_values[4] not in (1, 2)
        or layout_values[5] not in (1, 2)
    ):
        raise AcquisitionError(
            "runtime constructed vtable upstream layout is invalid"
        )
    return {
        "binary": binary_identity,
        "constructed_generic_model": file_identity(constructed_model_path),
        "constructed_generic_inventory": constructed_identity,
        "type_reference_model": file_identity(reference_model_path),
        "type_reference_inventory": reference_identity,
        "vtable_interface_model": file_identity(vtable_model_path),
        "vtable_interface_inventory": vtable_identity,
        "type_identity_inventory": file_identity(identity_path),
        "process_id": process_id,
        "image_base": vtable_header[9],
        "image_bytes": vtable_header[10],
        "layout": layout_values,
        "rows": rows,
        "interfaces": interfaces,
        "aliases": aliases,
        "class_aliases": sorted(class_aliases.items()),
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
typedef struct seed_header { char magic[8]; uint32_t version,header_bytes,record_bytes,reserved; uint64_t class_count,expected_interface_count,alias_count,class_alias_count,process_id,image_base,image_bytes; uint32_t vtable_start_byte,vtable_count_byte,interface_count_byte,interface_array_byte,item_encoding,pair_encoding; char executable[64],constructed[64],reference[64],upstream[64]; } seed_header;
typedef struct seed_record { uint64_t descriptor,klass; uint32_t generic_index,definition_index,interface_count,is_interface; uint64_t interface_start; } seed_record;
typedef struct seed_alias { uint64_t source,canonical; uint32_t shape,reserved; } seed_alias;
typedef struct seed_class_alias { uint64_t klass,descriptor; } seed_class_alias;
typedef struct output_header { char magic[8]; uint32_t version,header_bytes,record_bytes,interface_record_bytes; uint64_t class_count,vtable_count,interface_count,process_id,image_base,image_bytes; char executable[64],constructed[64],reference[64],upstream[64]; } output_header;
typedef struct output_record { uint64_t descriptor,klass; uint32_t generic_index,definition_index,vtable_count,interface_count; uint64_t vtable_start,interface_start; } output_record;
typedef struct output_interface { uint64_t descriptor; uint32_t offset,reserved; } output_interface;
typedef struct observation { output_record*records; uint64_t*vtable; output_interface*interfaces; uint64_t vtable_count,interface_count,zero_count,nonzero_count; } observation;
_Static_assert(sizeof(seed_header)==$seed_header_bytes,"seed header");
_Static_assert(sizeof(seed_record)==$seed_record_bytes,"seed record");
_Static_assert(sizeof(seed_alias)==$seed_alias_bytes,"seed alias");
_Static_assert(sizeof(seed_class_alias)==$seed_class_alias_bytes,"seed class alias");
_Static_assert(sizeof(output_header)==$output_header_bytes,"output header");
_Static_assert(sizeof(output_record)==$output_record_bytes,"output record");
_Static_assert(sizeof(output_interface)==$output_interface_bytes,"output interface");
static const char expected_seed_sha256[]="$seed_sha256";
static const wchar_t seed_path[]=$seed_path,output_path[]=$output_path,status_path[]=$status_path;
static seed_header*h;static seed_record*rows;static uint64_t*expected_interfaces;static seed_alias*aliases;static seed_class_alias*class_aliases;static uint64_t failure_index;static uint32_t failure_kind;
static int readable(uintptr_t p,SIZE_T n){MEMORY_BASIC_INFORMATION m;if(!p||!n||p+n<p||!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||(m.Protect&(PAGE_NOACCESS|PAGE_GUARD)))return 0;DWORD q=m.Protect&0xffu;if(q!=PAGE_READONLY&&q!=PAGE_READWRITE&&q!=PAGE_WRITECOPY&&q!=PAGE_EXECUTE_READ&&q!=PAGE_EXECUTE_READWRITE&&q!=PAGE_EXECUTE_WRITECOPY)return 0;return p+n<=(uintptr_t)m.BaseAddress+m.RegionSize;}
static int executable(uintptr_t p){MEMORY_BASIC_INFORMATION m;if(!p)return 0;if(!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||(m.Protect&(PAGE_NOACCESS|PAGE_GUARD)))return 0;DWORD q=m.Protect&0xffu;return q==PAGE_EXECUTE||q==PAGE_EXECUTE_READ||q==PAGE_EXECUTE_READWRITE||q==PAGE_EXECUTE_WRITECOPY;}
static int qword(uintptr_t p,uint64_t*v){if(!readable(p,8u))return 0;memcpy(v,(const void*)p,8u);return 1;}
static int word(uintptr_t p,uint16_t*v){if(!readable(p,2u))return 0;memcpy(v,(const void*)p,2u);return 1;}
static void digest_hex(const unsigned char digest[32],char output[65]){static const char alphabet[]="0123456789abcdef";for(int i=0;i<32;i++){output[i*2]=alphabet[digest[i]>>4];output[i*2+1]=alphabet[digest[i]&15];}output[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE input=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(input==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char digest[32],*object=NULL,*buffer=NULL;int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,HASH_CHUNK);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;while(ok){DWORD count=0;if(!ReadFile(input,buffer,HASH_CHUNK,&count,NULL)){ok=0;break;}if(!count)break;if(BCryptHashData(hash,buffer,count,0)<0)ok=0;}if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)<0)ok=0;if(ok)digest_hex(digest,output);if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(input);return ok;}
static int executable_identity(char output[65]){wchar_t path[32768];DWORD length=GetModuleFileNameW(NULL,path,(DWORD)(sizeof(path)/sizeof(path[0])));return length&&length<sizeof(path)/sizeof(path[0])&&sha256_file(path,output);}
static int descriptor_alias(uint64_t source,uint64_t*canonical,uint32_t*shape){uint64_t low=0,high=h->alias_count;while(low<high){uint64_t middle=low+(high-low)/2u;if(aliases[middle].source<source)low=middle+1u;else high=middle;}if(low>=h->alias_count||aliases[low].source!=source)return 0;*canonical=aliases[low].canonical;*shape=aliases[low].shape;return 1;}
static int class_alias(uint64_t klass,uint64_t*descriptor){uint64_t low=0,high=h->class_alias_count;while(low<high){uint64_t middle=low+(high-low)/2u;if(class_aliases[middle].klass<klass)low=middle+1u;else high=middle;}if(low>=h->class_alias_count||class_aliases[low].klass!=klass)return 0;*descriptor=class_aliases[low].descriptor;return 1;}
static int interface_descriptor(uint64_t item,uint64_t*source,uint64_t*canonical){uint32_t shape=0;if(h->item_encoding==1u){if(!class_alias(item,source))return 0;}else *source=item;return descriptor_alias(*source,canonical,&shape)&&!!(shape&32u);}
static void free_observation(observation*o){free(o->records);free(o->vtable);free(o->interfaces);memset(o,0,sizeof(*o));}
static int observe(observation*o){o->records=calloc((SIZE_T)h->class_count,sizeof(*o->records));if(!o->records)return 0;for(uint64_t i=0;i<h->class_count;i++){uint16_t vc=0,ic=0;if(!word((uintptr_t)rows[i].klass+h->vtable_count_byte,&vc)||!word((uintptr_t)rows[i].klass+h->interface_count_byte,&ic)||vc>4096u||ic!=rows[i].interface_count){failure_index=i+1u;failure_kind=1u;free_observation(o);return 0;}if(o->vtable_count+vc<o->vtable_count||o->vtable_count+vc>50000000ull){failure_index=i+1u;failure_kind=2u;free_observation(o);return 0;}o->records[i].descriptor=rows[i].descriptor;o->records[i].klass=rows[i].klass;o->records[i].generic_index=rows[i].generic_index;o->records[i].definition_index=rows[i].definition_index;o->records[i].vtable_count=vc;o->records[i].interface_count=ic;o->records[i].vtable_start=o->vtable_count;o->records[i].interface_start=o->interface_count;o->vtable_count+=vc;o->interface_count+=ic;o->zero_count+=vc==0;o->nonzero_count+=vc!=0;}if(o->interface_count!=h->expected_interface_count){failure_kind=3u;free_observation(o);return 0;}o->vtable=calloc((SIZE_T)o->vtable_count,8u);o->interfaces=calloc((SIZE_T)o->interface_count,sizeof(*o->interfaces));if((o->vtable_count&&!o->vtable)||(o->interface_count&&!o->interfaces)){failure_kind=4u;free_observation(o);return 0;}for(uint64_t i=0;i<h->class_count;i++){output_record*r=&o->records[i];for(uint32_t j=0;j<r->vtable_count;j++){uint64_t value=0;if(!qword((uintptr_t)r->klass+h->vtable_start_byte+(uint64_t)j*8u,&value)||(value&&!executable((uintptr_t)value))){failure_index=i+1u;failure_kind=5u;free_observation(o);return 0;}o->vtable[r->vtable_start+j]=value;}if(!r->interface_count)continue;uint64_t vector=0;if(!qword((uintptr_t)r->klass+h->interface_array_byte,&vector)||!vector||!readable((uintptr_t)vector,(SIZE_T)r->interface_count*16u)){failure_index=i+1u;failure_kind=6u;free_observation(o);return 0;}uint8_t*matched=calloc((SIZE_T)r->interface_count,1u);if(!matched){failure_kind=7u;free_observation(o);return 0;}for(uint32_t j=0;j<r->interface_count;j++){uint64_t first=0,second=0,source=0,canonical=0;if(!qword((uintptr_t)vector+(uint64_t)j*16u,&first)||!qword((uintptr_t)vector+(uint64_t)j*16u+8u,&second)){free(matched);failure_index=i+1u;failure_kind=8u;free_observation(o);return 0;}uint64_t item=h->pair_encoding==1u?first:second,raw_offset=h->pair_encoding==1u?second:first;if(raw_offset>>32||raw_offset>r->vtable_count||!interface_descriptor(item,&source,&canonical)){free(matched);failure_index=i+1u;failure_kind=9u;free_observation(o);return 0;}uint32_t hits=0,hit=0;for(uint32_t k=0;k<r->interface_count;k++){uint64_t expected=expected_interfaces[rows[i].interface_start+k],expected_canonical=0;uint32_t shape=0;if(!descriptor_alias(expected,&expected_canonical,&shape)){free(matched);failure_index=i+1u;failure_kind=10u;free_observation(o);return 0;}if(!matched[k]&&expected_canonical==canonical){hits++;hit=k;}}if(hits!=1u){free(matched);failure_index=i+1u;failure_kind=11u;free_observation(o);return 0;}matched[hit]=1u;o->interfaces[r->interface_start+j].descriptor=source;o->interfaces[r->interface_start+j].offset=(uint32_t)raw_offset;}free(matched);}return 1;}
static int same_observation(const observation*a,const observation*b){return a->vtable_count==b->vtable_count&&a->interface_count==b->interface_count&&a->zero_count==b->zero_count&&a->nonzero_count==b->nonzero_count&&!memcmp(a->records,b->records,(SIZE_T)h->class_count*sizeof(output_record))&&!memcmp(a->vtable,b->vtable,(SIZE_T)a->vtable_count*8u)&&!memcmp(a->interfaces,b->interfaces,(SIZE_T)a->interface_count*sizeof(output_interface));}
static int read_all(const wchar_t*p,uint8_t**data,SIZE_T*n){FILE*f=_wfopen(p,L"rb");if(!f)return 0;if(_fseeki64(f,0,SEEK_END)||(*n=(SIZE_T)_ftelli64(f))==0||_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*data=malloc(*n);int ok=*data&&fread(*data,1,*n,f)==*n&&!fclose(f);if(!ok){free(*data);*data=NULL;}return ok;}
static void write_status(const char*state,const observation*o,int match,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"class_count\": %llu,\n  \"vtable_entry_count\": %llu,\n  \"interface_offset_count\": %llu,\n  \"zero_vtable_class_count\": %llu,\n  \"nonzero_vtable_class_count\": %llu,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"two_observations_match\": %s,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"upstream_current_runtime_layout_used\": true,\n  \"upstream_process_identity_match\": true,\n  \"saved_layout_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",state,(unsigned long)GetCurrentProcessId(),(unsigned long long)h->class_count,(unsigned long long)(o?o->vtable_count:0u),(unsigned long long)(o?o->interface_count:0u),(unsigned long long)(o?o->zero_count:0u),(unsigned long long)(o?o->nonzero_count:0u),(unsigned long long)failure_index,failure_kind,match?"true":"false",written?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);uint8_t*seed=NULL;SIZE_T bytes=0;char seed_digest[65],executable_digest[65];if(!sha256_file(seed_path,seed_digest)||strcmp(seed_digest,expected_seed_sha256)||!read_all(seed_path,&seed,&bytes)||bytes<sizeof(seed_header)){return 0;}h=(seed_header*)seed;SIZE_T required=sizeof(*h)+(SIZE_T)h->class_count*sizeof(seed_record)+(SIZE_T)h->expected_interface_count*8u+(SIZE_T)h->alias_count*sizeof(seed_alias)+(SIZE_T)h->class_alias_count*sizeof(seed_class_alias);if(memcmp(h->magic,"ALPHACW1",8)||h->version!=$seed_version||h->header_bytes!=sizeof(*h)||h->record_bytes!=sizeof(seed_record)||h->reserved||h->process_id!=GetCurrentProcessId()||!executable_identity(executable_digest)||memcmp(h->executable,executable_digest,64)||!h->class_count||h->class_count>2000000ull||h->expected_interface_count>50000000ull||h->alias_count>2000000ull||h->class_alias_count>3000000ull||bytes!=required){failure_kind=100u;write_status("identity_mismatch",NULL,0,0);free(seed);return 0;}rows=(seed_record*)(seed+sizeof(*h));expected_interfaces=(uint64_t*)((uint8_t*)rows+(SIZE_T)h->class_count*sizeof(seed_record));aliases=(seed_alias*)((uint8_t*)expected_interfaces+(SIZE_T)h->expected_interface_count*8u);class_aliases=(seed_class_alias*)((uint8_t*)aliases+(SIZE_T)h->alias_count*sizeof(seed_alias));observation first={0},second={0};if(!observe(&first)){if(!failure_kind)failure_kind=101u;write_status("capture_failed",&first,0,0);free_observation(&first);free(seed);return 0;}Sleep(250u);if(!observe(&second)){if(!failure_kind)failure_kind=102u;write_status("capture_failed",&first,0,0);free_observation(&first);free_observation(&second);free(seed);return 0;}int match=same_observation(&first,&second),written=0;if(match){FILE*f=_wfopen(output_path,L"wb");output_header out={0};memcpy(out.magic,"ALPHACV1",8);out.version=$output_version;out.header_bytes=sizeof(out);out.record_bytes=sizeof(output_record);out.interface_record_bytes=sizeof(output_interface);out.class_count=h->class_count;out.vtable_count=first.vtable_count;out.interface_count=first.interface_count;out.process_id=h->process_id;out.image_base=h->image_base;out.image_bytes=h->image_bytes;memcpy(out.executable,h->executable,64);memcpy(out.constructed,h->constructed,64);memcpy(out.reference,h->reference,64);memcpy(out.upstream,h->upstream,64);written=f&&fwrite(&out,1,sizeof(out),f)==sizeof(out)&&fwrite(first.records,sizeof(output_record),(SIZE_T)h->class_count,f)==h->class_count&&fwrite(first.vtable,8u,(SIZE_T)first.vtable_count,f)==first.vtable_count&&fwrite(first.interfaces,sizeof(output_interface),(SIZE_T)first.interface_count,f)==first.interface_count;if(f&&fclose(f))written=0;if(written)_wchmod(output_path,0600);else _wremove(output_path);}write_status(written?"complete":(match?"write_failed":"observation_unstable"),&first,match,written);free_observation(&first);free_observation(&second);free(seed);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def prepare_runtime_constructed_vtables(
    *,
    binary: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    vtable_interface_model: Path,
    vtable_interface_inventory: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        constructed_generic_model=constructed_generic_model,
        constructed_generic_inventory=constructed_generic_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        vtable_interface_model=vtable_interface_model,
        vtable_interface_inventory=vtable_interface_inventory,
    )
    seed_path = output_dir / "runtime-constructed-vtable-seed.private.bin"
    output_path = output_dir / "runtime-constructed-vtable.private.bin"
    status_path = output_dir / "runtime-constructed-vtable-status.private.json"
    model_path = output_dir / "runtime-constructed-vtable.private.json"
    for path in (output_path, status_path, model_path):
        path.unlink(missing_ok=True)
    layout = binding["layout"]
    seed = bytearray(
        _SEED_HEADER.pack(
            _SEED_MAGIC,
            _SEED_VERSION,
            _SEED_HEADER.size,
            _SEED_RECORD.size,
            0,
            len(binding["rows"]),
            len(binding["interfaces"]),
            len(binding["aliases"]),
            len(binding["class_aliases"]),
            binding["process_id"],
            binding["image_base"],
            binding["image_bytes"],
            *layout,
            binding["binary"]["sha256"].encode("ascii"),
            binding["constructed_generic_inventory"]["sha256"].encode(
                "ascii"
            ),
            binding["type_reference_inventory"]["sha256"].encode("ascii"),
            binding["vtable_interface_inventory"]["sha256"].encode("ascii"),
        )
    )
    for row in binding["rows"]:
        seed.extend(_SEED_RECORD.pack(*row))
    for descriptor in binding["interfaces"]:
        seed.extend(struct.pack("<Q", descriptor))
    for alias in binding["aliases"]:
        seed.extend(_SEED_ALIAS.pack(*alias))
    for alias in binding["class_aliases"]:
        seed.extend(_SEED_CLASS_ALIAS.pack(*alias))
    seed_path.write_bytes(seed)
    seed_path.chmod(0o600)
    seed_identity = file_identity(seed_path)

    build_dir = _owner_directory(output_dir / "build-constructed-vtable")
    source_path = build_dir / "runtime-constructed-vtable.c"
    injector_source_path = build_dir / "runtime-constructed-vtable-injector.c"
    collector_path = build_dir / (
        f"alpha-runtime-constructed-vtable-{time.time_ns():x}.dll"
    )
    injector_path = build_dir / "alpha-runtime-constructed-vtable-injector.exe"
    source = _COLLECTOR.substitute(
        seed_header_bytes=_SEED_HEADER.size,
        seed_record_bytes=_SEED_RECORD.size,
        seed_alias_bytes=_SEED_ALIAS.size,
        seed_class_alias_bytes=_SEED_CLASS_ALIAS.size,
        output_header_bytes=RUNTIME_CONSTRUCTED_VTABLE_HEADER.size,
        output_record_bytes=RUNTIME_CONSTRUCTED_VTABLE_RECORD.size,
        output_interface_bytes=RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.size,
        seed_sha256=seed_identity["sha256"],
        seed_path=_wide_literal(_windows_z_path(seed_path)),
        output_path=_wide_literal(_windows_z_path(output_path)),
        status_path=_wide_literal(_windows_z_path(status_path)),
        status_schema=RUNTIME_CONSTRUCTED_VTABLE_STATUS_SCHEMA,
        seed_version=_SEED_VERSION,
        output_version=RUNTIME_CONSTRUCTED_VTABLE_VERSION,
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
        label="runtime constructed vtable collector",
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
        label="runtime constructed vtable injector",
    )
    input_keys = (
        "constructed_generic_model",
        "constructed_generic_inventory",
        "type_reference_model",
        "type_reference_inventory",
        "vtable_interface_model",
        "vtable_interface_inventory",
        "type_identity_inventory",
    )
    plan = {
        "schema": "alpha.runtime-constructed-vtable-plan/v1",
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
            "constructed_class_count": len(binding["rows"]),
            "expected_interface_offset_count": len(binding["interfaces"]),
            "canonical_alias_count": len(binding["aliases"]),
            "class_alias_count": len(binding["class_aliases"]),
        },
        "layout_owner_only": {
            key: value
            for key, value in zip(
                (
                    "vtable_start_byte",
                    "vtable_count_byte_offset",
                    "interface_count_byte_offset",
                    "interface_array_byte_offset",
                    "interface_item_encoding",
                    "interface_pair_encoding",
                ),
                layout,
                strict=True,
            )
        },
        "seed": seed_identity,
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "policy": {
            "layout_must_be_unique_in_same_process_upstream": True,
            "all_constructed_classes_observed": True,
            "interface_pairs_match_exact_reflection_closure": True,
            "two_observations_required": True,
            "saved_layout_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(
        output_dir / "runtime-constructed-vtable-plan.private.json", plan
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
        len(raw) < RUNTIME_CONSTRUCTED_VTABLE_HEADER.size
        or len(seed) < _SEED_HEADER.size
    ):
        raise AcquisitionError("runtime constructed vtable output is truncated")
    header = RUNTIME_CONSTRUCTED_VTABLE_HEADER.unpack_from(raw)
    seed_header = _SEED_HEADER.unpack_from(seed)
    class_count, vtable_count, interface_count = header[5:8]
    records_end = (
        RUNTIME_CONSTRUCTED_VTABLE_HEADER.size
        + class_count * RUNTIME_CONSTRUCTED_VTABLE_RECORD.size
    )
    vtable_end = records_end + vtable_count * 8
    seed_records_end = _SEED_HEADER.size + class_count * _SEED_RECORD.size
    seed_interfaces_end = seed_records_end + interface_count * 8
    seed_aliases_end = (
        seed_interfaces_end + seed_header[7] * _SEED_ALIAS.size
    )
    seed_end = seed_aliases_end + seed_header[8] * _SEED_CLASS_ALIAS.size
    header_ok = (
        header[0] == RUNTIME_CONSTRUCTED_VTABLE_MAGIC
        and header[1] == RUNTIME_CONSTRUCTED_VTABLE_VERSION
        and header[2] == RUNTIME_CONSTRUCTED_VTABLE_HEADER.size
        and header[3] == RUNTIME_CONSTRUCTED_VTABLE_RECORD.size
        and header[4] == RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.size
        and class_count == plan["contract"]["constructed_class_count"]
        and interface_count
        == plan["contract"]["expected_interface_offset_count"]
        and header[8] == plan["target"]["process_id"]
        and header[9] == plan["target"]["image_base_owner_only"]
        and header[10] == plan["target"]["image_bytes"]
        and _digest(header[11], label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[12], label="constructed")
        == plan["inputs"]["constructed_generic_inventory"]["sha256"]
        and _digest(header[13], label="reference")
        == plan["inputs"]["type_reference_inventory"]["sha256"]
        and _digest(header[14], label="upstream")
        == plan["inputs"]["vtable_interface_inventory"]["sha256"]
        and vtable_end
        + interface_count * RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.size
        == len(raw)
    )
    seed_ok = (
        hashlib.sha256(seed).hexdigest() == plan["seed"]["sha256"]
        and seed_header[0] == _SEED_MAGIC
        and seed_header[1] == _SEED_VERSION
        and seed_header[2] == _SEED_HEADER.size
        and seed_header[3] == _SEED_RECORD.size
        and seed_header[4] == 0
        and seed_header[5] == class_count
        and seed_header[6] == interface_count
        and seed_header[7] == plan["contract"]["canonical_alias_count"]
        and seed_header[8] == plan["contract"]["class_alias_count"]
        and seed_header[9] == plan["target"]["process_id"]
        and seed_header[10] == plan["target"]["image_base_owner_only"]
        and seed_header[11] == plan["target"]["image_bytes"]
        and tuple(seed_header[12:18])
        == tuple(plan["layout_owner_only"].values())
        and _digest(seed_header[18], label="seed executable")
        == plan["target"]["executable_sha256"]
        and _digest(seed_header[19], label="seed constructed")
        == plan["inputs"]["constructed_generic_inventory"]["sha256"]
        and _digest(seed_header[20], label="seed reference")
        == plan["inputs"]["type_reference_inventory"]["sha256"]
        and _digest(seed_header[21], label="seed upstream")
        == plan["inputs"]["vtable_interface_inventory"]["sha256"]
        and seed_end == len(seed)
    )
    aliases: dict[int, tuple[int, int]] = {}
    if seed_ok:
        for index in range(seed_header[7]):
            source, canonical, shape, reserved = _SEED_ALIAS.unpack_from(
                seed,
                seed_interfaces_end + index * _SEED_ALIAS.size,
            )
            if (
                reserved
                or not source
                or not canonical
                or source in aliases
            ):
                seed_ok = False
                break
            aliases[source] = (canonical, shape)
    rows_ok = header_ok and seed_ok
    vtable_cursor = interface_cursor = 0
    zero_count = nonzero_count = zero_entry_count = nonzero_entry_count = 0
    distinct_vtable_counts: set[int] = set()
    for index in range(class_count if rows_ok else 0):
        seed_row = _SEED_RECORD.unpack_from(
            seed, _SEED_HEADER.size + index * _SEED_RECORD.size
        )
        row = RUNTIME_CONSTRUCTED_VTABLE_RECORD.unpack_from(
            raw,
            RUNTIME_CONSTRUCTED_VTABLE_HEADER.size
            + index * RUNTIME_CONSTRUCTED_VTABLE_RECORD.size,
        )
        descriptor, klass, generic_index, definition_index, vc, ic, vs, ios = row
        expected_interfaces = tuple(
            struct.unpack_from(
                "<Q", seed, seed_records_end + (seed_row[6] + offset) * 8
            )[0]
            for offset in range(seed_row[4])
        )
        actual_interfaces: list[int] = []
        if (
            descriptor != seed_row[0]
            or klass != seed_row[1]
            or generic_index != seed_row[2]
            or definition_index != seed_row[3]
            or ic != seed_row[4]
            or vs != vtable_cursor
            or ios != interface_cursor
            or vtable_cursor + vc > vtable_count
            or interface_cursor + ic > interface_count
        ):
            rows_ok = False
            break
        zero_count += vc == 0
        nonzero_count += vc != 0
        distinct_vtable_counts.add(vc)
        for slot in range(vc):
            value = struct.unpack_from(
                "<Q", raw, records_end + (vtable_cursor + slot) * 8
            )[0]
            zero_entry_count += value == 0
            nonzero_entry_count += value != 0
        for offset_index in range(ic):
            source, offset, reserved = (
                RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.unpack_from(
                    raw,
                    vtable_end
                    + (interface_cursor + offset_index)
                    * RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.size,
                )
            )
            alias = aliases.get(source)
            if (
                reserved
                or alias is None
                or not alias[1] & TYPE_REFERENCE_INTERFACE
                or offset > vc
            ):
                rows_ok = False
                break
            actual_interfaces.append(alias[0])
        if not rows_ok:
            break
        try:
            expected_canonical = sorted(aliases[value][0] for value in expected_interfaces)
        except KeyError:
            rows_ok = False
            break
        if sorted(actual_interfaces) != expected_canonical:
            rows_ok = False
            break
        vtable_cursor += vc
        interface_cursor += ic
    rows_ok = (
        rows_ok
        and vtable_cursor == vtable_count
        and interface_cursor == interface_count
    )
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_CONSTRUCTED_VTABLE_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "header_bound": header_ok,
        "seed_bound": seed_ok,
        "all_constructed_class_rows_valid": rows_ok,
        "all_vtable_entries_accounted": rows_ok
        and status.get("vtable_entry_count") == vtable_count,
        "all_interface_offsets_accounted": rows_ok
        and status.get("interface_offset_count") == interface_count,
        "exact_interface_closure_matches": rows_ok,
        "vtable_sample_domain_nontrivial": nonzero_count * 10 >= class_count
        and len(distinct_vtable_counts) >= 8,
        "materialized_function_domain_nontrivial": nonzero_entry_count
        > zero_entry_count,
        "two_observations_match": status.get("two_observations_match") is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
        is True,
        "upstream_layout_current_runtime_derived": status.get(
            "upstream_current_runtime_layout_used"
        )
        is True,
        "upstream_process_identity_match": status.get(
            "upstream_process_identity_match"
        )
        is True,
        "saved_layout_absent": status.get("saved_layout_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    counts = {
        "constructed_class_count": class_count,
        "vtable_entry_count": vtable_count,
        "interface_offset_count": interface_count,
        "zero_vtable_class_count": zero_count,
        "nonzero_vtable_class_count": nonzero_count,
        "zero_function_entry_count": zero_entry_count,
        "nonzero_function_entry_count": nonzero_entry_count,
        "distinct_vtable_count": len(distinct_vtable_counts),
        "inventory_sha256": hashlib.sha256(raw).hexdigest(),
    }
    return counts, checks


def load_runtime_constructed_vtables(
    *,
    model_path: Path,
    inventory_path: Path,
    expected_executable_sha256: str,
    expected_constructed_generic_inventory_sha256: str,
    expected_type_reference_inventory_sha256: str,
    expected_vtable_interface_inventory_sha256: str,
) -> dict[str, Any]:
    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    model = read_json(model_path)
    identity = file_identity(inventory_path)
    if (
        not isinstance(model, dict)
        or model.get("schema") != RUNTIME_CONSTRUCTED_VTABLE_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != expected_executable_sha256
        or model.get("inventory") != identity
        or model.get("inputs", {}).get("constructed_generic_inventory", {}).get(
            "sha256"
        )
        != expected_constructed_generic_inventory_sha256
        or model.get("inputs", {}).get("type_reference_inventory", {}).get(
            "sha256"
        )
        != expected_type_reference_inventory_sha256
        or model.get("inputs", {}).get("vtable_interface_inventory", {}).get(
            "sha256"
        )
        != expected_vtable_interface_inventory_sha256
        or not model.get("checks")
        or not all(model["checks"].values())
    ):
        raise AcquisitionError("runtime constructed vtable binding is stale")
    raw = inventory_path.read_bytes()
    if len(raw) < RUNTIME_CONSTRUCTED_VTABLE_HEADER.size:
        raise AcquisitionError("runtime constructed vtable inventory is truncated")
    header = RUNTIME_CONSTRUCTED_VTABLE_HEADER.unpack_from(raw)
    class_count, vtable_count, interface_count = header[5:8]
    records_end = (
        RUNTIME_CONSTRUCTED_VTABLE_HEADER.size
        + class_count * RUNTIME_CONSTRUCTED_VTABLE_RECORD.size
    )
    vtable_end = records_end + vtable_count * 8
    if (
        header[0] != RUNTIME_CONSTRUCTED_VTABLE_MAGIC
        or header[1] != RUNTIME_CONSTRUCTED_VTABLE_VERSION
        or header[2] != RUNTIME_CONSTRUCTED_VTABLE_HEADER.size
        or header[3] != RUNTIME_CONSTRUCTED_VTABLE_RECORD.size
        or header[4] != RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.size
        or _digest(header[11], label="executable")
        != expected_executable_sha256
        or _digest(header[12], label="constructed")
        != expected_constructed_generic_inventory_sha256
        or _digest(header[13], label="reference")
        != expected_type_reference_inventory_sha256
        or _digest(header[14], label="upstream")
        != expected_vtable_interface_inventory_sha256
        or vtable_end
        + interface_count * RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.size
        != len(raw)
    ):
        raise AcquisitionError("runtime constructed vtable header is invalid")
    return {
        "model": file_identity(model_path),
        "inventory": identity,
        "records": tuple(
            RUNTIME_CONSTRUCTED_VTABLE_RECORD.unpack_from(
                raw,
                RUNTIME_CONSTRUCTED_VTABLE_HEADER.size
                + index * RUNTIME_CONSTRUCTED_VTABLE_RECORD.size,
            )
            for index in range(class_count)
        ),
        "vtable_entries": (
            struct.unpack_from(f"<{vtable_count}Q", raw, records_end)
            if vtable_count
            else ()
        ),
        "interface_offsets": tuple(
            RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.unpack_from(
                raw,
                vtable_end
                + index * RUNTIME_CONSTRUCTED_VTABLE_INTERFACE.size,
            )
            for index in range(interface_count)
        ),
        "counts": model["counts"],
        "layout_owner_only": model["layout_owner_only"],
    }


def capture_runtime_constructed_vtables(
    *,
    binary: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    vtable_interface_model: Path,
    vtable_interface_inventory: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 900.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    plan = prepare_runtime_constructed_vtables(
        binary=binary,
        constructed_generic_model=constructed_generic_model,
        constructed_generic_inventory=constructed_generic_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        vtable_interface_model=vtable_interface_model,
        vtable_interface_inventory=vtable_interface_inventory,
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
            "runtime constructed vtable injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-constructed-vtable-injector.private.log",
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
        raise AcquisitionError("runtime constructed vtable injection failed")
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
        raise AcquisitionError("runtime constructed vtable capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime constructed vtable capture failed "
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
            "runtime constructed vtable validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    model = {
        "schema": RUNTIME_CONSTRUCTED_VTABLE_SCHEMA,
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
        "layout_owner_only": plan["layout_owner_only"],
        "policy": plan["policy"],
        "owner_only": True,
    }
    atomic_write_json(Path(plan["model_path"]), model)
    Path(plan["model_path"]).chmod(0o600)
    return model


from alpha.h01 import AcquisitionError
from alpha.p39 import capture_runtime_type_descriptor_values
from alpha.p27 import capture_runtime_constructed_generic_layout
from alpha.p28 import capture_runtime_field_type_store, capture_runtime_generic_parameter_detail_inventory
from alpha.p35 import capture_runtime_field_reference_extension
from alpha.h02 import file_identity


def capture_field_reference_fixed_point(*, root, run, pair, identity, references, materializer,
        helper, native_semantics, method_pair, generic_pair, graph_pair, reflection_semantics_model,
        maximum_rounds=32):
    if type(maximum_rounds) is not int or not 1 <= maximum_rounds <= 256:
        raise AcquisitionError("field reference fixed-point round bound is invalid")
    previous_count = None
    field_closure = None
    iteration = 0
    for iteration in range(maximum_rounds):
        suffix = "" if iteration == 0 else f"-{iteration:03d}"
        descriptors_name = "descriptor-values" + suffix
        constructed_name = "constructed-layout" + suffix
        fields_name = "field-type-store" + suffix
        references_name = "field-references" + suffix
        run(descriptors_name, capture_runtime_type_descriptor_values, dict(
            **identity, **references, live_materializer_model=materializer))
        constructed_result = run(constructed_name, capture_runtime_constructed_generic_layout, dict(
            event_capture_plan=root / "events/runtime-event-module-plan.private.json",
            **references, native_helper_model=helper, native_semantics_model=native_semantics,
            **pair(descriptors_name, "runtime-type-descriptor-values", "descriptor_value"),
            **pair("strings", "runtime-metadata-usage-values", "metadata_usage_value"),
            metadata_usage_value_status=root / "strings/runtime-metadata-usage-values-status.private.json"))
        if (constructed_result.get("constructed_selection_source") != "observed-reflection-shape"
                or constructed_result.get("native_kind_tag_used_for_selection") is not False):
            raise AcquisitionError("field reference constructed selection lacks observed Reflection shape")
        if constructed_result.get("checks",{}).get("class_extent_load_code_derived") is not True:
            raise AcquisitionError("field reference constructed extent lacks current-code derivation")
        constructed = pair(constructed_name, "runtime-constructed-generic-layout", "constructed_generic")
        field_model = root / fields_name / "runtime-field-type-store.private.json"
        run(fields_name, capture_runtime_field_type_store, dict(**constructed,
            event_capture_plan=root / "events/runtime-event-module-plan.private.json",
            member_capture_plan=root / "members/runtime-native-member-detail-plan.private.json"),
            statuses=("runtime-observed",))
        before = file_identity(references["type_reference_inventory"])
        before_model = file_identity(references["type_reference_model"])
        result = run(references_name, capture_runtime_field_reference_extension, dict(
            field_type_store_model=field_model,
            reference_capture_plan=root / "references/runtime-type-reference-plan.private.json"),
            statuses=("runtime-validated", "field-domain-closed"))
        selected = pair(references_name + "/references", "runtime-type-reference", "type_reference")
        if (result.get("native_field_domain_scope") != "nominal-and-constructed"
                or result.get("all_nominal_native_field_types_in_reference_graph") is not True):
            raise AcquisitionError("field reference fixed point omitted the nominal native field domain")
        if (result.get("reference_model") != file_identity(selected["type_reference_model"])
                or result.get("reference_inventory") != file_identity(selected["type_reference_inventory"])):
            raise AcquisitionError("field reference fixed-point stage returned another graph")
        added = result.get("new_seed_count")
        count = result.get("merged_reference_count")
        closed = result.get("field_reference_fixed_point_observed")
        if (type(added) is not int or added < 0 or type(count) is not int or count <= 0 or count < added
                or type(closed) is not bool or closed != (added == 0)
                or (previous_count is not None and count < previous_count + added)):
            raise AcquisitionError("field reference fixed-point transition is inconsistent")
        unchanged = result["reference_inventory"]["sha256"] == before["sha256"]
        if closed:
            if (not unchanged or result["status"] != "field-domain-closed"
                    or (previous_count is not None and count != previous_count)
                    or file_identity(references["type_reference_inventory"]) != before
                    or file_identity(references["type_reference_model"]) != before_model):
                raise AcquisitionError("field reference zero-increment graph changed")
            field_closure = dict(references=references, constructed=constructed, field_type_store_model=field_model,
                        rounds=iteration + 1, field_reference_fixed_point_observed=True,
                        zero_increment_reference_identity_preserved=True,
                        native_field_domain_scope="nominal-and-constructed", all_native_fields_fixed_point_observed=True,
                        native_layout_complete=False, metadata_complete=False)
            break
        if unchanged or result["status"] != "runtime-validated":
            raise AcquisitionError("field reference positive increment did not extend the graph")
        references = selected
        previous_count = count
    if field_closure is None:
        raise AcquisitionError("field reference graph did not reach a fixed point within the resource bound")
    constraint_state = _constraint_closure_phase(
        root=root, run=run, pair=pair, identity=identity, references=field_closure["references"],
        materializer=materializer, helper=helper, native_semantics=native_semantics,
        method_pair=method_pair, generic_pair=generic_pair, graph_pair=graph_pair,
        reflection_semantics_model=reflection_semantics_model,
        field_type_store_model=field_closure["field_type_store_model"],
        constructed=field_closure["constructed"], rounds=field_closure["rounds"])
    return dict(references=constraint_state["references"], constructed=constraint_state["constructed"],
                field_type_store_model=constraint_state["field_type_store_model"],
                rounds=field_closure["rounds"], field_reference_fixed_point_observed=True,
                zero_increment_reference_identity_preserved=True,
                native_field_domain_scope="nominal-and-constructed", all_native_fields_fixed_point_observed=True,
                native_layout_complete=False, metadata_complete=False,
                constraint_closure_rounds=constraint_state["constraint_closure_rounds"])


def _constraint_closure_phase(*, root, run, pair, identity, references, materializer,
        helper, native_semantics, method_pair, generic_pair, graph_pair,
        reflection_semantics_model, field_type_store_model, constructed, rounds):
    constraint_rounds = 0
    field_iteration = rounds - 1
    field_model = field_type_store_model


    anchored = True
    next_index = field_iteration + 1
    while True:
        gp_name = "generic-parameters-full" + (
            f"-c{constraint_rounds:03d}" if constraint_rounds else "")
        gp_result = run(gp_name, capture_runtime_generic_parameter_detail_inventory, dict(
            **identity, **method_pair, **generic_pair, **references,
            reflection_semantics_model=reflection_semantics_model,
            type_graph_inventory=graph_pair["type_graph_inventory"],
            selection_evidence_plan=root / "generic-parameters/runtime-generic-parameter-detail-plan.private.json",
            selection_evidence_status=root / "generic-parameters/runtime-generic-parameter-detail-status.private.json"))
        remaining = gp_result.get("counts", {}).get("new_constraint_descriptor_count")
        if remaining == 0:
            if anchored:


                return dict(references=references, constructed=constructed,
                            field_type_store_model=field_model,
                            constraint_closure_rounds=constraint_rounds)


            anchor_suffix = f"-{next_index:03d}"
            next_index += 1
            anchor_descriptors = "descriptor-values" + anchor_suffix
            anchor_constructed = "constructed-layout" + anchor_suffix
            anchor_fields = "field-type-store" + anchor_suffix
            run(anchor_descriptors, capture_runtime_type_descriptor_values, dict(
                **identity, **references, live_materializer_model=materializer))
            run(anchor_constructed, capture_runtime_constructed_generic_layout, dict(
                event_capture_plan=root / "events/runtime-event-module-plan.private.json",
                **references, native_helper_model=helper, native_semantics_model=native_semantics,
                **pair(anchor_descriptors, "runtime-type-descriptor-values", "descriptor_value"),
                **pair("strings", "runtime-metadata-usage-values", "metadata_usage_value"),
                metadata_usage_value_status=root / "strings/runtime-metadata-usage-values-status.private.json"))
            constructed = pair(anchor_constructed, "runtime-constructed-generic-layout", "constructed_generic")
            field_model = root / anchor_fields / "runtime-field-type-store.private.json"
            run(anchor_fields, capture_runtime_field_type_store, dict(**constructed,
                event_capture_plan=root / "events/runtime-event-module-plan.private.json",
                member_capture_plan=root / "members/runtime-native-member-detail-plan.private.json"),
                statuses=("runtime-observed",))


            from pathlib import Path as _Path
            if _Path(field_model).exists():
                from alpha.p28 import load_extension_source as _load_source
                from alpha.h02 import read_json as _read_json
                _model = _read_json(field_model, maximum_bytes=256 * 1024 * 1024)
                _identity = _model.get("identity", {})
                _evidence = _load_source(field_model, expected_identity=_identity,
                    allow_empty=True, include_nominal=True)
                if _evidence.get("seed_descriptors"):
                    raise AcquisitionError(
                        "constraint re-anchor revealed new field types; combined field/constraint closure required")


            return dict(references=references, constructed=constructed,
                        field_type_store_model=field_model,
                        constraint_closure_rounds=constraint_rounds)
        constraint_rounds += 1
        if constraint_rounds > 8:
            raise AcquisitionError("generic parameter constraint closure did not converge")
        round_suffix = f"-{next_index:03d}"
        next_index += 1
        descriptors_name = "descriptor-values" + round_suffix
        constructed_name = "constructed-layout" + round_suffix
        fields_name = "field-type-store" + round_suffix
        references_name = "field-references" + round_suffix
        run(descriptors_name, capture_runtime_type_descriptor_values, dict(
            **identity, **references, live_materializer_model=materializer))
        run(constructed_name, capture_runtime_constructed_generic_layout, dict(
            event_capture_plan=root / "events/runtime-event-module-plan.private.json",
            **references, native_helper_model=helper, native_semantics_model=native_semantics,
            **pair(descriptors_name, "runtime-type-descriptor-values", "descriptor_value"),
            **pair("strings", "runtime-metadata-usage-values", "metadata_usage_value"),
            metadata_usage_value_status=root / "strings/runtime-metadata-usage-values-status.private.json"))
        constructed = pair(constructed_name, "runtime-constructed-generic-layout", "constructed_generic")
        field_model = root / fields_name / "runtime-field-type-store.private.json"
        run(fields_name, capture_runtime_field_type_store, dict(**constructed,
            event_capture_plan=root / "events/runtime-event-module-plan.private.json",
            member_capture_plan=root / "members/runtime-native-member-detail-plan.private.json"),
            statuses=("runtime-observed",))
        run(references_name, capture_runtime_field_reference_extension, dict(
            field_type_store_model=field_model,
            reference_capture_plan=root / "references/runtime-type-reference-plan.private.json",
            constraint_seed_model=root / (gp_name + "/runtime-generic-parameter-detail.private.bin")),
            statuses=("runtime-validated",))
        references = pair(references_name + "/references", "runtime-type-reference", "type_reference")
        anchored = False
    return dict(references=references, constructed=constructed, field_type_store_model=field_model,
                constraint_closure_rounds=constraint_rounds)
