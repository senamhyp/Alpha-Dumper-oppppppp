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
from alpha.p15 import RUNTIME_CLASS_SCHEMA
from alpha.p31 import _binding as _interface_binding
from alpha.p22 import RUNTIME_METHOD_DETAIL_HEADER, RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_METHOD, RUNTIME_METHOD_DETAIL_SCHEMA, RUNTIME_METHOD_DETAIL_VERSION
from alpha.p19 import _IDENTITY_HEADER, _IDENTITY_RECORD
from alpha.h02 import atomic_write_json, file_identity, read_json


RUNTIME_VTABLE_INTERFACE_SCHEMA = (
    "alpha.runtime-vtable-interface-inventory/v1"
)
RUNTIME_VTABLE_INTERFACE_STATUS_SCHEMA = (
    "alpha.runtime-vtable-interface-inventory-status/v1"
)
RUNTIME_VTABLE_INTERFACE_MAGIC = b"ALPHAVI1"
RUNTIME_VTABLE_INTERFACE_VERSION = 1
RUNTIME_VTABLE_INTERFACE_HEADER = struct.Struct(
    "<8sIIIIQQQQQQ64s64s64s64s"
)
RUNTIME_VTABLE_INTERFACE_RECORD = struct.Struct("<QIIIIQQ")
RUNTIME_VTABLE_INTERFACE_OFFSET = struct.Struct("<QII")

_SEED_MAGIC = b"ALPHAVS1"
_SEED_VERSION = 1
_SEED_HEADER = struct.Struct("<8sIIIIQQQQQQQ64s64s64s64s")
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
            f"runtime vtable/interface {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime vtable/interface {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime vtable/interface {label} digest is invalid"
        )
    return value


def _binding(
    *,
    binary: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    type_graph_model: Path,
    type_graph_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    class_model: Path,
) -> dict[str, Any]:
    binding = _interface_binding(
        binary=binary,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        constructed_generic_model=constructed_generic_model,
        constructed_generic_inventory=constructed_generic_inventory,
    )
    method_model_path = _owner_file(
        method_detail_model, label="method detail model"
    )
    method_path = _owner_file(
        method_detail_inventory, label="method detail inventory"
    )
    class_model_path = _owner_file(class_model, label="class model")
    method_model_data = read_json(method_model_path)
    class_model_data = read_json(class_model_path)
    method_raw = method_path.read_bytes()
    if len(method_raw) < RUNTIME_METHOD_DETAIL_HEADER.size:
        raise AcquisitionError("runtime method detail input is truncated")
    method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(method_raw)
    type_count = binding["type_count"]
    method_count = method_header[5]
    method_records_end = (
        RUNTIME_METHOD_DETAIL_HEADER.size
        + method_count * RUNTIME_METHOD_DETAIL_METHOD.size
    )
    class_layout = (
        class_model_data.get("layout")
        if isinstance(class_model_data, dict)
        else None
    )
    vtable_start_qword = (
        class_layout.get("vtable_start_qword")
        if isinstance(class_layout, dict)
        else None
    )
    if (
        not isinstance(method_model_data, dict)
        or method_model_data.get("schema") != RUNTIME_METHOD_DETAIL_SCHEMA
        or method_model_data.get("status") != "runtime-validated"
        or method_model_data.get("target", {}).get("executable_sha256")
        != binding["binary"]["sha256"]
        or method_model_data.get("inputs", {})
        .get("type_identity_inventory", {})
        .get("sha256")
        != binding["type_identity_inventory"]["sha256"]
        or method_model_data.get(
            "inventory", method_model_data.get("method_detail_inventory")
        )
        != file_identity(method_path)
        or not method_model_data.get("checks")
        or not all(method_model_data["checks"].values())
        or method_model_data.get("inputs", {}).get("class_model")
        != file_identity(class_model_path)
        or not isinstance(class_model_data, dict)
        or class_model_data.get("schema") != RUNTIME_CLASS_SCHEMA
        or class_model_data.get("status") != "discovered"
        or class_model_data.get("checks", {}).get("vtable_boundary_derived")
        is not True
        or class_model_data.get("checks", {}).get("fixed_address_used")
        is not False
        or class_model_data.get("checks", {}).get("fixed_offset_used")
        is not False
        or not isinstance(vtable_start_qword, int)
        or not 8 <= vtable_start_qword <= 64
        or method_header[0] != RUNTIME_METHOD_DETAIL_MAGIC
        or method_header[1] != RUNTIME_METHOD_DETAIL_VERSION
        or method_header[2] != RUNTIME_METHOD_DETAIL_HEADER.size
        or method_header[3] != RUNTIME_METHOD_DETAIL_METHOD.size
        or method_header[4] <= 0
        or method_header[8] != binding["image_base"]
        or method_header[9] != binding["image_bytes"]
        or _digest(method_header[12], label="method executable")
        != binding["binary"]["sha256"]
        or _digest(method_header[14], label="method type identity")
        != binding["type_identity_inventory"]["sha256"]
        or method_count
        != method_model_data.get("counts", {}).get("method_count")
        or method_records_end > len(method_raw)
    ):
        raise AcquisitionError("runtime vtable/interface bindings are stale")

    minimum_vtable_counts = [0] * type_count
    for method_index in range(method_count):
        row = RUNTIME_METHOD_DETAIL_METHOD.unpack_from(
            method_raw,
            RUNTIME_METHOD_DETAIL_HEADER.size
            + method_index * RUNTIME_METHOD_DETAIL_METHOD.size,
        )
        owner, slot = row[0], row[8]
        if owner >= type_count or row[1] != method_index:
            raise AcquisitionError("runtime method detail row is invalid")
        if slot != 0xFFFF:
            minimum_vtable_counts[owner] = max(
                minimum_vtable_counts[owner], slot + 1
            )

    identity_raw = Path(binding["type_identity_inventory"]["path"]).read_bytes()
    rows: list[tuple[int, ...]] = []
    interface_offset_count = 0
    for index, direct_row in enumerate(binding["rows"]):
        identity_row = _IDENTITY_RECORD.unpack_from(
            identity_raw,
            _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size,
        )
        is_interface = bool(identity_row[7] & 0x20)
        total_count = int(direct_row[3])
        expected_offset_count = 0 if is_interface else total_count
        interface_offset_count += expected_offset_count
        rows.append(
            (
                int(direct_row[0]),
                int(direct_row[1]),
                minimum_vtable_counts[index],
                expected_offset_count,
                1 if is_interface else 0,
                0,
                int(direct_row[5]),
            )
        )
    return {
        **binding,
        "method_detail_model": file_identity(method_model_path),
        "method_detail_inventory": file_identity(method_path),
        "class_model": file_identity(class_model_path),
        "vtable_start_qword": vtable_start_qword,
        "rows": rows,
        "interface_offset_count": interface_offset_count,
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

typedef struct seed_header { char magic[8]; uint32_t version,header_bytes,record_bytes,reserved; uint64_t type_count,total_interface_count,expected_interface_offset_count,alias_count,class_alias_count,process_id,descriptor_delta; char executable[64],identity[64],graph[64],methods[64]; } seed_header;
typedef struct seed_record { uint64_t klass,descriptor; uint32_t minimum_vtable_count,interface_offset_count,is_interface,reserved; uint64_t total_start; } seed_record;
typedef struct seed_alias { uint64_t source,canonical; uint32_t shape,reserved; } seed_alias;
typedef struct seed_class_alias { uint64_t klass,descriptor; } seed_class_alias;
typedef struct output_header { char magic[8]; uint32_t version,header_bytes,record_bytes,reserved; uint64_t type_count,vtable_count,interface_offset_count,process_id,image_base,image_bytes; char executable[64],identity[64],graph[64],methods[64]; } output_header;
typedef struct output_record { uint64_t klass; uint32_t vtable_count,interface_offset_count,reserved0,reserved1; uint64_t vtable_start,interface_offset_start; } output_record;
typedef struct output_interface { uint64_t descriptor; uint32_t offset,reserved; } output_interface;
typedef struct layout { uint32_t vtable_count_byte,interface_count_byte,interface_array_byte,item_encoding,pair_encoding; uint64_t exact_vtable_support; } layout;
typedef struct observation { output_record*records; uint64_t*vtable; output_interface*interfaces; uint64_t vtable_count,interface_count; layout selected; } observation;

_Static_assert(sizeof(seed_header)==$seed_header_bytes,"seed header");
_Static_assert(sizeof(seed_record)==$seed_record_bytes,"seed record");
_Static_assert(sizeof(seed_alias)==$seed_alias_bytes,"seed alias");
_Static_assert(sizeof(seed_class_alias)==$seed_class_alias_bytes,"seed class alias");
_Static_assert(sizeof(output_header)==$output_header_bytes,"output header");
_Static_assert(sizeof(output_record)==$output_record_bytes,"output record");
_Static_assert(sizeof(output_interface)==$output_interface_bytes,"output interface");

static const DWORD expected_pid=$process_id;
static const uint64_t expected_types=$type_count,expected_totals=$total_interface_count,expected_offsets=$interface_offset_count,expected_aliases=$alias_count,expected_class_aliases=$class_alias_count,expected_image_base=$image_base,expected_image_bytes=$image_bytes,descriptor_delta=$descriptor_delta;
static const uint32_t vtable_start_bytes=$vtable_start_bytes;
static const wchar_t seed_path[]=$seed_path,output_path[]=$output_path,status_path[]=$status_path;
static const char executable_sha256[]="$executable_sha256",identity_sha256[]="$identity_sha256",graph_sha256[]="$graph_sha256",method_sha256[]="$method_sha256";
static seed_record*rows;static uint64_t*totals;static seed_alias*aliases;static seed_class_alias*class_aliases;
static uint32_t failure_kind,candidate_count,conflicting_vtable_count_byte,conflicting_interface_count_byte,conflicting_interface_array_byte,conflicting_item_encoding,conflicting_pair_encoding;static uint64_t failure_index;

static int readable(uintptr_t p,SIZE_T n){MEMORY_BASIC_INFORMATION m;if(!p||!n||p+n<p||!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||(m.Protect&(PAGE_NOACCESS|PAGE_GUARD)))return 0;DWORD q=m.Protect&0xff;if(q!=PAGE_READONLY&&q!=PAGE_READWRITE&&q!=PAGE_WRITECOPY&&q!=PAGE_EXECUTE_READ&&q!=PAGE_EXECUTE_READWRITE&&q!=PAGE_EXECUTE_WRITECOPY)return 0;return p+n<=(uintptr_t)m.BaseAddress+m.RegionSize;}
static int executable(uintptr_t p){MEMORY_BASIC_INFORMATION m;if(!p)return 0;if(!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||(m.Protect&(PAGE_NOACCESS|PAGE_GUARD)))return 0;DWORD q=m.Protect&0xff;return q==PAGE_EXECUTE||q==PAGE_EXECUTE_READ||q==PAGE_EXECUTE_READWRITE||q==PAGE_EXECUTE_WRITECOPY;}
static int qword(uintptr_t p,uint64_t*v){if(!readable(p,8u))return 0;memcpy(v,(const void*)p,8u);return 1;}
static int word(uintptr_t p,uint16_t*v){if(!readable(p,2u))return 0;memcpy(v,(const void*)p,2u);return 1;}
static int descriptor_alias(uint64_t source,uint64_t*canonical,uint32_t*shape){uint64_t low=0,high=expected_aliases;while(low<high){uint64_t middle=low+(high-low)/2u;if(aliases[middle].source<source)low=middle+1u;else high=middle;}if(low>=expected_aliases||aliases[low].source!=source)return 0;*canonical=aliases[low].canonical;*shape=aliases[low].shape;return 1;}
static int class_alias(uint64_t klass,uint64_t*descriptor){uint64_t low=0,high=expected_class_aliases;while(low<high){uint64_t middle=low+(high-low)/2u;if(class_aliases[middle].klass<klass)low=middle+1u;else high=middle;}if(low>=expected_class_aliases||class_aliases[low].klass!=klass)return 0;*descriptor=class_aliases[low].descriptor;return 1;}
static int interface_descriptor(uint64_t item,uint32_t encoding,uint64_t*source,uint64_t*canonical){uint32_t shape=0;if(encoding==1u){if(!class_alias(item,source))*source=item+descriptor_delta;}else *source=item;return descriptor_alias(*source,canonical,&shape)&&!!(shape&32u);}
static int vtable_count_candidate(uint32_t byte,uint16_t*counts,uint64_t*support_out){uint64_t support=0,positive=0;uint8_t distinct[256]={0};uint32_t distinct_count=0;for(uint64_t i=0;i<expected_types;i++){uint16_t count=0;if(!word((uintptr_t)rows[i].klass+byte,&count)||count>4096u||(count&&count<rows[i].minimum_vtable_count))return 0;if(count&&!readable((uintptr_t)rows[i].klass+vtable_start_bytes,(SIZE_T)count*8u))return 0;for(uint32_t j=0;j<count;j++){uint64_t value=0;if(!qword((uintptr_t)rows[i].klass+vtable_start_bytes+(uint64_t)j*8u,&value)||(value&&!executable((uintptr_t)value)))return 0;}counts[i]=count;support+=count&&count==rows[i].minimum_vtable_count;positive+=count!=0;if(count<256u&&!distinct[count]){distinct[count]=1;distinct_count++;}}if(support<1000u||positive<expected_types/2u||distinct_count<8u)return 0;*support_out=support;return 1;}
static int select_vtable_count(uint16_t*counts,layout*selected){uint16_t*scratch=calloc((SIZE_T)expected_types,sizeof(*scratch));if(!scratch)return 0;uint64_t best=0;uint32_t ties=0;for(uint32_t byte=0;byte+2u<=vtable_start_bytes;byte+=2u){uint64_t support=0;memset(scratch,0,(SIZE_T)expected_types*sizeof(*scratch));if(!vtable_count_candidate(byte,scratch,&support))continue;if(support>best){best=support;ties=1u;selected->vtable_count_byte=byte;selected->exact_vtable_support=support;memcpy(counts,scratch,(SIZE_T)expected_types*sizeof(*counts));}else if(support==best){ties++;conflicting_vtable_count_byte=byte;}}free(scratch);candidate_count=ties;return best&&ties==1u;}
static int select_interface_count(layout*selected){uint32_t found=0;for(uint32_t byte=0;byte+2u<=vtable_start_bytes;byte+=2u){int ok=1;for(uint64_t i=0;i<expected_types;i++){uint16_t value=0;if(!word((uintptr_t)rows[i].klass+byte,&value)||value!=rows[i].interface_offset_count){ok=0;break;}}if(ok){found++;if(found==1u)selected->interface_count_byte=byte;else conflicting_interface_count_byte=byte;}}candidate_count=found;return found==1u;}
static int interface_layout_candidate(uint32_t array_byte,uint32_t item_encoding,uint32_t pair_encoding,const uint16_t*vcounts){for(uint64_t i=0;i<expected_types;i++){seed_record*r=&rows[i];if(!r->interface_offset_count)continue;uint64_t vector=0;if(!qword((uintptr_t)r->klass+array_byte,&vector)||!vector||!readable((uintptr_t)vector,(SIZE_T)r->interface_offset_count*16u))return 0;uint8_t*matched=calloc((SIZE_T)r->interface_offset_count,1u);if(!matched)return 0;for(uint32_t j=0;j<r->interface_offset_count;j++){uint64_t first=0,second=0;if(!qword((uintptr_t)vector+(uint64_t)j*16u,&first)||!qword((uintptr_t)vector+(uint64_t)j*16u+8u,&second)){free(matched);return 0;}uint64_t item=pair_encoding==1u?first:second,raw_offset=pair_encoding==1u?second:first,source=0,canonical=0;if(raw_offset>>32||!interface_descriptor(item,item_encoding,&source,&canonical)||(vcounts[i]&&raw_offset>vcounts[i])){free(matched);return 0;}uint32_t hits=0,hit=0;for(uint32_t k=0;k<r->interface_offset_count;k++){uint64_t expected=totals[r->total_start+k],expected_canonical=0;uint32_t shape=0;if(!descriptor_alias(expected,&expected_canonical,&shape)){free(matched);return 0;}if(!matched[k]&&expected_canonical==canonical){hits++;hit=k;}}if(hits!=1u){free(matched);return 0;}matched[hit]=1u;}free(matched);}return 1;}
static int select_interface_layout(const uint16_t*vcounts,layout*selected){uint32_t found=0;for(uint32_t array=0;array+8u<=vtable_start_bytes;array+=8u)for(uint32_t item=1;item<=2u;item++)for(uint32_t pair=1;pair<=2u;pair++){if(!interface_layout_candidate(array,item,pair,vcounts))continue;found++;if(found==1u){selected->interface_array_byte=array;selected->item_encoding=item;selected->pair_encoding=pair;}else{conflicting_interface_array_byte=array;conflicting_item_encoding=item;conflicting_pair_encoding=pair;}}candidate_count=found;return found==1u;}
static void free_observation(observation*o){free(o->records);free(o->vtable);free(o->interfaces);memset(o,0,sizeof(*o));}
static int observe(observation*o){uint16_t*counts=calloc((SIZE_T)expected_types,sizeof(*counts));if(!counts)return 0;if(!select_vtable_count(counts,&o->selected)){failure_kind=10u;free(counts);return 0;}if(!select_interface_count(&o->selected)){failure_kind=11u;free(counts);return 0;}if(!select_interface_layout(counts,&o->selected)){failure_kind=12u;free(counts);return 0;}for(uint64_t i=0;i<expected_types;i++)o->vtable_count+=counts[i];o->interface_count=expected_offsets;o->records=calloc((SIZE_T)expected_types,sizeof(*o->records));o->vtable=calloc((SIZE_T)o->vtable_count,sizeof(*o->vtable));o->interfaces=calloc((SIZE_T)o->interface_count,sizeof(*o->interfaces));if(!o->records||(o->vtable_count&&!o->vtable)||(o->interface_count&&!o->interfaces)){failure_kind=13u;free(counts);free_observation(o);return 0;}uint64_t vc=0,ic=0;for(uint64_t i=0;i<expected_types;i++){seed_record*r=&rows[i];output_record*out=&o->records[i];out->klass=r->klass;out->vtable_count=counts[i];out->interface_offset_count=r->interface_offset_count;out->vtable_start=vc;out->interface_offset_start=ic;for(uint32_t j=0;j<counts[i];j++){if(!qword((uintptr_t)r->klass+vtable_start_bytes+(uint64_t)j*8u,&o->vtable[vc++])){failure_kind=14u;failure_index=i+1u;free(counts);free_observation(o);return 0;}}if(r->interface_offset_count){uint64_t vector=0;if(!qword((uintptr_t)r->klass+o->selected.interface_array_byte,&vector)){failure_kind=15u;failure_index=i+1u;free(counts);free_observation(o);return 0;}for(uint32_t j=0;j<r->interface_offset_count;j++){uint64_t first=0,second=0,source=0,canonical=0;if(!qword((uintptr_t)vector+(uint64_t)j*16u,&first)||!qword((uintptr_t)vector+(uint64_t)j*16u+8u,&second)){failure_kind=16u;failure_index=i+1u;free(counts);free_observation(o);return 0;}uint64_t item=o->selected.pair_encoding==1u?first:second,raw_offset=o->selected.pair_encoding==1u?second:first;if(!interface_descriptor(item,o->selected.item_encoding,&source,&canonical)||raw_offset>>32){failure_kind=17u;failure_index=i+1u;free(counts);free_observation(o);return 0;}o->interfaces[ic].descriptor=source;o->interfaces[ic].offset=(uint32_t)raw_offset;ic++;}}}free(counts);return vc==o->vtable_count&&ic==o->interface_count;}
static int same_observation(const observation*a,const observation*b){return !memcmp(&a->selected,&b->selected,sizeof(layout))&&a->vtable_count==b->vtable_count&&a->interface_count==b->interface_count&&!memcmp(a->records,b->records,(SIZE_T)expected_types*sizeof(output_record))&&!memcmp(a->vtable,b->vtable,(SIZE_T)a->vtable_count*8u)&&!memcmp(a->interfaces,b->interfaces,(SIZE_T)a->interface_count*sizeof(output_interface));}
static int read_all(const wchar_t*p,uint8_t**data,SIZE_T*n){FILE*f=_wfopen(p,L"rb");if(!f)return 0;if(_fseeki64(f,0,SEEK_END)||(*n=(SIZE_T)_ftelli64(f))==0||_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*data=malloc(*n);int ok=*data&&fread(*data,1,*n,f)==*n&&!fclose(f);if(!ok){free(*data);*data=NULL;}return ok;}
static void write_status(const char*s,const observation*o,int match,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"vtable_start_byte_owner_only\": %u,\n  \"vtable_count_byte_offset_owner_only\": %u,\n  \"interface_count_byte_offset_owner_only\": %u,\n  \"interface_array_byte_offset_owner_only\": %u,\n  \"interface_item_encoding_owner_only\": %u,\n  \"interface_pair_encoding_owner_only\": %u,\n  \"conflicting_vtable_count_byte_offset_owner_only\": %u,\n  \"conflicting_interface_count_byte_offset_owner_only\": %u,\n  \"conflicting_interface_array_byte_offset_owner_only\": %u,\n  \"conflicting_interface_item_encoding_owner_only\": %u,\n  \"conflicting_interface_pair_encoding_owner_only\": %u,\n  \"candidate_count\": %u,\n  \"exact_vtable_support\": %llu,\n  \"layout_sample_count\": %llu,\n  \"vtable_entry_count\": %llu,\n  \"interface_offset_count\": %llu,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"two_observations_match\": %s,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"class_boundary_current_runtime_derived\": true,\n  \"saved_layout_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",s,(unsigned long)GetCurrentProcessId(),vtable_start_bytes,o?o->selected.vtable_count_byte:0u,o?o->selected.interface_count_byte:0u,o?o->selected.interface_array_byte:0u,o?o->selected.item_encoding:0u,o?o->selected.pair_encoding:0u,conflicting_vtable_count_byte,conflicting_interface_count_byte,conflicting_interface_array_byte,conflicting_item_encoding,conflicting_pair_encoding,candidate_count,(unsigned long long)(o?o->selected.exact_vtable_support:0u),(unsigned long long)expected_types,(unsigned long long)(o?o->vtable_count:0u),(unsigned long long)(o?o->interface_count:0u),(unsigned long long)failure_index,failure_kind,match?"true":"false",written?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);if(GetCurrentProcessId()!=expected_pid){failure_kind=100u;write_status("identity_mismatch",NULL,0,0);return 0;}uint8_t*seed=NULL;SIZE_T bytes=0;if(!read_all(seed_path,&seed,&bytes)||bytes<sizeof(seed_header)){failure_kind=101u;write_status("input_unavailable",NULL,0,0);return 0;}seed_header*h=(seed_header*)seed;SIZE_T required=sizeof(*h)+(SIZE_T)expected_types*sizeof(seed_record)+(SIZE_T)expected_totals*8u+(SIZE_T)expected_aliases*sizeof(seed_alias)+(SIZE_T)expected_class_aliases*sizeof(seed_class_alias);if(memcmp(h->magic,"ALPHAVS1",8)||h->version!=$seed_version||h->header_bytes!=sizeof(*h)||h->record_bytes!=sizeof(seed_record)||h->type_count!=expected_types||h->total_interface_count!=expected_totals||h->expected_interface_offset_count!=expected_offsets||h->alias_count!=expected_aliases||h->class_alias_count!=expected_class_aliases||h->process_id!=expected_pid||h->descriptor_delta!=descriptor_delta||memcmp(h->executable,executable_sha256,64)||memcmp(h->identity,identity_sha256,64)||memcmp(h->graph,graph_sha256,64)||memcmp(h->methods,method_sha256,64)||bytes!=required){failure_kind=102u;write_status("input_invalid",NULL,0,0);free(seed);return 0;}rows=(seed_record*)(seed+sizeof(*h));totals=(uint64_t*)(seed+sizeof(*h)+(SIZE_T)expected_types*sizeof(seed_record));aliases=(seed_alias*)((uint8_t*)totals+(SIZE_T)expected_totals*8u);class_aliases=(seed_class_alias*)((uint8_t*)aliases+(SIZE_T)expected_aliases*sizeof(seed_alias));observation first={0},second={0};if(!observe(&first)){if(!failure_kind)failure_kind=103u;write_status("capture_failed",&first,0,0);free_observation(&first);free(seed);return 0;}candidate_count=0;if(!observe(&second)){if(!failure_kind)failure_kind=104u;write_status("capture_failed",&first,0,0);free_observation(&first);free_observation(&second);free(seed);return 0;}int match=same_observation(&first,&second),written=0;if(match){FILE*f=_wfopen(output_path,L"wb");output_header o={0};memcpy(o.magic,"ALPHAVI1",8);o.version=$output_version;o.header_bytes=sizeof(o);o.record_bytes=sizeof(output_record);o.type_count=expected_types;o.vtable_count=first.vtable_count;o.interface_offset_count=first.interface_count;o.process_id=expected_pid;o.image_base=expected_image_base;o.image_bytes=expected_image_bytes;memcpy(o.executable,executable_sha256,64);memcpy(o.identity,identity_sha256,64);memcpy(o.graph,graph_sha256,64);memcpy(o.methods,method_sha256,64);written=f&&fwrite(&o,1,sizeof(o),f)==sizeof(o)&&fwrite(first.records,sizeof(output_record),(SIZE_T)expected_types,f)==expected_types&&fwrite(first.vtable,8u,(SIZE_T)first.vtable_count,f)==first.vtable_count&&fwrite(first.interfaces,sizeof(output_interface),(SIZE_T)first.interface_count,f)==first.interface_count;if(f&&fclose(f))written=0;if(!written)_wremove(output_path);else _wchmod(output_path,0600);}write_status(written?"complete":(match?"write_failed":"observation_unstable"),&first,match,written);free_observation(&first);free_observation(&second);free(seed);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def prepare_runtime_vtable_interfaces(
    *,
    binary: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    type_graph_model: Path,
    type_graph_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    class_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        constructed_generic_model=constructed_generic_model,
        constructed_generic_inventory=constructed_generic_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        class_model=class_model,
    )
    seed_path = output_dir / "runtime-vtable-interface-seed.private.bin"
    output_path = output_dir / "runtime-vtable-interface.private.bin"
    status_path = output_dir / "runtime-vtable-interface-status.private.json"
    model_path = output_dir / "runtime-vtable-interface.private.json"
    for path in (output_path, status_path, model_path):
        path.unlink(missing_ok=True)
    seed = bytearray(
        _SEED_HEADER.pack(
            _SEED_MAGIC,
            _SEED_VERSION,
            _SEED_HEADER.size,
            _SEED_RECORD.size,
            0,
            binding["type_count"],
            len(binding["interfaces"]),
            binding["interface_offset_count"],
            len(binding["aliases"]),
            len(binding["class_aliases"]),
            binding["process_id"],
            binding["descriptor_delta"],
            binding["binary"]["sha256"].encode("ascii"),
            binding["type_identity_inventory"]["sha256"].encode("ascii"),
            binding["type_graph_inventory"]["sha256"].encode("ascii"),
            binding["method_detail_inventory"]["sha256"].encode("ascii"),
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

    build_dir = _owner_directory(output_dir / "build-vtable-interface")
    nonce = time.time_ns()
    source_path = build_dir / "runtime-vtable-interface.c"
    injector_source = build_dir / "runtime-vtable-interface-injector.c"
    collector = build_dir / f"alpha-runtime-vtable-interface-{nonce:x}.dll"
    injector = build_dir / "alpha-runtime-vtable-interface-injector.exe"
    source = _COLLECTOR.substitute(
        seed_header_bytes=_SEED_HEADER.size,
        seed_record_bytes=_SEED_RECORD.size,
        seed_alias_bytes=_SEED_ALIAS.size,
        seed_class_alias_bytes=_SEED_CLASS_ALIAS.size,
        output_header_bytes=RUNTIME_VTABLE_INTERFACE_HEADER.size,
        output_record_bytes=RUNTIME_VTABLE_INTERFACE_RECORD.size,
        output_interface_bytes=RUNTIME_VTABLE_INTERFACE_OFFSET.size,
        process_id=binding["process_id"],
        type_count=binding["type_count"],
        total_interface_count=len(binding["interfaces"]),
        interface_offset_count=binding["interface_offset_count"],
        alias_count=len(binding["aliases"]),
        class_alias_count=len(binding["class_aliases"]),
        image_base=binding["image_base"],
        image_bytes=binding["image_bytes"],
        descriptor_delta=binding["descriptor_delta"],
        vtable_start_bytes=binding["vtable_start_qword"] * 8,
        seed_path=_wide_literal(_windows_z_path(seed_path)),
        output_path=_wide_literal(_windows_z_path(output_path)),
        status_path=_wide_literal(_windows_z_path(status_path)),
        executable_sha256=binding["binary"]["sha256"],
        identity_sha256=binding["type_identity_inventory"]["sha256"],
        graph_sha256=binding["type_graph_inventory"]["sha256"],
        method_sha256=binding["method_detail_inventory"]["sha256"],
        status_schema=RUNTIME_VTABLE_INTERFACE_STATUS_SCHEMA,
        seed_version=_SEED_VERSION,
        output_version=RUNTIME_VTABLE_INTERFACE_VERSION,
    )
    _private_text(source_path, source)
    _private_text(injector_source, runtime_injector_source())
    cc = _compiler(compiler)
    _build(
        [
            str(cc), "-shared", "-O2", "-s", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror", str(source_path), "-o", str(collector),
        ],
        label="runtime vtable/interface collector",
    )
    _build(
        [
            str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror", str(injector_source), "-o", str(injector),
        ],
        label="runtime vtable/interface injector",
    )
    input_keys = (
        "type_identity_model",
        "type_identity_inventory",
        "type_graph_model",
        "type_graph_inventory",
        "type_reference_model",
        "type_reference_inventory",
        "constructed_generic_model",
        "constructed_generic_inventory",
        "method_detail_model",
        "method_detail_inventory",
        "class_model",
    )
    plan = {
        "schema": "alpha.runtime-vtable-interface-plan/v1",
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
            "type_count": binding["type_count"],
            "total_interface_reference_count": len(binding["interfaces"]),
            "expected_interface_offset_count": binding[
                "interface_offset_count"
            ],
            "canonical_alias_count": len(binding["aliases"]),
            "constructed_class_alias_count": len(binding["class_aliases"]),
            "descriptor_delta": binding["descriptor_delta"],
            "vtable_start_bytes": binding["vtable_start_qword"] * 8,
        },
        "seed": file_identity(seed_path),
        "collector": file_identity(collector),
        "injector": file_identity(injector),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "policy": {
            "all_type_definitions_constrain_layout_discovery": True,
            "vtable_boundary_from_current_runtime_class_model": True,
            "vtable_count_selected_by_slot_and_executable_shape": True,
            "interface_count_selected_by_exact_transitive_closure": True,
            "interface_pair_layout_selected_by_exact_type_closure": True,
            "two_observations_required": True,
            "saved_layout_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(output_dir / "runtime-vtable-interface-plan.private.json", plan)
    return plan


def _validate(
    plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = _owner_file(Path(plan["output_path"]), label="inventory")
    raw = output_path.read_bytes()
    if len(raw) < RUNTIME_VTABLE_INTERFACE_HEADER.size:
        raise AcquisitionError("runtime vtable/interface inventory is truncated")
    header = RUNTIME_VTABLE_INTERFACE_HEADER.unpack_from(raw)
    type_count, vtable_count, interface_count = header[5:8]
    records_end = (
        RUNTIME_VTABLE_INTERFACE_HEADER.size
        + type_count * RUNTIME_VTABLE_INTERFACE_RECORD.size
    )
    vtable_end = records_end + vtable_count * 8
    header_ok = (
        header[0] == RUNTIME_VTABLE_INTERFACE_MAGIC
        and header[1] == RUNTIME_VTABLE_INTERFACE_VERSION
        and header[2] == RUNTIME_VTABLE_INTERFACE_HEADER.size
        and header[3] == RUNTIME_VTABLE_INTERFACE_RECORD.size
        and header[4] == 0
        and type_count == plan["contract"]["type_count"]
        and interface_count
        == plan["contract"]["expected_interface_offset_count"]
        and header[8] == plan["target"]["process_id"]
        and header[9] == plan["target"]["image_base_owner_only"]
        and header[10] == plan["target"]["image_bytes"]
        and _digest(header[11], label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[12], label="identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(header[13], label="graph")
        == plan["inputs"]["type_graph_inventory"]["sha256"]
        and _digest(header[14], label="methods")
        == plan["inputs"]["method_detail_inventory"]["sha256"]
        and vtable_end
        + interface_count * RUNTIME_VTABLE_INTERFACE_OFFSET.size
        == len(raw)
    )
    identity_raw = _owner_file(
        Path(plan["inputs"]["type_identity_inventory"]["path"]),
        label="type identity inventory",
    ).read_bytes()
    rows_ok = header_ok
    vtable_cursor = 0
    interface_cursor = 0
    zero_vtable_count = 0
    nonzero_vtable_count = 0
    distinct_vtable_counts: set[int] = set()
    distinct_interface_offsets: set[int] = set()
    for index in range(type_count if header_ok else 0):
        row = RUNTIME_VTABLE_INTERFACE_RECORD.unpack_from(
            raw,
            RUNTIME_VTABLE_INTERFACE_HEADER.size
            + index * RUNTIME_VTABLE_INTERFACE_RECORD.size,
        )
        identity_row = _IDENTITY_RECORD.unpack_from(
            identity_raw,
            _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size,
        )
        klass, vc, ic, reserved0, reserved1, vs, ios = row
        if (
            klass != identity_row[3]
            or reserved0
            or reserved1
            or vs != vtable_cursor
            or ios != interface_cursor
            or vtable_cursor + vc > vtable_count
            or interface_cursor + ic > interface_count
            or (identity_row[7] & 0x20 and ic)
        ):
            rows_ok = False
            break
        zero_vtable_count += vc == 0
        nonzero_vtable_count += vc != 0
        distinct_vtable_counts.add(vc)
        for offset_index in range(ic):
            descriptor, offset, reserved = (
                RUNTIME_VTABLE_INTERFACE_OFFSET.unpack_from(
                    raw,
                    vtable_end
                    + (interface_cursor + offset_index)
                    * RUNTIME_VTABLE_INTERFACE_OFFSET.size,
                )
            )
            if (
                not descriptor
                or descriptor & 7
                or reserved
                or (vc and offset > vc)
            ):
                rows_ok = False
                break
            distinct_interface_offsets.add(offset)
        if not rows_ok:
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
        == RUNTIME_VTABLE_INTERFACE_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "header_bound": header_ok,
        "all_type_rows_valid": rows_ok,
        "all_vtable_entries_accounted": rows_ok
        and status.get("vtable_entry_count") == vtable_count,
        "all_interface_offsets_accounted": rows_ok
        and status.get("interface_offset_count") == interface_count,
        "vtable_count_layout_unique": status.get(
            "conflicting_vtable_count_byte_offset_owner_only"
        ) == 0,
        "interface_count_layout_unique": status.get(
            "conflicting_interface_count_byte_offset_owner_only"
        ) == 0,
        "interface_pair_layout_unique": status.get(
            "conflicting_interface_array_byte_offset_owner_only"
        ) == 0
        and status.get("conflicting_interface_item_encoding_owner_only") == 0
        and status.get("conflicting_interface_pair_encoding_owner_only") == 0,
        "layout_selection_unique": status.get("candidate_count") == 1,
        "vtable_domain_nontrivial": nonzero_vtable_count > type_count // 2
        and len(distinct_vtable_counts) >= 8,
        "interface_offset_domain_nontrivial": interface_count > 100
        and len(distinct_interface_offsets) >= 3,
        "layout_full_type_domain_sampled": status.get("layout_sample_count")
        == type_count,
        "vtable_boundary_current_runtime_derived": status.get(
            "class_boundary_current_runtime_derived"
        )
        is True
        and status.get("vtable_start_byte_owner_only")
        == plan["contract"]["vtable_start_bytes"],
        "two_observations_match": status.get("two_observations_match") is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
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
        "type_count": type_count,
        "vtable_entry_count": vtable_count,
        "interface_offset_count": interface_count,
        "zero_vtable_type_count": zero_vtable_count,
        "nonzero_vtable_type_count": nonzero_vtable_count,
        "distinct_vtable_count": len(distinct_vtable_counts),
        "distinct_interface_offset_count": len(distinct_interface_offsets),
        "inventory_sha256": hashlib.sha256(raw).hexdigest(),
    }
    return counts, checks


def load_runtime_vtable_interfaces(
    *,
    model_path: Path,
    inventory_path: Path,
    expected_executable_sha256: str,
    expected_type_identity_inventory_sha256: str,
    expected_type_graph_inventory_sha256: str,
    expected_method_detail_inventory_sha256: str,
) -> dict[str, Any]:
    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    model = read_json(model_path)
    inventory_identity = file_identity(inventory_path)
    if (
        not isinstance(model, dict)
        or model.get("schema") != RUNTIME_VTABLE_INTERFACE_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != expected_executable_sha256
        or model.get("inventory") != inventory_identity
        or model.get("inputs", {}).get("type_identity_inventory", {}).get(
            "sha256"
        )
        != expected_type_identity_inventory_sha256
        or model.get("inputs", {}).get("type_graph_inventory", {}).get(
            "sha256"
        )
        != expected_type_graph_inventory_sha256
        or model.get("inputs", {}).get("method_detail_inventory", {}).get(
            "sha256"
        )
        != expected_method_detail_inventory_sha256
        or not model.get("checks")
        or not all(model["checks"].values())
    ):
        raise AcquisitionError("runtime vtable/interface binding is stale")
    raw = inventory_path.read_bytes()
    header = RUNTIME_VTABLE_INTERFACE_HEADER.unpack_from(raw)
    type_count, vtable_count, interface_count = header[5:8]
    records_end = (
        RUNTIME_VTABLE_INTERFACE_HEADER.size
        + type_count * RUNTIME_VTABLE_INTERFACE_RECORD.size
    )
    vtable_end = records_end + vtable_count * 8
    if (
        header[0] != RUNTIME_VTABLE_INTERFACE_MAGIC
        or header[1] != RUNTIME_VTABLE_INTERFACE_VERSION
        or header[2] != RUNTIME_VTABLE_INTERFACE_HEADER.size
        or header[3] != RUNTIME_VTABLE_INTERFACE_RECORD.size
        or _digest(header[11], label="executable")
        != expected_executable_sha256
        or _digest(header[12], label="identity")
        != expected_type_identity_inventory_sha256
        or _digest(header[13], label="graph")
        != expected_type_graph_inventory_sha256
        or _digest(header[14], label="methods")
        != expected_method_detail_inventory_sha256
        or vtable_end
        + interface_count * RUNTIME_VTABLE_INTERFACE_OFFSET.size
        != len(raw)
    ):
        raise AcquisitionError("runtime vtable/interface header is invalid")
    records = [
        RUNTIME_VTABLE_INTERFACE_RECORD.unpack_from(
            raw,
            RUNTIME_VTABLE_INTERFACE_HEADER.size
            + index * RUNTIME_VTABLE_INTERFACE_RECORD.size,
        )
        for index in range(type_count)
    ]
    vtable_entries = (
        struct.unpack_from(f"<{vtable_count}Q", raw, records_end)
        if vtable_count
        else ()
    )
    interface_offsets = [
        RUNTIME_VTABLE_INTERFACE_OFFSET.unpack_from(
            raw,
            vtable_end + index * RUNTIME_VTABLE_INTERFACE_OFFSET.size,
        )
        for index in range(interface_count)
    ]
    return {
        "model": file_identity(model_path),
        "inventory": inventory_identity,
        "records": records,
        "vtable_entries": vtable_entries,
        "interface_offsets": interface_offsets,
        "counts": model["counts"],
        "layout_owner_only": model["layout_owner_only"],
    }


def capture_runtime_vtable_interfaces(
    *,
    binary: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    type_graph_model: Path,
    type_graph_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    constructed_generic_model: Path,
    constructed_generic_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    class_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 900.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    plan = prepare_runtime_vtable_interfaces(
        binary=binary,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        constructed_generic_model=constructed_generic_model,
        constructed_generic_inventory=constructed_generic_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
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
            "runtime vtable/interface injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-vtable-interface-injector.private.log",
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
        raise AcquisitionError("runtime vtable/interface injection failed")
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
        raise AcquisitionError("runtime vtable/interface capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime vtable/interface capture failed "
            f"(status={status.get('status')}, "
            f"kind={status.get('failure_kind_owner_only')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"candidates={status.get('candidate_count')})"
        )
    _seal_runtime_output(Path(plan["output_path"]))
    _seal_runtime_output(status_path)
    counts, checks = _validate(plan, status)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime vtable/interface validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    model = {
        "schema": RUNTIME_VTABLE_INTERFACE_SCHEMA,
        "status": "runtime-validated",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"],
            "process_id": plan["target"]["process_id"],
        },
        "inputs": plan["inputs"],
        "inventory": file_identity(Path(plan["output_path"])),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "layout_owner_only": {
            "vtable_start_byte": status["vtable_start_byte_owner_only"],
            "vtable_count_byte_offset": status[
                "vtable_count_byte_offset_owner_only"
            ],
            "interface_count_byte_offset": status[
                "interface_count_byte_offset_owner_only"
            ],
            "interface_array_byte_offset": status[
                "interface_array_byte_offset_owner_only"
            ],
            "interface_item_encoding": status[
                "interface_item_encoding_owner_only"
            ],
            "interface_pair_encoding": status[
                "interface_pair_encoding_owner_only"
            ],
            "exact_vtable_support": status["exact_vtable_support"],
        },
        "policy": plan["policy"],
        "owner_only": True,
    }
    atomic_write_json(Path(plan["model_path"]), model)
    Path(plan["model_path"]).chmod(0o600)
    return model
