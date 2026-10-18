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
from alpha.p21 import RUNTIME_TYPE_GRAPH_HEADER, RUNTIME_TYPE_GRAPH_MAGIC, RUNTIME_TYPE_GRAPH_RECORD, RUNTIME_TYPE_GRAPH_SCHEMA, RUNTIME_TYPE_GRAPH_VERSION
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA, _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_RECORD, RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION, TYPE_REFERENCE_INTERFACE
from alpha.h02 import file_identity, read_json


RUNTIME_DIRECT_INTERFACE_SCHEMA = "alpha.runtime-direct-interface-inventory/v1"
RUNTIME_DIRECT_INTERFACE_STATUS_SCHEMA = (
    "alpha.runtime-direct-interface-inventory-status/v1"
)
RUNTIME_DIRECT_INTERFACE_MAGIC = b"ALPHADI1"
RUNTIME_DIRECT_INTERFACE_VERSION = 1
RUNTIME_DIRECT_INTERFACE_HEADER = struct.Struct(
    "<8sIIIIQQQQQ64s64s64s"
)
RUNTIME_DIRECT_INTERFACE_RECORD = struct.Struct("<QIIQ")

_SEED_MAGIC = b"ALPHADS1"
_SEED_VERSION = 4
_SEED_HEADER = struct.Struct("<8sIIIIQQQQQQ64s64s64s")
_SEED_RECORD = struct.Struct("<QQIII4xQ")
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
        raise AcquisitionError(f"runtime direct interface {label} is not owner-only")
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime direct interface {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(f"runtime direct interface {label} digest is invalid")
    return value


def _binding(
    *, binary: Path, type_identity_model: Path,
    type_identity_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path, type_reference_model: Path,
    type_reference_inventory: Path, constructed_generic_model: Path,
    constructed_generic_inventory: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    identity = file_identity(binary)
    identity_model_path = _owner_file(
        type_identity_model, label="type identity model"
    )
    identity_path = _owner_file(
        type_identity_inventory, label="type identity inventory"
    )
    graph_model_path = _owner_file(type_graph_model, label="type graph model")
    graph_path = _owner_file(type_graph_inventory, label="type graph inventory")
    reference_model_path = _owner_file(
        type_reference_model, label="type reference model"
    )
    reference_path = _owner_file(
        type_reference_inventory, label="type reference inventory"
    )
    constructed_model_path = _owner_file(
        constructed_generic_model, label="constructed generic model"
    )
    constructed_path = _owner_file(
        constructed_generic_inventory, label="constructed generic inventory"
    )
    identity_model = read_json(identity_model_path)
    graph_model = read_json(graph_model_path)
    reference_model = read_json(reference_model_path)
    constructed_model = read_json(constructed_model_path)
    identity_raw = identity_path.read_bytes()
    graph_raw = graph_path.read_bytes()
    reference_raw = reference_path.read_bytes()
    constructed_raw = constructed_path.read_bytes()
    if (
        len(identity_raw) < _IDENTITY_HEADER.size
        or len(graph_raw) < RUNTIME_TYPE_GRAPH_HEADER.size
        or len(reference_raw) < RUNTIME_TYPE_REFERENCE_HEADER.size
        or len(constructed_raw) < RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
    ):
        raise AcquisitionError("runtime direct interface input is truncated")
    identity_header = _IDENTITY_HEADER.unpack_from(identity_raw)
    graph_header = RUNTIME_TYPE_GRAPH_HEADER.unpack_from(graph_raw)
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
    constructed_header = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.unpack_from(
        constructed_raw
    )
    if (
        not isinstance(identity_model, dict)
        or identity_model.get("schema") != RUNTIME_TYPE_IDENTITY_SCHEMA
        or identity_model.get("status") != "runtime-validated"
        or identity_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or identity_model.get(
            "inventory", identity_model.get("identity_inventory")
        ) != file_identity(identity_path)
        or not identity_model.get("checks")
        or not all(identity_model["checks"].values())
        or not isinstance(graph_model, dict)
        or graph_model.get("schema") != RUNTIME_TYPE_GRAPH_SCHEMA
        or graph_model.get("status") != "runtime-validated"
        or graph_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or graph_model.get("inventory") != file_identity(graph_path)
        or not graph_model.get("checks")
        or not all(graph_model["checks"].values())
        or not isinstance(reference_model, dict)
        or reference_model.get("schema") != RUNTIME_TYPE_REFERENCE_SCHEMA
        or reference_model.get("status") != "runtime-validated"
        or reference_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or reference_model.get("inventory") != file_identity(reference_path)
        or not reference_model.get("checks")
        or not all(reference_model["checks"].values())
        or reference_model.get("inputs", {})
        .get("type_identity_inventory", {})
        .get("sha256")
        != file_identity(identity_path)["sha256"]
        or identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or graph_header[0] != RUNTIME_TYPE_GRAPH_MAGIC
        or graph_header[1] != RUNTIME_TYPE_GRAPH_VERSION
        or graph_header[5] != identity_header[5]
        or graph_header[8] != identity_header[6]
        or graph_header[9] != identity_header[7]
        or reference_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or reference_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or reference_header[2] != RUNTIME_TYPE_REFERENCE_HEADER.size
        or reference_header[3] != RUNTIME_TYPE_REFERENCE_RECORD.size
        or reference_header[4] != 0
        or reference_header[10] != identity_header[6]
        or reference_header[11] != identity_header[7]
        or _digest(reference_header[12], label="reference executable")
        != identity["sha256"]
        or _digest(reference_header[14], label="reference identity")
        != file_identity(identity_path)["sha256"]
        or _digest(reference_header[15], label="reference graph")
        != file_identity(graph_path)["sha256"]
        or not isinstance(constructed_model, dict)
        or constructed_model.get("schema")
        != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA
        or constructed_model.get("status") != "runtime-validated"
        or constructed_model.get("target", {}).get("executable_sha256")
        != identity["sha256"]
        or constructed_model.get("inventory") != file_identity(constructed_path)
        or not constructed_model.get("checks")
        or not all(constructed_model["checks"].values())
        or constructed_model.get("inputs", {})
        .get("type_reference_inventory", {})
        .get("sha256")
        != file_identity(reference_path)["sha256"]
        or constructed_header[0] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC
        or constructed_header[1] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
        or constructed_header[2] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        or constructed_header[3] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
        or constructed_header[7] != constructed_model.get("target", {}).get(
            "process_id"
        )
        or _digest(constructed_header[12], label="constructed executable")
        != identity["sha256"]
    ):
        raise AcquisitionError("runtime direct interface bindings are stale")
    type_count = identity_header[5]
    graph_interface_start = (
        RUNTIME_TYPE_GRAPH_HEADER.size
        + type_count * RUNTIME_TYPE_GRAPH_RECORD.size
    )
    graph_argument_start = graph_interface_start + graph_header[6] * 8
    reference_record_start = RUNTIME_TYPE_REFERENCE_HEADER.size
    reference_interface_start = (
        reference_record_start
        + reference_header[5] * RUNTIME_TYPE_REFERENCE_RECORD.size
    )
    reference_argument_start = reference_interface_start + reference_header[7] * 8
    reference_string_start = reference_argument_start + reference_header[8] * 8
    if (
        graph_argument_start + graph_header[7] * 8 != len(graph_raw)
        or reference_string_start + reference_header[9] != len(reference_raw)
    ):
        raise AcquisitionError("runtime direct interface graph is truncated")
    descriptor_deltas: set[int] = set()
    rows: list[tuple[int, int, int, int, int, int]] = []
    interfaces: list[int] = []
    aliases: list[tuple[int, int, int, int]] = []
    alias_sources: set[int] = set()
    reference_interfaces: dict[int, set[int]] = {}
    for index in range(reference_header[5]):
        reference_row = RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
            reference_raw,
            reference_record_start + index * RUNTIME_TYPE_REFERENCE_RECORD.size,
        )
        source, canonical = reference_row[:2]
        if (
            not source or source & 7 or not canonical or canonical & 7
            or source in alias_sources
        ):
            raise AcquisitionError(
                "runtime direct interface type reference aliases are invalid"
            )
        alias_sources.add(source)
        aliases.append((source, canonical, reference_row[4], 0))
        reference_count = reference_row[7]
        reference_start = reference_row[15]
        if reference_start + reference_count > reference_header[7]:
            raise AcquisitionError(
                "runtime direct interface reference range is invalid"
            )
        reference_interfaces[source] = {
            struct.unpack_from(
                "<Q", reference_raw,
                reference_interface_start + (reference_start + offset) * 8,
            )[0]
            for offset in range(reference_count)
        }
    aliases.sort()
    class_aliases: list[tuple[int, int]] = []
    class_pointers: set[int] = set()
    constructed_records_end = (
        RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        + constructed_header[5] * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
    )
    if constructed_records_end > len(constructed_raw):
        raise AcquisitionError(
            "runtime direct interface constructed generic input is truncated"
        )
    for index in range(constructed_header[5]):
        constructed_row = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.unpack_from(
            constructed_raw,
            RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
            + index * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size,
        )
        descriptor, class_pointer = constructed_row[0], constructed_row[6]
        if (
            descriptor not in alias_sources or not class_pointer
            or class_pointer & 7 or class_pointer in class_pointers
        ):
            raise AcquisitionError(
                "runtime direct interface constructed class aliases are invalid"
            )
        class_pointers.add(class_pointer)
        class_aliases.append((class_pointer, descriptor))
    class_aliases.sort()
    for index in range(type_count):
        identity_row = _IDENTITY_RECORD.unpack_from(
            identity_raw, _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size
        )
        graph_row = RUNTIME_TYPE_GRAPH_RECORD.unpack_from(
            graph_raw,
            RUNTIME_TYPE_GRAPH_HEADER.size
            + index * RUNTIME_TYPE_GRAPH_RECORD.size,
        )
        if identity_row[0] != index or not identity_row[2] or not identity_row[3]:
            raise AcquisitionError("runtime direct interface identity row is invalid")
        descriptor_deltas.add(identity_row[2] - identity_row[3])
        count = graph_row[6]
        start = len(interfaces)
        if graph_row[8] + count > graph_header[6]:
            raise AcquisitionError("runtime direct interface graph range is invalid")
        total_values = tuple(
            struct.unpack_from(
                "<Q", graph_raw,
                graph_interface_start + (graph_row[8] + offset) * 8,
            )[0]
            for offset in range(count)
        )
        interfaces.extend(total_values)
        base_descriptor = graph_row[3]
        if base_descriptor:
            base_interfaces = reference_interfaces.get(base_descriptor)
            if base_interfaces is None:
                raise AcquisitionError(
                    "runtime direct interface base reference is absent"
                )
        else:
            base_interfaces = set()
        residual = tuple(
            descriptor for descriptor in total_values
            if descriptor not in base_interfaces
        )
        minimum_count = sum(
            not any(
                descriptor in reference_interfaces.get(other, set())
                for other in residual if other != descriptor
            )
            for descriptor in residual
        )
        rows.append(
            (
                identity_row[3], identity_row[2],
                1 if identity_row[1] & 0x20 else 0,
                count, minimum_count, start,
            )
        )
    if len(descriptor_deltas) != 1:
        raise AcquisitionError(
            "runtime direct interface class/descriptor delta is not unique"
        )
    descriptor_delta = next(iter(descriptor_deltas))
    if not 0 < descriptor_delta <= 256 or descriptor_delta & 7:
        raise AcquisitionError(
            "runtime direct interface class/descriptor delta is invalid"
        )
    plan_path = _owner_file(
        identity_model_path.parent / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    plan = read_json(plan_path)
    process_id = plan.get("target", {}).get("process_id")
    if not isinstance(process_id, int) or process_id <= 0:
        raise AcquisitionError("runtime direct interface process id is absent")
    return {
        "binary": identity,
        "type_identity_model": file_identity(identity_model_path),
        "type_identity_inventory": file_identity(identity_path),
        "type_graph_model": file_identity(graph_model_path),
        "type_graph_inventory": file_identity(graph_path),
        "type_reference_model": file_identity(reference_model_path),
        "type_reference_inventory": file_identity(reference_path),
        "constructed_generic_model": file_identity(constructed_model_path),
        "constructed_generic_inventory": file_identity(constructed_path),
        "process_id": process_id,
        "image_base": identity_header[6],
        "image_bytes": identity_header[7],
        "type_count": type_count,
        "descriptor_delta": descriptor_delta,
        "rows": rows,
        "interfaces": interfaces,
        "aliases": aliases,
        "class_aliases": class_aliases,
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

typedef struct seed_header { char magic[8]; uint32_t version,header_bytes,record_bytes,reserved; uint64_t type_count,interface_count,alias_count,class_alias_count,process_id,descriptor_delta; char executable[64],identity[64],graph[64]; } seed_header;
typedef struct seed_record { uint64_t klass,descriptor; uint32_t is_enum,total_count,minimum_count,reserved; uint64_t total_start; } seed_record;
typedef struct seed_alias { uint64_t source,canonical; uint32_t shape,reserved; } seed_alias;
typedef struct seed_class_alias { uint64_t klass,descriptor; } seed_class_alias;
typedef struct output_header { char magic[8]; uint32_t version,header_bytes,record_bytes,reserved; uint64_t type_count,interface_count,process_id,image_base,image_bytes; char executable[64],identity[64],graph[64]; } output_header;
typedef struct output_record { uint64_t klass; uint32_t count,reserved; uint64_t start; } output_record;
typedef struct layout { uint32_t array_offset,entry_encoding,metadata_offset,count_byte,codec_kind,codec_key,distinct_counts; } layout;
static const DWORD expected_pid=$process_id; static const uint64_t expected_types=$type_count,expected_totals=$interface_count,expected_aliases=$alias_count,expected_class_aliases=$class_alias_count,expected_image_base=$image_base,expected_image_bytes=$image_bytes,descriptor_delta=$descriptor_delta;
static const wchar_t seed_path[]=$seed_path, output_path[]=$output_path, status_path[]=$status_path;
static const char executable_sha256[]="$executable_sha256", identity_sha256[]="$identity_sha256", graph_sha256[]="$graph_sha256";
static seed_record*rows; static uint64_t*totals; static seed_alias*aliases; static seed_class_alias*class_aliases; static uint64_t out_count; static layout selected,conflicting; static uint64_t failure_index; static uint32_t failure_kind,candidate_count;
static int readable(uintptr_t p,SIZE_T n){MEMORY_BASIC_INFORMATION m;if(!p||!n||p+n<p||!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||(m.Protect&(PAGE_NOACCESS|PAGE_GUARD)))return 0;DWORD q=m.Protect&0xff;if(q!=PAGE_READONLY&&q!=PAGE_READWRITE&&q!=PAGE_WRITECOPY&&q!=PAGE_EXECUTE_READ&&q!=PAGE_EXECUTE_READWRITE&&q!=PAGE_EXECUTE_WRITECOPY)return 0;return p+n<=(uintptr_t)m.BaseAddress+m.RegionSize;}
static int qword(uintptr_t p,uint64_t*v){if(!readable(p,8))return 0;memcpy(v,(void*)p,8);return 1;}
static int descriptor_alias(uint64_t source,uint64_t*canonical,uint32_t*shape){uint64_t low=0,high=expected_aliases;while(low<high){uint64_t middle=low+(high-low)/2u;if(aliases[middle].source<source)low=middle+1u;else high=middle;}if(low>=expected_aliases||aliases[low].source!=source)return 0;*canonical=aliases[low].canonical;*shape=aliases[low].shape;return 1;}
static int class_alias(uint64_t klass,uint64_t*descriptor){uint64_t low=0,high=expected_class_aliases;while(low<high){uint64_t middle=low+(high-low)/2u;if(class_aliases[middle].klass<klass)low=middle+1u;else high=middle;}if(low>=expected_class_aliases||class_aliases[low].klass!=klass)return 0;*descriptor=class_aliases[low].descriptor;return 1;}
static int interface_descriptor(uint64_t item,uint32_t encoding,uint64_t*source){uint64_t canonical=0;uint32_t shape=0;if(encoding==1u){if(!class_alias(item,source))*source=item+descriptor_delta;}else *source=item;return descriptor_alias(*source,&canonical,&shape)&&!!(shape&32u);}
static int counts_for(uint32_t array_offset,uint32_t encoding,uint32_t*counts,uint32_t*distinct_out){uint64_t sum=0;uint32_t distinct[256]={0},distinct_count=0;for(uint64_t i=0;i<expected_types;i++){seed_record*r=&rows[i];uint64_t vector=0;if(!qword((uintptr_t)r->klass+array_offset,&vector))return 0;uint32_t count=0;if(vector&&r->total_count&&!r->is_enum){for(;count<r->total_count;count++){uint64_t item=0,descriptor=0;if(!qword((uintptr_t)vector+(uint64_t)count*8u,&item)||!item||!interface_descriptor(item,encoding,&descriptor))break;uint32_t duplicate=0;for(uint32_t prior=0;prior<count;prior++){uint64_t previous=0,prior_descriptor=0;if(!qword((uintptr_t)vector+(uint64_t)prior*8u,&previous)||!interface_descriptor(previous,encoding,&prior_descriptor)||prior_descriptor==descriptor){duplicate=1u;break;}}if(duplicate)break;}}if(count<r->minimum_count||count>255u)return 0;counts[i]=count;sum+=count;if(!distinct[count]){distinct[count]=1;distinct_count++;}}*distinct_out=distinct_count;return sum>=100u&&distinct_count>=3u;}
static int select_layout(uint32_t*counts){uint32_t*scratch=calloc((SIZE_T)expected_types,sizeof(uint32_t));if(!scratch)return 0;candidate_count=0;memset(&conflicting,0,sizeof(conflicting));for(uint32_t array=0;array<$class_scan_bytes;array+=8u)for(uint32_t encoding=1;encoding<=2u;encoding++){uint32_t distinct=0;memset(scratch,0,(SIZE_T)expected_types*sizeof(uint32_t));if(!counts_for(array,encoding,scratch,&distinct))continue;layout value={array,encoding,0u,0u,0u,0u,distinct};candidate_count++;if(candidate_count==1u){selected=value;memcpy(counts,scratch,(SIZE_T)expected_types*sizeof(uint32_t));}else{conflicting=value;free(scratch);return 0;}}free(scratch);return candidate_count==1u;}
static int observe(output_record*records,uint64_t*values,uint64_t*value_count){uint32_t*counts=calloc((SIZE_T)expected_types,sizeof(uint32_t));if(!counts)return 0;if(!select_layout(counts)){failure_kind=10u;free(counts);return 0;}uint64_t cursor=0;for(uint64_t i=0;i<expected_types;i++){uint64_t vector=0;records[i].klass=rows[i].klass;records[i].count=counts[i];records[i].start=cursor;if(counts[i]&&!qword((uintptr_t)rows[i].klass+selected.array_offset,&vector)){failure_kind=11u;failure_index=i+1u;free(counts);return 0;}for(uint32_t j=0;j<counts[i];j++){uint64_t item=0,descriptor=0;if(!qword((uintptr_t)vector+(uint64_t)j*8u,&item)||!interface_descriptor(item,selected.entry_encoding,&descriptor)){failure_kind=12u;failure_index=i+1u;free(counts);return 0;}values[cursor++]=descriptor;}}*value_count=cursor;free(counts);return 1;}
static int read_all(const wchar_t*p,uint8_t**data,SIZE_T*n){FILE*f=_wfopen(p,L"rb");if(!f)return 0;if(_fseeki64(f,0,SEEK_END)||(*n=(SIZE_T)_ftelli64(f))==0||_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*data=malloc(*n);int ok=*data&&fread(*data,1,*n,f)==*n&&!fclose(f);if(!ok){free(*data);*data=NULL;}return ok;}
static void status(const char*s,int match,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"array_byte_offset_owner_only\": %u,\n  \"entry_encoding_owner_only\": %u,\n  \"conflicting_array_byte_offset_owner_only\": %u,\n  \"conflicting_entry_encoding_owner_only\": %u,\n  \"metadata_pointer_byte_offset_owner_only\": %u,\n  \"count_byte_offset_owner_only\": %u,\n  \"count_codec_kind_owner_only\": %u,\n  \"count_codec_key_owner_only\": %u,\n  \"distinct_direct_counts\": %u,\n  \"conflicting_distinct_direct_counts\": %u,\n  \"candidate_count\": %u,\n  \"layout_sample_count\": %llu,\n  \"canonical_alias_count\": %llu,\n  \"constructed_class_alias_count\": %llu,\n  \"direct_interface_count\": %llu,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"two_observations_match\": %s,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"saved_layout_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n+}\n",s,(unsigned long)GetCurrentProcessId(),selected.array_offset,selected.entry_encoding,conflicting.array_offset,conflicting.entry_encoding,selected.metadata_offset,selected.count_byte,selected.codec_kind,selected.codec_key,selected.distinct_counts,conflicting.distinct_counts,candidate_count,(unsigned long long)expected_types,(unsigned long long)expected_aliases,(unsigned long long)expected_class_aliases,(unsigned long long)out_count,(unsigned long long)failure_index,failure_kind,match?"true":"false",written?"true":"false");fclose(f);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);if(GetCurrentProcessId()!=expected_pid){failure_kind=100u;status("identity_mismatch",0,0);return 0;}uint8_t*seed=NULL;SIZE_T bytes=0;if(!read_all(seed_path,&seed,&bytes)||bytes<sizeof(seed_header)){failure_kind=101u;status("input_unavailable",0,0);return 0;}seed_header*h=(seed_header*)seed;if(memcmp(h->magic,"ALPHADS1",8)||h->version!=$seed_version||h->header_bytes!=sizeof(*h)||h->record_bytes!=sizeof(seed_record)||h->type_count!=expected_types||h->interface_count!=expected_totals||h->alias_count!=expected_aliases||h->class_alias_count!=expected_class_aliases||h->process_id!=expected_pid||h->descriptor_delta!=descriptor_delta||memcmp(h->executable,executable_sha256,64)||memcmp(h->identity,identity_sha256,64)||memcmp(h->graph,graph_sha256,64)||bytes!=sizeof(*h)+expected_types*sizeof(seed_record)+expected_totals*8u+expected_aliases*sizeof(seed_alias)+expected_class_aliases*sizeof(seed_class_alias)){failure_kind=102u;status("input_invalid",0,0);free(seed);return 0;}rows=(seed_record*)(seed+sizeof(*h));totals=(uint64_t*)(seed+sizeof(*h)+expected_types*sizeof(seed_record));aliases=(seed_alias*)(seed+sizeof(*h)+expected_types*sizeof(seed_record)+expected_totals*8u);class_aliases=(seed_class_alias*)((uint8_t*)aliases+expected_aliases*sizeof(seed_alias));output_record*first=calloc((SIZE_T)expected_types,sizeof(*first)),*second=calloc((SIZE_T)expected_types,sizeof(*second));uint64_t*first_values=calloc((SIZE_T)expected_totals,8u),*second_values=calloc((SIZE_T)expected_totals,8u);uint64_t first_count=0,second_count=0;if(!first||!second||!first_values||!second_values||!observe(first,first_values,&first_count)){if(!failure_kind)failure_kind=103u;status("capture_failed",0,0);free(seed);free(first);free(second);free(first_values);free(second_values);return 0;}layout first_layout=selected;candidate_count=0;memset(&selected,0,sizeof(selected));int second_ok=observe(second,second_values,&second_count);int match=second_ok&&!memcmp(&first_layout,&selected,sizeof(selected))&&first_count==second_count&&!memcmp(first,second,(SIZE_T)expected_types*sizeof(*first))&&!memcmp(first_values,second_values,(SIZE_T)first_count*8u);int written=0;if(match){FILE*f=_wfopen(output_path,L"wb");output_header o={{0}};memcpy(o.magic,"ALPHADI1",8);o.version=$output_version;o.header_bytes=sizeof(o);o.record_bytes=sizeof(output_record);o.type_count=expected_types;o.interface_count=first_count;o.process_id=expected_pid;o.image_base=expected_image_base;o.image_bytes=expected_image_bytes;memcpy(o.executable,executable_sha256,64);memcpy(o.identity,identity_sha256,64);memcpy(o.graph,graph_sha256,64);written=f&&fwrite(&o,1,sizeof(o),f)==sizeof(o)&&fwrite(first,sizeof(*first),(SIZE_T)expected_types,f)==expected_types&&fwrite(first_values,8u,(SIZE_T)first_count,f)==first_count;if(f&&fclose(f))written=0;if(!written)_wremove(output_path);else _wchmod(output_path,0600);out_count=first_count;}status(written?"complete":(match?"write_failed":"observation_unstable"),match,written);free(seed);free(first);free(second);free(first_values);free(second_values);return 0;}
BOOL WINAPI DllMain(HINSTANCE m,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(m);HANDLE t=CreateThread(NULL,0,worker,NULL,0,NULL);if(t)CloseHandle(t);}return TRUE;}
''')


def prepare_runtime_direct_interfaces(
    *, binary: Path, type_identity_model: Path,
    type_identity_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path, type_reference_model: Path,
    type_reference_inventory: Path, constructed_generic_model: Path,
    constructed_generic_inventory: Path, output_dir: Path,
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
    )
    seed_path = output_dir / "runtime-direct-interface-seed.private.bin"
    output_path = output_dir / "runtime-direct-interface.private.bin"
    status_path = output_dir / "runtime-direct-interface-status.private.json"
    model_path = output_dir / "runtime-direct-interface.private.json"
    for path in (output_path, status_path, model_path):
        path.unlink(missing_ok=True)
    seed = bytearray(
        _SEED_HEADER.pack(
            _SEED_MAGIC, _SEED_VERSION, _SEED_HEADER.size, _SEED_RECORD.size, 0,
            binding["type_count"], len(binding["interfaces"]),
            len(binding["aliases"]), len(binding["class_aliases"]),
            binding["process_id"],
            binding["descriptor_delta"],
            binding["binary"]["sha256"].encode("ascii"),
            binding["type_identity_inventory"]["sha256"].encode("ascii"),
            binding["type_graph_inventory"]["sha256"].encode("ascii"),
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
    build_dir = _owner_directory(output_dir / "build-direct-interface")
    nonce = time.time_ns()
    source_path = build_dir / "runtime-direct-interface.c"
    injector_source = build_dir / "runtime-direct-interface-injector.c"
    collector = build_dir / f"alpha-runtime-direct-interface-{nonce:x}.dll"
    injector = build_dir / "alpha-runtime-direct-interface-injector.exe"
    source = _COLLECTOR.substitute(
        process_id=binding["process_id"],
        type_count=binding["type_count"],
        interface_count=len(binding["interfaces"]),
        alias_count=len(binding["aliases"]),
        class_alias_count=len(binding["class_aliases"]),
        image_base=binding["image_base"], image_bytes=binding["image_bytes"],
        descriptor_delta=binding["descriptor_delta"],
        class_scan_bytes=264,
        seed_path=_wide_literal(_windows_z_path(seed_path)),
        output_path=_wide_literal(_windows_z_path(output_path)),
        status_path=_wide_literal(_windows_z_path(status_path)),
        executable_sha256=binding["binary"]["sha256"],
        identity_sha256=binding["type_identity_inventory"]["sha256"],
        graph_sha256=binding["type_graph_inventory"]["sha256"],
        status_schema=RUNTIME_DIRECT_INTERFACE_STATUS_SCHEMA,
        seed_version=_SEED_VERSION,
        output_version=RUNTIME_DIRECT_INTERFACE_VERSION,
    )


    source = source.replace("\\n+}\\n", "\\n}\\n").replace(
        "output_header o={{0}}", "output_header o={0}"
    )
    _private_text(source_path, source)
    _private_text(injector_source, runtime_injector_source())
    cc = _compiler(compiler)
    _build(
        [str(cc), "-shared", "-O2", "-s", "-Wall", "-Wextra",
         "-Wformat=2", "-Werror", str(source_path), "-o", str(collector),
         "-lbcrypt"],
        label="runtime direct interface collector",
    )
    _build(
        [str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
         "-Wformat=2", "-Werror", str(injector_source), "-o", str(injector)],
        label="runtime direct interface injector",
    )
    plan = {
        "schema": "alpha.runtime-direct-interface-plan/v1",
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            key: binding[key] for key in (
                "type_identity_model", "type_identity_inventory",
                "type_graph_model", "type_graph_inventory",
                "type_reference_model", "type_reference_inventory",
                "constructed_generic_model", "constructed_generic_inventory",
            )
        },
        "contract": {
            "type_count": binding["type_count"],
            "total_interface_reference_count": len(binding["interfaces"]),
            "canonical_alias_count": len(binding["aliases"]),
            "constructed_class_alias_count": len(binding["class_aliases"]),
            "descriptor_delta": binding["descriptor_delta"],
        },
        "seed": file_identity(seed_path),
        "collector": file_identity(collector),
        "injector": file_identity(injector),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "policy": {
            "all_type_definitions_constrain_layout_discovery": True,
            "direct_interface_layout_runtime_discovered": True,
            "interface_count_bounded_by_total_domain": True,
            "closure_validated_against_complete_type_reference_graph": True,
            "constructed_interfaces_resolved_from_current_class_layout": True,
            "two_observations_required": True,
            "saved_layout_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(output_dir / "runtime-direct-interface-plan.private.json", plan)
    return plan


def _validate(plan: dict[str, Any], status: dict[str, Any]) -> tuple[dict[str, Any], dict[str, bool]]:
    output = _owner_file(Path(plan["output_path"]), label="inventory")
    raw = output.read_bytes()
    if len(raw) < RUNTIME_DIRECT_INTERFACE_HEADER.size:
        raise AcquisitionError("runtime direct interface inventory is truncated")
    header = RUNTIME_DIRECT_INTERFACE_HEADER.unpack_from(raw)
    type_count, interface_count = header[5:7]
    records_end = (
        RUNTIME_DIRECT_INTERFACE_HEADER.size
        + type_count * RUNTIME_DIRECT_INTERFACE_RECORD.size
    )
    header_ok = (
        header[0] == RUNTIME_DIRECT_INTERFACE_MAGIC
        and header[1] == RUNTIME_DIRECT_INTERFACE_VERSION
        and header[2] == RUNTIME_DIRECT_INTERFACE_HEADER.size
        and header[3] == RUNTIME_DIRECT_INTERFACE_RECORD.size
        and type_count == plan["contract"]["type_count"]
        and header[7] == plan["target"]["process_id"]
        and header[8] == plan["target"]["image_base_owner_only"]
        and header[9] == plan["target"]["image_bytes"]
        and _digest(header[10], label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[11], label="identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(header[12], label="graph")
        == plan["inputs"]["type_graph_inventory"]["sha256"]
        and len(raw) == records_end + interface_count * 8
    )
    identity_raw = _owner_file(
        Path(plan["inputs"]["type_identity_inventory"]["path"]),
        label="type identity inventory",
    ).read_bytes()
    graph_raw = _owner_file(
        Path(plan["inputs"]["type_graph_inventory"]["path"]),
        label="type graph inventory",
    ).read_bytes()
    reference_raw = _owner_file(
        Path(plan["inputs"]["type_reference_inventory"]["path"]),
        label="type reference inventory",
    ).read_bytes()
    graph_header = (
        RUNTIME_TYPE_GRAPH_HEADER.unpack_from(graph_raw)
        if len(graph_raw) >= RUNTIME_TYPE_GRAPH_HEADER.size else None
    )
    graph_interface_start = (
        RUNTIME_TYPE_GRAPH_HEADER.size
        + type_count * RUNTIME_TYPE_GRAPH_RECORD.size
    )
    reference_header = (
        RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
        if len(reference_raw) >= RUNTIME_TYPE_REFERENCE_HEADER.size else None
    )
    reference_record_start = RUNTIME_TYPE_REFERENCE_HEADER.size
    reference_interface_start = (
        reference_record_start
        + (reference_header[5] if reference_header else 0)
        * RUNTIME_TYPE_REFERENCE_RECORD.size
    )
    reference_argument_start = (
        reference_interface_start
        + (reference_header[7] if reference_header else 0) * 8
    )
    reference_string_start = (
        reference_argument_start
        + (reference_header[8] if reference_header else 0) * 8
    )
    source_domains_ok = bool(
        graph_header
        and len(identity_raw) >= _IDENTITY_HEADER.size
        + type_count * _IDENTITY_RECORD.size
        and graph_header[0] == RUNTIME_TYPE_GRAPH_MAGIC
        and graph_header[1] == RUNTIME_TYPE_GRAPH_VERSION
        and graph_header[5] == type_count
        and graph_interface_start + graph_header[6] * 8 <= len(graph_raw)
        and reference_header
        and reference_header[0] == RUNTIME_TYPE_REFERENCE_MAGIC
        and reference_header[1] == RUNTIME_TYPE_REFERENCE_VERSION
        and reference_header[2] == RUNTIME_TYPE_REFERENCE_HEADER.size
        and reference_header[3] == RUNTIME_TYPE_REFERENCE_RECORD.size
        and reference_header[4] == 0
        and _digest(reference_header[12], label="reference executable")
        == plan["target"]["executable_sha256"]
        and _digest(reference_header[14], label="reference identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(reference_header[15], label="reference graph")
        == plan["inputs"]["type_graph_inventory"]["sha256"]
        and reference_string_start + reference_header[9] == len(reference_raw)
    )
    rows_ok = header_ok and source_domains_ok
    domain_resolved_ok = rows_ok
    unique_ok = rows_ok
    enum_empty_ok = rows_ok
    generator_coverage_ok = rows_ok
    cursor = 0
    direct_owner_count = 0
    semantic_alias_count = 0
    direct_by_owner: list[tuple[int, ...]] = []
    total_by_owner: list[tuple[int, ...]] = []
    reference_interfaces_by_descriptor: dict[int, tuple[int, ...]] = {}
    reference_rows_by_descriptor: dict[int, tuple[Any, ...]] = {}
    if rows_ok:
        for index in range(reference_header[5]):
            reference_row = RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
                reference_raw,
                reference_record_start
                + index * RUNTIME_TYPE_REFERENCE_RECORD.size,
            )
            descriptor = reference_row[0]
            count = reference_row[7]
            start = reference_row[15]
            if (
                not descriptor or descriptor & 7
                or start + count > reference_header[7]
                or descriptor in reference_interfaces_by_descriptor
            ):
                rows_ok = False
                break
            reference_rows_by_descriptor[descriptor] = reference_row
            reference_interfaces_by_descriptor[descriptor] = (
                struct.unpack_from(
                    f"<{count}Q", reference_raw,
                    reference_interface_start + start * 8,
                ) if count else ()
            )

    def compatible_targets(
        source: int, total_values: tuple[int, ...],
    ) -> tuple[int, ...]:
        source_row = reference_rows_by_descriptor.get(source)
        if source_row is None or not source_row[4] & TYPE_REFERENCE_INTERFACE:
            return ()
        exact = tuple(value for value in total_values if value == source)
        if exact:
            return exact
        canonical = source_row[1]
        canonical_matches = tuple(
            value for value in total_values
            if (
                value == canonical
                or reference_rows_by_descriptor.get(value, (None, None))[1]
                == source
                or reference_rows_by_descriptor.get(value, (None, None))[1]
                == canonical
            )
        )
        if canonical_matches:
            return canonical_matches
        definition = source_row[14]
        definition_row = reference_rows_by_descriptor.get(definition)
        definition_canonical = definition_row[1] if definition_row else 0
        if not definition_canonical:
            return ()
        return tuple(
            value for value in total_values
            if (
                (value_row := reference_rows_by_descriptor.get(value))
                and value_row[8] == source_row[8]
                and (
                    (value_definition_row := reference_rows_by_descriptor.get(
                        value_row[14]
                    ))
                    and value_definition_row[1] == definition_canonical
                )
            )
        )

    def saturates(
        left: tuple[int, ...], candidates: Any,
    ) -> bool:
        matched: dict[int, int] = {}

        def visit(value: int, seen: set[int]) -> bool:
            for candidate in candidates(value):
                if candidate in seen:
                    continue
                seen.add(candidate)
                if candidate not in matched or visit(matched[candidate], seen):
                    matched[candidate] = value
                    return True
            return False

        return all(visit(value, set()) for value in left)

    for index in range(type_count if rows_ok else 0):
        klass, count, reserved, start = RUNTIME_DIRECT_INTERFACE_RECORD.unpack_from(
            raw,
            RUNTIME_DIRECT_INTERFACE_HEADER.size
            + index * RUNTIME_DIRECT_INTERFACE_RECORD.size,
        )
        identity_row = _IDENTITY_RECORD.unpack_from(
            identity_raw, _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size
        )
        graph_row = RUNTIME_TYPE_GRAPH_RECORD.unpack_from(
            graph_raw,
            RUNTIME_TYPE_GRAPH_HEADER.size
            + index * RUNTIME_TYPE_GRAPH_RECORD.size,
        )
        if (
            not klass or klass & 7 or reserved or start != cursor
            or identity_row[0] != index or identity_row[3] != klass
            or graph_row[8] + graph_row[6] > graph_header[6]
        ):
            rows_ok = False
            break
        direct_values = struct.unpack_from(
            f"<{count}Q", raw, records_end + start * 8
        ) if count else ()
        total_values = struct.unpack_from(
            f"<{graph_row[6]}Q", graph_raw,
            graph_interface_start + graph_row[8] * 8,
        ) if graph_row[6] else ()
        unique_ok = unique_ok and len(set(direct_values)) == len(direct_values)
        enum_empty_ok = enum_empty_ok and not (
            identity_row[1] & 0x20 and direct_values
        )
        targets_by_source = {
            value: compatible_targets(value, total_values)
            for value in direct_values
        }
        domain_resolved_ok = domain_resolved_ok and all(
            targets_by_source.values()
        ) and saturates(
            direct_values, lambda value: targets_by_source[value]
        )
        semantic_alias_count += sum(
            value not in total_values for value in direct_values
        )
        base = graph_row[3]
        if base:
            base_interfaces = reference_interfaces_by_descriptor.get(base)
            if base_interfaces is None:
                generator_coverage_ok = False
                base_interfaces = ()
        else:
            base_interfaces = ()
        residual = tuple(
            value for value in total_values if value not in base_interfaces
        )
        generators = tuple(
            value for value in residual
            if not any(
                value in reference_interfaces_by_descriptor.get(other, ())
                for other in residual if other != value
            )
        )
        generator_coverage_ok = generator_coverage_ok and saturates(
            generators,
            lambda generator: tuple(
                source for source in direct_values
                if generator in targets_by_source[source]
            ),
        )
        direct_by_owner.append(direct_values)
        total_by_owner.append(total_values)
        cursor += count
        direct_owner_count += bool(count)
    descriptors = (
        struct.unpack_from(f"<{interface_count}Q", raw, records_end)
        if rows_ok and interface_count else ()
    )
    descriptors_ok = (
        rows_ok and cursor == interface_count
        and all(
            value and not value & 7
            and value in reference_rows_by_descriptor
            and reference_rows_by_descriptor[value][4]
            & TYPE_REFERENCE_INTERFACE
            for value in descriptors
        )
    )
    closure_exact = (
        descriptors_ok and domain_resolved_ok and generator_coverage_ok
    )
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_DIRECT_INTERFACE_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "header_bound": header_ok,
        "all_type_rows_valid": rows_ok,
        "all_direct_interface_descriptors_valid": descriptors_ok,
        "all_direct_interfaces_are_total_interfaces": descriptors_ok
        and domain_resolved_ok,
        "all_direct_interfaces_resolve_into_total_domain": descriptors_ok
        and domain_resolved_ok,
        "direct_interfaces_unique_per_owner": descriptors_ok and unique_ok,
        "enum_direct_interfaces_absent": descriptors_ok and enum_empty_ok,
        "direct_interface_count_exact": descriptors_ok and cursor == interface_count,
        "direct_interface_generators_cover_total_closure_exactly": closure_exact,
        "total_interface_closure_reconstructed_exactly": closure_exact,
        "layout_candidate_unique": status.get("candidate_count") == 1,
        "layout_full_type_domain_sampled": status.get(
            "layout_sample_count"
        ) == type_count,
        "count_domain_nontrivial": (
            isinstance(status.get("distinct_direct_counts"), int)
            and status["distinct_direct_counts"] >= 3
        ),
        "canonical_alias_domain_complete": status.get(
            "canonical_alias_count"
        ) == plan["contract"]["canonical_alias_count"],
        "constructed_class_alias_domain_complete": status.get(
            "constructed_class_alias_count"
        ) == plan["contract"]["constructed_class_alias_count"],
        "two_observations_match": status.get("two_observations_match") is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_layout_absent": status.get("saved_layout_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    return {
        "type_count": type_count,
        "direct_interface_owner_count": direct_owner_count,
        "direct_interface_count": interface_count,
        "semantic_alias_direct_interface_count": semantic_alias_count,
        "inventory_sha256": hashlib.sha256(raw).hexdigest(),
    }, checks


def load_runtime_direct_interfaces(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str,
    expected_type_identity_inventory_sha256: str,
    expected_type_graph_inventory_sha256: str,
) -> dict[str, Any]:

    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    model = read_json(model_path)
    identity = file_identity(inventory_path)
    if (
        not isinstance(model, dict)
        or model.get("schema") != RUNTIME_DIRECT_INTERFACE_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != expected_executable_sha256
        or model.get("inventory") != identity
        or model.get("inputs", {}).get("type_identity_inventory", {}).get(
            "sha256"
        ) != expected_type_identity_inventory_sha256
        or model.get("inputs", {}).get("type_graph_inventory", {}).get(
            "sha256"
        ) != expected_type_graph_inventory_sha256
        or not model.get("checks")
        or not all(model["checks"].values())
    ):
        raise AcquisitionError("runtime direct interface binding is stale")
    raw = inventory_path.read_bytes()
    if len(raw) < RUNTIME_DIRECT_INTERFACE_HEADER.size:
        raise AcquisitionError("runtime direct interface inventory is truncated")
    header = RUNTIME_DIRECT_INTERFACE_HEADER.unpack_from(raw)
    type_count, interface_count = header[5:7]
    records_end = (
        RUNTIME_DIRECT_INTERFACE_HEADER.size
        + type_count * RUNTIME_DIRECT_INTERFACE_RECORD.size
    )
    if (
        header[0] != RUNTIME_DIRECT_INTERFACE_MAGIC
        or header[1] != RUNTIME_DIRECT_INTERFACE_VERSION
        or header[2] != RUNTIME_DIRECT_INTERFACE_HEADER.size
        or header[3] != RUNTIME_DIRECT_INTERFACE_RECORD.size
        or type_count != model.get("counts", {}).get("type_count")
        or interface_count != model.get("counts", {}).get(
            "direct_interface_count"
        )
        or _digest(header[10], label="executable")
        != expected_executable_sha256
        or _digest(header[11], label="identity")
        != expected_type_identity_inventory_sha256
        or _digest(header[12], label="graph")
        != expected_type_graph_inventory_sha256
        or len(raw) != records_end + interface_count * 8
    ):
        raise AcquisitionError("runtime direct interface header is invalid")
    descriptors = (
        struct.unpack_from(f"<{interface_count}Q", raw, records_end)
        if interface_count else ()
    )
    rows: list[tuple[int, ...]] = []
    cursor = 0
    for index in range(type_count):
        row = RUNTIME_DIRECT_INTERFACE_RECORD.unpack_from(
            raw,
            RUNTIME_DIRECT_INTERFACE_HEADER.size
            + index * RUNTIME_DIRECT_INTERFACE_RECORD.size,
        )
        if not row[0] or row[0] & 7 or row[2] or row[3] != cursor:
            raise AcquisitionError("runtime direct interface row is invalid")
        cursor += row[1]
        rows.append(row)
    if cursor != interface_count or any(
        not descriptor or descriptor & 7 for descriptor in descriptors
    ):
        raise AcquisitionError(
            "runtime direct interface descriptor domain is invalid"
        )
    return {
        "model": file_identity(model_path),
        "inventory": identity,
        "rows": rows,
        "descriptors": descriptors,
        "type_count": type_count,
        "interface_count": interface_count,
    }


def capture_runtime_direct_interfaces(
    *, binary: Path, type_identity_model: Path,
    type_identity_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path, type_reference_model: Path,
    type_reference_inventory: Path, constructed_generic_model: Path,
    constructed_generic_inventory: Path, output_dir: Path, wine: Path,
    wineprefix: Path, compiler: Path | None = None,
    timeout: float = 900.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    plan = prepare_runtime_direct_interfaces(
        binary=binary,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        constructed_generic_model=constructed_generic_model,
        constructed_generic_inventory=constructed_generic_inventory,
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
        raise AcquisitionError("runtime direct interface injector could not run") from error
    _private_text(
        output_dir / "runtime-direct-interface-injector.private.log",
        json.dumps(
            {"returncode": injected.returncode, "stdout": injected.stdout,
             "stderr": injected.stderr}, ensure_ascii=False, indent=2
        ) + "\n",
    )
    if injected.returncode:
        raise AcquisitionError("runtime direct interface injection failed")
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
        raise AcquisitionError("runtime direct interface capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime direct interface capture failed "
            f"(status={status.get('status')}, kind={status.get('failure_kind_owner_only')}, "
            f"index={status.get('failure_index_owner_only')})"
        )
    _seal_runtime_output(Path(plan["output_path"]))
    _seal_runtime_output(status_path)
    counts, checks = _validate(plan, status)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime direct interface validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    model = {
        "schema": RUNTIME_DIRECT_INTERFACE_SCHEMA,
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
            "array_byte_offset": status["array_byte_offset_owner_only"],
            "entry_encoding": status["entry_encoding_owner_only"],
            "metadata_pointer_byte_offset": status[
                "metadata_pointer_byte_offset_owner_only"
            ],
            "count_byte_offset": status["count_byte_offset_owner_only"],
            "count_codec_kind": status["count_codec_kind_owner_only"],
            "count_codec_key": status["count_codec_key_owner_only"],
        },
        "owner_only": True,
    }
    _private_json(Path(plan["model_path"]), model)
    return model
