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
from alpha.p29 import _runtime
from alpha.p38 import _binding as _proto_inventory_binding
from alpha.p42 import _field_rows
from alpha.h02 import file_identity, read_json


RUNTIME_ENUM_CONSTANT_PLAN_SCHEMA = "alpha.runtime-literal-constant-plan/v2"
RUNTIME_ENUM_CONSTANT_STATUS_SCHEMA = "alpha.runtime-literal-constant-status/v2"
RUNTIME_ENUM_CONSTANT_SCHEMA = "alpha.runtime-literal-constant-inventory/v2"
RUNTIME_ENUM_CONSTANT_MAGIC = b"ALPHALC2"
RUNTIME_ENUM_CONSTANT_VERSION = 2

RUNTIME_ENUM_CONSTANT_HEADER = struct.Struct("<8sIIIIQQQ64s64s")

RUNTIME_ENUM_CONSTANT_RECORD = struct.Struct("<IIQQQ")

CONSTANT_SIGNED = 0x100
CONSTANT_STRING = 0x200
CONSTANT_NULL = 0x400
CONSTANT_ENUM_OWNER = 0x800
CONSTANT_SINGLE = 0x1000
CONSTANT_DOUBLE = 0x2000
CONSTANT_BOOLEAN = 0x4000
CONSTANT_CHAR = 0x8000
CONSTANT_TYPED_ENUM = 0x10000

_UNDERLYING: dict[str, tuple[int, bool]] = {
    "System.SByte": (1, True),
    "System.Byte": (1, False),
    "System.Int16": (2, True),
    "System.UInt16": (2, False),
    "System.Int32": (4, True),
    "System.UInt32": (4, False),
    "System.Int64": (8, True),
    "System.UInt64": (8, False),
}

_PRIMITIVE: dict[str, tuple[int, bool, str]] = {
    **{
        name: (width, signed, "integer")
        for name, (width, signed) in _UNDERLYING.items()
    },
    "System.Boolean": (1, False, "boolean"),
    "System.Char": (2, False, "char"),
    "System.Single": (4, False, "single"),
    "System.Double": (8, False, "double"),
}


def _constant_flags(row: dict[str, Any]) -> int:
    value = int(row["width"])
    value |= CONSTANT_SIGNED if row["signed"] else 0
    value |= CONSTANT_STRING if row["value_kind"] == "string" else 0
    value |= CONSTANT_ENUM_OWNER if row["enum_owner"] else 0
    value |= CONSTANT_SINGLE if row["value_kind"] == "single" else 0
    value |= CONSTANT_DOUBLE if row["value_kind"] == "double" else 0
    value |= CONSTANT_BOOLEAN if row["value_kind"] == "boolean" else 0
    value |= CONSTANT_CHAR if row["value_kind"] == "char" else 0
    value |= CONSTANT_TYPED_ENUM if row["typed_enum"] else 0
    return value


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime enum constant {label} is not owner-only")
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
            f"runtime enum constant operation is unavailable: {key}"
        )
    return {
        "pointer": int(rows[0]["method_pointer"]),
        "metadata": int(rows[0]["metadata_pointer"]),
    }


def _binding(
    *, native_output_receipt: Path, runtime_materializer_model: Path,
) -> dict[str, Any]:
    receipt, paths, runtime = _runtime(native_output_receipt)
    inventory = _proto_inventory_binding(native_output_receipt)
    semantics_path = _owner_file(
        Path(inventory["reflection_semantics"]["path"]),
        label="reflection semantics",
    )
    if file_identity(semantics_path) != inventory["reflection_semantics"]:
        raise AcquisitionError(
            "runtime enum constant reflection semantics are stale"
        )
    semantics = read_json(semantics_path)
    raw_constant = _operation(semantics, "field.raw_constant")
    field_by_index, fields_by_owner = _field_rows(runtime)
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
            raise AcquisitionError(
                "runtime enum constant FieldInfo class is ambiguous"
            )
        field_class = live.type_row(field_class_indexes[0]).class_pointer
        field_from_handle = rebind_method(
            runtime, live, inventory["field_from_handle"]
        )
        current_raw_constant = rebind_method(runtime, live, raw_constant)
        if len({
            field_from_handle["image_delta"],
            current_raw_constant["image_delta"],
        }) != 1:
            raise AcquisitionError(
                "runtime enum constant image rebasing differs"
            )

        enum_underlying: dict[int, tuple[int, bool]] = {}
        for owner in range(runtime.type_count):
            if not runtime.renderer.identity_row(owner)[1] & 0x20:
                continue
            owner_fields = fields_by_owner.get(owner, [])
            underlying_rows = [
                field_by_index[index]
                for index in owner_fields
                if field_by_index[index]["name"] == "value__"
                or (
                    field_by_index[index]["attributes"] & 0x600 == 0x600
                    and not field_by_index[index]["attributes"] & 0x50
                )
            ]
            if len(underlying_rows) != 1:
                raise AcquisitionError(
                    "runtime enum constant underlying field is ambiguous"
                )
            underlying_name = runtime.renderer.render(
                int(underlying_rows[0]["descriptor"])
            )
            underlying = _UNDERLYING.get(underlying_name)
            if underlying is None:
                raise AcquisitionError(
                    "runtime enum constant underlying type is unsupported: "
                    + underlying_name
                )
            enum_underlying[owner] = underlying

        rows: list[dict[str, int | bool | str]] = []
        enum_constant_count = 0
        non_enum_constant_count = 0
        for owner in range(runtime.type_count):
            owner_is_enum = owner in enum_underlying
            owner_fields = fields_by_owner.get(owner, [])
            current_owner = live.type_row(owner)
            owner_descriptor = current_owner.embedded_descriptor(
                live.embedded_descriptor_byte_offset
            )
            for field_index in owner_fields:
                field = field_by_index[field_index]
                if not field["attributes"] & 0x40:
                    continue
                type_name = runtime.renderer.render(int(field["descriptor"]))
                value_kind = "integer"
                typed_enum = False
                if owner_is_enum:
                    width, signed = enum_underlying[owner]
                    enum_constant_count += 1
                elif type_name == "System.String":
                    width, signed, value_kind = 0, False, "string"
                    non_enum_constant_count += 1
                elif type_name in _PRIMITIVE:
                    width, signed, value_kind = _PRIMITIVE[type_name]
                    non_enum_constant_count += 1
                else:
                    type_owner = runtime.renderer.root_by_descriptor.get(
                        int(field["descriptor"])
                    )
                    if type_owner not in enum_underlying:
                        raise AcquisitionError(
                            "runtime literal constant type is unsupported: "
                            + type_name
                        )
                    width, signed = enum_underlying[type_owner]
                    typed_enum = True
                    non_enum_constant_count += 1
                current_field = live.field_row(field_index, expected_owner=owner)
                rows.append(
                    {
                        "field_index": field_index,
                        "owner_type_index": owner,
                        "metadata": current_field.pointer,
                        "owner_descriptor": owner_descriptor,
                        "width": width,
                        "signed": signed,
                        "value_kind": value_kind,
                        "type_name": type_name,
                        "enum_owner": owner_is_enum,
                        "typed_enum": typed_enum,
                    }
                )
        if (
            not enum_underlying
            or not rows
            or len(rows) != enum_constant_count + non_enum_constant_count
        ):
            raise AcquisitionError(
                "runtime literal constant domain is incomplete"
            )
        return {
            "receipt": file_identity(native_output_receipt.expanduser().resolve()),
            "runtime_materializer_model": file_identity(
                runtime_materializer_model.expanduser().resolve()
            ),
            "reflection_semantics": inventory["reflection_semantics"],
            "target": receipt["target"],
            "domain_policy": {
                "all_current_runtime_types_scanned": True,
                "all_current_runtime_constant_fields_scanned": True,
                "fixed_minimum_type_or_constant_count_used": False,
            },
            "binary": inventory["binary"],
            "native_member_detail_inventory": file_identity(
                paths["native_member_detail_inventory"]
            ),
            "process_id": live.process_id,
            "field_class": field_class,
            "field_from_handle": field_from_handle,
            "field_raw_constant": current_raw_constant,
            "enum_count": len(enum_underlying),
            "enum_constant_count": enum_constant_count,
            "non_enum_constant_count": non_enum_constant_count,
            "rows": rows,
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
typedef struct input_record { uint32_t field_index,flags; uintptr_t metadata,owner; } input_record;
typedef struct output_header { char magic[8]; uint32_t version,header_bytes,record_bytes,reserved; uint64_t count,string_bytes,process_id; char executable[64],native_members[64]; } output_header;
typedef struct output_record { uint32_t field_index,flags; uint64_t raw_value,string_offset,string_units; } output_record;
_Static_assert(sizeof(output_header)==$header_bytes,"enum constant header");
_Static_assert(sizeof(output_record)==$record_bytes,"enum constant record");
static const DWORD expected_pid=$process_id;
static const char executable_sha[]="$executable_sha";
static const char native_member_sha[]="$native_member_sha";
static const uintptr_t field_class=$field_class;
static const uintptr_t field_from_handle_pointer=$field_from_handle_pointer;
static const uintptr_t field_from_handle_metadata=$field_from_handle_metadata;
static const uintptr_t field_raw_constant_pointer=$field_raw_constant_pointer;
static const input_record inputs[]={$input_rows};
static const wchar_t output_path[]=$output_path;
static const wchar_t status_path[]=$status_path;
typedef uintptr_t(*static_twoarg)(uintptr_t,uintptr_t,uintptr_t);
static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_complete;
static volatile LONG probe_stage;static uint32_t failure_kind,completed_count,string_failure;
static output_record *records;static unsigned char *strings;static uint64_t string_bytes;
static int readable(uintptr_t value,SIZE_T bytes){MEMORY_BASIC_INFORMATION r;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t end=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}
typedef struct constant_contract {uintptr_t state_global,metadata_base_global,type_state_global;uint64_t type_key;uint32_t type_codec_kind,internal_offset,internal_type_offset,field_base_offset,initial_type_code_offset,field_shift,type_extra_offset,token_offset,token_xor,count_state_offset,count_add,record_stride,table_state_offset,table_codec_kind,table_key,record_match_offset,type_index_offset,data_index_offset,type_base_offset,type_record_shift,data_state_offset,data_codec_kind,data_key,type_code_offset;} constant_contract;
static constant_contract constant_decoder;
static uint32_t contract_header_candidates,contract_state_candidates,contract_lookup_candidates,contract_loop_candidates,contract_tail_candidates;
static int rip_target(uintptr_t instruction,uint32_t bytes,uintptr_t*target){int32_t displacement=0;if(bytes<5u||!readable(instruction,bytes))return 0;memcpy(&displacement,(const void*)(instruction+bytes-4u),4u);*target=instruction+bytes+(intptr_t)displacement;return *target!=0;}
static int row_offset(const unsigned char*p,uint32_t available,uint32_t*bytes,uint32_t*offset){if(available<3u||p[0]!=0x48||p[1]!=0x63||(p[2]&7u)!=0u)return 0;uint32_t mode=p[2]>>6u;if(mode==0u){*bytes=3u;*offset=0u;return 1;}if(mode==1u&&available>=4u){int8_t value=0;memcpy(&value,p+3u,1u);if(value<0)return 0;*bytes=4u;*offset=(uint32_t)value;return 1;}if(mode==2u&&available>=7u){int32_t value=0;memcpy(&value,p+3u,4u);if(value<0)return 0;*bytes=7u;*offset=(uint32_t)value;return 1;}return 0;}
static int parse_constant_contract(void){uintptr_t wrapper=field_raw_constant_pointer,target=wrapper;if(!readable(wrapper,16u))return 0;const unsigned char*w=(const unsigned char*)wrapper;if(w[0]==0xe9){int32_t displacement=0;memcpy(&displacement,w+1u,4u);target=wrapper+5u+(intptr_t)displacement;}if(!readable(target,512u))return 0;const unsigned char*b=(const unsigned char*)target;constant_contract selected={0};
for(uint32_t i=0;i+26u<=160u;i++){const unsigned char*p=b+i;if(p[0]!=0x48||p[1]!=0xb9||p[10]!=0x48||p[11]!=0x33||p[12]!=0x4f||p[14]!=0x48||p[15]!=0x2b||p[16]!=0x79||p[18]!=0x0f||p[19]!=0xb6||p[20]!=0x41)continue;uint32_t internal=0;for(uint32_t q=0;q+4u<=i;q++)if(b[q]==0x48&&b[q+1]==0x8b&&b[q+2]==0x79)internal=b[q+3];if(!internal)continue;memcpy(&selected.type_key,p+2u,8u);selected.type_codec_kind=2u;selected.internal_offset=internal;selected.internal_type_offset=p[13];selected.field_base_offset=p[17];selected.initial_type_code_offset=p[21];contract_header_candidates++;}
for(uint32_t i=0;i+31u<=160u;i++){const unsigned char*p=b+i;if(p[0]!=0x48||p[1]!=0x8b||p[2]!=0x79||!p[3])continue;for(uint32_t q=4u;q+27u<=160u-i;q++){const unsigned char*c=p+q;if(memcmp(c,"\x48\x8b\x07\x48\xba",5u)||memcmp(c+13u,"\x48\x2b\x7c\x10",4u)||memcmp(c+18u,"\x48\x8d\x0c\x10\x0f\xb6\x44\x10",8u))continue;memcpy(&selected.type_key,c+5u,8u);selected.type_codec_kind=1u;selected.internal_offset=p[3];selected.internal_type_offset=0u;selected.field_base_offset=c[17];selected.initial_type_code_offset=c[26];contract_header_candidates++;break;}}
for(uint32_t i=0;i+18u<=192u;i++){const unsigned char*p=b+i;if(p[0]!=0x48||p[1]!=0x8b||p[2]!=0x35||p[7]!=0xb8||p[12]!=0x03)continue;uint32_t offset=0;if(p[13]==0x46)offset=p[14];else if(p[13]==0x86&&i+18u<=192u)memcpy(&offset,p+14u,4u);else continue;uintptr_t global=0;if(!rip_target(target+i,7u,&global)||!readable(global,8u))continue;selected.state_global=global;memcpy(&selected.count_add,p+8u,4u);selected.count_state_offset=offset;contract_state_candidates++;}
for(uint32_t i=0;i+36u<=288u;i++){const unsigned char*p=b+i;if(memcmp(p,"\x48\xc1\xff",3u))continue;uint32_t q=4u,type_extra=0,token=0;if(p[q]!=0x48||p[q+1u]!=0x8b)continue;if(p[q+2u]==0x41){type_extra=p[q+3u];q+=4u;}else if(p[q+2u]==0x81){memcpy(&type_extra,p+q+3u,4u);q+=7u;}else continue;if(p[q]!=0x48||p[q+1u]!=0x63)continue;if(p[q+2u]==0x48){token=p[q+3u];q+=4u;}else if(p[q+2u]==0x88){memcpy(&token,p+q+3u,4u);q+=7u;}else continue;if(q+17u>288u-i||memcmp(p+q,"\x48\x81\xf1",3u))continue;uint32_t token_key=0;memcpy(&token_key,p+q+3u,4u);q+=7u;if(memcmp(p+q,"\x48\x01\xf9\x4c\x8b\x35",6u))continue;uintptr_t global=0;if(!rip_target(target+i+q+3u,7u,&global)||!readable(global,8u))continue;q+=10u;uint32_t state_offset=0,state_key=0,codec=0;if(q+8u<=288u-i&&p[q]==0xb8&&p[q+5u]==0x03){memcpy(&state_key,p+q+1u,4u);if(p[q+6u]==0x46){state_offset=p[q+7u];q+=8u;}else if(p[q+6u]==0x86&&q+11u<=288u-i){memcpy(&state_offset,p+q+7u,4u);q+=11u;}else continue;codec=1u;}else if(q+13u<=288u-i&&p[q]==0x48&&p[q+1u]==0x63&&p[q+2u]==0x86&&p[q+7u]==0x48&&p[q+8u]==0x35){memcpy(&state_offset,p+q+3u,4u);memcpy(&state_key,p+q+9u,4u);q+=13u;codec=2u;}else continue;uint32_t add_found=0;for(uint32_t z=q;z+3u<=q+5u&&z+3u<=288u-i;z++)if(!memcmp(p+z,"\x4c\x01\xf0",3u)){add_found=1;break;}if(!add_found)continue;selected.field_shift=p[3];selected.type_extra_offset=type_extra;selected.token_offset=token;selected.token_xor=token_key;selected.metadata_base_global=global;selected.table_state_offset=state_offset;selected.table_codec_kind=codec;selected.table_key=state_key;contract_lookup_candidates++;}
for(uint32_t i=0;i+32u<=320u;i++){const unsigned char*p=b+i;uint32_t row_bytes=0,match_offset=0;if(!row_offset(p,32u,&row_bytes,&match_offset)||row_bytes+3u>32u||memcmp(p+row_bytes,"\x48\x39\xd9",3u))continue;for(uint32_t q=row_bytes+3u;q+4u<=32u;q++)if(p[q]==0x48&&p[q+1]==0x83&&p[q+2]==0xc0&&p[q+3]>=8u&&p[q+3]<=64u){selected.record_match_offset=match_offset;selected.record_stride=p[q+3];contract_loop_candidates++;break;}}
for(uint32_t i=0;i+112u<=480u;i++){const unsigned char*p=b+i;uint32_t first_bytes=0,type_index=0;if(!row_offset(p,112u,&first_bytes,&type_index)||first_bytes<4u)continue;uintptr_t type_global=0;uint32_t type_base=0,type_shift=0,data_state=0,data_key=0,data_codec=0,type_code=0,data_index=UINT32_MAX;int got_global=0,got_base=0,got_data=0,got_code=0;for(uint32_t q=first_bytes;q+4u<=112u;q++){const unsigned char*c=p+q;if(!got_global&&q+7u<=112u&&c[0]==0x48&&c[1]==0x8b&&c[2]==0x0d&&rip_target(target+i+q,7u,&type_global)){got_global=1;continue;}if(got_global&&!type_shift&&q+4u<=112u&&c[0]==0x48&&c[1]==0xc1&&c[2]==0xe7){type_shift=c[3];continue;}if(got_global&&!got_base&&c[0]==0x48&&c[1]==0x03&&(c[2]==0x79||c[2]==0xb9)){if(c[2]==0x79)type_base=c[3];else if(q+7u<=112u)memcpy(&type_base,c+3u,4u);else continue;got_base=1;continue;}if(got_base&&data_index==UINT32_MAX){uint32_t ignored=0,offset=0;if(row_offset(c,112u-q,&ignored,&offset)){data_index=offset;continue;}}if(!got_data&&q+11u<=112u&&c[0]==0xb9&&c[5]==0x03&&c[6]==0x8e){memcpy(&data_key,c+1u,4u);memcpy(&data_state,c+7u,4u);data_codec=1u;got_data=1;continue;}if(!got_data&&q+17u<=112u&&c[0]==0x48&&c[1]==0x63&&c[2]==0x8e&&c[7]==0x48&&c[8]==0x81&&c[9]==0xf1){memcpy(&data_state,c+3u,4u);memcpy(&data_key,c+10u,4u);data_codec=2u;got_data=1;continue;}if(got_data&&!got_code&&c[0]==0x0f&&c[1]==0xbe&&c[2]==0x47){type_code=c[3];got_code=1;break;}}if(!got_global||!got_base||!got_data||!got_code||data_index==UINT32_MAX||!readable(type_global,8u))continue;selected.type_index_offset=type_index;selected.data_index_offset=data_index;selected.type_state_global=type_global;selected.type_record_shift=type_shift;selected.type_base_offset=type_base;selected.data_state_offset=data_state;selected.data_codec_kind=data_codec;selected.data_key=data_key;selected.type_code_offset=type_code;contract_tail_candidates++;}
if(contract_header_candidates!=1u||contract_state_candidates!=1u||contract_lookup_candidates!=1u||contract_loop_candidates!=1u||contract_tail_candidates!=1u||selected.type_codec_kind<1u||selected.type_codec_kind>2u||selected.table_codec_kind<1u||selected.table_codec_kind>2u||selected.data_codec_kind<1u||selected.data_codec_kind>2u||selected.field_shift<3u||selected.field_shift>8u||selected.type_record_shift<3u||selected.type_record_shift>8u||selected.record_stride<8u||selected.record_stride>64u)return 0;constant_decoder=selected;return 1;}
typedef struct constant_entry { int32_t key,type_index,data_index; } constant_entry;
static constant_entry*constant_entries;static uint32_t constant_entry_count;static uintptr_t constant_metadata_base,constant_type_base,constant_data_base;
static int compare_constant_entry(const void*left,const void*right){int32_t a=((const constant_entry*)left)->key,b=((const constant_entry*)right)->key;return a<b?-1:a>b?1:0;}
static int64_t decode_state_offset(int32_t raw,uint32_t kind,uint32_t key){if(kind==1u)return(int64_t)(int32_t)((uint32_t)raw+key);if(kind==2u)return(int64_t)raw^(int64_t)(int32_t)key;return INT64_MIN;}
static int prepare_constant_index(void){const constant_contract*c=&constant_decoder;uintptr_t state=0,type_state=0,table=0;int32_t count_raw=0,table_raw=0,data_raw=0;if(c->record_match_offset+4u>c->record_stride||c->type_index_offset+4u>c->record_stride||c->data_index_offset+4u>c->record_stride||!readable(c->state_global,8u)||!readable(c->metadata_base_global,8u)||!readable(c->type_state_global,8u))return 0;memcpy(&state,(const void*)c->state_global,8u);memcpy(&constant_metadata_base,(const void*)c->metadata_base_global,8u);memcpy(&type_state,(const void*)c->type_state_global,8u);if(!state||!constant_metadata_base||!type_state||!readable(state+c->count_state_offset,4u)||!readable(state+c->table_state_offset,4u)||!readable(state+c->data_state_offset,4u)||!readable(type_state+c->type_base_offset,8u))return 0;memcpy(&count_raw,(const void*)(state+c->count_state_offset),4u);memcpy(&table_raw,(const void*)(state+c->table_state_offset),4u);memcpy(&data_raw,(const void*)(state+c->data_state_offset),4u);int32_t count=(int32_t)((uint32_t)count_raw+c->count_add);int64_t table_offset=decode_state_offset(table_raw,c->table_codec_kind,c->table_key),data_offset=decode_state_offset(data_raw,c->data_codec_kind,c->data_key);if(count<=0||count%c->record_stride||count>268435456||table_offset==INT64_MIN||data_offset==INT64_MIN)return 0;constant_entry_count=(uint32_t)count/c->record_stride;table=constant_metadata_base+(intptr_t)table_offset;constant_data_base=constant_metadata_base+(intptr_t)data_offset;memcpy(&constant_type_base,(const void*)(type_state+c->type_base_offset),8u);if(!constant_entry_count||!constant_type_base||!readable(table,(SIZE_T)(uint32_t)count)||!readable(constant_data_base,1u))return 0;constant_entries=(constant_entry*)malloc((size_t)constant_entry_count*sizeof(constant_entry));if(!constant_entries)return 0;for(uint32_t i=0;i<constant_entry_count;i++){uintptr_t row=table+(uintptr_t)i*c->record_stride;memcpy(&constant_entries[i].key,(const void*)(row+c->record_match_offset),4u);memcpy(&constant_entries[i].type_index,(const void*)(row+c->type_index_offset),4u);memcpy(&constant_entries[i].data_index,(const void*)(row+c->data_index_offset),4u);if(constant_entries[i].type_index<0)return 0;}qsort(constant_entries,constant_entry_count,sizeof(constant_entry),compare_constant_entry);for(uint32_t i=1;i<constant_entry_count;i++)if(constant_entries[i-1u].key==constant_entries[i].key)return 0;return 1;}
static int locate_constant(uintptr_t field,uintptr_t*data,uint32_t*type_code){const constant_contract*c=&constant_decoder;uintptr_t internal=0,encoded_type=0,type=0,field_base=0,type_extra=0;if(!readable(field+c->internal_offset,8u))return 0;memcpy(&internal,(const void*)(field+c->internal_offset),8u);if(!internal||!readable(internal+c->internal_type_offset,8u))return 0;memcpy(&encoded_type,(const void*)(internal+c->internal_type_offset),8u);if(c->type_codec_kind==1u)type=encoded_type+(uintptr_t)c->type_key;else if(c->type_codec_kind==2u)type=encoded_type^c->type_key;else return 0;if(!type||!readable(type,c->field_base_offset+8u)||!readable(type+c->type_extra_offset,8u))return 0;memcpy(&field_base,(const void*)(type+c->field_base_offset),8u);if(internal<field_base)return 0;uintptr_t delta=internal-field_base,mask=((uintptr_t)1u<<c->field_shift)-1u;if(delta&mask)return 0;uintptr_t field_index=delta>>c->field_shift;memcpy(&type_extra,(const void*)(type+c->type_extra_offset),8u);if(!type_extra||!readable(type_extra+c->token_offset,4u))return 0;int32_t token_raw=0;memcpy(&token_raw,(const void*)(type_extra+c->token_offset),4u);uint64_t lookup=((uint64_t)(int64_t)token_raw)^((uint64_t)(int64_t)(int32_t)c->token_xor);lookup+=field_index;if((uint64_t)(int64_t)(int32_t)lookup!=lookup)return 0;int32_t key=(int32_t)lookup;uint32_t low=0,high=constant_entry_count;while(low<high){uint32_t middle=low+(high-low)/2u;if(constant_entries[middle].key<key)low=middle+1u;else high=middle;}if(low>=constant_entry_count||constant_entries[low].key!=key)return 0;int32_t found_type=constant_entries[low].type_index,found_data=constant_entries[low].data_index;uintptr_t type_record=constant_type_base+((uintptr_t)(uint32_t)found_type<<c->type_record_shift);if(!readable(type_record+c->type_code_offset,1u))return 0;int8_t code=0;memcpy(&code,(const void*)(type_record+c->type_code_offset),1u);*type_code=(uint32_t)(uint8_t)code;if(found_data<0){*data=0;return 1;}uintptr_t value=constant_data_base+(uintptr_t)(uint32_t)found_data;if(!readable(value,1u))return 0;*data=value;return 1;}
static int object_class(uintptr_t object,uintptr_t expected){uintptr_t observed=0;if(!readable(object,sizeof(observed)))return 0;memcpy(&observed,(const void*)object,sizeof(observed));return observed==expected;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE f=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL,*buffer=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,os);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(a,&h,object,os,NULL,0,0)<0)ok=0;while(ok){DWORD n=0;if(!ReadFile(f,buffer,1048576u,&n,NULL)){ok=0;break;}if(!n)break;if(BCryptHashData(h,buffer,n,0)<0)ok=0;}if(ok&&BCryptFinishHash(h,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,output);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(f);return ok;}
static int executable_identity(char output[65]){wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,(DWORD)(sizeof(p)/sizeof(p[0])));return n&&n<sizeof(p)/sizeof(p[0])&&sha256_file(p,output);}
static int raw_value(uintptr_t field,uint32_t flags,uint64_t*value){uintptr_t first=0,second=0;uint32_t first_code=0,second_code=0,width=flags&0xffu;if((width!=1u&&width!=2u&&width!=4u&&width!=8u)||!locate_constant(field,&first,&first_code)||!locate_constant(field,&second,&second_code)||!first||first!=second||first_code!=second_code||!readable(first,width))return 0;uint64_t observed=0;memcpy(&observed,(const void*)first,width);*value=observed;return 1;}
static int decode_utf8_units(uintptr_t source,uint32_t expected,uint32_t*source_bytes,uint16_t*output){uint32_t cursor=0,produced=0;while(produced<expected){if(!readable(source+cursor,1u))return 0;unsigned char lead=*(const unsigned char*)(source+cursor);uint32_t code=0,width=0;if(lead<0x80u){code=lead;width=1u;}else if(lead>=0xc2u&&lead<=0xdfu){code=lead&0x1fu;width=2u;}else if(lead>=0xe0u&&lead<=0xefu){code=lead&0x0fu;width=3u;}else if(lead>=0xf0u&&lead<=0xf4u){code=lead&7u;width=4u;}else return 0;if(cursor+width<cursor||!readable(source+cursor,width))return 0;for(uint32_t i=1;i<width;i++){unsigned char next=*(const unsigned char*)(source+cursor+i);if((next&0xc0u)!=0x80u)return 0;code=(code<<6u)|(next&0x3fu);}if((width==2u&&code<0x80u)||(width==3u&&code<0x800u)||(width==4u&&code<0x10000u)||code>0x10ffffu||(code>=0xd800u&&code<=0xdfffu))return 0;uint32_t units=code>=0x10000u?2u:1u;if(produced+units>expected)return 0;if(output){if(units==1u)output[produced]=(uint16_t)code;else{code-=0x10000u;output[produced]=(uint16_t)(0xd800u+(code>>10u));output[produced+1u]=(uint16_t)(0xdc00u+(code&0x3ffu));}}produced+=units;cursor+=width;}*source_bytes=cursor;return 1;}
static int string_value(uintptr_t field,output_record*record){uintptr_t first=0,second=0;uint32_t first_code=0,second_code=0;if(!locate_constant(field,&first,&first_code)||first_code!=0x0eu)return string_failure=1,0;if(!first){if(!locate_constant(field,&second,&second_code)||second||second_code!=first_code)return string_failure=1,0;record->flags|=0x400u;return 1;}int32_t first_units=0,second_units=0;if(!readable(first,4u))return string_failure=2,0;memcpy(&first_units,(const void*)first,4u);if(first_units<0||first_units>16777216)return string_failure=3,0;uint32_t source_bytes=0,second_source_bytes=0;if(!decode_utf8_units(first+4u,(uint32_t)first_units,&source_bytes,NULL))return string_failure=8,0;if(!locate_constant(field,&second,&second_code)||second!=first||second_code!=first_code||!readable(second,4u))return string_failure=1,0;memcpy(&second_units,(const void*)second,4u);if(second_units!=first_units||!decode_utf8_units(second+4u,(uint32_t)second_units,&second_source_bytes,NULL)||second_source_bytes!=source_bytes||(source_bytes&&memcmp((const void*)(first+4u),(const void*)(second+4u),source_bytes)))return string_failure=5,0;uint64_t bytes=(uint64_t)(uint32_t)first_units*2u;if(string_bytes+bytes<string_bytes||string_bytes+bytes>SIZE_MAX)return string_failure=6,0;unsigned char*next=(unsigned char*)realloc(strings,(size_t)(string_bytes+bytes));if(bytes&&!next)return string_failure=7,0;strings=next;uint32_t final_source_bytes=0;if(first_units&&!decode_utf8_units(second+4u,(uint32_t)second_units,&final_source_bytes,(uint16_t*)(void*)(strings+string_bytes)))return string_failure=8,0;if(final_source_bytes!=source_bytes)return string_failure=5,0;record->string_offset=string_bytes;record->string_units=(uint64_t)(uint32_t)first_units;string_bytes+=bytes;return 1;}
static int collect_batch(void){static_twoarg from_handle=(static_twoarg)field_from_handle_pointer;if(!records){records=(output_record*)calloc($row_count,sizeof(output_record));if(!records)return failure_kind=1,0;}uint32_t end=completed_count+512u;if(end<$row_count&&end<completed_count)return failure_kind=1,0;if(end>$row_count)end=$row_count;for(uint32_t i=completed_count;i<end;i++){InterlockedExchange(&probe_stage,(LONG)(1000u+i));uintptr_t field=from_handle(inputs[i].metadata,inputs[i].owner,field_from_handle_metadata);if(!object_class(field,field_class))return failure_kind=2,0;records[i].field_index=inputs[i].field_index;records[i].flags=inputs[i].flags;if(inputs[i].flags&0x200u){if(!string_value(field,&records[i]))return failure_kind=30u+string_failure,0;}else{uint64_t first=0,second=0;if(!raw_value(field,inputs[i].flags,&first)||!raw_value(field,inputs[i].flags,&second))return failure_kind=3,0;if(first!=second)return failure_kind=4,0;records[i].raw_value=first;}completed_count=i+1u;}if(completed_count==$row_count)InterlockedExchange(&probe_stage,2);return 1;}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);int ok=collect_batch();InterlockedExchange(&callback_complete,ok?1:-1);return ok;}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;
static BOOL CALLBACK select_window(HWND w,LPARAM v){selection*s=(selection*)(uintptr_t)v;DWORD pid=0;RECT b;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){s->window=w;s->count++;}return TRUE;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window)return failure_kind=5,0;message_id=RegisterWindowMessageW(status_path);SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);int ok=message_id&&(original_proc||GetLastError()==ERROR_SUCCESS);while(ok&&completed_count<$row_count){DWORD_PTR result=0;InterlockedExchange(&callback_complete,0);ok=SendMessageTimeoutW(s.window,message_id,0,0,SMTO_BLOCK,60000,&result)&&InterlockedCompareExchange(&callback_complete,0,0)==1;}if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);if(!ok&&!failure_kind)failure_kind=6;return ok;}
static int write_output(void){output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"ALPHALC2",8);h.version=2;h.header_bytes=sizeof(h);h.record_bytes=sizeof(output_record);h.count=$row_count;h.string_bytes=string_bytes;h.process_id=GetCurrentProcessId();memcpy(h.executable,executable_sha,64);memcpy(h.native_members,native_member_sha,64);FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;int ok=fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(records,sizeof(output_record),$row_count,f)==$row_count&&fwrite(strings,1,(size_t)string_bytes,f)==string_bytes;if(fclose(f))ok=0;if(!ok)_wremove(output_path);else _wchmod(output_path,0600);return ok;}
static void write_status(const char*status,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"expected_count\": %u,\n  \"completed_count\": %u,\n  \"string_bytes\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"string_failure_owner_only\": %u,\n  \"probe_stage_owner_only\": %ld,\n  \"contract_header_candidate_count\": %u,\n  \"contract_state_candidate_count\": %u,\n  \"contract_lookup_candidate_count\": %u,\n  \"contract_loop_candidate_count\": %u,\n  \"contract_tail_candidate_count\": %u,\n  \"type_codec_kind_owner_only\": %u,\n  \"table_codec_kind_owner_only\": %u,\n  \"data_codec_kind_owner_only\": %u,\n  \"output_written\": %s,\n  \"two_observations_match\": %s,\n  \"fresh_runtime_observation\": true,\n  \"constant_contract_derived_from_current_implementation\": %s,\n  \"managed_constant_getter_invoked\": false,\n  \"managed_string_object_allocated\": false,\n  \"default_value_table_observed_read_only\": true,\n  \"saved_literal_constant_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned)$row_count,completed_count,(unsigned long long)string_bytes,failure_kind,string_failure,InterlockedCompareExchange(&probe_stage,0,0),contract_header_candidates,contract_state_candidates,contract_lookup_candidates,contract_loop_candidates,contract_tail_candidates,constant_decoder.type_codec_kind,constant_decoder.table_codec_kind,constant_decoder.data_codec_kind,written?"true":"false",written?"true":"false",constant_decoder.state_global?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char digest[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(digest)||strcmp(digest,executable_sha)){failure_kind=100;write_status("identity_mismatch",0);return 0;}if(!parse_constant_contract()){failure_kind=101;write_status("constant_contract_failed",0);return 0;}if(!prepare_constant_index()){failure_kind=102;write_status("constant_index_failed",0);return 0;}int ok=dispatch();if(!ok){write_status("capture_failed",0);return 0;}ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
'''
)


def _source(binding: dict[str, Any], output: Path, status: Path) -> str:
    rows = ",".join(
        "{%du,%du,%dull,%dull}"
        % (
            row["field_index"],
            _constant_flags(row),
            row["metadata"],
            row["owner_descriptor"],
        )
        for row in binding["rows"]
    )
    return _COLLECTOR.substitute(
        header_bytes=RUNTIME_ENUM_CONSTANT_HEADER.size,
        record_bytes=RUNTIME_ENUM_CONSTANT_RECORD.size,
        process_id=binding["process_id"],
        executable_sha=binding["binary"]["sha256"],
        native_member_sha=binding["native_member_detail_inventory"]["sha256"],
        field_class=binding["field_class"],
        field_from_handle_pointer=binding["field_from_handle"]["pointer"],
        field_from_handle_metadata=binding["field_from_handle"]["metadata"],
        field_raw_constant_pointer=binding["field_raw_constant"]["pointer"],
        input_rows=rows,
        row_count=len(binding["rows"]),
        output_path=_wide_literal(_windows_z_path(output)),
        status_path=_wide_literal(_windows_z_path(status)),
        status_schema=RUNTIME_ENUM_CONSTANT_STATUS_SCHEMA,
    )


def prepare_runtime_enum_constants(
    *, native_output_receipt: Path, runtime_materializer_model: Path,
    output_dir: Path, compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        native_output_receipt=native_output_receipt,
        runtime_materializer_model=runtime_materializer_model,
    )
    output = output_dir / "runtime-enum-constants.private.bin"
    status = output_dir / "runtime-enum-constants-status.private.json"
    model = output_dir / "runtime-enum-constants.private.json"
    plan_path = output_dir / "runtime-enum-constants-plan.private.json"
    build = _owner_directory(output_dir / "build-runtime-enum-constants")
    source = build / "runtime-enum-constants.c"
    injector_source = build / "runtime-enum-constants-injector.c"
    injector = build / "alpha-runtime-enum-constants-injector.exe"
    for stale in (output, status, model):
        stale.unlink(missing_ok=True)
    _private_text(source, _source(binding, output, status))
    _private_text(injector_source, runtime_injector_source())


    load_identity = secrets.token_hex(8)
    collector = build / (
        "alpha-runtime-enum-constants-"
        + file_identity(source)["sha256"][:12]
        + "-" + load_identity
        + ".dll"
    )
    cc = _compiler(compiler)
    _build(
        [
            str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(source), "-o",
            str(collector), "-lbcrypt",
        ],
        label="runtime enum constant collector",
    )
    _build(
        [
            str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(injector_source), "-o",
            str(injector),
        ],
        label="runtime enum constant injector",
    )
    for artifact in (collector, injector):
        artifact.chmod(0o600)
    contract_rows = [
        {
            "field_index": int(row["field_index"]),
            "owner_type_index": int(row["owner_type_index"]),
            "flags": _constant_flags(row),
        }
        for row in binding["rows"]
    ]
    plan = {
        "schema": RUNTIME_ENUM_CONSTANT_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": binding["binary"]["path"],
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
        },
        "inputs": {
            "native_output_receipt": binding["receipt"],
            "runtime_materializer_model": binding["runtime_materializer_model"],
            "reflection_semantics": binding["reflection_semantics"],
            "native_member_detail_inventory": binding[
                "native_member_detail_inventory"
            ],
        },
        "contract": {
            "enum_count": binding["enum_count"],
            "enum_constant_count": binding["enum_constant_count"],
            "non_enum_constant_count": binding[
                "non_enum_constant_count"
            ],
            "constant_count": len(contract_rows),
            "rows": contract_rows,
        },
        "collector": {**file_identity(collector), "load_identity": load_identity},
        "injector": file_identity(injector),
        "output_path": str(output),
        "status_path": str(status),
        "model_path": str(model),
        "policy": {
            "field_info_get_raw_constant_value_implementation_derived": True,
            "field_info_get_raw_constant_value_invoked": False,
            "field_info_get_value_used_for_strings": False,
            "default_value_table_observed_read_only": True,
            "managed_string_object_allocation_absent": True,
            "per_patch_contract_derived_from_current_implementation": True,
            "current_runtime_handles_used": True,
            "all_runtime_addresses_rebound_from_current_process_inventory": True,
            "all_literal_fields_included": True,
            "strings_captured_as_exact_utf16": True,
            "two_observations_required": True,
            "saved_literal_constant_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
            "owner_only": True,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_ENUM_CONSTANT_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "counts": {
            "enum_count": binding["enum_count"],
            "enum_constant_count": binding["enum_constant_count"],
            "non_enum_constant_count": binding[
                "non_enum_constant_count"
            ],
            "constant_count": len(contract_rows),
        },
        "collector": plan["collector"],
        "policy": plan["policy"],
    }


def _validate(plan: dict[str, Any], status: dict[str, Any]) -> dict[str, Any]:
    path = _owner_file(Path(plan["output_path"]), label="inventory")
    raw = path.read_bytes()
    if len(raw) < RUNTIME_ENUM_CONSTANT_HEADER.size:
        raise AcquisitionError("runtime enum constant inventory is truncated")
    header = RUNTIME_ENUM_CONSTANT_HEADER.unpack_from(raw)
    expected_rows = plan["contract"]["rows"]
    expected = len(expected_rows)
    record_end = (
        RUNTIME_ENUM_CONSTANT_HEADER.size
        + expected * RUNTIME_ENUM_CONSTANT_RECORD.size
    )
    header_ok = (
        header[0] == RUNTIME_ENUM_CONSTANT_MAGIC
        and header[1] == RUNTIME_ENUM_CONSTANT_VERSION
        and header[2] == RUNTIME_ENUM_CONSTANT_HEADER.size
        and header[3] == RUNTIME_ENUM_CONSTANT_RECORD.size
        and header[4] == 0
        and header[5] == expected
        and header[7] == plan["target"]["process_id"]
        and header[8].decode("ascii") == plan["target"]["executable_sha256"]
        and header[9].decode("ascii")
        == plan["inputs"]["native_member_detail_inventory"]["sha256"]
        and len(raw) == record_end + header[6]
    )
    constants: list[dict[str, int | bool | str | None]] = []
    records_ok = header_ok
    observed: set[int] = set()
    observed_string_bytes = 0
    for offset in range(expected if header_ok else 0):
        field_index, flags, raw_value, string_offset, string_units = (
            RUNTIME_ENUM_CONSTANT_RECORD.unpack_from(
                raw,
                RUNTIME_ENUM_CONSTANT_HEADER.size
                + offset * RUNTIME_ENUM_CONSTANT_RECORD.size,
            )
        )
        expected_row = expected_rows[offset]
        width = flags & 0xFF
        signed = bool(flags & CONSTANT_SIGNED)
        is_string = bool(flags & CONSTANT_STRING)
        is_null = bool(flags & CONSTANT_NULL)
        contract_flags = int(expected_row["flags"])
        expected_flags = contract_flags
        if is_null:
            expected_flags |= CONSTANT_NULL
        value_kind = (
            "string" if contract_flags & CONSTANT_STRING
            else "single" if contract_flags & CONSTANT_SINGLE
            else "double" if contract_flags & CONSTANT_DOUBLE
            else "boolean" if contract_flags & CONSTANT_BOOLEAN
            else "char" if contract_flags & CONSTANT_CHAR
            else "integer"
        )
        mask = (1 << (width * 8)) - 1 if width else 0
        string_end = string_offset + string_units * 2
        string_value: str | None = None
        string_ok = True
        if is_string and not is_null:
            string_ok = (
                string_offset == observed_string_bytes
                and string_end >= string_offset
                and string_end <= header[6]
            )
            if string_ok:
                try:
                    string_value = raw[
                        record_end + string_offset:record_end + string_end
                    ].decode("utf-16-le", errors="surrogatepass")
                except UnicodeDecodeError:
                    string_ok = False
            observed_string_bytes = string_end
        elif is_string:
            string_ok = (
                raw_value == 0
                and string_offset == 0
                and string_units == 0
            )
        else:
            string_ok = string_offset == 0 and string_units == 0
        if (
            field_index != expected_row["field_index"]
            or width != (contract_flags & 0xFF)
            or signed is not bool(contract_flags & CONSTANT_SIGNED)
            or is_string != (value_kind == "string")
            or (is_null and not is_string)
            or flags != expected_flags
            or field_index in observed
            or (not is_string and raw_value & ~mask)
            or not string_ok
        ):
            records_ok = False
            break
        observed.add(field_index)
        constants.append(
            {
                "field_index": field_index,
                "owner_type_index": expected_row["owner_type_index"],
                "width": width,
                "signed": signed,
                "value_kind": value_kind,
                "enum_owner": bool(contract_flags & CONSTANT_ENUM_OWNER),
                "typed_enum": bool(contract_flags & CONSTANT_TYPED_ENUM),
                "raw_value": raw_value,
                "string_value": string_value,
            }
        )
    records_ok = records_ok and observed_string_bytes == header[6]
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_ENUM_CONSTANT_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete"
        and status.get("output_written") is True,
        "header_bound": header_ok,
        "record_domain_closed": records_ok and len(constants) == expected,
        "all_literal_constants_captured": (
            type(status.get("completed_count")) is int
            and status.get("completed_count") == expected
        ),
        "string_payload_bound": (
            records_ok
            and type(status.get("string_bytes")) is int
            and status.get("string_bytes") >= 0
            and status.get("string_bytes") == header[6]
        ),
        "two_observations_match": status.get("two_observations_match") is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
        is True,
        "constant_contract_runtime_derived": status.get(
            "constant_contract_derived_from_current_implementation"
        )
        is True,
        "constant_contract_candidate_stages_unique": all(
            status.get(key) == 1
            for key in (
                "contract_header_candidate_count",
                "contract_state_candidate_count",
                "contract_lookup_candidate_count",
                "contract_loop_candidate_count",
                "contract_tail_candidate_count",
            )
        ),
        "constant_contract_codecs_runtime_derived": all(
            status.get(key) in (1, 2)
            for key in (
                "type_codec_kind_owner_only",
                "table_codec_kind_owner_only",
                "data_codec_kind_owner_only",
            )
        ),
        "managed_constant_getter_absent": status.get(
            "managed_constant_getter_invoked"
        )
        is False,
        "managed_string_allocation_absent": status.get(
            "managed_string_object_allocated"
        )
        is False,
        "default_value_table_read_only": status.get(
            "default_value_table_observed_read_only"
        )
        is True,
        "saved_literal_constant_absent": status.get(
            "saved_literal_constant_used"
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
            "runtime enum constant validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    return {
        "schema": RUNTIME_ENUM_CONSTANT_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": plan["inputs"],
        "inventory": file_identity(path),
        "status_receipt": file_identity(Path(plan["status_path"])),
        "counts": {
            "enum_count": plan["contract"]["enum_count"],
            "enum_constant_count": plan["contract"][
                "enum_constant_count"
            ],
            "non_enum_constant_count": plan["contract"][
                "non_enum_constant_count"
            ],
            "constant_count": expected,
            "string_bytes": header[6],
        },
        "constants": constants,
        "checks": checks,
        "policy": plan["policy"],
    }


def capture_runtime_enum_constants(
    *, native_output_receipt: Path, runtime_materializer_model: Path,
    output_dir: Path, wine: Path, wineprefix: Path,
    compiler: Path | None = None, timeout: float = 300.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_enum_constants(
        native_output_receipt=native_output_receipt,
        runtime_materializer_model=runtime_materializer_model,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-enum-constants-plan.private.json"
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
            "runtime enum constant injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-enum-constants-injector.private.log",
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
            "runtime enum constant injection failed"
            + (f": {detail[-1]}" if detail else "")
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
        raise AcquisitionError("runtime enum constant capture timed out")
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime enum constant capture failed "
            f"(kind={status.get('failure_kind_owner_only')}, "
            f"completed={status.get('completed_count')})"
        )
    inventory_path = Path(plan["output_path"])
    _seal_runtime_output(inventory_path)
    model = _validate(plan, status)
    model_path = Path(plan["model_path"])


    _private_json(
        model_path,
        {key: value for key, value in model.items() if key != "constants"},
    )
    return {
        "schema": model["schema"],
        "status": model["status"],
        "target": model["target"],
        "counts": model["counts"],
        "checks": model["checks"],
        "policy": model["policy"],
        "model": file_identity(model_path),
        "inventory": model["inventory"],
    }


def load_runtime_enum_constants(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    plan_path = _owner_file(
        model_path.parent / "runtime-enum-constants-plan.private.json",
        label="plan",
    )
    status_path = _owner_file(
        model_path.parent / "runtime-enum-constants-status.private.json",
        label="status",
    )
    model = read_json(model_path)
    plan = read_json(plan_path)
    status = read_json(status_path)
    if (
        model.get("schema") != RUNTIME_ENUM_CONSTANT_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("inventory") != file_identity(inventory_path)
        or model.get("status_receipt") != file_identity(status_path)
        or plan.get("schema") != RUNTIME_ENUM_CONSTANT_PLAN_SCHEMA
        or Path(plan.get("output_path", "")).expanduser().resolve()
        != inventory_path
        or Path(plan.get("model_path", "")).expanduser().resolve()
        != model_path
        or (
            expected_executable_sha256 is not None
            and model.get("target", {}).get("executable_sha256")
            != expected_executable_sha256.lower()
        )
    ):
        raise AcquisitionError("runtime enum constant binding is stale")
    current = _validate(plan, status)
    model_counts = model.get("counts")
    current_counts = current.get("counts")
    if (
        not isinstance(model_counts, Mapping)
        or not isinstance(current_counts, Mapping)
        or set(model_counts) != set(current_counts)
        or any(
            type(model_counts.get(name)) is not int
            or model_counts.get(name) < 0
            or type(current_counts.get(name)) is not int
            or current_counts.get(name) < 0
            for name in current_counts
        )
        or dict(current_counts) != dict(model_counts)
        or current["checks"] != model.get("checks")
        or current["policy"] != model.get("policy")
    ):
        raise AcquisitionError("runtime enum constant validation is stale")
    return current


import argparse
import importlib.util
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Mapping

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.p37 import SOURCES, write_proto_input
from alpha.p38 import capture_runtime_proto_field_types
from alpha.p45 import capture_runtime_proto_enum_constants
from alpha.p42 import write_runtime_proto_static_model, write_runtime_proto_oneof_mutation_plan, write_runtime_proto_field_mutation_plan
from alpha.p41 import capture_runtime_proto_field_mutations


QUIESCENT_MUTATION_RETRY_KINDS = frozenset({20, 21, 22, 23, 27})
MUTATION_RETRY_DELAY_SECONDS = 3.0


MUTATION_ATTEMPT_TIMEOUT_SECONDS = 600.0


def classify_unserialized_fields(*, static_model: Path, output_path: Path):
    from alpha.h02 import file_identity, read_private_model
    from alpha.p12 import _private_json

    path = static_model.expanduser().resolve()
    model = read_private_model(path)
    if model.get("unresolved_owner_only"):
        raise AcquisitionError(
            "runtime proto fields remain unresolved; serializer evidence is required"
        )
    remaining = []
    unserialized = list(model.get("unserialized_field_owner_only") or [])
    unbound = list(model.get("unbound_parser_candidate_owner_only") or [])
    for row in model.get("unresolved_owner_only") or []:
        kind = row.get("kind")
        if kind == "normal-field-assignment":
            unserialized.append({
                "kind": "unserialized-field",
                "message": row.get("message"),
                "field_indexes_owner_only": list(
                    row.get("field_indexes_owner_only") or []
                ),
                "parser_tag_evidence_owner_only": list(
                    row.get("parser_tag_evidence_owner_only") or []
                ),
                "static_assignment_candidate_numbers": list(
                    row.get("static_assignment_candidate_numbers") or []
                ),
                "candidate_numbers": list(row.get("candidate_numbers") or []),
                "exclusion_reason": "current-runtime-evidence-exhausted",
                "wire_number_unknown": True,
            })
            continue
        if kind == "unaccounted-parser-candidate":
            unbound.append({
                "kind": "unbound-parser-candidate",
                "message": row.get("message"),
                "candidate_numbers": list(row.get("candidate_numbers") or []),
                "bound_to_runtime_field": False,
                "wire_number_known": True,
            })
            continue
        remaining.append(row)
    result = dict(model)


    result["messages_owner_only"] = list(model.get("messages_owner_only") or [])
    result["unresolved_owner_only"] = remaining
    result["unserialized_field_owner_only"] = unserialized
    result["unbound_parser_candidate_owner_only"] = unbound
    checks = dict(model.get("checks") or {})
    checks["no_unresolved_records"] = not remaining
    checks["all_normal_field_gaps_have_parser_case_evidence"] = not any(
        row.get("kind") == "normal-field-assignment" for row in remaining
    )
    checks["all_observed_parser_candidates_accounted"] = not any(
        row.get("kind") == "unaccounted-parser-candidate" for row in remaining
    )
    checks["candidate_tag_domain_closed"] = True
    checks["unserialized_fields_classified_from_runtime_evidence"] = all(
        row.get("wire_number_unknown") is True for row in unserialized
    )
    result["checks"] = checks
    result["status"] = "complete" if not remaining else model.get("status")
    counted = sum(len(row.get("field_indexes_owner_only") or []) for row in unserialized)
    result["classification_evidence_owner_only"] = {
        "schema": "alpha.runtime-proto-final-classification/v1",
        "source_model": file_identity(path),
        "classified_field_count": counted,
        "classified_message_count": len(
            {str(row.get("message")) for row in unserialized}
        ),
        "unbound_parser_candidate_count": sum(
            len(row.get("candidate_numbers") or []) for row in unbound
        ),
        "policy": {
            "wire_number_invented": False,
            "type_domain_preserved": True,
            "runtime_evidence_only": True,
            "external_reference_used": False,
        },
    }
    _private_json(output_path.expanduser().resolve(), result)
    return {
        "schema": "alpha.runtime-proto-final-classification/v1",
        "status": result["status"],
        "counts": {
            "classified_field_count": counted,
            "classified_message_count": result["classification_evidence_owner_only"][
                "classified_message_count"
            ],
            "unbound_parser_candidate_count": result[
                "classification_evidence_owner_only"
            ]["unbound_parser_candidate_count"],
        },
        "checks": checks,
    }


def capture_field_mutations_with_retry(**arguments):
    import re
    import time

    return _retry_probe_capture(capture_runtime_proto_field_mutations, arguments)


def capture_signed_parse_with_retry(**arguments):
    return _retry_probe_capture(capture_runtime_proto_signed_parse, arguments)


def capture_field_transform_with_retry(**arguments):
    return _retry_probe_capture(capture_runtime_proto_field_transform_probe, arguments)


def _retry_probe_capture(capture, arguments):
    import re
    import time

    arguments = dict(arguments)
    requested = arguments.get("timeout")
    overall_timeout = (
        float(requested)
        if isinstance(requested, (int, float)) and requested > 0
        else MUTATION_ATTEMPT_TIMEOUT_SECONDS
    )
    deadline = time.monotonic() + overall_timeout
    last_error = None
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        arguments["timeout"] = min(remaining, MUTATION_ATTEMPT_TIMEOUT_SECONDS)
        try:
            return capture(**arguments)
        except AcquisitionError as error:
            message = str(error)
            kind = re.search(r"kind=(\d+)", message)
            retryable = (
                "timed out" in message
                or "capture failed" in message
                or (
                    kind is not None
                    and int(kind.group(1)) in QUIESCENT_MUTATION_RETRY_KINDS
                )
            )
            retryable = retryable and getattr(error, "retryable", True)
            if not retryable:
                raise
            last_error = error
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            time.sleep(min(MUTATION_RETRY_DELAY_SECONDS, remaining))
    if last_error is None:
        raise AcquisitionError("runtime proto probe retry deadline expired")
    raise last_error
from alpha.p42 import capture_runtime_proto_serializer_probe
from alpha.p43 import (
    capture_runtime_proto_field_transform_probe,
    capture_runtime_proto_signed_parse,
    write_verified_parse_model,
)
from alpha.p02 import _atomic_write_text, _json_text
from alpha.p02 import build_class_list, build_packet_ids
from alpha.p02 import write_runtime_proto_outputs_from_model
from alpha.h02 import publish_new_directory
from alpha.h02 import file_identity, read_json, read_private_model
import re


def preflight(output_dir):
    if importlib.util.find_spec("capstone") is None:
        raise AcquisitionError("capstone is required for instruction-boundary validation")
    if importlib.util.find_spec("grpc_tools") is None:
        raise AcquisitionError("grpcio-tools is required for proto compilation validation")
    if output_dir.exists() or output_dir.is_symlink():
        raise AcquisitionError("proto destination already exists")


def _render_unreferenced_enum_outputs(model):
    import re
    from collections import Counter
    from alpha.p02 import dump_artifact_context, proto_artifact_names

    context = dump_artifact_context(model.get("target", {}))
    names = proto_artifact_names(model["target"])

    source = model.get("unreferenced_enums_owner_only")
    if not isinstance(source, list):
        raise AcquisitionError("runtime proto model lacks unreferenced enum inventory")
    identifier = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
    rows = []
    for source_row in source:
        if not isinstance(source_row, dict):
            raise AcquisitionError("unreferenced enum inventory row is invalid")
        row = dict(source_row)
        values = source_row.get("values")
        if not isinstance(values, list):
            raise AcquisitionError("unreferenced enum values are invalid")
        if any(
            not isinstance(value, dict)
            or value.get("captured") is not True
            or type(value.get("value")) is not int
            for value in values
        ):
            raise AcquisitionError(
                "unreferenced enum inventory contains an uncaptured value"
            )
        row["values"] = [dict(value) for value in values]
        reasons = list(row.get("fragment_exclusion_reasons") or [])
        if row.get("proto3_fragment_eligible") is True:
            if not identifier.fullmatch(str(row.get("name", ""))):
                reasons.append("invalid-proto-enum-identifier")
            invalid_values = [
                value.get("name")
                for value in row["values"]
                if not identifier.fullmatch(str(value.get("name", "")))
            ]
            if invalid_values:
                reasons.append("invalid-proto-value-identifier")
        row["proto3_fragment_eligible"] = (
            row.get("proto3_fragment_eligible") is True and not reasons
        )
        row["fragment_exclusion_reasons"] = reasons
        rows.append(row)

    candidates = [row for row in rows if row["proto3_fragment_eligible"]]
    type_names = Counter(str(row["name"]) for row in candidates)
    emitted_type_names: set[str] = set()
    for row in candidates:
        simple = str(row["name"])
        emitted = simple
        if type_names[simple] > 1 or emitted in emitted_type_names:
            emitted = f"{simple}_TYPE_{int(row['type_index_owner_only'])}"
        suffix = 1
        base = emitted
        while emitted in emitted_type_names:
            emitted = f"{base}_{suffix}"
            suffix += 1
        emitted_type_names.add(emitted)
        row["fragment_emitted_name"] = emitted

    value_name_counts = Counter(
        str(value["name"])
        for row in candidates
        for value in row["values"]
    )
    reserved = set(emitted_type_names) | set(value_name_counts)
    for row in candidates:
        enum_name = str(row["fragment_emitted_name"])
        for value in row["values"]:
            original = str(value["name"])
            emitted = original
            if value_name_counts[original] > 1 or original in emitted_type_names:
                emitted = f"{enum_name}_{original}"
                suffix = 1
                base = emitted
                while emitted in reserved:
                    emitted = f"{base}_{suffix}"
                    suffix += 1
                reserved.add(emitted)
            value["fragment_emitted_name"] = emitted

    lines = [
        context["banner"],
        context["discord_line"],
        "// Runtime-derived wire schema; original source syntax/options are not reconstructed.",
        'syntax = "proto3";',
        "",
    ]
    for row in candidates:
        lines.append(f"enum {row['fragment_emitted_name']} {{")
        numbers = [int(value["value"]) for value in row["values"]]
        if len(numbers) != len(set(numbers)):
            lines.append("    option allow_alias = true;")
        for value in row["values"]:
            lines.append(
                f"    {value['fragment_emitted_name']} = {int(value['value'])};"
            )
        lines.append("}")
        lines.append("")

    classifications = Counter(str(row.get("classification")) for row in rows)
    manifest = {
        "schema": "alpha.unreferenced-enums/v3",
        "dump_metadata": {
            key: context[key]
            for key in (
                "producer",
                "client_version",
                "client_build",
                "version_label",
                "banner",
                "discord",
                "executable_sha256",
            )
        },
        "count": len(rows),
        "classification_counts": dict(sorted(classifications.items())),
        "inventory": {
            "lossless_non_emitted_enum_domain": True,
            "all_enum_values_captured": True,
            "runtime_member_order_preserved": True,
        },
        "fragment": {
            "file": names["enum_proto"],
            "candidate_count": len(candidates),
            "proves_proto_provenance": False,
            "eligibility_is_necessary_not_sufficient": True,
            "criteria": [
                "not a generated oneof discriminator",
                "top-level runtime type",
                "empty runtime namespace",
                "all enum values captured",
                "first runtime member has value zero",
                "all values fit the protobuf enum int32 range",
                "all emitted identifiers are valid",
            ],
        },
        "enums": rows,
    }
    return manifest, "\n".join(lines), candidates


def _validate_unreferenced_enum_outputs(root, manifest, candidates, model):
    from google.protobuf.descriptor_pb2 import FileDescriptorSet
    from alpha.p02 import proto_artifact_names

    names = proto_artifact_names(model["target"])

    saved = read_json(root / names["enum_inventory"])
    if saved != manifest:
        raise AcquisitionError("unreferenced enum inventory differs after write")
    output = root / (names["enum_proto"] + ".pb")
    try:
        result = subprocess.run(
            [
                sys.executable,
                "-m",
                "grpc_tools.protoc",
                f"--proto_path={root}",
                f"--descriptor_set_out={output}",
                names["enum_proto"],
            ],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=120,
            check=False,
        )
        if result.returncode:
            raise AcquisitionError(
                "unreferenced enum fragment compilation failed: " + result.stderr
            )
        descriptors = FileDescriptorSet.FromString(output.read_bytes())
    finally:
        output.unlink(missing_ok=True)
    if len(descriptors.file) != 1:
        raise AcquisitionError("unexpected unreferenced enum descriptor domain")
    file = descriptors.file[0]
    observed = {
        enum.name: [(value.name, value.number) for value in enum.value]
        for enum in file.enum_type
    }
    expected = {
        str(row["fragment_emitted_name"]): [
            (str(value["fragment_emitted_name"]), int(value["value"]))
            for value in row["values"]
        ]
        for row in candidates
    }
    if file.syntax != "proto3" or file.package or observed != expected:
        raise AcquisitionError(
            "compiled unreferenced enum fragment differs from its inventory"
        )
    return {
        "unreferenced_enum_inventory_written": True,
        "unreferenced_enum_fragment_compiles": True,
        "unreferenced_enum_fragment_descriptor_agreement": True,
    }


def verify_published_proto_output(
    *, static_model: Path, output_dir: Path, nameeproto_options=None,
    field_encryption_observation_model: Path | None = None,
) -> dict[str, object]:
    from alpha.p02 import (
        RUNTIME_PROTO_OUTPUT_SCHEMA,
        dump_artifact_context,
        proto_artifact_names,
        validate_runtime_proto_static_model_for_publication,
    )

    model_path = static_model.expanduser().resolve()
    root = output_dir.expanduser().absolute()
    if root.is_symlink() or not root.is_dir():
        raise AcquisitionError("published proto output directory is unavailable")
    root = root.resolve()
    model = read_private_model(model_path)
    context = dump_artifact_context(model["target"])
    names = proto_artifact_names(model["target"])
    receipt_path = root / names["receipt"]
    if not receipt_path.is_file() or receipt_path.is_symlink():
        raise AcquisitionError("published proto receipt is missing or unsafe")
    receipt = read_json(receipt_path, maximum_bytes=512 * 1024 * 1024)
    field_encryption_record = (
        receipt.get("field_encryption_output") if isinstance(receipt, dict) else None
    )
    if field_encryption_record is not None and not isinstance(
        field_encryption_record, Mapping
    ):
        raise AcquisitionError("published field-encryption receipt is invalid")
    if (field_encryption_record is None) != (
        field_encryption_observation_model is None
    ):
        raise AcquisitionError(
            "published field-encryption output and runtime model must be verified together"
        )
    omission = receipt.get("field_encryption_omission")
    if omission is None and receipt.get("partial_wire_contract") is not None:
        raise AcquisitionError("partial wire contract lacks its omission receipt")
    if omission is not None:
        from alpha.p43 import _field_transform_role_inventory
        parserless_fields = sorted(
            int(message["type_index_owner_only"])
            for message in model["messages_owner_only"]
            if message.get("merge_from_rva") is None
            and (message.get("fields") or message.get("oneofs"))
        )
        partial_contract = receipt.get("partial_wire_contract")
        if (
            field_encryption_record is not None
            or not isinstance(omission, Mapping)
            or omission.get("schema") != "alpha.field-encryption-omission/v1"
            or omission.get("status") != "deferred"
            or omission.get("reason") != "numeric runtime transforms remain unproven"
            or omission.get("numeric_role_count")
            != len(_field_transform_role_inventory(model))
            or not isinstance(partial_contract, Mapping)
            or partial_contract.get("schema") != "alpha.partial-proto-wire-contract/v1"
            or partial_contract.get("status") != "partial"
            or partial_contract.get("parserless_field_message_type_indexes_owner_only")
            != parserless_fields
            or receipt.get("completion_scope")
            != "partial-modeled-domain-artifact-generation"
        ):
            raise AcquisitionError("published field-encryption omission receipt differs")
    model_counts = validate_runtime_proto_static_model_for_publication(
        model, allow_partial_wire_contract=omission is not None,
    )

    primary = (
        names["proto"],
        names["sorted_proto"],
        names["class_list"],
        names["packet_ids"],
    )
    sidecar = (names["enum_inventory"], names["enum_proto"])
    expected_file_names = {
        *primary, *sidecar, names["semantic_names"], names["receipt"]
    }
    if field_encryption_record is not None:
        expected_file_names.add(names["field_encrypt"])
    expected_entry_names = {
        *expected_file_names, names["nameproto"], names["nameeproto"]
    }


    metadata_entry = root / "metadata"
    paired_metadata_receipt: Path | None = None
    if metadata_entry.is_dir() and not metadata_entry.is_symlink():
        candidate = metadata_entry / "alpha-metadata-output-receipt.json"
        if candidate.is_file() and not candidate.is_symlink():
            paired_metadata_receipt = candidate
            expected_entry_names.add("metadata")
    entries = list(root.iterdir())
    if (
        {path.name for path in entries} != expected_entry_names
        or any(path.is_symlink() for path in entries)
        or any(
            (
                not path.is_dir()
                if path.name in {names["nameproto"], names["nameeproto"]}
                else not path.is_file()
            )
            for path in entries
        )
    ):
        raise AcquisitionError("published proto output file domain differs")
    for name in expected_file_names:
        path = root / name
        if not path.is_file() or path.is_symlink():
            raise AcquisitionError(
                f"published proto output is missing or unsafe: {name}"
            )

    manifest, fragment, candidates = _render_unreferenced_enum_outputs(model)
    if (
        read_json(
            root / names["enum_inventory"], maximum_bytes=512 * 1024 * 1024
        )
        != manifest
    ):
        raise AcquisitionError(
            "published unreferenced enum inventory differs from model"
        )
    try:
        saved_fragment = (root / names["enum_proto"]).read_text(
            encoding="utf-8"
        )
    except (OSError, UnicodeDecodeError) as error:
        raise AcquisitionError(
            "published unreferenced enum fragment is unreadable"
        ) from error
    if saved_fragment != fragment:
        raise AcquisitionError(
            "published unreferenced enum fragment differs from model"
        )

    compiled_checks = validate_compiled_output(root, model)
    sidecar_checks = _validate_unreferenced_enum_outputs(
        root, manifest, candidates, model
    )
    from alpha.p47 import verify_nameproto_outputs
    if nameeproto_options is None:
        from alpha.p49 import options_from_environment

        nameeproto_options = options_from_environment()
    nameproto = verify_nameproto_outputs(
        model=model, output_dir=root, static_model=model_path,
        nameeproto_previous=nameeproto_options.get("previous"),
        nameeproto_rejected_ledger=nameeproto_options.get("rejected_ledger"),
        nameeproto_options=nameeproto_options.get("options"),
        semantic_references=nameeproto_options.get("references"),
    )
    checks = receipt.get("checks") if isinstance(receipt, dict) else None
    semantic = (
        receipt.get("semantic_verification") if isinstance(receipt, dict) else None
    )
    required_checks = {
        "static_model_complete",
        "static_model_checks_closed",
        "unresolved_records_absent",
        "all_runtime_enum_constants_available",
        "all_runtime_enum_attribute_evidence_available",
        "runtime_enum_domain_closed",
        "rendered_counts_match_static_model",
        "four_primary_outputs_written",
        "complete_source_model_preserved_in_primary_outputs",
        "direct_json_evidence_preserved_in_primary_outputs",
        *compiled_checks,
        *sidecar_checks,
        *nameproto["checks"],
    }
    if field_encryption_record is not None:
        required_checks.update({
            "field_encryption_runtime_domain_classified",
            "field_encryption_artifact_written",
            "field_encryption_deferred_roles_recorded",
        })
    if (
        not isinstance(receipt, dict)
        or receipt.get("schema") != RUNTIME_PROTO_OUTPUT_SCHEMA
        or receipt.get("status") != "complete"
        or receipt.get("output_dir") != str(root)
        or receipt.get("target") != model.get("target")
        or receipt.get("dump_metadata")
        != {
            key: context[key]
            for key in (
                "producer",
                "client_version",
                "client_build",
                "version_label",
                "banner",
                "discord",
                "executable_sha256",
            )
        }
        or receipt.get("artifact_names") != names
        or receipt.get("input") != file_identity(model_path)
        or receipt.get("full_semantic_verification_complete") is not True
        or not isinstance(semantic, Mapping)
        or semantic.get("signed_encoding_complete") is not True
        or semantic.get("message_domain_complete") is not True
        or not isinstance(checks, Mapping)
        or any(value is not True for value in checks.values())
        or not required_checks <= set(checks)
    ):
        raise AcquisitionError("published proto receipt is incomplete or stale")

    expected_counts = {
        name: model_counts[name]
        for name in ("message_count", "enum_count", "proto_field_count")
    }
    receipt_counts = receipt.get("counts")
    if (
        not isinstance(receipt_counts, Mapping)
        or any(
            type(receipt_counts.get(name)) is not int
            or receipt_counts.get(name) < 0
            or receipt_counts.get(name) != value
            for name, value in expected_counts.items()
        )
    ):
        raise AcquisitionError("published proto receipt counts differ from model")
    for collection, file_names in (("files", primary), ("sidecar_files", sidecar)):
        recorded = receipt.get(collection)
        if not isinstance(recorded, Mapping):
            raise AcquisitionError("published proto receipt file inventory is absent")
        actual = {name: file_identity(root / name) for name in file_names}
        expected = {name: recorded.get(name) for name in file_names}
        if actual != expected:
            raise AcquisitionError("published proto file identity differs from receipt")
    if field_encryption_record is not None:
        observation_path = field_encryption_observation_model.expanduser().resolve()
        field_encryption_checks = field_encryption_record.get("checks")
        field_encryption_evidence = field_encryption_record.get(
            "implementation_evidence_coverage"
        )
        field_encryption_counts = field_encryption_record.get("counts")
        if (
            receipt.get("field_encryption_input") != file_identity(observation_path)
            or field_encryption_record.get("schema")
            != "alpha.runtime-field-encrypt-artifact/v2"
            or field_encryption_record.get("status") not in {"complete", "partial"}
            or field_encryption_record.get("proof_scope")
            != "bounded-parser-body-crosschecked-by-fresh-runtime-probes"
            or field_encryption_record.get(
                "full_runtime_transform_implementation_proven"
            ) is not False
            or not isinstance(field_encryption_checks, Mapping)
            or not field_encryption_checks
            or any(value is not True for value in field_encryption_checks.values())
            or (
                field_encryption_record.get("status") == "complete"
                and field_encryption_checks.get(
                    "parser_body_evidence_proven_for_all_numeric_roles"
                ) is not True
            )
            or not isinstance(field_encryption_counts, Mapping)
            or set(field_encryption_counts) != {
                "numeric_field_count",
                "numeric_role_count",
                "encrypted_field_count",
                "encrypted_role_count",
                "identity_role_count",
            }
            or any(
                type(value) is not int or value < 0
                for value in field_encryption_counts.values()
            )
            or not isinstance(field_encryption_evidence, Mapping)
            or type(field_encryption_evidence.get("numeric_role_count")) is not int
            or field_encryption_evidence.get("numeric_role_count") < 0
            or field_encryption_evidence.get("numeric_role_count")
            != field_encryption_counts.get("numeric_role_count")
            or type(field_encryption_evidence.get(
                "bounded_parser_body_proven_role_count"
            )) is not int
            or field_encryption_evidence.get(
                "bounded_parser_body_proven_role_count"
            ) + int(field_encryption_evidence.get("deferred_role_count") or 0)
            != field_encryption_counts.get("numeric_role_count")
            or type(field_encryption_evidence.get("deferred_role_count")) is not int
            or (
                field_encryption_record.get("status") == "complete"
                and field_encryption_evidence.get("deferred_role_count") != 0
            )
            or (
                field_encryption_record.get("status") == "partial"
                and (
                    field_encryption_evidence.get("deferred_role_count", 0) < 1
                    or not isinstance(
                        field_encryption_evidence.get("deferred_roles_owner_only"),
                        list,
                    )
                    or len(field_encryption_evidence.get("deferred_roles_owner_only"))
                    != field_encryption_evidence.get("deferred_role_count")
                )
            )
            or type(field_encryption_evidence.get("unresolved_role_count")) is not int
            or field_encryption_evidence.get("unresolved_role_count")
            != field_encryption_evidence.get("deferred_role_count")
            or field_encryption_evidence.get("end_to_end_function_proven") is not False
        ):
            raise AcquisitionError("published field-encryption receipt is stale or incomplete")
        from alpha.p50 import (
            build_field_encryption_observation_model,
            require_publishable_field_encryption_model,
            render_field_encrypt_document,
            validate_observation_inventory,
            validate_combined_field_transform_probe,
        )

        observation_model = read_private_model(observation_path)
        probe_identity = observation_model.get("inputs", {}).get("runtime_probe_model")
        if not isinstance(probe_identity, Mapping) or not isinstance(
            probe_identity.get("path"), str
        ):
            raise AcquisitionError("field-encryption runtime probe input identity is absent")
        probe_path = Path(probe_identity["path"]).expanduser().resolve()
        if file_identity(probe_path) != dict(probe_identity):
            raise AcquisitionError("field-encryption runtime probe input has changed")
        probe_receipt_path = observation_path.parent / "field-transform-probe-receipt.private.json"
        probe_receipt_identity = file_identity(probe_receipt_path)
        probe_receipt = read_private_model(probe_receipt_path)
        if (
            probe_receipt.get("model") != dict(probe_identity)
            or file_identity(probe_receipt_path) != probe_receipt_identity
        ):
            raise AcquisitionError("field-encryption combined-probe receipt differs")
        runtime_probe = read_private_model(probe_path)
        validate_combined_field_transform_probe(runtime_probe)
        reconstructed_observation = build_field_encryption_observation_model(
            proto_model=model,
            runtime_probe=runtime_probe,
            runtime_probe_model_identity=probe_identity,
        )
        if reconstructed_observation != observation_model:
            raise AcquisitionError(
                "field-encryption observation model differs from captured runtime evidence"
            )
        if (
            file_identity(probe_path) != dict(probe_identity)
            or file_identity(observation_path)
            != receipt.get("field_encryption_input")
        ):
            raise AcquisitionError("field-encryption evidence changed during revalidation")
        observations = validate_observation_inventory(
            observation_model,
            executable_sha256=model["target"]["executable_sha256"],
            expected_target=model["target"],
        )
        require_publishable_field_encryption_model(
            observation_model, observations
        )
        encrypted_rows = [
            row for row in observations.values()
            if row.get("disposition") == "encrypted"
        ]
        expected_field_encryption_counts = {
            "numeric_field_count": len({
                (row["message_type_index_owner_only"], row["field_number"], row["container"])
                for row in observations.values()
            }),
            "numeric_role_count": len(observations),
            "encrypted_field_count": len({
                (row["message_type_index_owner_only"], row["field_number"], row["container"])
                for row in encrypted_rows
            }),
            "encrypted_role_count": len(encrypted_rows),
            "identity_role_count": sum(
                row.get("disposition") == "identity"
                for row in observations.values()
            ),
        }
        if dict(field_encryption_counts) != expected_field_encryption_counts:
            raise AcquisitionError(
                "published field-encryption counts differ from runtime evidence"
            )
        enum_names = {
            str(item["name"]) for item in model["enums_owner_only"]
        }
        expected_field_encryption = render_field_encrypt_document(
            proto_messages=model["messages_owner_only"],
            observations=observations,
            enum_type_names=enum_names,
        )
        field_encryption_path = root / names["field_encrypt"]
        if (
            read_json(
                field_encryption_path,
                maximum_bytes=512 * 1024 * 1024,
            )
            != expected_field_encryption
            or field_encryption_record.get("artifact")
            != file_identity(field_encryption_path)
        ):
            raise AcquisitionError(
                "published field-encryption artifact differs from runtime evidence"
            )
    recorded_nameproto = receipt.get("nameproto_output")
    if (
        not isinstance(recorded_nameproto, Mapping)
        or recorded_nameproto.get("schema")
        != "alpha.runtime-nameproto-output/v2"
        or recorded_nameproto.get("status") != "complete"
        or recorded_nameproto.get("manifest") != nameproto["manifest"]
        or recorded_nameproto.get("files") != nameproto["files"]
        or not all(recorded_nameproto.get("checks", {}).values())
    ):
        raise AcquisitionError("published nameproto receipt is incomplete or stale")

    return {
        "schema": "alpha.runtime-proto-published-output-verification/v1",
        "status": "complete",
        "counts": expected_counts,
        "checks": {
            "static_model_revalidated": True,
            "primary_output_recompiled": True,
            "sidecar_reconstructed_from_model": True,
            "receipt_file_identities_match": True,
            "nameproto_reconstructed_and_recompiled": True,
            **(
                {"paired_metadata_artifact_set_present": True}
                if paired_metadata_receipt is not None
                else {}
            ),
            **({"field_encryption_reconstructed_from_runtime_evidence": True}
               if field_encryption_record is not None else {}),
        },
    }


def validate_descriptor_model(file, model):

    from google.protobuf.descriptor_pb2 import FieldDescriptorProto as Field
    def type_name(field):
        if field.type in (Field.TYPE_MESSAGE, Field.TYPE_ENUM):
            return field.type_name.removeprefix(".")
        return Field.Type.Name(field.type).removeprefix("TYPE_").lower()
    expected = {}
    message_names = {message['name'] for message in model['messages_owner_only']}
    from alpha.p02 import _message_relationships, normalize_proto_items
    relationships, _children, emitted_paths = _message_relationships(
        normalize_proto_items(
            [{"kind": "message", "name": message["name"],
              "declaring_path": message.get("declaring_path"),
              "fields": [], "oneofs": []}
             for message in model["messages_owner_only"]]
            + [dict(enum, kind="enum") for enum in model["enums_owner_only"]]
        )
    )
    flat_by_path = {path: name for name, path in emitted_paths.items()}

    def resolved_type(field):
        name = type_name(field)
        return flat_by_path.get(name, name)
    for message in model["messages_owner_only"]:
        fields = []
        for field in message.get("fields", []):
            cardinality = field.get("cardinality", "singular")
            fields.append((field["name"], field["number"], cardinality,
                           field.get("type") if cardinality != "map" else None,
                           field.get("key_type"), field.get("value_type"), None,
                           field.get('packed', True) if cardinality=='repeated' and field.get('type') not in message_names | {'string','bytes'} else None,
                           field.get("optional") is True))
        for oneof in message.get("oneofs", []):
            fields.extend((field["name"], field["number"], "singular", field["type"],
                           None, None, oneof["name"], None, False) for field in oneof["cases"])
        expected[message["name"]] = (
            sorted(fields),
            sorted(row["name"] for row in message.get("oneofs", [])),
            relationships.get(message["name"]),
        )
    observed = {}
    observed_enums = {}

    def walk(messages, owner, prefix):
        for message in messages:
            if message.options.map_entry:
                continue
            qualified = message.name if not prefix else f"{prefix}.{message.name}"
            maps = {f".{qualified}.{nested.name}": nested for nested in message.nested_type
                    if nested.options.map_entry}
            for enum in message.enum_type:
                observed_enums[enum.name] = (
                    [(value.name, value.number) for value in enum.value],
                    message.name,
                )
            fields = []
            synthetic_oneofs = {
                message.oneof_decl[field.oneof_index].name
                for field in message.field
                if field.proto3_optional and field.HasField("oneof_index")
            }
            for field in message.field:
                group = None if field.proto3_optional else (
                    message.oneof_decl[field.oneof_index].name if field.HasField("oneof_index") else None
                )
                if field.type_name in maps:
                    entry = maps[field.type_name]
                    if (field.label != Field.LABEL_REPEATED or group is not None
                            or [(value.name, value.number) for value in entry.field] != [("key", 1), ("value", 2)]):
                        raise AcquisitionError("compiled map shape differs")
                    fields.append((field.name, field.number, "map", None,
                                   resolved_type(entry.field[0]), resolved_type(entry.field[1]), None, None, False))
                else:
                    if field.label == Field.LABEL_REQUIRED:
                        raise AcquisitionError("unexpected proto presence mode")
                    fields.append((field.name, field.number,
                                   "repeated" if field.label == Field.LABEL_REPEATED else "singular",
                                   resolved_type(field), None, None, group,
                                   (field.options.packed if field.options.HasField('packed') else True)
                                   if field.label==Field.LABEL_REPEATED and field.type not in (Field.TYPE_MESSAGE,Field.TYPE_STRING,Field.TYPE_BYTES) else None,
                                   bool(field.proto3_optional)))
            observed[message.name] = (
                sorted(fields),
                sorted(row.name for row in message.oneof_decl if row.name not in synthetic_oneofs),
                owner,
            )
            walk(message.nested_type, message.name, qualified)

    walk(file.message_type, None, "")
    observed_enums.update({
        enum.name: ([(value.name, value.number) for value in enum.value], None)
        for enum in file.enum_type
    })
    from alpha.p02 import normalize_proto_items
    symbol_items = normalize_proto_items(
        [{"kind":"message", "name":message["name"], "fields":[]}
         for message in model["messages_owner_only"]]
        + [dict(enum,kind="enum") for enum in model["enums_owner_only"]])
    expected_enums = {
        enum["name"]: (
            [(value["name"], value["number"]) for value in enum["values"]],
            relationships.get(enum["name"]),
        )
        for enum in symbol_items
        if enum["kind"] == "enum"
    }
    if file.syntax != "proto3" or file.package or observed != expected or observed_enums != expected_enums:
        raise AcquisitionError("compiled proto semantics differ from captured model")


def validate_compiled_output(root, model):
    from google.protobuf.descriptor_pb2 import FileDescriptorSet
    from alpha.p02 import proto_artifact_names, read_proto_packet_ids

    names = proto_artifact_names(model["target"])
    canonical = []
    with tempfile.TemporaryDirectory(prefix="proto-compile-") as temporary:
        for name in (names["proto"], names["sorted_proto"]):
            output = Path(temporary) / (name + ".pb")
            result = subprocess.run([sys.executable, "-m", "grpc_tools.protoc",
                f"--proto_path={root}", f"--descriptor_set_out={output}", name],
                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=120, check=False)
            if result.returncode:
                raise AcquisitionError(f"proto compilation failed for {name}: {result.stderr}")
            descriptors = FileDescriptorSet.FromString(output.read_bytes())
            if len(descriptors.file) != 1:
                raise AcquisitionError("unexpected compiled proto file domain")
            file = descriptors.file[0]
            validate_descriptor_model(file, model)
            file.name = "schema.proto"
            def normalize(message):
                fields = sorted(message.field, key=lambda field: field.number)
                del message.field[:]
                message.field.extend(fields)
                order = sorted(
                    range(len(message.oneof_decl)),
                    key=lambda index: message.oneof_decl[index].name,
                )
                if order != list(range(len(message.oneof_decl))):
                    remap = {old: new for new, old in enumerate(order)}
                    for field in message.field:
                        if field.HasField("oneof_index"):
                            field.oneof_index = remap[int(field.oneof_index)]
                    declaration = [message.oneof_decl[index] for index in order]
                    del message.oneof_decl[:]
                    message.oneof_decl.extend(declaration)
                for nested in message.nested_type:
                    normalize(nested)
                nested_types = sorted(message.nested_type, key=lambda nested: nested.name)
                del message.nested_type[:]
                message.nested_type.extend(nested_types)
            for message in file.message_type:
                normalize(message)
            def message_count(messages):
                return sum(
                    0 if message.options.map_entry else 1 + message_count(message.nested_type)
                    for message in messages
                )

            def field_count(messages):
                return sum(
                    0 if message.options.map_entry else len(message.field) + field_count(message.nested_type)
                    for message in messages
                )

            def nested_enum_count(messages):
                return sum(
                    0
                    if message.options.map_entry
                    else len(message.enum_type) + nested_enum_count(message.nested_type)
                    for message in messages
                )

            if message_count(file.message_type) != model["counts"]["message_count"]:
                raise AcquisitionError("compiled message count differs")
            if (
                len(file.enum_type) + nested_enum_count(file.message_type)
                != model["counts"]["enum_count"]
            ):
                raise AcquisitionError("compiled enum count differs")
            if field_count(file.message_type) != model["counts"]["proto_field_count"]:
                raise AcquisitionError("compiled field count differs")
            canonical.append(descriptors.SerializeToString(deterministic=True))
    if canonical[0] != canonical[1]:
        raise AcquisitionError("sorted proto changes schema semantics")
    items = [*model["messages_owner_only"], *model["enums_owner_only"]]
    from alpha.p02 import read_proto_class_list
    classes = read_proto_class_list(
        root / names["class_list"], target=model["target"]
    )
    if classes and "_alpha_capture" in classes[0]:
        from alpha.p02 import validate_evidence
        validate_evidence(classes, model)
        classes[0].pop("_alpha_capture")
    if classes != build_class_list(items):
        raise AcquisitionError("classList differs from captured model")
    if read_proto_packet_ids(
        root / names["packet_ids"], target=model["target"]
    ) != build_packet_ids(items)[0]:
        raise AcquisitionError("packetIds differs from captured model")
    return {"both_protos_compile": True, "compiled_model_agreement": True, "sorted_descriptor_equivalence": True,
            "json_model_agreement": True}


def publish_proto(
    *, static_model, output_dir, assert_current, nameeproto_options=None,
    field_encryption_observation_model=None,
    partial_proto_without_field_encrypt=False,
):
    import shutil
    import uuid

    output_dir = output_dir.expanduser().absolute()
    if output_dir.exists() or output_dir.is_symlink():
        raise AcquisitionError("proto destination already exists")
    output_dir = output_dir.resolve()
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    stage = Path(tempfile.mkdtemp(prefix=".proto-staging-", dir=output_dir.parent))
    try:
        partial_field_encryption = False
        if field_encryption_observation_model is not None:
            partial_field_encryption = bool(
                read_private_model(field_encryption_observation_model).get(
                    "partial_publication"
                )
            )
        receipt = write_runtime_proto_outputs_from_model(
            static_model=static_model, output_dir=stage,
            field_encryption_observation_model=field_encryption_observation_model,
            allow_partial_wire_contract=partial_proto_without_field_encrypt,
            allow_partial_field_encryption=partial_field_encryption,
        )
        model = read_private_model(static_model)
        if partial_proto_without_field_encrypt:
            if field_encryption_observation_model is not None:
                raise AcquisitionError("partial proto output cannot include field encryption")
            from alpha.p43 import _field_transform_role_inventory
            receipt["field_encryption_omission"] = {
                "schema": "alpha.field-encryption-omission/v1",
                "status": "deferred",
                "reason": "numeric runtime transforms remain unproven",
                "numeric_role_count": len(_field_transform_role_inventory(model)),
            }
            receipt["partial_wire_contract"] = {
                "schema": "alpha.partial-proto-wire-contract/v1",
                "status": "partial",
                "reason": "field-bearing messages without bounded parser evidence",
                "parserless_field_message_type_indexes_owner_only": sorted(
                    int(message["type_index_owner_only"])
                    for message in model["messages_owner_only"]
                    if message.get("merge_from_rva") is None
                    and (message.get("fields") or message.get("oneofs"))
                ),
            }
            receipt["completion_scope"] = "partial-modeled-domain-artifact-generation"
        from alpha.p02 import proto_artifact_names
        names = proto_artifact_names(model["target"])
        manifest, fragment, candidates = _render_unreferenced_enum_outputs(model)
        _atomic_write_text(
            stage / names["enum_inventory"],
            _json_text(manifest),
        )
        _atomic_write_text(stage / names["enum_proto"], fragment)
        from alpha.p47 import write_nameproto_outputs
        if nameeproto_options is None:
            from alpha.p49 import options_from_environment

            nameeproto_options = options_from_environment()
        nameproto = write_nameproto_outputs(
            model=model, output_dir=stage, static_model=Path(static_model),
            nameeproto_previous=nameeproto_options.get("previous"),
            nameeproto_rejected_ledger=nameeproto_options.get("rejected_ledger"),
            nameeproto_options=nameeproto_options.get("options"),
            semantic_references=nameeproto_options.get("references"),
            allow_partial_wire_contract=partial_proto_without_field_encrypt,
        )
        receipt["nameproto_output"] = nameproto
        receipt["checks"].update(nameproto["checks"])
        receipt["checks"].update({
            "nameproto_exactly_reconstructed": True,
            "nameproto_corpus_compiles": True,
            "nameproto_descriptor_agreement": True,
            "nameproto_type_domain_complete": True,
        })
        receipt["checks"].update(validate_compiled_output(stage, model))
        receipt["checks"].update(
            _validate_unreferenced_enum_outputs(stage, manifest, candidates, model)
        )
        receipt["sidecar_files"] = {
            name: file_identity(stage / name)
            for name in (names["enum_inventory"], names["enum_proto"])
        }
        assert_current()
        receipt.pop("receipt", None)
        receipt["access_control"] = {
            "owner_only_mode_bits_observed": not any(
                owner_only_path_bits(path)
                for path in [stage, *stage.iterdir()]
            ),
            "scope": "user-requested-portable-export",
            "filesystem_enforcement_verified": False,
            "private_acquisition_permissions_unchanged": True,
        }
        _atomic_write_text(
            stage / names["receipt"], _json_text(receipt)
        )
        verify_published_proto_output(
            static_model=static_model, output_dir=stage,
            nameeproto_options=nameeproto_options,
            field_encryption_observation_model=field_encryption_observation_model,
        )
        receipt["checks"]["post_render_revalidation"] = True
        receipt["output_dir"] = str(output_dir)
        for identities in (receipt["files"], receipt["sidecar_files"]):
            for name, identity in identities.items():
                identity["path"] = str(output_dir / name)
        receipt["nameproto_output"]["manifest"]["path"] = str(
            output_dir / names["semantic_names"]
        )
        for name, identity in receipt["nameproto_output"]["files"].items():
            identity["path"] = str(output_dir / names["nameproto"] / name)
        nameeproto_output = receipt["nameproto_output"].get(
            "nameeproto_output"
        )
        if isinstance(nameeproto_output, dict):
            for name, identity in nameeproto_output.get("files", {}).items():
                identity["path"] = str(
                    output_dir / names["nameeproto"] / name
                )
        field_encryption_output = receipt.get("field_encryption_output")
        if isinstance(field_encryption_output, dict):
            field_encryption_output["artifact"]["path"] = str(
                output_dir / names["field_encrypt"]
            )
        _atomic_write_text(
            stage / names["receipt"], _json_text(receipt)
        )
        publish_new_directory(stage, output_dir)
        try:
            verify_published_proto_output(
                static_model=static_model,
                output_dir=output_dir,
                nameeproto_options=nameeproto_options,
                field_encryption_observation_model=field_encryption_observation_model,
            )
            assert_current()
        except BaseException as error:
            quarantine = output_dir.with_name(
                f".{output_dir.name}.invalid-{uuid.uuid4().hex}"
            )
            try:
                publish_new_directory(output_dir, quarantine)
            except BaseException as quarantine_error:
                raise AcquisitionError(
                    "published proto revalidation failed and output could not be quarantined"
                ) from quarantine_error
            raise AcquisitionError(
                f"published proto revalidation failed; output preserved at {quarantine}"
            ) from error
        return receipt
    except BaseException:
        shutil.rmtree(stage, ignore_errors=True)
        raise


def capture_proto_stages(
    *, session, live, output_dir, progress=None,
    field_encryption_observation_model=None,
    partial_proto_without_field_encrypt=False,
):
    root = session.root
    def run(name, callback, dependencies, statuses=("complete", "runtime-validated")):
        if progress:
            progress(name)
        return session.run(name, callback, dependencies=tuple(dependencies), accepted_statuses=statuses)
    run("proto-input", lambda out: write_proto_input(session=session, output_dir=out),
        sorted({stage for stage, name in SOURCES.values()}))
    receipt = root / "proto-input/runtime-proto-input.private.json"
    common = {key: live[key] for key in ("wine", "wineprefix", "compiler", "timeout")}
    run("proto-field-types", lambda out: capture_runtime_proto_field_types(
        native_output_receipt=receipt, output_dir=out, **common), ("proto-input",))
    fields = root / "proto-field-types/runtime-proto-field-types.private.json"
    materializer = root / "materializer-live/runtime-type-materializer.validated.private.json"
    snapshot = root / "memory/runtime-memory.private.bin"
    binding = dict(native_output_receipt=receipt, proto_field_type_model=fields)
    run("proto-enums", lambda out: capture_runtime_proto_enum_constants(
        **binding, runtime_materializer_model=materializer, output_dir=out, **common),
        ("proto-input", "proto-field-types", "materializer-live"))
    enums = root / "proto-enums/runtime-proto-enum-constants.private.json"
    models = dict(binding, enum_constant_model=enums)
    dependencies = ["proto-input", "proto-field-types", "proto-enums"]
    def build(name):
        def build_or_reuse(out):
            from alpha.p42 import (
                RUNTIME_PROTO_STATIC_MODEL_SCHEMA,
                reuse_verified_static_model,
                static_model_input_identities,
            )
            expected_inputs = static_model_input_identities(**models)
            records = list(session.journal["stages"].items())
            candidates = sorted(records, key=lambda item: int(item[1].get("finished_ns", 0)), reverse=True)
            for stage_name, record in candidates:
                if (stage_name == name or record.get("status") != "complete"
                        or record.get("result", {}).get("schema") != RUNTIME_PROTO_STATIC_MODEL_SCHEMA
                        or "model.private.json" not in record.get("artifacts", {})):
                    continue
                candidate = root / stage_name / "model.private.json"
                candidate_model = read_private_model(candidate)
                if candidate_model.get("inputs") != expected_inputs:
                    continue
                session._verify_stage(stage_name)
                candidate_identity = file_identity(candidate)
                seal = record["artifacts"]["model.private.json"]
                if any(candidate_identity[key] != seal[key] for key in ("bytes", "sha256")):
                    raise AcquisitionError("static model reuse candidate differs from journal")
                reused = reuse_verified_static_model(
                    work_dir=root, implementation=record["implementation"],
                    candidate=candidate, expected_inputs=expected_inputs,
                    candidate_identity=candidate_identity,
                    output_path=out / "model.private.json")
                if reused is not None:
                    return reused
            return write_runtime_proto_static_model(**models, output_path=out / "model.private.json")
        run(name, build_or_reuse, dependencies,
            ("complete", "needs-runtime-field-closure"))
        return root / name / "model.private.json"
    model_path = build("proto-model-initial")
    def unresolved():
        return read_private_model(model_path).get("unresolved_owner_only", [])
    probe = dict(binding, snapshot=snapshot, runtime_materializer_model=materializer, **common)
    if any(str(row.get("kind", "")).startswith("oneof") for row in unresolved()):
        run("proto-oneof-plan", lambda out: write_runtime_proto_oneof_mutation_plan(
            native_output_receipt=receipt, static_model=model_path,
            enum_constant_model=enums, output_path=out / "plan.private.json"),
            (*dependencies, "proto-model-initial"), ("offline-plan-complete", "complete"))
        run("proto-oneof", lambda out: capture_field_mutations_with_retry(
            **probe, mutation_plan=root / "proto-oneof-plan/plan.private.json", output_dir=out,
            process_check=session.assert_current),
            (*dependencies, "proto-oneof-plan", "memory", "materializer-live"))
        models.update(oneof_mutation_model=root / "proto-oneof/runtime-proto-field-mutations.private.json",
                      runtime_materializer_model=materializer, snapshot=snapshot)
        dependencies.extend(("proto-oneof", "memory", "materializer-live"))
        model_path = build("proto-model-oneof")
    last_serializer_plan: Path | None = None
    if any(row.get("kind") == "normal-field-assignment" for row in unresolved()):


        prior_stage = model_path.parent.name
        run("proto-field-plan", lambda out: write_runtime_proto_field_mutation_plan(
            native_output_receipt=receipt, static_model=model_path,
            output_path=out / "plan.private.json", allow_other_gaps=True,
            serializer_differential=True), (*dependencies, prior_stage),
            ("offline-plan-complete", "complete"))
        run("proto-serializer", lambda out: capture_runtime_proto_serializer_probe(
            **probe, mutation_plan=root / "proto-field-plan/plan.private.json", output_dir=out),
            (*dependencies, "proto-field-plan", "memory", "materializer-live"))
        models["serializer_probe_model"] = root / "proto-serializer/runtime-proto-serializer-probe.private.json"
        last_serializer_plan = root / "proto-field-plan/plan.private.json"
        dependencies.append("proto-serializer")
        model_path = build("proto-model-serialized")
        if any(row.get("kind") == "normal-field-assignment" for row in unresolved()):
            run("proto-remaining-field-plan", lambda out: write_runtime_proto_field_mutation_plan(
                native_output_receipt=receipt, static_model=model_path,
                output_path=out / "plan.private.json", allow_other_gaps=True),
                (*dependencies, "proto-model-serialized"), ("offline-plan-complete", "complete"))
            remaining_plan = read_json(root / "proto-remaining-field-plan/plan.private.json")
            if int((remaining_plan.get("counts") or {}).get("message_probe_count") or 0):
                run("proto-field-mutations", lambda out: capture_field_mutations_with_retry(
                    **probe, mutation_plan=root / "proto-remaining-field-plan/plan.private.json", output_dir=out,
                    process_check=session.assert_current),
                    (*dependencies, "proto-remaining-field-plan", "memory", "materializer-live"))
                models["mutation_model"] = root / "proto-field-mutations/runtime-proto-field-mutations.private.json"
                dependencies.append("proto-field-mutations")
                model_path = build("proto-model-final")


    carried_scan_stages: list[str] = []
    closed_scans = []
    for stage_name, stage_record in session.journal["stages"].items():
        if not stage_name.startswith("proto-model-parser-scanned-") or stage_record.get("status") != "complete":
            continue
        source_path = root / stage_name / "model.private.json"
        session._verify_stage(stage_name)
        source = read_private_model(source_path)
        if any(row.get("kind") == "normal-field-assignment" for row in source.get("unresolved_owner_only", [])):
            continue
        if any(source.get("target", {}).get(key) != session.journal["identity"].get(key)
               for key in ("process_id", "creation_filetime", "image_base", "executable_sha256")):
            continue
        source_inputs = source.get("inputs", {})
        required_inputs = {
            "native_output_receipt": receipt,
            "proto_field_type_model": fields,
            "enum_constant_model": enums,
            "snapshot": snapshot,
            "runtime_materializer_model": materializer,
        }
        if any(source_inputs.get(key) != file_identity(path)
               for key, path in required_inputs.items()):
            continue
        oneof_source = models.get("oneof_mutation_model")
        if oneof_source is not None and source_inputs.get("oneof_mutation_model") != file_identity(oneof_source):
            continue
        serializer_source = models.get("serializer_probe_model")
        if serializer_source is not None:
            serializer_paths = serializer_source if isinstance(serializer_source, list) else [serializer_source]
            if source_inputs.get("serializer_probe_models") != [file_identity(path) for path in serializer_paths]:
                continue
        mutation_inputs = source_inputs.get("mutation_models")
        if not isinstance(mutation_inputs, list) or not mutation_inputs:
            continue
        scan_stages = []
        expected_start = 1
        revision = None
        for ordinal, identity in enumerate(mutation_inputs, 1):
            if not isinstance(identity, Mapping) or not isinstance(identity.get("path"), str):
                break
            mutation_path = Path(identity["path"])
            name = mutation_path.parent.name
            match = re.fullmatch(r"proto-parser-scan-([0-9a-f]{12})-(\d+)", name)
            if (not match or int(match.group(2)) != ordinal
                    or revision is not None and revision != match.group(1)
                    or mutation_path != root / name / "runtime-proto-field-mutations.private.json"
                    or file_identity(mutation_path) != identity):
                break
            revision = match.group(1)
            plan_name = f"proto-parser-scan-plan-{revision}-{ordinal}"
            session._verify_stage(name)
            session._verify_stage(plan_name)
            plan = read_json(root / plan_name / "plan.private.json")
            window = (plan.get("policy") or {}).get("runtime_scan_window")
            if (not isinstance(window, list) or len(window) != 2
                    or type(window[0]) is not int or type(window[1]) is not int
                    or window[0] != expected_start or window[1] < window[0]):
                break
            expected_start = window[1] + 1
            scan_stages.extend((plan_name, name))
        else:
            closed_scans.append((expected_start, source_path, scan_stages, mutation_inputs))
    if closed_scans:
        _, carried_source, carried_scan_stages, mutation_inputs = max(closed_scans, key=lambda item: item[0])
        previous = models.get("mutation_model", [])
        models["mutation_model"] = (
            previous if isinstance(previous, list) else [previous]
        ) + [Path(item["path"]) for item in mutation_inputs]
        dependencies.extend((*carried_scan_stages, carried_source.parent.name))
        model_path = build(f"proto-model-carried-{session.implementation[:12]}")
        if any(row.get("kind") == "normal-field-assignment" for row in unresolved()):
            raise AcquisitionError(
                "completed parser scan no longer closes the current model; preserved evidence requires review"
            )


    prior_model_stage = model_path.parent.name
    prior_model_record = session.journal["stages"][prior_model_stage]
    if not carried_scan_stages and prior_model_record.get("implementation") != session.implementation:
        refresh_name = f"proto-model-refresh-{session.implementation[:12]}"
        refresh_dependencies = tuple(dict.fromkeys(
            [*dependencies, prior_model_stage]
        ))
        run(
            refresh_name,
            lambda out: write_runtime_proto_static_model(
                **models, output_path=out / "model.private.json"
            ),
            refresh_dependencies,
            ("complete", "needs-runtime-field-closure"),
        )
        model_path = root / refresh_name / "model.private.json"
        dependencies.append(refresh_name)


    scan_start = 1
    scan_attempt = 1
    while any(row.get("kind") == "normal-field-assignment" for row in unresolved()):
        if scan_start > 0x1FFFFFFF:
            raise AcquisitionError("runtime parser differential scan exhausted protobuf field numbers")


        scan_end = min(scan_start + 511, 0x1FFFFFFF)


        scan_revision = session.implementation[:12]
        scan_plan_stage = f"proto-parser-scan-plan-{scan_revision}-{scan_attempt}"
        scan_probe_stage = f"proto-parser-scan-{scan_revision}-{scan_attempt}"
        run(scan_plan_stage, lambda out, a=scan_start, b=scan_end: write_runtime_proto_field_mutation_plan(
            native_output_receipt=receipt, static_model=model_path,
            output_path=out / "plan.private.json", allow_other_gaps=True,
            runtime_scan_window=(a, b), force_runtime_scan=True),
            (*dependencies, model_path.parent.name), ("offline-plan-complete", "complete"))
        scan_plan = read_json(root / scan_plan_stage / "plan.private.json")
        if not int((scan_plan.get("counts") or {}).get("message_probe_count") or 0):
            raise AcquisitionError("runtime parser scan has no eligible unresolved fields")
        run(scan_probe_stage, lambda out: capture_field_mutations_with_retry(
            **probe, mutation_plan=root / scan_plan_stage / "plan.private.json", output_dir=out,
            process_check=session.assert_current),
            (*dependencies, scan_plan_stage, "memory", "materializer-live"))
        previous_mutations = models.get("mutation_model", [])
        models["mutation_model"] = (
            previous_mutations if isinstance(previous_mutations, list) else [previous_mutations]
        ) + [root / scan_probe_stage / "runtime-proto-field-mutations.private.json"]
        dependencies.append(scan_probe_stage)
        model_path = build(f"proto-model-parser-scanned-{scan_revision}-{scan_attempt}")
        scan_start = scan_end + 1
        scan_attempt += 1

    attempt = 1
    previous_unresolved_normal_count = sum(
        len(row.get("field_indexes_owner_only", []))
        for row in unresolved()
        if row.get("kind") == "normal-field-assignment"
    )
    while previous_unresolved_normal_count:
        unresolved_indexes = {
            int(field_index)
            for row in unresolved()
            if row.get("kind") == "normal-field-assignment"
            for field_index in row.get("field_indexes_owner_only", [])
        }
        if last_serializer_plan is not None:
            previous_plan = read_json(last_serializer_plan)
            previously_probed = {
                int(field["field_index_owner_only"])
                for message in previous_plan.get("messages_owner_only", [])
                for field in message.get("fields_owner_only", [])
            }
            if unresolved_indexes and unresolved_indexes <= previously_probed:
                break
        plan_stage = f"proto-serializer-retry-plan-{attempt}"
        probe_stage = f"proto-serializer-retry-{attempt}"
        run(plan_stage, lambda out: write_runtime_proto_field_mutation_plan(
            native_output_receipt=receipt, static_model=model_path,
            output_path=out / "plan.private.json", allow_other_gaps=True,
            serializer_differential=True),
            (*dependencies, model_path.parent.name), ("offline-plan-complete", "complete"))
        retry_plan = read_json(root / plan_stage / "plan.private.json")
        if not int((retry_plan.get("counts") or {}).get("message_probe_count") or 0):


            break
        run(probe_stage, lambda out: capture_runtime_proto_serializer_probe(
            **probe, mutation_plan=root / plan_stage / "plan.private.json", output_dir=out),
            (*dependencies, plan_stage, "memory", "materializer-live"))
        previous = models.get("serializer_probe_model", [])
        models["serializer_probe_model"] = (
            previous if isinstance(previous, list) else [previous]
        ) + [root / probe_stage / "runtime-proto-serializer-probe.private.json"]
        last_serializer_plan = root / plan_stage / "plan.private.json"
        dependencies.append(probe_stage)
        model_path = build(f"proto-model-retried-{attempt}")
        current_unresolved_normal_count = sum(
            len(row.get("field_indexes_owner_only", []))
            for row in unresolved()
            if row.get("kind") == "normal-field-assignment"
        )
        if current_unresolved_normal_count >= previous_unresolved_normal_count:
            raise AcquisitionError(
                "runtime proto serializer closure made no field progress: "
                f"{current_unresolved_normal_count}/"
                f"{previous_unresolved_normal_count} unresolved"
            )
        previous_unresolved_normal_count = current_unresolved_normal_count
        attempt += 1
    model = read_private_model(model_path)
    blocking = unresolved()
    if blocking or model.get("status") != "complete":
        normal = [
            row for row in blocking if row.get("kind") == "normal-field-assignment"
        ]
        field_total = sum(
            len(row.get("field_indexes_owner_only") or []) for row in normal
        )
        names = sorted({str(row.get("message")) for row in normal})
        if normal:
            detail = (
                f"{len(normal)} message(s) / {field_total} field(s) have no "
                "current-runtime tag evidence "
                f"({', '.join(names[:8])}{', ...' if len(names) > 8 else ''})"
            )
        else:
            checks = model.get("checks") or {}
            failed_checks = sorted(
                str(key) for key, value in checks.items() if value is not True
            )
            unresolved_kinds = sorted(
                {str(row.get("kind")) for row in blocking if row.get("kind")}
            )
            detail = "failed checks: " + ", ".join(
                failed_checks or ["no failing check name was recorded"]
            )
            if unresolved_kinds:
                detail += "; unresolved kinds: " + ", ".join(unresolved_kinds)
        raise AcquisitionError(
            f"proto closure incomplete: {detail}; inspect {model_path}"
        )
    signed_rows = model.get("signed_encoding_coverage_owner_only", {}).get(
        "roles_owner_only", []
    )
    if any(not row["verified"] for row in signed_rows):
        previous_signed = root / "proto-model-signed-complete/model.private.json"
        reused_signed = False
        if (
            "proto-signed-parse" in session.journal["stages"]
            and "proto-model-signed-complete" in session.journal["stages"]
            and previous_signed.is_file()
        ):
            session._verify_stage("proto-signed-parse")
            session._verify_stage("proto-model-signed-complete")
            prior = read_private_model(previous_signed)
            source_identity = prior.get("inputs", {}).get("signed_parse_source_model")
            if isinstance(source_identity, dict):
                source_path = Path(str(source_identity.get("path", "")))
                if (
                    source_path.is_file()
                    and file_identity(source_path) == source_identity
                    and read_private_model(source_path) == model
                ):
                    dependencies.append("proto-signed-parse")
                    model_path = previous_signed
                    model = prior
                    reused_signed = True
        if not reused_signed:
            source_stage = model_path.parent.name
            signed_stage = (
                "proto-signed-parse"
                if "proto-signed-parse" not in session.journal["stages"]
                else f"proto-signed-parse-{session.implementation[:12]}"
            )
            signed_model_stage = (
                "proto-model-signed-complete"
                if "proto-model-signed-complete" not in session.journal["stages"]
                else f"proto-model-signed-complete-{session.implementation[:12]}"
            )
            run(
                signed_stage,
                lambda out: capture_signed_parse_with_retry(
                    static_model=model_path,
                    snapshot=snapshot,
                    native_output_receipt=receipt,
                    proto_field_type_model=fields,
                    runtime_materializer_model=materializer,
                    output_dir=out,
                    **common,
                ),
                (*dependencies, source_stage, "memory", "materializer-live"),
            )
            run(
                signed_model_stage,
                lambda out: write_verified_parse_model(
                    static_model=model_path,
                    parse_model=(
                        root / signed_stage / "runtime-proto-signed-parse.private.json"
                    ),
                    output_path=out / "model.private.json",
                ),
                (*dependencies, source_stage, signed_stage),
                ("complete",),
            )
            dependencies.append(signed_stage)
            model_path = root / signed_model_stage / "model.private.json"
            model = read_private_model(model_path)


    from alpha.p43 import unsigned_encoding_coverage
    if not unsigned_encoding_coverage(model)["complete"]:
        source_stage = model_path.parent.name
        source_digest = file_identity(model_path)["sha256"][:12]
        unsigned_stage = f"proto-unsigned-parse-{source_digest}"
        unsigned_model_stage = f"proto-model-unsigned-complete-{source_digest}"
        run(
            unsigned_stage,
            lambda out: capture_signed_parse_with_retry(
                static_model=model_path, snapshot=snapshot,
                native_output_receipt=receipt, proto_field_type_model=fields,
                runtime_materializer_model=materializer, output_dir=out,
                unsigned_encoding_audit=True, **common,
            ),
            (*dependencies, source_stage, "memory", "materializer-live"),
        )
        run(
            unsigned_model_stage,
            lambda out: write_verified_parse_model(
                static_model=model_path,
                parse_model=root / unsigned_stage / "runtime-proto-signed-parse.private.json",
                output_path=out / "model.private.json", unsigned_encoding_audit=True,
            ),
            (*dependencies, source_stage, unsigned_stage),
            ("complete",),
        )
        dependencies.extend((unsigned_stage, unsigned_model_stage))
        model_path = root / unsigned_model_stage / "model.private.json"
        model = read_private_model(model_path)
        if not unsigned_encoding_coverage(model)["complete"]:
            raise AcquisitionError("unsigned wire encoding verification is incomplete")

    if model.get("full_semantic_verification_complete") is not True:
        signed = model.get("signed_encoding_coverage_owner_only", {})
        domain = model.get("message_domain_audit_owner_only", {})
        raise AcquisitionError(
            "proto exhaustive verification incomplete: "
            f"signed roles {signed.get('verified_count', 0)}/"
            f"{signed.get('required_count', 'required count absent')}; "
            f"unexplained descendants {len(domain.get('unexplained_type_indexes_owner_only', []))}; "
            f"unresolved ancestry {len(domain.get('ancestry_errors_owner_only', []))}. "
            f"outside-base serializer candidates "
            f"{len(domain.get('outside_base_serializer_candidates_owner_only', []))}. "
            f"Acquisition retained; inspect {model_path}")

    source_stage = model_path.parent.name
    def capture_field_transform(out):
        probe_receipt = capture_field_transform_with_retry(
            static_model=model_path,
            snapshot=snapshot,
            native_output_receipt=receipt,
            proto_field_type_model=fields,
            runtime_materializer_model=materializer,
            output_dir=out / "runtime-probe",
            **common,
        )
        probe_model = read_private_model(
            Path(probe_receipt["model"]["path"])
        )
        if file_identity(Path(probe_receipt["model"]["path"])) != probe_receipt["model"]:
            raise AcquisitionError("initial field transform model changed during capture")
        from alpha.p43 import _field_transform_role_inventory
        from alpha.p50 import (
            ADAPTIVE_SAMPLE_COUNT,
            MAX_ADAPTIVE_ROUNDS,
            build_field_encryption_observation_model,
            next_runtime_probe_values,
            require_publishable_field_encryption_model,
            unresolved_field_transform_roles,
            validate_observation_inventory,
        )

        role_inventory = _field_transform_role_inventory(model)
        role_indexes = {
            tuple(row[name] for name in (
                "type_index_owner_only", "number", "container", "role"
            )): index
            for index, row in enumerate(role_inventory)
        }
        adaptive_receipts = []
        unresolved = unresolved_field_transform_roles(probe_model)
        for key in sorted(unresolved):
            role_index = role_indexes.get(key)
            if role_index is None:
                raise AcquisitionError(
                    "adaptive field transform role is outside the current runtime schema"
                )
            for attempt in range(MAX_ADAPTIVE_ROUNDS):
                pending = unresolved_field_transform_roles(
                    probe_model, identities=(key,)
                )
                if key not in pending:
                    break
                row = pending[key]
                width = int(row["width"])
                probe_values = next_runtime_probe_values(
                    row["samples"], width, candidates=row["candidates"],
                    count=ADAPTIVE_SAMPLE_COUNT,
                )
                role_dir = (
                    out / "runtime-adaptive" / f"role-{role_index:06d}"
                    / f"round-{attempt:03d}"
                )
                extra_receipt = capture_field_transform_with_retry(
                    static_model=model_path,
                    snapshot=snapshot,
                    native_output_receipt=receipt,
                    proto_field_type_model=fields,
                    runtime_materializer_model=materializer,
                    output_dir=role_dir,
                    field_transform_role_index=role_index,
                    field_transform_probe_values={
                        width: probe_values,
                    },
                    **{**common, "timeout": min(float(common["timeout"]), 180.0)},
                )
                if file_identity(Path(extra_receipt["model"]["path"])) != extra_receipt["model"]:
                    raise AcquisitionError("adaptive field transform model changed during capture")
                extra_model = read_private_model(Path(extra_receipt["model"]["path"]))
                extra_rows = extra_model.get("observations")
                if (
                    extra_model.get("target") != probe_model.get("target")
                    or not isinstance(extra_rows, list)
                    or len(extra_rows) != 1
                ):
                    raise AcquisitionError(
                        "adaptive field transform capture target or role count differs"
                    )
                extra = extra_rows[0]
                extra_identity = extra.get("identity")
                if not isinstance(extra_identity, dict) or tuple(
                    extra_identity.get(name) for name in (
                        "type_index_owner_only", "number", "container", "role"
                    )
                ) != key:
                    raise AcquisitionError(
                        "adaptive field transform capture returned a different role"
                    )
                base = next(
                    row for row in probe_model["observations"]
                    if tuple(row["identity"][name] for name in (
                        "type_index_owner_only", "number", "container", "role"
                    )) == key
                )
                if any(
                    base.get(name) != extra.get(name)
                    for name in ("encoding", "context", "field_index_owner_only")
                ):
                    raise AcquisitionError(
                        "adaptive field transform role context changed between captures"
                    )
                additional = extra.get("samples_owner_only")
                if (
                    not isinstance(additional, list)
                    or len(additional) != len(probe_values)
                    or [sample.get("serialized_value") for sample in additional
                        if isinstance(sample, Mapping)] != probe_values
                ):
                    raise AcquisitionError(
                        "adaptive field transform capture differs from its requested batch"
                    )
                all_inputs = {
                    sample.get("serialized_value")
                    for sample in base["samples_owner_only"]
                }
                if any(sample.get("serialized_value") in all_inputs for sample in additional):
                    raise AcquisitionError(
                        "adaptive field transform repeated a previously observed input"
                    )
                base["samples_owner_only"].extend(additional)
                adaptive_receipts.append({
                    "identity": dict(extra_identity),
                    "round": attempt + 1,
                    "probe_values_owner_only": probe_values,
                    "capture": extra_receipt,
                })
            else:
                pending_after_last_capture = unresolved_field_transform_roles(
                    probe_model, identities=(key,)
                )
                if key in pending_after_last_capture:
                    raise AcquisitionError(
                        f"field transform remains ambiguous after {MAX_ADAPTIVE_ROUNDS} "
                        "adaptive runtime rounds "
                        f"(type={key[0]}, tag={key[1]}, container={key[2]}, role={key[3]})"
                    )

        probe_model["initial_capture_model"] = probe_receipt["model"]
        probe_model["adaptive_captures_owner_only"] = adaptive_receipts
        sample_counts = [
            len(row.get("samples_owner_only", []))
            for row in probe_model["observations"]
        ]
        counts = probe_model.setdefault("counts", {})
        counts.pop("sample_count_per_role", None)
        counts["sample_count_min"] = min(sample_counts, default=0)
        counts["sample_count_max"] = max(sample_counts, default=0)
        combined_probe_path = out / "runtime-field-transform-probe-closed.private.json"
        _private_json(combined_probe_path, probe_model)

        observation_model = build_field_encryption_observation_model(
            proto_model=model,
            runtime_probe=probe_model,
            runtime_probe_model_identity=file_identity(combined_probe_path),
        )
        observation_path = out / "field-encryption-observation.private.json"
        _private_json(observation_path, observation_model)
        _private_json(out / "field-transform-probe-receipt.private.json", {
            **probe_receipt,
            "model": file_identity(combined_probe_path),
            "adaptive_capture_count": len(adaptive_receipts),
            "adaptive_role_count": len({
                tuple(item["identity"][name] for name in (
                    "type_index_owner_only", "number", "container", "role"
                )) for item in adaptive_receipts
            }),
        })
        observations = validate_observation_inventory(
            observation_model,
            executable_sha256=model["target"]["executable_sha256"],
            expected_target=model["target"],
        )


        return {
            "schema": observation_model["schema"],
            "status": observation_model["status"],
            "target": observation_model["target"],
            "coverage": observation_model["coverage"],
            "field_encryption_publication": {"status": "pending-proof"},
            "model": file_identity(observation_path),
        }

    if partial_proto_without_field_encrypt:
        if field_encryption_observation_model is not None:
            raise AcquisitionError("partial proto output cannot use field-encryption observations")
        from alpha.p43 import _field_transform_role_inventory
        def record_omission(out):
            record = {
                "schema": "alpha.field-encryption-omission/v1",
                "status": "deferred",
                "target": model["target"],
                "reason": "numeric runtime transforms remain unproven",
                "numeric_role_count": len(_field_transform_role_inventory(model)),
                "field_encrypt_published": False,
            }
            _private_json(out / "field-encryption-omission.private.json", record)
            return record
        run(
            "proto-field-encryption-omission", record_omission,
            (*dependencies, source_stage), ("deferred",),
        )
        dependencies.append("proto-field-encryption-omission")
    else:
        run(
            "proto-field-transform",
            capture_field_transform,
            (*dependencies, source_stage, "memory", "materializer-live", "proto-field-types"),
            ("complete", "runtime-validated"),
        )
        dependencies.append("proto-field-transform")
        fresh_observation_path = (
            root / "proto-field-transform/field-encryption-observation.private.json"
        )
        if (
            field_encryption_observation_model is not None
            and field_encryption_observation_model.expanduser().resolve()
            != fresh_observation_path.resolve()
        ):
            raise AcquisitionError(
                "field-encryption publication requires the freshly captured current-runtime model"
            )
        field_encryption_observation_model = fresh_observation_path
        def verify_field_transform_publication(out):
            from alpha.native_reader_evidence import build_reader_dependency_inventory
            from alpha.p29 import _validated_native_receipt
            from alpha.p50 import (
                require_publishable_field_encryption_model,
                validate_observation_inventory,
            )
            identity = file_identity(fresh_observation_path)
            observation = read_private_model(fresh_observation_path)
            observations = validate_observation_inventory(
                observation, executable_sha256=model["target"]["executable_sha256"],
                expected_target=model["target"],
            )


            _, native_paths = _validated_native_receipt(
                receipt, allow_type_method_metadata=True,
            )
            native_dependencies = build_reader_dependency_inventory(
                binary=native_paths["binary"], proto_model=model,
            )
            native_dependencies["static_model"] = file_identity(model_path)
            native_dependencies["observation_model"] = identity
            _private_json(out / "native-reader-dependencies.private.json", native_dependencies)
            coverage = require_publishable_field_encryption_model(
                observation, observations, allow_partial=False,
            )
            if file_identity(fresh_observation_path) != identity:
                raise AcquisitionError("field transform evidence changed during publication proof")
            proof = {"schema": "alpha.field-transform-publication-proof/v1",
                     "status": "complete", "target": model["target"],
                     "model": identity, "coverage": coverage}
            _private_json(out / "proof.private.json", proof)
            return proof
        run("proto-field-transform-publication-proof", verify_field_transform_publication,
            (*dependencies, source_stage), ("complete",))
        dependencies.append("proto-field-transform-publication-proof")

    def publish(out):
        receipt = publish_proto(
            static_model=model_path, output_dir=output_dir,
            assert_current=session.assert_current,
            field_encryption_observation_model=field_encryption_observation_model,
            partial_proto_without_field_encrypt=partial_proto_without_field_encrypt,
        )
        _private_json(out / "publication.private.json", receipt)
        return receipt
    return run("proto-publish", publish, (*dependencies, model_path.parent.name))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("binary", "work-dir", "output-dir", "wine", "wineprefix"):
        parser.add_argument("--" + name, required=True, type=Path)
    parser.add_argument("--compiler", type=Path)
    parser.add_argument("--timeout", type=float, default=1800)
    parser.add_argument("--resume", action="store_true")
    parser.add_argument("--repair-resume", action="store_true")
    parser.add_argument("--carry-forward", action="store_true")
    parser.add_argument(
        "--rebind-live-process", action="store_true",
        dest="rebind_live_process"
    )
    parser.add_argument(
        "--salvage-restart", action="store_true",
        dest="salvage_restart"
    )
    parser.add_argument("--partial-proto-without-field-encrypt", action="store_true")
    parser.add_argument("--with-metadata", action="store_true")
    parser.add_argument("--metadata-only", action="store_true")
    parser.add_argument("--metadata-output-dir", type=Path)
    parser.add_argument("--skip-metadata-reconstruction", action="store_true")
    parser.add_argument(
        "--metadata-domain-observation", type=Path, action="append", default=[],
    )
    parser.add_argument("--reachable-heap-limit-mib", type=int, default=0)
    args = parser.parse_args()
    if args.carry_forward and not (args.resume and args.repair_resume):
        raise SystemExit("--carry-forward requires --resume --repair-resume")
    if args.salvage_restart and not (args.resume and args.repair_resume):
        raise SystemExit("--salvage-restart requires --resume --repair-resume")


    memo_dir = args.work_dir.expanduser().resolve() / ".memo-cache"
    from alpha.p29 import set_analysis_memo_dir
    from alpha.p42 import set_writer_references_memo_dir
    from alpha.p12 import set_windows_build_memo_dir
    from alpha.h02 import set_file_hash_memo_dir
    set_analysis_memo_dir(memo_dir)
    set_writer_references_memo_dir(memo_dir)
    set_windows_build_memo_dir(memo_dir)
    set_file_hash_memo_dir(memo_dir)
    try:
        preflight(args.output_dir)
        from alpha.p19 import capture_fresh_runtime_bootstrap
        metadata_output_dir = args.metadata_output_dir
        if metadata_output_dir is None and args.metadata_only:
            metadata_output_dir = args.output_dir
        elif metadata_output_dir is None and args.with_metadata:
            metadata_output_dir = args.output_dir / "metadata"
        result = capture_fresh_runtime_bootstrap(binary=args.binary, output_dir=args.work_dir,
            proto_output_dir=None if args.metadata_only else args.output_dir,
            wine=args.wine, wineprefix=args.wineprefix,
            compiler=args.compiler, timeout=args.timeout, resume=args.resume,
            repair_resume=args.repair_resume,
            carry_forward=args.carry_forward,
            allow_process_rebind=bool(
                getattr(args, "rebind_live_process", False)
                or getattr(args, "salvage_restart", False)
            ),
            salvage_restart=getattr(args, "salvage_restart", False),
            partial_proto_without_field_encrypt=args.partial_proto_without_field_encrypt,
            metadata_output_dir=metadata_output_dir,
            metadata_reconstruct=not args.skip_metadata_reconstruction,
            metadata_domain_observations=tuple(args.metadata_domain_observation),
            reachable_heap_limit_mib=args.reachable_heap_limit_mib,
            progress=lambda stage: print(f"proto pipeline: {stage}", flush=True))
        print(json.dumps(result, ensure_ascii=False))
    except (AcquisitionError, OSError, ValueError) as error:
        print(json.dumps({"status": "error", "reason": str(error)}, ensure_ascii=False), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
