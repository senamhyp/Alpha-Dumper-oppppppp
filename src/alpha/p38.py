from alpha.h02 import windows_run as _host_run

import json
import os
import stat
import struct
import subprocess
import time
from collections import Counter
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import _build, _compiler, _owner_directory, _private_bytes, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.p37 import validated_proto_receipt as _validated_native_receipt
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER
from alpha.p33 import _RuntimeOutput
from alpha.p33 import _MetadataUsageTypeRenderer
from alpha.p20 import load_runtime_metadata_usage_value_inventory
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_MEMBER_HEADER, _NATIVE_MEMBER_MAGIC, _NATIVE_MEMBER_RECORD, _NATIVE_MEMBER_VERSION, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json


RUNTIME_PROTO_FIELD_TYPE_PLAN_SCHEMA = "alpha.runtime-proto-field-type-plan/v1"
RUNTIME_PROTO_FIELD_TYPE_STATUS_SCHEMA = "alpha.runtime-proto-field-type-status/v1"
RUNTIME_PROTO_FIELD_TYPE_SCHEMA = "alpha.runtime-proto-field-type-inventory/v1"
RUNTIME_PROTO_FIELD_TYPE_MAGIC = b"ALPHAPF1"
RUNTIME_PROTO_FIELD_TYPE_VERSION = 1
RUNTIME_PROTO_FIELD_TYPE_HEADER = struct.Struct("<8sIIIIQQ64s64s64s")
RUNTIME_PROTO_FIELD_TYPE_RECORD = struct.Struct("<IIQQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime proto {label} is not owner-only")
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
        raise AcquisitionError(f"runtime proto operation is unavailable: {key}")
    return rows[0]


def _evidence_qword(
    semantics: dict[str, Any], *, collection: str, operation: str
) -> int:
    rows = [
        row
        for row in semantics.get(collection, [])
        if isinstance(row, dict)
        and row.get("operation_key") == operation
        and isinstance(row.get("selected_field_qword"), int)
        and row.get("selected_field_support", 0) >= 128
    ]
    if len(rows) != 1 or not 2 <= rows[0]["selected_field_qword"] < 64:
        raise AcquisitionError(
            f"runtime proto object layout is unavailable: {operation}"
        )
    return rows[0]["selected_field_qword"]


def _class_pointer(class_model: dict[str, Any], owner: str) -> int:
    values = [
        row.get("class_pointer")
        for row in class_model.get("classes", [])
        if isinstance(row, dict) and row.get("runtime_owner") == owner
    ]
    if len(values) != 1 or not isinstance(values[0], int) or values[0] <= 0:
        raise AcquisitionError(f"runtime proto class is unavailable: {owner}")
    return values[0]


def _binding(native_output_receipt: Path) -> dict[str, Any]:
    receipt, paths = _validated_native_receipt(
        native_output_receipt, allow_type_method_metadata=True
    )
    type_model = read_json(paths["model"])
    member_model_record = type_model.get("inputs", {}).get(
        "native_member_detail_model"
    )
    if not isinstance(member_model_record, dict) or not isinstance(
        member_model_record.get("path"), str
    ):
        raise AcquisitionError("runtime proto native member model is unavailable")
    member_model_path = _owner_file(
        Path(member_model_record["path"]), label="native member model"
    )
    if file_identity(member_model_path) != member_model_record:
        raise AcquisitionError("runtime proto native member model is stale")
    member_model = read_json(member_model_path)
    semantics_path = _owner_file(
        Path(member_model["inputs"]["semantics"]["path"]),
        label="reflection semantics",
    )
    class_model_path = _owner_file(
        Path(member_model["inputs"]["class_model"]["path"]),
        label="class model",
    )
    type_plan_path = _owner_file(
        Path(member_model["inputs"]["type_identity_plan"]["path"]),
        label="type identity plan",
    )
    semantics = read_json(semantics_path)
    class_model = read_json(class_model_path)
    type_plan = read_json(type_plan_path)
    field_from_handle = _operation(semantics, "field.from_handle")

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
    base_counts: Counter[int] = Counter()
    for index in range(runtime.type_count):
        identity = runtime.renderer.identity_row(index)
        graph = runtime.renderer.graph_row(index)
        attributes = identity[7]
        if (
            attributes & 0x100
            and not identity[1] & 0x60
            and not attributes & 0x20
            and graph[6] >= 2
            and graph[3]
        ):
            base_counts[graph[3]] += 1
    ranked = base_counts.most_common(2)
    if (
        len(ranked) < 2
        or ranked[0][1] < 128
        or ranked[0][1] < ranked[1][1] * 4
    ):
        raise AcquisitionError("runtime proto dominant sealed base is ambiguous")
    selected_base, selected_support = ranked[0]
    family_types = [
        index
        for index in range(runtime.type_count)
        if runtime.renderer.graph_row(index)[3] == selected_base
        and runtime.renderer.identity_row(index)[7] & 0x100
        and runtime.renderer.graph_row(index)[6] >= 2
        and runtime.renderer.graph_row(index)[7] == 0
    ]
    if len(family_types) != selected_support:
        raise AcquisitionError(
            "runtime proto sealed self-message family is inconsistent"
        )
    selected_types = [
        index
        for index in family_types
        if "System.Collections.Generic.IEnumerable<System.Byte>"
        not in runtime.renderer.root_interfaces(index)
    ]
    if not selected_types:
        raise AcquisitionError("runtime proto sealed message family is empty")


    selected_set = set(family_types)
    native = paths["native_member_detail_inventory"].read_bytes()
    header = RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.unpack_from(native)
    selected_fields: list[int] = []
    for field_index in range(header[5]):
        row = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + field_index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        if row[0] in selected_set and not row[5] & 0x10:
            selected_fields.append(field_index)
    if not selected_fields:
        raise AcquisitionError("runtime proto field domain is empty")
    return {
        "receipt": file_identity(native_output_receipt.expanduser().resolve()),
        "target": receipt["target"],
        "binary": file_identity(paths["binary"]),
        "native_inventory": file_identity(
            Path(member_model["inputs"]["native_inventory"]["path"])
        ),
        "native_member_inventory": file_identity(
            Path(member_model["inputs"]["native_member_inventory"]["path"])
        ),
        "native_member_detail_inventory": file_identity(
            paths["native_member_detail_inventory"]
        ),
        "metadata_usage_pair_inventory": file_identity(
            paths["metadata_usage_pair_inventory"]
        ),
        "metadata_usage_value_model": file_identity(
            paths["metadata_usage_value_model"]
        ),
        "metadata_usage_value_inventory": file_identity(
            paths["metadata_usage_value_inventory"]
        ),
        "reflection_semantics": file_identity(semantics_path),
        "type_identity_plan": file_identity(type_plan_path),
        "process_id": type_plan["target"]["process_id"],
        "image_base": type_plan["target"]["image_base_owner_only"],
        "image_bytes": type_plan["target"]["image_bytes"],
        "descriptor_offset": type_plan[
            "embedded_type_descriptor_offset_owner_only"
        ],
        "field_class": _class_pointer(
            class_model, "System.Reflection.MonoField"
        ),
        "type_class": _class_pointer(class_model, "System.RuntimeType"),
        "field_from_handle": {
            "pointer": field_from_handle["method_pointer"],
            "metadata": field_from_handle["metadata_pointer"],
        },
        "field_type_object_qword": _evidence_qword(
            semantics,
            collection="object_field_evidence",
            operation="field.type",
        ),
        "type_handle_object_qword": _evidence_qword(
            semantics,
            collection="native_type_descriptor_evidence",
            operation="type.handle",
        ),
        "type_count": runtime.type_count,
        "method_count": runtime.method_count,
        "field_count": runtime.field_count,
        "selected_base_descriptor_owner_only": selected_base,
        "message_type_indexes": selected_types,
        "field_indexes": selected_fields,
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#define ALPHA_BATCH 512u
typedef struct native_header { char magic[8]; uint32_t version,type_bytes,method_bytes,reserved; uint64_t type_count,method_count,image_bytes; char executable[64],model[64]; uint32_t layout[8]; } native_header;
typedef struct native_type { uint32_t definition_index,name_bytes; uint64_t flags,descriptor_rva,class_pointer,parent,declaring; uint32_t method_count,reserved; uint64_t method_start,name_offset; } native_type;
typedef struct member_header { char magic[8]; uint32_t version,record_bytes,type_count,reserved; uint64_t field_count,property_count,event_count,image_bytes; char executable[64],materializer[64],helper[64]; uint64_t field_rva; uint32_t field_offset,field_stride; uint64_t property_rva; uint32_t property_offset,property_stride; uint64_t event_rva; uint32_t event_offset,event_stride; } member_header;
typedef struct member_record { uint32_t type_index,member_index; uint64_t pointer; uint32_t kind,stride; unsigned char payload[48]; } member_record;
typedef struct output_header { char magic[8]; uint32_t version,header_bytes,record_bytes,reserved; uint64_t record_count,type_count; char executable[64],members[64],semantics[64]; } output_header;
typedef struct output_record { uint32_t type_index,field_index; uint64_t member_pointer,type_descriptor; } output_record;
_Static_assert(sizeof(native_header)==$native_header_bytes,"native header");
_Static_assert(sizeof(native_type)==$native_type_bytes,"native type");
_Static_assert(sizeof(member_header)==$member_header_bytes,"member header");
_Static_assert(sizeof(member_record)==$member_record_bytes,"member record");
_Static_assert(sizeof(output_header)==$output_header_bytes,"output header");
_Static_assert(sizeof(output_record)==$output_record_bytes,"output record");
static const uint32_t selected_indexes[]={$selected_indexes};
static const uint64_t selected_count=$selected_count;
static const uint64_t expected_type_count=$type_count;
static const uint64_t expected_field_count=$field_count;
static const DWORD expected_pid=$process_id;
static const uint32_t descriptor_offset=$descriptor_offset;
static const uintptr_t field_class=$field_class;
static const uintptr_t type_class=$type_class;
static const uintptr_t from_handle_pointer=$from_handle_pointer;
static const uintptr_t from_handle_metadata=$from_handle_metadata;
static const uint32_t field_type_qword=$field_type_qword;
static const uint32_t type_handle_qword=$type_handle_qword;
static const char executable_sha[]="$executable_sha";
static const char member_sha[]="$member_sha";
static const char semantics_sha[]="$semantics_sha";
static const wchar_t native_path[]=$native_path;
static const wchar_t member_path[]=$member_path;
static const wchar_t output_path[]=$output_path;
static const wchar_t status_path[]=$status_path;
typedef uintptr_t(*static_twoarg)(uintptr_t,uintptr_t,uintptr_t);
static unsigned char*native_data,*member_data; static native_type*types; static member_record*members; static output_record*records; static uint64_t cursor,completed,unresolved,failure_index; static uint32_t failure_kind; static UINT message_id; static WNDPROC original_proc; static volatile LONG callback_complete;
static int readable(uintptr_t value,SIZE_T bytes){MEMORY_BASIC_INFORMATION r;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t end=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}
static int object_class(uintptr_t object,uintptr_t expected){uintptr_t observed=0;if(!readable(object,8u))return 0;memcpy(&observed,(const void*)object,8u);return observed==expected;}
static int read_file(const wchar_t*path,unsigned char**data,SIZE_T*bytes){FILE*f=_wfopen(path,L"rb");if(!f||_fseeki64(f,0,SEEK_END))return 0;*bytes=(SIZE_T)_ftelli64(f);if(_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*data=malloc(*bytes?*bytes:1u);int ok=*data&&fread(*data,1,*bytes,f)==*bytes;fclose(f);return ok;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE f=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD os=0,got=0;unsigned char*object=NULL,*buffer=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&got,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,os);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(a,&h,object,os,NULL,0,0)<0)ok=0;while(ok){DWORD n=0;if(!ReadFile(f,buffer,1048576u,&n,NULL)){ok=0;break;}if(!n)break;if(BCryptHashData(h,buffer,n,0)<0)ok=0;}if(ok&&BCryptFinishHash(h,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,output);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(f);return ok;}
static int executable_identity(char output[65]){wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,(DWORD)(sizeof(p)/sizeof(p[0])));return n&&n<sizeof(p)/sizeof(p[0])&&sha256_file(p,output);}
static int capture_batch(void){static_twoarg from_handle=(static_twoarg)from_handle_pointer;uint64_t end=cursor+ALPHA_BATCH;if(end>selected_count)end=selected_count;for(;cursor<end;cursor++){uint32_t field_index=selected_indexes[cursor];if(field_index>=expected_field_count){failure_index=cursor+1u;failure_kind=1u;return 0;}member_record*s=&members[field_index];if(s->kind!=0u||s->type_index>=expected_type_count||!s->pointer){failure_index=cursor+1u;failure_kind=2u;return 0;}uintptr_t object=from_handle(s->pointer,0,from_handle_metadata);if(!object_class(object,field_class)){failure_index=cursor+1u;failure_kind=3u;return 0;}uintptr_t type_object=0,descriptor=0;memcpy(&type_object,(const void*)(object+(uintptr_t)field_type_qword*8u),8u);if(!object_class(type_object,type_class)){failure_index=cursor+1u;failure_kind=4u;return 0;}memcpy(&descriptor,(const void*)(type_object+(uintptr_t)type_handle_qword*8u),8u);if(!readable(descriptor,16u)){failure_index=cursor+1u;failure_kind=5u;return 0;}records[cursor]=(output_record){s->type_index,field_index,s->pointer,descriptor};completed++;}return 1;}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);int ok=capture_batch();InterlockedExchange(&callback_complete,ok?1:-1);return ok;}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;static BOOL CALLBACK select_window(HWND w,LPARAM v){selection*s=(selection*)(uintptr_t)v;DWORD pid=0;RECT b;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){s->window=w;s->count++;}return TRUE;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window)return 0;message_id=RegisterWindowMessageW(status_path);SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);int ok=message_id&&(original_proc||GetLastError()==ERROR_SUCCESS);uint32_t retries=0;while(ok&&cursor<selected_count){DWORD_PTR result=0;InterlockedExchange(&callback_complete,0);int sent=SendMessageTimeoutW(s.window,message_id,0,0,SMTO_BLOCK,60000,&result)!=0;LONG callback=InterlockedCompareExchange(&callback_complete,0,0);if(sent&&callback==1){retries=0;continue;}if(failure_kind||callback==-1){ok=0;break;}if(retries++<2u)continue;uint32_t field_index=selected_indexes[cursor];member_record*source=&members[field_index];records[cursor]=(output_record){source->type_index,field_index,source->pointer,0};cursor++;completed++;unresolved++;retries=0;}if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);return ok;}
static int write_output(void){output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"ALPHAPF1",8);h.version=1;h.header_bytes=sizeof(h);h.record_bytes=sizeof(output_record);h.record_count=selected_count;h.type_count=expected_type_count;memcpy(h.executable,executable_sha,64);memcpy(h.members,member_sha,64);memcpy(h.semantics,semantics_sha,64);FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;int ok=fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(records,sizeof(*records),selected_count,f)==selected_count;if(fclose(f))ok=0;if(!ok)_wremove(output_path);return ok;}
static void write_status(const char*status,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"completed_field_count\": %llu,\n  \"expected_field_count\": %llu,\n  \"unresolved_field_count\": %llu,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"saved_reference_generation_seed_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)completed,(unsigned long long)selected_count,(unsigned long long)unresolved,(unsigned long long)failure_index,failure_kind,written?"true":"false");fclose(f);_wchmod(status_path,0600);}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char e[65],m[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(e)||strcmp(e,executable_sha)||!sha256_file(member_path,m)||strcmp(m,member_sha)){failure_kind=100u;write_status("identity_mismatch",0);return 0;}SIZE_T nb=0,mb=0;if(!read_file(native_path,&native_data,&nb)||!read_file(member_path,&member_data,&mb)){failure_kind=101u;write_status("input_unavailable",0);return 0;}native_header*nh=(native_header*)native_data;member_header*mh=(member_header*)member_data;if(nb<sizeof(*nh)||mb<sizeof(*mh)||memcmp(nh->magic,"ALPHANI1",8)||memcmp(mh->magic,"ALPHANM1",8)||nh->type_count!=expected_type_count||mh->field_count!=expected_field_count){failure_kind=102u;write_status("input_invalid",0);return 0;}types=(native_type*)(native_data+sizeof(*nh));members=(member_record*)(member_data+sizeof(*mh));records=calloc((SIZE_T)selected_count,sizeof(*records));if(!records){failure_kind=103u;write_status("allocation_failed",0);return 0;}int ok=dispatch();if(!ok||completed!=selected_count){if(!failure_kind)failure_kind=104u;write_status("capture_failed",0);return 0;}ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def _source(binding: dict[str, Any], output: Path, status: Path) -> str:
    indexes = ",".join(f"{value}u" for value in binding["field_indexes"])
    return _COLLECTOR.substitute(
        native_header_bytes=_NATIVE_INVENTORY_HEADER.size,
        native_type_bytes=_NATIVE_TYPE_RECORD.size,
        member_header_bytes=struct.calcsize(
            "<8sIIIIQQQQ64s64s64sQIIQIIQII"
        ),
        member_record_bytes=struct.calcsize("<IIQII48s"),
        output_header_bytes=RUNTIME_PROTO_FIELD_TYPE_HEADER.size,
        output_record_bytes=RUNTIME_PROTO_FIELD_TYPE_RECORD.size,
        selected_indexes=indexes,
        selected_count=len(binding["field_indexes"]),
        type_count=binding["type_count"],
        field_count=binding["field_count"],
        process_id=binding["process_id"],
        descriptor_offset=binding["descriptor_offset"],
        field_class=binding["field_class"],
        type_class=binding["type_class"],
        from_handle_pointer=binding["field_from_handle"]["pointer"],
        from_handle_metadata=binding["field_from_handle"]["metadata"],
        field_type_qword=binding["field_type_object_qword"],
        type_handle_qword=binding["type_handle_object_qword"],
        executable_sha=binding["binary"]["sha256"],
        member_sha=binding["native_member_inventory"]["sha256"],
        semantics_sha=binding["reflection_semantics"]["sha256"],
        native_path=_wide_literal(
            _windows_z_path(Path(binding["native_inventory"]["path"]))
        ),
        member_path=_wide_literal(
            _windows_z_path(Path(binding["native_member_inventory"]["path"]))
        ),
        output_path=_wide_literal(_windows_z_path(output)),
        status_path=_wide_literal(_windows_z_path(status)),
        status_schema=RUNTIME_PROTO_FIELD_TYPE_STATUS_SCHEMA,
    )


def prepare_runtime_proto_field_types(
    *, native_output_receipt: Path, output_dir: Path, compiler: Path | None = None
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(native_output_receipt)
    observed = output_dir / "runtime-proto-field-types-observed.private.bin"
    output = output_dir / "runtime-proto-field-types.private.bin"
    status = output_dir / "runtime-proto-field-types-status.private.json"
    model = output_dir / "runtime-proto-field-types.private.json"
    plan_path = output_dir / "runtime-proto-field-types-plan.private.json"
    for stale in (observed, output, status, model):
        stale.unlink(missing_ok=True)
    build = _owner_directory(output_dir / "build-runtime-proto-field-types")
    source = build / "runtime-proto-field-types.c"
    injector_source = build / "runtime-proto-field-types-injector.c"
    _private_text(source, _source(binding, observed, status))
    _private_text(injector_source, runtime_injector_source())
    collector = build / (
        "alpha-runtime-proto-field-types-"
        + file_identity(source)["sha256"][:12]
        + ".dll"
    )
    injector = build / "alpha-runtime-proto-field-types-injector.exe"
    cc = _compiler(compiler)
    _build(
        [
            str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(source), "-o", str(collector),
            "-lbcrypt",
        ],
        label="runtime proto field type collector",
    )
    _build(
        [
            str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(injector_source), "-o",
            str(injector),
        ],
        label="runtime proto field type injector",
    )
    for artifact in (collector, injector):
        artifact.chmod(0o600)
    private_binding = dict(binding)
    private_binding["message_type_indexes_owner_only"] = private_binding.pop(
        "message_type_indexes"
    )
    private_binding["field_indexes_owner_only"] = private_binding.pop(
        "field_indexes"
    )
    plan = {
        "schema": RUNTIME_PROTO_FIELD_TYPE_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": binding["binary"]["path"],
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
        },
        "binding": private_binding,
        "collector": file_identity(collector),
        "injector": file_identity(injector),
        "observed_output_path": str(observed),
        "output_path": str(output),
        "status_path": str(status),
        "model_path": str(model),
        "counts": {
            "message_type_count": len(binding["message_type_indexes"]),
            "field_count": len(binding["field_indexes"]),
        },
        "policy": {
            "dominant_base_runtime_derived": True,
            "saved_reference_generation_seed_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
            "raw_pointers_owner_only": True,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_PROTO_FIELD_TYPE_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "counts": plan["counts"],
        "policy": plan["policy"],
    }


def _resolve_unobserved_field_types(
    plan: dict[str, Any], status: dict[str, Any]
) -> dict[str, Any]:

    observed_path = Path(plan["observed_output_path"])
    observed = observed_path.read_bytes()
    count = plan["counts"]["field_count"]
    expected_bytes = (
        RUNTIME_PROTO_FIELD_TYPE_HEADER.size
        + count * RUNTIME_PROTO_FIELD_TYPE_RECORD.size
    )
    if len(observed) != expected_bytes:
        raise AcquisitionError("runtime proto observed field types are truncated")
    member_path = Path(plan["binding"]["native_member_inventory"]["path"])
    members = member_path.read_bytes()
    member_header = _NATIVE_MEMBER_HEADER.unpack_from(members)
    if (
        member_header[0] != _NATIVE_MEMBER_MAGIC
        or member_header[1] != _NATIVE_MEMBER_VERSION
        or member_header[2] != _NATIVE_MEMBER_RECORD.size
        or member_header[5] != plan["binding"]["field_count"]
    ):
        raise AcquisitionError("runtime proto native field payloads are invalid")

    records: list[list[int]] = []
    payloads: list[tuple[int, ...]] = []
    directly_observed = 0
    for index in range(count):
        record = list(
            RUNTIME_PROTO_FIELD_TYPE_RECORD.unpack_from(
                observed,
                RUNTIME_PROTO_FIELD_TYPE_HEADER.size
                + index * RUNTIME_PROTO_FIELD_TYPE_RECORD.size,
            )
        )
        field_index = record[1]
        if field_index != plan["binding"]["field_indexes_owner_only"][index]:
            raise AcquisitionError("runtime proto observed field order differs")
        member = _NATIVE_MEMBER_RECORD.unpack_from(
            members,
            _NATIVE_MEMBER_HEADER.size
            + field_index * _NATIVE_MEMBER_RECORD.size,
        )
        if member[2] != record[2] or member[3] != 0:
            raise AcquisitionError("runtime proto observed field identity differs")
        records.append(record)
        payloads.append(struct.unpack("<6Q", member[5]))
        directly_observed += bool(record[3])

    image_base = plan["binding"]["image_base"]
    image_end = image_base + plan["binding"]["image_bytes"]
    unresolved_before = count - directly_observed
    codec: dict[str, Any] | None = None
    if unresolved_before:
        candidates: list[dict[str, Any]] = []
        for qword in range(6):
            mapping: dict[int, int] = {}
            conflicts = 0
            repeated_support = 0
            deltas: Counter[int] = Counter()
            for record, payload in zip(records, payloads):
                descriptor = record[3]
                if not descriptor:
                    continue
                encoded = payload[qword]
                previous = mapping.get(encoded)
                if previous is None:
                    mapping[encoded] = descriptor
                elif previous == descriptor:
                    repeated_support += 1
                else:
                    conflicts += 1
                if image_base <= descriptor < image_end and not descriptor & 0xF:
                    deltas[(encoded - descriptor) & ((1 << 64) - 1)] += 1
            dominant = deltas.most_common(2)
            if (
                conflicts == 0
                and len(mapping) >= 64
                and repeated_support >= 128
                and len(dominant) == 1
                and dominant[0][1] >= 128
            ):
                candidates.append(
                    {
                        "qword": qword,
                        "mapping": mapping,
                        "delta": dominant[0][0],
                        "affine_support": dominant[0][1],
                        "repeat_support": repeated_support,
                        "distinct_encoding_count": len(mapping),
                    }
                )
        if len(candidates) != 1:
            raise AcquisitionError(
                "runtime proto native field type encoding is ambiguous"
            )
        codec = candidates[0]

    mapped_count = 0
    affine_count = 0
    derived_names: set[str] = set()
    if codec is not None:
        values = load_runtime_metadata_usage_value_inventory(
            model_path=Path(
                plan["binding"]["metadata_usage_value_model"]["path"]
            ),
            inventory_path=Path(
                plan["binding"]["metadata_usage_value_inventory"]["path"]
            ),
            expected_executable_sha256=plan["target"]["executable_sha256"],
            expected_metadata_usage_pair_inventory_sha256=plan["binding"]
            ["metadata_usage_pair_inventory"]["sha256"],
        )
        runtime_receipt = Path(plan["binding"]["receipt"]["path"])
        _receipt, native_paths = _validated_native_receipt(
            runtime_receipt, allow_type_method_metadata=True
        )
        runtime = _RuntimeOutput(
            binary=native_paths["binary"],
            type_identity=native_paths["type_identity_inventory"].read_bytes(),
            type_graph=native_paths["type_graph_inventory"].read_bytes(),
            type_references=native_paths["type_reference_inventory"].read_bytes(),
            methods=native_paths["method_detail_inventory"].read_bytes(),
            native_members=native_paths["native_member_detail_inventory"].read_bytes(),
            event_modules=native_paths["event_module_inventory"].read_bytes(),
            method_generics=native_paths["method_generic_inventory"].read_bytes(),
            generic_parameter_details=native_paths[
                "generic_parameter_detail_inventory"
            ].read_bytes(),
        )
        with _MetadataUsageTypeRenderer(
            binary=native_paths["binary"],
            renderer=runtime.renderer,
            generic_records=values["generic_records_owner_only"],
        ) as renderer:
            for index, (record, payload) in enumerate(zip(records, payloads)):
                if record[3]:
                    continue
                encoded = payload[codec["qword"]]
                descriptor = codec["mapping"].get(encoded)
                if descriptor is not None:
                    mapped_count += 1
                else:
                    descriptor = (encoded - codec["delta"]) & ((1 << 64) - 1)
                    if (
                        not image_base <= descriptor < image_end
                        or descriptor & 0xF
                    ):
                        raise AcquisitionError(
                            "runtime proto derived field type is outside the image"
                        )
                    try:
                        data, bits = renderer._type_record(descriptor)
                        derived_names.add(renderer.render(descriptor, data, bits))
                    except Exception as error:
                        raise AcquisitionError(
                            "runtime proto derived field type is not a PE type record"
                        ) from error
                    affine_count += 1
                record[3] = descriptor

    if (
        mapped_count + affine_count != unresolved_before
        or status.get("unresolved_field_count") != unresolved_before
        or any(not record[3] for record in records)
    ):
        raise AcquisitionError(
            "runtime proto field type resolution does not close the capture"
        )
    final = bytearray(observed[:RUNTIME_PROTO_FIELD_TYPE_HEADER.size])
    for record in records:
        final.extend(RUNTIME_PROTO_FIELD_TYPE_RECORD.pack(*record))
    _private_bytes(Path(plan["output_path"]), bytes(final))
    resolution = {
        "direct_runtime_descriptor_count": directly_observed,
        "native_encoding_exact_match_count": mapped_count,
        "native_encoding_affine_match_count": affine_count,
        "unresolved_before_native_encoding_resolution": unresolved_before,
        "native_encoding_codec_needed": codec is not None,
        "fresh_capture_derived": True,
        "fixed_codec_used": False,
    }
    if codec is not None:
        resolution.update(
            {
                "field_type_payload_qword_owner_only": codec["qword"],
                "affine_delta_owner_only": codec["delta"],
                "affine_observation_support": codec["affine_support"],
                "repeated_encoding_observation_support": codec["repeat_support"],
                "distinct_encoding_observation_count": codec[
                    "distinct_encoding_count"
                ],
                "affine_derived_type_name_count": len(derived_names),
            }
        )
    return resolution


def _validate(
    plan: dict[str, Any], status: dict[str, Any], resolution: dict[str, Any]
) -> tuple[dict[str, int], dict[str, bool]]:
    raw = Path(plan["output_path"]).read_bytes()
    count = plan["counts"]["field_count"]
    header = RUNTIME_PROTO_FIELD_TYPE_HEADER.unpack_from(raw)
    records_end = RUNTIME_PROTO_FIELD_TYPE_HEADER.size + count * RUNTIME_PROTO_FIELD_TYPE_RECORD.size
    header_ok = (
        len(raw) == records_end
        and header[0] == RUNTIME_PROTO_FIELD_TYPE_MAGIC
        and header[1] == RUNTIME_PROTO_FIELD_TYPE_VERSION
        and header[2] == RUNTIME_PROTO_FIELD_TYPE_HEADER.size
        and header[3] == RUNTIME_PROTO_FIELD_TYPE_RECORD.size
        and header[4] == 0
        and header[5] == count
        and header[6] == plan["binding"]["type_count"]
        and header[7].decode("ascii") == plan["target"]["executable_sha256"]
        and header[8].decode("ascii")
        == plan["binding"]["native_member_inventory"]["sha256"]
        and header[9].decode("ascii")
        == plan["binding"]["reflection_semantics"]["sha256"]
    )
    expected = plan["binding"]["field_indexes_owner_only"]
    owner_matches = 0
    detail_matches = 0
    descriptors: set[int] = set()
    unresolved_descriptors = 0
    rows_ok = header_ok
    image_base = plan["binding"]["image_base"]
    native = Path(plan["binding"]["native_inventory"]["path"]).read_bytes()
    old_native = Path(
        plan["binding"]["native_member_detail_inventory"]["path"]
    ).read_bytes()
    for index in range(count):
        type_index, field_index, pointer, descriptor = RUNTIME_PROTO_FIELD_TYPE_RECORD.unpack_from(
            raw, RUNTIME_PROTO_FIELD_TYPE_HEADER.size + index * RUNTIME_PROTO_FIELD_TYPE_RECORD.size
        )
        old = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            old_native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + field_index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        if field_index != expected[index] or type_index != old[0] or pointer != old[2]:
            rows_ok = False
            break
        if descriptor:
            owner_rva = _NATIVE_TYPE_RECORD.unpack_from(
                native,
                _NATIVE_INVENTORY_HEADER.size
                + type_index * _NATIVE_TYPE_RECORD.size,
            )[3]
            owner_matches += descriptor == image_base + owner_rva
            detail_matches += descriptor == old[3]
            descriptors.add(descriptor)
        else:
            unresolved_descriptors += 1
    counts = {
        "message_type_count": plan["counts"]["message_type_count"],
        "field_count": count,
        "distinct_field_type_descriptor_count": len(descriptors),
        "owner_descriptor_match_count": owner_matches,
        "native_detail_descriptor_match_count": detail_matches,
        "unresolved_field_type_descriptor_count": unresolved_descriptors,
        "direct_runtime_descriptor_count": resolution[
            "direct_runtime_descriptor_count"
        ],
        "native_encoding_resolved_descriptor_count": (
            resolution["native_encoding_exact_match_count"]
            + resolution["native_encoding_affine_match_count"]
        ),
    }
    checks = {
        "status_schema": status.get("schema") == RUNTIME_PROTO_FIELD_TYPE_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "all_fields_captured": status.get("completed_field_count") == count,
        "all_field_type_descriptors_resolved": (
            unresolved_descriptors == 0
        ),
        "raw_unresolved_fields_accounted": status.get(
            "unresolved_field_count"
        )
        == resolution["unresolved_before_native_encoding_resolution"],
        "native_encoding_codec_accounted": (
            resolution["unresolved_before_native_encoding_resolution"] == 0
        )
        == (resolution.get("native_encoding_codec_needed") is False),
        "header_bound": header_ok,
        "rows_match_current_field_domain": rows_ok,
        "field_types_not_collapsed_to_owner_types": (
            owner_matches < count - unresolved_descriptors
        ),
        "field_type_domain_nontrivial": len(descriptors) >= 64,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_reference_generation_seed_absent": status.get("saved_reference_generation_seed_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get("external_runtime_component_used") is False,
        "fresh_native_encoding_derivation": resolution.get(
            "fresh_capture_derived"
        )
        is True,
        "fixed_native_encoding_absent": resolution.get("fixed_codec_used")
        is False,
    }
    return counts, checks


_PLAN_BOUND_IDENTITY_KEYS = frozenset({"path", "bytes", "sha256"})


def _plan_bound_identities(plan: dict[str, Any]) -> list[dict[str, Any]]:

    found: list[dict[str, Any]] = []

    def walk(node: Any) -> None:
        if isinstance(node, dict):
            if set(node) == _PLAN_BOUND_IDENTITY_KEYS and all(
                isinstance(node[key], str if key != "bytes" else int)
                for key in _PLAN_BOUND_IDENTITY_KEYS
            ):
                found.append(node)
                return
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for value in node:
                walk(value)

    walk(plan)
    return found


def _validate_prepared_plan(plan: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(plan, dict) or plan.get("schema") != RUNTIME_PROTO_FIELD_TYPE_PLAN_SCHEMA:
        raise AcquisitionError("runtime proto field type plan schema is invalid")
    if plan.get("status") != "prepared":
        raise AcquisitionError("runtime proto field type plan is not prepared")
    binding = plan.get("binding")
    counts = plan.get("counts")
    target = plan.get("target")
    if not isinstance(binding, dict) or not isinstance(counts, dict) or not isinstance(target, dict):
        raise AcquisitionError("runtime proto field type plan is incomplete")
    if (
        not isinstance(counts.get("field_count"), int)
        or counts["field_count"] <= 0
        or not isinstance(binding.get("field_indexes_owner_only"), list)
        or len(binding["field_indexes_owner_only"]) != counts["field_count"]
        or not isinstance(binding.get("field_count"), int)
        or binding["field_count"] < counts["field_count"]
        or not isinstance(binding.get("type_count"), int)
        or binding["type_count"] <= 0
    ):
        raise AcquisitionError("runtime proto field type plan counts are inconsistent")
    for key in ("observed_output_path", "output_path", "status_path", "model_path"):
        if not isinstance(plan.get(key), str):
            raise AcquisitionError(
                f"runtime proto field type plan output path is unavailable: {key}"
            )
    executable = Path(target.get("executable_path", ""))
    if (
        not target.get("executable_sha256")
        or not isinstance(target["executable_sha256"], str)
    ):
        raise AcquisitionError("runtime proto field type plan target is unbound")
    if not executable.is_file():
        raise AcquisitionError("runtime proto field type target executable is missing")
    if file_identity(executable)["sha256"] != target["executable_sha256"]:
        raise AcquisitionError("runtime proto field type target executable changed")
    for identity in _plan_bound_identities(plan):
        path = Path(identity["path"])
        if not path.is_file() or file_identity(path) != identity:
            raise AcquisitionError(
                f"runtime proto field type plan input is stale: {identity['path']}"
            )
    return plan


def _validate_captured_status(
    status: dict[str, Any], plan: dict[str, Any]
) -> dict[str, Any]:
    if not isinstance(status, dict) or status.get("schema") != RUNTIME_PROTO_FIELD_TYPE_STATUS_SCHEMA:
        raise AcquisitionError("runtime proto field type status schema is invalid")
    count = plan["counts"]["field_count"]
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime proto field type capture did not complete: "
            f"{status.get('status')}"
        )
    if (
        status.get("completed_field_count") != count
        or status.get("expected_field_count") != count
    ):
        raise AcquisitionError("runtime proto field type status counts are stale")
    for key in (
        "output_written",
        "fresh_runtime_observation",
    ):
        if status.get(key) is not True:
            raise AcquisitionError(
                f"runtime proto field type capture did not record {key}"
            )
    for key in (
        "saved_reference_generation_seed_used",
        "fixed_address_used",
        "fixed_offset_used",
        "external_runtime_component_used",
    ):
        if status.get(key) is not False:
            raise AcquisitionError(
                f"runtime proto field type capture recorded a forbidden policy: {key}"
            )
    return status


def resume_runtime_proto_field_types(*, output_dir: Path) -> dict[str, Any]:

    output_dir = _owner_directory(output_dir)
    plan_path = output_dir / "runtime-proto-field-types-plan.private.json"
    if not plan_path.is_file():
        raise AcquisitionError("runtime proto field type plan is unavailable")
    plan = _validate_prepared_plan(read_json(plan_path))
    observed_path = Path(plan["observed_output_path"])
    _owner_file(observed_path, label="observed field types")
    count = plan["counts"]["field_count"]
    expected_bytes = (
        RUNTIME_PROTO_FIELD_TYPE_HEADER.size
        + count * RUNTIME_PROTO_FIELD_TYPE_RECORD.size
    )
    if observed_path.stat().st_size != expected_bytes:
        raise AcquisitionError("runtime proto observed field types are truncated")
    status_path = Path(plan["status_path"])
    if not status_path.is_file():
        raise AcquisitionError("runtime proto field type status is unavailable")
    _owner_file(status_path, label="field type status")
    status = _validate_captured_status(read_json(status_path), plan)
    return _finalize_runtime_proto_field_types(plan, status)


def _finalize_runtime_proto_field_types(
    plan: dict[str, Any], status: dict[str, Any]
) -> dict[str, Any]:
    observed_output_path = Path(plan["observed_output_path"])
    _seal_runtime_output(observed_output_path)
    _seal_runtime_output(Path(plan["status_path"]))
    resolution = _resolve_unobserved_field_types(plan, status)
    output_path = Path(plan["output_path"])
    _seal_runtime_output(output_path)
    counts, checks = _validate(plan, status, resolution)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime proto field type validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    model = {
        "schema": RUNTIME_PROTO_FIELD_TYPE_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": {
            "native_output_receipt": plan["binding"]["receipt"],
            "native_member_inventory": plan["binding"]["native_member_inventory"],
            "reflection_semantics": plan["binding"]["reflection_semantics"],
            "observed_field_type_inventory": file_identity(
                observed_output_path
            ),
            "metadata_usage_value_inventory": plan["binding"]
            ["metadata_usage_value_inventory"],
        },
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(Path(plan["status_path"])),
        "resolution": resolution,
        "counts": counts,
        "checks": checks,
        "owner_only": True,
    }
    _private_json(Path(plan["model_path"]), model)
    return model


def capture_runtime_proto_field_types(
    *, native_output_receipt: Path, output_dir: Path, wine: Path,
    wineprefix: Path, compiler: Path | None = None, timeout: float = 600.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_proto_field_types(
        native_output_receipt=native_output_receipt,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-proto-field-types-plan.private.json"
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
        raise AcquisitionError("runtime proto field type injector could not run") from error
    _private_text(
        output_dir / "runtime-proto-field-types-injector.private.log",
        json.dumps(
            {"returncode": injected.returncode, "stdout": injected.stdout, "stderr": injected.stderr},
            ensure_ascii=False,
            indent=2,
        )
        + "\n",
    )
    if injected.returncode:
        raise AcquisitionError("runtime proto field type injection failed")
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
        raise AcquisitionError("runtime proto field type capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime proto field type capture failed "
            f"(index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    return _finalize_runtime_proto_field_types(plan, status)
