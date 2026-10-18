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

from alpha.p12 import _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import (
    AcquisitionError,
    owner_only_path_bits,
    owner_uid,
    same_executable_path,
)
from alpha.p23 import _binding as _member_binding
from alpha.p19 import _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p17 import _NATIVE_INVENTORY_HEADER, _NATIVE_INVENTORY_MAGIC, _NATIVE_INVENTORY_VERSION, _NATIVE_MEMBER_HEADER, _NATIVE_MEMBER_RECORD, _NATIVE_METHOD_RECORD, _NATIVE_TYPE_RECORD
from alpha.h02 import file_identity, read_json
from alpha.c01 import current_runtime_process_binding
from alpha.c04 import RuntimeProcessLifetimeGuard
from alpha.p14 import read_runtime_progress
from alpha.p18 import load_runtime_string_layout_candidate
from alpha.p14 import event_string_reader_source, validate_event_string_io


RUNTIME_EVENT_MODULE_PLAN_SCHEMA = "alpha.runtime-event-module-plan/v1"
RUNTIME_EVENT_MODULE_STATUS_SCHEMA = "alpha.runtime-event-module-status/v1"
RUNTIME_EVENT_MODULE_SCHEMA = "alpha.runtime-event-module-inventory/v1"
RUNTIME_EVENT_MODULE_MAGIC = b"ALPHAEM1"
RUNTIME_EVENT_MODULE_VERSION = 1
RUNTIME_EVENT_MODULE_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQ64s64s64s64s"
)
RUNTIME_EVENT_MODULE_MODULE = struct.Struct("<QIIQ")
RUNTIME_EVENT_MODULE_EVENT = struct.Struct("<IIQQQQIIIIQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime event module {label} is not owner-only"
        )
    return path


def _binding(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    native_semantics_model: Path,
    native_inventory: Path,
    native_member_inventory: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    runtime_inventory_dispatch: Path | None,
    string_layout_model: Path | None = None,
) -> dict[str, Any]:
    current = current_runtime_process_binding()
    if current is None or string_layout_model is None:
        raise AcquisitionError("event/module capture requires an explicit current String layout model")
    binding = _member_binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        native_semantics_model=native_semantics_model,
        native_inventory=native_inventory,
        native_member_inventory=native_member_inventory,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
    )
    semantics = read_json(_owner_file(
        reflection_semantics_model, label="reflection semantics"
    ))
    native_semantics = read_json(_owner_file(
        native_semantics_model, label="native semantics"
    ))
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
    }
    required = (
        "type.events",
        "event.name",
        "event.handler_type",
        "event.add_method",
        "event.remove_method",
        "event.raise_method",
        "member.metadata_token",
    )
    if set(required) - set(operations) or any(
        operations[key].get("semantic_identity_resolved") is not True
        or not isinstance(operations[key].get("method_pointer"), int)
        or operations[key]["method_pointer"] <= 0
        or not isinstance(operations[key].get("metadata_pointer"), int)
        or operations[key]["metadata_pointer"] <= 0
        for key in required
    ):
        raise AcquisitionError(
            "runtime event module operations are unavailable"
        )
    accessors = native_semantics.get("accessor_codecs", {}).get("event")
    if (
        not isinstance(accessors, list)
        or len(accessors) != 2
        or any(
            row.get("operation") not in {"xor", "add", "subtract"}
            for row in accessors
        )
        or any(
            not isinstance(row.get(key), int)
            for row in accessors
            for key in ("slot", "key")
        )
    ):
        raise AcquisitionError(
            "runtime event module accessor codecs are invalid"
        )
    type_model_path = _owner_file(
        type_identity_model, label="type identity model"
    )
    type_plan_path = _owner_file(
        type_model_path.parent / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    type_status_path = _owner_file(
        type_model_path.parent / "runtime-type-identity-status.private.json",
        label="type identity status",
    )
    type_plan = read_json(type_plan_path)
    type_status = read_json(type_status_path)
    classes = type_plan.get("runtime_classes_owner_only", {})
    handle_qword = type_status.get("runtime_type_handle_qword_owner_only")
    class_model = read_json(Path(binding["class_model"]["path"]))
    event_class = next(
        (
            row.get("class_pointer")
            for row in class_model.get("classes", [])
            if isinstance(row, dict)
            and row.get("runtime_owner") == "System.Reflection.MonoEvent"
        ),
        None,
    )
    if (
        not isinstance(classes.get("runtime_type"), int)
        or classes["runtime_type"] <= 0
        or not isinstance(classes.get("string"), int)
        or classes["string"] <= 0
        or not isinstance(event_class, int)
        or event_class <= 0
        or not isinstance(handle_qword, int)
        or not 2 <= handle_qword < 16
    ):
        raise AcquisitionError(
            "runtime event module class binding is unavailable"
        )
    event_info_fill = binding["attribute_semantics"]["operations"][
        "event.info_fill"
    ]
    if (
        event_info_fill.get("semantic_identity_resolved") is not True
        or not isinstance(event_info_fill.get("method_pointer"), int)
        or not binding["image_base"] <= event_info_fill["method_pointer"]
        < binding["image_base"] + binding["image_bytes"]
        or not isinstance(event_info_fill.get("metadata_pointer"), int)
        or event_info_fill["metadata_pointer"] <= 0
    ):
        raise AcquisitionError(
            "runtime event module event info binding is invalid"
        )
    identity_path = _owner_file(
        type_identity_inventory, label="type identity inventory"
    )
    raw = identity_path.read_bytes()
    if len(raw) < _IDENTITY_HEADER.size:
        raise AcquisitionError(
            "runtime event module type identity is truncated"
        )
    header = _IDENTITY_HEADER.unpack_from(raw)
    if (
        header[0] != _IDENTITY_MAGIC
        or header[1] != _IDENTITY_VERSION
        or header[2] != _IDENTITY_HEADER.size
        or header[3] != _IDENTITY_RECORD.size
        or header[5] != binding["type_count"]
        or header[6] != binding["image_base"]
        or header[7] != binding["image_bytes"]
    ):
        raise AcquisitionError(
            "runtime event module type identity binding is invalid"
        )
    from alpha.c04 import _verify_files
    layout_path = _owner_file(string_layout_model, label="String layout model")
    layout_record = file_identity(layout_path)
    layout = load_runtime_string_layout_candidate(model_path=layout_path,
        expected_identity={"executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"], "process_id": current[0],
            "creation_filetime": current[1], "image_base": binding["image_base"], "image_bytes": binding["image_bytes"]},
        expected_inputs={"snapshot": binding["runtime_snapshot"], "native_inventory": binding["native_inventory"]})
    if layout["class_pointer"] != classes["string"]:
        raise AcquisitionError("event/module String class differs from current type source")
    _verify_files({"layout": layout_record})
    return {
        **binding,
        "string_layout_contract": layout, "string_layout_model": layout_record,
        "type_identity_status": file_identity(type_status_path),
        "runtime_type_class": classes["runtime_type"],
        "string_class": classes["string"],
        "event_class": event_class,
        "handle_qword": handle_qword,
        "operations": {
            key: {
                "pointer": operations[key]["method_pointer"],
                "metadata": operations[key]["metadata_pointer"],
            }
            for key in required
        },
        "event_add": accessors[0],
        "event_remove": accessors[1],
        "event_info_fill": {
            "pointer": event_info_fill["method_pointer"],
            "metadata": event_info_fill["metadata_pointer"],
        },
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <io.h>
#include <fcntl.h>
#include <sys/stat.h>

#define ALPHA_MAX_TEXT 16384u
#define ALPHA_MAX_MANAGED_TEXT ALPHA_MAX_TEXT
#define ALPHA_BINDING_FLAGS 0x3eu

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
typedef struct member_header {
    char magic[8]; uint32_t version, record_bytes, type_count, reserved;
    uint64_t field_count, property_count, event_count, image_bytes;
    char executable_sha256[64], materializer_sha256[64], helper_sha256[64];
    uint64_t field_rva; uint32_t field_offset, field_stride;
    uint64_t property_rva; uint32_t property_offset, property_stride;
    uint64_t event_rva; uint32_t event_offset, event_stride;
} member_header;
typedef struct member_record {
    uint32_t type_index, member_index; uint64_t pointer;
    uint32_t kind, stride; unsigned char payload[48];
} member_record;
typedef struct native_header {
    char magic[8]; uint32_t version, type_record_bytes, method_record_bytes, reserved;
    uint64_t type_count, method_count, image_bytes;
    char executable_sha256[64], materializer_sha256[64];
    uint32_t descriptor_offset, class_name_qword, parent_class_qword,
        class_declaring_qword, method_array_qword, method_count_offset,
        method_declaring_qword, method_pointer_qword;
} native_header;
typedef struct native_type {
    uint32_t definition_index, name_bytes; uint64_t type_flags, descriptor_rva,
        class_pointer, parent_pointer, declaring_pointer; uint32_t method_count,
        reserved; uint64_t method_start, name_offset;
} native_type;
typedef struct native_method {
    uint32_t definition_index, method_index;
    uint64_t metadata_pointer, method_pointer;
} native_method;
typedef struct output_header {
    char magic[8]; uint32_t version, header_bytes, module_record_bytes, event_record_bytes;
    uint64_t module_count, event_count, string_bytes, image_base, image_bytes;
    uint64_t type_count, reserved;
    char executable_sha256[64], identity_sha256[64], member_sha256[64], semantics_sha256[64];
} output_header;
typedef struct output_module {
    uint64_t module_pointer; uint32_t name_bytes, reserved; uint64_t name_offset;
} output_module;
typedef struct output_event {
    uint32_t type_index, member_index;
    uint64_t member_pointer, handler_descriptor, add_pointer, remove_pointer;
    uint32_t metadata_token, name_bytes, flags, reserved; uint64_t name_offset;
} output_event;

_Static_assert(sizeof(identity_header) == $identity_header_bytes, "identity header");
_Static_assert(sizeof(identity_record) == $identity_record_bytes, "identity record");
_Static_assert(sizeof(member_header) == $member_header_bytes, "member header");
_Static_assert(sizeof(member_record) == $member_record_bytes, "member record");
_Static_assert(sizeof(native_header) == $native_header_bytes, "native header");
_Static_assert(sizeof(native_type) == $native_type_bytes, "native type");
_Static_assert(sizeof(native_method) == $native_method_bytes, "native method");
_Static_assert(sizeof(output_header) == $output_header_bytes, "output header");
_Static_assert(sizeof(output_module) == $output_module_bytes, "output module");
_Static_assert(sizeof(output_event) == $output_event_bytes, "output event");

static const char executable_sha256[] = "$executable_sha256";
static const char identity_sha256[] = "$identity_sha256";
static const char member_sha256[] = "$member_sha256";
static const char native_sha256[] = "$native_sha256";
static const char semantics_sha256[] = "$semantics_sha256";
static const DWORD expected_pid = ${process_id}u;
static const uintptr_t expected_image_base = ${image_base}ull;
static const uint64_t expected_image_bytes = ${image_bytes}ull;
static const uint64_t expected_type_count = ${type_count}ull;
static const uint64_t expected_module_count = ${module_count}ull;
static const uint64_t expected_field_count = ${field_count}ull;
static const uint64_t expected_property_count = ${property_count}ull;
static const uint64_t expected_event_count = ${event_count}ull;
static const uint64_t expected_method_count = ${method_count}ull;
static const uint32_t expected_metadata_token_rid_base =
    ${metadata_token_rid_base}u;
static const uintptr_t runtime_type_class = ${runtime_type_class}ull;
static const uintptr_t event_class = ${event_class}ull;
static const uintptr_t method_class = ${method_class}ull;
static const uint32_t handle_qword = ${handle_qword}u;
static const uintptr_t type_events_pointer = ${type_events_pointer}ull;
static const uintptr_t type_events_metadata = ${type_events_metadata}ull;
static const uintptr_t event_name_pointer = ${event_name_pointer}ull;
static const uintptr_t event_name_metadata = ${event_name_metadata}ull;
static const uintptr_t event_handler_pointer = ${event_handler_pointer}ull;
static const uintptr_t event_handler_metadata = ${event_handler_metadata}ull;
static const uintptr_t event_add_method_pointer = ${event_add_method_pointer}ull;
static const uintptr_t event_add_method_metadata = ${event_add_method_metadata}ull;
static const uintptr_t event_remove_method_pointer = ${event_remove_method_pointer}ull;
static const uintptr_t event_remove_method_metadata = ${event_remove_method_metadata}ull;
static const uintptr_t event_raise_method_pointer = ${event_raise_method_pointer}ull;
static const uintptr_t event_raise_method_metadata = ${event_raise_method_metadata}ull;
static const uintptr_t event_info_fill_pointer = ${event_info_fill_pointer}ull;
static const uintptr_t event_info_fill_metadata = ${event_info_fill_metadata}ull;
static const uintptr_t metadata_token_pointer = ${metadata_token_pointer}ull;
static const uintptr_t metadata_token_metadata = ${metadata_token_metadata}ull;
static const uint32_t accessor0_slot = ${accessor0_slot}u;
static const uint64_t accessor0_key = ${accessor0_key}ull;
static const uint32_t accessor0_operation = ${accessor0_operation}u;
static const uint32_t accessor1_slot = ${accessor1_slot}u;
static const uint64_t accessor1_key = ${accessor1_key}ull;
static const uint32_t accessor1_operation = ${accessor1_operation}u;
static const wchar_t identity_path[] = $identity_path;
static const wchar_t member_path[] = $member_path;
static const wchar_t native_path[] = $native_path;
static const wchar_t output_path[] = $output_path;
static const wchar_t status_path[] = $status_path;

typedef uintptr_t (*instance_flags)(uintptr_t, uintptr_t, uintptr_t);
typedef uintptr_t (*instance_noarg)(uintptr_t, uintptr_t);
typedef uintptr_t (*instance_boolarg)(uintptr_t, uint32_t, uintptr_t);
typedef uint32_t (*instance_dword)(uintptr_t, uintptr_t);
typedef void (*event_info_fill_fn)(uintptr_t, uintptr_t *, uintptr_t);
static unsigned char *identity_data, *member_data, *native_data;
static identity_record *types;
static member_record *events;
static native_method *native_methods;
static output_module *modules;
static output_event *output_events;
static uint64_t module_count, event_cursor, completed_events;
static uint64_t synthetic_events, string_bytes, string_capacity;
static char *strings;
static uint32_t array_length_qword, array_vector_qword, module_name_qword;
static uint32_t event_info_name_qword = UINT32_MAX;
static uint32_t event_info_flags_offset = UINT32_MAX;
static uint64_t failure_index; static uint32_t failure_kind;
static uint32_t previous_event_rid;
static uint64_t direct_accessor_permutation_count;
static uint64_t crossed_accessor_permutation_count;
static uint32_t add_codec_index = UINT32_MAX, remove_codec_index = UINT32_MAX;
static UINT message_id; static WNDPROC original_proc;
static volatile LONG callback_complete;

static int readable(uintptr_t value, SIZE_T bytes) {
    MEMORY_BASIC_INFORMATION region;
    if (!value || !bytes || value + bytes < value ||
        !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD) return 0;
    DWORD protect = region.Protect & 0xffu;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    return protect && protect != PAGE_NOACCESS && end >= value && value + bytes <= end;
}
static int object_class(uintptr_t object, uintptr_t expected) {
    uintptr_t observed = 0; if (!readable(object, sizeof(observed))) return 0;
    memcpy(&observed, (const void *)object, sizeof(observed)); return observed == expected;
}
static uintptr_t method_pointer_from_object(uintptr_t object) {
    if (!object || !readable(object, 8u)) return 0;
    instance_dword get_token = (instance_dword)metadata_token_pointer;
    uint32_t token = get_token(object, metadata_token_metadata);
    uint32_t rid = token & 0x00ffffffu;
    if ((token & 0xff000000u) != 0x06000000u ||
        rid < expected_metadata_token_rid_base ||
        (uint64_t)(rid - expected_metadata_token_rid_base) >=
            expected_method_count) return 0;
    native_method *method = &native_methods[
        rid - expected_metadata_token_rid_base];
    return method->metadata_pointer;
}
$derived_string_reader
static int managed_string_equal(uintptr_t left, uintptr_t right) {
    char *a = NULL, *b = NULL; uint32_t an = 0, bn = 0;
    int same = managed_utf8(left, &a, &an) && managed_utf8(right, &b, &bn) &&
        an == bn && (!an || !memcmp(a, b, an));
    free(a); free(b); return same;
}
static int method_object_equal(uintptr_t left, uintptr_t right) {
    if (!left || !right) return left == right;
    if (!readable(left, 8u) || !readable(right, 8u)) return 0;
    uintptr_t a = 0, b = 0;
    memcpy(&a, (const void *)left, 8u);
    memcpy(&b, (const void *)right, 8u);
    if (a != b) return 0;
    uintptr_t lm = method_pointer_from_object(left);
    return lm && lm == method_pointer_from_object(right);
}
static int append_text(const char *value, uint32_t bytes, uint64_t *offset) {
    if (!value || !bytes || string_bytes + bytes < string_bytes) return 0;
    uint64_t required = string_bytes + bytes;
    if (required > string_capacity) {
        uint64_t capacity = string_capacity ? string_capacity : 65536u;
        while (capacity < required) capacity *= 2u;
        char *grown = realloc(strings, (SIZE_T)capacity); if (!grown) return 0;
        strings = grown; string_capacity = capacity;
    }
    *offset = string_bytes; memcpy(strings + string_bytes, value, bytes); string_bytes += bytes; return 1;
}
static int descriptor_from_type(uintptr_t object, uintptr_t *descriptor) {
    *descriptor = 0; if (!object_class(object, runtime_type_class)) return 0;
    memcpy(descriptor, (const void *)(object + (uintptr_t)handle_qword * 8u), 8u);
    return readable(*descriptor, 16u);
}
static uint64_t decode_value(uint64_t raw,uint64_t key,uint32_t operation){if(operation==1u)return raw^key;if(operation==2u)return raw-key;if(operation==3u)return key-raw;return 0;}
static int object_contains(uintptr_t object,uintptr_t value){if(!object||!value||!readable(object,32u*8u))return 0;for(uint32_t q=0;q<32u;q++){uintptr_t observed=0;memcpy(&observed,(const void*)(object+(uintptr_t)q*8u),8u);if(observed==value)return 1;}return 0;}
static int event_info(
    uintptr_t object, uintptr_t name, uintptr_t add, uintptr_t remove,
    uintptr_t raise, uint32_t *attributes
) {
    event_info_fill_fn fill = (event_info_fill_fn)event_info_fill_pointer;
    uintptr_t info[16]; memset(info, 0, sizeof(info));
    fill(object, info, event_info_fill_metadata);
    if (event_info_name_qword == UINT32_MAX) {
        uint32_t candidate = UINT32_MAX, count = 0;
        for (uint32_t qword = 0; qword + 4u < 16u; qword++) {
            if (managed_string_equal(info[qword], name) &&
                method_object_equal(info[qword + 1u], add) &&
                method_object_equal(info[qword + 2u], remove) &&
                method_object_equal(info[qword + 3u], raise) &&
                add && remove) {
                candidate = qword; count++;
            }
        }
        if (count != 1u) return 0;
        event_info_name_qword = candidate;
        event_info_flags_offset = (candidate + 4u) * sizeof(uintptr_t);
    }
    if (!managed_string_equal(info[event_info_name_qword], name) ||
        !method_object_equal(info[event_info_name_qword + 1u], add) ||
        !method_object_equal(info[event_info_name_qword + 2u], remove) ||
        !method_object_equal(info[event_info_name_qword + 3u], raise) ||
        event_info_flags_offset + sizeof(uint32_t) > sizeof(info)) return 0;
    memcpy(attributes, (const unsigned char *)info + event_info_flags_offset,
        sizeof(*attributes));
    return *attributes <= UINT16_MAX;
}
static int typed_event_array(uintptr_t array, uintptr_t **items, uint32_t *count, int derive) {
    *items = NULL; *count = 0;
    if (!array || !readable(array, (derive ? 80u : 40u))) return 0;
    uint32_t lq = array_length_qword, vq = array_vector_qword;
    if (derive) {
        lq = vq = 0;
        for (uint32_t l = 1; l < 8; l++) { uintptr_t length = 0;
            memcpy(&length, (const void *)(array + (uintptr_t)l * 8u), 8u);
            if (!length || length > 4096u) continue;
            for (uint32_t v = l + 1; v < 10; v++) { uintptr_t vector = array + (uintptr_t)v * 8u;
                if (!readable(vector, (SIZE_T)length * 8u)) continue;
                uint64_t valid = 0; for (; valid < length; valid++) { uintptr_t item = 0;
                    memcpy(&item, (const void *)(vector + valid * 8u), 8u);
                    if (!object_class(item, event_class)) break;
                }
                if (valid == length) { if (lq) return 0; lq = l; vq = v; }
            }
        }
        if (!lq) return 0; array_length_qword = lq; array_vector_qword = vq;
    }
    uintptr_t length = 0; memcpy(&length, (const void *)(array + (uintptr_t)lq * 8u), 8u);
    if (length > 4096u) return 0; uintptr_t vector = array + (uintptr_t)vq * 8u;
    if (length && !readable(vector, (SIZE_T)length * 8u)) return 0;
    for (uint64_t i = 0; i < length; i++) { uintptr_t item = 0;
        memcpy(&item, (const void *)(vector + i * 8u), 8u);
        if (!object_class(item, event_class)) return 0;
    }
    *items = (uintptr_t *)vector; *count = (uint32_t)length; return 1;
}
static int read_file(const wchar_t *path, unsigned char **data, SIZE_T *bytes) {
    FILE *in = _wfopen(path, L"rb"); if (!in || _fseeki64(in, 0, SEEK_END)) return 0;
    *bytes = (SIZE_T)_ftelli64(in); if (_fseeki64(in, 0, SEEK_SET)) { fclose(in); return 0; }
    *data = malloc(*bytes ? *bytes : 1u); int ok = *data && fread(*data, 1, *bytes, in) == *bytes;
    fclose(in); return ok;
}
static void digest_hex(const unsigned char d[32], char out[65]) {
    static const char a[] = "0123456789abcdef"; for (int i=0;i<32;i++){out[i*2]=a[d[i]>>4];out[i*2+1]=a[d[i]&15];}out[64]=0;
}
static int sha256_file(const wchar_t *path, char output[65]) {
    HANDLE in=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);
    if(in==INVALID_HANDLE_VALUE)return 0; BCRYPT_ALG_HANDLE alg=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD os=0,r=0;unsigned char *o=NULL,*b=NULL,d[32];
    int ok=BCryptOpenAlgorithmProvider(&alg,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(alg,BCRYPT_OBJECT_LENGTH,(PUCHAR)&os,sizeof(os),&r,0)>=0;
    if(ok)o=HeapAlloc(GetProcessHeap(),0,os);if(ok)b=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!o||!b))ok=0;
    if(ok&&BCryptCreateHash(alg,&hash,o,os,NULL,0,0)<0)ok=0;while(ok){DWORD n=0;if(!ReadFile(in,b,1048576u,&n,NULL)){ok=0;break;}if(!n)break;if(BCryptHashData(hash,b,n,0)<0)ok=0;}
    if(ok&&BCryptFinishHash(hash,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,output);if(hash)BCryptDestroyHash(hash);if(alg)BCryptCloseAlgorithmProvider(alg,0);if(o)HeapFree(GetProcessHeap(),0,o);if(b)HeapFree(GetProcessHeap(),0,b);CloseHandle(in);return ok;
}
static int executable_identity(char output[65]) { wchar_t path[32768];DWORD n=GetModuleFileNameW(NULL,path,32768);return n&&n<32768&&sha256_file(path,output); }

$module_candidate_diagnostics

static int capture_modules(void) {
    modules = calloc(expected_type_count, sizeof(*modules)); if (!modules) { failure_kind=1081; return 0; }
    for (uint64_t i=0;i<expected_type_count;i++){uintptr_t p=types[i].module_pointer;uint64_t j=0;for(;j<module_count;j++)if(modules[j].module_pointer==p)break;if(j==module_count){modules[module_count].module_pointer=p;module_count++;}}
    if (!module_count || module_count != expected_module_count) { failure_kind=1085; failure_index=module_count; return 0; }
    uint32_t support[16]={0};
    for(uint64_t i=0;i<module_count;i++)for(uint32_t q=2;q<16;q++){uintptr_t s=0;uintptr_t a=modules[i].module_pointer+(uintptr_t)q*8u;if(!readable(a,8u))continue;memcpy(&s,(const void*)a,8u);char *v=NULL;uint32_t n=0;if(managed_utf8(s,&v,&n)){if(n>=4&&(!memcmp(v+n-4,".dll",4)||!memcmp(v+n-4,".exe",4)))support[q]++;free(v);}}
    uint32_t candidate=UINT32_MAX,matches=0;
    for(uint32_t q=2;q<16;q++)if(support[q]==module_count){candidate=q;matches++;}

    if(matches!=1u){write_module_candidate_diagnostic(support,matches);failure_kind=1082;failure_index=matches;return 0;}
    module_name_qword=candidate;
    for(uint64_t i=0;i<module_count;i++){uintptr_t s=0;memcpy(&s,(const void*)(modules[i].module_pointer+(uintptr_t)module_name_qword*8u),8u);char *v=NULL;uint32_t n=0;if(!managed_utf8_recorded(s,&v,&n)||!n){free(v);failure_kind=1083;failure_index=i+1;return 0;}if(!append_text(v,n,&modules[i].name_offset)){free(v);failure_kind=1084;failure_index=i+1;return 0;}modules[i].name_bytes=n;free(v);}return 1;
}
static int validate_event_token_order(void);
static int capture_events(void) {
    instance_flags collect=(instance_flags)type_events_pointer;instance_noarg get_name=(instance_noarg)event_name_pointer;instance_noarg get_handler=(instance_noarg)event_handler_pointer;instance_boolarg get_add=(instance_boolarg)event_add_method_pointer;instance_boolarg get_remove=(instance_boolarg)event_remove_method_pointer;instance_boolarg get_raise=(instance_boolarg)event_raise_method_pointer;instance_dword get_metadata_token=(instance_dword)metadata_token_pointer;
    while(event_cursor<expected_event_count){uint32_t type_index=events[event_cursor].type_index;uint64_t start=event_cursor;while(event_cursor<expected_event_count&&events[event_cursor].type_index==type_index)event_cursor++;uint32_t expected=(uint32_t)(event_cursor-start);
        uintptr_t array=collect(types[type_index].type_object,ALPHA_BINDING_FLAGS,type_events_metadata);uintptr_t *items=NULL;uint32_t count=0;if(!typed_event_array(array,&items,&count,!array_length_qword)||count!=expected){failure_index=start+1;failure_kind=1;return 0;}
        for(uint32_t j=0;j<count;j++){uintptr_t name=get_name(items[j],event_name_metadata);uintptr_t handler=get_handler(items[j],event_handler_metadata);uintptr_t add_object=get_add(items[j],1u,event_add_method_metadata);uintptr_t remove_object=get_remove(items[j],1u,event_remove_method_metadata);uintptr_t raise_object=get_raise(items[j],1u,event_raise_method_metadata);uintptr_t observed_add=method_pointer_from_object(add_object),observed_remove=method_pointer_from_object(remove_object);if(!observed_add||!observed_remove){failure_index=start+j+1;failure_kind=31;return 0;}uint64_t index=UINT64_MAX;uint32_t link_matches=0;int matched_direct=0;for(uint32_t k=0;k<expected;k++){member_record*candidate=&events[start+k];uint64_t candidate_raw0=0,candidate_raw1=0;memcpy(&candidate_raw0,candidate->payload+(uintptr_t)accessor0_slot*8u,8u);memcpy(&candidate_raw1,candidate->payload+(uintptr_t)accessor1_slot*8u,8u);uintptr_t decoded0=(uintptr_t)decode_value(candidate_raw0,accessor0_key,accessor0_operation),decoded1=(uintptr_t)decode_value(candidate_raw1,accessor1_key,accessor1_operation);int direct=observed_add==decoded0&&observed_remove==decoded1;int crossed=observed_add==decoded1&&observed_remove==decoded0;if(direct||crossed){index=start+k;matched_direct=direct;link_matches++;}}if(link_matches!=1u||index==UINT64_MAX||output_events[index].member_pointer){failure_index=start+j+1;failure_kind=5;return 0;}member_record *src=&events[index];output_event *dst=&output_events[index];char *value=NULL;uint32_t bytes=0;
            dst->type_index=src->type_index;dst->member_index=src->member_index;dst->member_pointer=src->pointer;dst->metadata_token=get_metadata_token(items[j],metadata_token_metadata);uint32_t rid=dst->metadata_token&0x00ffffffu;if((dst->metadata_token&0xff000000u)!=0x14000000u||rid<expected_metadata_token_rid_base){failure_index=index+1;failure_kind=4000u+rid;return 0;}
            if(!descriptor_from_type(handler,&dst->handler_descriptor)||!managed_utf8_recorded(name,&value,&bytes)){free(value);failure_index=index+1;failure_kind=2;return 0;}
            if(!bytes){char synthetic[40];int n=snprintf(synthetic,sizeof(synthetic),"EmptyEvent_%X",dst->metadata_token);if(n<=0||n>=(int)sizeof(synthetic)||!append_text(synthetic,(uint32_t)n,&dst->name_offset)){free(value);return 0;}dst->name_bytes=(uint32_t)n;synthetic_events++;}else{dst->name_bytes=bytes;if(!append_text(value,bytes,&dst->name_offset)){free(value);return 0;}}free(value);
            if(matched_direct)direct_accessor_permutation_count++;else crossed_accessor_permutation_count++;dst->add_pointer=observed_add;dst->remove_pointer=observed_remove;if(!event_info(items[j],name,add_object,remove_object,raise_object,&dst->flags)){failure_index=index+1;failure_kind=34;return 0;}completed_events++;
        }
    }return validate_event_token_order();
}
static int validate_event_token_order(void) {
    previous_event_rid = 0;
    for (uint64_t index = 0; index < expected_event_count; index++) {
        uint32_t token = output_events[index].metadata_token;
        uint32_t rid = token & 0x00ffffffu;
        if ((token & 0xff000000u) != 0x14000000u ||
            rid < expected_metadata_token_rid_base ||
            (!index && rid != expected_metadata_token_rid_base) ||
            (index && rid <= previous_event_rid)) {
            failure_index = index + 1u; failure_kind = 4000u + rid;
            return 0;
        }
        previous_event_rid = rid;
    }
    return 1;
}
static volatile LONG event_request_generation, event_generation_sequence, event_callback_active;
static LRESULT CALLBACK window_proc(HWND w, UINT m, WPARAM wp, LPARAM lp) {
    if (m != message_id) return CallWindowProcW(original_proc, w, m, wp, lp);
    LONG generation = (LONG)wp;
    if (!generation || InterlockedCompareExchange(&event_request_generation, 0, 0) != generation ||
        InterlockedCompareExchange(&event_callback_active, 1, 0)) return 0;
    if (InterlockedCompareExchange(&event_request_generation, 0, generation) != generation) {
        InterlockedExchange(&event_callback_active, 0); return 0;
    }
    int ok = capture_events();
    InterlockedExchange(&callback_complete, ok ? 1 : -1);
    InterlockedExchange(&event_callback_active, 0);
    return ok;
}
typedef struct selection { DWORD pid; HWND window; uint32_t count; } selection;
static BOOL CALLBACK select_window(HWND w, LPARAM p) {
    selection *s = (selection *)(uintptr_t)p;
    DWORD pid = 0; RECT b;
    if (!IsWindowVisible(w) || GetWindow(w, GW_OWNER) || !GetWindowRect(w, &b) ||
        b.right <= b.left || b.bottom <= b.top) return TRUE;
    GetWindowThreadProcessId(w, &pid);
    if (pid == s->pid) { s->window = w; s->count++; }
    return TRUE;
}
static int event_quiescent(void) {
    for (uint32_t i = 0; i < 200u; i++) {
        if (!InterlockedCompareExchange(&event_callback_active, 0, 0)) return 1;
        Sleep(10u);
    }
    return !InterlockedCompareExchange(&event_callback_active, 0, 0);
}
static int dispatch_events(void) {
    selection s = {0}; s.pid = GetCurrentProcessId();
    if (!EnumWindows(select_window, (LPARAM)(uintptr_t)&s)) {
        failure_kind = 13001u; failure_index = GetLastError(); return 0;
    }
    if (s.count != 1 || !s.window) { failure_kind = 13002u; failure_index = s.count; return 0; }
    message_id = RegisterWindowMessageW(L"ALPHA v2 current runtime event module inventory");
    if (!message_id) { failure_kind = 13003u; failure_index = GetLastError(); return 0; }
    SetLastError(0);
    original_proc = (WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window, GWLP_WNDPROC, (LONG_PTR)(uintptr_t)window_proc);
    DWORD error = GetLastError();
    if (!original_proc && error != ERROR_SUCCESS) {
        failure_kind = 13004u; failure_index = error; return 0;
    }
    int ok = 0;
    for (uint32_t attempt = 0; attempt < 17u; attempt++) {
        if (!event_quiescent()) { failure_kind = 13007u; break; }
        LONG generation = InterlockedIncrement(&event_generation_sequence);
        if (generation <= 0) { failure_kind = 13008u; break; }
        InterlockedExchange(&callback_complete, 0);
        InterlockedExchange(&event_request_generation, generation);
        DWORD_PTR result = 0;
        SetLastError(0);
        int sent = SendMessageTimeoutW(s.window, message_id, (WPARAM)generation, 0,
            SMTO_BLOCK, 60000u, &result) != 0;
        error = GetLastError();
        InterlockedExchange(&event_request_generation, 0);
        if (!event_quiescent()) { failure_kind = 13007u; failure_index = error; break; }
        LONG complete = InterlockedCompareExchange(&callback_complete, 0, 0);
        if (complete == 1) {
            if (completed_events == expected_event_count && event_cursor == expected_event_count) ok = 1;
            else { failure_kind = 13008u; failure_index = completed_events; }
            break;
        }
        if (complete == -1) {
            if (!failure_kind) failure_kind = 13006u;
            break;
        }
        if (sent) { failure_kind = 13006u; failure_index = error; break; }
        if (attempt == 16u) { failure_kind = 13005u; failure_index = error; break; }
        Sleep(250u);
    }
    InterlockedExchange(&event_request_generation, 0);
    SetLastError(0);
    LONG_PTR restored = SetWindowLongPtrW(s.window, GWLP_WNDPROC, (LONG_PTR)(uintptr_t)original_proc);
    error = GetLastError();
    if (!restored && error != ERROR_SUCCESS) { failure_kind = 13009u; failure_index = error; ok = 0; }
    return ok;
}
static FILE *open_private_output(const wchar_t *path) {
    int fd = _wopen(path, _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY, _S_IREAD | _S_IWRITE);
    if (fd < 0) return NULL;
    FILE *output = _fdopen(fd, "wb");
    if (!output) { _close(fd); _wremove(path); }
    return output;
}
static void write_status(const char *status,int written){FILE*out=open_private_output(status_path);if(!out)return;fprintf(out,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"module_count\": %llu,\n  \"completed_event_count\": %llu,\n  \"expected_event_count\": %llu,\n  \"synthetic_event_name_count\": %llu,\n  \"metadata_token_rid_base\": %u,\n  \"module_name_qword_owner_only\": %u,\n  \"array_length_qword_owner_only\": %u,\n  \"array_vector_qword_owner_only\": %u,\n  \"event_info_name_qword_owner_only\": %u,\n  \"event_info_flags_offset_owner_only\": %u,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"event_flags_live_info_structure_derived\": true,\n  \"event_accessors_cross_checked_against_method_inventory\": true,\n  \"legacy_event_attribute_dispatch_used\": false,\n  \"saved_event_module_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)module_count,(unsigned long long)completed_events,(unsigned long long)expected_event_count,(unsigned long long)synthetic_events,expected_metadata_token_rid_base,module_name_qword,array_length_qword,array_vector_qword,event_info_name_qword,event_info_flags_offset,(unsigned long long)failure_index,failure_kind,written?"true":"false");fclose(out);}
static int write_output(void){uint64_t end=sizeof(output_header)+module_count*sizeof(output_module)+expected_event_count*sizeof(output_event);for(uint64_t i=0;i<module_count;i++)modules[i].name_offset+=end;for(uint64_t i=0;i<expected_event_count;i++)output_events[i].name_offset+=end;output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"ALPHAEM1",8);h.version=$output_version;h.header_bytes=sizeof(h);h.module_record_bytes=sizeof(output_module);h.event_record_bytes=sizeof(output_event);h.module_count=module_count;h.event_count=expected_event_count;h.string_bytes=string_bytes;h.image_base=expected_image_base;h.image_bytes=expected_image_bytes;h.type_count=expected_type_count;memcpy(h.executable_sha256,executable_sha256,64);memcpy(h.identity_sha256,identity_sha256,64);memcpy(h.member_sha256,member_sha256,64);memcpy(h.semantics_sha256,semantics_sha256,64);FILE*out=open_private_output(output_path);if(!out)return 0;int ok=fwrite(&h,1,sizeof(h),out)==sizeof(h)&&fwrite(modules,sizeof(*modules),module_count,out)==module_count&&fwrite(output_events,sizeof(*output_events),expected_event_count,out)==expected_event_count&&fwrite(strings,1,string_bytes,out)==string_bytes;if(fclose(out))ok=0;if(!ok)_wremove(output_path);return ok;}
static DWORD WINAPI worker(LPVOID unused){(void)unused;char eh[65],ih[65],mh[65],nh[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(eh)||strcmp(eh,executable_sha256)||!sha256_file(identity_path,ih)||strcmp(ih,identity_sha256)||!sha256_file(member_path,mh)||strcmp(mh,member_sha256)||!sha256_file(native_path,nh)||strcmp(nh,native_sha256)){failure_kind=100;write_status("identity_mismatch",0);return 0;}SIZE_T ib=0,mb=0,nb=0;if(!read_file(identity_path,&identity_data,&ib)||!read_file(member_path,&member_data,&mb)||!read_file(native_path,&native_data,&nb)){failure_kind=101;write_status("input_unavailable",0);return 0;}identity_header*ihd=(identity_header*)identity_data;member_header*mhd=(member_header*)member_data;native_header*nhd=(native_header*)native_data;if(ib<sizeof(*ihd)||mb<sizeof(*mhd)||nb<sizeof(*nhd)+expected_type_count*sizeof(native_type)+expected_method_count*sizeof(native_method)||memcmp(ihd->magic,"ALPHATI1",8)||memcmp(mhd->magic,"ALPHANM1",8)||memcmp(nhd->magic,"ALPHANI1",8)||nhd->version!=$native_version||nhd->type_record_bytes!=sizeof(native_type)||nhd->method_record_bytes!=sizeof(native_method)||ihd->type_count!=expected_type_count||nhd->type_count!=expected_type_count||nhd->method_count!=expected_method_count||mhd->event_count!=expected_event_count){failure_kind=102;write_status("input_invalid",0);return 0;}types=(identity_record*)(identity_data+sizeof(*ihd));events=(member_record*)(member_data+sizeof(*mhd)+(expected_field_count+expected_property_count)*sizeof(member_record));native_methods=(native_method*)(native_data+sizeof(*nhd)+expected_type_count*sizeof(native_type));output_events=calloc(expected_event_count,sizeof(*output_events));if(!output_events){failure_kind=107;write_status("capture_failed",0);return 0;}for(uint64_t i=0;i<expected_method_count;i++)if(native_methods[i].metadata_pointer==0){failure_kind=103;failure_index=i+1;write_status("input_invalid",0);return 0;}if(!capture_modules()){if(!failure_kind)failure_kind=108;write_status("capture_failed",0);return 0;}if(!dispatch_events()){if(!failure_kind)failure_kind=109;write_status("capture_failed",0);return 0;}if(completed_events!=expected_event_count){failure_kind=110;failure_index=completed_events;write_status("capture_failed",0);return 0;}int ok=write_string_io_probe()&&write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def runtime_event_module_source(
    *, binding: dict[str, Any], output_path: Path, status_path: Path
) -> str:
    from alpha.c04 import diagnostic_source
    operations = binding["operations"]
    return _COLLECTOR.substitute({
        "identity_header_bytes": _IDENTITY_HEADER.size,
        "identity_record_bytes": _IDENTITY_RECORD.size,
        "member_header_bytes": _NATIVE_MEMBER_HEADER.size,
        "member_record_bytes": _NATIVE_MEMBER_RECORD.size,
        "native_header_bytes": _NATIVE_INVENTORY_HEADER.size,
        "native_type_bytes": _NATIVE_TYPE_RECORD.size,
        "native_method_bytes": _NATIVE_METHOD_RECORD.size,
        "native_version": _NATIVE_INVENTORY_VERSION,
        "output_header_bytes": RUNTIME_EVENT_MODULE_HEADER.size,
        "output_module_bytes": RUNTIME_EVENT_MODULE_MODULE.size,
        "output_event_bytes": RUNTIME_EVENT_MODULE_EVENT.size,
        "output_version": RUNTIME_EVENT_MODULE_VERSION,
        "status_schema": RUNTIME_EVENT_MODULE_STATUS_SCHEMA,
        "module_candidate_diagnostics": diagnostic_source(output_path.parent / "runtime-module-name-candidates.private.json"),
        "derived_string_reader": event_string_reader_source(contract=binding["string_layout_contract"],
            output_path=output_path.parent / "runtime-event-string-io.private.json"),
        "executable_sha256": binding["binary"]["sha256"],
        "identity_sha256": binding["type_identity_inventory"]["sha256"],
        "member_sha256": binding["native_member_inventory"]["sha256"],
        "native_sha256": binding["native_inventory"]["sha256"],
        "semantics_sha256": binding["native_semantics"]["sha256"],
        "process_id": binding["process_id"], "image_base": binding["image_base"],
        "image_bytes": binding["image_bytes"], "type_count": binding["type_count"],
        "module_count": binding["module_count"],
        "field_count": binding["field_count"], "property_count": binding["property_count"],
        "event_count": binding["event_count"],
        "method_count": binding["method_count"],
        "metadata_token_rid_base": binding["metadata_token_rid_base"],
        "runtime_type_class": binding["runtime_type_class"],
        "string_class": binding["string_class"], "event_class": binding["event_class"],
        "method_class": binding["method_class"],
        "handle_qword": binding["handle_qword"],
        "type_events_pointer": operations["type.events"]["pointer"],
        "type_events_metadata": operations["type.events"]["metadata"],
        "event_name_pointer": operations["event.name"]["pointer"],
        "event_name_metadata": operations["event.name"]["metadata"],
        "event_handler_pointer": operations["event.handler_type"]["pointer"],
        "event_handler_metadata": operations["event.handler_type"]["metadata"],
        "event_add_method_pointer": operations["event.add_method"]["pointer"],
        "event_add_method_metadata": operations["event.add_method"]["metadata"],
        "event_remove_method_pointer": operations["event.remove_method"]["pointer"],
        "event_remove_method_metadata": operations["event.remove_method"]["metadata"],
        "event_raise_method_pointer": operations["event.raise_method"]["pointer"],
        "event_raise_method_metadata": operations["event.raise_method"]["metadata"],
        "event_info_fill_pointer": binding["event_info_fill"]["pointer"],
        "event_info_fill_metadata": binding["event_info_fill"]["metadata"],
        "metadata_token_pointer": operations["member.metadata_token"]["pointer"],
        "metadata_token_metadata": operations["member.metadata_token"]["metadata"],
        "accessor0_slot": binding["event_add"]["slot"], "accessor0_key": binding["event_add"]["key"],
        "accessor0_operation": {"xor": 1, "add": 2, "subtract": 3}[binding["event_add"]["operation"]],
        "accessor1_slot": binding["event_remove"]["slot"], "accessor1_key": binding["event_remove"]["key"],
        "accessor1_operation": {"xor": 1, "add": 2, "subtract": 3}[binding["event_remove"]["operation"]],
        "identity_path": _wide_literal(_windows_z_path(Path(binding["type_identity_inventory"]["path"]))),
        "member_path": _wide_literal(_windows_z_path(Path(binding["native_member_inventory"]["path"]))),
        "native_path": _wide_literal(_windows_z_path(Path(binding["native_inventory"]["path"]))),
        "output_path": _wide_literal(_windows_z_path(output_path)),
        "status_path": _wide_literal(_windows_z_path(status_path)),
    })


def _validate_current_identity_source(binding, current_process):

    from alpha.c04 import _verify_files
    from alpha.c06 import load_raw_type_names
    from alpha.p13 import _safe_path, _file_record
    records = {role: binding[role] for role in
        ("type_identity_plan", "type_identity_model", "type_identity_inventory", "native_inventory", "semantics")}
    _verify_files(records)
    plan = read_json(Path(binding["type_identity_plan"]["path"]))
    model = read_json(Path(binding["type_identity_model"]["path"]))
    expected = {"process_id": current_process[0], "creation_filetime": current_process[1],
        "executable_path": str(
            Path(current_process[2]).expanduser().resolve()
        ), "executable_sha256": binding["binary"]["sha256"],
        "image_base_owner_only": binding["image_base"], "image_bytes": binding["image_bytes"]}
    if (any(plan.get("target", {}).get(key) != value or
            type(plan.get("target", {}).get(key)) is not type(value) for key, value in expected.items()) or
        plan.get("inventory_path") != binding["type_identity_inventory"]["path"] or
        plan.get("inputs", {}).get("native_inventory") != binding["native_inventory"] or
        plan.get("inputs", {}).get("reflection_semantics") != binding["semantics"] or
        model.get("identity_inventory") != binding["type_identity_inventory"] or
        not isinstance(model.get("raw_names"), dict) or
        not isinstance(plan.get("raw_type_names_path"), str) or
        not isinstance(plan.get("raw_names_output_path"), str)):
        raise AcquisitionError("event/module type source belongs to a different process instance or source domain")
    source_files = {}
    for role, key in (("raw_type_observation", "raw_type_names_path"), ("raw_type_names", "raw_names_output_path")):
        path = _safe_path(Path(plan[key]))
        source_files[role] = dict(_file_record(path), path=str(path))
    load_raw_type_names(model=model["raw_names"], inventory_path=Path(plan["raw_names_output_path"]),
        expected_identity=dict(expected, image_base=expected["image_base_owner_only"]),
        expected_inputs={"native_inventory": binding["native_inventory"], "reflection_semantics": binding["semantics"],
            "type_identity_inventory": binding["type_identity_inventory"],
            "raw_type_observation": source_files["raw_type_observation"]}, expected_count=binding["type_count"])
    _verify_files(dict(records, **source_files))
    return source_files


def prepare_runtime_event_module_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    native_semantics_model: Path, native_inventory: Path,
    native_member_inventory: Path, type_identity_model: Path,
    type_identity_inventory: Path, runtime_inventory_dispatch: Path | None,
    output_dir: Path,
    compiler: Path | None = None,
    string_layout_model: Path | None = None,
    method_detail_model: Path | None = None,
    method_detail_inventory: Path | None = None,
    ancestry_inventory: Path | None = None,
) -> dict[str, Any]:
    from alpha.c10 import ROLES, replay_owners, attach_raw_event_module_names
    from alpha.p17 import attach_event_accessors
    from alpha.c04 import _verify_files
    from alpha.c08 import derive_bound_operations
    from alpha.c09 import getter_binding
    from alpha.c04 import compose_module_capture
    current_process = current_runtime_process_binding()
    if current_process is None:
        raise AcquisitionError("lossless event/module capture requires an explicitly bound current process")
    output_dir = _owner_directory(output_dir)
    binding = _binding(binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        native_semantics_model=native_semantics_model,
        native_inventory=native_inventory,
        native_member_inventory=native_member_inventory,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        runtime_inventory_dispatch=runtime_inventory_dispatch, string_layout_model=string_layout_model)
    if (binding["process_id"] != current_process[0] or
        not same_executable_path(binary, current_process[2])):
        raise AcquisitionError("event/module source process differs from current binding")
    type_sources = _validate_current_identity_source(binding, current_process)
    operation, method_sources, derived_modules = derive_bound_operations(native=binding, binary=binary,
        method_detail_model=method_detail_model, method_detail_inventory=method_detail_inventory,
        ancestry_inventory=ancestry_inventory,
        process_identity={"process_id": current_process[0], "creation_filetime": current_process[1]})
    module_binding = getter_binding(native=binding, inputs=method_sources, operation=operation,
        identity={"process_id": current_process[0], "creation_filetime": current_process[1]})
    raw_inputs = {role: binding["semantics" if role == "reflection_semantics" else role] for role in ROLES}
    _verify_files(raw_inputs)
    raw_binding = {"executable_sha256": binding["binary"]["sha256"], "process_id": current_process[0],
        "creation_filetime": current_process[1], "inputs": {role: row["sha256"] for role, row in raw_inputs.items()}}
    module_owners, _ = replay_owners(identity_inventory=Path(binding["type_identity_inventory"]["path"]).read_bytes(),
        native_member_inventory=Path(binding["native_member_inventory"]["path"]).read_bytes(),
        expected_binding=raw_binding, type_count=binding["type_count"], event_count=binding["event_count"],
        image_base=binding["image_base"], image_bytes=binding["image_bytes"])
    _verify_files(raw_inputs)
    binding["module_count"] = len(module_owners)
    if derived_modules != module_owners:
        raise AcquisitionError("Module getter and raw owner domains differ")
    output_path = output_dir / "runtime-event-module.private.bin"
    raw_observation_path = output_dir / "runtime-event-module-raw-observation.private.bin"
    raw_names_path = output_dir / "runtime-event-module-raw-names.private.bin"
    string_io_path = output_dir / "runtime-event-string-io.private.json"
    accessor_path = output_dir / "runtime-event-accessors.private.json"
    module_diagnostic_path = output_dir / "runtime-module-name-candidates.private.json"
    module_getter_path = output_dir / "runtime-module-name-getter-io.private.json"
    status_path = output_dir / "runtime-event-module-status.private.json"
    model_path = output_dir / "runtime-event-module.private.json"
    plan_path = output_dir / "runtime-event-module-plan.private.json"
    build_dir = _owner_directory(output_dir / "build-event-module")
    source_path = build_dir / "runtime-event-module.c"
    injector_source = build_dir / "runtime-event-module-injector.c"
    injector_path = build_dir / "alpha-runtime-event-module-injector.exe"
    for existing in (output_path, status_path, model_path, plan_path, raw_observation_path, raw_names_path, string_io_path, accessor_path, module_diagnostic_path, module_getter_path):
        if existing.exists() or existing.is_symlink():
            raise AcquisitionError("event/module capture requires new private output files")
    source, composed_binding, domains = attach_raw_event_module_names(runtime_event_module_source(
        binding=binding, output_path=output_path, status_path=status_path), binding=binding,
        creation_filetime=current_process[1], module_count=len(module_owners), output_path=raw_observation_path)
    if composed_binding != raw_binding or domains != {"event": binding["event_count"], "module": len(module_owners)}:
        raise AcquisitionError("event/module raw collector binding differs")
    source = compose_module_capture(source, model=operation, modules=module_owners,
        binding=module_binding, observation_path=module_getter_path)
    source = attach_event_accessors(source, binding=raw_binding, output_path=accessor_path)
    from concurrent.futures import ThreadPoolExecutor
    _private_text(source_path, source)
    _private_text(injector_source, runtime_injector_source())
    collector_path = build_dir / ("alpha-runtime-event-module-" +
        file_identity(source_path)["sha256"][:12] + ".dll")
    cc = _compiler(compiler)


    with ThreadPoolExecutor(max_workers=2) as executor:
        collector_build = executor.submit(
            cached_windows_build,
            [str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra", "-Wformat=2",
                "-Werror=format", str(source_path), "-o", str(collector_path), "-lbcrypt"],
            label="runtime event module collector",
            source_path=source_path,
            output_path=collector_path,
        )
        injector_build = executor.submit(
            cached_windows_build,
            [str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra", "-Wformat=2",
                "-Werror=format", str(injector_source), "-o", str(injector_path)],
            label="runtime event module injector",
            source_path=injector_source,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        if not artifact.is_file() or not artifact.stat().st_size:
            raise AcquisitionError(
                f"runtime event module build did not produce {artifact.name}"
            )
        artifact.chmod(0o600)
    plan = {"schema": RUNTIME_EVENT_MODULE_PLAN_SCHEMA, "status": "prepared",
        "target": {"executable_path": str(Path(binary).expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"], "creation_filetime": current_process[1],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"]},
        "inputs": {"string_layout_model": binding["string_layout_model"], **method_sources, **type_sources, **{key: binding[key] for key in (
            "semantics", "native_semantics", "native_inventory", "native_member_inventory",
            "type_identity_model", "type_identity_inventory", "type_identity_plan",
            "type_identity_status", "runtime_snapshot", "class_model")}},
        "attribute_semantics": binding["attribute_semantics"],
        "collector": file_identity(collector_path), "injector": file_identity(injector_path),
        "output_path": str(output_path), "status_path": str(status_path),
        "raw_observation_path": str(raw_observation_path), "raw_names_path": str(raw_names_path),
        "string_layout_io_path": str(string_io_path),
        "event_accessor_observation_path": str(accessor_path),
        "module_candidate_diagnostic_path": str(module_diagnostic_path),
        "module_getter_observation_path": str(module_getter_path),
        "module_getter_operation_owner_only": operation,
        "module_getter_binding": module_binding,
        "string_layout_contract_owner_only": {key: value.hex() if isinstance(value, bytes) else value
                                               for key, value in binding["string_layout_contract"].items()},
        "model_path": str(model_path),
        "contract": {"type_count": binding["type_count"], "event_count": binding["event_count"],
            "module_count": len(module_owners), "lossless_raw_names_required": True,
            "event_accessor_observations_required": True,
            "module_getter_observations_required": True,
            "module_record_bytes": RUNTIME_EVENT_MODULE_MODULE.size,
            "event_record_bytes": RUNTIME_EVENT_MODULE_EVENT.size,
            "metadata_token_rid_base": binding["metadata_token_rid_base"],
            "all_metadata_tokens_runtime_observed": True,
            "all_table_rids_definition_order_validated": True,
            "all_event_attributes_live_info_structure_observed": True},
        "policy": {"same_process_required": True, "runtime_layout_live_derived": True,
            "event_accessors_cross_checked_against_current_method_inventory": True,
            "runtime_token_rid_gaps_measured_not_compacted": True,
            "legacy_runtime_dispatch_used": False,
            "module_name_suffix_selection_used": False,
            "image_file_name_role_proven": False,
            "module_name_role_proven": False,
            "event_attribute_getter_invented": False,
            "member_attribute_fill_operations_current_structure_derived": True,
            "raw_pointers_owner_only": True, "saved_event_module_used": False,
            "fixed_address_used": False, "fixed_offset_used": False,
            "external_runtime_component_used": False}}
    _verify_files(plan["inputs"])
    _private_json(plan_path, plan)
    return {"schema": RUNTIME_EVENT_MODULE_PLAN_SCHEMA, "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "event_count": binding["event_count"], "policy": plan["policy"]}


def _digest(raw: bytes, label: str) -> str:
    try: value = raw.decode("ascii")
    except UnicodeDecodeError as error: raise AcquisitionError(f"runtime event module {label} digest is invalid") from error
    if len(value) != 64 or any(c not in "0123456789abcdef" for c in value):
        raise AcquisitionError(f"runtime event module {label} digest is invalid")
    return value


def _validate(plan: dict[str, Any], status: dict[str, Any]) -> tuple[dict[str, int], dict[str, bool]]:
    raw = Path(plan["output_path"]).read_bytes()
    if len(raw) < RUNTIME_EVENT_MODULE_HEADER.size: raise AcquisitionError("runtime event module output is truncated")
    h = RUNTIME_EVENT_MODULE_HEADER.unpack_from(raw); modules, events, strings = h[5:8]
    end = RUNTIME_EVENT_MODULE_HEADER.size + modules * RUNTIME_EVENT_MODULE_MODULE.size + events * RUNTIME_EVENT_MODULE_EVENT.size
    header_ok = (h[0] == RUNTIME_EVENT_MODULE_MAGIC and h[1] == RUNTIME_EVENT_MODULE_VERSION and
        h[2] == RUNTIME_EVENT_MODULE_HEADER.size and h[3] == RUNTIME_EVENT_MODULE_MODULE.size and
        h[4] == RUNTIME_EVENT_MODULE_EVENT.size and events == plan["contract"]["event_count"] and
        modules == plan["contract"]["module_count"] and 0 < modules <= plan["contract"]["type_count"] and
        h[8] == plan["target"]["image_base_owner_only"] and
        h[9] == plan["target"]["image_bytes"] and h[10] == plan["contract"]["type_count"] and h[11] == 0 and
        _digest(h[12], "executable") == plan["target"]["executable_sha256"] and
        _digest(h[13], "identity") == plan["inputs"]["type_identity_inventory"]["sha256"] and
        _digest(h[14], "members") == plan["inputs"]["native_member_inventory"]["sha256"] and
        _digest(h[15], "semantics") == plan["inputs"]["native_semantics"]["sha256"] and end + strings == len(raw))
    if not header_ok:
        raise AcquisitionError("runtime event/module header, domain or source binding differs")
    module_ok = header_ok; pointers: set[int] = set()


    module_region = memoryview(raw)[
        RUNTIME_EVENT_MODULE_HEADER.size:RUNTIME_EVENT_MODULE_HEADER.size
        + modules * RUNTIME_EVENT_MODULE_MODULE.size
    ]
    try:
        for p, n, reserved, o in RUNTIME_EVENT_MODULE_MODULE.iter_unpack(module_region):
            if not p or not n or reserved or o < end or o + n > len(raw): module_ok = False; break
            try: name = raw[o:o+n].decode("utf-8")
            except UnicodeDecodeError: module_ok = False; break
            if p in pointers: module_ok = False; break
            pointers.add(p)
    finally:
        module_region.release()
    event_ok = module_ok; synthetic = 0; tokens: set[int] = set(); event_rids: list[int] = []; start = RUNTIME_EVENT_MODULE_HEADER.size + modules * RUNTIME_EVENT_MODULE_MODULE.size
    if event_ok:
        event_region = memoryview(raw)[
            start:start + events * RUNTIME_EVENT_MODULE_EVENT.size
        ]
        try:
            first = True
            for row in RUNTIME_EVENT_MODULE_EVENT.iter_unpack(event_region):
                type_index, member_index, pointer, handler, add, remove, token, n, flags, reserved, o = row
                if (
                    type_index >= plan["contract"]["type_count"]
                    or not pointer
                    or not handler
                    or not add
                    or not remove
                    or token >> 24 != 0x14
                    or (token & 0x00FFFFFF)
                    < plan["contract"]["metadata_token_rid_base"]
                    or (first and (token & 0x00FFFFFF)
                        != plan["contract"]["metadata_token_rid_base"])
                    or (event_rids and (token & 0x00FFFFFF) <= event_rids[-1])
                    or token in tokens
                    or not n
                    or flags > 0xFFFF
                    or reserved
                    or o < end
                    or o + n > len(raw)
                ):
                    event_ok = False
                    break
                tokens.add(token)
                event_rids.append(token & 0x00FFFFFF)
                try: name = raw[o:o+n].decode("utf-8")
                except UnicodeDecodeError: event_ok = False; break
                synthetic += name.startswith("EmptyEvent_")
                first = False
        finally:
            event_region.release()
    rid_gap_count = sum(
        right - left - 1 for left, right in zip(event_rids, event_rids[1:])
    )
    counts = {"module_count": modules, "event_count": events,
        "string_bytes": strings, "display_placeholder_prefix_event_count": synthetic,
        "event_metadata_token_count": len(tokens),
        "event_metadata_rid_gap_count": rid_gap_count,
        "event_metadata_rid_min": min(event_rids) if event_rids else 0,
        "event_metadata_rid_max": max(event_rids) if event_rids else 0}
    checks = {"status_schema": status.get("schema") == RUNTIME_EVENT_MODULE_STATUS_SCHEMA,
        "status_process_bound": status.get("process_id") == plan["target"]["process_id"],
        "status_complete": status.get("status") == "complete", "header_bound": header_ok,
        "module_rows_valid": module_ok, "event_rows_valid": event_ok,
        "module_count_matches": status.get("module_count") == modules,
        "all_events_captured": status.get("completed_event_count") == events,
        "event_metadata_tokens_unique": len(tokens) == events,
        "metadata_token_rid_base_matches_current_runtime": status.get(
            "metadata_token_rid_base"
        ) == plan["contract"]["metadata_token_rid_base"],
        "all_runtime_visible_table_rids_strict_definition_order": event_ok,
        "event_info_layout_runtime_derived": (
            status.get("event_info_name_qword_owner_only")
            not in (None, 0xFFFFFFFF)
            and status.get("event_info_flags_offset_owner_only")
            not in (None, 0xFFFFFFFF)
            and status.get("event_flags_live_info_structure_derived") is True
            and status.get("legacy_event_attribute_dispatch_used") is False
        ),
        "event_accessors_cross_checked": status.get(
            "event_accessors_cross_checked_against_method_inventory"
        ) is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_event_module_absent": status.get("saved_event_module_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get("external_runtime_component_used") is False}
    return counts, checks


def capture_runtime_event_module_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    native_semantics_model: Path, native_inventory: Path,
    native_member_inventory: Path, type_identity_model: Path,
    type_identity_inventory: Path, runtime_inventory_dispatch: Path | None,
    output_dir: Path, wine: Path,
    wineprefix: Path, compiler: Path | None = None, timeout: float = 300.0,
    string_layout_model: Path | None = None,
    method_detail_model: Path | None = None,
    method_detail_inventory: Path | None = None,
    ancestry_inventory: Path | None = None,
) -> dict[str, Any]:
    if string_layout_model is None:
        raise AcquisitionError("event/module capture requires an explicit current String layout model")
    if any(path is None for path in (method_detail_model, method_detail_inventory, ancestry_inventory)):
        raise AcquisitionError("event/module capture requires explicit current method and ancestry sources")
    if current_runtime_process_binding() is None:


        arguments = locals().copy()
        import tempfile
        from alpha.p13 import RuntimeProcessProbe
        from alpha.c01 import bind_runtime_process
        with tempfile.TemporaryDirectory(prefix="alpha-event-process-") as temporary:
            probe = RuntimeProcessProbe(binary=binary, wine=wine, wineprefix=wineprefix,
                compiler=compiler, build_dir=Path(temporary).resolve())
            current = probe()
            with bind_runtime_process(current):
                result = capture_runtime_event_module_inventory(**arguments)
            if probe() != current:
                raise AcquisitionError("event/module target changed during individual capture")
            return result
    output_dir = _owner_directory(output_dir)
    prepare_runtime_event_module_inventory(binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        native_semantics_model=native_semantics_model,
        native_inventory=native_inventory, native_member_inventory=native_member_inventory,
        type_identity_model=type_identity_model, type_identity_inventory=type_identity_inventory,
        runtime_inventory_dispatch=runtime_inventory_dispatch,
        output_dir=output_dir, compiler=compiler, string_layout_model=string_layout_model,
        method_detail_model=method_detail_model, method_detail_inventory=method_detail_inventory,
        ancestry_inventory=ancestry_inventory)
    plan = read_json(output_dir / "runtime-event-module-plan.private.json")
    with RuntimeProcessLifetimeGuard(identity=plan["target"], wine=wine, wineprefix=wineprefix,
            compiler=compiler, build_dir=output_dir / "build-process-lifetime") as lifetime:
        return _capture_prepared_event_module(plan=plan, output_dir=output_dir, wine=wine,
            wineprefix=wineprefix, timeout=timeout, lifetime=lifetime)


def _capture_prepared_event_module(*, plan, output_dir, wine, wineprefix, timeout, lifetime):
    from alpha.c04 import _verify_files
    lifetime.assert_alive()
    _verify_files(dict(plan["inputs"], collector=plan["collector"], injector=plan["injector"]))
    env = os.environ.copy(); env["WINEPREFIX"] = str(wineprefix.expanduser().resolve()); env["WINEDEBUG"] = "-all"
    try: injected = subprocess.run(_host_run(str(wine.expanduser().resolve()), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name), env=env, check=False,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="replace", timeout=90)
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError("runtime event module injector could not run") from error
    _private_text(output_dir / "runtime-event-module-injector.private.log",
        json.dumps({"returncode": injected.returncode, "stdout": injected.stdout,
            "stderr": injected.stderr}, ensure_ascii=False, indent=2) + "\n")
    if injected.returncode: raise AcquisitionError("runtime event module injection failed")
    lifetime.assert_alive()
    deadline = time.monotonic() + timeout; status_path = Path(plan["status_path"]); status = None
    while time.monotonic() < deadline:
        lifetime.assert_alive()
        if status_path.is_file():
            candidate = read_runtime_progress(status_path)
            if isinstance(candidate, dict) and candidate.get("status"): status = candidate; break
        time.sleep(0.2)
    if status is None: raise AcquisitionError("runtime event module capture timed out")
    if status.get("status") != "complete": raise AcquisitionError(
        "runtime event module capture failed "
        f"(status={status.get('status')}, index={status.get('failure_index_owner_only')}, "
        f"kind={status.get('failure_kind_owner_only')})")
    lifetime.assert_alive()
    result = _finalize_event_module(plan=plan, status=status)
    lifetime.assert_alive()
    return result


def _validate_event_string_evidence(plan, raw_names, *, include_names=False):
    from alpha.c10 import ROLES, load_raw_event_module_names
    from alpha.c04 import _verify_files
    if (not isinstance(plan.get("string_layout_contract_owner_only"), dict) or
        not isinstance(plan.get("string_layout_io_path"), str) or "string_layout_model" not in plan["inputs"]):
        raise AcquisitionError("event/module String layout proof is absent")
    _verify_files(plan["inputs"])
    layout_model = read_json(Path(plan["inputs"]["string_layout_model"]["path"]))
    source_contract = layout_model.get("observation", {}).get("contract")
    if not isinstance(source_contract, dict):
        raise AcquisitionError("event/module String source contract is absent")
    expected_contract = {key.replace("_code_hex", "_code"): value for key, value in source_contract.items()}
    if expected_contract != plan["string_layout_contract_owner_only"]:
        raise AcquisitionError("event/module String contract changed after candidate derivation")
    records = {role: plan["inputs"]["semantics" if role == "reflection_semantics" else role] for role in ROLES}
    records.update(event_module_inventory=file_identity(Path(plan["output_path"])),
                   raw_event_module_observation=file_identity(Path(plan["raw_observation_path"])))
    names, _ = load_raw_event_module_names(model=raw_names, inventory_path=Path(plan["raw_names_path"]),
        expected_identity=dict(plan["target"], image_base=plan["target"]["image_base_owner_only"]),
        expected_inputs=records, expected_counts={key: plan["contract"][key + "_count"] for key in ("event", "module")},
        type_count=plan["contract"]["type_count"], rid_base=plan["contract"]["metadata_token_rid_base"])
    io_path = Path(plan["string_layout_io_path"])
    if not _seal_runtime_output(io_path):
        raise AcquisitionError("event/module String I/O output is absent")
    io_record = file_identity(io_path)
    result = validate_event_string_io(observation=read_json(io_path), names=names,
        expected_process_id=plan["target"]["process_id"], contract=plan["string_layout_contract_owner_only"])
    _verify_files(dict(plan["inputs"], string_io=io_record))
    result["inventory"] = io_record
    result["all_event_module_string_reads_use_derived_layout"] = True
    result["all_collectors_use_derived_string_layout"] = False
    return (result, names) if include_names else result


def _finalize_event_module(*, plan, status):
    from alpha.c10 import ROLES, normalize_raw_event_module_names
    from alpha.c04 import _verify_files
    if plan.get("contract", {}).get("lossless_raw_names_required") is not True:
        raise AcquisitionError("event/module plan has no lossless raw-name contract")
    if (plan["contract"].get("event_accessor_observations_required") is not True or
        not isinstance(plan.get("event_accessor_observation_path"), str)):
        raise AcquisitionError("event/module plan has no complete accessor observation contract")
    if plan["contract"].get("module_getter_observations_required") is not True:
        raise AcquisitionError("event/module plan has no code-derived Module getter contract")
    _verify_files(plan["inputs"])
    status_path = Path(plan["status_path"])
    output_path = Path(plan["output_path"]); _seal_runtime_output(output_path); _seal_runtime_output(status_path)
    _seal_runtime_output(Path(plan["raw_observation_path"]))
    counts, checks = _validate(plan, status)
    if not all(checks.values()): raise AcquisitionError("runtime event module validation failed: " +
        ", ".join(sorted(k for k, v in checks.items() if not v)))
    records = {role: dict(plan["inputs"]["semantics" if role == "reflection_semantics" else role]) for role in ROLES}
    records.update(event_module_inventory=file_identity(output_path),
        raw_event_module_observation=file_identity(Path(plan["raw_observation_path"])))
    identity = dict(plan["target"], image_base=plan["target"]["image_base_owner_only"])
    raw_names = normalize_raw_event_module_names(records=records, identity=identity,
        counts={"event": plan["contract"]["event_count"], "module": plan["contract"]["module_count"]},
        type_count=plan["contract"]["type_count"], rid_base=plan["contract"]["metadata_token_rid_base"],
        output_path=Path(plan["raw_names_path"]))
    checks.update(raw_names["checks"])
    for domain in ("event", "module"):
        for kind in ("empty", "null"):
            key = f"{kind}_{domain}_names"
            counts[key] = raw_names["counts"][key]
    counts["synthetic_event_name_count"] = counts["empty_event_names"] + counts["null_event_names"]
    checks["synthetic_event_names_accounted_from_originals"] = (
        status.get("synthetic_event_name_count") == counts["synthetic_event_name_count"])
    if not all(checks.values()):
        raise AcquisitionError("raw event names differ from native status")
    string_io, names = _validate_event_string_evidence(plan, raw_names, include_names=True)
    checks.update(string_io["checks"])
    from alpha.c09 import validate_module_getter_evidence
    module_getter = validate_module_getter_evidence(plan=plan, names=names)
    checks.update(module_getter["checks"])
    from alpha.p17 import validate_event_accessor_files
    accessor_path = Path(plan["event_accessor_observation_path"])
    if not _seal_runtime_output(accessor_path):
        raise AcquisitionError("event accessor observation output is absent")
    accessors = validate_event_accessor_files(observation_path=accessor_path, identity=plan["target"],
        inputs=plan["inputs"], event_path=output_path, type_count=plan["contract"]["type_count"])
    checks.update(accessors["checks"])
    counts.update(type_count=plan["contract"]["type_count"],
                  raise_accessor_present_count=accessors["counts"]["raise_present"],
                  raise_accessor_observed_null_count=accessors["counts"]["raise_null_observed"])
    _verify_files(plan["inputs"])
    model = {"schema": RUNTIME_EVENT_MODULE_SCHEMA, "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": plan["inputs"], "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path), "counts": counts,
        "checks": checks, "raw_names": raw_names, "string_layout_io": string_io, "event_accessors": accessors,
        "module_getter": module_getter,
        "owner_only": True, "metadata_complete": False}
    _private_json(Path(plan["model_path"]), model)
    return {"schema": RUNTIME_EVENT_MODULE_SCHEMA, "status": "runtime-validated",
        "target": model["target"], "counts": counts, "checks": checks,
        "inventory": model["inventory"]}
