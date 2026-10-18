from alpha.h02 import windows_run as _host_run

import json
import hashlib
import os
import stat
import struct
import subprocess
import time
from pathlib import Path
from string import Template
from typing import Any

from concurrent.futures import ThreadPoolExecutor

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.p19 import RUNTIME_TYPE_IDENTITY_PLAN_SCHEMA, RUNTIME_TYPE_IDENTITY_SCHEMA
from alpha.h02 import file_identity, read_json


RUNTIME_STRING_LITERAL_PLAN_SCHEMA = "alpha.runtime-string-literal-plan/v2"
RUNTIME_STRING_LITERAL_STATUS_SCHEMA = "alpha.runtime-string-literal-status/v2"
RUNTIME_STRING_LITERAL_SCHEMA = "alpha.runtime-string-literal-inventory/v2"
RUNTIME_STRING_LITERAL_MAGIC = b"ALPHASL2"
RUNTIME_STRING_LITERAL_VERSION = 2
RUNTIME_STRING_LITERAL_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQ64s64s64s64s"
)
RUNTIME_STRING_LITERAL_RECORD = struct.Struct("<IIQQII")
RUNTIME_METADATA_USAGE_PAIR_SCHEMA = "alpha.runtime-metadata-usage-pair-inventory/v1"
RUNTIME_METADATA_USAGE_PAIR_STATUS_SCHEMA = "alpha.runtime-metadata-usage-pair-status/v1"
RUNTIME_METADATA_USAGE_PAIR_MAGIC = b"ALPHAUP1"
RUNTIME_METADATA_USAGE_PAIR_VERSION = 1
RUNTIME_METADATA_USAGE_PAIR_HEADER = struct.Struct(
    "<8sIIIIQQQQ8Q64s64s64s"
)
RUNTIME_METADATA_USAGE_PAIR_RECORD = struct.Struct("<IIIIQ")
RUNTIME_METADATA_USAGE_VALUE_SCHEMA = (
    "alpha.runtime-metadata-usage-value-inventory/v1"
)
RUNTIME_METADATA_USAGE_VALUE_STATUS_SCHEMA = (
    "alpha.runtime-metadata-usage-value-status/v1"
)
RUNTIME_METADATA_USAGE_VALUE_MAGIC = b"ALPHAUV1"
RUNTIME_METADATA_USAGE_VALUE_VERSION = 1
RUNTIME_METADATA_USAGE_VALUE_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQQQQ64s64s64s"
)
RUNTIME_METADATA_USAGE_VALUE_RECORD = struct.Struct("<IIII" + "Q" * 14)
RUNTIME_METADATA_USAGE_GENERIC_RECORD = struct.Struct("<QQQQ")
RUNTIME_METADATA_USAGE_MEMBER_SCHEMA = (
    "alpha.runtime-metadata-usage-member-inventory/v1"
)
RUNTIME_METADATA_USAGE_MEMBER_STATUS_SCHEMA = (
    "alpha.runtime-metadata-usage-member-status/v1"
)
RUNTIME_METADATA_USAGE_MEMBER_MAGIC = b"ALPHAUM1"
RUNTIME_METADATA_USAGE_MEMBER_VERSION = 1
RUNTIME_METADATA_USAGE_MEMBER_HEADER = struct.Struct(
    "<8sIIII" + "Q" * 9 + "64s" * 4
)
RUNTIME_METADATA_USAGE_MEMBER_RECORD = struct.Struct("<IIIIQiiiI")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime string literal {label} is not owner-only")
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime string literal {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(f"runtime string literal {label} digest is invalid")
    return value


def _binding(
    *, binary: Path, type_identity_model: Path, type_identity_inventory: Path
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    binary_identity = file_identity(binary)
    model_path = _owner_file(type_identity_model, label="type identity model")
    inventory_path = _owner_file(
        type_identity_inventory, label="type identity inventory"
    )
    model = read_json(model_path)
    inventory_identity = file_identity(inventory_path)
    plan_path = _owner_file(
        model_path.parent / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    plan = read_json(plan_path)
    runtime_classes = plan.get("runtime_classes_owner_only", {})
    target = plan.get("target", {})
    checks = model.get("checks", {})
    if (
        not isinstance(model, dict)
        or model.get("schema") != RUNTIME_TYPE_IDENTITY_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != binary_identity["sha256"]
        or model.get("identity_inventory", model.get("inventory", {})).get(
            "sha256"
        )
        != inventory_identity["sha256"]
        or not isinstance(checks, dict)
        or not checks
        or not all(checks.values())
        or not isinstance(plan, dict)
        or plan.get("schema") != RUNTIME_TYPE_IDENTITY_PLAN_SCHEMA
        or plan.get("status") != "prepared"
        or target.get("executable_sha256") != binary_identity["sha256"]
        or Path(target.get("executable_path", "")).expanduser().resolve() != binary
        or not isinstance(target.get("process_id"), int)
        or target["process_id"] <= 0
        or not isinstance(target.get("image_base_owner_only"), int)
        or target["image_base_owner_only"] <= 0
        or not isinstance(target.get("image_bytes"), int)
        or target["image_bytes"] <= 0
        or not isinstance(runtime_classes.get("string"), int)
        or runtime_classes["string"] <= 0
    ):
        raise AcquisitionError("runtime string literal type binding is stale")


    from alpha.c01 import current_runtime_process_binding

    live = current_runtime_process_binding()
    if live is None:
        raise AcquisitionError(
            "runtime string literal capture requires a current process binding"
        )
    if live[2] != str(binary) and str(binary) != str(binary):
        raise AcquisitionError("runtime string literal executable binding is stale")
    return {
        "binary": binary_identity,
        "type_identity_model": file_identity(model_path),
        "type_identity_inventory": inventory_identity,
        "type_identity_plan": file_identity(plan_path),
        "process_id": live[0],
        "image_base": target["image_base_owner_only"],
        "image_bytes": target["image_bytes"],
        "string_class": runtime_classes["string"],
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ALPHA_MAX_REGIONS 65536u
#define ALPHA_MIN_LITERAL_COUNT 1024u
#define ALPHA_MAX_LITERAL_COUNT 1000000u
#define ALPHA_MAX_UTF16_LENGTH 0x100000u
#define ALPHA_MAX_LITERAL_BYTES 0x1000000u
#define ALPHA_BOUNDARY_WITNESSES 64u

typedef struct output_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t literal_count, mapping_base, image_base, image_bytes, string_bytes;
    uint64_t readable_region_count, boundary_witness_count;
    char executable_sha256[64], identity_sha256[64];
    char mapping_sha256[64], content_sha256[64];
} output_header;
typedef struct output_record {
    uint32_t source_index, utf16_length;
    uint64_t raw_pointer, text_offset;
    uint32_t text_bytes, raw_start;
} output_record;
typedef struct usage_output_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t usage_count, occurrence_count, image_base, image_bytes;
    uint64_t kind_counts[8];
    char executable_sha256[64], identity_sha256[64], content_sha256[64];
} usage_output_header;
typedef struct usage_output_record {
    uint32_t first_occurrence_index, destination_index, usage_kind, source_index;
    uint64_t slot_pointer;
} usage_output_record;
typedef struct usage_value_output_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t usage_count, nonzero_value_count, kind1_count;
    uint64_t image_base, image_bytes, type_record_base, type_record_stride;
    uint64_t generic_record_base, generic_record_stride, generic_record_count;
    char executable_sha256[64], identity_sha256[64], content_sha256[64];
} usage_value_output_header;
typedef struct usage_value_output_record {
    uint32_t first_occurrence_index, destination_index, usage_kind, source_index;
    uint64_t slot_pointer, slot_value, type_record_pointer;
    uint64_t type_record_data, type_record_bits;
    uint64_t related_pointer, related_data, related_bits, related_aux;
    uint64_t generic_record_pointer, generic_qword0, generic_qword1;
    uint64_t generic_qword2, generic_qword3;
} usage_value_output_record;
typedef struct usage_generic_output_record {
    uint64_t qword0, qword1, qword2, qword3;
} usage_generic_output_record;
typedef struct usage_member_output_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t usage_count, field_ref_count, method_spec_count;
    uint64_t image_base, image_bytes, type_record_base, type_record_stride;
    uint64_t generic_inst_base, generic_inst_stride;
    char executable_sha256[64], identity_sha256[64];
    char usage_sha256[64], content_sha256[64];
} usage_member_output_header;
typedef struct usage_member_output_record {
    uint32_t first_occurrence_index, destination_index, usage_kind, source_index;
    uint64_t slot_pointer;
    int32_t value0, value1, value2; uint32_t reserved;
} usage_member_output_record;
typedef struct region_record {
    uintptr_t base, end; SIZE_T bytes; DWORD protect, type;
} region_record;
typedef struct decoder_contract {
    uintptr_t case5_target, byte_decoder_target, descriptor_global, metadata_base_global;
    uintptr_t descriptor, metadata_base, mapping_base, data_base;
    uint32_t mapping_selector_field, data_selector_field;
    int32_t mapping_selector_xor, data_selector_xor;
    uint64_t index_multiplier, start_bias, end_bias;
    uint64_t stream_step, stream_index_multiplier, stream_index_bias;
    uint64_t stream_index_xor, stream_final_multiplier;
    uint64_t stream_mix_multiplier, stream_mix_add, stream_final_xor;
    uint32_t mix_multiplier, mix_xor, mix_add, mix_second_xor;
    uint32_t mix_second_add, mix_second_multiplier, final_xor;
    int32_t mapping_selector_add, data_selector_add;
    uint8_t index_shift, boundary_codec, selector_codec, stream_codec;
    uint8_t literal_codec;
    uint32_t string_length_offset, string_data_offset;
} decoder_contract;
typedef struct usage_pair_contract {
    uintptr_t range_base, pair_base;
    uintptr_t type_helper, type_resolver, type_state_global, type_record_base;
    uintptr_t generic_state_global, generic_record_base;
    uint32_t range_selector_field, range_selector_xor;
    uint32_t range_index_multiplier, range_mix_xor, range_mix_multiplier;
    uint32_t range_mix_second_xor, range_mix_add, range_final_add;
    uint32_t range_mid_multiplier, range_final_multiplier;
    uint64_t range_wide_add, range_wide_multiplier;
    uint32_t pair_selector_field, pair_selector_add;
    uint32_t pair_index_multiplier, pair_index_xor, pair_mix_multiplier;
    uint32_t pair_shift, pair_mix_add, pair_mix_xor;
    uint32_t pair_final_multiplier, pair_final_shift;
    uint32_t pair_encoded_add, pair_destination_add;
    uint32_t pair_source_xor, pair_destination_xor;
    uint32_t type_state_field, type_record_shift;
    uint32_t generic_state_field, generic_record_shift;
    uint32_t case_fields[8];
    uint64_t direct_index_multiplier, direct_index_add;
    uintptr_t direct_pair_base;
    uint32_t direct_key_multiplier, direct_selector_field;
    uint32_t direct_selector_xor, direct_encoded_add;
    uint32_t direct_destination_xor, direct_destination_add;
    uint32_t direct_key_add, direct_encoded_xor;
    uint8_t direct_index_shift, direct_key_shift, usage_codec;
    uint8_t range_first_shift, range_second_shift, range_third_shift;
} usage_pair_contract;
typedef struct usage_member_contract {
    uintptr_t field_ref_base, method_spec_base;
    uintptr_t generic_inst_state_global, generic_inst_base;
    uint32_t field_selector_field, field_selector_add;
    uint64_t field_index_multiplier, field_index_bias;
    uint32_t field_index_xor, field_index_mix, field_final_multiplier;
    uint32_t field_value0_xor, field_value1_xor, field_value1_add;
    uint32_t field_index_shift, field_record_stride;
    uint32_t method_selector_field, method_selector_add;
    uint32_t method_record_stride;
    uint32_t generic_inst_state_field, generic_inst_shift;
    uint32_t member_codec;
} usage_member_contract;
typedef struct decoded_usage_inventory {
    usage_output_record*records; uint64_t count, occurrence_count;
    uint64_t kind_counts[8]; char content_sha256[65];
} decoded_usage_inventory;
typedef struct decoded_usage_value_inventory {
    usage_value_output_record*records;
    uint64_t count, nonzero_value_count, kind1_count;
    usage_generic_output_record*generic_records;
    uint64_t generic_record_count;
    char content_sha256[65];
} decoded_usage_value_inventory;
typedef struct decoded_usage_member_inventory {
    usage_member_output_record*records;
    uint64_t count, field_ref_count, method_spec_count;
    char content_sha256[65];
} decoded_usage_member_inventory;
typedef struct decoded_inventory {
    output_record*records; char*text; uint64_t count, text_bytes;
    char mapping_sha256[65], content_sha256[65];
} decoded_inventory;
static int decode_literals_any(HMODULE image,uint64_t*count,decoded_inventory*inventory);
static int populate_usage_tables_v2(void);
static int observe_string_layout_v2(const decoded_usage_inventory*usage);
static int decode_literal_inventory_v2(const decoded_usage_inventory*usage,decoded_inventory*inventory);
static int decode_literal_inventory_metadata_v2(const decoded_usage_inventory*usage,decoded_inventory*inventory);
static int derive_literal_boundary(uint64_t*count);
static int decode_literal_inventory(uint64_t count,decoded_inventory*inventory);

_Static_assert(sizeof(output_header) == $header_bytes, "output header");
_Static_assert(sizeof(output_record) == $record_bytes, "output record");
_Static_assert(sizeof(usage_output_header) == $usage_header_bytes, "usage output header");
_Static_assert(sizeof(usage_output_record) == $usage_record_bytes, "usage output record");
_Static_assert(sizeof(usage_value_output_header) == $usage_value_header_bytes, "usage value output header");
_Static_assert(sizeof(usage_value_output_record) == $usage_value_record_bytes, "usage value output record");
_Static_assert(sizeof(usage_generic_output_record) == $usage_generic_record_bytes, "usage generic output record");
_Static_assert(sizeof(usage_member_output_header) == $usage_member_header_bytes, "usage member output header");
_Static_assert(sizeof(usage_member_output_record) == $usage_member_record_bytes, "usage member output record");

static const char executable_sha256[]="$executable_sha256";
static const char identity_sha256[]="$identity_sha256";
static const DWORD expected_pid=${process_id}u;
static const uintptr_t expected_image_base=${image_base}ull;
static const uint64_t expected_image_bytes=${image_bytes}ull;
static const uintptr_t string_class=${string_class}ull;
static const wchar_t output_path[]=$output_path;
static const wchar_t status_path[]=$status_path;
static const wchar_t usage_output_path[]=$usage_output_path;
static const wchar_t usage_status_path[]=$usage_status_path;
static const wchar_t usage_value_output_path[]=$usage_value_output_path;
static const wchar_t usage_value_status_path[]=$usage_value_status_path;
static const wchar_t usage_member_output_path[]=$usage_member_output_path;
static const wchar_t usage_member_status_path[]=$usage_member_status_path;
static const wchar_t decode_probe_path[]=$decode_probe_path;
/*
 * Derived metadata usage codec (current build family).  The parameters are
 * derived in Python from the current image and confirmed in-process before
 * any of them is used; the classic byte-pattern derivation above stays as the
 * fallback path for older clients.
 */
static const uint32_t usage_v2_available=$usage_v2_available;
/* Materializing through the target's own initializer is opt-in only; the
 * default path stays read-only. */
static const uint32_t usage_v2_materialize=$usage_v2_materialize;
static const uint32_t usage_v2_materialize_limit=$usage_v2_materialize_limit;
static const uintptr_t usage_v2_descriptor=${usage_v2_descriptor}ull;
static const uintptr_t usage_v2_descriptor_global=${usage_v2_descriptor_global}ull;
static const uintptr_t usage_v2_metadata_base_global=${usage_v2_metadata_base_global}ull;
static const uintptr_t usage_v2_metadata_base=${usage_v2_metadata_base}ull;
static const uint32_t usage_v2_range_field=${usage_v2_range_field}u;
static const uint32_t usage_v2_range_add=${usage_v2_range_add}u;
static const uint64_t usage_v2_range_multiplier=${usage_v2_range_multiplier}ull;
static const uint32_t usage_v2_range_shift1=${usage_v2_range_shift1}u;
static const uint64_t usage_v2_range_second=${usage_v2_range_second}ull;
static const uint32_t usage_v2_range_shift2=${usage_v2_range_shift2}u;
static const uint32_t usage_v2_range_mix=${usage_v2_range_mix}u;
static const uint32_t usage_v2_range_xor=${usage_v2_range_xor}u;
static const uint32_t usage_v2_pair_field=${usage_v2_pair_field}u;
static const uint32_t usage_v2_pair_bias=${usage_v2_pair_bias}u;
static const uint64_t usage_v2_pair_multiplier=${usage_v2_pair_multiplier}ull;
static const uint32_t usage_v2_pair_shift=${usage_v2_pair_shift}u;
static const uint32_t usage_v2_pair_xor=${usage_v2_pair_xor}u;
static const uint64_t usage_v2_pair_second=${usage_v2_pair_second}ull;
static const uint32_t usage_v2_pair_shift2=${usage_v2_pair_shift2}u;
static const uint32_t usage_v2_pair_add=${usage_v2_pair_add}u;
static const uint32_t usage_v2_pair_value_add=${usage_v2_pair_value_add}u;
static const uint32_t usage_v2_field_base_field=${usage_v2_field_base_field}u;
static const uint32_t usage_v2_field_base_xor=${usage_v2_field_base_xor}u;
static const uint32_t usage_v2_field_index_multiplier=${usage_v2_field_index_multiplier}u;
static const uint32_t usage_v2_field_index_xor=${usage_v2_field_index_xor}u;
static const uint32_t usage_v2_field_index_mix=${usage_v2_field_index_mix}u;
static const uint32_t usage_v2_field_index_add=${usage_v2_field_index_add}u;
static const uint32_t usage_v2_field_index_final_xor=${usage_v2_field_index_final_xor}u;
static const uint32_t usage_v2_field_value0_xor=${usage_v2_field_value0_xor}u;
static const uint32_t usage_v2_field_value1_xor=${usage_v2_field_value1_xor}u;
static const uint32_t usage_v2_method_spec_field=${usage_v2_method_spec_field}u;
static const uint32_t usage_v2_method_spec_xor=${usage_v2_method_spec_xor}u;
static const uint32_t usage_v2_method_spec_stride=${usage_v2_method_spec_stride}u;
static const uintptr_t usage_v2_generic_state_global=${usage_v2_generic_state_global}ull;
static const uint32_t usage_v2_generic_state_field=${usage_v2_generic_state_field}u;
static const uintptr_t usage_v2_generic_base=${usage_v2_generic_base}ull;
static const uint32_t usage_v2_generic_stride=${usage_v2_generic_stride}u;
static const uintptr_t usage_v2_type_record_base=${usage_v2_type_record_base}ull;
static const uint32_t usage_v2_literal_base_field=${usage_v2_literal_base_field}u;
static const uint64_t usage_v2_literal_stream_step=${usage_v2_literal_stream_step}ull;
static const uint64_t usage_v2_literal_key_multiplier=${usage_v2_literal_key_multiplier}ull;
static const uint64_t usage_v2_literal_key_add=${usage_v2_literal_key_add}ull;
static const uint64_t usage_v2_literal_key_xor=${usage_v2_literal_key_xor}ull;
static const uint64_t usage_v2_literal_key_bias=${usage_v2_literal_key_bias}ull;
static const uint32_t usage_v2_literal_base_xor=${usage_v2_literal_base_xor}u;
static const uint32_t usage_v2_literal_index_multiplier=${usage_v2_literal_index_multiplier}u;
static const uint32_t usage_v2_literal_index_add=${usage_v2_literal_index_add}u;
static const uint32_t usage_v2_literal_value_add=${usage_v2_literal_value_add}u;
static const uint32_t usage_v2_literal_second_index_add=${usage_v2_literal_second_index_add}u;
static const uint32_t usage_v2_literal_descriptor_field=${usage_v2_literal_descriptor_field}u;
static const uint32_t usage_v2_literal_descriptor_bias=${usage_v2_literal_descriptor_bias}u;
static const uint32_t usage_v2_type_record_shift=${usage_v2_type_record_shift}u;
static const uintptr_t usage_v2_type_helper=${usage_v2_type_helper}ull;
static const uintptr_t usage_v2_type_state_global=${usage_v2_type_state_global}ull;
static const uint32_t usage_v2_type_state_field=${usage_v2_type_state_field}u;
static const uintptr_t usage_v2_type_generic_state_global=${usage_v2_type_generic_state_global}ull;
static const uint32_t usage_v2_type_generic_state_field=${usage_v2_type_generic_state_field}u;
static const uint32_t usage_v2_type_generic_stride_shift=${usage_v2_type_generic_stride_shift}u;

static region_record regions[ALPHA_MAX_REGIONS];
static uint32_t region_count;
static uintptr_t usage_initializer, usage_state_global, usage_state, usage_table;
static uint32_t usage_switch_entries, usage_case5_field;
static uint32_t usage_case_fields[8];
static uintptr_t usage_case_tables[8];
static uint64_t usage_call_sites, usage_unique_indices, usage_max_index;
static uint32_t usage_coverage_per_mille;
static uint64_t usage_uncovered_nonempty_ranges;
static uint32_t usage_contract_stage_owner_only;
static uint32_t usage_v2_selected;
static uintptr_t usage_v2_live_descriptor, usage_v2_live_metadata_base;
static uint64_t usage_decode_failure_index=UINT64_MAX;
static uint32_t usage_decode_failure_stage,usage_decode_failure_raw0,usage_decode_failure_raw1,usage_decode_failure_value0,usage_decode_failure_value1;
static uint32_t usage_range_sample_raw[4],usage_range_sample_value[4];
static uint64_t usage_value_failure_index=UINT64_MAX;
static uint32_t usage_value_failure_stage,usage_value_failure_source;
static uintptr_t usage_value_failure_pointer;
static uint32_t usage_value_failure_type_code;
static usage_member_contract usage_members;
static uint64_t usage_member_failure_index=UINT64_MAX;
static uint32_t usage_member_failure_stage;
static uintptr_t usage_member_failure_pointer;
static uint64_t boundary_prefix_nulls, boundary_prefix_strings;
static uint32_t boundary_suffix_foreign;
static uint64_t literal_structural_tail_count;
static uintptr_t boundary_witness_classes[3];
static uint64_t decode_failure_index=UINT64_MAX;
static uint32_t decode_failure_stage,decode_failure_start,decode_failure_end,decode_failure_length;
static uintptr_t decode_failure_pointer;static uint64_t decode_failure_sample_owner_only;
static decoder_contract decoder;
static usage_pair_contract usage_pairs;
/*
 * Read-only diagnostics for the v2 literal decode.  A decode that fails closed
 * must still leave auditable evidence: every failure class is counted and a
 * bounded sample of the decoded/undecoded boundary is recorded next to the
 * status file.  Nothing here changes the decode result or touches the target.
 */
static uint32_t literal_decode_probe_stage;
static uint64_t literal_decode_totals[8];
static uint64_t literal_decode_domain;
static uint64_t literal_decode_referenced,literal_decode_referenced_beyond;
static uint32_t literal_decode_sample_count;
typedef struct literal_decode_sample {
    uint32_t stage,source,destination,encoded,value,span,readable,raw_count,decoded_count;
    uintptr_t pointer;
    unsigned char raw[16],decoded[16];
} literal_decode_sample;
static literal_decode_sample literal_decode_samples[16];

static void digest_hex(const unsigned char digest[32], char output[65]) {
    static const char alphabet[]="0123456789abcdef";
    for(int i=0;i<32;i++){output[i*2]=alphabet[digest[i]>>4];output[i*2+1]=alphabet[digest[i]&15];}
    output[64]=0;
}
static int sha256_file(const wchar_t *path,char output[65]) {
    HANDLE input=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);
    if(input==INVALID_HANDLE_VALUE)return 0;
    BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char*object=NULL,*buffer=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0&&object_size&&received==sizeof(object_size);
    if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1024u*1024u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;
    while(ok){DWORD count=0;if(!ReadFile(input,buffer,1024u*1024u,&count,NULL)){ok=0;break;}if(!count)break;if(BCryptHashData(hash,buffer,count,0)<0)ok=0;}
    if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)<0)ok=0;if(ok)digest_hex(digest,output);if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(input);return ok;
}
static int executable_identity(char output[65]){wchar_t path[32768];DWORD length=GetModuleFileNameW(NULL,path,(DWORD)(sizeof(path)/sizeof(path[0])));return length&&length<sizeof(path)/sizeof(path[0])&&sha256_file(path,output);}
static int readable_protect(DWORD protect){protect&=0xffu;return protect&&protect!=PAGE_NOACCESS;}
static int enumerate_regions(void){
    region_count=0;
    uintptr_t cursor=0;MEMORY_BASIC_INFORMATION memory;
    while(VirtualQuery((const void*)cursor,&memory,sizeof(memory))){uintptr_t base=(uintptr_t)memory.BaseAddress,end=base+memory.RegionSize;if(end<=base)break;if(memory.State==MEM_COMMIT&&!(memory.Protect&PAGE_GUARD)&&readable_protect(memory.Protect)){if(region_count>=ALPHA_MAX_REGIONS)return 0;regions[region_count++]=(region_record){base,end,memory.RegionSize,memory.Protect,memory.Type};}cursor=end;if(!cursor)break;}
    return region_count>0;
}
static int region_for(uintptr_t value,SIZE_T bytes,uint32_t*index){
    uint32_t left=0,right=region_count;while(left<right){uint32_t middle=left+(right-left)/2;if(regions[middle].base<=value)left=middle+1;else right=middle;}if(!left)return 0;left--;if(value<regions[left].base||value+bytes<value||value+bytes>regions[left].end)return 0;if(index)*index=left;return 1;
}
/* Read optional live pointers through the OS so absent contracts never form
 * a null memcpy source, even when the compiler folds template constants. */
static int read_live_pointer(uintptr_t base,SIZE_T offset,uintptr_t*value){
    SIZE_T copied=0;
    if(!value)return 0;
    *value=0;
    if(!base||offset>UINTPTR_MAX-base||!region_for(base+offset,sizeof(*value),NULL))return 0;
    return ReadProcessMemory(GetCurrentProcess(),(const void*)(base+offset),value,sizeof(*value),&copied)&&copied==sizeof(*value);
}
static void record_literal_decode_sample(uint32_t stage,uint32_t source,uint32_t destination,uint32_t encoded,uint32_t value,uintptr_t pointer,uint32_t span,const unsigned char*raw,uint32_t raw_count,const unsigned char*decoded,uint32_t decoded_count){
    if(literal_decode_sample_count>=16u)return;
    literal_decode_sample*sample=&literal_decode_samples[literal_decode_sample_count++];
    memset(sample,0,sizeof(*sample));
    sample->stage=stage;sample->source=source;sample->destination=destination;
    sample->encoded=encoded;sample->value=value;sample->pointer=pointer;sample->span=span;
    sample->readable=pointer&&region_for(pointer,1u,NULL)?1u:0u;
    if(raw&&raw_count){sample->raw_count=raw_count<16u?raw_count:16u;memcpy(sample->raw,raw,sample->raw_count);}
    if(decoded&&decoded_count){sample->decoded_count=decoded_count<16u?decoded_count:16u;memcpy(sample->decoded,decoded,sample->decoded_count);}
}
static void write_literal_decode_probe(void){
    FILE*output=_wfopen(decode_probe_path,L"wb");if(!output)return;
    fprintf(output,"{\n  \"schema\": \"alpha.runtime-string-literal-decode-probe/v1\",\n  \"stage\": %u,\n  \"domain\": %llu,\n  \"boundary\": {\"prefix_nulls\": %llu, \"prefix_strings\": %llu, \"suffix_foreign\": %llu, \"witness_classes\": [%llu, %llu, %llu]},\n  \"totals\": {\"records\": %llu, \"seen\": %llu, \"entry_unreadable\": %llu, \"pointer_unreadable\": %llu, \"empty_text\": %llu, \"utf8_invalid\": %llu, \"decoded\": %llu, \"source_equals_destination\": %llu},\n",
        literal_decode_probe_stage,
        (unsigned long long)literal_decode_domain,
        (unsigned long long)boundary_prefix_nulls,(unsigned long long)boundary_prefix_strings,(unsigned long long)boundary_suffix_foreign,
        (unsigned long long)boundary_witness_classes[0],(unsigned long long)boundary_witness_classes[1],(unsigned long long)boundary_witness_classes[2],
        (unsigned long long)literal_decode_totals[0],(unsigned long long)literal_decode_totals[1],(unsigned long long)literal_decode_totals[2],(unsigned long long)literal_decode_totals[3],(unsigned long long)literal_decode_totals[4],(unsigned long long)literal_decode_totals[5],(unsigned long long)literal_decode_totals[6],(unsigned long long)literal_decode_totals[7]);
    fprintf(output,"  \"referenced\": {\"maximum\": %llu, \"beyond_domain\": %llu},\n",
        (unsigned long long)literal_decode_referenced,(unsigned long long)literal_decode_referenced_beyond);
    fprintf(output,"  \"samples\": [");
    for(uint32_t i=0;i<literal_decode_sample_count;i++){
        const literal_decode_sample*c=&literal_decode_samples[i];
        fprintf(output,"%s{\"stage\": %u, \"source\": %u, \"destination\": %u, \"encoded\": %u, \"value\": %u, \"pointer\": %llu, \"span\": %u, \"readable\": %u, \"raw\": [",i?", ":"",c->stage,c->source,c->destination,c->encoded,c->value,(unsigned long long)c->pointer,c->span,c->readable);
        for(uint32_t j=0;j<c->raw_count;j++)fprintf(output,"%s%u",j?", ":"",(unsigned)c->raw[j]);
        fprintf(output,"], \"decoded\": [");
        for(uint32_t j=0;j<c->decoded_count;j++)fprintf(output,"%s%u",j?", ":"",(unsigned)c->decoded[j]);
        fprintf(output,"]}");
    }
    fprintf(output,"]\n}\n");
    fclose(output);_wchmod(decode_probe_path,0600);
}
static int string_pointer(uintptr_t object,uint32_t*length){
    if(!object||(object&7u)||!region_for(object,20u,NULL))return 0;uintptr_t klass=0;int32_t size=0;memcpy(&klass,(const void*)object,8u);if(klass!=string_class)return 0;memcpy(&size,(const void*)(object+16u),4u);if(size<0||(uint32_t)size>ALPHA_MAX_UTF16_LENGTH||(size&&!region_for(object+20u,(SIZE_T)(uint32_t)size*2u,NULL)))return 0;if(length)*length=(uint32_t)size;return 1;
}
static int executable_sections(HMODULE image,IMAGE_SECTION_HEADER**first,uint16_t*count){
    if(!image||!first||!count)return 0;
    IMAGE_DOS_HEADER*dos=(IMAGE_DOS_HEADER*)image;
    if(dos->e_magic!=IMAGE_DOS_SIGNATURE||dos->e_lfanew<=0||
       (uint64_t)(uint32_t)dos->e_lfanew+sizeof(IMAGE_NT_HEADERS64)>expected_image_bytes)return 0;
    IMAGE_NT_HEADERS64*nt=(IMAGE_NT_HEADERS64*)((uintptr_t)image+(uint32_t)dos->e_lfanew);
    if(nt->Signature!=IMAGE_NT_SIGNATURE||nt->OptionalHeader.Magic!=IMAGE_NT_OPTIONAL_HDR64_MAGIC||
       nt->OptionalHeader.SizeOfImage!=expected_image_bytes||!nt->FileHeader.NumberOfSections)return 0;
    *first=IMAGE_FIRST_SECTION(nt);*count=nt->FileHeader.NumberOfSections;return 1;
}
static int function_bounds(uintptr_t address,uintptr_t*begin,uintptr_t*end){
    DWORD64 base=0;PRUNTIME_FUNCTION runtime=RtlLookupFunctionEntry((DWORD64)address,&base,NULL);
    if(!runtime||base!=expected_image_base)return 0;
    uintptr_t lower=(uintptr_t)base+runtime->BeginAddress,upper=(uintptr_t)base+runtime->EndAddress;
    if(lower<expected_image_base||upper<=lower||upper>expected_image_base+expected_image_bytes||
       address<lower||address>=upper)return 0;
    *begin=lower;*end=upper;return 1;
}
static int rip_target(uintptr_t instruction,uint32_t bytes,uintptr_t*target){
    int32_t displacement=0;if(!region_for(instruction,bytes,NULL)||bytes<5u)return 0;
    memcpy(&displacement,(const void*)(instruction+bytes-4u),4u);
    uintptr_t value=instruction+bytes+(intptr_t)displacement;
    if(value<expected_image_base||value>=expected_image_base+expected_image_bytes)return 0;
    *target=value;return 1;
}
static int case_root(uintptr_t target,uintptr_t*global,uint32_t*field){
    if(!region_for(target,32u,NULL))return 0;
    const unsigned char*p=(const unsigned char*)target;
    for(uint32_t i=0;i+11u<=32u;i++){
        if(p[i]!=0x48||p[i+1]!=0x8b||(p[i+2]&0xc7u)!=0x05u)continue;uint32_t reg=(p[i+2]>>3u)&7u;
        uintptr_t root_global=0;if(!rip_target(target+i,7u,&root_global)||!region_for(root_global,8u,NULL))continue;
        uint32_t cursor=i+7u,selector=0;
        unsigned char direct=(unsigned char)((reg<<3u)|reg),disp8=(unsigned char)(0x40u|direct),disp32=(unsigned char)(0x80u|direct);
        if(cursor+3u<=32u&&p[cursor]==0x48&&p[cursor+1]==0x8b&&p[cursor+2]==direct)selector=0;
        else if(cursor+4u<=32u&&p[cursor]==0x48&&p[cursor+1]==0x8b&&p[cursor+2]==disp8)selector=p[cursor+3];
        else if(cursor+7u<=32u&&p[cursor]==0x48&&p[cursor+1]==0x8b&&p[cursor+2]==disp32)memcpy(&selector,p+cursor+3u,4u);
        else continue;
        *global=root_global;*field=selector;return 1;
    }
    return 0;
}
static int parse_generic_record_contract(uintptr_t resolver,usage_pair_contract*contract){
    uintptr_t begin=0,end=0;if(!function_bounds(resolver,&begin,&end)||resolver!=begin||end-begin<128u||end-begin>8192u)return 0;uintptr_t dispatch_limit=begin+96u;if(dispatch_limit>end)dispatch_limit=end;uintptr_t jump_table=0;uint32_t entry_count=0,dispatches=0;
    for(uintptr_t p=begin;p+24u<=dispatch_limit;p++){const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x0f||b[1]!=0xbe||b[2]!=0x49||memcmp(b+4,"\x31\xc0\xff\xc9\x83\xf9",6u))continue;uint32_t maximum=b[10];for(uintptr_t q=p+11u;q+7u<=dispatch_limit&&q<p+40u;q++){const unsigned char*c=(const unsigned char*)q;if(c[0]==0x48&&c[1]==0x8d&&c[2]==0x35&&rip_target(q,7u,&jump_table)){entry_count=maximum+1u;dispatches++;break;}}}
    if(dispatches!=1u||entry_count<0x15u||!region_for(jump_table,(SIZE_T)entry_count*4u,NULL))return 0;int32_t relative=0;memcpy(&relative,(const void*)(jump_table+(0x15u-1u)*4u),4u);uintptr_t handler=jump_table+(intptr_t)relative;if(handler<begin||handler>=end)return 0;uintptr_t limit=handler+64u;if(limit>end)limit=end;uint32_t matches=0;uintptr_t selected_global=0;uint32_t selected_field=0,selected_shift=0;
    for(uintptr_t p=handler;p+18u<=limit;p++){const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x48||b[1]!=0x8b||b[2]!=0x05||b[7]!=0x48||b[8]!=0x63||b[9]!=0x0f||memcmp(b+10,"\x48\xc1\xe1",3u)||b[14]!=0x48||b[15]!=0x03||b[16]!=0x48)continue;uint32_t shift=b[13],field=b[17];uintptr_t global=0;if(shift<3u||shift>8u||field>4096u||!rip_target(p,7u,&global)||!region_for(global,8u,NULL))continue;selected_global=global;selected_field=field;selected_shift=shift;matches++;}
    if(matches!=1u)return 0;uintptr_t state=0,base=0;memcpy(&state,(const void*)selected_global,8u);if(!state||!region_for(state+selected_field,8u,NULL))return 0;memcpy(&base,(const void*)(state+selected_field),8u);if(!base||!region_for(base,32u,NULL))return 0;contract->type_resolver=resolver;contract->generic_state_global=selected_global;contract->generic_record_base=base;contract->generic_state_field=selected_field;contract->generic_record_shift=selected_shift;return 1;
}
/* Decode the ModRM displacement of add rcx,[rax+field]. The zero,
 * signed-byte and signed-dword forms encode the same table lookup. */
static int parse_rcx_table_add(const unsigned char*code,const unsigned char*end,uint32_t*field,uint32_t*bytes){
    if((SIZE_T)(end-code)<3u||code[0]!=0x48||code[1]!=0x03)return 0;
    int32_t offset=0;
    if(code[2]==0x08){*bytes=3u;}
    else if(code[2]==0x48){if((SIZE_T)(end-code)<4u)return 0;offset=(int8_t)code[3];*bytes=4u;}
    else if(code[2]==0x88){if((SIZE_T)(end-code)<7u)return 0;memcpy(&offset,code+3u,4u);*bytes=7u;}
    else return 0;
    if(offset<0||offset>4096)return 0;
    *field=(uint32_t)offset;return 1;
}
static int parse_type_record_helper(uintptr_t helper,usage_pair_contract*contract){
    uintptr_t begin=0,end=0;if(!function_bounds(helper,&begin,&end)||helper!=begin||end-begin<64u||end-begin>2048u)return 0;uintptr_t limit=begin+128u;if(limit>end)limit=end;uint32_t matches=0;uintptr_t selected_global=0,selected_resolver=0;uint32_t selected_field=0,selected_shift=0;
    for(uintptr_t p=begin;p+22u<=limit;p++){const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x48||b[1]!=0x8b||b[2]!=0x05||memcmp(b+7,"\x48\x89\xf9\x48\xc1\xe1",6u))continue;uint32_t shift=b[13],field=0,bytes=0;if(shift<3u||shift>6u||!parse_rcx_table_add(b+14u,(const unsigned char*)limit,&field,&bytes))continue;bytes+=14u;uintptr_t global=0;if(!bytes||field>4096u||p+bytes+5u>limit||b[bytes]!=0xe8||!rip_target(p,7u,&global)||!region_for(global,8u,NULL))continue;int32_t displacement=0;memcpy(&displacement,b+bytes+1u,4u);uintptr_t resolver=p+bytes+5u+(intptr_t)displacement;if(resolver<expected_image_base||resolver>=expected_image_base+expected_image_bytes)continue;selected_global=global;selected_field=field;selected_shift=shift;selected_resolver=resolver;matches++;}
    if(matches!=1u)return 0;uintptr_t state=0,base=0;memcpy(&state,(const void*)selected_global,8u);if(!state||!region_for(state+selected_field,8u,NULL))return 0;memcpy(&base,(const void*)(state+selected_field),8u);if(!base||base<expected_image_base||base>=expected_image_base+expected_image_bytes||!region_for(base,16u,NULL))return 0;contract->type_helper=helper;contract->type_state_global=selected_global;contract->type_record_base=base;contract->type_state_field=selected_field;contract->type_record_shift=selected_shift;return parse_generic_record_contract(selected_resolver,contract);
}

static int parse_generic_record_contract_type_code_arm(uintptr_t resolver,usage_pair_contract*contract){
    uintptr_t begin=0,end=0;if(!function_bounds(resolver,&begin,&end)||resolver!=begin||end-begin<128u||end-begin>8192u)return 0;uintptr_t dispatch_limit=begin+96u;if(dispatch_limit>end)dispatch_limit=end;uintptr_t jump_table=0;uint32_t dispatches=0;
    for(uintptr_t p=begin;p+18u<=dispatch_limit;p++){const unsigned char*b=(const unsigned char*)p;if(memcmp(b,"\x0f\xbe\x49\x0a\x31\xc0\xff\xc9\x83\xf9",10u))continue;for(uintptr_t q=p+10u;q+7u<=dispatch_limit&&q<p+40u;q++){const unsigned char*c=(const unsigned char*)q;if(c[0]==0x48&&c[1]==0x8d&&c[2]==0x35&&rip_target(q,7u,&jump_table)){dispatches++;break;}}}
    if(dispatches!=1u||!region_for(jump_table,(SIZE_T)0x15u*4u,NULL))return 0;int32_t relative=0;memcpy(&relative,(const void*)(jump_table+(0x15u-1u)*4u),4u);uintptr_t handler=jump_table+(intptr_t)relative;if(handler<begin||handler>=end)return 0;uintptr_t limit=handler+48u;if(limit>end)limit=end;uint32_t matches=0;uintptr_t selected_global=0;uint32_t selected_field=0,selected_shift=0;
    for(uintptr_t p=handler;p+18u<=limit;p++){const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x48||b[1]!=0x8b||b[2]!=0x05||b[7]!=0x48||b[8]!=0x63||b[9]!=0x0f||memcmp(b+10,"\x48\xc1\xe1",3u)||b[14]!=0x48||b[15]!=0x03||b[16]!=0x48)continue;uint32_t shift=b[13],field=b[17];uintptr_t global=0;if(shift<3u||shift>8u||field>4096u||!rip_target(p,7u,&global)||!region_for(global,8u,NULL))continue;selected_global=global;selected_field=field;selected_shift=shift;matches++;}
    if(matches!=1u)return 0;uintptr_t state=0,base=0;memcpy(&state,(const void*)selected_global,8u);if(!state||!region_for(state+selected_field,8u,NULL))return 0;memcpy(&base,(const void*)(state+selected_field),8u);if(!base||!region_for(base,32u,NULL))return 0;contract->type_resolver=resolver;contract->generic_state_global=selected_global;contract->generic_record_base=base;contract->generic_state_field=selected_field;contract->generic_record_shift=selected_shift;return 1;
}
static int parse_type_record_helper_wide_field(uintptr_t helper,usage_pair_contract*contract){
    uintptr_t begin=0,end=0;if(!function_bounds(helper,&begin,&end)||helper!=begin||end-begin<64u||end-begin>2048u)return 0;uintptr_t limit=begin+160u;if(limit>end)limit=end;uint32_t matches=0;uintptr_t selected_global=0,selected_resolver=0;uint32_t selected_field=0,selected_shift=0;
    for(uintptr_t p=begin;p+26u<=limit;p++){const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x48||b[1]!=0x8b||b[2]!=0x05||memcmp(b+7,"\x48\x89\xf9\x48\xc1\xe1",6u)||b[14]!=0x48||b[15]!=0x03||b[16]!=0x88||b[21]!=0xe8)continue;uint32_t shift=b[13],field=0;if(shift<3u||shift>6u)continue;memcpy(&field,b+17u,4u);uintptr_t global=0;if(field>4096u||!rip_target(p,7u,&global)||!region_for(global,8u,NULL))continue;int32_t displacement=0;memcpy(&displacement,b+22u,4u);uintptr_t resolver=p+26u+(intptr_t)displacement;if(resolver<expected_image_base||resolver>=expected_image_base+expected_image_bytes)continue;selected_global=global;selected_field=field;selected_shift=shift;selected_resolver=resolver;matches++;}
    if(matches!=1u)return 0;uintptr_t state=0,base=0;memcpy(&state,(const void*)selected_global,8u);if(!state||!region_for(state+selected_field,8u,NULL))return 0;memcpy(&base,(const void*)(state+selected_field),8u);if(!base||base<expected_image_base||base>=expected_image_base+expected_image_bytes||!region_for(base,16u,NULL))return 0;contract->type_helper=helper;contract->type_state_global=selected_global;contract->type_record_base=base;contract->type_state_field=selected_field;contract->type_record_shift=selected_shift;return parse_generic_record_contract_type_code_arm(selected_resolver,contract);
}
static int derive_type_record_contract(uintptr_t case1,uintptr_t function_end,usage_pair_contract*contract){
    uintptr_t limit=case1+128u;if(limit<case1||limit>function_end)limit=function_end;uintptr_t helper=0;uint32_t matches=0;for(uintptr_t p=case1;p+7u<=limit;p++){const unsigned char*b=(const unsigned char*)p;if(b[0]!=0xb2||b[1]!=0x01||b[2]!=0xe8)continue;int32_t displacement=0;memcpy(&displacement,b+3u,4u);uintptr_t target=p+7u+(intptr_t)displacement;if(target<expected_image_base||target>=expected_image_base+expected_image_bytes||target==helper)continue;usage_pair_contract candidate=*contract;if(!parse_type_record_helper(target,&candidate)&&!parse_type_record_helper_wide_field(target,&candidate))continue;if(helper&&helper!=target)return 0;*contract=candidate;helper=target;matches++;}return matches==1u&&helper==contract->type_helper;
}
static int add_signed_offset(uintptr_t base,int64_t offset,uintptr_t*result){
    if((offset>=0&&(uint64_t)offset>UINTPTR_MAX-base)||(offset<0&&(uint64_t)(-(offset+1))+1u>base))return 0;
    *result=offset>=0?base+(uintptr_t)offset:base-(uintptr_t)(-(offset+1))-1u;return 1;
}
static int derive_decoder_globals(uintptr_t begin,decoder_contract*contract){
    uint32_t descriptor_count=0,base_count=0;uintptr_t limit=begin+128u;
    for(uintptr_t p=begin;p+7u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;uintptr_t target=0;
        if((b[0]==0x48||b[0]==0x4c)&&b[1]==0x8b&&b[2]==0x15&&rip_target(p,7u,&target)){contract->descriptor_global=target;descriptor_count++;}

        if(b[0]==0x4c&&b[1]==0x8b&&(b[2]==0x25||b[2]==0x2d)&&rip_target(p,7u,&target)){contract->metadata_base_global=target;base_count++;}
    }
    return descriptor_count==1u&&base_count==1u&&contract->descriptor_global!=contract->metadata_base_global;
}

static int parse_usage_pair_contract_direct(uintptr_t begin,uintptr_t end,const decoder_contract*literal_contract,usage_pair_contract*contract){
    uintptr_t limit=begin+1024u;if(limit<begin||limit>end)limit=end;uint32_t matches=0;usage_pair_contract selected={0};
    for(uintptr_t p=begin;p+80u<=limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;usage_pair_contract candidate={0};uint64_t multiplier=0,add=0;uint32_t key_multiplier=0,selector_field=0,selector_xor=0,encoded_add=0,destination_xor=0,destination_add=0;uint8_t index_shift=0,key_shift=0;
#define DIRECT_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto direct_mismatch;cursor+=amount;}while(0)
#define DIRECT_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto direct_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
        DIRECT_LITERAL("\x44\x89\xf1\x48\x89\xc8\x49\x0f\xaf\xc0\x4c\x01\xc8\x48\xc1\xe8");if(cursor>=finish)goto direct_mismatch;index_shift=*cursor++;
        DIRECT_LITERAL("\x48\x69\xd8");DIRECT_U32(key_multiplier);DIRECT_LITERAL("\x48\xc1\xeb");if(cursor>=finish)goto direct_mismatch;key_shift=*cursor++;
        DIRECT_LITERAL("\x48\x63\x72");if(cursor>=finish)goto direct_mismatch;selector_field=*cursor++;DIRECT_LITERAL("\x48\x81\xf6");DIRECT_U32(selector_xor);
        DIRECT_LITERAL("\x4c\x01\xe6\x8b\x04\xce\x29\xd8\x05");DIRECT_U32(encoded_add);
        DIRECT_LITERAL("\x89\xc7\xc1\xef\x1d\x83\xff\x07");

        int found=0;for(;cursor+12u<=finish&&cursor<(const unsigned char*)p+160u;cursor++){if(!memcmp(cursor,"\x8b\x74\xce\x04\x44\x31\xd6\x29\xde\x81\xc6",11u)){cursor+=11u;DIRECT_U32(destination_add);found=1;break;}}
        if(!found||selector_field>4096u||index_shift>=64u||key_shift>=64u||!key_multiplier)goto direct_mismatch;


        uintptr_t setup=begin;int got=0;for(uintptr_t q=begin;q+32u<=p;q++){const unsigned char*b=(const unsigned char*)q;if(b[0]!=0x49||b[1]!=0xb8)continue;memcpy(&multiplier,b+2u,8u);if(b[10]!=0x49||b[11]!=0xb9)continue;memcpy(&add,b+12u,8u);if(b[20]!=0x41||b[21]!=0xba)continue;memcpy(&destination_xor,b+22u,4u);setup=q;got=1;}
        if(!got||setup>=p||!multiplier)goto direct_mismatch;
        candidate.direct_index_multiplier=multiplier;candidate.direct_index_add=add;candidate.direct_key_multiplier=key_multiplier;candidate.direct_index_shift=index_shift;candidate.direct_key_shift=key_shift;candidate.direct_selector_field=selector_field;candidate.direct_selector_xor=selector_xor;candidate.direct_encoded_add=encoded_add;candidate.direct_destination_xor=destination_xor;candidate.direct_destination_add=destination_add;candidate.usage_codec=2u;
        if(!literal_contract->descriptor||!literal_contract->metadata_base||!region_for(literal_contract->descriptor+(SIZE_T)selector_field,4u,NULL))goto direct_mismatch;int32_t raw=0;memcpy(&raw,(const void*)(literal_contract->descriptor+selector_field),4u);int64_t offset=(int64_t)(((uint64_t)(int64_t)raw)^((uint64_t)(int64_t)(int32_t)selector_xor));if(!add_signed_offset(literal_contract->metadata_base,offset,&candidate.direct_pair_base)||!region_for(candidate.direct_pair_base,8192u,NULL))goto direct_mismatch;candidate.range_base=candidate.direct_pair_base;candidate.pair_base=candidate.direct_pair_base;selected=candidate;matches++;
direct_mismatch:;
#undef DIRECT_U32
#undef DIRECT_LITERAL
    }
    if(matches!=1u)return 0;*contract=selected;return 1;
}
static int parse_usage_pair_contract_affine(uintptr_t begin,uintptr_t end,const decoder_contract*literal_contract,usage_pair_contract*contract){
    uintptr_t limit=begin+512u;if(limit<begin||limit>end)limit=end;
    uint32_t matches=0;usage_pair_contract selected={0};
    for(uintptr_t p=begin;p+64u<=limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;
        usage_pair_contract candidate={0};
        if(cursor[0]!=0x48||cursor[1]!=0x63||cursor[2]!=0x4a)continue;
#define PAIR_AFFINE_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto affine_pair_mismatch;cursor+=amount;}while(0)
#define PAIR_AFFINE_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto affine_pair_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
        PAIR_AFFINE_LITERAL("\x48\x63\x4a");candidate.direct_selector_field=*cursor++;
        PAIR_AFFINE_LITERAL("\x48\x81\xf1");PAIR_AFFINE_U32(candidate.direct_selector_xor);
        PAIR_AFFINE_LITERAL("\x4c\x01\xe1\x44\x89\xf7\x48\x89\xf8\x49\x0f\xaf\xc0\x4c\x01\xc8\x48\xc1\xe8");
        if(cursor>=finish)goto affine_pair_mismatch;candidate.direct_index_shift=*cursor++;
        PAIR_AFFINE_LITERAL("\x69\xf0");PAIR_AFFINE_U32(candidate.direct_key_multiplier);
        PAIR_AFFINE_LITERAL("\x81\xc6");PAIR_AFFINE_U32(candidate.direct_key_add);
        PAIR_AFFINE_LITERAL("\x8b\x04\xf9\x31\xf0\x35");PAIR_AFFINE_U32(candidate.direct_encoded_xor);
        PAIR_AFFINE_LITERAL("\x89\xc3\xc1\xeb\x1d\x83\xfb\x07");
        {const unsigned char destination[]={0x8b,0x4c,0xf9,0x04,0x44,0x01,0xd1,0x31,0xce};int found=0;
        for(const unsigned char*q=cursor;q+sizeof(destination)<=finish&&q<cursor+96u;q++)if(!memcmp(q,destination,sizeof(destination))){found=1;break;}
        if(!found)goto affine_pair_mismatch;}
        if(candidate.direct_selector_field>4096u||candidate.direct_index_shift>=64u||!candidate.direct_key_multiplier)goto affine_pair_mismatch;
        {uint32_t setups=0;for(uintptr_t q=begin;q+28u<=p;q++){
            const unsigned char*b=(const unsigned char*)q;
            if(b[0]!=0x49||b[1]!=0xb8||b[10]!=0x49||b[11]!=0xb9||b[20]!=0x41||b[21]!=0xba)continue;
            uint64_t multiplier=0,add=0;uint32_t destination_add=0;
            memcpy(&multiplier,b+2u,8u);memcpy(&add,b+12u,8u);memcpy(&destination_add,b+22u,4u);
            if(setups&&(candidate.direct_index_multiplier!=multiplier||candidate.direct_index_add!=add||candidate.direct_destination_add!=destination_add))goto affine_pair_mismatch;
            candidate.direct_index_multiplier=multiplier;candidate.direct_index_add=add;candidate.direct_destination_add=destination_add;
            setups++;
        }if(!setups||!candidate.direct_index_multiplier)goto affine_pair_mismatch;}
        if(!literal_contract->descriptor||!literal_contract->metadata_base||
           !region_for(literal_contract->descriptor+candidate.direct_selector_field,4u,NULL))goto affine_pair_mismatch;
        {int32_t raw=0;int64_t offset=0;memcpy(&raw,(const void*)(literal_contract->descriptor+candidate.direct_selector_field),4u);
        offset=(int64_t)(((uint64_t)(int64_t)raw)^((uint64_t)(int64_t)(int32_t)candidate.direct_selector_xor));
        if(!add_signed_offset(literal_contract->metadata_base,offset,&candidate.direct_pair_base)||
           !region_for(candidate.direct_pair_base,8192u,NULL))goto affine_pair_mismatch;}
        candidate.range_base=candidate.direct_pair_base;candidate.pair_base=candidate.direct_pair_base;
        candidate.usage_codec=4u;selected=candidate;matches++;
affine_pair_mismatch:;
#undef PAIR_AFFINE_U32
#undef PAIR_AFFINE_LITERAL
    }
    if(matches!=1u)return 0;*contract=selected;return 1;
}
static int parse_usage_pair_contract_ranged_mix(uintptr_t begin,uintptr_t end,usage_pair_contract*contract){
    uintptr_t limit=begin+512u;if(limit<begin||limit>end)limit=end;uint32_t matches=0;usage_pair_contract selected={0};
    for(uintptr_t p=begin;p+160u<=limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;usage_pair_contract candidate={0};uint32_t second_index_multiplier=0,second_mix_xor=0,second_mix_multiplier=0,second_mid_multiplier=0,second_final_multiplier=0,boundary_bias=0,boundary_bias_copy=0;uint64_t second_wide_add=0;uint8_t second_first_shift=0,second_second_shift=0,second_third_shift=0;
#define RANGED_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto ranged_mismatch;cursor+=amount;}while(0)
#define RANGED_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto ranged_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
#define RANGED_U64(value) do{if((SIZE_T)(finish-cursor)<8u)goto ranged_mismatch;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
        RANGED_LITERAL("\x49\x63\x82");RANGED_U32(candidate.range_selector_field);
        RANGED_LITERAL("\x48\x35");RANGED_U32(candidate.range_selector_xor);
        RANGED_LITERAL("\x89\xcb\x4c\x8b\x2d");if((SIZE_T)(finish-cursor)<4u)goto ranged_mismatch;cursor+=4u;
        RANGED_LITERAL("\x4c\x01\xe8\x48\x69\xfb");RANGED_U32(candidate.range_index_multiplier);
        RANGED_LITERAL("\x48\x81\xf7");RANGED_U32(candidate.range_mix_xor);
        RANGED_LITERAL("\x48\x69\xff");RANGED_U32(candidate.range_mix_multiplier);
        RANGED_LITERAL("\x48\xc1\xef");if(cursor>=finish)goto ranged_mismatch;candidate.range_first_shift=*cursor++;
        RANGED_LITERAL("\x48\x69\xff");RANGED_U32(candidate.range_mid_multiplier);
        RANGED_LITERAL("\x49\xb8");RANGED_U64(candidate.range_wide_add);
        RANGED_LITERAL("\x4c\x01\xc7\x48\xc1\xef");if(cursor>=finish)goto ranged_mismatch;candidate.range_second_shift=*cursor++;
        RANGED_LITERAL("\x48\x69\xff");RANGED_U32(candidate.range_final_multiplier);
        RANGED_LITERAL("\x48\xc1\xef");if(cursor>=finish)goto ranged_mismatch;candidate.range_third_shift=*cursor++;
        RANGED_LITERAL("\xff\xc1\x48\x69\xf1");RANGED_U32(second_index_multiplier);
        RANGED_LITERAL("\x48\x81\xf6");RANGED_U32(second_mix_xor);
        RANGED_LITERAL("\x48\x69\xf6");RANGED_U32(second_mix_multiplier);
        RANGED_LITERAL("\x48\xc1\xee");if(cursor>=finish)goto ranged_mismatch;second_first_shift=*cursor++;
        RANGED_LITERAL("\x48\x69\xf6");RANGED_U32(second_mid_multiplier);
        RANGED_LITERAL("\x4c\x01\xc6\x48\xc1\xee");if(cursor>=finish)goto ranged_mismatch;second_second_shift=*cursor++;
        RANGED_LITERAL("\x48\x69\xf6");RANGED_U32(second_final_multiplier);
        RANGED_LITERAL("\x48\xc1\xee");if(cursor>=finish)goto ranged_mismatch;second_third_shift=*cursor++;
        RANGED_LITERAL("\x44\x8b\x3c\x98\x41\x29\xff\x41\xbe");RANGED_U32(boundary_bias);
        RANGED_LITERAL("\x44\x03\x34\x88\x41\x8d\x04\x37\x05");RANGED_U32(boundary_bias_copy);
        RANGED_LITERAL("\x41\x29\xc6");
        if(candidate.range_selector_field>4096u||!candidate.range_index_multiplier||!candidate.range_mix_multiplier||!candidate.range_mid_multiplier||!candidate.range_final_multiplier||candidate.range_first_shift>=64u||candidate.range_second_shift>=64u||candidate.range_third_shift>=64u||second_index_multiplier!=candidate.range_index_multiplier||second_mix_xor!=candidate.range_mix_xor||second_mix_multiplier!=candidate.range_mix_multiplier||second_first_shift!=candidate.range_first_shift||second_mid_multiplier!=candidate.range_mid_multiplier||second_second_shift!=candidate.range_second_shift||second_final_multiplier!=candidate.range_final_multiplier||second_third_shift!=candidate.range_third_shift||second_wide_add!=0u||boundary_bias!=boundary_bias_copy)goto ranged_mismatch;
        {
            uintptr_t pair_limit=begin+768u;if(pair_limit<begin||pair_limit>end)pair_limit=end;uint32_t pair_matches=0;
            for(uintptr_t q=(uintptr_t)cursor;q+80u<=pair_limit;q++){
                const unsigned char*pair=(const unsigned char*)q,*pair_finish=(const unsigned char*)pair_limit;usage_pair_contract pair_candidate=candidate;uint32_t source_mask=0;
#define PAIR_MIX_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(pair_finish-pair)<amount||memcmp(pair,pattern,amount))goto pair_mix_mismatch;pair+=amount;}while(0)
#define PAIR_MIX_U32(value) do{if((SIZE_T)(pair_finish-pair)<4u)goto pair_mix_mismatch;memcpy(&(value),pair,4u);pair+=4u;}while(0)
                PAIR_MIX_LITERAL("\x41\x81\xc7");PAIR_MIX_U32(pair_candidate.range_final_add);
                PAIR_MIX_LITERAL("\x49\xf7\xde\x45\x69\xe7");PAIR_MIX_U32(pair_candidate.pair_index_multiplier);
                for(;pair+96u<=pair_finish&&pair<(const unsigned char*)q+160u;pair++)if(!memcmp(pair,"\x44\x89\xe0\x35",4u))break;
                PAIR_MIX_LITERAL("\x44\x89\xe0\x35");PAIR_MIX_U32(pair_candidate.pair_index_xor);
                PAIR_MIX_LITERAL("\x69\xf0");PAIR_MIX_U32(pair_candidate.pair_mix_multiplier);
                PAIR_MIX_LITERAL("\x49\x63\x4a");if(pair>=pair_finish)goto pair_mix_mismatch;pair_candidate.pair_selector_field=*pair++;
                PAIR_MIX_LITERAL("\x48\x81\xf1");PAIR_MIX_U32(pair_candidate.pair_selector_add);
                PAIR_MIX_LITERAL("\x4c\x01\xe9\x44\x89\xfb\x8b\x04\xd9\x31\xf0\x89\xc7\xc1\xef\x1d\x83\xff\x07");
                for(;pair+24u<=pair_finish&&pair<(const unsigned char*)q+192u;pair++)if(!memcmp(pair,"\x33\x74\xd9\x04\x81\xf6",6u))break;
                PAIR_MIX_LITERAL("\x33\x74\xd9\x04\x81\xf6");PAIR_MIX_U32(pair_candidate.pair_destination_xor);
                PAIR_MIX_LITERAL("\x89\xc1\x81\xe1");PAIR_MIX_U32(source_mask);
                PAIR_MIX_LITERAL("\x81\xf1");PAIR_MIX_U32(pair_candidate.pair_source_xor);
                if(pair_candidate.pair_selector_field>4096u||!pair_candidate.pair_index_multiplier||!pair_candidate.pair_mix_multiplier||source_mask!=0x1fffffffu)goto pair_mix_mismatch;
                candidate=pair_candidate;pair_matches++;
pair_mix_mismatch:;
#undef PAIR_MIX_U32
#undef PAIR_MIX_LITERAL
            }
            if(pair_matches!=1u)goto ranged_mismatch;
        }
        candidate.usage_codec=3u;selected=candidate;matches++;
ranged_mismatch:;
#undef RANGED_U64
#undef RANGED_U32
#undef RANGED_LITERAL
    }
    if(matches!=1u)return 0;*contract=selected;return 1;
}
static int parse_usage_pair_contract(uintptr_t begin,uintptr_t end,usage_pair_contract*contract){
    uintptr_t range_limit=begin+192u;if(range_limit>end)range_limit=end;uint32_t range_matches=0,pair_matches=0;usage_pair_contract selected={0};
    for(uintptr_t p=begin;p+64u<=range_limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)range_limit;usage_pair_contract candidate={0};uint32_t index2=0,xor2=0,multiplier2=0,second_xor2=0,add2=0;
#define RANGE_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto range_mismatch;cursor+=amount;}while(0)
#define RANGE_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto range_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
        RANGE_LITERAL("\x48\x63\x82");RANGE_U32(candidate.range_selector_field);
        RANGE_LITERAL("\x48\x35");RANGE_U32(candidate.range_selector_xor);
        RANGE_LITERAL("\x89\xcb\x4c\x8b\x2d");cursor+=4u;RANGE_LITERAL("\x4c\x01\xe8\x69\xf1");RANGE_U32(candidate.range_index_multiplier);
        RANGE_LITERAL("\x89\xf7\x81\xf7");RANGE_U32(candidate.range_mix_xor);
        RANGE_LITERAL("\x69\xff");RANGE_U32(candidate.range_mix_multiplier);
        RANGE_LITERAL("\x81\xf7");RANGE_U32(candidate.range_mix_second_xor);
        RANGE_LITERAL("\x81\xc7");RANGE_U32(candidate.range_mix_add);
        RANGE_LITERAL("\xff\xc1\x81\xc6");RANGE_U32(index2);
        RANGE_LITERAL("\x81\xf6");RANGE_U32(xor2);
        RANGE_LITERAL("\x69\xf6");RANGE_U32(multiplier2);
        RANGE_LITERAL("\x81\xf6");RANGE_U32(second_xor2);
        RANGE_LITERAL("\x81\xc6");RANGE_U32(add2);
        RANGE_LITERAL("\x41\xbe");RANGE_U32(candidate.range_final_add);
        if(candidate.range_selector_field<=4096u&&candidate.range_index_multiplier&&candidate.range_mix_multiplier&&index2==candidate.range_index_multiplier&&xor2==candidate.range_mix_xor&&multiplier2==candidate.range_mix_multiplier&&second_xor2==candidate.range_mix_second_xor&&add2==candidate.range_mix_add){selected=candidate;range_matches++;}
range_mismatch:;
#undef RANGE_U32
#undef RANGE_LITERAL
    }
    uintptr_t pair_limit=begin+1024u;if(pair_limit>end)pair_limit=end;
    for(uintptr_t p=begin;p+80u<=pair_limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)pair_limit;usage_pair_contract candidate=selected;
#define PAIR_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto pair_mismatch;cursor+=amount;}while(0)
#define PAIR_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto pair_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
        PAIR_LITERAL("\x44\x89\xf9\x48\x69\xc1");PAIR_U32(candidate.pair_index_multiplier);
        PAIR_LITERAL("\x48\x35");PAIR_U32(candidate.pair_index_xor);
        PAIR_LITERAL("\x48\x69\xc0");PAIR_U32(candidate.pair_mix_multiplier);
        PAIR_LITERAL("\x48\xc1\xe8");if(cursor>=finish)goto pair_mismatch;candidate.pair_shift=*cursor++;
        PAIR_LITERAL("\x48\x05");PAIR_U32(candidate.pair_mix_add);
        PAIR_LITERAL("\x48\x35");PAIR_U32(candidate.pair_mix_xor);
        PAIR_LITERAL("\x48\x69\xf8");PAIR_U32(candidate.pair_final_multiplier);
        PAIR_LITERAL("\x48\xc1\xef");if(cursor>=finish)goto pair_mismatch;candidate.pair_final_shift=*cursor++;
        PAIR_LITERAL("\x8b\x82");PAIR_U32(candidate.pair_selector_field);
        PAIR_LITERAL("\xbb");PAIR_U32(candidate.pair_selector_add);
        PAIR_LITERAL("\x01\xd8\x48\x63\xf0\x4c\x01\xee\x8b\x44\xce\x04\x29\xf8\x05");PAIR_U32(candidate.pair_encoded_add);
        for(;cursor+8u<=finish&&cursor<(const unsigned char*)p+96u;cursor++)if(!memcmp(cursor,"\x8b\x34\xce\x29\xfe\x81\xc6",7u)){cursor+=7u;PAIR_U32(candidate.pair_destination_add);break;}
        if(!candidate.pair_destination_add||candidate.pair_selector_field>4096u||!candidate.pair_index_multiplier||!candidate.pair_mix_multiplier||!candidate.pair_final_multiplier||candidate.pair_shift>=64u||candidate.pair_final_shift>=64u)goto pair_mismatch;
        selected=candidate;pair_matches++;
pair_mismatch:;
#undef PAIR_U32
#undef PAIR_LITERAL
    }
    if(range_matches!=1u||pair_matches!=1u)return 0;*contract=selected;return 1;
}
static int realize_usage_pair_contract(usage_pair_contract*contract,const decoder_contract*literal_contract){
    uint32_t maximum_field=contract->range_selector_field>contract->pair_selector_field?contract->range_selector_field:contract->pair_selector_field;
    if(!literal_contract->descriptor||!literal_contract->metadata_base||!region_for(literal_contract->descriptor,(SIZE_T)maximum_field+4u,NULL))return 0;
    int32_t range_raw=0,pair_raw=0;memcpy(&range_raw,(const void*)(literal_contract->descriptor+contract->range_selector_field),4u);memcpy(&pair_raw,(const void*)(literal_contract->descriptor+contract->pair_selector_field),4u);
    int64_t range_offset=(int64_t)(((uint64_t)(int64_t)range_raw)^((uint64_t)(int64_t)(int32_t)contract->range_selector_xor));
    int64_t pair_offset=contract->usage_codec==3u?(int64_t)(((uint64_t)(int64_t)pair_raw)^((uint64_t)(int64_t)(int32_t)contract->pair_selector_add)):(int64_t)(int32_t)((uint32_t)pair_raw+contract->pair_selector_add);
    return add_signed_offset(literal_contract->metadata_base,range_offset,&contract->range_base)&&add_signed_offset(literal_contract->metadata_base,pair_offset,&contract->pair_base)&&region_for(contract->range_base,8192u,NULL)&&region_for(contract->pair_base,8192u,NULL);
}
#define FAMILY_BYTES(value) do{const unsigned char pattern[]=value;SIZE_T n=sizeof(pattern)-1u;if((SIZE_T)(end-cursor)<n||memcmp(cursor,pattern,n))return 0;cursor+=n;}while(0)
#define FAMILY_U32(value) do{if((SIZE_T)(end-cursor)<4u)return 0;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
#define FAMILY_U64(value) do{if((SIZE_T)(end-cursor)<8u)return 0;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
#define FAMILY_U8(value) do{if(cursor>=end)return 0;(value)=*cursor++;}while(0)
static int parse_scalar_stream_mix(const unsigned char*cursor,const unsigned char*end,decoder_contract*contract){
    FAMILY_BYTES("\x49\xbb");
    FAMILY_U64(contract->stream_step);
    FAMILY_BYTES("\x44\x89\xc8");
    FAMILY_BYTES("\x48\xbb");
    FAMILY_U64(contract->stream_index_multiplier);
    FAMILY_BYTES("\x48\x0f\xaf\xd8");
    FAMILY_BYTES("\x48\xb8");
    FAMILY_U64(contract->stream_index_bias);
    FAMILY_BYTES("\x48\x31\xd8");
    FAMILY_BYTES("\x48\xbb");
    FAMILY_U64(contract->stream_mix_multiplier);
    FAMILY_BYTES("\x48\x0f\xaf\xd8");
    FAMILY_BYTES("\x48\xb8");
    FAMILY_U64(contract->stream_mix_add);
    FAMILY_BYTES("\x48\x01\xd8");
    FAMILY_BYTES("\x48\xbb");
    FAMILY_U64(contract->stream_final_xor);
    FAMILY_BYTES("\x48\x31\xc3");
    FAMILY_BYTES("\x48\xb8");
    FAMILY_U64(contract->stream_final_multiplier);
    FAMILY_BYTES("\x48\x0f\xaf\xc3");
    if(!contract->stream_step||!contract->stream_index_multiplier||!contract->stream_mix_multiplier||!contract->stream_final_multiplier)return 0;
    contract->stream_codec=4u;return 1;
}
#undef FAMILY_BYTES
#undef FAMILY_U32
#undef FAMILY_U64
#undef FAMILY_U8
static int parse_byte_decoder(uintptr_t target,decoder_contract*contract){
    uintptr_t begin=0,end=0;if(!function_bounds(target,&begin,&end)||begin!=target||end-begin<256u||end-begin>4096u)return 0;uintptr_t limit=begin+256u;if(limit>end)limit=end;uint32_t matches=0;
    for(uintptr_t p=begin;p+80u<=limit;p++){const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;if(cursor[0]!=0x49||cursor[1]!=0xbb)continue;decoder_contract candidate=*contract;
#define STREAM_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto stream_mismatch;cursor+=amount;}while(0)
#define STREAM_U64(value) do{if((SIZE_T)(finish-cursor)<8u)goto stream_mismatch;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
        STREAM_LITERAL("\x49\xbb");STREAM_U64(candidate.stream_step);
        STREAM_LITERAL("\x44\x89\xc8\x48\xbb");STREAM_U64(candidate.stream_index_multiplier);
        STREAM_LITERAL("\x48\x0f\xaf\xd8\x48\xb8");STREAM_U64(candidate.stream_index_bias);
        STREAM_LITERAL("\x48\x01\xd8\x48\xbb");STREAM_U64(candidate.stream_index_xor);
        STREAM_LITERAL("\x48\x31\xc3\x48\xb8");STREAM_U64(candidate.stream_final_multiplier);
        STREAM_LITERAL("\x48\x0f\xaf\xc3");
        if(!candidate.stream_step||!candidate.stream_index_multiplier||!candidate.stream_final_multiplier)goto stream_mismatch;candidate.stream_codec=1u;*contract=candidate;matches++;
stream_mismatch:;
    }
#undef STREAM_U64
#undef STREAM_LITERAL
    for(uintptr_t p=begin;p+96u<=limit;p++){const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;if(cursor[0]!=0x49||cursor[1]!=0xbb)continue;decoder_contract candidate=*contract;
#define MIXED_STREAM_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto mixed_stream_mismatch;cursor+=amount;}while(0)
#define MIXED_STREAM_U64(value) do{if((SIZE_T)(finish-cursor)<8u)goto mixed_stream_mismatch;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
        MIXED_STREAM_LITERAL("\x49\xbb");MIXED_STREAM_U64(candidate.stream_step);
        MIXED_STREAM_LITERAL("\x44\x89\xc8\x48\xbb");MIXED_STREAM_U64(candidate.stream_index_multiplier);
        MIXED_STREAM_LITERAL("\x48\x0f\xaf\xd8\x48\xb8");MIXED_STREAM_U64(candidate.stream_index_bias);
        MIXED_STREAM_LITERAL("\x48\x31\xd8\x48\xbb");MIXED_STREAM_U64(candidate.stream_mix_multiplier);
        MIXED_STREAM_LITERAL("\x48\x0f\xaf\xd8\x48\xbf");MIXED_STREAM_U64(candidate.stream_mix_add);
        MIXED_STREAM_LITERAL("\x48\x01\xdf\x48\xb8");MIXED_STREAM_U64(candidate.stream_final_xor);
        MIXED_STREAM_LITERAL("\x48\x31\xf8");
        if(!candidate.stream_step||!candidate.stream_index_multiplier||!candidate.stream_mix_multiplier){goto mixed_stream_mismatch;}candidate.stream_codec=2u;*contract=candidate;matches++;
mixed_stream_mismatch:;
    }
#undef MIXED_STREAM_U64
#undef MIXED_STREAM_LITERAL
    /* A vectorized decoder may keep the same affine qword key in an
       unrolled SIMD loop and in a scalar remainder loop.  Derive its
       constants from the scalar setup and require the scalar update. */
    for(uintptr_t p=begin;p+40u<=limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;
        decoder_contract candidate=*contract;
        if(cursor[0]!=0x49||cursor[1]!=0xbb)continue;
#define AFFINE_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto affine_stream_mismatch;cursor+=amount;}while(0)
#define AFFINE_U64(value) do{if((SIZE_T)(finish-cursor)<8u)goto affine_stream_mismatch;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
        AFFINE_LITERAL("\x49\xbb");AFFINE_U64(candidate.stream_step);
        AFFINE_LITERAL("\x44\x89\xc8\x48\xbb");AFFINE_U64(candidate.stream_index_multiplier);
        AFFINE_LITERAL("\x48\x0f\xaf\xd8\x48\xb8");AFFINE_U64(candidate.stream_index_bias);
        AFFINE_LITERAL("\x48\x01\xd8");
        if(!candidate.stream_step||!candidate.stream_index_multiplier)goto affine_stream_mismatch;
        {const unsigned char scalar[]={0x48,0x8b,0x3c,0xda,0x48,0x31,0xc7,0x4c,0x01,0xd8,0x48,0x89,0x3c,0xde};
        int found=0;for(uintptr_t q=begin;q+sizeof(scalar)<=end;q++)if(!memcmp((const void*)q,scalar,sizeof(scalar))){found=1;break;}
        if(!found)goto affine_stream_mismatch;}
        candidate.stream_codec=3u;*contract=candidate;matches++;
affine_stream_mismatch:;
#undef AFFINE_U64
#undef AFFINE_LITERAL
    }
    for(uintptr_t p=begin;p+94u<=limit;p++){
        decoder_contract candidate=*contract;
        if(parse_scalar_stream_mix((const unsigned char*)p,(const unsigned char*)limit,&candidate)){*contract=candidate;matches++;}
    }
    if(matches!=1u)return 0;const unsigned char abi_pattern[]={0x41,0x89,0xc9,0x45,0x8d,0x50,0x07};const unsigned char loop_pattern[]={0x48,0x8b,0x3c,0xda,0x48,0x31,0xc7,0x4c,0x01,0xd8,0x48,0x89,0x3c,0xde};int abi=0,loop=0;
    for(uintptr_t p=begin;p+sizeof(abi_pattern)<=end&&p<begin+96u;p++)if(!memcmp((const void*)p,abi_pattern,sizeof(abi_pattern)))abi=1;
    for(uintptr_t p=begin;p+sizeof(loop_pattern)<=end;p++)if(!memcmp((const void*)p,loop_pattern,sizeof(loop_pattern)))loop=1;
    if((!abi&&contract->stream_codec!=3u&&contract->stream_codec!=4u)||!loop)return 0;contract->byte_decoder_target=target;return 1;
}
static int parse_case5_at(const unsigned char*cursor,const unsigned char*end,decoder_contract*contract){
#define TAKE_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(end-cursor)<amount||memcmp(cursor,pattern,amount))return 0;cursor+=amount;}while(0)
#define TAKE_U32(value) do{if((SIZE_T)(end-cursor)<4u)return 0;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
#define TAKE_U64(value) do{if((SIZE_T)(end-cursor)<8u)return 0;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
    uint8_t second_shift=0;uint32_t second_mix=0,second_xor=0,second_add=0,second_final=0;
    TAKE_LITERAL("\x41\x89\xc9\x48\x63\x82");TAKE_U32(contract->mapping_selector_field);
    TAKE_LITERAL("\x48\x35");TAKE_U32(contract->mapping_selector_xor);
    TAKE_LITERAL("\x4c\x01\xe8\x4c\x89\xcb\x48\xbf");TAKE_U64(contract->index_multiplier);
    TAKE_LITERAL("\x48\x0f\xaf\xdf\x48\xbf");TAKE_U64(contract->start_bias);
    TAKE_LITERAL("\x48\x01\xdf\x48\xc1\xef");if(cursor>=end)return 0;contract->index_shift=*cursor++;
    TAKE_LITERAL("\x69\xff");TAKE_U32(contract->mix_multiplier);
    TAKE_LITERAL("\x81\xf7");TAKE_U32(contract->mix_xor);
    TAKE_LITERAL("\x81\xc7");TAKE_U32(contract->mix_add);
    TAKE_LITERAL("\x42\x33\x3c\x88\x81\xf7");TAKE_U32(contract->final_xor);
    TAKE_LITERAL("\x48\xbe");TAKE_U64(contract->end_bias);
    TAKE_LITERAL("\x48\x01\xf3\x48\xc1\xeb");if(cursor>=end)return 0;second_shift=*cursor++;
    TAKE_LITERAL("\x48\x63\xff\x48\x63\x92");TAKE_U32(contract->data_selector_field);
    TAKE_LITERAL("\x48\x81\xf2");TAKE_U32(contract->data_selector_xor);
    TAKE_LITERAL("\x4c\x01\xea\x48\x01\xfa\x44\x69\xc3");TAKE_U32(second_mix);
    TAKE_LITERAL("\x41\x81\xf0");TAKE_U32(second_xor);
    TAKE_LITERAL("\x41\x81\xc0");TAKE_U32(second_add);
    TAKE_LITERAL("\x46\x33\x44\x88\x04\x41\x81\xf0");TAKE_U32(second_final);
    TAKE_LITERAL("\x41\x29\xf8\xe8");
#undef TAKE_U64
#undef TAKE_U32
#undef TAKE_LITERAL
    if((SIZE_T)(end-cursor)<4u||!contract->index_multiplier||contract->index_shift>=64u||
       contract->mapping_selector_field>4096u||contract->data_selector_field>4096u||
       contract->mapping_selector_field==contract->data_selector_field||
       second_shift!=contract->index_shift||second_mix!=contract->mix_multiplier||
       second_xor!=contract->mix_xor||second_add!=contract->mix_add||second_final!=contract->final_xor)return 0;
    int32_t displacement=0;memcpy(&displacement,cursor,4u);uintptr_t byte_decoder=(uintptr_t)(cursor+4u)+(intptr_t)displacement;
    return byte_decoder>=expected_image_base&&byte_decoder<expected_image_base+expected_image_bytes&&parse_byte_decoder(byte_decoder,contract);
}
static int parse_case5_at_index_successor(const unsigned char*cursor,const unsigned char*end,decoder_contract*contract){
#define SUCCESSOR_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(end-cursor)<amount||memcmp(cursor,pattern,amount))return 0;cursor+=amount;}while(0)
#define SUCCESSOR_U32(value) do{if((SIZE_T)(end-cursor)<4u)return 0;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
    uint32_t end_multiplier=0,end_xor=0,end_mix_multiplier=0,end_add=0,end_second_xor=0,end_second_add=0,end_final=0;
    SUCCESSOR_LITERAL("\x41\x89\xc9\x8b\x82");SUCCESSOR_U32(contract->mapping_selector_field);
    SUCCESSOR_LITERAL("\xbb");SUCCESSOR_U32(contract->mapping_selector_add);
    SUCCESSOR_LITERAL("\x01\xd8\x48\x98\x4c\x01\xe0\x69\xf9");SUCCESSOR_U32(contract->index_multiplier);
    SUCCESSOR_LITERAL("\x89\xfb\x81\xf3");SUCCESSOR_U32(contract->mix_xor);
    SUCCESSOR_LITERAL("\x69\xdb");SUCCESSOR_U32(contract->mix_multiplier);
    SUCCESSOR_LITERAL("\x81\xc3");SUCCESSOR_U32(contract->mix_add);
    SUCCESSOR_LITERAL("\x81\xf3");SUCCESSOR_U32(contract->mix_second_xor);
    SUCCESSOR_LITERAL("\x81\xc3");SUCCESSOR_U32(contract->mix_second_add);
    SUCCESSOR_LITERAL("\x42\x33\x1c\x88\x81\xf3");SUCCESSOR_U32(contract->final_xor);
    SUCCESSOR_LITERAL("\x81\xc7");SUCCESSOR_U32(end_multiplier);
    SUCCESSOR_LITERAL("\x81\xf7");SUCCESSOR_U32(end_xor);
    SUCCESSOR_LITERAL("\x44\x69\xc7");SUCCESSOR_U32(end_mix_multiplier);
    SUCCESSOR_LITERAL("\x41\x81\xc0");SUCCESSOR_U32(end_add);
    SUCCESSOR_LITERAL("\x41\x81\xf0");SUCCESSOR_U32(end_second_xor);
    SUCCESSOR_LITERAL("\x41\x81\xc0");SUCCESSOR_U32(end_second_add);
    SUCCESSOR_LITERAL("\x48\x63\xdb\x8b\x92");SUCCESSOR_U32(contract->data_selector_field);
    SUCCESSOR_LITERAL("\xbf");SUCCESSOR_U32(contract->data_selector_add);
    SUCCESSOR_LITERAL("\x01\xfa\x48\x63\xd2\x4c\x01\xe2\x48\x01\xda\x46\x33\x44\x88\x04\x41\x81\xf0");SUCCESSOR_U32(end_final);
    SUCCESSOR_LITERAL("\x41\x29\xd8\xe8");
#undef SUCCESSOR_U32
#undef SUCCESSOR_LITERAL
    if((SIZE_T)(end-cursor)<4u||!contract->index_multiplier||!contract->mix_multiplier||
       contract->mapping_selector_field>4096u||contract->data_selector_field>4096u||
       contract->mapping_selector_field==contract->data_selector_field||
       end_multiplier!=(uint32_t)contract->index_multiplier||end_xor!=contract->mix_xor||
       end_mix_multiplier!=contract->mix_multiplier||end_add!=contract->mix_add||
       end_second_xor!=contract->mix_second_xor||end_second_add!=contract->mix_second_add||
       end_final!=contract->final_xor)return 0;
    int32_t displacement=0;memcpy(&displacement,cursor,4u);uintptr_t byte_decoder=(uintptr_t)(cursor+4u)+(intptr_t)displacement;


    contract->end_bias=1u;contract->boundary_codec=2u;contract->selector_codec=2u;
    return byte_decoder>=expected_image_base&&byte_decoder<expected_image_base+expected_image_bytes&&parse_byte_decoder(byte_decoder,contract);
}
static int parse_case5_at_shifted_mix(const unsigned char*cursor,const unsigned char*end,decoder_contract*contract){
#define SHIFTED_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(end-cursor)<amount||memcmp(cursor,pattern,amount))return 0;cursor+=amount;}while(0)
#define SHIFTED_U32(value) do{if((SIZE_T)(end-cursor)<4u)return 0;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
    uint32_t end_index_multiplier=0,end_mix_xor=0,end_mix_multiplier=0,end_second_xor=0,end_second_multiplier=0,end_final_xor=0;
    uint8_t end_shift=0;
    SHIFTED_LITERAL("\x41\x89\xc9\x49\x63\x42");if(cursor>=end)return 0;contract->mapping_selector_field=*cursor++;
    SHIFTED_LITERAL("\x48\x35");SHIFTED_U32(contract->mapping_selector_xor);
    SHIFTED_LITERAL("\x4c\x01\xe8\x49\x69\xf9");SHIFTED_U32(contract->index_multiplier);
    SHIFTED_LITERAL("\x48\x89\xfb\x48\x81\xf3");SHIFTED_U32(contract->mix_xor);
    SHIFTED_LITERAL("\x48\x69\xdb");SHIFTED_U32(contract->mix_multiplier);
    SHIFTED_LITERAL("\x48\x81\xf3");SHIFTED_U32(contract->mix_second_xor);
    SHIFTED_LITERAL("\x48\x69\xdb");SHIFTED_U32(contract->mix_second_multiplier);
    SHIFTED_LITERAL("\x48\xc1\xeb");if(cursor>=end)return 0;contract->index_shift=*cursor++;
    SHIFTED_LITERAL("\x49\x63\x92");SHIFTED_U32(contract->data_selector_field);
    SHIFTED_LITERAL("\x48\x81\xf2");SHIFTED_U32(contract->data_selector_xor);
    SHIFTED_LITERAL("\x42\x33\x1c\x88\x81\xf3");SHIFTED_U32(contract->final_xor);
    SHIFTED_LITERAL("\x48\x81\xc7");SHIFTED_U32(end_index_multiplier);
    SHIFTED_LITERAL("\x48\x81\xf7");SHIFTED_U32(end_mix_xor);
    SHIFTED_LITERAL("\x48\x69\xff");SHIFTED_U32(end_mix_multiplier);
    SHIFTED_LITERAL("\x48\x81\xf7");SHIFTED_U32(end_second_xor);
    SHIFTED_LITERAL("\x4c\x69\xc7");SHIFTED_U32(end_second_multiplier);
    SHIFTED_LITERAL("\x49\xc1\xe8");if(cursor>=end)return 0;end_shift=*cursor++;
    SHIFTED_LITERAL("\x48\x63\xdb\x4c\x01\xea\x48\x01\xda\x46\x33\x44\x88\x04\x41\x81\xf0");SHIFTED_U32(end_final_xor);
    SHIFTED_LITERAL("\x41\x29\xd8\xe8");
#undef SHIFTED_U32
#undef SHIFTED_LITERAL
    if((SIZE_T)(end-cursor)<4u||!contract->index_multiplier||!contract->mix_multiplier||!contract->mix_second_multiplier||
       contract->index_shift>=32u||contract->mapping_selector_field>4096u||contract->data_selector_field>4096u||
       contract->mapping_selector_field==contract->data_selector_field||
       end_index_multiplier!=(uint32_t)contract->index_multiplier||end_mix_xor!=contract->mix_xor||
       end_mix_multiplier!=contract->mix_multiplier||end_second_xor!=contract->mix_second_xor||
       end_second_multiplier!=contract->mix_second_multiplier||end_shift!=contract->index_shift||end_final_xor!=contract->final_xor)return 0;
    int32_t displacement=0;memcpy(&displacement,cursor,4u);uintptr_t byte_decoder=(uintptr_t)(cursor+4u)+(intptr_t)displacement;
    contract->end_bias=1u;contract->boundary_codec=3u;
    return byte_decoder>=expected_image_base&&byte_decoder<expected_image_base+expected_image_bytes&&parse_byte_decoder(byte_decoder,contract);
}
static int parse_case5_at_affine_boundary(const unsigned char*cursor,const unsigned char*end,decoder_contract*contract){
#define AFFINE_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(end-cursor)<amount||memcmp(cursor,pattern,amount))return 0;cursor+=amount;}while(0)
#define AFFINE_U32(value) do{if((SIZE_T)(end-cursor)<4u)return 0;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
#define AFFINE_U64(value) do{if((SIZE_T)(end-cursor)<8u)return 0;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
    uint32_t end_xor=0,end_add=0;uint8_t end_shift=0;
    AFFINE_LITERAL("\x89\xc8\x8b\x5a");if(cursor>=end)return 0;contract->mapping_selector_field=*cursor++;
    AFFINE_LITERAL("\xbf");AFFINE_U32(contract->mapping_selector_add);
    AFFINE_LITERAL("\x01\xfb\x48\x63\xdb\x4c\x01\xe3\x8b\x3c\x83\x44\x8b\x44\x83\x04\x49\xb9");AFFINE_U64(contract->index_multiplier);
    AFFINE_LITERAL("\x49\x0f\xaf\xc1\x48\x89\xc3\x48\xc1\xeb");if(cursor>=end)return 0;contract->index_shift=*cursor++;
    AFFINE_LITERAL("\x81\xf3");AFFINE_U32(contract->mix_xor);
    AFFINE_LITERAL("\x01\xfb\x81\xc3");AFFINE_U32(contract->mix_add);
    AFFINE_LITERAL("\x4c\x01\xc8\x48\xc1\xe8");if(cursor>=end)return 0;end_shift=*cursor++;
    AFFINE_LITERAL("\x48\x63\xdb\x8b\x92");AFFINE_U32(contract->data_selector_field);
    AFFINE_LITERAL("\xbf");AFFINE_U32(contract->data_selector_add);
    AFFINE_LITERAL("\x01\xfa\x48\x63\xd2\x4c\x01\xe2\x48\x01\xda\x35");AFFINE_U32(end_xor);
    AFFINE_LITERAL("\x29\xd8\x41\x01\xc0\x41\x81\xc0");AFFINE_U32(end_add);
    AFFINE_LITERAL("\xe8");
#undef AFFINE_U64
#undef AFFINE_U32
#undef AFFINE_LITERAL
    if((SIZE_T)(end-cursor)<4u||!contract->index_multiplier||contract->index_shift>=64u||
       contract->mapping_selector_field>4096u||contract->data_selector_field>4096u||
       contract->mapping_selector_field==contract->data_selector_field||
       end_shift!=contract->index_shift||end_xor!=contract->mix_xor||end_add!=contract->mix_add)return 0;
    int32_t displacement=0;memcpy(&displacement,cursor,4u);
    uintptr_t byte_decoder=(uintptr_t)(cursor+4u)+(intptr_t)displacement;
    contract->end_bias=1u;contract->boundary_codec=4u;contract->selector_codec=2u;
    return byte_decoder>=expected_image_base&&byte_decoder<expected_image_base+expected_image_bytes&&parse_byte_decoder(byte_decoder,contract);
}
#define FAMILY_BYTES(value) do{const unsigned char pattern[]=value;SIZE_T n=sizeof(pattern)-1u;if((SIZE_T)(end-cursor)<n||memcmp(cursor,pattern,n))return 0;cursor+=n;}while(0)
#define FAMILY_U32(value) do{if((SIZE_T)(end-cursor)<4u)return 0;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
#define FAMILY_U64(value) do{if((SIZE_T)(end-cursor)<8u)return 0;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
#define FAMILY_U8(value) do{if(cursor>=end)return 0;(value)=*cursor++;}while(0)
static int parse_case5_at_scalar_boundary(const unsigned char*cursor,const unsigned char*end,decoder_contract*contract){
    uint32_t second_final=0,relative=0;
    FAMILY_BYTES("\x89\xc8");
    FAMILY_BYTES("\x41\x8b\x9a");
    FAMILY_U32(contract->mapping_selector_field);
    FAMILY_BYTES("\xba");
    FAMILY_U32(contract->mapping_selector_add);
    FAMILY_BYTES("\x01\xd3");
    FAMILY_BYTES("\x48\x63\xdb");
    FAMILY_BYTES("\x4c\x01\xe3");
    FAMILY_BYTES("\x44\x69\xc1");
    FAMILY_U32(contract->index_multiplier);
    FAMILY_BYTES("\x41\x8d\xb8");
    FAMILY_U32(contract->start_bias);
    FAMILY_BYTES("\x49\x63\x92");
    FAMILY_U32(contract->data_selector_field);
    FAMILY_BYTES("\x48\x81\xf2");
    FAMILY_U32(contract->data_selector_xor);
    FAMILY_BYTES("\x33\x3c\x83");
    FAMILY_BYTES("\x81\xf7");
    FAMILY_U32(contract->final_xor);
    FAMILY_BYTES("\x41\x81\xc0");
    FAMILY_U32(contract->end_bias);
    FAMILY_BYTES("\x48\x63\xff");
    FAMILY_BYTES("\x4c\x01\xe2");
    FAMILY_BYTES("\x48\x01\xfa");
    FAMILY_BYTES("\x44\x33\x44\x83\x04");
    FAMILY_BYTES("\x41\x81\xf0");
    FAMILY_U32(second_final);
    FAMILY_BYTES("\x41\x29\xf8");
    FAMILY_BYTES("\xe8");
    FAMILY_U32(relative);
    if(!contract->index_multiplier||contract->mapping_selector_field>4096u||contract->data_selector_field>4096u||contract->mapping_selector_field==contract->data_selector_field||second_final!=contract->final_xor)return 0;
    uintptr_t helper=(uintptr_t)cursor+(intptr_t)(int32_t)relative;
    contract->boundary_codec=5u;contract->selector_codec=3u;
    return helper>=expected_image_base&&helper<expected_image_base+expected_image_bytes&&parse_byte_decoder(helper,contract);
}
#undef FAMILY_BYTES
#undef FAMILY_U32
#undef FAMILY_U64
#undef FAMILY_U8
static int parse_case5_decoder(uintptr_t target,uintptr_t function_end,decoder_contract*contract){
    uintptr_t limit=target+256u;if(limit<target||limit>function_end)limit=function_end;uint32_t matches=0;decoder_contract selected={0};
    for(uintptr_t p=target;p+16u<=limit;p++){const unsigned char*b=(const unsigned char*)p;decoder_contract candidate={0};candidate.case5_target=target;if((b[0]==0x41&&b[1]==0x89&&b[2]==0xc9&&(parse_case5_at(b,(const unsigned char*)limit,&candidate)||parse_case5_at_index_successor(b,(const unsigned char*)limit,&candidate)||parse_case5_at_shifted_mix(b,(const unsigned char*)limit,&candidate)))||(b[0]==0x89&&b[1]==0xc8&&(parse_case5_at_affine_boundary(b,(const unsigned char*)limit,&candidate)||parse_case5_at_scalar_boundary(b,(const unsigned char*)limit,&candidate)))){selected=candidate;matches++;}}
    if(matches!=1u)return 0;*contract=selected;return 1;
}
static int parse_member_usage_contract(uintptr_t case4,uintptr_t case6,uintptr_t function_end,const decoder_contract*literal_contract,const usage_pair_contract*pair_contract,usage_member_contract*contract){
    usage_member_contract selected={0};uint32_t field_matches=0,method_matches=0,inst_matches=0;uintptr_t limit=case4+256u;if(limit<case4||limit>function_end)limit=function_end;
    for(uintptr_t p=case4;p+96u<=limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;usage_member_contract candidate=selected;if(cursor[0]!=0x89||cursor[1]!=0xce||cursor[2]!=0x8b||cursor[3]!=0x42)continue;cursor+=4u;
#define MEMBER_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto field_mismatch;cursor+=amount;}while(0)
#define MEMBER_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto field_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
#define MEMBER_U64(value) do{if((SIZE_T)(finish-cursor)<8u)goto field_mismatch;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
        candidate.field_selector_field=*cursor++;MEMBER_LITERAL("\xb9");MEMBER_U32(candidate.field_selector_add);MEMBER_LITERAL("\x01\xc8\x48\x98\x49\x01\xc5\x48\x89\xf0\x48\xb9");MEMBER_U64(candidate.field_index_multiplier);MEMBER_LITERAL("\x48\x0f\xaf\xc1\x48\xb9");MEMBER_U64(candidate.field_index_bias);MEMBER_LITERAL("\x48\x01\xc8\x48\x35");MEMBER_U32(candidate.field_index_xor);MEMBER_LITERAL("\x48\x69\xc0");MEMBER_U32(candidate.field_index_mix);MEMBER_LITERAL("\x48\xc1\xe8");if(cursor>=finish)goto field_mismatch;candidate.field_index_shift=*cursor++;MEMBER_LITERAL("\x41\x8b\x4c\xf5\x00\xba");MEMBER_U32(candidate.field_value0_xor);MEMBER_LITERAL("\x31\xd1\x69\xf8");MEMBER_U32(candidate.field_final_multiplier);MEMBER_LITERAL("\x29\xf9\xb2\x01\xe8");if(cursor+4u>finish)goto field_mismatch;int32_t displacement=0;memcpy(&displacement,cursor,4u);uintptr_t helper=(uintptr_t)(cursor+4u)+(intptr_t)displacement;cursor+=4u;MEMBER_LITERAL("\x41\x8b\x4c\xf5\x04\xba");MEMBER_U32(candidate.field_value1_xor);MEMBER_LITERAL("\x31\xd1\x29\xf9");
        if(candidate.field_selector_field>4096u||!candidate.field_index_multiplier||!candidate.field_index_mix||!candidate.field_final_multiplier||candidate.field_index_shift>=64u||helper!=pair_contract->type_helper)goto field_mismatch;candidate.field_record_stride=8u;selected=candidate;field_matches++;
field_mismatch:;
#undef MEMBER_U64
#undef MEMBER_U32
#undef MEMBER_LITERAL
    }
    limit=case6+256u;if(limit<case6||limit>function_end)limit=function_end;
    for(uintptr_t p=case6;p+32u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x8b||b[1]!=0x82||b[6]!=0xb9||b[11]!=0x01||b[12]!=0xc8||memcmp(b+13,"\x48\x98\x49\x01\xc5\x4b\x8d\x04\x64\x49\x63\x54\x85\x04",14u))continue;uint32_t field=0,add=0;memcpy(&field,b+2u,4u);memcpy(&add,b+7u,4u);if(field>4096u)continue;selected.method_selector_field=field;selected.method_selector_add=add;selected.method_record_stride=12u;method_matches++;
    }
    for(uintptr_t p=case6;p+18u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x48||b[1]!=0x8b||b[2]!=0x0d||memcmp(b+7,"\x48\xc1\xe2",3u)||b[11]!=0x48||b[12]!=0x03||b[13]!=0x51)continue;uintptr_t global=0;uint32_t shift=b[10],field=b[14];if(shift<3u||shift>6u||field>4096u||!rip_target(p,7u,&global)||global!=pair_contract->type_state_global)continue;if(!inst_matches){selected.generic_inst_state_global=global;selected.generic_inst_state_field=field;selected.generic_inst_shift=shift;inst_matches=1u;}else if(selected.generic_inst_state_global!=global||selected.generic_inst_state_field!=field||selected.generic_inst_shift!=shift)return 0;
    }
    if(field_matches!=1u||method_matches!=1u||inst_matches!=1u)return 0;int32_t field_raw=0,method_raw=0;if(!literal_contract->descriptor||!literal_contract->metadata_base||!region_for(literal_contract->descriptor,(SIZE_T)(selected.field_selector_field>selected.method_selector_field?selected.field_selector_field:selected.method_selector_field)+4u,NULL))return 0;memcpy(&field_raw,(const void*)(literal_contract->descriptor+selected.field_selector_field),4u);memcpy(&method_raw,(const void*)(literal_contract->descriptor+selected.method_selector_field),4u);int64_t field_offset=(int64_t)(int32_t)((uint32_t)field_raw+selected.field_selector_add),method_offset=(int64_t)(int32_t)((uint32_t)method_raw+selected.method_selector_add);uintptr_t state=0;if(!add_signed_offset(literal_contract->metadata_base,field_offset,&selected.field_ref_base)||!add_signed_offset(literal_contract->metadata_base,method_offset,&selected.method_spec_base)||!region_for(selected.field_ref_base,8u,NULL)||!region_for(selected.method_spec_base,12u,NULL)||!region_for(selected.generic_inst_state_global,8u,NULL))return 0;memcpy(&state,(const void*)selected.generic_inst_state_global,8u);if(!state||!region_for(state+selected.generic_inst_state_field,8u,NULL))return 0;memcpy(&selected.generic_inst_base,(const void*)(state+selected.generic_inst_state_field),8u);if(!selected.generic_inst_base||selected.generic_inst_base<expected_image_base||selected.generic_inst_base>=expected_image_base+expected_image_bytes||!region_for(selected.generic_inst_base,16u,NULL))return 0;selected.member_codec=1u;*contract=selected;return 1;
}
static int parse_member_usage_contract_affine(uintptr_t case4,uintptr_t case6,uintptr_t function_end,const decoder_contract*literal_contract,const usage_pair_contract*pair_contract,usage_member_contract*contract){
    usage_member_contract selected={0};uint32_t field_matches=0,method_matches=0,inst_matches=0;
    uintptr_t limit=case4+256u;if(limit<case4||limit>function_end)limit=function_end;
    for(uintptr_t p=case4;p+64u<=limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;
        usage_member_contract candidate=selected;if(cursor[0]!=0x89||cursor[1]!=0xce)continue;
#define MEMBER_AFFINE_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto field_affine_mismatch;cursor+=amount;}while(0)
#define MEMBER_AFFINE_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto field_affine_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
        MEMBER_AFFINE_LITERAL("\x89\xce\x48\x63\x82");MEMBER_AFFINE_U32(candidate.field_selector_field);
        MEMBER_AFFINE_LITERAL("\x48\x35");MEMBER_AFFINE_U32(candidate.field_selector_add);
        MEMBER_AFFINE_LITERAL("\x49\x01\xc4\x44\x69\xf9");uint32_t multiplier=0;MEMBER_AFFINE_U32(multiplier);candidate.field_index_multiplier=multiplier;
        MEMBER_AFFINE_LITERAL("\x41\x81\xc7");uint32_t key_add=0;MEMBER_AFFINE_U32(key_add);candidate.field_index_bias=key_add;
        MEMBER_AFFINE_LITERAL("\x41\x8b\x0c\xf4\x44\x31\xf9\x81\xf1");MEMBER_AFFINE_U32(candidate.field_value0_xor);
        MEMBER_AFFINE_LITERAL("\xb2\x01\xe8");if((SIZE_T)(finish-cursor)<4u)goto field_affine_mismatch;int32_t displacement=0;memcpy(&displacement,cursor,4u);uintptr_t helper=(uintptr_t)(cursor+4u)+(intptr_t)displacement;cursor+=4u;
        MEMBER_AFFINE_LITERAL("\x41\x8b\x4c\xf4\x04\xba");MEMBER_AFFINE_U32(candidate.field_value1_add);
        MEMBER_AFFINE_LITERAL("\x01\xd1\x41\x31\xcf\x41\x81\xf7");MEMBER_AFFINE_U32(candidate.field_value1_xor);
        MEMBER_AFFINE_LITERAL("\x49\x63\xcf\x48\xc1\xe1");if(cursor>=finish)goto field_affine_mismatch;uint32_t shift=*cursor++;
        MEMBER_AFFINE_LITERAL("\x48\x03\x48");if(cursor>=finish)goto field_affine_mismatch;uint32_t field_array_offset=*cursor++;
        if(candidate.field_selector_field>4096u||!candidate.field_index_multiplier||shift<3u||shift>8u||field_array_offset>0x100u||helper!=pair_contract->type_helper)goto field_affine_mismatch;
        candidate.field_record_stride=8u;candidate.member_codec=4u;selected=candidate;field_matches++;
field_affine_mismatch:;
#undef MEMBER_AFFINE_U32
#undef MEMBER_AFFINE_LITERAL
    }
    limit=case6+256u;if(limit<case6||limit>function_end)limit=function_end;
    for(uintptr_t p=case6;p+31u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x8b||b[1]!=0x82||b[6]!=0xb9||memcmp(b+11,"\x01\xc8\x48\x98\x49\x01\xc4\x48\x8d\x04\x7f\x49\x63\x54\x84\x04",16u))continue;
        uint32_t field=0,add=0;memcpy(&field,b+2u,4u);memcpy(&add,b+7u,4u);if(field>4096u)continue;
        selected.method_selector_field=field;selected.method_selector_add=add;selected.method_record_stride=12u;method_matches++;
    }
    for(uintptr_t p=case6;p+18u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x48||b[1]!=0x8b||b[2]!=0x0d||memcmp(b+7,"\x48\xc1\xe2",3u)||b[11]!=0x48||b[12]!=0x03||b[13]!=0x51)continue;
        uintptr_t global=0;uint32_t shift=b[10],field=b[14];if(shift<3u||shift>6u||field>4096u||!rip_target(p,7u,&global)||global!=pair_contract->type_state_global)continue;
        if(!inst_matches){selected.generic_inst_state_global=global;selected.generic_inst_state_field=field;selected.generic_inst_shift=shift;inst_matches=1u;}
        else if(selected.generic_inst_state_global!=global||selected.generic_inst_state_field!=field||selected.generic_inst_shift!=shift)return 0;
    }
    if(field_matches!=1u||method_matches!=1u||inst_matches!=1u)return 0;
    int32_t field_raw=0,method_raw=0;uint32_t maximum_field=selected.field_selector_field>selected.method_selector_field?selected.field_selector_field:selected.method_selector_field;
    if(!literal_contract->descriptor||!literal_contract->metadata_base||!region_for(literal_contract->descriptor,(SIZE_T)maximum_field+4u,NULL))return 0;
    memcpy(&field_raw,(const void*)(literal_contract->descriptor+selected.field_selector_field),4u);memcpy(&method_raw,(const void*)(literal_contract->descriptor+selected.method_selector_field),4u);
    int64_t field_offset=(int64_t)(((uint64_t)(int64_t)field_raw)^((uint64_t)(int64_t)(int32_t)selected.field_selector_add));
    int64_t method_offset=(int64_t)(int32_t)((uint32_t)method_raw+selected.method_selector_add);uintptr_t state=0;
    if(!add_signed_offset(literal_contract->metadata_base,field_offset,&selected.field_ref_base)||!add_signed_offset(literal_contract->metadata_base,method_offset,&selected.method_spec_base)||!region_for(selected.field_ref_base,8u,NULL)||!region_for(selected.method_spec_base,12u,NULL)||!region_for(selected.generic_inst_state_global,8u,NULL))return 0;
    memcpy(&state,(const void*)selected.generic_inst_state_global,8u);if(!state||!region_for(state+selected.generic_inst_state_field,8u,NULL))return 0;
    memcpy(&selected.generic_inst_base,(const void*)(state+selected.generic_inst_state_field),8u);
    if(!selected.generic_inst_base||selected.generic_inst_base<expected_image_base||selected.generic_inst_base>=expected_image_base+expected_image_bytes||!region_for(selected.generic_inst_base,16u,NULL))return 0;
    *contract=selected;return 1;
}


static int parse_member_usage_contract_keyed(uintptr_t case4,uintptr_t case6,uintptr_t function_end,const decoder_contract*literal_contract,const usage_pair_contract*pair_contract,usage_member_contract*contract){
    usage_member_contract selected={0};uint32_t field_matches=0,method_matches=0,inst_matches=0;uintptr_t limit=case4+256u;if(limit<case4||limit>function_end)limit=function_end;
    for(uintptr_t p=case4;p+80u<=limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;usage_member_contract candidate=selected;if(cursor[0]!=0x89||cursor[1]!=0xce)continue;cursor+=2u;
#define MEMBER_KEYED_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto field_keyed_mismatch;cursor+=amount;}while(0)
#define MEMBER_KEYED_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto field_keyed_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
        MEMBER_KEYED_LITERAL("\x48\x63\x82");MEMBER_KEYED_U32(candidate.field_selector_field);MEMBER_KEYED_LITERAL("\x48\x35");MEMBER_KEYED_U32(candidate.field_selector_add);MEMBER_KEYED_LITERAL("\x49\x01\xc4\x69\xc1");uint32_t key_multiplier=0;MEMBER_KEYED_U32(key_multiplier);candidate.field_index_multiplier=key_multiplier;MEMBER_KEYED_LITERAL("\x35");MEMBER_KEYED_U32(candidate.field_index_xor);MEMBER_KEYED_LITERAL("\x44\x69\xf8");MEMBER_KEYED_U32(candidate.field_index_mix);MEMBER_KEYED_LITERAL("\x41\x81\xf7");MEMBER_KEYED_U32(candidate.field_final_multiplier);MEMBER_KEYED_LITERAL("\x41\x81\xc7");uint32_t key_add=0;MEMBER_KEYED_U32(key_add);candidate.field_index_bias=key_add;MEMBER_KEYED_LITERAL("\x41\x8b\x4c\xf4\x04\xb8");MEMBER_KEYED_U32(candidate.field_value1_xor);MEMBER_KEYED_LITERAL("\x31\xc1\x44\x29\xf9\xb2\x01\xe8");if(cursor+4u>finish)goto field_keyed_mismatch;int32_t displacement=0;memcpy(&displacement,cursor,4u);uintptr_t helper=(uintptr_t)(cursor+4u)+(intptr_t)displacement;cursor+=4u;MEMBER_KEYED_LITERAL("\x41\x8b\x0c\xf4\xba");MEMBER_KEYED_U32(candidate.field_value0_xor);MEMBER_KEYED_LITERAL("\x31\xd1\x44\x29\xf9\x48\x63\xc9\x48\xc1\xe1");if(cursor>=finish)goto field_keyed_mismatch;candidate.field_index_shift=*cursor++;MEMBER_KEYED_LITERAL("\x48\x03\x48");if(cursor>=finish)goto field_keyed_mismatch;uint32_t runtime_fields_offset=*cursor++;
        if(candidate.field_selector_field>4096u||!candidate.field_index_multiplier||!candidate.field_index_mix||candidate.field_index_shift<4u||candidate.field_index_shift>6u||runtime_fields_offset>0x100u||helper!=pair_contract->type_helper)goto field_keyed_mismatch;candidate.field_record_stride=8u;candidate.member_codec=2u;selected=candidate;field_matches++;
field_keyed_mismatch:;
#undef MEMBER_KEYED_U32
#undef MEMBER_KEYED_LITERAL
    }
    limit=case6+256u;if(limit<case6||limit>function_end)limit=function_end;
    for(uintptr_t p=case6;p+36u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;if(memcmp(b,"\x48\x63\x82",3u)||b[7]!=0x48||b[8]!=0x35||memcmp(b+13,"\x49\x01\xc4\x48\x8d\x04\x7f\x49\x63\x54\x84\x08",12u))continue;uint32_t field=0,xor_value=0;memcpy(&field,b+3u,4u);memcpy(&xor_value,b+9u,4u);if(field>4096u)continue;selected.method_selector_field=field;selected.method_selector_add=xor_value;selected.method_record_stride=12u;method_matches++;
    }
    for(uintptr_t p=case6;p+18u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x48||b[1]!=0x8b||b[2]!=0x0d||memcmp(b+7,"\x48\xc1\xe2",3u)||b[11]!=0x48||b[12]!=0x03||b[13]!=0x51)continue;uintptr_t global=0;uint32_t shift=b[10],field=b[14];if(shift<3u||shift>6u||field>4096u||!rip_target(p,7u,&global)||global!=pair_contract->type_state_global)continue;if(!inst_matches){selected.generic_inst_state_global=global;selected.generic_inst_state_field=field;selected.generic_inst_shift=shift;inst_matches=1u;}else if(selected.generic_inst_state_global!=global||selected.generic_inst_state_field!=field||selected.generic_inst_shift!=shift)return 0;
    }
    if(field_matches!=1u||method_matches!=1u||inst_matches!=1u)return 0;int32_t field_raw=0,method_raw=0;if(!literal_contract->descriptor||!literal_contract->metadata_base||!region_for(literal_contract->descriptor,(SIZE_T)(selected.field_selector_field>selected.method_selector_field?selected.field_selector_field:selected.method_selector_field)+4u,NULL))return 0;memcpy(&field_raw,(const void*)(literal_contract->descriptor+selected.field_selector_field),4u);memcpy(&method_raw,(const void*)(literal_contract->descriptor+selected.method_selector_field),4u);int64_t field_offset=(int64_t)field_raw^(int64_t)(int32_t)selected.field_selector_add,method_offset=(int64_t)method_raw^(int64_t)(int32_t)selected.method_selector_add;uintptr_t state=0;if(!add_signed_offset(literal_contract->metadata_base,field_offset,&selected.field_ref_base)||!add_signed_offset(literal_contract->metadata_base,method_offset,&selected.method_spec_base)||!region_for(selected.field_ref_base,8u,NULL)||!region_for(selected.method_spec_base,12u,NULL)||!region_for(selected.generic_inst_state_global,8u,NULL))return 0;memcpy(&state,(const void*)selected.generic_inst_state_global,8u);if(!state||!region_for(state+selected.generic_inst_state_field,8u,NULL))return 0;memcpy(&selected.generic_inst_base,(const void*)(state+selected.generic_inst_state_field),8u);if(!selected.generic_inst_base||selected.generic_inst_base<expected_image_base||selected.generic_inst_base>=expected_image_base+expected_image_bytes||!region_for(selected.generic_inst_base,16u,NULL))return 0;*contract=selected;return 1;
}
static int parse_member_usage_contract_ranged_mix(uintptr_t case4,uintptr_t case6,uintptr_t function_end,const decoder_contract*literal_contract,const usage_pair_contract*pair_contract,usage_member_contract*contract){
    usage_member_contract selected={0};uint32_t field_matches=0,method_matches=0,inst_matches=0;uintptr_t limit=case4+256u;if(limit<case4||limit>function_end)limit=function_end;
    for(uintptr_t p=case4;p+80u<=limit;p++){
        const unsigned char*cursor=(const unsigned char*)p,*finish=(const unsigned char*)limit;usage_member_contract candidate=selected;
#define RANGED_MEMBER_LITERAL(value) do{const unsigned char pattern[]=value;SIZE_T amount=sizeof(pattern)-1u;if((SIZE_T)(finish-cursor)<amount||memcmp(cursor,pattern,amount))goto ranged_member_mismatch;cursor+=amount;}while(0)
#define RANGED_MEMBER_U32(value) do{if((SIZE_T)(finish-cursor)<4u)goto ranged_member_mismatch;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
        RANGED_MEMBER_LITERAL("\x89\xce\x41\x8b\x42");if(cursor>=finish)goto ranged_member_mismatch;candidate.field_selector_field=*cursor++;
        RANGED_MEMBER_LITERAL("\xb9");RANGED_MEMBER_U32(candidate.field_selector_add);
        RANGED_MEMBER_LITERAL("\x01\xc8\x48\x98\x49\x01\xc5\x48\x69\xc6");RANGED_MEMBER_U32(candidate.field_index_multiplier);
        RANGED_MEMBER_LITERAL("\x48\xc1\xe8");if(cursor>=finish)goto ranged_member_mismatch;candidate.field_index_shift=*cursor++;
        RANGED_MEMBER_LITERAL("\x41\x8b\x4c\xf5\x04\xba");RANGED_MEMBER_U32(candidate.field_value1_add);
        RANGED_MEMBER_LITERAL("\x01\xd1\x69\xf8");RANGED_MEMBER_U32(candidate.field_final_multiplier);
        RANGED_MEMBER_LITERAL("\x31\xf9\x81\xf1");RANGED_MEMBER_U32(candidate.field_value1_xor);
        RANGED_MEMBER_LITERAL("\xb2\x01\xe8");if((SIZE_T)(finish-cursor)<4u)goto ranged_member_mismatch;int32_t displacement=0;memcpy(&displacement,cursor,4u);uintptr_t helper=(uintptr_t)(cursor+4u)+(intptr_t)displacement;cursor+=4u;
        RANGED_MEMBER_LITERAL("\x41\x33\x7c\xf5\x00\x81\xf7");RANGED_MEMBER_U32(candidate.field_value0_xor);
        RANGED_MEMBER_LITERAL("\x48\x63\xcf\x48\xc1\xe1");if(cursor>=finish)goto ranged_member_mismatch;uint32_t runtime_field_shift=*cursor++;
        RANGED_MEMBER_LITERAL("\x48\x03\x48");if(cursor>=finish)goto ranged_member_mismatch;uint32_t runtime_fields_offset=*cursor++;
        if(candidate.field_selector_field>4096u||!candidate.field_index_multiplier||!candidate.field_final_multiplier||candidate.field_index_shift>=32u||runtime_field_shift<3u||runtime_field_shift>8u||runtime_fields_offset>0x100u||helper!=pair_contract->type_helper)goto ranged_member_mismatch;
        candidate.field_record_stride=8u;candidate.member_codec=3u;selected=candidate;field_matches++;
ranged_member_mismatch:;
#undef RANGED_MEMBER_U32
#undef RANGED_MEMBER_LITERAL
    }
    limit=case6+256u;if(limit<case6||limit>function_end)limit=function_end;
    for(uintptr_t p=case6;p+32u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;if(memcmp(b,"\x41\x8b\x82",3u)||b[7]!=0xb9||memcmp(b+12,"\x01\xc8\x48\x98\x49\x01\xc5\x48\x8d\x04\x7f\x49\x63\x54\x85\x00",16u))continue;uint32_t field=0,add=0;memcpy(&field,b+3u,4u);memcpy(&add,b+8u,4u);if(field>4096u)continue;selected.method_selector_field=field;selected.method_selector_add=add;selected.method_record_stride=12u;method_matches++;
    }
    for(uintptr_t p=case6;p+18u<=limit;p++){
        const unsigned char*b=(const unsigned char*)p;if(b[0]!=0x48||b[1]!=0x8b||b[2]!=0x0d||memcmp(b+7,"\x48\xc1\xe2",3u)||b[11]!=0x48||b[12]!=0x03||b[13]!=0x51)continue;uintptr_t global=0;uint32_t shift=b[10],field=b[14];if(shift<3u||shift>6u||field>4096u||!rip_target(p,7u,&global)||global!=pair_contract->type_state_global)continue;if(!inst_matches){selected.generic_inst_state_global=global;selected.generic_inst_state_field=field;selected.generic_inst_shift=shift;inst_matches=1u;}else if(selected.generic_inst_state_global!=global||selected.generic_inst_state_field!=field||selected.generic_inst_shift!=shift)return 0;
    }
    if(field_matches!=1u||method_matches!=1u||inst_matches!=1u)return 0;int32_t field_raw=0,method_raw=0;if(!literal_contract->descriptor||!literal_contract->metadata_base||!region_for(literal_contract->descriptor,(SIZE_T)(selected.field_selector_field>selected.method_selector_field?selected.field_selector_field:selected.method_selector_field)+4u,NULL))return 0;memcpy(&field_raw,(const void*)(literal_contract->descriptor+selected.field_selector_field),4u);memcpy(&method_raw,(const void*)(literal_contract->descriptor+selected.method_selector_field),4u);int64_t field_offset=(int64_t)(int32_t)((uint32_t)field_raw+selected.field_selector_add),method_offset=(int64_t)(int32_t)((uint32_t)method_raw+selected.method_selector_add);uintptr_t state=0;if(!add_signed_offset(literal_contract->metadata_base,field_offset,&selected.field_ref_base)||!add_signed_offset(literal_contract->metadata_base,method_offset,&selected.method_spec_base)||!region_for(selected.field_ref_base,8u,NULL)||!region_for(selected.method_spec_base,12u,NULL)||!region_for(selected.generic_inst_state_global,8u,NULL))return 0;memcpy(&state,(const void*)selected.generic_inst_state_global,8u);if(!state||!region_for(state+selected.generic_inst_state_field,8u,NULL))return 0;memcpy(&selected.generic_inst_base,(const void*)(state+selected.generic_inst_state_field),8u);if(!selected.generic_inst_base||selected.generic_inst_base<expected_image_base||selected.generic_inst_base>=expected_image_base+expected_image_bytes||!region_for(selected.generic_inst_base,16u,NULL))return 0;*contract=selected;return 1;
}
static int realize_decoder(decoder_contract*contract){
    if(!region_for(contract->descriptor_global,8u,NULL)||!region_for(contract->metadata_base_global,8u,NULL))return 0;
    memcpy(&contract->descriptor,(const void*)contract->descriptor_global,8u);memcpy(&contract->metadata_base,(const void*)contract->metadata_base_global,8u);
    uint32_t maximum_field=contract->mapping_selector_field>contract->data_selector_field?contract->mapping_selector_field:contract->data_selector_field;
    if(!contract->descriptor||!contract->metadata_base||!region_for(contract->descriptor,(SIZE_T)maximum_field+4u,NULL))return 0;
    int32_t mapping_raw=0,data_raw=0;memcpy(&mapping_raw,(const void*)(contract->descriptor+contract->mapping_selector_field),4u);memcpy(&data_raw,(const void*)(contract->descriptor+contract->data_selector_field),4u);
    int64_t mapping_offset=(contract->selector_codec==2u||contract->selector_codec==3u)?(int64_t)(int32_t)((uint32_t)mapping_raw+(uint32_t)contract->mapping_selector_add):(int64_t)(((uint64_t)(int64_t)mapping_raw)^((uint64_t)(int64_t)contract->mapping_selector_xor));
    int64_t data_offset=contract->selector_codec==2u?(int64_t)(int32_t)((uint32_t)data_raw+(uint32_t)contract->data_selector_add):(int64_t)(((uint64_t)(int64_t)data_raw)^((uint64_t)(int64_t)contract->data_selector_xor));
    return add_signed_offset(contract->metadata_base,mapping_offset,&contract->mapping_base)&&
           add_signed_offset(contract->metadata_base,data_offset,&contract->data_base)&&
           region_for(contract->mapping_base,8192u,NULL)&&region_for(contract->data_base,1u,NULL);
}
#define FAMILY_BYTES(value) do{const unsigned char pattern[]=value;SIZE_T n=sizeof(pattern)-1u;if((SIZE_T)(end-cursor)<n||memcmp(cursor,pattern,n))return 0;cursor+=n;}while(0)
#define FAMILY_U32(value) do{if((SIZE_T)(end-cursor)<4u)return 0;memcpy(&(value),cursor,4u);cursor+=4u;}while(0)
#define FAMILY_U64(value) do{if((SIZE_T)(end-cursor)<8u)return 0;memcpy(&(value),cursor,8u);cursor+=8u;}while(0)
#define FAMILY_U8(value) do{if(cursor>=end)return 0;(value)=*cursor++;}while(0)
static int parse_scalar_range_at(const unsigned char*cursor,const unsigned char*end,usage_pair_contract*contract){
    uint32_t relative=0;uint8_t shift0=0,shift1=0;
    FAMILY_BYTES("\x49\x63\x82");
    FAMILY_U32(contract->range_selector_field);
    FAMILY_BYTES("\x48\x35");
    FAMILY_U32(contract->range_selector_xor);
    FAMILY_BYTES("\x89\xcf");
    FAMILY_BYTES("\x4c\x8b\x25");
    FAMILY_U32(relative);
    FAMILY_BYTES("\x4c\x01\xe0");
    FAMILY_BYTES("\x48\xbb");
    FAMILY_U64(contract->range_wide_multiplier);
    FAMILY_BYTES("\x44\x8b\x04\xb8");
    FAMILY_BYTES("\x48\x0f\xaf\xfb");
    FAMILY_BYTES("\x48\xbe");
    FAMILY_U64(contract->range_wide_add);
    FAMILY_BYTES("\x48\x01\xf7");
    FAMILY_BYTES("\x48\xc1\xef");
    FAMILY_U8(shift0);
    FAMILY_BYTES("\xff\xc1");
    FAMILY_BYTES("\x48\x0f\xaf\xd9");
    FAMILY_BYTES("\x48\x01\xf3");
    FAMILY_BYTES("\x48\xc1\xeb");
    FAMILY_U8(shift1);
    FAMILY_BYTES("\xbe");
    FAMILY_U32(contract->range_final_add);
    FAMILY_BYTES("\x41\x31\xf0");
    FAMILY_BYTES("\x69\xff");
    FAMILY_U32(contract->range_mix_multiplier);
    FAMILY_BYTES("\x81\xc7");
    FAMILY_U32(contract->range_mix_add);
    FAMILY_BYTES("\x81\xf7");
    FAMILY_U32(contract->range_mix_second_xor);
    if(contract->range_selector_field>4096u||!contract->range_wide_multiplier||!contract->range_mix_multiplier||shift0>=64u||shift0!=shift1)return 0;
    contract->range_first_shift=shift0;return 1;
}
static int parse_scalar_pair_at(const unsigned char*cursor,const unsigned char*end,usage_pair_contract*contract){
    uint32_t relative=0;uint8_t kind_shift=0,kind_max=0;
    FAMILY_BYTES("\x44\x89\xf0");
    FAMILY_BYTES("\x35");
    FAMILY_U32(contract->pair_index_xor);
    FAMILY_BYTES("\x69\xc0");
    FAMILY_U32(contract->pair_mix_multiplier);
    FAMILY_BYTES("\x05");
    FAMILY_U32(contract->pair_mix_add);
    FAMILY_BYTES("\x35");
    FAMILY_U32(contract->pair_mix_xor);
    FAMILY_BYTES("\x69\xc8");
    FAMILY_U32(contract->pair_final_multiplier);
    FAMILY_BYTES("\x41\x8b\x82");
    FAMILY_U32(contract->pair_selector_field);
    FAMILY_BYTES("\x44\x01\xc0");
    FAMILY_BYTES("\x48\x63\xf0");
    FAMILY_BYTES("\x4c\x01\xe6");
    FAMILY_BYTES("\x44\x89\xfb");
    FAMILY_BYTES("\x8b\x44\xde\x04");
    FAMILY_BYTES("\x29\xc8");
    FAMILY_BYTES("\x05");
    FAMILY_U32(contract->pair_encoded_add);
    FAMILY_BYTES("\x89\xc7");
    FAMILY_BYTES("\xc1\xef");
    FAMILY_U8(kind_shift);
    FAMILY_BYTES("\x83\xff");
    FAMILY_U8(kind_max);
    FAMILY_BYTES("\x77");
    FAMILY_U8(relative);
    FAMILY_BYTES("\x8b\x34\xde");
    FAMILY_BYTES("\x44\x31\xce");
    FAMILY_BYTES("\x29\xce");
    if(contract->pair_selector_field>4096u||!contract->pair_mix_multiplier||!contract->pair_final_multiplier||kind_shift!=29u||kind_max!=7u)return 0;
    return 1;
}
static int parse_scalar_pair_setup(const unsigned char*cursor,const unsigned char*end,usage_pair_contract*contract){
    FAMILY_BYTES("\x46\x8d\x3c\x07\x41\xff\xc7\x8d\x14\x30\xff\xc2\x44\x29\xfa");
    FAMILY_BYTES("\x45\x69\xf7");
    FAMILY_U32(contract->pair_index_multiplier);
    FAMILY_BYTES("\x41\xb8");
    FAMILY_U32(contract->pair_selector_add);
    FAMILY_BYTES("\x41\xb9");
    FAMILY_U32(contract->pair_destination_xor);
    return contract->pair_index_multiplier!=0;
}
static int parse_scalar_field_at(const unsigned char*cursor,const unsigned char*end,usage_member_contract*contract,uintptr_t type_helper){
    uint32_t relative=0,runtime_field_offset=0;uint8_t runtime_field_shift=0;
    FAMILY_BYTES("\x89\xce");
    FAMILY_BYTES("\x41\x8b\x82");
    FAMILY_U32(contract->field_selector_field);
    FAMILY_BYTES("\xba");
    FAMILY_U32(contract->field_selector_add);
    FAMILY_BYTES("\x01\xd0");
    FAMILY_BYTES("\x48\x98");
    FAMILY_BYTES("\x49\x01\xc4");
    FAMILY_BYTES("\x69\xc1");
    FAMILY_U32(contract->field_index_multiplier);
    FAMILY_BYTES("\x35");
    FAMILY_U32(contract->field_index_xor);
    FAMILY_BYTES("\x44\x69\xe8");
    FAMILY_U32(contract->field_index_mix);
    FAMILY_BYTES("\x41\x81\xc5");
    FAMILY_U32(contract->field_index_bias);
    FAMILY_BYTES("\x41\x81\xf5");
    FAMILY_U32(contract->field_final_multiplier);
    FAMILY_BYTES("\x41\x8b\x0c\xf4");
    FAMILY_BYTES("\xb8");
    FAMILY_U32(contract->field_value0_xor);
    FAMILY_BYTES("\x31\xc1");
    FAMILY_BYTES("\x44\x29\xe9");
    FAMILY_BYTES("\xb2\x01");
    FAMILY_BYTES("\xe8");
    FAMILY_U32(relative);
    uintptr_t helper=(uintptr_t)cursor+(intptr_t)(int32_t)relative;
    FAMILY_BYTES("\x41\x8b\x4c\xf4\x04");
    FAMILY_BYTES("\xba");
    FAMILY_U32(contract->field_value1_xor);
    FAMILY_BYTES("\x31\xd1");
    FAMILY_BYTES("\x44\x29\xe9");
    FAMILY_BYTES("\x48\x63\xc9");
    FAMILY_BYTES("\x48\xc1\xe1");
    FAMILY_U8(runtime_field_shift);
    FAMILY_BYTES("\x48\x03\x48");
    FAMILY_U8(runtime_field_offset);
    if(helper!=type_helper||contract->field_selector_field>4096u||!contract->field_index_multiplier||!contract->field_index_mix||runtime_field_shift<3u||runtime_field_shift>8u||runtime_field_offset>256u)return 0;
    contract->field_record_stride=8u;contract->member_codec=6u;return 1;
}
static int parse_scalar_method_at(const unsigned char*cursor,const unsigned char*end,usage_member_contract*contract){
    FAMILY_BYTES("\x49\x63\x82");
    FAMILY_U32(contract->method_selector_field);
    FAMILY_BYTES("\x48\x35");
    FAMILY_U32(contract->method_selector_add);
    FAMILY_BYTES("\x49\x01\xc4");
    FAMILY_BYTES("\x48\x8d\x04\x7f");
    FAMILY_BYTES("\x49\x63\x54\x84\x04");
    contract->method_record_stride=12u;return contract->method_selector_field<=4096u;
}
static int parse_scalar_inst_at(const unsigned char*cursor,const unsigned char*end,usage_member_contract*contract){
    uintptr_t origin=(uintptr_t)cursor;uint32_t relative=0;
    FAMILY_BYTES("\x48\x8b\x0d");
    FAMILY_U32(relative);
    FAMILY_BYTES("\x48\xc1\xe2");
    FAMILY_U8(contract->generic_inst_shift);
    FAMILY_BYTES("\x48\x03\x51");
    FAMILY_U8(contract->generic_inst_state_field);
    if(contract->generic_inst_shift<3u||contract->generic_inst_shift>6u)return 0;
    uintptr_t global=origin+7u+(intptr_t)(int32_t)relative;
    contract->generic_inst_state_global=global;return 1;
}
#undef FAMILY_BYTES
#undef FAMILY_U32
#undef FAMILY_U64
#undef FAMILY_U8
/* Scalar ranged family: all fields and keys come from the live instruction
 * stream. Unique matches, shared roots, helper identity and readable tables
 * are required before this contract is accepted. */
static int parse_usage_pair_contract_scalar(uintptr_t begin,uintptr_t end,const decoder_contract*literal_contract,usage_pair_contract*contract){
    usage_pair_contract selected={0};uint32_t nr=0,np=0,ns=0;
    for(uintptr_t p=begin;p+16u<=end;p++){
        usage_pair_contract candidate={0};
        if(parse_scalar_range_at((const unsigned char*)p,(const unsigned char*)end,&candidate)){selected.range_selector_field=candidate.range_selector_field;selected.range_selector_xor=candidate.range_selector_xor;selected.range_wide_multiplier=candidate.range_wide_multiplier;selected.range_wide_add=candidate.range_wide_add;selected.range_first_shift=candidate.range_first_shift;selected.range_final_add=candidate.range_final_add;selected.range_mix_multiplier=candidate.range_mix_multiplier;selected.range_mix_add=candidate.range_mix_add;selected.range_mix_second_xor=candidate.range_mix_second_xor;nr++;}
        if(parse_scalar_pair_at((const unsigned char*)p,(const unsigned char*)end,&candidate)){selected.pair_index_xor=candidate.pair_index_xor;selected.pair_mix_multiplier=candidate.pair_mix_multiplier;selected.pair_mix_add=candidate.pair_mix_add;selected.pair_mix_xor=candidate.pair_mix_xor;selected.pair_final_multiplier=candidate.pair_final_multiplier;selected.pair_selector_field=candidate.pair_selector_field;selected.pair_encoded_add=candidate.pair_encoded_add;np++;}
        if(parse_scalar_pair_setup((const unsigned char*)p,(const unsigned char*)end,&candidate)){selected.pair_index_multiplier=candidate.pair_index_multiplier;selected.pair_selector_add=candidate.pair_selector_add;selected.pair_destination_xor=candidate.pair_destination_xor;ns++;}
    }
    if(nr!=1u||np!=1u||ns!=1u)return 0;
    selected.usage_codec=6u;
    if(!realize_usage_pair_contract(&selected,literal_contract))return 0;
    *contract=selected;return 1;
}
static int parse_member_usage_contract_scalar(uintptr_t case4,uintptr_t case6,uintptr_t function_end,const decoder_contract*literal_contract,const usage_pair_contract*pair_contract,usage_member_contract*contract){
    usage_member_contract selected={0};uint32_t nf=0,nm=0,ni=0;
    uintptr_t end4=case4+256u;if(end4>function_end)end4=function_end;
    for(uintptr_t p=case4;p+16u<=end4;p++){usage_member_contract candidate=selected;if(parse_scalar_field_at((const unsigned char*)p,(const unsigned char*)end4,&candidate,pair_contract->type_helper)){selected=candidate;nf++;}}
    uintptr_t end6=case6+256u;if(end6>function_end)end6=function_end;
    for(uintptr_t p=case6;p+16u<=end6;p++){
        usage_member_contract candidate=selected;
        if(parse_scalar_method_at((const unsigned char*)p,(const unsigned char*)end6,&candidate)){selected=candidate;nm++;}
        candidate=selected;
        if(parse_scalar_inst_at((const unsigned char*)p,(const unsigned char*)end6,&candidate)){selected=candidate;ni++;}
    }
    if(nf!=1u||nm!=1u||ni!=1u||selected.generic_inst_state_global!=pair_contract->type_state_global)return 0;
    uint32_t field=0;int32_t method=0;uintptr_t state=0;
    if(!region_for(literal_contract->descriptor+selected.field_selector_field,4u,NULL)||!region_for(literal_contract->descriptor+selected.method_selector_field,4u,NULL))return 0;
    memcpy(&field,(const void*)(literal_contract->descriptor+selected.field_selector_field),4u);memcpy(&method,(const void*)(literal_contract->descriptor+selected.method_selector_field),4u);
    if(!add_signed_offset(literal_contract->metadata_base,(int64_t)(int32_t)(field+selected.field_selector_add),&selected.field_ref_base)||!add_signed_offset(literal_contract->metadata_base,((int64_t)method)^((int64_t)(int32_t)selected.method_selector_add),&selected.method_spec_base)||!read_live_pointer(selected.generic_inst_state_global,0u,&state)||!read_live_pointer(state,selected.generic_inst_state_field,&selected.generic_inst_base)||!selected.generic_inst_base||!region_for(selected.field_ref_base,8u,NULL)||!region_for(selected.method_spec_base,12u,NULL)||!region_for(selected.generic_inst_base,16u,NULL))return 0;
    *contract=selected;return 1;
}
static int validate_switch_candidate(uintptr_t hit,uintptr_t*function,uintptr_t*state_global,uint32_t*case5_field,decoder_contract*contract,usage_pair_contract*pair_contract){
    uintptr_t begin=0,end=0;if(!function_bounds(hit,&begin,&end)||end-begin<256u||end-begin>8192u)return 0;
    const unsigned char*h=(const unsigned char*)hit;
    uint32_t reg=h[1]&7u;if(h[0]!=0xc1||(h[1]&0xf8u)!=0xe8u||h[2]!=0x1du||h[3]!=0x83||h[4]!=(unsigned char)(0xf8u+reg)||h[5]!=7u)return 0;
    int source_mask=0;for(uintptr_t p=hit+6u;p+6u<=end&&p<hit+96u;p++)if(*(const unsigned char*)p==0x81u&&(*(const unsigned char*)(p+1u)&0xf8u)==0xe0u&&*(const uint32_t*)(p+2u)==0x1fffffffu){source_mask=1;break;}if(!source_mask)return 0;
    uintptr_t jump_table=0,targets[8]={0};uint32_t table_matches=0;
    uintptr_t table_limit=hit+96u;if(table_limit>end)table_limit=end;
    for(uintptr_t p=begin;p+7u<=table_limit;p++){
        const unsigned char*b=(const unsigned char*)p;uintptr_t candidate_table=0,candidate_targets[8]={0};uint32_t distinct=0;int valid=1;
        if((b[0]!=0x48&&b[0]!=0x4c)||b[1]!=0x8d||(b[2]&0xc7u)!=0x05u||!rip_target(p,7u,&candidate_table)||!region_for(candidate_table,32u,NULL))continue;
        for(uint32_t i=0;i<8u;i++){int32_t relative=0;memcpy(&relative,(const void*)(candidate_table+i*4u),4u);candidate_targets[i]=candidate_table+(intptr_t)relative;if(candidate_targets[i]<begin||candidate_targets[i]>=end){valid=0;break;}int seen=0;for(uint32_t j=0;j<i;j++)if(candidate_targets[j]==candidate_targets[i])seen=1;if(!seen)distinct++;}
        if(!valid||distinct<6u||candidate_table==jump_table)continue;
        jump_table=candidate_table;memcpy(targets,candidate_targets,sizeof(targets));table_matches++;
    }
    if(table_matches!=1u||!jump_table)return 0;
    if(usage_contract_stage_owner_only<1u)usage_contract_stage_owner_only=1u;
    uintptr_t roots[8]={0};uint32_t fields[8]={0},rooted=0;uintptr_t common_root=0;
    for(uint32_t kind=0;kind<8u;kind++){
        int duplicate=-1;for(uint32_t prior=0;prior<kind;prior++)if(targets[prior]==targets[kind]){duplicate=(int)prior;break;}
        if(duplicate>=0){roots[kind]=roots[duplicate];fields[kind]=fields[duplicate];continue;}
        if(case_root(targets[kind],&roots[kind],&fields[kind])){if(fields[kind]>4096u||common_root&&roots[kind]!=common_root)return 0;if(!common_root)common_root=roots[kind];rooted++;}
    }
    if(rooted<5u||!roots[0]||!roots[1]||!roots[4]||!roots[5]||!roots[7]||fields[1]==fields[4]||fields[1]==fields[5]||fields[4]==fields[5])return 0;
    if(usage_contract_stage_owner_only<2u)usage_contract_stage_owner_only=2u;
    decoder_contract candidate={0};if(!parse_case5_decoder(targets[5],end,&candidate))return 0;if(usage_contract_stage_owner_only<3u)usage_contract_stage_owner_only=3u;if(!derive_decoder_globals(begin,&candidate))return 0;if(usage_contract_stage_owner_only<4u)usage_contract_stage_owner_only=4u;if(!realize_decoder(&candidate))return 0;if(usage_contract_stage_owner_only<5u)usage_contract_stage_owner_only=5u;
    usage_pair_contract pair_candidate={0};if(!parse_usage_pair_contract_scalar(begin,end,&candidate,&pair_candidate)&&!parse_usage_pair_contract_direct(begin,end,&candidate,&pair_candidate)&&!parse_usage_pair_contract_affine(begin,end,&candidate,&pair_candidate)&&!parse_usage_pair_contract_ranged_mix(begin,end,&pair_candidate)&&!parse_usage_pair_contract(begin,end,&pair_candidate))return 0;if(usage_contract_stage_owner_only<6u)usage_contract_stage_owner_only=6u;usage_pairs=pair_candidate;if(pair_candidate.usage_codec!=2u&&pair_candidate.usage_codec!=4u&&!realize_usage_pair_contract(&pair_candidate,&candidate)){usage_pairs=pair_candidate;return 0;}if(!derive_type_record_contract(targets[1],end,&pair_candidate))return 0;if(usage_contract_stage_owner_only<7u)usage_contract_stage_owner_only=7u;usage_member_contract member_candidate={0};if(pair_candidate.usage_codec==6u){if(!parse_member_usage_contract_scalar(targets[4],targets[6],end,&candidate,&pair_candidate,&member_candidate))return 0;}else if(pair_candidate.usage_codec==2u){if(!parse_member_usage_contract_keyed(targets[4],targets[6],end,&candidate,&pair_candidate,&member_candidate))return 0;}else if(pair_candidate.usage_codec==3u){if(!parse_member_usage_contract_ranged_mix(targets[4],targets[6],end,&candidate,&pair_candidate,&member_candidate))return 0;}else if(pair_candidate.usage_codec==4u){if(!parse_member_usage_contract_affine(targets[4],targets[6],end,&candidate,&pair_candidate,&member_candidate))return 0;}else if(!parse_member_usage_contract(targets[4],targets[6],end,&candidate,&pair_candidate,&member_candidate))return 0;memcpy(pair_candidate.case_fields,fields,sizeof(fields));
    uintptr_t root=0,table=0;memcpy(&root,(const void*)roots[1],8u);if(!root||!region_for(root+fields[5],8u,NULL))return 0;memcpy(&table,(const void*)(root+fields[5]),8u);if(!table||!region_for(table,8192u,NULL))return 0;
    uint32_t existing_strings=0;for(uint32_t i=0;i<1024u;i++){uintptr_t value=0;memcpy(&value,(const void*)(table+i*8u),8u);if(string_pointer(value,NULL))existing_strings++;}if(existing_strings<64u)return 0;if(usage_contract_stage_owner_only<8u)usage_contract_stage_owner_only=8u;
    *function=begin;*state_global=roots[1];*case5_field=fields[5];*contract=candidate;*pair_contract=pair_candidate;usage_members=member_candidate;return 1;
}

static int switch_structure(uintptr_t hit,uintptr_t*function,uintptr_t*state_global,uint32_t*case5_field,uintptr_t targets[8],uint32_t fields[8]){
    uintptr_t begin=0,end=0;if(!function_bounds(hit,&begin,&end)||end-begin<256u||end-begin>8192u)return 0;
    const unsigned char*h=(const unsigned char*)hit;
    uint32_t reg=h[1]&7u;if(h[0]!=0xc1||(h[1]&0xf8u)!=0xe8u||h[2]!=0x1du||h[3]!=0x83||h[4]!=(unsigned char)(0xf8u+reg)||h[5]!=7u)return 0;
    int source_mask=0;for(uintptr_t p=hit+6u;p+6u<=end&&p<hit+96u;p++)if(*(const unsigned char*)p==0x81u&&(*(const unsigned char*)(p+1u)&0xf8u)==0xe0u&&*(const uint32_t*)(p+2u)==0x1fffffffu){source_mask=1;break;}
    if(!source_mask)return 0;
    uintptr_t jump_table=0;uint32_t table_matches=0;
    uintptr_t table_limit=hit+96u;if(table_limit>end)table_limit=end;
    for(uintptr_t p=begin;p+7u<=table_limit;p++){
        const unsigned char*b=(const unsigned char*)p;uintptr_t candidate_table=0,candidate_targets[8]={0};uint32_t distinct=0;int valid=1;
        if((b[0]!=0x48&&b[0]!=0x4c)||b[1]!=0x8d||(b[2]&0xc7u)!=0x05u||!rip_target(p,7u,&candidate_table)||!region_for(candidate_table,32u,NULL))continue;
        for(uint32_t i=0;i<8u;i++){int32_t relative=0;memcpy(&relative,(const void*)(candidate_table+i*4u),4u);candidate_targets[i]=candidate_table+(intptr_t)relative;if(candidate_targets[i]<begin||candidate_targets[i]>=end){valid=0;break;}int seen=0;for(uint32_t j=0;j<i;j++)if(candidate_targets[j]==candidate_targets[i])seen=1;if(!seen)distinct++;}
        if(!valid||distinct<6u||candidate_table==jump_table)continue;
        jump_table=candidate_table;memcpy(targets,candidate_targets,sizeof(candidate_targets));table_matches++;
    }
    if(table_matches!=1u||!jump_table)return 0;
    uintptr_t roots[8]={0};uint32_t local_fields[8]={0},rooted=0;uintptr_t common_root=0;
    for(uint32_t kind=0;kind<8u;kind++){
        int duplicate=-1;for(uint32_t prior=0;prior<kind;prior++)if(targets[prior]==targets[kind]){duplicate=(int)prior;break;}
        if(duplicate>=0){roots[kind]=roots[duplicate];local_fields[kind]=local_fields[duplicate];continue;}
        if(case_root(targets[kind],&roots[kind],&local_fields[kind])){if(local_fields[kind]>4096u||(common_root&&roots[kind]!=common_root))return 0;if(!common_root)common_root=roots[kind];rooted++;}
    }
    if(rooted<5u||!roots[0]||!roots[1]||!roots[4]||!roots[5]||!roots[7]||local_fields[1]==local_fields[4]||local_fields[1]==local_fields[5]||local_fields[4]==local_fields[5])return 0;
    *function=begin;*state_global=roots[1];*case5_field=local_fields[5];memcpy(fields,local_fields,sizeof(local_fields));
    return 1;
}
static int bind_usage_state(void){
    memcpy(&usage_state,(const void*)usage_state_global,8u);if(!usage_state||!region_for(usage_state+usage_case5_field,8u,NULL))return 0;
    const uint32_t rooted_kinds[]={0u,1u,3u,4u,5u,7u};for(uint32_t i=0;i<sizeof(rooted_kinds)/sizeof(rooted_kinds[0]);i++){uint32_t kind=rooted_kinds[i];if(!region_for(usage_state+usage_case_fields[kind],8u,NULL))return 0;memcpy(&usage_case_tables[kind],(const void*)(usage_state+usage_case_fields[kind]),8u);if(!usage_case_tables[kind]||usage_case_tables[kind]<expected_image_base||usage_case_tables[kind]>=expected_image_base+expected_image_bytes||!region_for(usage_case_tables[kind],8u,NULL))return 0;}usage_case_tables[6]=usage_case_tables[3];
    usage_table=usage_case_tables[5];return usage_table&&region_for(usage_table,8192u,NULL);
}
static int derive_usage_contract_v2(uintptr_t begin,const uintptr_t targets[8],const uint32_t fields[8]){
    usage_contract_stage_owner_only=30u;
    if(!usage_v2_available){usage_contract_stage_owner_only=31u;return 0;}
    if(usage_v2_method_spec_stride!=12u||usage_v2_generic_stride!=16u){usage_contract_stage_owner_only=32u;return 0;}
    uintptr_t descriptor=0,metadata_base_live=0;
    read_live_pointer(usage_v2_descriptor_global,0u,&descriptor);
    read_live_pointer(usage_v2_metadata_base_global,0u,&metadata_base_live);
    if(!descriptor||!metadata_base_live){usage_contract_stage_owner_only=38u;return 0;}
    if(!region_for(descriptor,0x400u,NULL)){usage_contract_stage_owner_only=33u;return 0;}
    const unsigned char*d=(const unsigned char*)descriptor;
    uint32_t range_field=0,pair_field=0,field_field=0,method_field=0;
    memcpy(&range_field,d+usage_v2_range_field,4u);
    memcpy(&pair_field,d+usage_v2_pair_field,4u);
    memcpy(&field_field,d+usage_v2_field_base_field,4u);
    memcpy(&method_field,d+usage_v2_method_spec_field,4u);
    uintptr_t metadata_base=metadata_base_live;
    uintptr_t range_base=metadata_base+(intptr_t)(int32_t)(range_field+usage_v2_range_add);
    uintptr_t pair_base=metadata_base+(intptr_t)(int32_t)(pair_field^usage_v2_pair_bias);
    uintptr_t field_base=metadata_base+(intptr_t)(int32_t)(field_field^usage_v2_field_base_xor);
    uintptr_t method_base=metadata_base+(intptr_t)(int32_t)(method_field^usage_v2_method_spec_xor);
    if(!region_for(range_base,8u,NULL)){usage_contract_stage_owner_only=34u;return 0;}
    if(!region_for(pair_base,8u,NULL)){usage_contract_stage_owner_only=35u;return 0;}
    if(!region_for(field_base,8u,NULL)){usage_contract_stage_owner_only=36u;return 0;}
    if(!region_for(method_base,12u,NULL)){usage_contract_stage_owner_only=37u;return 0;}
    memset(&usage_pairs,0,sizeof(usage_pairs));
    usage_pairs.usage_codec=5u;
    usage_pairs.range_base=range_base;
    usage_pairs.pair_base=pair_base;
    usage_pairs.type_record_base=usage_v2_type_record_base;
    usage_pairs.type_record_shift=usage_v2_type_record_shift;
    usage_pairs.type_helper=usage_v2_type_helper;
    usage_pairs.type_state_global=usage_v2_type_state_global;
    usage_pairs.type_state_field=usage_v2_type_state_field;
    /*
     * Kind-1 type usages resolve their generic instances through the type
     * code's own 0x15 arm, which is a different table from the method spec
     * generic instance table the member inventory uses.  The base lives in a
     * global's field, so it is read live here instead of being templated.
     */
    usage_pairs.generic_state_global=usage_v2_type_generic_state_global;
    usage_pairs.generic_state_field=usage_v2_type_generic_state_field;
    usage_pairs.generic_record_shift=usage_v2_type_generic_stride_shift;
    uintptr_t type_generic_base=0;
    if(!usage_v2_type_generic_state_global||usage_v2_type_generic_stride_shift<4u||usage_v2_type_generic_stride_shift>8u||!read_live_pointer(usage_v2_type_generic_state_global,usage_v2_type_generic_state_field,&type_generic_base)){usage_contract_stage_owner_only=39u;return 0;}
    if(!type_generic_base){usage_contract_stage_owner_only=40u;return 0;}
    usage_pairs.generic_record_base=type_generic_base;
    memcpy(usage_pairs.case_fields,fields,sizeof(usage_pairs.case_fields));
    memset(&usage_members,0,sizeof(usage_members));
    usage_members.member_codec=5u;
    usage_members.field_ref_base=field_base;
    usage_members.field_record_stride=8u;
    usage_members.method_spec_base=method_base;
    usage_members.method_record_stride=12u;
    usage_members.generic_inst_base=usage_v2_generic_base;
    usage_members.generic_inst_shift=4u;
    usage_members.generic_inst_state_global=usage_v2_generic_state_global;
    usage_members.generic_inst_state_field=usage_v2_generic_state_field;
    usage_members.field_selector_field=usage_v2_field_base_field;
    usage_members.field_index_multiplier=usage_v2_field_index_multiplier;
    usage_members.field_index_xor=usage_v2_field_index_xor;
    usage_members.field_index_mix=usage_v2_field_index_mix;
    usage_members.field_index_bias=usage_v2_field_index_add;
    usage_members.field_final_multiplier=usage_v2_field_index_final_xor;
    usage_members.field_value0_xor=usage_v2_field_value0_xor;
    usage_members.field_value1_xor=usage_v2_field_value1_xor;
    memset(&decoder,0,sizeof(decoder));
    decoder.case5_target=targets[5];
    decoder.literal_codec=1u;
    decoder.descriptor=descriptor;
    decoder.metadata_base=metadata_base;
    usage_v2_live_descriptor=descriptor;
    usage_v2_live_metadata_base=metadata_base_live;
    usage_v2_selected=1u;
    return 1;
}
static int derive_usage_contract_v2_scan(HMODULE image){
    usage_contract_stage_owner_only=20u;
    IMAGE_SECTION_HEADER*sections=NULL;uint16_t section_count=0;if(!executable_sections(image,&sections,&section_count))return 0;
    uintptr_t selected=0,selected_global=0,selected_targets[8]={0};uint32_t selected_field=0,selected_fields[8]={0},hits=0;
    for(uint16_t s=0;s<section_count;s++){
        if(!(sections[s].Characteristics&IMAGE_SCN_MEM_EXECUTE))continue;
        uintptr_t begin=(uintptr_t)image+sections[s].VirtualAddress;uint64_t amount=sections[s].Misc.VirtualSize;if(amount<sections[s].SizeOfRawData)amount=sections[s].SizeOfRawData;if(!amount||sections[s].VirtualAddress+amount>expected_image_bytes)continue;uintptr_t end=begin+(uintptr_t)amount;
        for(uintptr_t p=begin;p+6u<=end;p++){const unsigned char*b=(const unsigned char*)p;if(b[0]!=0xc1||(b[1]&0xf8u)!=0xe8u||b[2]!=0x1du||b[3]!=0x83||b[4]!=(unsigned char)(b[1]+0x10u)||b[5]!=7u)continue;uintptr_t function=0,global=0,targets[8]={0};uint32_t field=0,fields[8]={0};if(switch_structure(p,&function,&global,&field,targets,fields)){if(function!=selected){selected=function;selected_global=global;selected_field=field;memcpy(selected_targets,targets,sizeof(targets));memcpy(selected_fields,fields,sizeof(fields));hits++;}}}
    }
    if(hits!=1u||!selected)return 0;
    usage_contract_stage_owner_only=21u;
    if(!derive_usage_contract_v2(selected,selected_targets,selected_fields))return 0;
    usage_contract_stage_owner_only=22u;
    usage_initializer=selected;usage_state_global=selected_global;usage_case5_field=selected_field;usage_switch_entries=8u;
    memcpy(usage_case_fields,selected_fields,sizeof(usage_case_fields));
    return 1;
}
static int derive_usage_contract(HMODULE image){
    IMAGE_SECTION_HEADER*sections=NULL;uint16_t section_count=0;if(!executable_sections(image,&sections,&section_count))return 0;
    uintptr_t selected=0,selected_global=0;uint32_t selected_field=0,candidates=0;decoder_contract selected_decoder={0};usage_pair_contract selected_pairs={0};
    for(uint16_t s=0;s<section_count;s++){
        if(!(sections[s].Characteristics&IMAGE_SCN_MEM_EXECUTE))continue;
        uintptr_t begin=(uintptr_t)image+sections[s].VirtualAddress;uint64_t amount=sections[s].Misc.VirtualSize;if(amount<sections[s].SizeOfRawData)amount=sections[s].SizeOfRawData;if(!amount||sections[s].VirtualAddress+amount>expected_image_bytes)continue;uintptr_t end=begin+(uintptr_t)amount;
        for(uintptr_t p=begin;p+6u<=end;p++){const unsigned char*b=(const unsigned char*)p;if(b[0]!=0xc1||(b[1]&0xf8u)!=0xe8u||b[2]!=0x1du||b[3]!=0x83||b[4]!=(unsigned char)(b[1]+0x10u)||b[5]!=7u)continue;uintptr_t function=0,global=0;uint32_t field=0;decoder_contract candidate={0};usage_pair_contract pair_candidate={0};if(validate_switch_candidate(p,&function,&global,&field,&candidate,&pair_candidate)){if(function!=selected){selected=function;selected_global=global;selected_field=field;selected_decoder=candidate;selected_pairs=pair_candidate;candidates++;}}}
    }
    if(candidates!=1u||!selected){
        /* Preserve the real discovery stage when there is no optional v2
         * contract; an unavailable fallback must not overwrite the cause. */
        if(!usage_v2_available)return 0;
        if(!derive_usage_contract_v2_scan(image))return 0;
        return bind_usage_state();
    }
    usage_initializer=selected;usage_state_global=selected_global;usage_case5_field=selected_field;usage_switch_entries=8u;decoder=selected_decoder;usage_pairs=selected_pairs;memcpy(usage_case_fields,selected_pairs.case_fields,sizeof(usage_case_fields));
    memcpy(&usage_state,(const void*)usage_state_global,8u);if(!usage_state||!region_for(usage_state+usage_case5_field,8u,NULL))return 0;
    const uint32_t rooted_kinds[]={0u,1u,3u,4u,5u,7u};for(uint32_t i=0;i<sizeof(rooted_kinds)/sizeof(rooted_kinds[0]);i++){uint32_t kind=rooted_kinds[i];if(!region_for(usage_state+usage_case_fields[kind],8u,NULL))return 0;memcpy(&usage_case_tables[kind],(const void*)(usage_state+usage_case_fields[kind]),8u);if(!usage_case_tables[kind]||usage_case_tables[kind]<expected_image_base||usage_case_tables[kind]>=expected_image_base+expected_image_bytes||!region_for(usage_case_tables[kind],8u,NULL))return 0;}usage_case_tables[6]=usage_case_tables[3];
    usage_table=usage_case_tables[5];return usage_table&&region_for(usage_table,8192u,NULL);
}
static int visit_initializer_calls(HMODULE image,unsigned char*seen,uint64_t capacity,uint64_t*sites,uint64_t*maximum){
    IMAGE_SECTION_HEADER*sections=NULL;uint16_t section_count=0;if(!executable_sections(image,&sections,&section_count))return 0;uint64_t count=0,max_index=0;
    for(uint16_t s=0;s<section_count;s++){
        if(!(sections[s].Characteristics&IMAGE_SCN_MEM_EXECUTE))continue;
        uintptr_t begin=(uintptr_t)image+sections[s].VirtualAddress;uint64_t amount=sections[s].Misc.VirtualSize;if(amount<sections[s].SizeOfRawData)amount=sections[s].SizeOfRawData;if(!amount||sections[s].VirtualAddress+amount>expected_image_bytes)continue;uintptr_t end=begin+(uintptr_t)amount;
        for(uintptr_t p=begin+5u;p+5u<=end;p++){if(*(const unsigned char*)p!=0xe8u)continue;int32_t displacement=0;memcpy(&displacement,(const void*)(p+1u),4u);if(p+5u+(intptr_t)displacement!=usage_initializer)continue;uint32_t index=UINT32_MAX;if(*(const unsigned char*)(p-5u)==0xb9u)memcpy(&index,(const void*)(p-4u),4u);else if((*(const unsigned char*)(p-2u)==0x31u||*(const unsigned char*)(p-2u)==0x33u)&&*(const unsigned char*)(p-1u)==0xc9u)index=0u;else continue;if(index>=2000000u)return 0;count++;if(index>max_index)max_index=index;if(seen&&index<capacity)seen[index]=1u;}
    }
    *sites=count;*maximum=max_index;return count>=1024u&&max_index>=1024u;
}
static int derive_call_site_coverage(HMODULE image){
    uint64_t sites=0,maximum=0;if(!visit_initializer_calls(image,NULL,0,&sites,&maximum)||maximum+1u>2000000u)return 0;
    unsigned char*seen=calloc((SIZE_T)(maximum+1u),1u);if(!seen)return 0;if(!visit_initializer_calls(image,seen,maximum+1u,&sites,&maximum)){free(seen);return 0;}
    uint64_t unique=0;for(uint64_t i=0;i<=maximum;i++)if(seen[i])unique++;
    uint32_t coverage=(uint32_t)((unique*1000u)/(maximum+1u));if(unique<1024u||coverage<990u){free(seen);return 0;}
    usage_call_sites=sites;usage_unique_indices=unique;usage_max_index=maximum;usage_coverage_per_mille=coverage;free(seen);return 1;
}
static uint32_t decode_usage_range_value(uint32_t index,uint32_t encrypted){
    if(usage_pairs.usage_codec==6u){uint64_t wide=(uint64_t)index*usage_pairs.range_wide_multiplier+usage_pairs.range_wide_add;wide>>=usage_pairs.range_first_shift;uint32_t key=(uint32_t)wide*usage_pairs.range_mix_multiplier+usage_pairs.range_mix_add;key^=usage_pairs.range_mix_second_xor;/* This handler increments both bounds before iterating: normalize
         * the encoded -1 sentinel into the half-open [0,N) domain. */
        return (encrypted^usage_pairs.range_final_add)+key+1u;}
    if(usage_pairs.usage_codec==5u){uint64_t mixed=(uint64_t)index*usage_v2_range_multiplier;mixed>>=usage_v2_range_shift1;mixed=(mixed*usage_v2_range_second);mixed>>=usage_v2_range_shift2;return (encrypted^((uint32_t)mixed*usage_v2_range_mix))^usage_v2_range_xor;}
    if(usage_pairs.usage_codec==3u){uint64_t mixed=(uint64_t)index*usage_pairs.range_index_multiplier;mixed^=usage_pairs.range_mix_xor;mixed*=usage_pairs.range_mix_multiplier;mixed>>=usage_pairs.range_first_shift;mixed*=usage_pairs.range_mid_multiplier;mixed+=usage_pairs.range_wide_add;mixed>>=usage_pairs.range_second_shift;mixed*=usage_pairs.range_final_multiplier;mixed>>=usage_pairs.range_third_shift;return encrypted-(uint32_t)mixed+usage_pairs.range_final_add;}
    uint32_t mixed=index*usage_pairs.range_index_multiplier;mixed^=usage_pairs.range_mix_xor;mixed*=usage_pairs.range_mix_multiplier;mixed^=usage_pairs.range_mix_second_xor;mixed+=usage_pairs.range_mix_add;return (encrypted+usage_pairs.range_final_add)^mixed;
}
static uint32_t decode_usage_pair_key(uint32_t index){
    if(usage_pairs.usage_codec==6u){uint32_t key=index*usage_pairs.pair_index_multiplier;key^=usage_pairs.pair_index_xor;key*=usage_pairs.pair_mix_multiplier;key+=usage_pairs.pair_mix_add;key^=usage_pairs.pair_mix_xor;return key*usage_pairs.pair_final_multiplier;}
    if(usage_pairs.usage_codec==5u){uint64_t mixed=(uint64_t)index*usage_v2_pair_multiplier;mixed>>=usage_v2_pair_shift;mixed^=usage_v2_pair_xor;mixed=(mixed*usage_v2_pair_second);mixed>>=usage_v2_pair_shift2;return (uint32_t)mixed;}
    uint64_t mixed=(uint64_t)index*usage_pairs.pair_index_multiplier;mixed^=usage_pairs.pair_index_xor;mixed*=usage_pairs.pair_mix_multiplier;mixed>>=usage_pairs.pair_shift;mixed+=usage_pairs.pair_mix_add;mixed^=usage_pairs.pair_mix_xor;mixed*=usage_pairs.pair_final_multiplier;mixed>>=usage_pairs.pair_final_shift;return (uint32_t)mixed;
}
static int usage_record_compare(const void*left,const void*right){const usage_output_record*a=left,*b=right;if(a->slot_pointer<b->slot_pointer)return -1;if(a->slot_pointer>b->slot_pointer)return 1;if(a->usage_kind<b->usage_kind)return -1;if(a->usage_kind>b->usage_kind)return 1;if(a->source_index<b->source_index)return -1;if(a->source_index>b->source_index)return 1;return 0;}
static void free_decoded_usage_inventory(decoded_usage_inventory*inventory){if(!inventory)return;free(inventory->records);memset(inventory,0,sizeof(*inventory));}
static int hash_decoded_usage_inventory(decoded_usage_inventory*inventory){
    BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char*object=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0&&object_size&&received==sizeof(object_size);if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok&&!object)ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;if(ok&&inventory->count&&BCryptHashData(hash,(PUCHAR)inventory->records,(ULONG)(inventory->count*sizeof(*inventory->records)),0)<0)ok=0;if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)>=0)digest_hex(digest,inventory->content_sha256);else ok=0;if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);return ok;
}
static int decode_usage_inventory(HMODULE image,decoded_usage_inventory*inventory){
    memset(inventory,0,sizeof(*inventory));usage_decode_failure_index=UINT64_MAX;usage_decode_failure_stage=usage_decode_failure_raw0=usage_decode_failure_raw1=usage_decode_failure_value0=usage_decode_failure_value1=0;uint64_t sites=0,maximum=0;if(!visit_initializer_calls(image,NULL,0,&sites,&maximum)||maximum!=usage_max_index||maximum+2u>2000000u){usage_decode_failure_stage=1u;return 0;}uint64_t range_count=maximum+2u;if(!region_for(usage_pairs.range_base,(SIZE_T)(range_count*4u),NULL)){usage_decode_failure_stage=2u;return 0;}
    unsigned char*seen=calloc((SIZE_T)(maximum+1u),1u);uint32_t*ranges=calloc((SIZE_T)range_count,sizeof(*ranges));if(!seen||!ranges){free(seen);free(ranges);return 0;}if(!visit_initializer_calls(image,seen,maximum+1u,&sites,&maximum)){free(seen);free(ranges);return 0;}
    if(usage_pairs.usage_codec==2u||usage_pairs.usage_codec==4u){
        free(ranges);ranges=NULL;if(!region_for(usage_pairs.direct_pair_base,(SIZE_T)(maximum+1u)*8u,NULL)){free(seen);return 0;}
        usage_output_record*expanded=calloc((SIZE_T)(maximum+1u),sizeof(*expanded));if(!expanded){free(seen);return 0;}uint64_t occurrences=0;int ok=1;
        for(uint64_t i=0;i<=maximum;i++){uint32_t raw_encoded=0,raw_destination=0;memcpy(&raw_encoded,(const void*)(usage_pairs.direct_pair_base+i*8u),4u);memcpy(&raw_destination,(const void*)(usage_pairs.direct_pair_base+i*8u+4u),4u);uint64_t mixed=(uint64_t)(uint32_t)i*usage_pairs.direct_index_multiplier+usage_pairs.direct_index_add;mixed>>=usage_pairs.direct_index_shift;uint32_t key=0,encoded=0,destination=0;if(usage_pairs.usage_codec==4u){key=(uint32_t)mixed*usage_pairs.direct_key_multiplier+usage_pairs.direct_key_add;encoded=raw_encoded^key^usage_pairs.direct_encoded_xor;destination=(raw_destination+usage_pairs.direct_destination_add)^key;}else{mixed*=usage_pairs.direct_key_multiplier;mixed>>=usage_pairs.direct_key_shift;key=(uint32_t)mixed;encoded=raw_encoded-key+usage_pairs.direct_encoded_add;destination=(raw_destination^usage_pairs.direct_destination_xor)-key+usage_pairs.direct_destination_add;}uint32_t kind=encoded>>29u,source=encoded&0x1fffffffu,slot_index=(kind==0u||kind==7u)?destination&0xffffffu:destination;if(kind==2u||(usage_pairs.usage_codec==2u&&(kind==0u||kind==7u)))continue;if(kind>=8u||!usage_case_tables[kind]||slot_index>(expected_image_bytes/8u)){ok=0;break;}uintptr_t slot=usage_case_tables[kind]+(uintptr_t)slot_index*8u;if(slot<expected_image_base||slot>=expected_image_base+expected_image_bytes||(slot&7u)){ok=0;break;}expanded[occurrences++]=(usage_output_record){(uint32_t)i,destination,kind,source,slot};}
        free(seen);if(!ok||occurrences<1024u){free(expanded);return 0;}qsort(expanded,(SIZE_T)occurrences,sizeof(*expanded),usage_record_compare);uint64_t unique=0;for(uint64_t i=0;i<occurrences;i++){if(unique&&expanded[i].slot_pointer==expanded[unique-1u].slot_pointer){if(expanded[i].usage_kind!=expanded[unique-1u].usage_kind||expanded[i].source_index!=expanded[unique-1u].source_index||expanded[i].destination_index!=expanded[unique-1u].destination_index){free(expanded);return 0;}if(expanded[i].first_occurrence_index<expanded[unique-1u].first_occurrence_index)expanded[unique-1u].first_occurrence_index=expanded[i].first_occurrence_index;continue;}expanded[unique++]=expanded[i];}
        if(unique<1024u){free(expanded);return 0;}usage_output_record*records=realloc(expanded,(SIZE_T)(unique*sizeof(*records)));if(!records)records=expanded;inventory->records=records;inventory->count=unique;inventory->occurrence_count=occurrences;for(uint64_t i=0;i<unique;i++)inventory->kind_counts[records[i].usage_kind]++;usage_uncovered_nonempty_ranges=0;if(!hash_decoded_usage_inventory(inventory)){free_decoded_usage_inventory(inventory);return 0;}return 1;
    }
    for(uint32_t sample=0;sample<4u&&sample<range_count;sample++){memcpy(&usage_range_sample_raw[sample],(const void*)(usage_pairs.range_base+(uintptr_t)sample*4u),4u);usage_range_sample_value[sample]=decode_usage_range_value(sample,usage_range_sample_raw[sample]);}
    int ok=1;for(uint64_t i=0;i<range_count;i++){uint32_t encrypted=0;memcpy(&encrypted,(const void*)(usage_pairs.range_base+i*4u),4u);ranges[i]=decode_usage_range_value((uint32_t)i,encrypted);if((i==0u&&ranges[i]!=0u)||(i&&ranges[i]<ranges[i-1])||ranges[i]>2000000u){usage_decode_failure_stage=3u;usage_decode_failure_index=i;usage_decode_failure_raw0=encrypted;usage_decode_failure_value0=ranges[i];usage_decode_failure_value1=i?ranges[i-1u]:0u;ok=0;break;}}
    uint64_t occurrences=ok?ranges[range_count-1u]:0u;usage_uncovered_nonempty_ranges=0;for(uint64_t i=0;ok&&i<=maximum;i++)if(!seen[i]&&ranges[i]!=ranges[i+1u])usage_uncovered_nonempty_ranges++;free(seen);if(!ok||occurrences<1024u||!region_for(usage_pairs.pair_base,(SIZE_T)(occurrences*8u),NULL)){if(!usage_decode_failure_stage)usage_decode_failure_stage=4u;usage_decode_failure_value0=(uint32_t)occurrences;free(ranges);return 0;}
    usage_output_record*expanded=calloc((SIZE_T)occurrences,sizeof(*expanded));if(!expanded){usage_decode_failure_stage=5u;free(ranges);return 0;}for(uint64_t i=0;ok&&i<occurrences;i++){uint32_t raw_destination=0,raw_encoded=0;memcpy(&raw_destination,(const void*)(usage_pairs.pair_base+i*8u),4u);memcpy(&raw_encoded,(const void*)(usage_pairs.pair_base+i*8u+4u),4u);uint32_t key=0,destination=0,encoded=0,source=0;if(usage_pairs.usage_codec==5u){uint32_t mixed=decode_usage_pair_key((uint32_t)i);encoded=(raw_destination+usage_v2_pair_add)^mixed;destination=(raw_encoded+usage_v2_pair_value_add)^mixed;source=encoded&0x1fffffffu;}else if(usage_pairs.usage_codec==6u){key=decode_usage_pair_key((uint32_t)i);encoded=raw_encoded-key+usage_pairs.pair_encoded_add;destination=(raw_destination^usage_pairs.pair_destination_xor)-key;source=encoded&0x1fffffffu;}else if(usage_pairs.usage_codec==3u){key=((uint32_t)i*usage_pairs.pair_index_multiplier^usage_pairs.pair_index_xor)*usage_pairs.pair_mix_multiplier;encoded=raw_destination^key;destination=raw_encoded^key^usage_pairs.pair_destination_xor;source=(encoded&0x1fffffffu)^usage_pairs.pair_source_xor;}else{key=decode_usage_pair_key((uint32_t)i);destination=raw_destination-key+usage_pairs.pair_destination_add;encoded=raw_encoded-key+usage_pairs.pair_encoded_add;source=encoded&0x1fffffffu;}uint32_t kind=encoded>>29u,slot_index=destination;if(kind==0u||kind==7u)slot_index&=0xffffffu;if(kind>=8u||kind==2u||!usage_case_tables[kind]||slot_index>(expected_image_bytes/8u)){usage_decode_failure_stage=6u;usage_decode_failure_index=i;usage_decode_failure_raw0=raw_destination;usage_decode_failure_raw1=raw_encoded;usage_decode_failure_value0=destination;usage_decode_failure_value1=encoded;ok=0;break;}uintptr_t slot=usage_case_tables[kind]+(uintptr_t)slot_index*8u;if(slot<expected_image_base||slot>=expected_image_base+expected_image_bytes||(slot&7u)){usage_decode_failure_stage=7u;usage_decode_failure_index=i;usage_decode_failure_raw0=raw_destination;usage_decode_failure_raw1=raw_encoded;usage_decode_failure_value0=destination;usage_decode_failure_value1=encoded;ok=0;break;}expanded[i]=(usage_output_record){(uint32_t)i,destination,kind,source,slot};}
    free(ranges);if(!ok){free(expanded);return 0;}qsort(expanded,(SIZE_T)occurrences,sizeof(*expanded),usage_record_compare);uint64_t unique=0;for(uint64_t i=0;i<occurrences;i++){if(unique&&expanded[i].slot_pointer==expanded[unique-1u].slot_pointer){if(expanded[i].usage_kind!=expanded[unique-1u].usage_kind||expanded[i].source_index!=expanded[unique-1u].source_index||expanded[i].destination_index!=expanded[unique-1u].destination_index){ok=0;break;}if(expanded[i].first_occurrence_index<expanded[unique-1u].first_occurrence_index)expanded[unique-1u].first_occurrence_index=expanded[i].first_occurrence_index;continue;}expanded[unique++]=expanded[i];}
    if(!ok||unique<1024u){free(expanded);return 0;}usage_output_record*records=realloc(expanded,(SIZE_T)(unique*sizeof(*records)));if(!records)records=expanded;inventory->records=records;inventory->count=unique;inventory->occurrence_count=occurrences;for(uint64_t i=0;i<unique;i++)inventory->kind_counts[records[i].usage_kind]++;if(!hash_decoded_usage_inventory(inventory)){free_decoded_usage_inventory(inventory);return 0;}return 1;
}
static void free_decoded_usage_value_inventory(decoded_usage_value_inventory*inventory){if(!inventory)return;free(inventory->records);free(inventory->generic_records);memset(inventory,0,sizeof(*inventory));}
static int hash_decoded_usage_value_inventory(decoded_usage_value_inventory*inventory){
    BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char*object=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0&&object_size&&received==sizeof(object_size);if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok&&!object)ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;if(ok&&inventory->count&&BCryptHashData(hash,(PUCHAR)inventory->records,(ULONG)(inventory->count*sizeof(*inventory->records)),0)<0)ok=0;if(ok&&inventory->generic_record_count&&BCryptHashData(hash,(PUCHAR)inventory->generic_records,(ULONG)(inventory->generic_record_count*sizeof(*inventory->generic_records)),0)<0)ok=0;if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)>=0)digest_hex(digest,inventory->content_sha256);else ok=0;if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);return ok;
}
static int snapshot_usage_values(const decoded_usage_inventory*usage,decoded_usage_value_inventory*inventory){
    memset(inventory,0,sizeof(*inventory));usage_value_failure_index=UINT64_MAX;usage_value_failure_stage=usage_value_failure_source=usage_value_failure_type_code=0;usage_value_failure_pointer=0;if(!usage||!usage->records||!usage->count||!usage_pairs.type_record_base||usage_pairs.type_record_shift>=63u||!usage_pairs.generic_record_base||usage_pairs.generic_record_shift>=63u||usage->count>SIZE_MAX/sizeof(usage_value_output_record)){usage_value_failure_stage=1u;return 0;}usage_value_output_record*records=calloc((SIZE_T)usage->count,sizeof(*records));if(!records){usage_value_failure_stage=2u;return 0;}int ok=1;uint64_t type_stride=1ull<<usage_pairs.type_record_shift,generic_stride=1ull<<usage_pairs.generic_record_shift,max_type_source=0;
    for(uint64_t i=0;i<usage->count;i++){const usage_output_record*source=&usage->records[i];usage_value_output_record*target=&records[i];uintptr_t value=0;usage_value_failure_index=i;usage_value_failure_source=source->source_index;usage_value_failure_pointer=(uintptr_t)source->slot_pointer;if(!region_for((uintptr_t)source->slot_pointer,8u,NULL)){usage_value_failure_stage=3u;ok=0;break;}memcpy(&value,(const void*)(uintptr_t)source->slot_pointer,8u);target->first_occurrence_index=source->first_occurrence_index;target->destination_index=source->destination_index;target->usage_kind=source->usage_kind;target->source_index=source->source_index;target->slot_pointer=source->slot_pointer;target->slot_value=value;if(value)inventory->nonzero_value_count++;
        if(source->usage_kind==1u){if(type_stride<16u||source->source_index>(expected_image_bytes-16u)/type_stride){usage_value_failure_stage=4u;ok=0;break;}if(source->source_index>max_type_source)max_type_source=source->source_index;uintptr_t type_record=usage_pairs.type_record_base+(uintptr_t)source->source_index*(uintptr_t)type_stride;usage_value_failure_pointer=type_record;if(type_record<expected_image_base||type_record+16u<type_record||type_record+16u>expected_image_base+expected_image_bytes||!region_for(type_record,16u,NULL)){usage_value_failure_stage=5u;ok=0;break;}target->type_record_pointer=type_record;memcpy(&target->type_record_data,(const void*)type_record,8u);memcpy(&target->type_record_bits,(const void*)(type_record+8u),8u);uint32_t type_code=(uint32_t)((target->type_record_bits>>16u)&0xffu);usage_value_failure_type_code=type_code;if(type_code<1u||type_code>0x1eu){usage_value_failure_stage=6u;ok=0;break;}
            if(type_code==0x14u||type_code==0x1du){uintptr_t related=(uintptr_t)target->type_record_data;if(type_code==0x14u){usage_value_failure_pointer=related;if(!region_for(related,16u,NULL)){usage_value_failure_stage=9u;ok=0;break;}memcpy(&related,(const void*)related,8u);memcpy(&target->related_aux,(const void*)((uintptr_t)target->type_record_data+8u),8u);}usage_value_failure_pointer=related;if(!related||!region_for(related,16u,NULL)){usage_value_failure_stage=10u;ok=0;break;}target->related_pointer=related;memcpy(&target->related_data,(const void*)related,8u);memcpy(&target->related_bits,(const void*)(related+8u),8u);}
            if(type_code==0x15u){int32_t generic_index=(int32_t)(uint32_t)target->type_record_data;if(generic_index<0||generic_stride<32u||(uint64_t)(uint32_t)generic_index>(UINTPTR_MAX-usage_pairs.generic_record_base)/generic_stride){usage_value_failure_stage=11u;ok=0;break;}uintptr_t generic_record=usage_pairs.generic_record_base+(uintptr_t)(uint32_t)generic_index*(uintptr_t)generic_stride;usage_value_failure_pointer=generic_record;if(!usage_v2_selected){if(!region_for(generic_record,32u,NULL)){usage_value_failure_stage=12u;ok=0;break;}target->generic_record_pointer=generic_record;memcpy(&target->generic_qword0,(const void*)generic_record,8u);memcpy(&target->generic_qword1,(const void*)(generic_record+8u),8u);memcpy(&target->generic_qword2,(const void*)(generic_record+16u),8u);memcpy(&target->generic_qword3,(const void*)(generic_record+24u),8u);}else{/* The client keeps reallocating the type generic table while it runs; the derived contract records the derived base and index relation and leaves the volatile contents to the consumer. */target->generic_record_pointer=generic_record;}}
            inventory->kind1_count++;}
    }
    if(ok&&inventory->kind1_count!=usage->kind_counts[1]){usage_value_failure_stage=7u;ok=0;}uint64_t maximum_generic=0;int generic_found=0;usage_generic_output_record*generic_records=NULL;if(ok&&usage_v2_selected){/* the current build resolves generic instances through the member contract, so the classic 32-byte generic record array does not exist for it */maximum_generic=0;generic_found=0;}else if(ok){for(uint64_t source=0;source<=max_type_source;source++){uintptr_t pointer=usage_pairs.type_record_base+(uintptr_t)source*(uintptr_t)type_stride;uint64_t data=0,bits=0;if(!region_for(pointer,16u,NULL)){usage_value_failure_stage=13u;usage_value_failure_index=source;usage_value_failure_pointer=pointer;ok=0;break;}memcpy(&data,(const void*)pointer,8u);memcpy(&bits,(const void*)(pointer+8u),8u);if(((bits>>16u)&0xffu)==0x15u){if(data>>32u||data>2000000u){usage_value_failure_stage=14u;usage_value_failure_index=source;usage_value_failure_pointer=pointer;ok=0;break;}if(!generic_found||data>maximum_generic)maximum_generic=data;generic_found=1;}}}uint64_t generic_count=generic_found?maximum_generic+1u:0u;if(ok&&!usage_v2_selected&&(!generic_count||generic_count>2000000u||generic_count>SIZE_MAX/sizeof(*generic_records))){usage_value_failure_stage=15u;ok=0;}if(ok&&!usage_v2_selected){generic_records=calloc((SIZE_T)generic_count,sizeof(*generic_records));if(!generic_records){usage_value_failure_stage=16u;ok=0;}}for(uint64_t index=0;ok&&index<generic_count;index++){if(generic_stride<32u||index>(UINTPTR_MAX-usage_pairs.generic_record_base)/generic_stride){usage_value_failure_stage=17u;ok=0;break;}uintptr_t pointer=usage_pairs.generic_record_base+(uintptr_t)index*(uintptr_t)generic_stride;usage_value_failure_index=index;usage_value_failure_pointer=pointer;if(!region_for(pointer,32u,NULL)){usage_value_failure_stage=18u;ok=0;break;}memcpy(&generic_records[index],(const void*)pointer,32u);}if(!ok){free(records);free(generic_records);memset(inventory,0,sizeof(*inventory));return 0;}inventory->records=records;inventory->count=usage->count;inventory->generic_records=generic_records;inventory->generic_record_count=generic_count;if(!hash_decoded_usage_value_inventory(inventory)){usage_value_failure_stage=8u;free_decoded_usage_value_inventory(inventory);return 0;}usage_value_failure_index=UINT64_MAX;usage_value_failure_stage=usage_value_failure_source=usage_value_failure_type_code=0;usage_value_failure_pointer=0;return 1;
}
static void free_decoded_usage_member_inventory(decoded_usage_member_inventory*inventory){if(!inventory)return;free(inventory->records);memset(inventory,0,sizeof(*inventory));}
static int hash_decoded_usage_member_inventory(decoded_usage_member_inventory*inventory){
    BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char*object=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0&&object_size&&received==sizeof(object_size);if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok&&!object)ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;if(ok&&inventory->count&&BCryptHashData(hash,(PUCHAR)inventory->records,(ULONG)(inventory->count*sizeof(*inventory->records)),0)<0)ok=0;if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)>=0)digest_hex(digest,inventory->content_sha256);else ok=0;if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);return ok;
}
static int validate_generic_inst_index(int32_t index){
    if(index<0)return index==-1;if((uint32_t)index>2000000u||usage_members.generic_inst_shift>=63u)return 0;uint64_t stride=1ull<<usage_members.generic_inst_shift;if((uint64_t)(uint32_t)index>(UINTPTR_MAX-usage_members.generic_inst_base)/stride)return 0;uintptr_t pointer=usage_members.generic_inst_base+(uintptr_t)(uint32_t)index*(uintptr_t)stride;uint64_t count=0,arguments=0;if(pointer<expected_image_base||pointer+16u>expected_image_base+expected_image_bytes||!region_for(pointer,16u,NULL))return 0;memcpy(&count,(const void*)pointer,8u);memcpy(&arguments,(const void*)(pointer+8u),8u);if(count<1u||count>64u||!region_for(arguments,(SIZE_T)count*8u,NULL))return 0;for(uint64_t i=0;i<count;i++){uintptr_t argument=0;memcpy(&argument,(const void*)(arguments+i*8u),8u);if(argument<expected_image_base||argument+16u>expected_image_base+expected_image_bytes||!region_for(argument,16u,NULL))return 0;}return 1;
}
static int snapshot_usage_members(const decoded_usage_inventory*usage,decoded_usage_member_inventory*inventory){
    memset(inventory,0,sizeof(*inventory));usage_member_failure_index=UINT64_MAX;usage_member_failure_stage=0;usage_member_failure_pointer=0;if(!usage||!usage->records||!usage_members.field_ref_base||!usage_members.method_spec_base||!usage_members.generic_inst_base||usage_members.field_record_stride!=8u||usage_members.method_record_stride!=12u||usage->kind_counts[4]+usage->kind_counts[6]>SIZE_MAX/sizeof(usage_member_output_record)){usage_member_failure_stage=1u;return 0;}uint64_t count=usage->kind_counts[4]+usage->kind_counts[6];usage_member_output_record*records=calloc((SIZE_T)count,sizeof(*records));if(!records){usage_member_failure_stage=2u;return 0;}uint64_t output=0,type_stride=1ull<<usage_pairs.type_record_shift;int ok=1;
    for(uint64_t i=0;i<usage->count&&ok;i++){const usage_output_record*source=&usage->records[i];if(source->usage_kind!=4u&&source->usage_kind!=6u)continue;usage_member_output_record*target=&records[output++];target->first_occurrence_index=source->first_occurrence_index;target->destination_index=source->destination_index;target->usage_kind=source->usage_kind;target->source_index=source->source_index;target->slot_pointer=source->slot_pointer;target->value2=-1;usage_member_failure_index=i;
        if(source->usage_kind==4u){if(source->source_index>(UINTPTR_MAX-usage_members.field_ref_base)/8u){usage_member_failure_stage=3u;ok=0;break;}uintptr_t pointer=usage_members.field_ref_base+(uintptr_t)source->source_index*8u;usage_member_failure_pointer=pointer;if(!region_for(pointer,8u,NULL)){usage_member_failure_stage=4u;ok=0;break;}uint32_t encoded0=0,encoded1=0;memcpy(&encoded0,(const void*)pointer,4u);memcpy(&encoded1,(const void*)(pointer+4u),4u);uint32_t key=0;if((usage_members.member_codec==5u||usage_members.member_codec==6u)){key=source->source_index*usage_members.field_index_multiplier;key^=usage_members.field_index_xor;key*=usage_members.field_index_mix;key+=usage_members.field_index_bias;key^=usage_members.field_final_multiplier;target->value0=(int32_t)((encoded0^usage_members.field_value0_xor)-key);target->value1=(int32_t)((encoded1^usage_members.field_value1_xor)-key);}else if(usage_members.member_codec==4u){key=source->source_index*(uint32_t)usage_members.field_index_multiplier+(uint32_t)usage_members.field_index_bias;target->value0=(int32_t)(encoded0^key^usage_members.field_value0_xor);target->value1=(int32_t)((encoded1+usage_members.field_value1_add)^key^usage_members.field_value1_xor);}else if(usage_members.member_codec==3u){uint64_t mixed=(uint64_t)source->source_index*usage_members.field_index_multiplier;mixed>>=usage_members.field_index_shift;key=(uint32_t)mixed*usage_members.field_final_multiplier;target->value0=(int32_t)(((encoded1+usage_members.field_value1_add)^key)^usage_members.field_value1_xor);target->value1=(int32_t)(encoded0^key^usage_members.field_value0_xor);}else if(usage_members.member_codec==2u){key=source->source_index*(uint32_t)usage_members.field_index_multiplier;key^=usage_members.field_index_xor;key*=usage_members.field_index_mix;key^=usage_members.field_final_multiplier;key+=(uint32_t)usage_members.field_index_bias;target->value0=(int32_t)((encoded1^usage_members.field_value1_xor)-key);target->value1=(int32_t)((encoded0^usage_members.field_value0_xor)-key);}else{uint64_t mixed=(uint64_t)source->source_index*usage_members.field_index_multiplier+usage_members.field_index_bias;mixed^=usage_members.field_index_xor;mixed*=usage_members.field_index_mix;mixed>>=usage_members.field_index_shift;key=(uint32_t)mixed*usage_members.field_final_multiplier;target->value0=(int32_t)((encoded0^usage_members.field_value0_xor)-key);target->value1=(int32_t)((encoded1^usage_members.field_value1_xor)-key);}if(target->value0<0||target->value1<0||(uint32_t)target->value0>(expected_image_bytes-16u)/type_stride||(uint32_t)target->value1>1000000u){usage_member_failure_stage=5u;ok=0;break;}uintptr_t type_pointer=usage_pairs.type_record_base+(uintptr_t)(uint32_t)target->value0*(uintptr_t)type_stride;uint64_t bits=0;usage_member_failure_pointer=type_pointer;if(type_pointer<expected_image_base||type_pointer+16u>expected_image_base+expected_image_bytes||!region_for(type_pointer,16u,NULL)){usage_member_failure_stage=6u;ok=0;break;}memcpy(&bits,(const void*)(type_pointer+8u),8u);uint32_t code=(uint32_t)((bits>>16u)&0xffu);if(code!=0x11u&&code!=0x12u){usage_member_failure_stage=7u;ok=0;break;}inventory->field_ref_count++;
        }else{if(source->source_index>(UINTPTR_MAX-usage_members.method_spec_base)/12u){usage_member_failure_stage=8u;ok=0;break;}uintptr_t pointer=usage_members.method_spec_base+(uintptr_t)source->source_index*12u;usage_member_failure_pointer=pointer;if(!region_for(pointer,12u,NULL)){usage_member_failure_stage=9u;ok=0;break;}if((usage_members.member_codec==5u||usage_members.member_codec==6u)){int32_t m0=0,m1=0,m2=0;memcpy(&m0,(const void*)pointer,4u);memcpy(&m1,(const void*)(pointer+4u),4u);memcpy(&m2,(const void*)(pointer+8u),4u);target->value0=m0;target->value1=m1;target->value2=m2;}else if(usage_members.member_codec==2u){memcpy(&target->value2,(const void*)pointer,4u);memcpy(&target->value0,(const void*)(pointer+4u),4u);memcpy(&target->value1,(const void*)(pointer+8u),4u);}else if(usage_members.member_codec==3u){memcpy(&target->value1,(const void*)pointer,4u);memcpy(&target->value0,(const void*)(pointer+4u),4u);memcpy(&target->value2,(const void*)(pointer+8u),4u);}else if(usage_members.member_codec==4u){memcpy(&target->value2,(const void*)pointer,4u);memcpy(&target->value1,(const void*)(pointer+4u),4u);memcpy(&target->value0,(const void*)(pointer+8u),4u);}else{memcpy(&target->value0,(const void*)pointer,4u);memcpy(&target->value1,(const void*)(pointer+4u),4u);memcpy(&target->value2,(const void*)(pointer+8u),4u);}if(!validate_generic_inst_index(target->value0)||!validate_generic_inst_index(target->value1)||target->value2<0||target->value2>=2000000){usage_member_failure_stage=10u;ok=0;break;}inventory->method_spec_count++;}
    }
    if(!ok||output!=count||inventory->field_ref_count!=usage->kind_counts[4]||inventory->method_spec_count!=usage->kind_counts[6]){free(records);memset(inventory,0,sizeof(*inventory));return 0;}inventory->records=records;inventory->count=count;if(!hash_decoded_usage_member_inventory(inventory)){usage_member_failure_stage=11u;free_decoded_usage_member_inventory(inventory);return 0;}usage_member_failure_index=UINT64_MAX;usage_member_failure_stage=0;usage_member_failure_pointer=0;return 1;
}
static int validate_usage_literal_subset(const decoded_usage_inventory*inventory,uint64_t literal_count){for(uint64_t i=0;i<inventory->count;i++){const usage_output_record*record=&inventory->records[i];if(record->usage_kind!=5u)continue;if(record->source_index>=literal_count||record->destination_index!=record->source_index||record->slot_pointer!=usage_table+(uintptr_t)record->source_index*8u)return 0;}return inventory->kind_counts[5]>0u&&inventory->kind_counts[5]<=literal_count;}
static int object_class(uintptr_t object,uintptr_t*klass){if(!object||(object&7u)||!region_for(object,8u,NULL))return 0;memcpy(klass,(const void*)object,8u);return *klass!=0;}
static int derive_literal_boundary(uint64_t*count){
    if(!usage_state||!region_for(usage_state+usage_case5_field,8u,NULL))return 0;memcpy(&usage_table,(const void*)(usage_state+usage_case5_field),8u);if(!usage_table)return 0;
    uint64_t length=0,nulls=0,strings=0;for(;length<ALPHA_MAX_LITERAL_COUNT;length++){uintptr_t object=0;if(!region_for(usage_table+length*8u,8u,NULL))break;memcpy(&object,(const void*)(usage_table+length*8u),8u);if(!object){nulls++;continue;}if(string_pointer(object,NULL)){strings++;continue;}break;}
    if(length<ALPHA_MIN_LITERAL_COUNT||length>=ALPHA_MAX_LITERAL_COUNT||!region_for(usage_table+length*8u,(ALPHA_BOUNDARY_WITNESSES+1u)*8u,NULL))return 0;
    uint32_t foreign=0;uintptr_t witnesses[3]={0};for(uint32_t i=0;i<ALPHA_BOUNDARY_WITNESSES;i++){uintptr_t object=0,klass=0;memcpy(&object,(const void*)(usage_table+(length+i)*8u),8u);if(object_class(object,&klass)&&klass!=string_class){foreign++;if(i==0u)witnesses[0]=klass;if(i==1u)witnesses[1]=klass;if(i==ALPHA_BOUNDARY_WITNESSES-1u)witnesses[2]=klass;}}
    if(foreign<60u||!witnesses[0]||!witnesses[1]||!witnesses[2]||!region_for(decoder.mapping_base,(SIZE_T)(length+1u)*4u,NULL))return 0;
    boundary_prefix_nulls=nulls;boundary_prefix_strings=strings;boundary_suffix_foreign=foreign;memcpy(boundary_witness_classes,witnesses,sizeof(witnesses));*count=length;return 1;
}
static uint32_t decode_boundary_value(uint32_t index,uint32_t encrypted,uint64_t bias){
    if(decoder.boundary_codec==5u){uint32_t key=index*(uint32_t)decoder.index_multiplier+(uint32_t)bias;return encrypted^key^decoder.final_xor;}
    if(decoder.boundary_codec==4u){if(bias)index++;uint64_t mixed=(uint64_t)index*decoder.index_multiplier;mixed>>=decoder.index_shift;return encrypted+(((uint32_t)mixed)^decoder.mix_xor)+decoder.mix_add;}
    if(decoder.boundary_codec==3u){if(bias)index++;uint64_t mixed=(uint64_t)index*decoder.index_multiplier;mixed^=decoder.mix_xor;mixed*=decoder.mix_multiplier;mixed^=decoder.mix_second_xor;mixed*=decoder.mix_second_multiplier;mixed>>=decoder.index_shift;return (uint32_t)mixed^encrypted^decoder.final_xor;}
    if(decoder.boundary_codec==2u){if(bias)index++;uint32_t mixed=index*(uint32_t)decoder.index_multiplier;mixed^=decoder.mix_xor;mixed*=decoder.mix_multiplier;mixed+=decoder.mix_add;mixed^=decoder.mix_second_xor;mixed+=decoder.mix_second_add;mixed^=encrypted;mixed^=decoder.final_xor;return mixed;}
    uint64_t transformed=(uint64_t)index*decoder.index_multiplier+bias;uint32_t mixed=(uint32_t)(transformed>>decoder.index_shift);mixed*=decoder.mix_multiplier;mixed^=decoder.mix_xor;mixed+=decoder.mix_add;mixed^=encrypted;mixed^=decoder.final_xor;return mixed;
}
static int append_bytes(char**text,uint64_t*bytes,uint64_t*capacity,const char*value,uint32_t count,uint64_t*offset){*offset=*bytes;if(!count)return 1;if(*bytes+count<*bytes)return 0;uint64_t required=*bytes+count;if(required>*capacity){uint64_t next=*capacity?*capacity:65536u;while(next<required){if(next>UINT64_MAX/2u)return 0;next*=2u;}char*grown=realloc(*text,(SIZE_T)next);if(!grown)return 0;*text=grown;*capacity=next;}memcpy(*text+*bytes,value,count);*bytes=required;return 1;}
static int hash_decoded_inventory(decoded_inventory*inventory){
    BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE mapping_hash=NULL,content_hash=NULL;DWORD object_size=0,received=0;unsigned char*object1=NULL,*object2=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0&&object_size&&received==sizeof(object_size);if(ok)object1=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)object2=HeapAlloc(GetProcessHeap(),0,object_size);if(ok&&(!object1||!object2))ok=0;if(ok&&BCryptCreateHash(algorithm,&mapping_hash,object1,object_size,NULL,0,0)<0)ok=0;if(ok&&BCryptCreateHash(algorithm,&content_hash,object2,object_size,NULL,0,0)<0)ok=0;
    for(uint64_t i=0;ok&&i<inventory->count;i++){output_record*record=&inventory->records[i];uint32_t end=record->raw_start+record->text_bytes;if(BCryptHashData(mapping_hash,(PUCHAR)&record->source_index,4u,0)<0||BCryptHashData(mapping_hash,(PUCHAR)&record->raw_start,4u,0)<0||BCryptHashData(mapping_hash,(PUCHAR)&end,4u,0)<0||BCryptHashData(content_hash,(PUCHAR)&record->source_index,4u,0)<0||BCryptHashData(content_hash,(PUCHAR)&record->text_bytes,4u,0)<0||(record->text_bytes&&BCryptHashData(content_hash,(PUCHAR)(inventory->text+record->text_offset),record->text_bytes,0)<0))ok=0;}
    if(ok&&BCryptFinishHash(mapping_hash,digest,sizeof(digest),0)>=0)digest_hex(digest,inventory->mapping_sha256);else ok=0;if(ok&&BCryptFinishHash(content_hash,digest,sizeof(digest),0)>=0)digest_hex(digest,inventory->content_sha256);else ok=0;if(mapping_hash)BCryptDestroyHash(mapping_hash);if(content_hash)BCryptDestroyHash(content_hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object1)HeapFree(GetProcessHeap(),0,object1);if(object2)HeapFree(GetProcessHeap(),0,object2);return ok;
}
static void free_decoded_inventory(decoded_inventory*inventory){if(!inventory)return;free(inventory->records);free(inventory->text);memset(inventory,0,sizeof(*inventory));}
static int measure_utf8(const unsigned char*value,uint32_t bytes,uint32_t*utf16_length){
    uint32_t cursor=0,units=0;while(cursor<bytes){uint32_t amount=0;unsigned char first=value[cursor];
        if(first<=0x7fu)amount=1u;
        else if(first>=0xc2u&&first<=0xdfu){if(cursor+1u>=bytes||value[cursor+1u]<0x80u||value[cursor+1u]>0xbfu)return 0;amount=2u;}
        else if(first>=0xe0u&&first<=0xefu){if(cursor+2u>=bytes||value[cursor+2u]<0x80u||value[cursor+2u]>0xbfu)return 0;unsigned char second=value[cursor+1u];if((first==0xe0u&&(second<0xa0u||second>0xbfu))||(first==0xedu&&(second<0x80u||second>0x9fu))||(first!=0xe0u&&first!=0xedu&&(second<0x80u||second>0xbfu)))return 0;amount=3u;}
        else if(first>=0xf0u&&first<=0xf4u){if(cursor+3u>=bytes||value[cursor+2u]<0x80u||value[cursor+2u]>0xbfu||value[cursor+3u]<0x80u||value[cursor+3u]>0xbfu)return 0;unsigned char second=value[cursor+1u];if((first==0xf0u&&(second<0x90u||second>0xbfu))||(first==0xf4u&&(second<0x80u||second>0x8fu))||(first!=0xf0u&&first!=0xf4u&&(second<0x80u||second>0xbfu)))return 0;amount=4u;}
        else return 0;if(units>UINT32_MAX-(amount==4u?2u:1u))return 0;units+=amount==4u?2u:1u;cursor+=amount;
    }if(units>ALPHA_MAX_UTF16_LENGTH)return 0;*utf16_length=units;return 1;
}
static uint32_t decode_protected_literal(uint32_t index,uint32_t start,uint32_t end,unsigned char**scratch,uint64_t*scratch_capacity,uintptr_t*raw_pointer,uint32_t*utf16_length){
    uint32_t length=end-start;if(length>ALPHA_MAX_LITERAL_BYTES)return 2u;uint32_t padded=(length+7u)&~7u;if(padded<length||!add_signed_offset(decoder.data_base,(int64_t)(int32_t)start,raw_pointer)||!region_for(*raw_pointer,padded?padded:1u,NULL))return 3u;
    if(padded>*scratch_capacity){unsigned char*grown=realloc(*scratch,padded);if(!grown)return 5u;*scratch=grown;*scratch_capacity=padded;}
    uint64_t stream_key=0;if(decoder.stream_codec==3u){stream_key=(uint64_t)index*decoder.stream_index_multiplier+decoder.stream_index_bias;}else if(decoder.stream_codec==2u){stream_key=(uint64_t)index*decoder.stream_index_multiplier;stream_key^=decoder.stream_index_bias;stream_key*=decoder.stream_mix_multiplier;stream_key+=decoder.stream_mix_add;stream_key^=decoder.stream_final_xor;}else if(decoder.stream_codec==4u){stream_key=(uint64_t)index*decoder.stream_index_multiplier;stream_key^=decoder.stream_index_bias;stream_key*=decoder.stream_mix_multiplier;stream_key+=decoder.stream_mix_add;stream_key^=decoder.stream_final_xor;stream_key*=decoder.stream_final_multiplier;}else{stream_key=((uint64_t)index*decoder.stream_index_multiplier+decoder.stream_index_bias)^decoder.stream_index_xor;stream_key*=decoder.stream_final_multiplier;}
    for(uint32_t offset=0;offset<padded;offset+=8u){uint64_t word=0;memcpy(&word,(const void*)(*raw_pointer+offset),8u);word^=stream_key;memcpy(*scratch+offset,&word,8u);stream_key+=decoder.stream_step;}
    return measure_utf8(*scratch,length,utf16_length)?0u:4u;
}

/*
 * Current-build literal path.
 *
 * The client keeps one lazily filled table per usage kind, indexed by the
 * destination slot that the usage pair decode produces.  The literals are the
 * managed string objects stored in the kind-5 table, so the decoder only has
 * to (a) let the runtime populate the tables through its own initializer for
 * every usage index that still has an empty slot, and (b) read the managed
 * string layout straight from those live objects.
 */
static volatile LONG usage_materialized_index_count;
static volatile LONG usage_materialized_call_count;
static uint32_t usage_v2_string_length_offset, usage_v2_string_data_offset;
static uint32_t usage_v2_literal_slot_count;
static uintptr_t usage_v2_literal_table;

static void usage_call_initializer(uintptr_t initializer,uintptr_t descriptor,uintptr_t metadata_base,uint32_t index){
    volatile uintptr_t fn=initializer,d=descriptor,m=metadata_base;
    volatile uint32_t ix=index;
    /* The runtime initializer is SSE heavy, so the call site must keep the
     * stack 16 byte aligned; every register the initializer may clobber is
     * saved explicitly because it is invoked outside the compiler's ABI. */
    __asm__ volatile(
        "pushq %%rbx\n\t"
        "pushq %%r12\n\tpushq %%r13\n\tpushq %%r14\n\tpushq %%r15\n\t"
        "movq %%rsp, %%rax\n\tandq $$-16, %%rsp\n\tpushq %%rax\n\t"
        "movq %0, %%r8\n\t"
        "movq %1, %%r12\n\t"
        "movl %2, %%ecx\n\t"
        "call *%3\n\t"
        "popq %%rax\n\tmovq %%rax, %%rsp\n\t"
        "popq %%r15\n\tpopq %%r14\n\tpopq %%r13\n\tpopq %%r12\n\t"
        "popq %%rbx\n\t"
        :
        : "m"(d), "m"(m), "m"(ix), "m"(fn)
        : "rax","rcx","rdx","rsi","rdi","r8","r9","r10","r11","memory","cc"
    );
}
static int usage_slot_index(uint32_t kind,uint32_t destination,uint32_t*slot){
    uint32_t candidate=destination;
    if(kind==0u||kind==7u)candidate&=0xffffffu;
    if(kind>=8u||!usage_case_tables[kind]||candidate>(expected_image_bytes/8u))return 0;
    *slot=candidate;return 1;
}
static int populate_usage_tables_v2(void){
    if(!usage_v2_selected||!usage_initializer||!usage_pairs.pair_base)return 0;
    uint64_t range_count=usage_max_index+2u;
    if(range_count<3u||range_count>2000000u)return 0;
    uint32_t*range_values=(uint32_t*)calloc((SIZE_T)range_count,sizeof(uint32_t));
    if(!range_values)return 0;
    uint32_t previous=0;
    for(uint64_t i=0;i<range_count;i++){
        if(!region_for(usage_pairs.range_base+i*4u,4u,NULL)){free(range_values);return 0;}
        uint32_t raw=0;memcpy(&raw,(const void*)(usage_pairs.range_base+i*4u),4u);
        uint32_t value=decode_usage_range_value((uint32_t)i,raw);
        if(i&&value<previous){free(range_values);return 0;}
        range_values[i]=value;previous=value;
    }
    uint64_t calls=0;
    for(uint64_t index=0;index+1u<range_count;index++){
        uint64_t start=range_values[index],end=range_values[index+1];
        if(end<=start)continue;
        if(end>usage_max_index+2u)end=usage_max_index+2u;
        int missing=0;
        for(uint64_t occurrence=start;occurrence<end&&!missing;occurrence++){
            if(!region_for(usage_pairs.pair_base+occurrence*8u,8u,NULL)){missing=1;break;}
            uint32_t raw_destination=0,raw_encoded=0;
            memcpy(&raw_destination,(const void*)(usage_pairs.pair_base+occurrence*8u),4u);
            memcpy(&raw_encoded,(const void*)(usage_pairs.pair_base+occurrence*8u+4u),4u);
            uint32_t mixed=decode_usage_pair_key((uint32_t)occurrence);
            uint32_t encoded=(raw_destination+usage_v2_pair_add)^mixed;
            uint32_t destination=(raw_encoded+usage_v2_pair_value_add)^mixed;
            uint32_t kind=encoded>>29u,slot=0;
            if(!usage_slot_index(kind,destination,&slot)){missing=1;break;}
            uint64_t value=0;
            if(!region_for(usage_case_tables[kind]+(uintptr_t)slot*8u,8u,NULL)){missing=1;break;}
            memcpy(&value,(const void*)(usage_case_tables[kind]+(uintptr_t)slot*8u),8u);
            if(!value)missing=1;
        }
        if(!missing)continue;
        if(!usage_v2_materialize)continue;
        if(usage_v2_materialize_limit&&calls>=usage_v2_materialize_limit)continue;
        usage_call_initializer(usage_initializer,usage_v2_descriptor,usage_v2_metadata_base,(uint32_t)index);
        calls++;
    }
    free(range_values);
    InterlockedExchange(&usage_materialized_index_count,(LONG)(usage_max_index+1u));
    InterlockedExchange(&usage_materialized_call_count,(LONG)calls);
    return 1;
}
static int decode_literals_any(HMODULE image,uint64_t*count,decoded_inventory*inventory){
    if(decoder.literal_codec==1u){
        static decoded_usage_inventory literal_usage;
        if(!literal_usage.records){
            if(!decode_usage_inventory(image,&literal_usage)){decode_failure_stage=20u;return 0;}
        }
        if(usage_v2_materialize){
            if(!populate_usage_tables_v2()){decode_failure_stage=25u;return 0;}
            free_decoded_usage_inventory(&literal_usage);
            if(!decode_usage_inventory(image,&literal_usage)){decode_failure_stage=26u;return 0;}
        }
        if(decode_literal_inventory_metadata_v2(&literal_usage,inventory)){
            *count=inventory->count;
            write_literal_decode_probe();
            return 1;
        }
        write_literal_decode_probe();
        if(!observe_string_layout_v2(&literal_usage)){decode_failure_stage=21u;return 0;}
        if(!decode_literal_inventory_v2(&literal_usage,inventory))return 0;
        *count=inventory->count;
        return 1;
    }
    if(!derive_literal_boundary(count))return 0;
    return decode_literal_inventory(*count,inventory);
}
static int observe_string_layout_v2(const decoded_usage_inventory*usage){
    uintptr_t table=usage_case_tables[5];
    if(!table||!usage||!usage->records)return 0;
    const uint32_t candidates[4][2]={{0x10u,0x14u},{0x8u,0xcu},{0x10u,0x18u},{0xcu,0x10u}};
    uint32_t best_valid=0,best_length=0,best_data=0,slot_count=0;
    for(uint64_t index=0;index<usage->count&&slot_count<4096u;index++){
        const usage_output_record*source=&usage->records[index];
        if(source->usage_kind!=5u)continue;
        uintptr_t entry=(uintptr_t)source->slot_pointer;
        if(!region_for(entry,8u,NULL))continue;
        uint64_t pointer=0;memcpy(&pointer,(const void*)entry,8u);
        if(!pointer)continue;
        slot_count++;
    }
    if(slot_count<64u)return 0;
    for(uint32_t candidate=0;candidate<4u;candidate++){
        uint32_t length_offset=candidates[candidate][0],data_offset=candidates[candidate][1];
        uint32_t valid=0;
        for(uint64_t index=0;index<usage->count&&valid<64u;index++){
            const usage_output_record*source=&usage->records[index];
            if(source->usage_kind!=5u)continue;
            uintptr_t entry=(uintptr_t)source->slot_pointer;
            if(!region_for(entry,8u,NULL))continue;
            uint64_t pointer=0;memcpy(&pointer,(const void*)entry,8u);
            if(!pointer||!region_for(pointer,(SIZE_T)data_offset+8u,NULL))continue;
            uint32_t length=0;memcpy(&length,(const void*)(pointer+length_offset),4u);
            if(!length||length>0x100000u)continue;
            if(!region_for(pointer+data_offset,(SIZE_T)length*2u,NULL))continue;
            const wchar_t*text=(const wchar_t*)(pointer+data_offset);
            uint32_t index=0;
            for(;index<length;index++)if(!text[index]||text[index]<0x20u)break;
            if(index!=length)continue;
            valid++;
        }
        if(valid>best_valid){best_valid=valid;best_length=length_offset;best_data=data_offset;}
    }
    if(best_valid<32u)return 0;
    usage_v2_string_length_offset=best_length;
    usage_v2_string_data_offset=best_data;
    usage_v2_literal_table=table;
    usage_v2_literal_slot_count=slot_count;
    return 1;
}
/*
 * Metadata direct literal decode (read only).
 *
 * The runtime's own case-5 handler reads a dword pair at
 * ``table + index*4`` (the value dword and the adjacent length dword), derives
 * the byte pointer and the byte length from them, and XORs the length bytes
 * with the index keyed stream.  This routine evaluates exactly those
 * expressions, so the whole literal domain is enumerated without calling into
 * the target and without touching any cache.  A slot classifies as a string,
 * as a null (zero length) entry, or as a foreign entry; the domain is the
 * prefix of strings/nulls that ends where a witness window of 64 entries is
 * overwhelmingly foreign.
 */
static uint32_t literal_slot_class(uintptr_t table,uintptr_t data_base,uint32_t index,unsigned char*text,uint32_t capacity,uint32_t*value_out,uint32_t*length_out,uintptr_t*pointer_out){
    uint32_t mixed=index*usage_v2_literal_index_multiplier;
    uintptr_t entry=table+(uintptr_t)index*4u;
    if(value_out)*value_out=0u;
    if(length_out)*length_out=0u;
    if(pointer_out)*pointer_out=0u;
    if(!region_for(entry,8u,NULL))return 2u;
    uint32_t value_dword=0,length_dword=0;
    memcpy(&value_dword,(const void*)entry,4u);
    memcpy(&length_dword,(const void*)(entry+4u),4u);
    uint32_t value=(value_dword+usage_v2_literal_value_add)^(mixed+usage_v2_literal_index_add);
    uint32_t length=((length_dword+usage_v2_literal_value_add)^(mixed+usage_v2_literal_second_index_add))-value;
    uintptr_t pointer=data_base+(intptr_t)(int32_t)value;
    if(value_out)*value_out=value;
    if(length_out)*length_out=length;
    if(pointer_out)*pointer_out=pointer;
    if(!length)return 1u;
    if(length>capacity)return 3u;
    if(!region_for(pointer,(SIZE_T)length,NULL))return 2u;
    memcpy(text,(const void*)pointer,(SIZE_T)length);
    uint64_t key=((usage_v2_literal_key_add+((uint64_t)index*usage_v2_literal_key_multiplier))
        ^usage_v2_literal_key_xor)+usage_v2_literal_key_bias;
    for(uint32_t offset=0;offset<length;offset++){
        uint64_t unit=key+((uint64_t)(offset/8u)*usage_v2_literal_stream_step);
        text[offset]=(unsigned char)(text[offset]^((unit>>(8u*(offset%8u)))&0xffu));
    }
    if(MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,(const char*)text,(int)length,NULL,0)<=0)return 3u;
    return 0u;
}
static int decode_literal_inventory_metadata_v2(const decoded_usage_inventory*usage,decoded_inventory*inventory){
    literal_decode_probe_stage=0u;literal_decode_sample_count=0u;
    memset(literal_decode_totals,0,sizeof(literal_decode_totals));
    literal_decode_domain=0u;
    if(!usage_v2_literal_base_field||!usage_v2_literal_descriptor_field){literal_decode_probe_stage=1u;return 0;}
    if(!usage||!usage->records||!usage->kind_counts[5]){literal_decode_probe_stage=2u;return 0;}
    uintptr_t metadata_base=usage_v2_live_metadata_base?usage_v2_live_metadata_base:usage_v2_metadata_base;
    uintptr_t descriptor=usage_v2_live_descriptor?usage_v2_live_descriptor:usage_v2_descriptor;
    if(!metadata_base||!descriptor||!region_for(descriptor,0x400u,NULL)){literal_decode_probe_stage=3u;return 0;}
    uint32_t base_raw=0,descriptor_raw=0;
    memcpy(&base_raw,(const void*)(descriptor+usage_v2_literal_base_field),4u);
    memcpy(&descriptor_raw,(const void*)(descriptor+usage_v2_literal_descriptor_field),4u);
    uintptr_t table=metadata_base+(intptr_t)(int32_t)(base_raw^usage_v2_literal_base_xor);
    uintptr_t data_base=metadata_base+(intptr_t)(int32_t)(descriptor_raw+usage_v2_literal_descriptor_bias);
    if(!region_for(table,8u,NULL)){literal_decode_probe_stage=4u;return 0;}
    if(!region_for(data_base,1u,NULL)){literal_decode_probe_stage=5u;return 0;}
    decoder.mapping_base=table;
    decoder.data_base=data_base;
    decoder.descriptor_global=usage_v2_descriptor_global;
    decoder.metadata_base_global=usage_v2_metadata_base_global;
    uint64_t domain=0;
    if(!derive_literal_boundary(&domain)){literal_decode_probe_stage=6u;return 0;}
    literal_decode_domain=domain;
    if(domain<ALPHA_MIN_LITERAL_COUNT||domain>ALPHA_MAX_LITERAL_COUNT){literal_decode_probe_stage=7u;return 0;}
    literal_decode_totals[0]=usage->count;
    uint32_t referenced=0;
    for(uint64_t index=0;index<usage->count;index++){
        const usage_output_record*source=&usage->records[index];
        if(source->usage_kind!=5u)continue;
        literal_decode_totals[1]++;
        if((uint32_t)source->source_index==(uint32_t)source->destination_index)literal_decode_totals[7]++;
        if((uint32_t)source->source_index>referenced)referenced=(uint32_t)source->source_index;
    }
    literal_decode_referenced=referenced;
    if(domain<(uint64_t)referenced+1u){
        literal_decode_referenced_beyond=0u;
        for(uint64_t index=0;index<usage->count;index++){
            const usage_output_record*source=&usage->records[index];
            if(source->usage_kind!=5u)continue;
            if((uint32_t)source->source_index>=domain){
                if(literal_decode_referenced_beyond<8u)record_literal_decode_sample(40u,(uint32_t)source->source_index,(uint32_t)source->destination_index,0u,0u,0u,0u,NULL,0u,NULL,0u);
                literal_decode_referenced_beyond++;
            }
        }
        literal_decode_probe_stage=8u;
        return 0;
    }
    uint64_t capacity=domain;
    if(!capacity||capacity>SIZE_MAX/sizeof(*inventory->records)){literal_decode_probe_stage=9u;return 0;}
    inventory->records=calloc((SIZE_T)capacity,sizeof(*inventory->records));
    if(!inventory->records){decode_failure_stage=1u;literal_decode_probe_stage=10u;return 0;}
    unsigned char text[4096];
    uint64_t text_capacity=0,count=0,prefix_nulls=0,prefix_strings=0;
    literal_structural_tail_count=0u;
    for(uint64_t index=0;index<domain;index++){
        uint32_t value=0,length=0;uintptr_t pointer=0;
        uint32_t class=literal_slot_class(table,data_base,(uint32_t)index,text,(uint32_t)sizeof(text),&value,&length,&pointer);
        if(class==1u){
            prefix_nulls++;
            inventory->records[count]=(output_record){(uint32_t)index,0u,pointer?pointer:data_base,inventory->text_bytes,0u,value};
            count++;
            continue;
        }
        if(class!=0u){
            record_literal_decode_sample(30u+class,(uint32_t)index,(uint32_t)index,value,value,pointer,length,NULL,0u,NULL,0u);
            uint64_t tail=domain-index;
            int tail_ok=tail>=1u&&tail<=ALPHA_BOUNDARY_WITNESSES;
            for(uint64_t follow=index;tail_ok&&follow<domain;follow++){
                uint32_t follow_value=0,follow_length=0;uintptr_t follow_pointer=0;
                uint32_t follow_class=literal_slot_class(table,data_base,(uint32_t)follow,text,(uint32_t)sizeof(text),&follow_value,&follow_length,&follow_pointer);
                if(follow_class<2u)tail_ok=0;
            }
            if(tail_ok){
                literal_structural_tail_count=tail;
                literal_decode_domain=index;
                break;
            }
            literal_decode_probe_stage=11u;
            free(inventory->records);memset(inventory,0,sizeof(*inventory));
            return 0;
        }
        prefix_strings++;
        int utf16=MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,(const char*)text,(int)length,NULL,0);
        uint64_t text_offset=0;
        if(utf16<=0||!append_bytes(&inventory->text,&inventory->text_bytes,&text_capacity,(const char*)text,length,&text_offset)){
            decode_failure_stage=8u;literal_decode_probe_stage=12u;
            free(inventory->records);memset(inventory,0,sizeof(*inventory));
            return 0;
        }
        inventory->records[count]=(output_record){(uint32_t)index,(uint32_t)utf16,pointer,text_offset,length,value};
        if(count<4u)record_literal_decode_sample(1u,(uint32_t)index,(uint32_t)index,value,value,pointer,length,text,length,text,length<8u?length:8u);
        count++;
    }
    literal_decode_totals[4]=prefix_nulls;
    literal_decode_totals[5]=prefix_strings;
    if(count<(uint64_t)ALPHA_MIN_LITERAL_COUNT||count<(uint64_t)referenced+1u){
        literal_decode_probe_stage=13u;
        free(inventory->records);memset(inventory,0,sizeof(*inventory));
        return 0;
    }
    usage_v2_literal_slot_count=(uint32_t)(count<0xffffffffu?count:0xffffffffu);
    inventory->count=count;
    if(!hash_decoded_inventory(inventory)){decode_failure_stage=24u;literal_decode_probe_stage=14u;return 0;}
    literal_decode_probe_stage=15u;
    return 1;
}
static int decode_literal_inventory_v2(const decoded_usage_inventory*usage,decoded_inventory*inventory){
    uintptr_t table=usage_case_tables[5];
    if(!table||!usage_v2_string_length_offset||!usage||!usage->records)return 0;
    uint64_t literal_capacity=usage->kind_counts[5]?usage->kind_counts[5]:usage->count;
    if(!literal_capacity||literal_capacity>SIZE_MAX/sizeof(*inventory->records))return 0;
    inventory->records=calloc((SIZE_T)literal_capacity,sizeof(*inventory->records));
    if(!inventory->records){decode_failure_stage=1u;return 0;}
    uint64_t capacity=0,count=0;uint32_t previous_end=0;
    for(uint64_t record_index=0;record_index<usage->count;record_index++){
        const usage_output_record*source=&usage->records[record_index];
        if(source->usage_kind!=5u)continue;
        uintptr_t entry=(uintptr_t)source->slot_pointer;
        if(!region_for(entry,8u,NULL))continue;
        uint64_t pointer=0;memcpy(&pointer,(const void*)entry,8u);
        if(!pointer)continue;
        uint32_t length=0;
        if(!region_for(pointer,(SIZE_T)usage_v2_string_length_offset+4u,NULL)){decode_failure_stage=2u;break;}
        memcpy(&length,(const void*)(pointer+usage_v2_string_length_offset),4u);
        if(!length||length>0x100000u){decode_failure_stage=3u;break;}
        if(!region_for(pointer+usage_v2_string_data_offset,(SIZE_T)length*2u,NULL)){decode_failure_stage=4u;break;}
        const wchar_t*text=(const wchar_t*)(pointer+usage_v2_string_data_offset);
        int required=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,text,(int)length,NULL,0,NULL,NULL);
        if(required<=0||required>(int)(4u*length)){decode_failure_stage=5u;break;}
        char*encoded=(char*)malloc((SIZE_T)required);
        if(!encoded){decode_failure_stage=6u;break;}
        if(WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,text,(int)length,encoded,required,NULL,NULL)!=required){free(encoded);decode_failure_stage=7u;break;}
        uint64_t text_offset=0;
        if(!append_bytes(&inventory->text,&inventory->text_bytes,&capacity,encoded,(uint32_t)required,&text_offset)){free(encoded);decode_failure_stage=8u;break;}
        free(encoded);
        inventory->records[count]=(output_record){source->destination_index,length,pointer,text_offset,(uint32_t)required,(uint32_t)(pointer-expected_image_base)};
        previous_end=(uint32_t)(pointer-expected_image_base);
        (void)previous_end;
        count++;
    }
    if(decode_failure_stage){free(inventory->records);memset(inventory,0,sizeof(*inventory));return 0;}
    usage_v2_literal_slot_count=(uint32_t)(count<0xffffffffu?count:0xffffffffu);
    if(count<1024u){decode_failure_stage=23u;decode_failure_index=count;free(inventory->records);memset(inventory,0,sizeof(*inventory));return 0;}
    inventory->count=count;inventory->mapping_sha256[0]=0;
    if(!hash_decoded_inventory(inventory)){decode_failure_stage=24u;return 0;}
    return 1;
}
static int decode_literal_inventory(uint64_t count,decoded_inventory*inventory){
    memset(inventory,0,sizeof(*inventory));decode_failure_index=UINT64_MAX;decode_failure_stage=0;decode_failure_start=decode_failure_end=decode_failure_length=0;decode_failure_pointer=0;decode_failure_sample_owner_only=0;
    inventory->records=calloc((SIZE_T)count,sizeof(*inventory->records));if(!inventory->records){decode_failure_stage=1u;return 0;}inventory->count=count;literal_structural_tail_count=0;uint64_t capacity=0,scratch_capacity=0;unsigned char*scratch=NULL;uint32_t previous_end=0;int ok=1;
    for(uint64_t i=0;ok&&i<count;i++){
        uint32_t encrypted_start=0,encrypted_end=0;memcpy(&encrypted_start,(const void*)(decoder.mapping_base+i*4u),4u);memcpy(&encrypted_end,(const void*)(decoder.mapping_base+(i+1u)*4u),4u);
        uint32_t start=decode_boundary_value((uint32_t)i,encrypted_start,decoder.start_bias);uint32_t end=decode_boundary_value((uint32_t)i,encrypted_end,decoder.end_bias);uint32_t length=end-start;decode_failure_index=i;decode_failure_start=start;decode_failure_end=end;decode_failure_length=length;uintptr_t raw_pointer=0;uint32_t utf16_length=0;
        uint32_t stage=(start!=(i?previous_end:0u))?2u:decode_protected_literal((uint32_t)i,start,end,&scratch,&scratch_capacity,&raw_pointer,&utf16_length);decode_failure_pointer=raw_pointer;if(raw_pointer&&region_for(raw_pointer,8u,NULL))memcpy(&decode_failure_sample_owner_only,(const void*)raw_pointer,8u);
        if(stage){uint64_t tail=count-i;int tail_valid=0,tail_resource_failure=0;int tail_contract=i>=ALPHA_MIN_LITERAL_COUNT&&tail<=ALPHA_BOUNDARY_WITNESSES&&stage>=2u&&stage<=4u;if(tail_contract){for(uint64_t j=i+1u;j<count;j++){uint32_t raw_start=0,raw_end=0;memcpy(&raw_start,(const void*)(decoder.mapping_base+j*4u),4u);memcpy(&raw_end,(const void*)(decoder.mapping_base+(j+1u)*4u),4u);uint32_t tail_start=decode_boundary_value((uint32_t)j,raw_start,decoder.start_bias),tail_end=decode_boundary_value((uint32_t)j,raw_end,decoder.end_bias),tail_utf16=0;uintptr_t tail_pointer=0;uint32_t tail_stage=decode_protected_literal((uint32_t)j,tail_start,tail_end,&scratch,&scratch_capacity,&tail_pointer,&tail_utf16);if(!tail_stage)tail_valid=1;if(tail_stage==5u)tail_resource_failure=1;}}if(!tail_contract||tail_valid||tail_resource_failure){decode_failure_stage=stage;ok=0;break;}inventory->count=i;literal_structural_tail_count=tail;break;}
        uint64_t text_offset=0;if(!append_bytes(&inventory->text,&inventory->text_bytes,&capacity,(const char*)scratch,length,&text_offset)){decode_failure_stage=5u;ok=0;break;}inventory->records[i]=(output_record){(uint32_t)i,utf16_length,raw_pointer,text_offset,length,start};previous_end=end;
    }
    free(scratch);if(ok&&!hash_decoded_inventory(inventory)){decode_failure_stage=6u;ok=0;}if(ok){decode_failure_index=UINT64_MAX;decode_failure_stage=0;decode_failure_start=decode_failure_end=decode_failure_length=0;decode_failure_pointer=0;decode_failure_sample_owner_only=0;}if(!ok)free_decoded_inventory(inventory);return ok;
}
static int write_output(const decoded_inventory*inventory){
    FILE*output=_wfopen(output_path,L"wb");if(!output)return 0;int ok=1;output_header header={0};memcpy(header.magic,"ALPHASL2",8);header.version=2u;header.header_bytes=sizeof(header);header.record_bytes=sizeof(output_record);header.literal_count=inventory->count;header.mapping_base=decoder.mapping_base;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;header.string_bytes=inventory->text_bytes;header.readable_region_count=region_count;header.boundary_witness_count=ALPHA_BOUNDARY_WITNESSES;memcpy(header.executable_sha256,executable_sha256,64);memcpy(header.identity_sha256,identity_sha256,64);memcpy(header.mapping_sha256,inventory->mapping_sha256,64);memcpy(header.content_sha256,inventory->content_sha256,64);
    if(fwrite(&header,1,sizeof(header),output)!=sizeof(header))ok=0;if(ok&&fwrite(inventory->records,sizeof(*inventory->records),(SIZE_T)inventory->count,output)!=(SIZE_T)inventory->count)ok=0;if(ok&&inventory->text_bytes&&fwrite(inventory->text,1,(SIZE_T)inventory->text_bytes,output)!=(SIZE_T)inventory->text_bytes)ok=0;if(fclose(output))ok=0;if(ok)_wchmod(output_path,0600);else _wremove(output_path);return ok;
}
static int write_usage_output(const decoded_usage_inventory*inventory){
    FILE*output=_wfopen(usage_output_path,L"wb");if(!output)return 0;int ok=1;usage_output_header header={0};memcpy(header.magic,"ALPHAUP1",8);header.version=1u;header.header_bytes=sizeof(header);header.record_bytes=sizeof(usage_output_record);header.usage_count=inventory->count;header.occurrence_count=inventory->occurrence_count;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;memcpy(header.kind_counts,inventory->kind_counts,sizeof(header.kind_counts));memcpy(header.executable_sha256,executable_sha256,64);memcpy(header.identity_sha256,identity_sha256,64);memcpy(header.content_sha256,inventory->content_sha256,64);
    if(fwrite(&header,1,sizeof(header),output)!=sizeof(header))ok=0;if(ok&&fwrite(inventory->records,sizeof(*inventory->records),(SIZE_T)inventory->count,output)!=(SIZE_T)inventory->count)ok=0;if(fclose(output))ok=0;if(ok)_wchmod(usage_output_path,0600);else _wremove(usage_output_path);return ok;
}
static int write_usage_value_output(const decoded_usage_value_inventory*inventory){
    FILE*output=_wfopen(usage_value_output_path,L"wb");if(!output)return 0;int ok=1;usage_value_output_header header={0};memcpy(header.magic,"ALPHAUV1",8);header.version=1u;header.header_bytes=sizeof(header);header.record_bytes=sizeof(usage_value_output_record);header.usage_count=inventory->count;header.nonzero_value_count=inventory->nonzero_value_count;header.kind1_count=inventory->kind1_count;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;header.type_record_base=usage_pairs.type_record_base;header.type_record_stride=1ull<<usage_pairs.type_record_shift;header.generic_record_base=usage_pairs.generic_record_base;header.generic_record_stride=1ull<<usage_pairs.generic_record_shift;header.generic_record_count=inventory->generic_record_count;memcpy(header.executable_sha256,executable_sha256,64);memcpy(header.identity_sha256,identity_sha256,64);memcpy(header.content_sha256,inventory->content_sha256,64);
    if(fwrite(&header,1,sizeof(header),output)!=sizeof(header))ok=0;if(ok&&fwrite(inventory->records,sizeof(*inventory->records),(SIZE_T)inventory->count,output)!=(SIZE_T)inventory->count)ok=0;if(ok&&fwrite(inventory->generic_records,sizeof(*inventory->generic_records),(SIZE_T)inventory->generic_record_count,output)!=(SIZE_T)inventory->generic_record_count)ok=0;if(fclose(output))ok=0;if(ok)_wchmod(usage_value_output_path,0600);else _wremove(usage_value_output_path);return ok;
}
static int write_usage_member_output(const decoded_usage_member_inventory*inventory,const decoded_usage_inventory*usage){
    FILE*output=_wfopen(usage_member_output_path,L"wb");if(!output)return 0;int ok=1;usage_member_output_header header={0};memcpy(header.magic,"ALPHAUM1",8);header.version=1u;header.header_bytes=sizeof(header);header.record_bytes=sizeof(usage_member_output_record);header.usage_count=usage->count;header.field_ref_count=inventory->field_ref_count;header.method_spec_count=inventory->method_spec_count;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;header.type_record_base=usage_pairs.type_record_base;header.type_record_stride=1ull<<usage_pairs.type_record_shift;header.generic_inst_base=usage_members.generic_inst_base;header.generic_inst_stride=1ull<<usage_members.generic_inst_shift;memcpy(header.executable_sha256,executable_sha256,64);memcpy(header.identity_sha256,identity_sha256,64);memcpy(header.usage_sha256,usage->content_sha256,64);memcpy(header.content_sha256,inventory->content_sha256,64);if(fwrite(&header,1,sizeof(header),output)!=sizeof(header))ok=0;if(ok&&fwrite(inventory->records,sizeof(*inventory->records),(SIZE_T)inventory->count,output)!=(SIZE_T)inventory->count)ok=0;if(fclose(output))ok=0;if(ok)_wchmod(usage_member_output_path,0600);else _wremove(usage_member_output_path);return ok;
}
static void write_usage_value_status(const char*status,int complete,const decoded_usage_value_inventory*first,const decoded_usage_value_inventory*second){
    FILE*output=_wfopen(usage_value_status_path,L"wb");if(!output)return;fprintf(output,"{\n  \"schema\": \"alpha.runtime-metadata-usage-value-status/v1\",\n  \"status\": \"%s\",\n  \"complete\": %s,\n  \"usage_count\": %llu,\n  \"nonzero_value_count\": %llu,\n  \"kind1_count\": %llu,\n  \"type_record_base_owner_only\": %llu,\n  \"type_helper_owner_only\": %llu,\n  \"type_state_global_owner_only\": %llu,\n  \"type_state_field_owner_only\": %u,\n  \"type_record_stride\": %llu,\n  \"generic_state_global_owner_only\": %llu,\n  \"generic_state_field_owner_only\": %u,\n  \"generic_record_base_owner_only\": %llu,\n  \"generic_record_stride\": %llu,\n  \"failure_index_owner_only\": %llu,\n  \"failure_stage\": %u,\n  \"failure_source_owner_only\": %u,\n  \"failure_pointer_owner_only\": %llu,\n  \"failure_type_code_owner_only\": %u,\n  \"first_content_sha256\": \"%s\",\n  \"second_content_sha256\": \"%s\",\n  \"two_observations_match\": %s,\n  \"type_record_helper_runtime_derived\": %s,\n  \"read_only_snapshot\": true,\n  \"usage_materialization_performed\": false,\n  \"fresh_runtime_observation\": true,\n  \"saved_metadata_usage_value_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,complete?"true":"false",(unsigned long long)(first?first->count:0u),(unsigned long long)(first?first->nonzero_value_count:0u),(unsigned long long)(first?first->kind1_count:0u),(unsigned long long)usage_pairs.type_record_base,(unsigned long long)usage_pairs.type_helper,(unsigned long long)usage_pairs.type_state_global,usage_pairs.type_state_field,(unsigned long long)(1ull<<usage_pairs.type_record_shift),(unsigned long long)usage_pairs.generic_state_global,usage_pairs.generic_state_field,(unsigned long long)usage_pairs.generic_record_base,(unsigned long long)(1ull<<usage_pairs.generic_record_shift),(unsigned long long)usage_value_failure_index,usage_value_failure_stage,usage_value_failure_source,(unsigned long long)usage_value_failure_pointer,usage_value_failure_type_code,first?first->content_sha256:"",second?second->content_sha256:"",complete?"true":"false",usage_pairs.type_helper&&usage_pairs.type_state_global&&usage_pairs.type_record_base&&usage_pairs.generic_state_global&&usage_pairs.generic_record_base?"true":"false");fclose(output);_wchmod(usage_value_status_path,0600);
}
static void write_usage_member_status(const char*status,int complete,const decoded_usage_member_inventory*first,const decoded_usage_member_inventory*second){
    FILE*output=_wfopen(usage_member_status_path,L"wb");if(!output)return;fprintf(output,"{\n  \"schema\": \"alpha.runtime-metadata-usage-member-status/v1\",\n  \"status\": \"%s\",\n  \"complete\": %s,\n  \"member_usage_count\": %llu,\n  \"field_ref_count\": %llu,\n  \"method_spec_count\": %llu,\n  \"field_ref_base_owner_only\": %llu,\n  \"field_ref_record_stride\": %u,\n  \"method_spec_base_owner_only\": %llu,\n  \"method_spec_record_stride\": %u,\n  \"generic_inst_state_global_owner_only\": %llu,\n  \"generic_inst_state_field_owner_only\": %u,\n  \"generic_inst_base_owner_only\": %llu,\n  \"generic_inst_stride\": %llu,\n  \"failure_index_owner_only\": %llu,\n  \"failure_stage\": %u,\n  \"failure_pointer_owner_only\": %llu,\n  \"first_content_sha256\": \"%s\",\n  \"second_content_sha256\": \"%s\",\n  \"two_observations_match\": %s,\n  \"member_contract_runtime_derived\": %s,\n  \"read_only_snapshot\": true,\n  \"usage_materialization_performed\": false,\n  \"fresh_runtime_observation\": true,\n  \"saved_metadata_usage_member_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,complete?"true":"false",(unsigned long long)(first?first->count:0u),(unsigned long long)(first?first->field_ref_count:0u),(unsigned long long)(first?first->method_spec_count:0u),(unsigned long long)usage_members.field_ref_base,usage_members.field_record_stride,(unsigned long long)usage_members.method_spec_base,usage_members.method_record_stride,(unsigned long long)usage_members.generic_inst_state_global,usage_members.generic_inst_state_field,(unsigned long long)usage_members.generic_inst_base,(unsigned long long)(1ull<<usage_members.generic_inst_shift),(unsigned long long)usage_member_failure_index,usage_member_failure_stage,(unsigned long long)usage_member_failure_pointer,first?first->content_sha256:"",second?second->content_sha256:"",complete?"true":"false",usage_members.field_ref_base&&usage_members.method_spec_base&&usage_members.generic_inst_base?"true":"false");fclose(output);_wchmod(usage_member_status_path,0600);
}
static void write_usage_status(const char*status,int complete,const decoded_usage_inventory*first,const decoded_usage_inventory*second){
    FILE*output=_wfopen(usage_status_path,L"wb");if(!output)return;uint64_t empty[8]={0};const uint64_t*counts=first?first->kind_counts:empty;fprintf(output,"{\n  \"schema\": \"alpha.runtime-metadata-usage-pair-status/v1\",\n  \"status\": \"%s\",\n  \"complete\": %s,\n  \"usage_count\": %llu,\n  \"occurrence_count\": %llu,\n  \"range_count\": %llu,\n  \"range_domain_complete\": %s,\n  \"kind_counts\": [%llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu],\n  \"range_base_owner_only\": %llu,\n  \"pair_base_owner_only\": %llu,\n  \"case_fields_owner_only\": [%u, %u, %u, %u, %u, %u, %u, %u],\n  \"case_tables_owner_only\": [%llu, %llu, %llu, %llu, %llu, %llu, %llu, %llu],\n  \"decode_failure_index_owner_only\": %llu,\n  \"decode_failure_stage\": %u,\n  \"decode_failure_raw_owner_only\": [%u, %u],\n  \"decode_failure_values_owner_only\": [%u, %u],\n  \"range_codec_owner_only\": [%u, %u, %u, %u, %llu, %u, %u, %u],\n  \"direct_call_form_unmatched_nonempty_range_count\": %llu,\n  \"first_content_sha256\": \"%s\",\n  \"second_content_sha256\": \"%s\",\n  \"two_observations_match\": %s,\n  \"initializer_contract_runtime_derived\": %s,\n  \"read_only_decoder\": true,\n  \"usage_materialization_performed\": false,\n  \"fresh_runtime_observation\": true,\n  \"saved_metadata_usage_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,complete?"true":"false",(unsigned long long)(first?first->count:0u),(unsigned long long)(first?first->occurrence_count:0u),(unsigned long long)(usage_max_index+2u),usage_max_index?"true":"false",(unsigned long long)counts[0],(unsigned long long)counts[1],(unsigned long long)counts[2],(unsigned long long)counts[3],(unsigned long long)counts[4],(unsigned long long)counts[5],(unsigned long long)counts[6],(unsigned long long)counts[7],(unsigned long long)usage_pairs.range_base,(unsigned long long)usage_pairs.pair_base,usage_case_fields[0],usage_case_fields[1],usage_case_fields[2],usage_case_fields[3],usage_case_fields[4],usage_case_fields[5],usage_case_fields[6],usage_case_fields[7],(unsigned long long)usage_case_tables[0],(unsigned long long)usage_case_tables[1],(unsigned long long)usage_case_tables[2],(unsigned long long)usage_case_tables[3],(unsigned long long)usage_case_tables[4],(unsigned long long)usage_case_tables[5],(unsigned long long)usage_case_tables[6],(unsigned long long)usage_case_tables[7],(unsigned long long)usage_decode_failure_index,usage_decode_failure_stage,usage_decode_failure_raw0,usage_decode_failure_raw1,usage_decode_failure_value0,usage_decode_failure_value1,usage_pairs.range_index_multiplier,usage_pairs.range_mix_xor,usage_pairs.range_mix_multiplier,usage_pairs.range_mid_multiplier,(unsigned long long)usage_pairs.range_wide_add,usage_pairs.range_final_multiplier,usage_pairs.range_first_shift,usage_pairs.range_second_shift*256u+usage_pairs.range_third_shift,(unsigned long long)usage_uncovered_nonempty_ranges,first?first->content_sha256:"",second?second->content_sha256:"",complete?"true":"false",usage_pairs.range_base&&usage_pairs.pair_base?"true":"false");fclose(output);_wchmod(usage_status_path,0600);
}
static void write_status(const char*status,int complete,uint64_t count,const char first_mapping[65],const char first_content[65],const char second_mapping[65],const char second_content[65]){
    FILE*output=_wfopen(status_path,L"wb");if(!output)return;fprintf(output,"{\n  \"schema\": \"alpha.runtime-string-literal-status/v2\",\n  \"status\": \"%s\",\n  \"complete\": %s,\n  \"literal_count\": %llu,\n  \"mapping_upper_bound_count\": %llu,\n  \"non_literal_mapping_tail_count\": %llu,\n  \"readable_region_count\": %u,\n  \"destination_table_owner_only\": %llu,\n  \"mapping_base_owner_only\": %llu,\n  \"data_base_owner_only\": %llu,\n  \"descriptor_global_owner_only\": %llu,\n  \"metadata_base_global_owner_only\": %llu,\n  \"descriptor_owner_only\": %llu,\n  \"metadata_base_owner_only\": %llu,\n  \"case5_target_owner_only\": %llu,\n  \"boundary_prefix_null_count\": %llu,\n  \"boundary_prefix_string_count\": %llu,\n  \"boundary_suffix_foreign_count\": %u,\n  \"boundary_witness_classes_owner_only\": [%llu, %llu, %llu],\n  \"decode_failure_index_owner_only\": %llu,\n  \"decode_failure_stage\": %u,\n  \"decode_failure_start_owner_only\": %u,\n  \"decode_failure_end_owner_only\": %u,\n  \"decode_failure_length_owner_only\": %u,\n  \"decode_failure_pointer_owner_only\": %llu,\n  \"usage_contract_stage_owner_only\": %u,\n  \"usage_initializer_owner_only\": %llu,\n  \"usage_state_global_owner_only\": %llu,\n  \"usage_state_owner_only\": %llu,\n  \"usage_switch_entry_count\": %u,\n  \"usage_case5_field_owner_only\": %u,\n  \"usage_call_site_count\": %llu,\n  \"usage_unique_index_count\": %llu,\n  \"usage_max_index_owner_only\": %llu,\n  \"usage_index_coverage_per_mille\": %u,\n  \"usage_initializer_derived\": %s,\n  \"case3_case6_shared\": %s,\n  \"case5_selector_derived\": %s,\n  \"decoder_contract_runtime_derived\": %s,\n  \"read_only_decoder\": true,\n  \"usage_materialization_performed\": false,\n  \"first_mapping_sha256\": \"%s\",\n  \"first_content_sha256\": \"%s\",\n  \"second_mapping_sha256\": \"%s\",\n  \"second_content_sha256\": \"%s\",\n  \"two_observations_match\": %s,\n  \"fresh_runtime_observation\": true,\n  \"saved_string_literal_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,complete?"true":"false",(unsigned long long)count,(unsigned long long)(count+literal_structural_tail_count),(unsigned long long)literal_structural_tail_count,region_count,(unsigned long long)usage_table,(unsigned long long)decoder.mapping_base,(unsigned long long)decoder.data_base,(unsigned long long)decoder.descriptor_global,(unsigned long long)decoder.metadata_base_global,(unsigned long long)decoder.descriptor,(unsigned long long)decoder.metadata_base,(unsigned long long)decoder.case5_target,(unsigned long long)boundary_prefix_nulls,(unsigned long long)boundary_prefix_strings,boundary_suffix_foreign,(unsigned long long)boundary_witness_classes[0],(unsigned long long)boundary_witness_classes[1],(unsigned long long)boundary_witness_classes[2],(unsigned long long)decode_failure_index,decode_failure_stage,decode_failure_start,decode_failure_end,decode_failure_length,(unsigned long long)decode_failure_pointer,usage_contract_stage_owner_only,(unsigned long long)usage_initializer,(unsigned long long)usage_state_global,(unsigned long long)usage_state,usage_switch_entries,usage_case5_field,(unsigned long long)usage_call_sites,(unsigned long long)usage_unique_indices,(unsigned long long)usage_max_index,usage_coverage_per_mille,usage_initializer?"true":"false",usage_switch_entries==8u?"true":"false",usage_case5_field?"true":"false",decoder.mapping_base&&decoder.data_base?"true":"false",first_mapping,first_content,second_mapping,second_content,complete?"true":"false");fclose(output);_wchmod(status_path,0600);
}
static void write_decode_failure_sample(void){
    FILE*output=_wfopen(output_path,L"wb");if(!output)return;const char magic[8]={'B','A','L','S','L','D','I','A'};fwrite(magic,1,8u,output);fwrite(&decode_failure_stage,1,4u,output);fwrite(&decode_failure_index,1,8u,output);fwrite(&decode_failure_start,1,4u,output);fwrite(&decode_failure_end,1,4u,output);fwrite(&decode_failure_length,1,4u,output);fwrite(&decode_failure_pointer,1,8u,output);fwrite(&decode_failure_sample_owner_only,1,8u,output);fclose(output);_wchmod(output_path,0600);
}
static void write_usage_range_samples(void){
    FILE*output=_wfopen(usage_value_status_path,L"wb");if(!output)return;fprintf(output,"{\n  \"usage_codec\": %u,\n  \"failure_index\": %llu,\n  \"failure_stage\": %u,\n  \"samples\": [[%u, %u], [%u, %u], [%u, %u], [%u, %u]]\n}\n",usage_pairs.usage_codec,(unsigned long long)usage_decode_failure_index,usage_decode_failure_stage,usage_range_sample_raw[0],usage_range_sample_value[0],usage_range_sample_raw[1],usage_range_sample_value[1],usage_range_sample_raw[2],usage_range_sample_value[2],usage_range_sample_raw[3],usage_range_sample_value[3]);fclose(output);_wchmod(usage_value_status_path,0600);
}
static DWORD WINAPI worker(LPVOID unused){
    (void)unused;_wremove(output_path);_wremove(status_path);_wremove(usage_output_path);_wremove(usage_status_path);_wremove(usage_value_output_path);_wremove(usage_value_status_path);_wremove(usage_member_output_path);_wremove(usage_member_status_path);char executable[65]={0},empty[65]={0};uint64_t upper_count=0,second_upper_count=0,count=0,first_tail_count=0;decoded_inventory first={0},second={0};decoded_usage_inventory first_usage={0},second_usage={0};decoded_usage_value_inventory first_values={0},second_values={0};decoded_usage_member_inventory first_members={0},second_members={0};
    if(GetCurrentProcessId()!=expected_pid||!executable_identity(executable)||strcmp(executable,executable_sha256)){write_status("identity_mismatch",0,0,empty,empty,empty,empty);return 0;}
    HMODULE image=GetModuleHandleW(NULL);if((uintptr_t)image!=expected_image_base||!enumerate_regions()){write_status("image_mismatch",0,0,empty,empty,empty,empty);return 0;}
    if(!derive_usage_contract(image)){write_usage_status("contract_not_unique",0,NULL,NULL);write_status("usage_decoder_contract_not_unique",0,0,empty,empty,empty,empty);return 0;}
    if(!derive_call_site_coverage(image)){write_status("usage_call_site_contract_failed",0,0,empty,empty,empty,empty);return 0;}


    if(usage_pairs.usage_codec==2u){
        if(!decode_literals_any(image,&upper_count,&first)){write_decode_failure_sample();write_status("first_read_only_decode_failed",0,upper_count,empty,empty,empty,empty);free_decoded_inventory(&first);return 0;}count=first.count;first_tail_count=literal_structural_tail_count;
        Sleep(250u);if(!decode_literals_any(image,&second_upper_count,&second)||second_upper_count!=upper_count||second.count!=count||literal_structural_tail_count!=first_tail_count||strcmp(first.mapping_sha256,second.mapping_sha256)||strcmp(first.content_sha256,second.content_sha256)){write_status("observation_unstable",0,count,first.mapping_sha256,first.content_sha256,second.mapping_sha256,second.content_sha256);free_decoded_inventory(&first);free_decoded_inventory(&second);return 0;}
        int pair_ok=decode_usage_inventory(image,&first_usage);Sleep(250u);if(pair_ok)pair_ok=decode_usage_inventory(image,&second_usage)&&first_usage.count==second_usage.count&&first_usage.occurrence_count==second_usage.occurrence_count&&!memcmp(first_usage.kind_counts,second_usage.kind_counts,sizeof(first_usage.kind_counts))&&!strcmp(first_usage.content_sha256,second_usage.content_sha256);if(pair_ok)pair_ok=validate_usage_literal_subset(&first_usage,count)&&write_usage_output(&first_usage);write_usage_status(pair_ok?"complete":"direct_pair_pending",pair_ok,&first_usage,&second_usage);


        int value_ok=0;if(pair_ok&&snapshot_usage_values(&first_usage,&first_values)){Sleep(250u);if(snapshot_usage_values(&second_usage,&second_values)&&first_values.count==second_values.count&&first_values.nonzero_value_count==second_values.nonzero_value_count&&first_values.kind1_count==second_values.kind1_count&&first_values.generic_record_count==second_values.generic_record_count&&!strcmp(first_values.content_sha256,second_values.content_sha256))value_ok=write_usage_value_output(&first_values);}write_usage_value_status(value_ok?"complete":"direct_value_pending",value_ok,&first_values,&second_values);
        int member_ok=0;if(pair_ok&&snapshot_usage_members(&first_usage,&first_members)){Sleep(250u);if(snapshot_usage_members(&second_usage,&second_members)&&first_members.count==second_members.count&&first_members.field_ref_count==second_members.field_ref_count&&first_members.method_spec_count==second_members.method_spec_count&&!strcmp(first_members.content_sha256,second_members.content_sha256))member_ok=write_usage_member_output(&first_members,&first_usage);}write_usage_member_status(member_ok?"complete":"direct_member_pending",member_ok,&first_members,&second_members);
        int direct_ok=pair_ok&&value_ok&&member_ok&&write_output(&first);write_status(direct_ok?"complete":"write_failed",direct_ok,count,first.mapping_sha256,first.content_sha256,second.mapping_sha256,second.content_sha256);free_decoded_inventory(&first);free_decoded_inventory(&second);free_decoded_usage_inventory(&first_usage);free_decoded_usage_inventory(&second_usage);free_decoded_usage_value_inventory(&first_values);free_decoded_usage_value_inventory(&second_values);free_decoded_usage_member_inventory(&first_members);free_decoded_usage_member_inventory(&second_members);return 0;
    }
    if(!decode_usage_inventory(image,&first_usage)){write_usage_range_samples();write_usage_status("first_read_only_decode_failed",0,NULL,NULL);write_status("usage_pair_decode_failed",0,0,empty,empty,empty,empty);return 0;}
    if(!snapshot_usage_values(&first_usage,&first_values)){write_usage_value_status("first_read_only_snapshot_failed",0,NULL,NULL);write_status("usage_value_snapshot_failed",0,0,empty,empty,empty,empty);free_decoded_usage_inventory(&first_usage);return 0;}
    if(!snapshot_usage_members(&first_usage,&first_members)){write_usage_member_status("first_read_only_snapshot_failed",0,NULL,NULL);write_status("usage_member_snapshot_failed",0,0,empty,empty,empty,empty);free_decoded_usage_inventory(&first_usage);free_decoded_usage_value_inventory(&first_values);return 0;}
    if(!decode_literals_any(image,&upper_count,&first)){write_decode_failure_sample();write_status("first_read_only_decode_failed",0,upper_count,empty,empty,empty,empty);free_decoded_usage_inventory(&first_usage);free_decoded_usage_value_inventory(&first_values);free_decoded_usage_member_inventory(&first_members);return 0;}count=first.count;first_tail_count=literal_structural_tail_count;
    Sleep(250u);if(!decode_usage_inventory(image,&second_usage)||first_usage.count!=second_usage.count||first_usage.occurrence_count!=second_usage.occurrence_count||memcmp(first_usage.kind_counts,second_usage.kind_counts,sizeof(first_usage.kind_counts))||strcmp(first_usage.content_sha256,second_usage.content_sha256)){write_usage_status("observation_unstable",0,&first_usage,&second_usage);write_status("usage_observation_unstable",0,count,first.mapping_sha256,first.content_sha256,empty,empty);free_decoded_inventory(&first);free_decoded_usage_inventory(&first_usage);free_decoded_usage_inventory(&second_usage);free_decoded_usage_value_inventory(&first_values);free_decoded_usage_member_inventory(&first_members);return 0;}
    if(!snapshot_usage_values(&second_usage,&second_values)||first_values.count!=second_values.count||first_values.nonzero_value_count!=second_values.nonzero_value_count||first_values.kind1_count!=second_values.kind1_count||first_values.generic_record_count!=second_values.generic_record_count||strcmp(first_values.content_sha256,second_values.content_sha256)){write_usage_value_status("observation_unstable",0,&first_values,&second_values);write_status("usage_value_observation_unstable",0,count,first.mapping_sha256,first.content_sha256,empty,empty);free_decoded_inventory(&first);free_decoded_usage_inventory(&first_usage);free_decoded_usage_inventory(&second_usage);free_decoded_usage_value_inventory(&first_values);free_decoded_usage_value_inventory(&second_values);free_decoded_usage_member_inventory(&first_members);return 0;}
    if(!snapshot_usage_members(&second_usage,&second_members)||first_members.count!=second_members.count||first_members.field_ref_count!=second_members.field_ref_count||first_members.method_spec_count!=second_members.method_spec_count||strcmp(first_members.content_sha256,second_members.content_sha256)){write_usage_member_status("observation_unstable",0,&first_members,&second_members);write_status("usage_member_observation_unstable",0,count,first.mapping_sha256,first.content_sha256,empty,empty);free_decoded_inventory(&first);free_decoded_usage_inventory(&first_usage);free_decoded_usage_inventory(&second_usage);free_decoded_usage_value_inventory(&first_values);free_decoded_usage_value_inventory(&second_values);free_decoded_usage_member_inventory(&first_members);free_decoded_usage_member_inventory(&second_members);return 0;}
    if(!decode_literals_any(image,&second_upper_count,&second)||second_upper_count!=upper_count||second.count!=count||literal_structural_tail_count!=first_tail_count||strcmp(first.mapping_sha256,second.mapping_sha256)||strcmp(first.content_sha256,second.content_sha256)){write_status("observation_unstable",0,count,first.mapping_sha256,first.content_sha256,second.mapping_sha256,second.content_sha256);free_decoded_inventory(&first);free_decoded_inventory(&second);free_decoded_usage_inventory(&first_usage);free_decoded_usage_inventory(&second_usage);free_decoded_usage_value_inventory(&first_values);free_decoded_usage_value_inventory(&second_values);free_decoded_usage_member_inventory(&first_members);free_decoded_usage_member_inventory(&second_members);return 0;}
    int member_ok=write_usage_member_output(&first_members,&first_usage);write_usage_member_status(member_ok?"complete":"write_failed",member_ok,&first_members,&second_members);int value_ok=member_ok&&write_usage_value_output(&first_values);write_usage_value_status(value_ok?"complete":"write_failed",value_ok,&first_values,&second_values);int usage_ok=value_ok&&validate_usage_literal_subset(&first_usage,count)&&validate_usage_literal_subset(&second_usage,count)&&write_usage_output(&first_usage);write_usage_status(usage_ok?"complete":"write_failed",usage_ok,&first_usage,&second_usage);int ok=usage_ok&&write_output(&first);write_status(ok?"complete":"write_failed",ok,count,first.mapping_sha256,first.content_sha256,second.mapping_sha256,second.content_sha256);free_decoded_inventory(&first);free_decoded_inventory(&second);free_decoded_usage_inventory(&first_usage);free_decoded_usage_inventory(&second_usage);free_decoded_usage_value_inventory(&first_values);free_decoded_usage_value_inventory(&second_values);free_decoded_usage_member_inventory(&first_members);free_decoded_usage_member_inventory(&second_members);return 0;
}
BOOL WINAPI DllMain(HINSTANCE instance,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(instance);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def runtime_string_literal_source(
    *, binding: dict[str, Any], output_path: Path, status_path: Path,
    usage_output_path: Path | None = None,
    usage_status_path: Path | None = None,
    usage_value_output_path: Path | None = None,
    usage_value_status_path: Path | None = None,
    usage_member_output_path: Path | None = None,
    usage_member_status_path: Path | None = None,
    decode_probe_path: Path | None = None,
    usage_v2: dict[str, Any] | None = None,
) -> str:
    if usage_output_path is None:
        usage_output_path = output_path.parent / "runtime-metadata-usage-pairs.private.bin"
    if usage_status_path is None:
        usage_status_path = output_path.parent / "runtime-metadata-usage-pairs-status.private.json"
    if usage_value_output_path is None:
        usage_value_output_path = (
            output_path.parent / "runtime-metadata-usage-values.private.bin"
        )
    if usage_value_status_path is None:
        usage_value_status_path = (
            output_path.parent / "runtime-metadata-usage-values-status.private.json"
        )
    if usage_member_output_path is None:
        usage_member_output_path = (
            output_path.parent / "runtime-metadata-usage-members.private.bin"
        )
    if usage_member_status_path is None:
        usage_member_status_path = (
            output_path.parent
            / "runtime-metadata-usage-members-status.private.json"
        )
    if decode_probe_path is None:
        decode_probe_path = (
            output_path.parent / "runtime-string-literals-decode.private.json"
        )
    v2 = usage_v2 or {}

    def v2_value(key: str, default: int = 0) -> int:
        value = v2.get(key, default)
        return int(value) if isinstance(value, int) and value >= 0 else default

    return _COLLECTOR.substitute(
        header_bytes=RUNTIME_STRING_LITERAL_HEADER.size,
        record_bytes=RUNTIME_STRING_LITERAL_RECORD.size,
        usage_header_bytes=RUNTIME_METADATA_USAGE_PAIR_HEADER.size,
        usage_record_bytes=RUNTIME_METADATA_USAGE_PAIR_RECORD.size,
        usage_value_header_bytes=RUNTIME_METADATA_USAGE_VALUE_HEADER.size,
        usage_value_record_bytes=RUNTIME_METADATA_USAGE_VALUE_RECORD.size,
        usage_generic_record_bytes=RUNTIME_METADATA_USAGE_GENERIC_RECORD.size,
        usage_member_header_bytes=RUNTIME_METADATA_USAGE_MEMBER_HEADER.size,
        usage_member_record_bytes=RUNTIME_METADATA_USAGE_MEMBER_RECORD.size,
        executable_sha256=binding["binary"]["sha256"],
        identity_sha256=binding["type_identity_inventory"]["sha256"],
        process_id=binding["process_id"],
        image_base=binding["image_base"],
        image_bytes=binding["image_bytes"],
        string_class=binding["string_class"],
        output_path=_wide_literal(_windows_z_path(output_path)),
        status_path=_wide_literal(_windows_z_path(status_path)),
        usage_output_path=_wide_literal(_windows_z_path(usage_output_path)),
        usage_status_path=_wide_literal(_windows_z_path(usage_status_path)),
        usage_value_output_path=_wide_literal(
            _windows_z_path(usage_value_output_path)
        ),
        usage_value_status_path=_wide_literal(
            _windows_z_path(usage_value_status_path)
        ),
        usage_member_output_path=_wide_literal(
            _windows_z_path(usage_member_output_path)
        ),
        usage_member_status_path=_wide_literal(
            _windows_z_path(usage_member_status_path)
        ),
        decode_probe_path=_wide_literal(_windows_z_path(decode_probe_path)),
        usage_v2_available=(
            1 if v2.get("available") is True else 0
        ),
        usage_v2_materialize=(
            1 if v2.get("materialize") is True else 0
        ),
        usage_v2_materialize_limit=v2_value("materialize_limit"),
        usage_v2_descriptor=v2_value("descriptor"),
        usage_v2_descriptor_global=v2_value("descriptor_global"),
        usage_v2_metadata_base_global=v2_value("metadata_base_global"),
        usage_v2_metadata_base=v2_value("metadata_base"),
        usage_v2_type_helper=v2_value("type_helper"),
        usage_v2_type_state_global=v2_value("type_state_global"),
        usage_v2_type_state_field=v2_value("type_state_field"),
        usage_v2_type_generic_state_global=v2_value("type_generic_state_global"),
        usage_v2_type_generic_state_field=v2_value("type_generic_state_field"),
        usage_v2_type_generic_stride_shift=v2_value(
            "type_generic_stride_shift"
        ),
        usage_v2_range_field=v2_value("range_field"),
        usage_v2_range_add=v2_value("range_add"),
        usage_v2_range_multiplier=v2_value("range_multiplier"),
        usage_v2_range_shift1=v2_value("range_first_shift"),
        usage_v2_range_second=v2_value("range_second_multiplier"),
        usage_v2_range_shift2=v2_value("range_second_shift"),
        usage_v2_range_mix=v2_value("range_mix_multiplier"),
        usage_v2_range_xor=v2_value("range_final_xor"),
        usage_v2_pair_field=v2_value("pair_field"),
        usage_v2_pair_bias=v2_value("pair_bias"),
        usage_v2_pair_multiplier=v2_value("pair_multiplier"),
        usage_v2_pair_shift=v2_value("pair_shift"),
        usage_v2_pair_xor=v2_value("pair_xor"),
        usage_v2_pair_second=v2_value("pair_second_multiplier"),
        usage_v2_pair_shift2=v2_value("pair_second_shift"),
        usage_v2_pair_add=v2_value("pair_add"),
        usage_v2_pair_value_add=v2_value("pair_value_add"),
        usage_v2_field_base_field=v2_value("field_base_field"),
        usage_v2_field_base_xor=v2_value("field_base_xor"),
        usage_v2_field_index_multiplier=v2_value("index_multiplier"),
        usage_v2_field_index_xor=v2_value("index_xor"),
        usage_v2_field_index_mix=v2_value("index_mix_multiplier"),
        usage_v2_field_index_add=v2_value("index_mix_add"),
        usage_v2_field_index_final_xor=v2_value("index_final_xor"),
        usage_v2_field_value0_xor=v2_value("value0_xor"),
        usage_v2_field_value1_xor=v2_value("value1_xor"),
        usage_v2_method_spec_field=v2_value("method_spec_field"),
        usage_v2_method_spec_xor=v2_value("method_spec_xor"),
        usage_v2_method_spec_stride=v2_value("method_spec_stride"),
        usage_v2_generic_state_global=v2_value("generic_instance_state_global"),
        usage_v2_generic_state_field=v2_value("generic_instance_state_field"),
        usage_v2_generic_base=v2_value("generic_instance_base"),
        usage_v2_generic_stride=v2_value("generic_instance_stride"),
        usage_v2_type_record_base=v2_value("type_record_base"),
        usage_v2_literal_base_field=v2_value("literal_base_field"),
        usage_v2_literal_stream_step=v2_value("literal_stream_step"),
        usage_v2_literal_key_multiplier=v2_value("literal_key_multiplier"),
        usage_v2_literal_key_add=v2_value("literal_key_add"),
        usage_v2_literal_key_xor=v2_value("literal_key_xor"),
        usage_v2_literal_key_bias=v2_value("literal_key_bias"),
        usage_v2_literal_base_xor=v2_value("literal_base_xor"),
        usage_v2_literal_index_multiplier=v2_value("literal_index_multiplier"),
        usage_v2_literal_index_add=v2_value("literal_index_add"),
        usage_v2_literal_value_add=v2_value("literal_value_add"),
        usage_v2_literal_second_index_add=v2_value("literal_second_index_add"),
        usage_v2_literal_descriptor_field=v2_value("literal_descriptor_field"),
        usage_v2_literal_descriptor_bias=v2_value("literal_descriptor_bias"),
        usage_v2_type_record_shift=v2_value("type_record_shift", 4),
    )


def prepare_runtime_string_literal_inventory(
    *, binary: Path, type_identity_model: Path, type_identity_inventory: Path,
    output_dir: Path, compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
    )
    output_path = output_dir / "runtime-string-literals.private.bin"
    status_path = output_dir / "runtime-string-literals-status.private.json"
    usage_output_path = output_dir / "runtime-metadata-usage-pairs.private.bin"
    usage_status_path = (
        output_dir / "runtime-metadata-usage-pairs-status.private.json"
    )
    usage_value_output_path = (
        output_dir / "runtime-metadata-usage-values.private.bin"
    )
    usage_value_status_path = (
        output_dir / "runtime-metadata-usage-values-status.private.json"
    )
    usage_value_model_path = (
        output_dir / "runtime-metadata-usage-values.private.json"
    )
    usage_member_output_path = (
        output_dir / "runtime-metadata-usage-members.private.bin"
    )
    usage_member_status_path = (
        output_dir / "runtime-metadata-usage-members-status.private.json"
    )
    usage_member_model_path = (
        output_dir / "runtime-metadata-usage-members.private.json"
    )
    decode_probe_path = output_dir / "runtime-string-literals-decode.private.json"
    model_path = output_dir / "runtime-string-literals.private.json"
    plan_path = output_dir / "runtime-string-literals-plan.private.json"
    build_dir = _owner_directory(output_dir / "build-string-literals")
    source_path = build_dir / "runtime-string-literals.c"
    injector_source = build_dir / "runtime-string-literals-injector.c"
    injector_path = build_dir / "alpha-runtime-string-literals-injector.exe"
    for stale in (
        output_path, status_path, usage_output_path, usage_status_path,
        usage_value_output_path, usage_value_status_path,
        usage_value_model_path, usage_member_output_path,
        usage_member_status_path, usage_member_model_path, decode_probe_path,
        model_path,
    ):
        stale.unlink(missing_ok=True)
    usage_v2: dict[str, Any] = {"available": False}
    try:
        from alpha.h04 import MemorySnapshot
        from alpha.p57 import (
            derive_field_reference_codec_v2,
            derive_generic_instance_contract_v2,
            derive_literal_codec_v2,
            derive_method_spec_codec_v2,
            derive_type_generic_record_contract_v2,
            derive_type_record_contract_v2,
            derive_usage_codec_v2,
        )

        identity_plan = read_json(Path(binding["type_identity_plan"]["path"]))
        snapshot_path = Path(
            identity_plan.get("inputs", {}).get("snapshot", {}).get("path", "")
        )
        with MemorySnapshot(snapshot_path) as snapshot:
            type_record = derive_type_record_contract_v2(
                binary=binary, snapshot=snapshot
            )
            type_generic = derive_type_generic_record_contract_v2(
                binary=binary, snapshot=snapshot
            )
            usage_v2 = {
                "available": True,
                **derive_literal_codec_v2(
                    binary=binary, snapshot=snapshot
                ),
                **derive_usage_codec_v2(
                    binary=binary, snapshot=snapshot
                ),
                **derive_field_reference_codec_v2(
                    binary=binary, snapshot=snapshot
                ),
                **derive_method_spec_codec_v2(
                    binary=binary, snapshot=snapshot
                ),
                **derive_generic_instance_contract_v2(
                    binary=binary, snapshot=snapshot
                ),
                "type_record_base": type_record["base"],
                "type_record_shift": type_record["stride_shift"],
                "type_helper": binding["image_base"] + type_record["helper_rva"],
                "type_state_global": type_record["state_global"],
                "type_state_field": type_record["state_field"],
                "type_generic_state_global": type_generic["state_global"],
                "type_generic_state_field": type_generic["state_field"],
                "type_generic_stride_shift": type_generic["stride_shift"],
                "materialize": (
                    os.environ.get("ALPHA_USAGE_V2_MATERIALIZE") == "1"
                ),
                "materialize_limit": int(
                    os.environ.get("ALPHA_USAGE_V2_MATERIALIZE_LIMIT", "0") or 0
                ),
            }
    except (AcquisitionError, OSError, ValueError, KeyError):
        usage_v2 = {"available": False}
    _private_text(
        source_path,
        runtime_string_literal_source(
            binding=binding, output_path=output_path, status_path=status_path,
            usage_output_path=usage_output_path,
            usage_status_path=usage_status_path,
            usage_value_output_path=usage_value_output_path,
            usage_value_status_path=usage_value_status_path,
            usage_member_output_path=usage_member_output_path,
            usage_member_status_path=usage_member_status_path,
            usage_v2=usage_v2,
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-string-literals-"
        + file_identity(source_path)["sha256"][:12]
        + ".dll"
    )
    cc = _compiler(compiler)


    with ThreadPoolExecutor(max_workers=2) as executor:
        collector_build = executor.submit(
            cached_windows_build,
            [
                str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra",
                "-Wformat=2", "-Werror=format", str(source_path), "-o",
                str(collector_path), "-lbcrypt",
            ],
            label="runtime string literal collector",
            source_path=source_path,
            output_path=collector_path,
        )
        injector_build = executor.submit(
            cached_windows_build,
            [
                str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
                "-Wformat=2", "-Werror=format", str(injector_source), "-o",
                str(injector_path),
            ],
            label="runtime string literal injector",
            source_path=injector_source,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_STRING_LITERAL_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            "type_identity_model": binding["type_identity_model"],
            "type_identity_inventory": binding["type_identity_inventory"],
            "type_identity_plan": binding["type_identity_plan"],
        },
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "usage_output_path": str(usage_output_path),
        "usage_status_path": str(usage_status_path),
        "usage_value_output_path": str(usage_value_output_path),
        "usage_value_status_path": str(usage_value_status_path),
        "usage_value_model_path": str(usage_value_model_path),
        "usage_member_output_path": str(usage_member_output_path),
        "usage_member_status_path": str(usage_member_status_path),
        "usage_member_model_path": str(usage_member_model_path),
        "model_path": str(model_path),
        "contract": {
            "discovery": "runtime-derived-metadata-usage-switch-case5-read-only-raw-decoder",
            "usage_codec": 5 if usage_v2.get("available") is True else 1,
            "minimum_literal_count": 1024,
            "maximum_literal_count": 1_000_000,
            "usage_switch_entry_count": 8,
            "case3_case6_shared_required": True,
            "direct_call_index_coverage_per_mille": 990,
            "literal_boundary": "contiguous-decodable-mapping-prefix-bounded-by-cache-domain-and-dense-foreign-object-domain",
            "boundary_witness_count": 64,
            "raw_utf8_validation_required": True,
            "read_only_decoder_required": True,
            "usage_materialization_performed": False,
            "two_observations_required": True,
            "mapping_and_content_hash_stability_required": True,
            "owner_only": True,
            "saved_literal_seed_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_STRING_LITERAL_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "collector": plan["collector"],
        "contract": plan["contract"],
    }


def _validate(plan: dict[str, Any], status: dict[str, Any]) -> tuple[dict[str, int], dict[str, bool]]:
    output_path = _owner_file(Path(plan["output_path"]), label="inventory")
    raw = output_path.read_bytes()
    if len(raw) < RUNTIME_STRING_LITERAL_HEADER.size:
        raise AcquisitionError("runtime string literal inventory is truncated")
    header = RUNTIME_STRING_LITERAL_HEADER.unpack_from(raw)
    (
        magic, version, header_bytes, record_bytes, reserved,
        literal_count, mapping_base, image_base, image_bytes, string_bytes,
        readable_regions, boundary_witnesses, executable_raw, identity_raw,
        mapping_raw, content_raw,
    ) = header
    records_end = header_bytes + literal_count * record_bytes
    header_ok = (
        magic == RUNTIME_STRING_LITERAL_MAGIC
        and version == RUNTIME_STRING_LITERAL_VERSION
        and header_bytes == RUNTIME_STRING_LITERAL_HEADER.size
        and record_bytes == RUNTIME_STRING_LITERAL_RECORD.size
        and reserved == 0
        and 1024 <= literal_count <= 1_000_000
        and mapping_base > 0
        and image_base == plan["target"]["image_base_owner_only"]
        and image_bytes == plan["target"]["image_bytes"]
        and _digest(executable_raw, label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(identity_raw, label="identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and records_end + string_bytes == len(raw)
        and readable_regions > 0
        and boundary_witnesses == 64
    )
    records_ok = header_ok
    observed_records = 0
    observed_text_bytes = 0
    mapping_hasher = hashlib.sha256()
    content_hasher = hashlib.sha256()
    for index in range(literal_count if header_ok else 0):
        source, utf16_length, raw_pointer, text_offset, text_bytes, raw_start = (
            RUNTIME_STRING_LITERAL_RECORD.unpack_from(
                raw, header_bytes + index * record_bytes
            )
        )
        if (
            source != index
            or raw_pointer <= 0
            or text_offset != observed_text_bytes
            or text_offset + text_bytes > string_bytes
            or utf16_length > 0x100000
            or text_bytes > 0x1000000
            or text_bytes > 4 * utf16_length
        ):
            records_ok = False
            break
        value = raw[
            records_end + text_offset:records_end + text_offset + text_bytes
        ]
        try:
            decoded = value.decode("utf-8")
        except UnicodeDecodeError:
            records_ok = False
            break
        if len(decoded.encode("utf-16-le")) // 2 != utf16_length:
            records_ok = False
            break
        mapping_hasher.update(struct.pack("<III", source, raw_start, (raw_start + text_bytes) & 0xFFFFFFFF))
        content_hasher.update(struct.pack("<II", source, text_bytes))
        content_hasher.update(value)
        observed_records += 1
        observed_text_bytes += text_bytes
    records_ok = records_ok and observed_text_bytes == string_bytes
    mapping_digest = _digest(mapping_raw, label="mapping") if header_ok else ""
    content_digest = _digest(content_raw, label="content") if header_ok else ""
    destination_table = status.get("destination_table_owner_only", 0)
    destination_bytes = literal_count * 8
    destination_table_in_image = (
        isinstance(destination_table, int)
        and destination_table >= image_base
        and destination_table & 7 == 0
        and destination_table - image_base <= image_bytes
        and destination_bytes <= image_bytes - (destination_table - image_base)
    )
    checks = {
        "status_schema": status.get("schema") == RUNTIME_STRING_LITERAL_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete"
        and status.get("complete") is True,
        "header_bound": header_ok,
        "records_valid": records_ok,
        "literal_indices_complete": observed_records == literal_count,
        "mapping_digest_recomputed": records_ok
        and mapping_hasher.hexdigest() == mapping_digest,
        "content_digest_recomputed": records_ok
        and content_hasher.hexdigest() == content_digest,
        "status_count_matches": status.get("literal_count") == literal_count,
        "usage_initializer_runtime_derived": status.get(
            "usage_initializer_derived"
        ) is True
        and status.get("usage_initializer_owner_only", 0) > 0,
        "usage_switch_shape_valid": status.get("usage_switch_entry_count") == 8
        and status.get("case3_case6_shared") is True,
        "case5_selector_runtime_derived": status.get(
            "case5_selector_derived"
        ) is True
        and status.get("usage_state_global_owner_only", 0) > 0
        and status.get("usage_state_owner_only", 0) > 0
        and status.get("case5_target_owner_only", 0) > 0,
        "decoder_contract_runtime_derived": status.get(
            "decoder_contract_runtime_derived"
        ) is True
        and status.get("descriptor_global_owner_only", 0) > 0
        and status.get("metadata_base_global_owner_only", 0) > 0
        and status.get("mapping_base_owner_only", 0) == mapping_base
        and status.get("data_base_owner_only", 0) > 0,
        "literal_boundary_runtime_derived": destination_table_in_image
        and isinstance(status.get("mapping_upper_bound_count"), int)
        and isinstance(status.get("non_literal_mapping_tail_count"), int)
        and status["mapping_upper_bound_count"]
        == status.get("boundary_prefix_null_count", -1)
        + status.get("boundary_prefix_string_count", -1)
        == literal_count + status["non_literal_mapping_tail_count"]
        and 0 <= status["non_literal_mapping_tail_count"] <= 64
        and status.get("boundary_suffix_foreign_count", 0) >= 60
        and isinstance(status.get("boundary_witness_classes_owner_only"), list)
        and len(status["boundary_witness_classes_owner_only"]) == 3
        and all(
            isinstance(value, int) and value > 0
            for value in status["boundary_witness_classes_owner_only"]
        ),
        "usage_call_sites_observed_read_only": status.get(
            "usage_materialization_performed"
        ) is False
        and status.get("read_only_decoder") is True
        and status.get("usage_call_site_count", 0) >= 1024
        and status.get("usage_unique_index_count", 0) >= 1024
        and status.get("usage_index_coverage_per_mille", 0) >= 990,
        "two_observations_match": status.get("two_observations_match") is True
        and status.get("first_mapping_sha256") == mapping_digest
        and status.get("second_mapping_sha256") == mapping_digest
        and status.get("first_content_sha256") == content_digest
        and status.get("second_content_sha256") == content_digest,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_literal_seed_absent": status.get("saved_string_literal_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get("external_runtime_component_used") is False,
    }
    return {
        "literal_count": literal_count,
        "string_bytes": string_bytes,
        "readable_region_count": readable_regions,
        "boundary_witness_count": boundary_witnesses,
    }, checks


def _validate_usage_pairs(
    plan: dict[str, Any], status: dict[str, Any], *, literal_count: int
) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = _owner_file(Path(plan["usage_output_path"]), label="usage pairs")
    raw = output_path.read_bytes()
    if len(raw) < RUNTIME_METADATA_USAGE_PAIR_HEADER.size:
        raise AcquisitionError("runtime metadata usage pair inventory is truncated")
    header = RUNTIME_METADATA_USAGE_PAIR_HEADER.unpack_from(raw)
    (
        magic, version, header_bytes, record_bytes, reserved,
        usage_count, occurrence_count, image_base, image_bytes,
        *tail,
    ) = header
    kind_counts = list(tail[:8])
    executable_raw, identity_raw, content_raw = tail[8:]
    records_end = header_bytes + usage_count * record_bytes
    header_ok = (
        magic == RUNTIME_METADATA_USAGE_PAIR_MAGIC
        and version == RUNTIME_METADATA_USAGE_PAIR_VERSION
        and header_bytes == RUNTIME_METADATA_USAGE_PAIR_HEADER.size
        and record_bytes == RUNTIME_METADATA_USAGE_PAIR_RECORD.size
        and reserved == 0
        and 1024 <= usage_count <= occurrence_count <= 2_000_000
        and image_base == plan["target"]["image_base_owner_only"]
        and image_bytes == plan["target"]["image_bytes"]
        and _digest(executable_raw, label="usage executable")
        == plan["target"]["executable_sha256"]
        and _digest(identity_raw, label="usage identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and records_end == len(raw)
        and sum(kind_counts) == usage_count
    )
    observed_counts = [0] * 8
    previous_slot = 0
    records_ok = header_ok
    literal_subset_ok = header_ok
    case_tables = status.get("case_tables_owner_only", [])
    for index in range(usage_count if header_ok else 0):
        (
            first_occurrence, destination, usage_kind, source, slot_pointer,
        ) = RUNTIME_METADATA_USAGE_PAIR_RECORD.unpack_from(
            raw, header_bytes + index * record_bytes
        )
        if (
            first_occurrence >= occurrence_count
            or usage_kind >= 8
            or usage_kind == 2
            or source > 0x1FFFFFFF
            or slot_pointer < image_base
            or slot_pointer >= image_base + image_bytes
            or slot_pointer & 7
            or slot_pointer <= previous_slot
        ):
            records_ok = False
            break
        observed_counts[usage_kind] += 1
        previous_slot = slot_pointer
        if usage_kind == 5 and (
            source >= literal_count
            or destination != source
            or not isinstance(case_tables, list)
            or len(case_tables) != 8
            or slot_pointer != case_tables[5] + source * 8
        ):
            literal_subset_ok = False
    content_digest = _digest(content_raw, label="usage content") if header_ok else ""
    content_recomputed = hashlib.sha256(raw[header_bytes:]).hexdigest()
    status_kind_counts = status.get("kind_counts")
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_METADATA_USAGE_PAIR_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete"
        and status.get("complete") is True,
        "header_bound": header_ok,
        "records_valid": records_ok,
        "slots_strictly_unique": records_ok and previous_slot > image_base,
        "kind_counts_recomputed": records_ok and observed_counts == kind_counts,
        "literal_usage_is_valid_subset": literal_subset_ok
        and 0 < observed_counts[5] <= literal_count,
        "content_digest_recomputed": header_ok
        and content_recomputed == content_digest,
        "status_counts_match": status.get("usage_count") == usage_count
        and status.get("occurrence_count") == occurrence_count
        and status_kind_counts == kind_counts,
        "range_domain_complete": status.get("range_domain_complete") is True
        and isinstance(status.get("range_count"), int)
        and status["range_count"] >= 1024
        and isinstance(
            status.get("direct_call_form_unmatched_nonempty_range_count"), int
        )
        and 0
        <= status["direct_call_form_unmatched_nonempty_range_count"]
        < status["range_count"] // 1000 + 1,
        "case_tables_runtime_derived": isinstance(case_tables, list)
        and len(case_tables) == 8
        and all(
            value == 0
            or isinstance(value, int)
            and image_base <= value < image_base + image_bytes
            and value & 7 == 0
            for value in case_tables
        )
        and all(case_tables[kind] > 0 for kind in (1, 3, 4, 5, 6)),
        "two_observations_match": status.get("two_observations_match") is True
        and status.get("first_content_sha256") == content_digest
        and status.get("second_content_sha256") == content_digest,
        "initializer_contract_runtime_derived": status.get(
            "initializer_contract_runtime_derived"
        ) is True
        and status.get("range_base_owner_only", 0) > 0
        and status.get("pair_base_owner_only", 0) > 0,
        "read_only_decoder": status.get("read_only_decoder") is True
        and status.get("usage_materialization_performed") is False,
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
        is True,
        "saved_metadata_usage_absent": status.get("saved_metadata_usage_used")
        is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    return {
        "usage_count": usage_count,
        "occurrence_count": occurrence_count,
        "range_count": status.get("range_count", 0),
        "kind_counts": kind_counts,
    }, checks


def _validate_usage_values(
    plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = _owner_file(
        Path(plan["usage_value_output_path"]), label="usage values"
    )
    pair_path = _owner_file(Path(plan["usage_output_path"]), label="usage pairs")
    raw = output_path.read_bytes()
    pair_raw = pair_path.read_bytes()
    if len(raw) < RUNTIME_METADATA_USAGE_VALUE_HEADER.size:
        raise AcquisitionError("runtime metadata usage value inventory is truncated")
    if len(pair_raw) < RUNTIME_METADATA_USAGE_PAIR_HEADER.size:
        raise AcquisitionError("runtime metadata usage pair inventory is truncated")
    header = RUNTIME_METADATA_USAGE_VALUE_HEADER.unpack_from(raw)
    (
        magic, version, header_bytes, record_bytes, reserved,
        usage_count, nonzero_count, kind1_count, image_base, image_bytes,
        type_record_base, type_record_stride, generic_record_base,
        generic_record_stride, generic_record_count, executable_raw,
        identity_raw, content_raw,
    ) = header
    pair_header = RUNTIME_METADATA_USAGE_PAIR_HEADER.unpack_from(pair_raw)
    pair_count = pair_header[5]
    records_end = header_bytes + usage_count * record_bytes
    generic_records_end = (
        records_end
        + generic_record_count * RUNTIME_METADATA_USAGE_GENERIC_RECORD.size
    )
    usage_codec = plan.get("contract", {}).get("usage_codec", 1)


    generic_count_ok = (
        generic_record_count == 0
        if usage_codec == 5
        else 1 <= generic_record_count <= 2_000_000
    )
    header_ok = (
        magic == RUNTIME_METADATA_USAGE_VALUE_MAGIC
        and version == RUNTIME_METADATA_USAGE_VALUE_VERSION
        and header_bytes == RUNTIME_METADATA_USAGE_VALUE_HEADER.size
        and record_bytes == RUNTIME_METADATA_USAGE_VALUE_RECORD.size
        and reserved == 0
        and usage_count == pair_count
        and usage_count >= 1024
        and 0 <= nonzero_count <= usage_count
        and 0 < kind1_count <= usage_count
        and image_base == plan["target"]["image_base_owner_only"]
        and image_bytes == plan["target"]["image_bytes"]
        and image_base <= type_record_base < image_base + image_bytes
        and type_record_base & 7 == 0
        and type_record_stride >= 16
        and type_record_stride <= 64
        and type_record_stride & (type_record_stride - 1) == 0
        and generic_record_base > 0
        and generic_record_stride >= 32
        and generic_record_stride <= 256
        and generic_record_stride & (generic_record_stride - 1) == 0
        and generic_count_ok
        and _digest(executable_raw, label="usage value executable")
        == plan["target"]["executable_sha256"]
        and _digest(identity_raw, label="usage value identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and generic_records_end == len(raw)
    )
    records_ok = header_ok
    aligned_with_pairs = header_ok
    observed_nonzero = 0
    observed_kind1 = 0
    type_sources: set[int] = set()
    type_codes: dict[int, int] = {}
    related_type_codes: dict[int, int] = {}
    for index in range(usage_count if header_ok else 0):
        (
            first_occurrence, destination, usage_kind, source, slot_pointer,
            slot_value, type_pointer, type_data, type_bits,
            related_pointer, related_data, related_bits, related_aux,
            generic_pointer, generic_qword0, generic_qword1,
            generic_qword2, generic_qword3,
        ) = RUNTIME_METADATA_USAGE_VALUE_RECORD.unpack_from(
            raw, header_bytes + index * record_bytes
        )
        pair = RUNTIME_METADATA_USAGE_PAIR_RECORD.unpack_from(
            pair_raw,
            RUNTIME_METADATA_USAGE_PAIR_HEADER.size
            + index * RUNTIME_METADATA_USAGE_PAIR_RECORD.size,
        )
        if (
            (first_occurrence, destination, usage_kind, source, slot_pointer)
            != pair
        ):
            aligned_with_pairs = False
            break
        observed_nonzero += bool(slot_value)
        if usage_kind == 1:
            type_code = (type_bits >> 16) & 0xFF
            expected_pointer = type_record_base + source * type_record_stride
            if (
                source in type_sources
                or expected_pointer < type_record_base
                or expected_pointer + 16 > image_base + image_bytes
                or type_pointer != expected_pointer
                or type_code < 1
                or type_code > 0x1E
            ):
                records_ok = False
                break
            type_sources.add(source)
            type_codes[type_code] = type_codes.get(type_code, 0) + 1
            if type_code in (0x14, 0x1D):
                related_code = (related_bits >> 16) & 0xFF
                if not related_pointer or not 1 <= related_code <= 0x1E:
                    records_ok = False
                    break
                related_type_codes[related_code] = (
                    related_type_codes.get(related_code, 0) + 1
                )
            elif related_pointer or related_data or related_bits or related_aux:
                records_ok = False
                break
            if type_code == 0x15:
                generic_index = type_data & 0xFFFFFFFF
                if (
                    generic_index & 0x80000000
                    or generic_pointer
                    != generic_record_base + generic_index * generic_record_stride
                ):
                    records_ok = False
                    break
            elif any(
                (
                    generic_pointer, generic_qword0, generic_qword1,
                    generic_qword2, generic_qword3,
                )
            ):
                records_ok = False
                break
            observed_kind1 += 1
        elif any(
            (
                type_pointer, type_data, type_bits, related_pointer,
                related_data, related_bits, related_aux, generic_pointer,
                generic_qword0, generic_qword1, generic_qword2,
                generic_qword3,
            )
        ):
            records_ok = False
            break
    content_digest = _digest(content_raw, label="usage value content") if header_ok else ""
    content_recomputed = hashlib.sha256(raw[header_bytes:]).hexdigest()
    generic_records_ok = header_ok
    for index in range(generic_record_count if header_ok else 0):
        qword0, qword1, _qword2, _qword3 = (
            RUNTIME_METADATA_USAGE_GENERIC_RECORD.unpack_from(
                raw,
                records_end
                + index * RUNTIME_METADATA_USAGE_GENERIC_RECORD.size,
            )
        )
        if (
            qword0 >> 32
            or qword0 >= 1_000_000
            or not image_base <= qword1 < image_base + image_bytes
            or qword1 & 7
        ):
            generic_records_ok = False
            break
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_METADATA_USAGE_VALUE_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete"
        and status.get("complete") is True,
        "header_bound": header_ok,
        "records_valid": records_ok,
        "usage_pairs_exactly_aligned": aligned_with_pairs,
        "counts_recomputed": records_ok
        and observed_nonzero == nonzero_count
        and observed_kind1 == kind1_count,
        "kind1_sources_strictly_unique": records_ok
        and len(type_sources) == kind1_count,
        "content_digest_recomputed": header_ok
        and content_recomputed == content_digest,
        "generic_record_domain_complete": generic_records_ok,
        "status_counts_match": status.get("usage_count") == usage_count
        and status.get("nonzero_value_count") == nonzero_count
        and status.get("kind1_count") == kind1_count,
        "two_observations_match": status.get("two_observations_match") is True
        and status.get("first_content_sha256") == content_digest
        and status.get("second_content_sha256") == content_digest,
        "type_record_helper_runtime_derived": status.get(
            "type_record_helper_runtime_derived"
        ) is True
        and status.get("type_record_base_owner_only") == type_record_base
        and status.get("type_record_stride") == type_record_stride
        and status.get("generic_record_base_owner_only") == generic_record_base
        and status.get("generic_record_stride") == generic_record_stride
        and status.get("type_helper_owner_only", 0) > 0
        and status.get("type_state_global_owner_only", 0) > 0
        and isinstance(status.get("type_state_field_owner_only"), int)
        and status.get("generic_state_global_owner_only", 0) > 0
        and isinstance(status.get("generic_state_field_owner_only"), int),
        "read_only_snapshot": status.get("read_only_snapshot") is True
        and status.get("usage_materialization_performed") is False,
        "fresh_runtime_observation": status.get("fresh_runtime_observation")
        is True,
        "saved_metadata_usage_value_absent": status.get(
            "saved_metadata_usage_value_used"
        ) is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    return {
        "usage_count": usage_count,
        "nonzero_value_count": nonzero_count,
        "kind1_count": kind1_count,
        "type_record_stride": type_record_stride,
        "generic_record_count": generic_record_count,


        "type_code_counts": {
            str(code): type_codes[code] for code in sorted(type_codes)
        },
        "related_type_code_counts": {
            str(code): related_type_codes[code]
            for code in sorted(related_type_codes)
        },
    }, checks


def _validate_usage_members(
    plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = _owner_file(
        Path(plan["usage_member_output_path"]), label="usage members"
    )
    pair_path = _owner_file(
        Path(plan["usage_output_path"]), label="usage pairs"
    )
    raw = output_path.read_bytes()
    pair_raw = pair_path.read_bytes()
    if len(raw) < RUNTIME_METADATA_USAGE_MEMBER_HEADER.size:
        raise AcquisitionError(
            "runtime metadata usage member inventory is truncated"
        )
    if len(pair_raw) < RUNTIME_METADATA_USAGE_PAIR_HEADER.size:
        raise AcquisitionError(
            "runtime metadata usage member pair inventory is truncated"
        )
    header = RUNTIME_METADATA_USAGE_MEMBER_HEADER.unpack_from(raw)
    (
        magic, version, header_bytes, record_bytes, reserved,
        usage_count, field_count, method_count, image_base, image_bytes,
        type_base, type_stride, generic_inst_base, generic_inst_stride,
        executable_raw, identity_raw, usage_raw, content_raw,
    ) = header
    pair_header = RUNTIME_METADATA_USAGE_PAIR_HEADER.unpack_from(pair_raw)
    member_count = field_count + method_count
    pair_header_ok = (
        pair_header[0] == RUNTIME_METADATA_USAGE_PAIR_MAGIC
        and pair_header[1] == RUNTIME_METADATA_USAGE_PAIR_VERSION
        and pair_header[2] == RUNTIME_METADATA_USAGE_PAIR_HEADER.size
        and pair_header[3] == RUNTIME_METADATA_USAGE_PAIR_RECORD.size
        and pair_header[4] == 0
        and RUNTIME_METADATA_USAGE_PAIR_HEADER.size
        + pair_header[5] * RUNTIME_METADATA_USAGE_PAIR_RECORD.size
        == len(pair_raw)
    )
    header_ok = (
        pair_header_ok
        and magic == RUNTIME_METADATA_USAGE_MEMBER_MAGIC
        and version == RUNTIME_METADATA_USAGE_MEMBER_VERSION
        and header_bytes == RUNTIME_METADATA_USAGE_MEMBER_HEADER.size
        and record_bytes == RUNTIME_METADATA_USAGE_MEMBER_RECORD.size
        and reserved == 0
        and usage_count == pair_header[5]
        and field_count == pair_header[9 + 4]
        and method_count == pair_header[9 + 6]
        and member_count >= 1024
        and header_bytes + member_count * record_bytes == len(raw)
        and image_base == plan["target"]["image_base_owner_only"]
        and image_bytes == plan["target"]["image_bytes"]
        and image_base <= type_base < image_base + image_bytes
        and type_stride == 16
        and image_base <= generic_inst_base < image_base + image_bytes
        and generic_inst_stride == 16
        and _digest(executable_raw, label="usage member executable")
        == plan["target"]["executable_sha256"]
        and _digest(identity_raw, label="usage member identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(usage_raw, label="usage member pair content")
        == _digest(pair_header[19], label="usage pair content")
    )
    pair_members: list[tuple[int, int, int, int, int]] = []
    if header_ok:


        for row in RUNTIME_METADATA_USAGE_PAIR_RECORD.iter_unpack(
            memoryview(pair_raw)[
                RUNTIME_METADATA_USAGE_PAIR_HEADER.size :
                RUNTIME_METADATA_USAGE_PAIR_HEADER.size
                + pair_header[5] * RUNTIME_METADATA_USAGE_PAIR_RECORD.size
            ]
        ):
            if row[2] in (4, 6):
                pair_members.append(row)
    records_ok = header_ok and len(pair_members) == member_count
    field_sources: set[int] = set()
    method_sources: set[int] = set()
    observed_fields = 0
    observed_methods = 0
    if records_ok:


        for pair_row, row in zip(
            pair_members,
            RUNTIME_METADATA_USAGE_MEMBER_RECORD.iter_unpack(
                memoryview(raw)[
                    header_bytes : header_bytes
                    + member_count * record_bytes
                ]
            ),
        ):
            (
                first, destination, kind, source, slot_pointer,
                value0, value1, value2, record_reserved,
            ) = row
            if (
                (first, destination, kind, source, slot_pointer) != pair_row
                or record_reserved
            ):
                records_ok = False
                break
            if kind == 4:
                if (
                    source in field_sources
                    or value0 < 0
                    or value1 < 0
                    or value2 != -1
                    or value0 > (image_bytes - 16) // type_stride
                    or value1 > 1_000_000
                ):
                    records_ok = False
                    break
                field_sources.add(source)
                observed_fields += 1
            elif kind == 6:
                if (
                    source in method_sources
                    or value0 < -1
                    or value1 < -1
                    or value0 > 2_000_000
                    or value1 > 2_000_000
                    or not 0 <= value2 < 2_000_000
                ):
                    records_ok = False
                    break
                method_sources.add(source)
                observed_methods += 1
            else:
                records_ok = False
                break
    content_digest = (
        _digest(content_raw, label="usage member content")
        if header_ok else ""
    )
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_METADATA_USAGE_MEMBER_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete"
        and status.get("complete") is True,
        "header_bound": header_ok,
        "records_valid": records_ok,
        "usage_pairs_exactly_aligned": records_ok,
        "counts_recomputed": records_ok
        and observed_fields == field_count
        and observed_methods == method_count,
        "sources_strictly_unique_by_kind": records_ok
        and len(field_sources) == field_count
        and len(method_sources) == method_count,
        "content_digest_recomputed": header_ok
        and hashlib.sha256(raw[header_bytes:]).hexdigest() == content_digest,
        "status_counts_match": status.get("member_usage_count")
        == member_count
        and status.get("field_ref_count") == field_count
        and status.get("method_spec_count") == method_count,
        "two_observations_match": status.get("two_observations_match")
        is True
        and status.get("first_content_sha256") == content_digest
        and status.get("second_content_sha256") == content_digest,
        "member_contract_runtime_derived": status.get(
            "member_contract_runtime_derived"
        ) is True
        and status.get("field_ref_base_owner_only", 0) > 0
        and status.get("field_ref_record_stride") == 8
        and status.get("method_spec_base_owner_only", 0) > 0
        and status.get("method_spec_record_stride") == 12
        and status.get("generic_inst_state_global_owner_only", 0) > 0
        and isinstance(
            status.get("generic_inst_state_field_owner_only"), int
        )
        and status.get("generic_inst_base_owner_only") == generic_inst_base
        and status.get("generic_inst_stride") == generic_inst_stride,
        "read_only_snapshot": status.get("read_only_snapshot") is True
        and status.get("usage_materialization_performed") is False,
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        ) is True,
        "saved_metadata_usage_member_absent": status.get(
            "saved_metadata_usage_member_used"
        ) is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        ) is False,
    }
    return {
        "usage_count": usage_count,
        "member_usage_count": member_count,
        "field_ref_count": field_count,
        "method_spec_count": method_count,
        "type_record_stride": type_stride,
        "generic_inst_stride": generic_inst_stride,
    }, checks


def load_runtime_string_literal_inventory(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:

    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    plan_path = _owner_file(
        model_path.parent / "runtime-string-literals-plan.private.json",
        label="plan",
    )
    status_path = _owner_file(
        model_path.parent / "runtime-string-literals-status.private.json",
        label="status receipt",
    )
    model = read_json(model_path)
    plan = read_json(plan_path)
    status = read_json(status_path)
    executable_sha256 = model.get("target", {}).get("executable_sha256")
    model_checks = model.get("checks", {})
    if (
        model.get("schema") != RUNTIME_STRING_LITERAL_SCHEMA
        or model.get("status") != "runtime-validated"
        or not isinstance(executable_sha256, str)
        or len(executable_sha256) != 64
        or not isinstance(model_checks, dict)
        or not model_checks
        or not all(model_checks.values())
        or model.get("inventory", {}).get("sha256")
        != file_identity(inventory_path)["sha256"]
        or model.get("status_receipt", {}).get("sha256")
        != file_identity(status_path)["sha256"]
        or plan.get("schema") != RUNTIME_STRING_LITERAL_PLAN_SCHEMA
        or plan.get("status") != "prepared"
        or plan.get("target", {}).get("executable_sha256")
        != executable_sha256
        or Path(plan.get("output_path", "")).expanduser().resolve()
        != inventory_path
        or Path(plan.get("status_path", "")).expanduser().resolve()
        != status_path
        or Path(plan.get("model_path", "")).expanduser().resolve()
        != model_path
        or (
            expected_executable_sha256 is not None
            and executable_sha256 != expected_executable_sha256.lower()
        )
    ):
        raise AcquisitionError("runtime string literal model binding is stale")
    counts, checks = _validate(plan, status)
    if (
        not all(checks.values())
        or model.get("counts") != counts
        or model_checks != checks
    ):
        raise AcquisitionError("runtime string literal validation is stale")

    raw = inventory_path.read_bytes()
    header = RUNTIME_STRING_LITERAL_HEADER.unpack_from(raw)
    header_bytes = header[2]
    record_bytes = header[3]
    literal_count = header[5]
    image_base = header[7]
    image_bytes = header[8]
    records_end = header_bytes + literal_count * record_bytes
    destination_table = status["destination_table_owner_only"]
    slot_base_rva = destination_table - image_base
    literals: list[dict[str, Any]] = []
    for index in range(literal_count):
        source, _utf16_length, _raw_pointer, text_offset, text_bytes, _raw_start = (
            RUNTIME_STRING_LITERAL_RECORD.unpack_from(
                raw, header_bytes + index * record_bytes
            )
        )
        value = raw[
            records_end + text_offset:records_end + text_offset + text_bytes
        ].decode("utf-8")
        literals.append(
            {
                "index": source,
                "rva": slot_base_rva + source * 8,
                "value": value,
            }
        )
    if (
        len(literals) != literal_count
        or any(record["index"] != index for index, record in enumerate(literals))
        or slot_base_rva & 7
        or slot_base_rva + literal_count * 8 > image_bytes
    ):
        raise AcquisitionError("runtime string literal public mapping is incomplete")
    return {
        "schema": RUNTIME_STRING_LITERAL_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contracts": {
            "type_identity_inventory_sha256": plan["inputs"][
                "type_identity_inventory"
            ]["sha256"],
            "mapping_sha256": _digest(header[14], label="mapping"),
            "content_sha256": _digest(header[15], label="content"),
        },
        "counts": counts,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "slot_base_rva": slot_base_rva,
        "slot_bytes": literal_count * 8,
        "literals": literals,
        "identity": file_identity(inventory_path),
        "read_only_decoder": True,
        "usage_materialization_performed": False,
        "raw_native_addresses_owner_only": True,
    }


def load_runtime_metadata_usage_pair_inventory(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
    expected_string_literal_inventory_sha256: str | None = None,
) -> dict[str, Any]:
    model_path = _owner_file(model_path, label="usage pair model")
    inventory_path = _owner_file(inventory_path, label="usage pair inventory")
    plan_path = _owner_file(
        model_path.parent / "runtime-string-literals-plan.private.json",
        label="usage pair plan",
    )
    status_path = _owner_file(
        model_path.parent / "runtime-metadata-usage-pairs-status.private.json",
        label="usage pair status",
    )
    model = read_json(model_path)
    plan = read_json(plan_path)
    status = read_json(status_path)
    target_sha256 = model.get("target", {}).get("executable_sha256")
    checks = model.get("checks", {})
    literal_count = model.get("contracts", {}).get("literal_count")
    literal_inventory_sha256 = model.get("inputs", {}).get(
        "string_literal_inventory", {}
    ).get("sha256")
    if (
        model.get("schema") != RUNTIME_METADATA_USAGE_PAIR_SCHEMA
        or model.get("status") != "runtime-validated"
        or not isinstance(checks, dict)
        or not checks
        or not all(checks.values())
        or not isinstance(literal_count, int)
        or literal_count < 1024
        or model.get("inventory", {}).get("sha256")
        != file_identity(inventory_path)["sha256"]
        or model.get("status_receipt", {}).get("sha256")
        != file_identity(status_path)["sha256"]
        or plan.get("schema") != RUNTIME_STRING_LITERAL_PLAN_SCHEMA
        or Path(plan.get("usage_output_path", "")).expanduser().resolve()
        != inventory_path
        or Path(plan.get("usage_status_path", "")).expanduser().resolve()
        != status_path
        or plan.get("target", {}).get("executable_sha256") != target_sha256
        or (
            expected_executable_sha256 is not None
            and target_sha256 != expected_executable_sha256.lower()
        )
        or (
            expected_string_literal_inventory_sha256 is not None
            and literal_inventory_sha256
            != expected_string_literal_inventory_sha256.lower()
        )
    ):
        raise AcquisitionError("runtime metadata usage pair binding is stale")
    counts, current_checks = _validate_usage_pairs(
        plan, status, literal_count=literal_count
    )
    if model.get("counts") != counts or checks != current_checks or not all(
        current_checks.values()
    ):
        raise AcquisitionError("runtime metadata usage pair validation is stale")
    raw = inventory_path.read_bytes()
    header = RUNTIME_METADATA_USAGE_PAIR_HEADER.unpack_from(raw)
    usage_count = header[5]
    image_base = header[7]
    image_bytes = header[8]
    records: list[dict[str, int]] = []
    for index in range(usage_count):
        first_occurrence, destination, usage_kind, source, slot_pointer = (
            RUNTIME_METADATA_USAGE_PAIR_RECORD.unpack_from(
                raw,
                RUNTIME_METADATA_USAGE_PAIR_HEADER.size
                + index * RUNTIME_METADATA_USAGE_PAIR_RECORD.size,
            )
        )
        records.append(
            {
                "first_occurrence_index": first_occurrence,
                "destination_index": destination,
                "usage_kind": usage_kind,
                "source_index": source,
                "rva": slot_pointer - image_base,
            }
        )
    return {
        "schema": RUNTIME_METADATA_USAGE_PAIR_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": target_sha256},
        "contracts": {
            "string_literal_inventory_sha256": literal_inventory_sha256,
            "literal_count": literal_count,
            "content_sha256": _digest(header[19], label="usage content"),
        },
        "counts": counts,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "usages": records,
        "identity": file_identity(inventory_path),
        "read_only_decoder": True,
        "usage_materialization_performed": False,
        "raw_native_addresses_owner_only": True,
    }


def load_runtime_metadata_usage_value_inventory(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
    expected_metadata_usage_pair_inventory_sha256: str | None = None,
) -> dict[str, Any]:
    model_path = _owner_file(model_path, label="usage value model")
    inventory_path = _owner_file(inventory_path, label="usage value inventory")
    plan_path = _owner_file(
        model_path.parent / "runtime-string-literals-plan.private.json",
        label="usage value plan",
    )
    status_path = _owner_file(
        model_path.parent / "runtime-metadata-usage-values-status.private.json",
        label="usage value status",
    )
    model = read_json(model_path)
    plan = read_json(plan_path)
    status = read_json(status_path)
    target_sha256 = model.get("target", {}).get("executable_sha256")
    checks = model.get("checks", {})
    pair_sha256 = model.get("inputs", {}).get(
        "metadata_usage_pair_inventory", {}
    ).get("sha256")
    if (
        model.get("schema") != RUNTIME_METADATA_USAGE_VALUE_SCHEMA
        or model.get("status") != "runtime-validated"
        or not isinstance(checks, dict)
        or not checks
        or not all(checks.values())
        or model.get("inventory", {}).get("sha256")
        != file_identity(inventory_path)["sha256"]
        or model.get("status_receipt", {}).get("sha256")
        != file_identity(status_path)["sha256"]
        or plan.get("schema") != RUNTIME_STRING_LITERAL_PLAN_SCHEMA
        or Path(plan.get("usage_value_output_path", "")).expanduser().resolve()
        != inventory_path
        or Path(plan.get("usage_value_status_path", "")).expanduser().resolve()
        != status_path
        or plan.get("target", {}).get("executable_sha256") != target_sha256
        or (
            expected_executable_sha256 is not None
            and target_sha256 != expected_executable_sha256.lower()
        )
        or (
            expected_metadata_usage_pair_inventory_sha256 is not None
            and pair_sha256
            != expected_metadata_usage_pair_inventory_sha256.lower()
        )
    ):
        raise AcquisitionError("runtime metadata usage value binding is stale")
    counts, current_checks = _validate_usage_values(plan, status)
    if model.get("counts") != counts or checks != current_checks or not all(
        current_checks.values()
    ):
        raise AcquisitionError("runtime metadata usage value validation is stale")
    raw = inventory_path.read_bytes()
    header = RUNTIME_METADATA_USAGE_VALUE_HEADER.unpack_from(raw)
    usage_count = header[5]
    image_base = header[8]
    image_bytes = header[9]
    type_usages: list[dict[str, int]] = []
    for index in range(usage_count):
        row = RUNTIME_METADATA_USAGE_VALUE_RECORD.unpack_from(
            raw,
            RUNTIME_METADATA_USAGE_VALUE_HEADER.size
            + index * RUNTIME_METADATA_USAGE_VALUE_RECORD.size,
        )
        if row[2] != 1:
            continue
        type_usages.append(
            {
                "first_occurrence_index": row[0],
                "destination_index": row[1],
                "source_index": row[3],
                "rva": row[4] - image_base,
                "slot_value_owner_only": row[5],
                "type_record_rva": row[6] - image_base,
                "type_data_owner_only": row[7],
                "type_bits_owner_only": row[8],
            }
        )
    generic_start = (
        RUNTIME_METADATA_USAGE_VALUE_HEADER.size
        + usage_count * RUNTIME_METADATA_USAGE_VALUE_RECORD.size
    )
    generic_records = tuple(
        RUNTIME_METADATA_USAGE_GENERIC_RECORD.unpack_from(
            raw,
            generic_start + index * RUNTIME_METADATA_USAGE_GENERIC_RECORD.size,
        )
        for index in range(header[14])
    )
    if len(type_usages) != header[7]:
        raise AcquisitionError("runtime metadata usage type domain is incomplete")
    return {
        "schema": RUNTIME_METADATA_USAGE_VALUE_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": target_sha256},
        "contracts": {
            "type_identity_inventory_sha256": plan["inputs"][
                "type_identity_inventory"
            ]["sha256"],
            "metadata_usage_pair_inventory_sha256": pair_sha256,
            "content_sha256": _digest(header[17], label="usage value content"),
        },
        "counts": counts,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "type_record_base_rva": header[10] - image_base,
        "type_record_stride": header[11],
        "type_usages": type_usages,
        "generic_records_owner_only": generic_records,
        "identity": file_identity(inventory_path),
        "read_only_snapshot": True,
        "usage_materialization_performed": False,
        "raw_native_addresses_owner_only": True,
    }


def _usage_member_rows(raw: bytes, member_count: int):
    start = RUNTIME_METADATA_USAGE_MEMBER_HEADER.size
    end = start + member_count * RUNTIME_METADATA_USAGE_MEMBER_RECORD.size
    if end <= len(raw):
        return RUNTIME_METADATA_USAGE_MEMBER_RECORD.iter_unpack(
            memoryview(raw)[start:end]
        )
    return (
        RUNTIME_METADATA_USAGE_MEMBER_RECORD.unpack_from(
            raw, start + index * RUNTIME_METADATA_USAGE_MEMBER_RECORD.size
        )
        for index in range(member_count)
    )


def load_runtime_metadata_usage_member_inventory(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
    expected_metadata_usage_pair_inventory_sha256: str | None = None,
) -> dict[str, Any]:

    model_path = _owner_file(model_path, label="usage member model")
    inventory_path = _owner_file(
        inventory_path, label="usage member inventory"
    )
    plan_path = _owner_file(
        model_path.parent / "runtime-string-literals-plan.private.json",
        label="usage member plan",
    )
    status_path = _owner_file(
        model_path.parent
        / "runtime-metadata-usage-members-status.private.json",
        label="usage member status",
    )
    model = read_json(model_path)
    plan = read_json(plan_path)
    status = read_json(status_path)
    target_sha256 = model.get("target", {}).get("executable_sha256")
    checks = model.get("checks", {})
    pair_sha256 = model.get("inputs", {}).get(
        "metadata_usage_pair_inventory", {}
    ).get("sha256")
    pair_path_value = plan.get("usage_output_path", "")
    try:
        pair_path = _owner_file(
            Path(pair_path_value), label="usage member pair inventory"
        )
    except (OSError, TypeError, ValueError) as error:
        raise AcquisitionError(
            "runtime metadata usage member binding is stale"
        ) from error
    if (
        model.get("schema") != RUNTIME_METADATA_USAGE_MEMBER_SCHEMA
        or model.get("status") != "runtime-validated"
        or not isinstance(checks, dict)
        or not checks
        or not all(checks.values())
        or model.get("inventory", {}).get("sha256")
        != file_identity(inventory_path)["sha256"]
        or model.get("status_receipt", {}).get("sha256")
        != file_identity(status_path)["sha256"]
        or not isinstance(pair_sha256, str)
        or pair_sha256 != file_identity(pair_path)["sha256"]
        or plan.get("schema") != RUNTIME_STRING_LITERAL_PLAN_SCHEMA
        or plan.get("status") != "prepared"
        or Path(plan.get("usage_member_output_path", ""))
        .expanduser().resolve() != inventory_path
        or Path(plan.get("usage_member_status_path", ""))
        .expanduser().resolve() != status_path
        or Path(plan.get("usage_member_model_path", ""))
        .expanduser().resolve() != model_path
        or plan.get("target", {}).get("executable_sha256") != target_sha256
        or (
            expected_executable_sha256 is not None
            and target_sha256 != expected_executable_sha256.lower()
        )
        or (
            expected_metadata_usage_pair_inventory_sha256 is not None
            and pair_sha256
            != expected_metadata_usage_pair_inventory_sha256.lower()
        )
    ):
        raise AcquisitionError(
            "runtime metadata usage member binding is stale"
        )
    counts, current_checks = _validate_usage_members(plan, status)
    if model.get("counts") != counts or checks != current_checks or not all(
        current_checks.values()
    ):
        raise AcquisitionError(
            "runtime metadata usage member validation is stale"
        )

    raw = inventory_path.read_bytes()
    header = RUNTIME_METADATA_USAGE_MEMBER_HEADER.unpack_from(raw)
    member_count = header[6] + header[7]
    image_base = header[8]
    image_bytes = header[9]
    field_refs: list[dict[str, int]] = []
    method_specs: list[dict[str, int]] = []
    for (
        first, destination, usage_kind, source, slot_pointer,
        value0, value1, value2, _reserved,
    ) in _usage_member_rows(raw, member_count):


        rva = slot_pointer - image_base
        if not 0 <= rva < image_bytes:
            raise AcquisitionError(
                "runtime metadata usage member domain is incomplete"
            )
        common = {
            "first_occurrence_index": first,
            "destination_index": destination,
            "source_index": source,
            "rva": rva,
        }
        if usage_kind == 4:
            field_refs.append(
                {
                    **common,
                    "type_source_index": value0,
                    "field_index": value1,
                }
            )
        elif usage_kind == 6:
            method_specs.append(
                {
                    **common,
                    "method_inst_index": value0,
                    "class_inst_index": value1,
                    "method_definition_index": value2,
                }
            )
        else:
            raise AcquisitionError(
                "runtime metadata usage member domain is incomplete"
            )
    if (
        len(field_refs) != header[6]
        or len(method_specs) != header[7]
    ):
        raise AcquisitionError(
            "runtime metadata usage member domain is incomplete"
        )
    return {
        "schema": RUNTIME_METADATA_USAGE_MEMBER_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": target_sha256},
        "contracts": {
            "type_identity_inventory_sha256": plan["inputs"][
                "type_identity_inventory"
            ]["sha256"],
            "metadata_usage_pair_inventory_sha256": pair_sha256,
            "metadata_usage_pair_content_sha256": _digest(
                header[16], label="usage member pair content"
            ),
            "content_sha256": _digest(
                header[17], label="usage member content"
            ),
        },
        "counts": counts,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "type_record_base_rva": header[10] - image_base,
        "type_record_stride": header[11],
        "generic_inst_base_rva": header[12] - image_base,
        "generic_inst_stride": header[13],
        "field_refs": field_refs,
        "method_specs": method_specs,
        "identity": file_identity(inventory_path),
        "read_only_snapshot": True,
        "usage_materialization_performed": False,
        "raw_native_addresses_owner_only": True,
    }


def capture_runtime_string_literal_inventory(
    *, binary: Path, type_identity_model: Path, type_identity_inventory: Path,
    output_dir: Path, wine: Path, wineprefix: Path,
    compiler: Path | None = None, timeout: float = 300.0,
) -> dict[str, Any]:
    prepare_runtime_string_literal_inventory(
        binary=binary,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    output_dir = output_dir.expanduser().resolve()
    plan = read_json(output_dir / "runtime-string-literals-plan.private.json")
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    environment["WINEDEBUG"] = "-all"
    status_path = Path(plan["status_path"])


    retryable_statuses = {
        "observation_unstable",
        "usage_observation_unstable",
        "usage_value_observation_unstable",
        "usage_member_observation_unstable",
    }
    attempts = 4
    status: dict[str, Any] | None = None
    for attempt in range(1, attempts + 1):
        status_path.unlink(missing_ok=True)
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
                "runtime string literal injector could not run"
            ) from error
        _private_text(
            output_dir / "runtime-string-literals-injector.private.log",
            json.dumps(
                {
                    "attempt": attempt,
                    "returncode": injected.returncode,
                    "stdout": injected.stdout,
                    "stderr": injected.stderr,
                },
                ensure_ascii=False,
                indent=2,
            ) + "\n",
        )
        if injected.returncode:
            raise AcquisitionError("runtime string literal injection failed")
        deadline = time.monotonic() + timeout
        status = None
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
            raise AcquisitionError("runtime string literal capture timed out")
        if status.get("status") == "complete":
            break
        if status.get("status") not in retryable_statuses:
            break
        time.sleep(0.5 * attempt)
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime string literal capture failed "
            f"(status={status.get('status')}, "
            f"longest={status.get('literal_count')}, "
            f"runner_up={status.get('runner_up_count_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    usage_output_path = Path(plan["usage_output_path"])
    usage_status_path = Path(plan["usage_status_path"])
    usage_value_output_path = Path(plan["usage_value_output_path"])
    usage_value_status_path = Path(plan["usage_value_status_path"])
    usage_member_output_path = Path(plan["usage_member_output_path"])
    usage_member_status_path = Path(plan["usage_member_status_path"])
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    counts, checks = _validate(plan, status)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime string literal validation failed: "
            + ", ".join(sorted(key for key, value in checks.items() if not value))
        )
    usage_artifacts = (
        usage_output_path, usage_status_path, usage_value_output_path,
        usage_value_status_path, usage_member_output_path,
        usage_member_status_path,
    )
    usage_counts: dict[str, Any] | None = None
    usage_checks: dict[str, bool] | None = None
    usage_value_counts: dict[str, Any] | None = None
    usage_value_checks: dict[str, bool] | None = None
    usage_model_path = output_dir / "runtime-metadata-usage-pairs.private.json"
    usage_value_model_path = Path(plan["usage_value_model_path"])
    pair_artifacts_present = usage_output_path.is_file() and usage_status_path.is_file()
    if pair_artifacts_present:
        _seal_runtime_output(usage_output_path)
        _seal_runtime_output(usage_status_path)
        usage_status = read_json(usage_status_path)
        usage_counts, usage_checks = _validate_usage_pairs(
            plan, usage_status, literal_count=counts["literal_count"]
        )
        if not all(usage_checks.values()):
            raise AcquisitionError(
                "runtime metadata usage pair validation failed: "
                + ", ".join(
                    sorted(key for key, value in usage_checks.items() if not value)
                )
            )
        usage_model = {
            "schema": RUNTIME_METADATA_USAGE_PAIR_SCHEMA,
            "status": "runtime-validated",
            "target": {"executable_sha256": plan["target"]["executable_sha256"]},
            "inputs": {
                **plan["inputs"],
                "string_literal_inventory": file_identity(output_path),
            },
            "contracts": {"literal_count": counts["literal_count"]},
            "inventory": file_identity(usage_output_path),
            "status_receipt": file_identity(usage_status_path),
            "counts": usage_counts,
            "checks": usage_checks,
            "owner_only": True,
        }
        _private_json(usage_model_path, usage_model)


    value_artifacts_present = (
        usage_value_output_path.is_file() and usage_value_status_path.is_file()
    )
    if value_artifacts_present:
        _seal_runtime_output(usage_value_output_path)
        _seal_runtime_output(usage_value_status_path)
        usage_value_status = read_json(usage_value_status_path)
        usage_value_counts, usage_value_checks = _validate_usage_values(
            plan, usage_value_status
        )
        if not all(usage_value_checks.values()):
            raise AcquisitionError(
                "runtime metadata usage value validation failed: "
                + ", ".join(
                    sorted(
                        key for key, value in usage_value_checks.items()
                        if not value
                    )
                )
            )
        usage_value_model = {
            "schema": RUNTIME_METADATA_USAGE_VALUE_SCHEMA,
            "status": "runtime-validated",
            "target": {"executable_sha256": plan["target"]["executable_sha256"]},
            "inputs": {
                **plan["inputs"],
                "metadata_usage_pair_inventory": file_identity(
                    usage_output_path
                ),
            },
            "inventory": file_identity(usage_value_output_path),
            "status_receipt": file_identity(usage_value_status_path),
            "counts": usage_value_counts,
            "checks": usage_value_checks,
            "owner_only": True,
        }
        _private_json(usage_value_model_path, usage_value_model)


    if not all(path.is_file() for path in usage_artifacts):
        model = {
            "schema": RUNTIME_STRING_LITERAL_SCHEMA,
            "status": "runtime-validated",
            "target": {"executable_sha256": plan["target"]["executable_sha256"]},
            "inputs": plan["inputs"],
            "inventory": file_identity(output_path),
            "status_receipt": file_identity(status_path),
            "counts": counts,
            "checks": checks,
            "metadata_usage_state": (
                "direct-pairs-and-type-values-validated-members-pending"
                if usage_value_counts is not None
                else "direct-pairs-validated-values-and-members-pending"
                if usage_counts is not None
                else "pending-direct-pair-normalization"
            ),
            "owner_only": True,
        }
        if usage_counts is not None:
            model["metadata_usage_pair_model"] = file_identity(usage_model_path)
            model["metadata_usage_pair_inventory"] = file_identity(
                usage_output_path
            )
        if usage_value_counts is not None:
            model["metadata_usage_value_model"] = file_identity(
                usage_value_model_path
            )
            model["metadata_usage_value_inventory"] = file_identity(
                usage_value_output_path
            )
        _private_json(Path(plan["model_path"]), model)
        return {
            "schema": RUNTIME_STRING_LITERAL_SCHEMA,
            "status": "runtime-validated",
            "target": model["target"],
            "counts": counts,
            "checks": checks,
            "inventory": model["inventory"],
            "metadata_usage_state": model["metadata_usage_state"],
            **({
                "metadata_usage_pairs": {
                    "model": model["metadata_usage_pair_model"],
                    "inventory": model["metadata_usage_pair_inventory"],
                    "counts": usage_counts,
                    "checks": usage_checks,
                }
            } if usage_counts is not None else {}),
            **({
                "metadata_usage_values": {
                    "model": model["metadata_usage_value_model"],
                    "inventory": model["metadata_usage_value_inventory"],
                    "counts": usage_value_counts,
                    "checks": usage_value_checks,
                }
            } if usage_value_counts is not None else {}),
        }
    for artifact in usage_artifacts:
        _seal_runtime_output(artifact)
    usage_status = read_json(usage_status_path)
    usage_counts, usage_checks = _validate_usage_pairs(
        plan, usage_status, literal_count=counts["literal_count"]
    )
    if not all(usage_checks.values()):
        raise AcquisitionError(
            "runtime metadata usage pair validation failed: "
            + ", ".join(
                sorted(key for key, value in usage_checks.items() if not value)
            )
        )
    usage_value_status = read_json(usage_value_status_path)
    usage_value_counts, usage_value_checks = _validate_usage_values(
        plan, usage_value_status
    )
    if not all(usage_value_checks.values()):
        raise AcquisitionError(
            "runtime metadata usage value validation failed: "
            + ", ".join(
                sorted(
                    key for key, value in usage_value_checks.items() if not value
                )
            )
        )
    usage_member_status = read_json(usage_member_status_path)
    usage_member_counts, usage_member_checks = _validate_usage_members(
        plan, usage_member_status
    )
    if not all(usage_member_checks.values()):
        raise AcquisitionError(
            "runtime metadata usage member validation failed: "
            + ", ".join(
                sorted(
                    key for key, value in usage_member_checks.items()
                    if not value
                )
            )
        )
    usage_model_path = output_dir / "runtime-metadata-usage-pairs.private.json"
    usage_model = {
        "schema": RUNTIME_METADATA_USAGE_PAIR_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": {
            **plan["inputs"],
            "string_literal_inventory": file_identity(output_path),
        },
        "contracts": {"literal_count": counts["literal_count"]},
        "inventory": file_identity(usage_output_path),
        "status_receipt": file_identity(usage_status_path),
        "counts": usage_counts,
        "checks": usage_checks,
        "owner_only": True,
    }
    _private_json(usage_model_path, usage_model)
    usage_value_model_path = Path(plan["usage_value_model_path"])
    usage_value_model = {
        "schema": RUNTIME_METADATA_USAGE_VALUE_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": {
            **plan["inputs"],
            "metadata_usage_pair_inventory": file_identity(usage_output_path),
        },
        "inventory": file_identity(usage_value_output_path),
        "status_receipt": file_identity(usage_value_status_path),
        "counts": usage_value_counts,
        "checks": usage_value_checks,
        "owner_only": True,
    }
    _private_json(usage_value_model_path, usage_value_model)
    usage_member_model_path = Path(plan["usage_member_model_path"])
    usage_member_model = {
        "schema": RUNTIME_METADATA_USAGE_MEMBER_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": {
            **plan["inputs"],
            "metadata_usage_pair_inventory": file_identity(
                usage_output_path
            ),
        },
        "inventory": file_identity(usage_member_output_path),
        "status_receipt": file_identity(usage_member_status_path),
        "counts": usage_member_counts,
        "checks": usage_member_checks,
        "owner_only": True,
    }
    _private_json(usage_member_model_path, usage_member_model)
    model = {
        "schema": RUNTIME_STRING_LITERAL_SCHEMA,
        "status": "runtime-validated",
        "target": {"executable_sha256": plan["target"]["executable_sha256"]},
        "inputs": plan["inputs"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "metadata_usage_pair_model": file_identity(usage_model_path),
        "metadata_usage_pair_inventory": file_identity(usage_output_path),
        "metadata_usage_value_model": file_identity(usage_value_model_path),
        "metadata_usage_value_inventory": file_identity(usage_value_output_path),
        "metadata_usage_member_model": file_identity(usage_member_model_path),
        "metadata_usage_member_inventory": file_identity(
            usage_member_output_path
        ),
        "counts": counts,
        "checks": checks,
        "owner_only": True,
    }
    _private_json(Path(plan["model_path"]), model)
    return {
        "schema": RUNTIME_STRING_LITERAL_SCHEMA,
        "status": "runtime-validated",
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "inventory": model["inventory"],
        "metadata_usage_pairs": {
            "model": model["metadata_usage_pair_model"],
            "inventory": model["metadata_usage_pair_inventory"],
            "counts": usage_counts,
            "checks": usage_checks,
        },
        "metadata_usage_values": {
            "model": model["metadata_usage_value_model"],
            "inventory": model["metadata_usage_value_inventory"],
            "counts": usage_value_counts,
            "checks": usage_value_checks,
        },
        "metadata_usage_members": {
            "model": model["metadata_usage_member_model"],
            "inventory": model["metadata_usage_member_inventory"],
            "counts": usage_member_counts,
            "checks": usage_member_checks,
        },
    }


from pathlib import Path
import struct

from alpha.h01 import AcquisitionError
from alpha.c07 import _load_members
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_HEADER as H, RUNTIME_NATIVE_MEMBER_DETAIL_FIELD as F, RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY as P


def ordered_nominal_field_seeds(*, fields, members, details, base_descriptors, candidate, attributes, read):
    from alpha.p28 import bound_decoder
    if not fields or len(fields) != len(members) or len(fields) != len(details):
        raise AcquisitionError("nominal field reference domain is empty or incomplete")
    offset, width = attributes.get("descriptor_attribute_offset"), attributes.get("descriptor_attribute_bytes")
    if type(offset) is not int or type(width) is not int or not 0 <= offset < offset + width <= 16:
        raise AcquisitionError("nominal field reference attribute load exceeds observed prefix")
    seeds, expected, pointers, descriptors, cursors = [], {}, set(), set(), {}


    decode_row = bound_decoder(candidate)
    slot_packers = {}


    prefixes = {}
    pointers_add = pointers.add
    descriptors_add = descriptors.add
    for row, member, detail in zip(fields, members, details):
        key = (member.definition_index, member.member_index, member.pointer)
        if (type(row.get("type_index")) is not int or type(row.get("field_ordinal")) is not int
                or type(row.get("field_metadata_pointer")) is not int or type(row.get("descriptor")) is not int
                or type(row.get("reflection_descriptor")) is not int or type(row.get("reflection_attributes")) is not int
                or member.kind != 0 or member.pointer in pointers or not member.pointer or member.pointer & 7
                or member.member_index != cursors.get(member.definition_index, 0)
                or len(detail) != 10 or key != detail[:3]
                or (row.get("type_index"), row.get("field_ordinal"), row.get("field_metadata_pointer")) != key
                or row.get("reflection_descriptor") != detail[3] or row.get("reflection_attributes") != detail[5]):
            raise AcquisitionError("nominal field reference source identity/order differs")
        slots = member.slots
        packer = slot_packers.get(len(slots))
        if packer is None:
            packer = slot_packers[len(slots)] = struct.Struct(f"<{len(slots)}Q")
        raw = packer.pack(*slots)
        if read(member.pointer, len(raw)) != raw:
            raise AcquisitionError("nominal field reference native bytes differ")
        descriptor = decode_row(raw)
        if row.get("descriptor") != descriptor:
            raise AcquisitionError("nominal field reference descriptor does not replay")
        prefix = prefixes.get(descriptor)
        if prefix is None:
            prefix = prefixes[descriptor] = read(descriptor, 16)
        reflected = prefixes.get(detail[3])
        if reflected is None:
            reflected = prefixes[detail[3]] = read(detail[3], 16)
        if (not isinstance(prefix, bytes) or len(prefix) != 16
                or not isinstance(reflected, bytes) or len(reflected) != 16):
            raise AcquisitionError("nominal field reference descriptor prefix is absent")
        if int.from_bytes(prefix[offset:offset + width], "little") != detail[5]:
            raise AcquisitionError("nominal field reference native attributes differ")
        for pointer, value in ((member.pointer, raw), (descriptor, prefix), (detail[3], reflected)):
            if pointer in expected and expected[pointer] != value:
                raise AcquisitionError("nominal field reference observations disagree")
            expected[pointer] = value
        if descriptor not in base_descriptors and descriptor not in descriptors:
            seeds.append(descriptor)
        pointers_add(member.pointer); descriptors_add(descriptor)
        cursors[member.definition_index] = member.member_index + 1
    return seeds, expected


def replay_nominal_field_domain(*, model, inputs, identity, type_count, base_descriptors, candidate, attributes, read):
    domains, _ = _load_members(Path(inputs["native_member_inventory"]["path"]),
        executable_sha256=identity["executable_sha256"], expected_identity=inputs["native_member_inventory"],
        type_count=type_count)
    raw = Path(inputs["member_detail_inventory"]["path"]).read_bytes()
    if len(raw) < H.size:
        raise AcquisitionError("nominal field reference detail header is truncated")
    h = H.unpack_from(raw)
    if (h[:7] != (b"ALPHAND1", 1, H.size, F.size, P.size, len(domains[0]), len(domains[1]))
            or h[8:12] != (identity["image_base"], identity["image_bytes"], type_count, 0)
            or h[12:16] != (identity["executable_sha256"].encode(), *(inputs[key]["sha256"].encode() for key in
                ("native_member_inventory", "type_identity_inventory", "native_semantics")))
            or H.size + h[5] * F.size + h[6] * P.size + h[7] != len(raw)):
        raise AcquisitionError("nominal field reference detail source binding differs")
    return ordered_nominal_field_seeds(fields=model["nominal_fields"], members=domains[0],
        details=list(F.iter_unpack(raw[H.size:H.size + h[5]*F.size])), base_descriptors=base_descriptors,
        candidate=candidate, attributes=attributes, read=read)


from itertools import zip_longest

from alpha.h01 import AcquisitionError
from alpha.p25 import TYPE_REFERENCE_GENERIC, TYPE_REFERENCE_GENERIC_DEFINITION, TYPE_REFERENCE_SHAPE_MASK


def select_constructed_seeds(reference_rows, value_rows):
    rows={};descriptors=set();current_pointers=set()
    for reference,value in zip_longest(reference_rows,value_rows):
        if reference is None or value is None or len(reference)!=19 or len(value)!=4:
            raise AcquisitionError("constructed seed source domains differ")
        descriptor,current,data,bits=value
        shape=reference[4]
        if (any(type(v) is not int or not 0<=v<1<<64 for v in value)
                or descriptor!=reference[0] or not descriptor or descriptor&7 or descriptor in descriptors
                or not current or current&7 or current in current_pointers
                or type(shape) is not int or shape<0 or shape&~TYPE_REFERENCE_SHAPE_MASK
                or shape&TYPE_REFERENCE_GENERIC_DEFINITION and not shape&TYPE_REFERENCE_GENERIC):
            raise AcquisitionError("constructed seed observed descriptor/shape identity is invalid")
        descriptors.add(descriptor);current_pointers.add(current)
        if not shape&TYPE_REFERENCE_GENERIC or shape&TYPE_REFERENCE_GENERIC_DEFINITION:
            continue
        if data>>32:
            raise AcquisitionError("runtime constructed generic index is invalid")
        prior=rows.get(data)
        rows[data]=(descriptor,current,data,1) if prior is None else (*prior[:3],prior[3]+1)
    if not rows:
        raise AcquisitionError("runtime constructed generic domain is empty")
    return [rows[index] for index in sorted(rows)]


from pathlib import Path
import tempfile

from alpha.h01 import AcquisitionError
from alpha.p13 import RuntimeProcessProbe, _safe_path
from alpha.c03 import derive_extent_load
from alpha.c08 import load_bound_method_ancestry
from alpha.c09 import canonical
from alpha.c01 import bind_runtime_process, current_runtime_process_binding
from alpha.c04 import _verify_files
from alpha.p14 import read_current_runtime_ranges, load_runtime_range_observation, prepare_range_observation
from alpha.c04 import MappedPE
from alpha.p04 import derive_extent_candidates
from alpha.p16 import root_extent_memory_requests, replay_root_extent_observation
from alpha.h02 import canonical_json_bytes, write_new_json
from alpha.h02 import file_identity, read_json


_TARGET_KEYS=("process_id","creation_filetime","executable_path","executable_sha256","image_base_owner_only","image_bytes")


_DERIVE_CORE_MEMO: dict[str, Any] | None = None
_DERIVE_CORE_STAT_KEYS=("st_dev","st_ino","st_size","st_mtime_ns","st_ctime_ns")


def _derive_core_fingerprint(path):
    status=path.stat()


    return (status.st_dev,status.st_ino,*(getattr(status,key) for key in
        ("st_size","st_mtime_ns","st_ctime_ns")))


def _derive_core(binary, event_capture_plan, identity, selected, native, target):
    global _DERIVE_CORE_MEMO
    paths=(binary,event_capture_plan,
        *(Path(selected[key]["path"]) for key in
            ("method_detail_model","method_detail_inventory","ancestry_inventory")))
    key=tuple(_derive_core_fingerprint(path) for path in paths)+(
        canonical_json_bytes({name:identity.get(name) for name in sorted(identity)}),)
    memo=_DERIVE_CORE_MEMO
    if memo is not None and memo["key"]==key:
        rows=tuple(list(part) for part in memo["rows"])
        return rows,deepcopy(memo["sources"]),deepcopy(memo["operation"])
    (identities,methods,ancestry),sources=load_bound_method_ancestry(native=native,binary=binary,
        process_identity=target,**{key_:Path(selected[key_]["path"]) for key_ in
            ("method_detail_model","method_detail_inventory","ancestry_inventory")})
    with MappedPE(binary) as image:
        if image.size_of_image!=identity["image_bytes"]:
            raise AcquisitionError("extent operation executable image size differs")
        operation=derive_extent_candidates(identity_rows=identities,method_rows=methods,ancestry_rows=ancestry,
            image=image,image_base=identity["image_base"])
    if tuple(_derive_core_fingerprint(path) for path in paths)!=key[:-1]:
        return tuple(list(part) for part in (identities,methods,ancestry)),deepcopy(sources),deepcopy(operation)
    _DERIVE_CORE_MEMO={"key":key,"rows":(identities,methods,ancestry),"sources":sources,"operation":operation}
    return tuple(list(part) for part in (identities,methods,ancestry)),deepcopy(sources),deepcopy(operation)


def _derive(binary, event_capture_plan, identity):
    plan=read_json(event_capture_plan)
    selected=dict(plan["inputs"],event_capture_plan=file_identity(event_capture_plan),binary=file_identity(binary))
    _verify_files(selected)
    target=plan["target"]
    if (any(key not in target for key in _TARGET_KEYS)
            or any(type(identity.get("image_base" if key=="image_base_owner_only" else key)) is not type(value)
                or identity.get("image_base" if key=="image_base_owner_only" else key)!=value for key,value in target.items())
            or selected["binary"]["sha256"]!=identity.get("executable_sha256")):
        raise AcquisitionError("extent operation source process differs")
    native=dict(selected,type_count=plan["contract"]["type_count"],image_base=identity["image_base"],image_bytes=identity["image_bytes"])
    (identities,methods,ancestry),sources,operation=_derive_core(binary,event_capture_plan,identity,selected,native,target)
    selected.update(sources)
    with MappedPE(binary) as image:
        if image.size_of_image!=identity["image_bytes"]:
            raise AcquisitionError("extent operation executable image size differs")
    derive_extent_load(operation)
    _verify_files(selected)
    return operation,selected


def capture_extent_operation(*,binary,event_capture_plan,output_dir,wine,wineprefix,compiler=None):
    from alpha.p19 import _implementation_digest
    binary,event_capture_plan,output_dir=map(_safe_path,(binary,event_capture_plan,output_dir))
    if output_dir.exists():raise AcquisitionError("extent operation output already exists")
    implementation=_implementation_digest()

    with tempfile.TemporaryDirectory(prefix="alpha-extent-probe-") as temporary:
        probe=RuntimeProcessProbe(binary=binary,wine=wine,wineprefix=wineprefix,build_dir=Path(temporary).resolve(),compiler=compiler)
        identity=probe();operation,selected=_derive(binary,event_capture_plan,identity)
    if any(output_dir.is_relative_to(Path(record["path"]).parent) for record in selected.values()):
        raise AcquisitionError("extent operation output overlaps its sources")
    output_dir.mkdir(mode=0o700,parents=True)


    requests=root_extent_memory_requests(operation)
    with bind_runtime_process(identity),ThreadPoolExecutor(max_workers=1) as executor:
        prepared=executor.submit(prepare_range_observation,binary=binary,ranges=requests,
            output_dir=output_dir/"ranges",binding=current_runtime_process_binding(),compiler=compiler)
        probe=RuntimeProcessProbe(binary=binary,wine=wine,wineprefix=wineprefix,build_dir=output_dir/"probe",compiler=compiler)
        if probe()!=identity:
            raise AcquisitionError("extent operation process changed during preparation")
        observed=read_current_runtime_ranges(binary=binary,ranges=requests,
            output_dir=output_dir/"ranges",wine=wine,wineprefix=wineprefix,compiler=compiler,
            prepared=prepared.result())
    replay=replay_root_extent_observation(operation,observed)
    receipt_path=output_dir/"ranges/runtime-ranges.private.json"
    receipt=read_json(receipt_path)
    selected["observation"]=file_identity(receipt_path)
    selected.update({"observation_"+k:receipt[k] for k in ("plan","source","observer","inventory")})
    _verify_files(selected)
    if probe()!=identity or _implementation_digest()!=implementation:
        raise AcquisitionError("extent operation process or implementation changed")
    model=dict(schema="alpha.runtime-extent-operation/v1",status="runtime-observed",inputs=selected,
        identity=identity,operation=operation,load=derive_extent_load(operation),code_replay=replay,
        native_type_sizes_proven=False,metadata_complete=False)
    path=output_dir/"runtime-extent-operation.private.json"
    write_new_json(path,model)
    return path


def load_extent_operation(path, *, expected_target):
    path=_safe_path(Path(path));record=file_identity(path);model=read_json(path)
    identity=model.get("identity",{})
    if (model.get("schema")!="alpha.runtime-extent-operation/v1" or model.get("status")!="runtime-observed"
            or any(key not in expected_target for key in _TARGET_KEYS)
            or any(type(identity.get("image_base" if k=="image_base_owner_only" else k)) is not type(v)
                or identity.get("image_base" if k=="image_base_owner_only" else k)!=v for k,v in expected_target.items())):
        raise AcquisitionError("extent operation explicit identity/model differs")
    inputs=model["inputs"];_verify_files(dict(inputs,model=record))
    operation,derived_inputs=_derive(Path(inputs["binary"]["path"]),Path(inputs["event_capture_plan"]["path"]),identity)
    if any(inputs.get(k)!=v for k,v in derived_inputs.items()) or canonical(operation)!=canonical(model["operation"]):
        raise AcquisitionError("extent operation does not rederive from current source structure")
    receipt=read_json(Path(inputs["observation"]["path"]))
    if any(inputs.get("observation_"+key)!=receipt.get(key) or not receipt.get(key)
           for key in ("plan","source","observer","inventory")):
        raise AcquisitionError("extent operation observation dependency chain differs")
    view=load_runtime_range_observation(Path(inputs["observation"]["path"]),expected_identity=identity)
    replay=replay_root_extent_observation(operation,dict(zip(view.starts,view.payloads)))
    load=derive_extent_load(operation)
    if canonical(replay)!=canonical(model["code_replay"]) or canonical(load)!=canonical(model["load"]):
        raise AcquisitionError("extent operation code replay differs")
    _verify_files(dict(inputs,model=record))
    return operation,dict(inputs,model=record)


def bind_constructed_extent(model, *, source_records=None):
    record=model.get("extent_operation")
    if not isinstance(record,dict):
        raise AcquisitionError("constructed extent requires code provenance; heuristic receipts are not accepted")
    reference_record=model["inputs"]["type_reference_model"]
    _verify_files(dict(extent=record,reference=reference_record))
    refs=read_json(Path(reference_record["path"]))
    if (any(k not in model.get("target",{}) for k in ("process_id","executable_sha256"))
            or any(type(refs.get("target",{}).get(k)) is not type(v)
                or refs.get("target",{}).get(k)!=v for k,v in model["target"].items())):
        raise AcquisitionError("constructed extent reference target differs")
    operation,inputs=load_extent_operation(Path(record["path"]),expected_target=refs["target"])
    for key in ("type_identity_inventory","method_detail_inventory"):
        if inputs.get(key)!=refs["inputs"].get(key):
            raise AcquisitionError("constructed extent nominal source domain differs")
    candidate=derive_extent_load(operation)["candidate"]
    offset,width=candidate["class_extent_offset"],candidate["class_extent_width"]
    if (model.get("checks",{}).get("class_extent_load_code_derived") is not True
            or type(model.get("counts",{}).get("instance_size_byte_offset")) is not int
            or model["counts"]["instance_size_byte_offset"]!=offset
            or type(model["counts"].get("instance_size_width_bytes")) is not int
            or model["counts"]["instance_size_width_bytes"]!=width):
        raise AcquisitionError("constructed extent summary differs from current-code load")
    _verify_files(dict(inputs,reference=reference_record))
    if source_records is not None:
        source_records.update(dict(inputs,reference=reference_record))
    return offset,width


from copy import deepcopy
from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.c04 import _verify_files
from alpha.c05 import load_reference_names
from alpha.h02 import write_new_bytes, write_new_json
from alpha.p25 import _reference_snapshot
from alpha.h02 import file_identity, read_json


def preserve_observed_reference_domain(*, source, current_inputs, output):
    scope = source.get("native_field_domain_scope", "constructed")
    if (scope not in ("constructed", "nominal-and-constructed")
            or (scope == "nominal-and-constructed" and (
                type(source.get("nominal_field_count")) is not int or source["nominal_field_count"] <= 0
                or source.get("all_selected_field_descriptors_already_in_base") is not True))):
        raise AcquisitionError("zero-increment nominal field domain is unproven")
    if (source.get("seed_descriptors") != []
            or source.get("all_constructed_field_descriptors_already_in_base") is not True
            or type(source.get("constructed_field_count")) is not int or source["constructed_field_count"] <= 0
            or not source.get("expected_current_bytes")
            or "current_field_bytes" not in current_inputs or "field_capture" not in current_inputs):
        raise AcquisitionError("zero-increment field domain requires complete current native evidence")
    selected = dict(current_inputs, base_model=source["base_type_reference_model"], base_inventory=source["base_type_reference_inventory"])
    _verify_files(selected)
    base = read_json(Path(source["base_type_reference_model"]["path"]))
    if (base.get("target") != source["target"] or base.get("status") != "runtime-validated"
            or base.get("inventory") != source["base_type_reference_inventory"]
            or not base.get("checks") or any(value is not True for value in base["checks"].values())):
        raise AcquisitionError("zero-increment field base graph is not validated/current")
    identity = dict(source["target"], image_base=source["target"]["image_base_owner_only"])
    load_reference_names(model=base.get("raw_names"), expected_identity=identity,
                         expected_inventory=base["inventory"])
    raw = Path(base["inventory"]["path"]).read_bytes()
    header, _, _ = _reference_snapshot(raw, label="zero-increment field base")
    if header[5] != source["base_type_reference_node_count"]:
        raise AcquisitionError("zero-increment field base count differs")
    if any(output.resolve().is_relative_to(Path(record["path"]).parent) for record in selected.values()):
        raise AcquisitionError("zero-increment field output must preserve all sources")
    path = output / "runtime-type-reference.private.bin"
    write_new_bytes(path, raw)
    model = deepcopy(base)
    model["inventory"] = file_identity(path)
    if any(model["inventory"][key] != base["inventory"][key] for key in ("sha256", "bytes")):
        raise AcquisitionError("zero-increment field copy changed graph bytes")
    model["raw_names"]["output"] = model["inventory"]
    model["inputs"].update({"field_closure_" + key: value for key, value in selected.items()})
    model["checks"]["observed_constructed_field_descriptors_already_in_graph"] = True
    model["field_reference_fixed_point_observed"] = True
    model["fresh_type_reference_capture_performed"] = False
    model["native_field_domain_scope"] = scope
    model["all_native_fields_fixed_point_observed"] = scope == "nominal-and-constructed"
    model["metadata_complete"] = False
    _verify_files(selected)
    model_path = output / "runtime-type-reference.private.json"
    write_new_json(model_path, model)
    return {"status": "field-domain-closed", "inventory": model["inventory"],
            "model": file_identity(model_path), "node_count": header[5],
            "fresh_type_reference_capture_performed": False, "metadata_complete": False}


from alpha.h01 import AcquisitionError
from alpha.p25 import TYPE_REFERENCE_GENERIC as GENERIC, TYPE_REFERENCE_GENERIC_DEFINITION as DEFINITION, TYPE_REFERENCE_ARRAY as ARRAY, TYPE_REFERENCE_BYREF as BYREF, TYPE_REFERENCE_POINTER as POINTER

SCALARS = ("attributes", "shape", "rank")
RELATIONS = ("base", "declaring", "element", "generic_definition")


def bind_original_names(order, entries):
    if not order or len(set(order))!=len(order) or len(entries)!=2*len(order):
        raise AcquisitionError("field alias original-name domain is incomplete")
    rows={}
    for entry in entries:
        domain=entry.domain
        key=(domain,entry.index)
        if (key in rows or domain not in ("type_reference","type_reference_namespace")
                or type(entry.index) is not int or not 0<=entry.index<len(order)
                or entry.value is not None and not isinstance(entry.value,bytes)):
            raise AcquisitionError("field alias original-name identity differs")
        rows[key]=entry.value
    return {pointer:(rows["type_reference",index],rows["type_reference_namespace",index])
            for index,pointer in enumerate(order)}


def compare_alias_pair(nodes, left, right, *, raw_names=None, verified=None):


    pending = [(left,right)]; seen = set(); core = {}; anchored = 0
    nodes_get = nodes.get
    while pending:
        pair = pending.pop()
        if pair in seen: continue
        if verified is not None and pair in verified: continue
        if pair == (0,0): continue
        if len(seen) >= 1 << 20:
            raise AcquisitionError("field type alias graph exceeded bounded pair analysis")
        a = nodes_get(pair[0]); b = nodes_get(pair[1])
        if a is None or b is None:
            raise AcquisitionError("field type alias relation is absent")
        if (a["attributes"] != b["attributes"] or a["shape"] != b["shape"]
                or a["rank"] != b["rank"]):
            raise AcquisitionError("field type alias scalar metadata differs")
        if raw_names is None:
            same_names=all(a.get(key)==b.get(key) for key in ("name","namespace"))
        else:
            if pair[0] not in raw_names or pair[1] not in raw_names:
                raise AcquisitionError("field type alias original name is absent")
            same_names=pair[0] == pair[1] or raw_names[pair[0]]==raw_names[pair[1]]
        if not same_names:
            raise AcquisitionError("field type alias original names differ")
        shape = a["shape"]
        anchor = (bool(a["canonical"]) and a["canonical"] == b["canonical"]
                  or bool(a["type_object"]) and a["type_object"] == b["type_object"])
        composite = bool(shape & (ARRAY | BYREF | POINTER)) or bool(shape & GENERIC and not shape & DEFINITION)
        if not anchor and not composite:
            raise AcquisitionError("field type alias atomic identity is unproven")
        anchored += bool(anchor)
        edges = [(a[key],b[key]) for key in RELATIONS]
        for key in ("interfaces", "arguments"):
            if len(a[key]) != len(b[key]):
                raise AcquisitionError("field type alias ordered relation count differs")
            edges.extend(zip(a[key],b[key]))


        if (a["canonical"],b["canonical"]) != pair:
            edges.append((a["canonical"],b["canonical"]))
        if shape & (ARRAY | BYREF | POINTER):
            if not a["element"] or not b["element"]:
                raise AcquisitionError("field type alias composite element is absent")
            core[pair] = [(a["element"],b["element"])]
        elif shape & GENERIC and not shape & DEFINITION:
            if not a["generic_definition"] or not b["generic_definition"] or not a["arguments"]:
                raise AcquisitionError("field type alias generic constructor is absent")
            core[pair] = [(a["generic_definition"],b["generic_definition"]), *zip(a["arguments"],b["arguments"])]
        else: core[pair] = []
        seen.add(pair); pending.extend(edges)


    done = set()
    for root in core:
        active = set(); stack = [(root,False)]
        while stack:
            pair, finish = stack.pop()
            if finish:
                active.remove(pair); done.add(pair); continue
            if pair in done: continue
            if pair in active:
                raise AcquisitionError("field type alias has cyclic composite construction")
            active.add(pair); stack.append((pair,True))
            stack.extend((child,False) for child in core.get(pair,[]))
    if verified is not None:


        verified |= seen
    return dict(observed_pair_count=len(seen), identity_anchored_pair_count=anchored,
        native_type_grammar_proven=False, native_layout_complete=False, metadata_complete=False)


def compare_nominal_aliases(fields, nodes, *, raw_names=None):
    if not fields or not nodes:
        raise AcquisitionError("nominal field alias domain is empty")
    pointers = set(); counts = {}; failures = []; passed = 0
    pointers_add = pointers.add
    counts_get = counts.get
    for row in fields:
        pointer = row["field_metadata_pointer"]
        if pointer in pointers: raise AcquisitionError("nominal field alias domain repeats a field")
        pointers_add(pointer)
        pair = (row["descriptor"],row["reflection_descriptor"])
        counts[pair] = counts_get(pair,0) + 1


    verified = set()
    for pair,count in counts.items():
        try: compare_alias_pair(nodes,*pair,raw_names=raw_names,verified=verified)
        except AcquisitionError as error:
            failures.append(dict(descriptor=pair[0],reflection_descriptor=pair[1],field_count=count,reason=str(error)))
        else: passed += count
    return dict(field_count=len(fields), distinct_alias_pair_count=len(counts), matched_field_count=passed,
        unmatched_field_count=len(fields)-passed, unmatched_alias_pair_count=len(failures),
        representative_failures=failures[:32], all_nominal_field_aliases_agree=passed==len(fields),
        equal_names_used_as_atomic_identity=False, native_type_grammar_proven=False,
        original_name_bytes_compared=raw_names is not None,
        native_layout_complete=False, metadata_complete=False)


import struct

from alpha.h01 import ContractViolation
from alpha.p25 import TYPE_REFERENCE_GENERIC, TYPE_REFERENCE_GENERIC_DEFINITION


def observed_generic_parts(renderer, row):
    if not row[4] & TYPE_REFERENCE_GENERIC:
        raise ContractViolation("observed generic projection requires a generic TypeRef")
    index = renderer.node_by_descriptor.get(row[14])
    if index is None:
        raise ContractViolation("observed generic definition is absent")
    definition = renderer.reference_row(index)
    root = renderer._root_alias(row[14], definition[1])
    if (root is None or not definition[4] & TYPE_REFERENCE_GENERIC_DEFINITION
            or row[8] <= 0 or definition[8] != row[8]
            or renderer.graph_row(root)[7] != row[8]):
        raise ContractViolation("observed generic definition/argument arity is inconsistent")
    start = renderer.reference_argument_start + row[16] * 8
    end = start + row[8] * 8
    if start < renderer.reference_argument_start or end > renderer.reference_argument_start + renderer.argument_count * 8:
        raise ContractViolation("observed generic arguments are out of range")
    arguments = tuple(value[0] for value in struct.iter_unpack("<Q", renderer.references[start:end]))
    if any(value not in renderer.node_by_descriptor for value in arguments):
        raise ContractViolation("observed generic argument is absent from TypeRefs")
    return root, arguments


def observed_generic_name(renderer, row, visit):
    root, arguments = observed_generic_parts(renderer, row)
    return renderer.constructed_root_name(root, [visit(value) for value in arguments])
