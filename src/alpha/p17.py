from alpha.h02 import windows_run as _host_run

import json
import os
import struct
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any

from alpha.p12 import (
    _compiler,
    _owner_directory,
    _private_json,
    _private_text,
    _seal_runtime_output,
    _wide_literal,
    _windows_z_path,
    cached_windows_build,
    runtime_injector_source,
)
from alpha.h01 import AcquisitionError
from alpha.p14 import REFLECTION_BOOTSTRAP_SCHEMA
from alpha.p15 import RUNTIME_CLASS_SCHEMA
from alpha.p16 import RUNTIME_NATIVE_HELPER_SCHEMA
from alpha.p16 import RUNTIME_TYPE_MATERIALIZER_SCHEMA
from alpha.h02 import file_identity, read_json


RUNTIME_TYPE_MATERIALIZER_PLAN_SCHEMA = (
    "alpha.runtime-type-materializer-validation-plan/v1"
)
RUNTIME_TYPE_MATERIALIZER_VALIDATION_SCHEMA = (
    "alpha.runtime-type-materializer-validation/v1"
)
_TYPE_MAP_MAGIC = b"ALPHATM1"
_TYPE_MAP_VERSION = 1
_TYPE_MAP_HEADER = struct.Struct("<8sIIQQ64s64s")
_TYPE_MAP_RECORD = struct.Struct("<IIQQQ")
_NATIVE_INVENTORY_MAGIC = b"ALPHANI1"
_NATIVE_INVENTORY_VERSION = 1
_NATIVE_INVENTORY_HEADER = struct.Struct(
    "<8sIIIIQQQ64s64sIIIIIIII"
)
_NATIVE_TYPE_RECORD = struct.Struct("<IIQQQQQIIQQ")
_NATIVE_METHOD_RECORD = struct.Struct("<IIQQ")
_NATIVE_MEMBER_MAGIC = b"ALPHANM1"
_NATIVE_MEMBER_VERSION = 1
_NATIVE_MEMBER_HEADER = struct.Struct(
    "<8sIIIIQQQQ64s64s64sQIIQIIQII"
)
_NATIVE_MEMBER_RECORD = struct.Struct("<IIQII48s")


def _c_string_literal(value: str) -> str:
    escaped = (
        value.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
    )
    return f'"{escaped}"'


def _load_bound_inputs(
    *,
    binary: Path,
    bootstrap_model: Path,
    class_model: Path,
    materializer_model: Path,
    native_helper_model: Path,
    preloaded_materializer: dict[str, Any] | None = None,
) -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    identity = file_identity(binary)
    bootstrap_identity = file_identity(bootstrap_model)
    class_identity = file_identity(class_model)
    bootstrap = read_json(bootstrap_model)
    classes = read_json(class_model)
    materializer = read_json(materializer_model)
    if preloaded_materializer is not None:


        materializer = preloaded_materializer
    native_helpers = read_json(native_helper_model)
    if (
        not isinstance(bootstrap, dict)
        or bootstrap.get("schema") != REFLECTION_BOOTSTRAP_SCHEMA
    ):
        raise AcquisitionError("runtime type materializer bootstrap is invalid")
    if not isinstance(classes, dict) or classes.get("schema") != RUNTIME_CLASS_SCHEMA:
        raise AcquisitionError("runtime type materializer class model is invalid")
    if (
        not isinstance(materializer, dict)
        or materializer.get("schema") != RUNTIME_TYPE_MATERIALIZER_SCHEMA
    ):
        raise AcquisitionError("runtime type materializer model is invalid")
    if (
        not isinstance(native_helpers, dict)
        or native_helpers.get("schema") != RUNTIME_NATIVE_HELPER_SCHEMA
        or native_helpers.get("binary", {}).get("sha256") != identity["sha256"]
        or native_helpers.get("checks", {}).get(
            "class_method_iterator_runtime_validated"
        )
        is not True
    ):
        raise AcquisitionError("runtime type materializer native helper is invalid")
    checks = materializer.get("checks")
    required_checks = (
        "binary_identity_bound",
        "snapshot_identity_bound",
        "bootstrap_identity_bound",
        "class_model_identity_bound",
        "type_resolver_function_bound",
        "unique_external_tail_materializer_derived",
        "embedded_descriptor_field_semantically_unique",
        "class_name_field_semantically_unique",
        "owner_static_descriptors_exact",
        "definition_flag_families_derived",
        "type_definition_indexes_contiguous",
        "primitive_descriptor_holes_uniquely_completed",
    )
    if (
        materializer.get("binary", {}).get("sha256") != identity["sha256"]
        or materializer.get("binary", {}).get("bytes") != identity["bytes"]
        or materializer.get("inputs", {}).get("bootstrap_model_sha256")
        != bootstrap_identity["sha256"]
        or materializer.get("inputs", {}).get("class_model_sha256")
        != class_identity["sha256"]
        or not isinstance(checks, dict)
        or any(checks.get(key) is not True for key in required_checks)
    ):
        raise AcquisitionError("runtime type materializer model binding is stale")
    if (
        bootstrap.get("binary", {}).get("sha256") != identity["sha256"]
        or classes.get("bootstrap_model_sha256")
        != bootstrap_identity["sha256"]
    ):
        raise AcquisitionError("runtime type materializer source inputs are stale")
    return identity, bootstrap, classes, materializer, native_helpers


def _owner_rows(materializer: dict[str, Any]) -> tuple[str, int]:
    observations = materializer.get("owner_validation_contract")
    definitions = materializer.get("type_definitions")
    if not isinstance(observations, list) or not observations:
        raise AcquisitionError("runtime type materializer owner contract is empty")
    if not isinstance(definitions, list) or not definitions:
        raise AcquisitionError("runtime type materializer definition domain is empty")
    rows: list[str] = []
    owners: set[tuple[str, str]] = set()
    indexes: set[int] = set()
    for observation in observations:
        if not isinstance(observation, dict):
            raise AcquisitionError("runtime type materializer owner row is invalid")
        owner = observation.get("runtime_owner")
        index = observation.get("definition_index")
        flags = observation.get("type_flags")
        descriptor_rva = observation.get("static_descriptor_rva")
        if (
            not isinstance(owner, str)
            or "." not in owner
            or not isinstance(index, int)
            or not 0 <= index < len(definitions)
            or not isinstance(flags, int)
            or flags <= 0
            or not isinstance(descriptor_rva, int)
            or descriptor_rva <= 0
        ):
            raise AcquisitionError("runtime type materializer owner row is invalid")
        namespace_name, type_name = owner.rsplit(".", 1)
        identity = (namespace_name, type_name)
        definition = definitions[index]
        if (
            identity in owners
            or index in indexes
            or not isinstance(definition, dict)
            or definition.get("type_definition_index") != index
            or definition.get("type_flags") != flags
            or definition.get("descriptor_rva") != descriptor_rva
        ):
            raise AcquisitionError(
                "runtime type materializer owner descriptor binding is stale"
            )
        owners.add(identity)
        indexes.add(index)
        rows.append(
            "    {"
            + ", ".join(
                (
                    _c_string_literal(namespace_name),
                    _c_string_literal(type_name),
                    f"{index}u",
                    f"{flags}ull",
                    f"{descriptor_rva}ull",
                )
            )
            + "}"
        )
    return ",\n".join(rows), len(rows)


def _definition_rows(materializer: dict[str, Any]) -> tuple[str, int]:
    definitions = materializer.get("type_definitions")
    if not isinstance(definitions, list) or not definitions:
        raise AcquisitionError("runtime type materializer definition domain is empty")
    rows: list[str] = []
    for expected_index, definition in enumerate(definitions):
        if not isinstance(definition, dict):
            raise AcquisitionError("runtime type materializer definition row is invalid")
        index = definition.get("type_definition_index")
        flags = definition.get("type_flags")
        descriptor_rva = definition.get("descriptor_rva")
        if (
            index != expected_index
            or not isinstance(flags, int)
            or flags <= 0
            or not isinstance(descriptor_rva, int)
            or descriptor_rva <= 0
        ):
            raise AcquisitionError("runtime type materializer definition row is invalid")
        rows.append(f"    {{{flags}ull, {descriptor_rva}ull}}")
    return ",\n".join(rows), len(rows)


def _inspect_materialized_type_map(
    *,
    path: Path,
    plan: dict[str, Any],
    materializer: dict[str, Any],
) -> dict[str, bool]:
    if not path.is_file() or path.is_symlink():
        return {"type_map_present": False}
    expected_count = plan.get("contract", {}).get("type_definition_count")
    expected_size = (
        _TYPE_MAP_HEADER.size
        + expected_count * _TYPE_MAP_RECORD.size
        if isinstance(expected_count, int) and expected_count > 0
        else -1
    )
    if path.stat().st_size != expected_size:
        return {
            "type_map_present": True,
            "type_map_size_exact": False,
        }
    raw = path.read_bytes()
    (
        magic,
        version,
        record_bytes,
        record_count,
        image_bytes,
        executable_hash_raw,
        model_hash_raw,
    ) = _TYPE_MAP_HEADER.unpack_from(raw, 0)
    try:
        executable_hash = executable_hash_raw.decode("ascii")
        model_hash = model_hash_raw.decode("ascii")
    except UnicodeDecodeError:
        executable_hash = ""
        model_hash = ""
    definitions = materializer.get("type_definitions")
    rows_valid = isinstance(definitions, list) and len(definitions) == record_count
    pointers: set[int] = set()
    if rows_valid:
        region_end = _TYPE_MAP_HEADER.size + record_count * _TYPE_MAP_RECORD.size
        if region_end > len(raw):
            rows_valid = False
        else:
            consumed = 0
            for row in _TYPE_MAP_RECORD.iter_unpack(raw[_TYPE_MAP_HEADER.size : region_end]):
                definition = definitions[consumed]
                consumed += 1
                (
                    observed_index,
                    reserved,
                    flags,
                    descriptor_rva,
                    class_pointer,
                ) = row
                if (
                    not isinstance(definition, dict)
                    or observed_index != consumed - 1
                    or reserved
                    or flags != definition.get("type_flags")
                    or descriptor_rva != definition.get("descriptor_rva")
                    or not class_pointer
                ):
                    rows_valid = False
                    break
                pointers.add(class_pointer)
            if rows_valid and consumed != len(definitions):
                rows_valid = False
    return {
        "type_map_present": True,
        "type_map_size_exact": True,
        "type_map_magic": magic == _TYPE_MAP_MAGIC,
        "type_map_version": version == _TYPE_MAP_VERSION,
        "type_map_record_size": record_bytes == _TYPE_MAP_RECORD.size,
        "type_map_record_count": record_count == expected_count,
        "type_map_image_size": image_bytes
        == materializer.get("binary", {}).get("size_of_image"),
        "type_map_executable_hash": executable_hash
        == plan.get("target", {}).get("executable_sha256"),
        "type_map_model_hash": model_hash
        == plan.get("inputs", {}).get("materializer_model_sha256"),
        "type_map_rows_bound": rows_valid,
        "type_map_class_pointers_unique": rows_valid
        and len(pointers) == record_count,
    }


def _inspect_native_inventory(
    *,
    path: Path,
    plan: dict[str, Any],
    materializer: dict[str, Any],
) -> dict[str, bool]:
    if not path.is_file() or path.is_symlink():
        return {"native_inventory_present": False}
    raw = path.read_bytes()
    if len(raw) < _NATIVE_INVENTORY_HEADER.size:
        return {
            "native_inventory_present": True,
            "native_inventory_header_complete": False,
        }
    values = _NATIVE_INVENTORY_HEADER.unpack_from(raw, 0)
    (
        magic,
        version,
        type_record_bytes,
        method_record_bytes,
        reserved,
        type_count,
        method_count,
        image_bytes,
        executable_hash_raw,
        model_hash_raw,
        class_name_qword,
        parent_qword,
        class_declaring_qword,
        method_array_qword,
        method_count_offset,
        method_declaring_qword,
        method_pointer_qword,
        reserved_layout,
    ) = values
    try:
        executable_hash = executable_hash_raw.decode("ascii")
        model_hash = model_hash_raw.decode("ascii")
    except UnicodeDecodeError:
        executable_hash = ""
        model_hash = ""
    expected_count = plan.get("contract", {}).get("type_definition_count")
    definitions = materializer.get("type_definitions")
    type_start = _NATIVE_INVENTORY_HEADER.size
    method_start = type_start + type_count * _NATIVE_TYPE_RECORD.size
    names_start = method_start + method_count * _NATIVE_METHOD_RECORD.size
    shape_valid = (
        magic == _NATIVE_INVENTORY_MAGIC
        and version == _NATIVE_INVENTORY_VERSION
        and type_record_bytes == _NATIVE_TYPE_RECORD.size
        and method_record_bytes == _NATIVE_METHOD_RECORD.size
        and reserved == 0
        and reserved_layout == 0
        and type_count == expected_count
        and isinstance(definitions, list)
        and len(definitions) == type_count
        and names_start <= len(raw)
    )
    type_rows_valid = shape_valid
    class_pointers: set[int] = set()
    name_end = names_start
    expected_method_start = 0
    type_method_counts: list[int] = []
    if type_rows_valid:
        type_region_end = type_start + type_count * _NATIVE_TYPE_RECORD.size
        if type_region_end > len(raw):
            type_rows_valid = False
        else:
            consumed = 0
            for row in _NATIVE_TYPE_RECORD.iter_unpack(raw[type_start:type_region_end]):
                definition = definitions[consumed]
                consumed += 1
                (
                    observed_index,
                    name_bytes,
                    flags,
                    descriptor_rva,
                    class_pointer,
                    _parent_pointer,
                    _declaring_pointer,
                    observed_method_count,
                    row_reserved,
                    observed_method_start,
                    name_offset,
                ) = row
                if (
                    not isinstance(definition, dict)
                    or observed_index != consumed - 1
                    or not 0 <= name_bytes <= 4096
                    or flags != definition.get("type_flags")
                    or descriptor_rva != definition.get("descriptor_rva")
                    or not class_pointer
                    or row_reserved
                    or observed_method_start != expected_method_start
                    or name_offset < names_start
                    or name_offset + name_bytes > len(raw)
                ):
                    type_rows_valid = False
                    break
                name = raw[name_offset : name_offset + name_bytes]
                try:
                    decoded_name = name.decode("utf-8")
                except UnicodeDecodeError:
                    decoded_name = ""
                if (name and not decoded_name) or b"\0" in name or name_offset != name_end:
                    type_rows_valid = False
                    break
                class_pointers.add(class_pointer)
                type_method_counts.append(observed_method_count)
                expected_method_start += observed_method_count
                name_end += name_bytes
            if type_rows_valid and consumed != len(definitions):
                type_rows_valid = False
    method_rows_valid = bool(
        type_rows_valid
        and expected_method_start == method_count
        and name_end == len(raw)
    )
    metadata_pointers: set[int] = set()
    if method_rows_valid:
        method_region_end = method_start + method_count * _NATIVE_METHOD_RECORD.size
        if method_region_end > len(raw):
            method_rows_valid = False
        else:


            method_type_total = len(type_method_counts)
            expected_type = 0
            expected_method = 0
            type_method_total = (
                type_method_counts[0] if method_type_total else -1
            )
            for observed in _NATIVE_METHOD_RECORD.iter_unpack(
                raw[method_start:method_region_end]
            ):
                if expected_method == type_method_total:
                    while (
                        expected_type < method_type_total
                        and expected_method == type_method_counts[expected_type]
                    ):
                        expected_type += 1
                        expected_method = 0
                    type_method_total = (
                        type_method_counts[expected_type]
                        if expected_type < method_type_total
                        else -1
                    )
                if expected_type >= method_type_total or (
                    observed[0] != expected_type
                    or observed[1] != expected_method
                    or not observed[2]
                ):
                    method_rows_valid = False
                    break
                metadata_pointers.add(observed[2])
                expected_method += 1
            if method_rows_valid:
                while (
                    expected_type < method_type_total
                    and expected_method == type_method_counts[expected_type]
                ):
                    expected_type += 1
                    expected_method = 0
                if expected_type != method_type_total:
                    method_rows_valid = False
    layout = materializer.get("inventory_layout", {})
    return {
        "native_inventory_present": True,
        "native_inventory_header_complete": len(raw)
        >= _NATIVE_INVENTORY_HEADER.size,
        "native_inventory_magic": magic == _NATIVE_INVENTORY_MAGIC,
        "native_inventory_version": version == _NATIVE_INVENTORY_VERSION,
        "native_inventory_record_sizes": type_record_bytes
        == _NATIVE_TYPE_RECORD.size
        and method_record_bytes == _NATIVE_METHOD_RECORD.size,
        "native_inventory_reserved_zero": reserved == 0 and reserved_layout == 0,
        "native_inventory_type_count": type_count == expected_count,
        "native_inventory_image_size": image_bytes
        == materializer.get("binary", {}).get("size_of_image"),
        "native_inventory_executable_hash": executable_hash
        == plan.get("target", {}).get("executable_sha256"),
        "native_inventory_model_hash": model_hash
        == plan.get("inputs", {}).get("materializer_model_sha256"),
        "native_inventory_layout_bound": isinstance(layout, dict)
        and class_name_qword == layout.get("class_name_pointer_qword")
        and parent_qword == layout.get("parent_class_qword")
        and class_declaring_qword == layout.get("class_declaring_qword")
        and method_array_qword == layout.get("method_array_pointer_qword")
        and method_count_offset == layout.get("method_count_byte_offset")
        and method_declaring_qword == layout.get("method_declaring_class_qword")
        and method_pointer_qword == layout.get("method_pointer_qword"),
        "native_inventory_type_rows_bound": type_rows_valid,
        "native_inventory_method_rows_bound": method_rows_valid,
        "native_inventory_class_pointers_unique": type_rows_valid
        and len(class_pointers) == type_count,
        "native_inventory_method_metadata_pointers_unique": method_rows_valid
        and len(metadata_pointers) == method_count,
    }


def _inspect_native_member_inventory(
    *,
    path: Path,
    plan: dict[str, Any],
    materializer: dict[str, Any],
) -> dict[str, bool]:
    if not path.is_file() or path.is_symlink():
        return {"native_member_inventory_present": False}
    raw = path.read_bytes()
    if len(raw) < _NATIVE_MEMBER_HEADER.size:
        return {
            "native_member_inventory_present": True,
            "native_member_inventory_header_complete": False,
        }
    values = _NATIVE_MEMBER_HEADER.unpack_from(raw, 0)
    (
        magic,
        version,
        record_bytes,
        type_count,
        reserved,
        field_count,
        property_count,
        event_count,
        image_bytes,
        executable_hash_raw,
        materializer_hash_raw,
        helper_hash_raw,
        field_rva,
        field_array_offset,
        field_stride,
        property_rva,
        property_array_offset,
        property_stride,
        event_rva,
        event_array_offset,
        event_stride,
    ) = values
    try:
        executable_hash = executable_hash_raw.decode("ascii")
        materializer_hash = materializer_hash_raw.decode("ascii")
        helper_hash = helper_hash_raw.decode("ascii")
    except UnicodeDecodeError:
        executable_hash = materializer_hash = helper_hash = ""
    total = field_count + property_count + event_count
    expected_size = _NATIVE_MEMBER_HEADER.size + total * _NATIVE_MEMBER_RECORD.size
    rows_valid = len(raw) == expected_size
    pointers: set[int] = set()
    counts = [field_count, property_count, event_count]
    strides = (field_stride, property_stride, event_stride)
    expected_type = [0, 0, 0]
    expected_member = [0, 0, 0]
    if rows_valid:


        zero_tails = {
            stride: b"" if stride >= 48 else bytes(48 - stride)
            for stride in set(strides)
        }
        for row in _NATIVE_MEMBER_RECORD.iter_unpack(
            raw[_NATIVE_MEMBER_HEADER.size : expected_size]
        ):
            type_index, member_index, pointer, kind, stride, payload = row
            if (
                kind > 2
                or type_index >= type_count
                or not pointer
                or stride not in strides
                or stride != strides[kind]
                or payload[stride:] != zero_tails[stride]
            ):
                rows_valid = False
                break
            if type_index != expected_type[kind]:
                if type_index < expected_type[kind]:
                    rows_valid = False
                    break
                expected_type[kind] = type_index
                expected_member[kind] = 0
            if member_index != expected_member[kind]:
                rows_valid = False
                break
            expected_member[kind] += 1


            pointers.add(pointer)
    helper_layout = plan.get("native_member_layout", {})
    expected_count = plan.get("contract", {}).get("type_definition_count")
    return {
        "native_member_inventory_present": True,
        "native_member_inventory_header_complete": len(raw)
        >= _NATIVE_MEMBER_HEADER.size,
        "native_member_inventory_magic": magic == _NATIVE_MEMBER_MAGIC,
        "native_member_inventory_version": version == _NATIVE_MEMBER_VERSION,
        "native_member_inventory_record_size": record_bytes
        == _NATIVE_MEMBER_RECORD.size,
        "native_member_inventory_type_count": type_count == expected_count,
        "native_member_inventory_reserved_zero": reserved == 0,
        "native_member_inventory_counts_positive": field_count > 0
        and property_count > 0
        and event_count > 0,
        "native_member_inventory_image_size": image_bytes
        == materializer.get("binary", {}).get("size_of_image"),
        "native_member_inventory_executable_hash": executable_hash
        == plan.get("target", {}).get("executable_sha256"),
        "native_member_inventory_materializer_hash": materializer_hash
        == plan.get("inputs", {}).get("materializer_model_sha256"),
        "native_member_inventory_helper_hash": helper_hash
        == plan.get("inputs", {}).get("native_helper_model_sha256"),
        "native_member_inventory_layout_bound": isinstance(helper_layout, dict)
        and (field_rva, field_array_offset, field_stride)
        == tuple(helper_layout.get("field", ()))
        and (property_rva, property_array_offset, property_stride)
        == tuple(helper_layout.get("property", ()))
        and (event_rva, event_array_offset, event_stride)
        == tuple(helper_layout.get("event", ())),
        "native_member_inventory_size_exact": len(raw) == expected_size,
        "native_member_inventory_rows_bound": rows_valid,
        "native_member_inventory_pointers_unique": rows_valid
        and len(pointers) == total,
    }


def runtime_type_materializer_validator_source(
    *,
    expected_executable_sha256: str,
    expected_materializer_model_sha256: str,
    expected_native_helper_model_sha256: str,
    status_path: Path,
    type_map_path: Path,
    native_inventory_path: Path,
    native_member_inventory_path: Path,
    state_slot_rva: int,
    resolver_helper_rva: int,
    materializer_rva: int,
    embedded_descriptor_byte_offset: int,
    owner_rows: str,
    owner_count: int,
    definition_rows: str,
    definition_count: int,
    class_name_pointer_qword: int,
    parent_class_qword: int,
    class_declaring_qword: int,
    method_array_pointer_qword: int,
    method_count_byte_offset: int,
    method_declaring_class_qword: int,
    method_pointer_qword: int,
    class_get_methods_rva: int,
    class_get_fields_rva: int,
    field_array_byte_offset: int,
    field_record_stride: int,
    class_get_properties_rva: int,
    property_array_byte_offset: int,
    property_record_stride: int,
    class_get_events_rva: int,
    event_array_byte_offset: int,
    event_record_stride: int,
    parent_class_byte_offset: int | None = None,
    parent_class_pointer_encoding: str = "native-pointer",
) -> str:
    if len(expected_executable_sha256) != 64 or any(
        character not in "0123456789abcdefABCDEF"
        for character in expected_executable_sha256
    ):
        raise AcquisitionError(
            "runtime type materializer validation requires an executable SHA-256"
        )
    if len(expected_materializer_model_sha256) != 64 or any(
        character not in "0123456789abcdefABCDEF"
        for character in expected_materializer_model_sha256
    ):
        raise AcquisitionError(
            "runtime type materializer validation requires a model SHA-256"
        )
    if len(expected_native_helper_model_sha256) != 64 or any(
        character not in "0123456789abcdefABCDEF"
        for character in expected_native_helper_model_sha256
    ):
        raise AcquisitionError(
            "runtime type materializer validation requires a helper SHA-256"
        )
    if parent_class_byte_offset is None:
        parent_class_byte_offset = parent_class_qword * 8
    if parent_class_pointer_encoding not in {
        "hierarchy-pointer",
        "native-pointer",
        "same-region-low32",
    }:
        raise AcquisitionError(
            "runtime type materializer parent encoding is invalid"
        )
    positive_rvas = {
        "state_slot_rva": state_slot_rva,
        "resolver_helper_rva": resolver_helper_rva,
        "materializer_rva": materializer_rva,
        "class_get_methods_rva": class_get_methods_rva,
        "class_get_fields_rva": class_get_fields_rva,
        "class_get_properties_rva": class_get_properties_rva,
        "class_get_events_rva": class_get_events_rva,
    }
    positive_u32 = {
        "owner_count": owner_count,
        "definition_count": definition_count,
        "field_record_stride": field_record_stride,
        "property_record_stride": property_record_stride,
        "event_record_stride": event_record_stride,
    }
    offsets_u32 = {
        "embedded_descriptor_byte_offset": embedded_descriptor_byte_offset,
        "class_name_pointer_qword": class_name_pointer_qword,
        "parent_class_qword": parent_class_qword,
        "parent_class_byte_offset": parent_class_byte_offset,
        "class_declaring_qword": class_declaring_qword,
        "method_array_pointer_qword": method_array_pointer_qword,
        "method_count_byte_offset": method_count_byte_offset,
        "method_declaring_class_qword": method_declaring_class_qword,
        "method_pointer_qword": method_pointer_qword,
        "field_array_byte_offset": field_array_byte_offset,
        "property_array_byte_offset": property_array_byte_offset,
        "event_array_byte_offset": event_array_byte_offset,
    }
    for name, value in positive_rvas.items():
        if type(value) is not int or not 0 < value < 1 << 64:
            raise AcquisitionError(
                f"runtime type materializer validation binding is invalid: {name}"
            )
    for name, value in positive_u32.items():
        if type(value) is not int or not 0 < value < 1 << 32:
            raise AcquisitionError(
                f"runtime type materializer validation binding is invalid: {name}"
            )
    for name, value in offsets_u32.items():
        if type(value) is not int or not 0 <= value < 1 << 32:
            raise AcquisitionError(
                f"runtime type materializer inventory layout is invalid: {name}"
            )
    if not owner_rows or not definition_rows:
        raise AcquisitionError("runtime type materializer validation contract is empty")
    status_literal = _wide_literal(_windows_z_path(status_path))
    type_map_literal = _wide_literal(_windows_z_path(type_map_path))
    native_inventory_literal = _wide_literal(
        _windows_z_path(native_inventory_path)
    )
    native_member_inventory_literal = _wide_literal(
        _windows_z_path(native_member_inventory_path)
    )
    return rf'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <wchar.h>

#define ALPHA_HASH_CHUNK (1024u * 1024u)

typedef struct alpha_owner {{
    const char *namespace_name;
    const char *type_name;
    uint32_t definition_index;
    uint64_t type_flags;
    uint64_t descriptor_rva;
}} alpha_owner;

typedef struct alpha_definition {{
    uint64_t type_flags;
    uint64_t descriptor_rva;
}} alpha_definition;

typedef struct alpha_type_map_header {{
    char magic[8];
    uint32_t version;
    uint32_t record_bytes;
    uint64_t record_count;
    uint64_t image_bytes;
    char executable_sha256[64];
    char materializer_model_sha256[64];
}} alpha_type_map_header;

typedef struct alpha_type_map_record {{
    uint32_t definition_index;
    uint32_t reserved;
    uint64_t type_flags;
    uint64_t descriptor_rva;
    uint64_t class_pointer;
}} alpha_type_map_record;

typedef struct alpha_native_inventory_header {{
    char magic[8];
    uint32_t version;
    uint32_t type_record_bytes;
    uint32_t method_record_bytes;
    uint32_t reserved;
    uint64_t type_count;
    uint64_t method_count;
    uint64_t image_bytes;
    char executable_sha256[64];
    char materializer_model_sha256[64];
    uint32_t class_name_qword;
    uint32_t parent_class_qword;
    uint32_t class_declaring_qword;
    uint32_t method_array_qword;
    uint32_t method_count_byte_offset;
    uint32_t method_declaring_qword;
    uint32_t method_pointer_qword;
    uint32_t reserved_layout;
}} alpha_native_inventory_header;

typedef struct alpha_native_type_record {{
    uint32_t definition_index;
    uint32_t name_bytes;
    uint64_t type_flags;
    uint64_t descriptor_rva;
    uint64_t class_pointer;
    uint64_t parent_pointer;
    uint64_t declaring_pointer;
    uint32_t method_count;
    uint32_t reserved;
    uint64_t method_start;
    uint64_t name_offset;
}} alpha_native_type_record;

typedef struct alpha_native_method_record {{
    uint32_t definition_index;
    uint32_t method_index;
    uint64_t metadata_pointer;
    uint64_t method_pointer;
}} alpha_native_method_record;

typedef struct alpha_native_member_inventory_header {{
    char magic[8];
    uint32_t version;
    uint32_t record_bytes;
    uint32_t type_count;
    uint32_t reserved;
    uint64_t field_count;
    uint64_t property_count;
    uint64_t event_count;
    uint64_t image_bytes;
    char executable_sha256[64];
    char materializer_model_sha256[64];
    char native_helper_model_sha256[64];
    uint64_t field_rva;
    uint32_t field_array_byte_offset;
    uint32_t field_record_stride;
    uint64_t property_rva;
    uint32_t property_array_byte_offset;
    uint32_t property_record_stride;
    uint64_t event_rva;
    uint32_t event_array_byte_offset;
    uint32_t event_record_stride;
}} alpha_native_member_inventory_header;

typedef struct alpha_native_member_record {{
    uint32_t definition_index;
    uint32_t member_index;
    uint64_t metadata_pointer;
    uint32_t kind;
    uint32_t stride;
    unsigned char payload[48];
}} alpha_native_member_record;

static const char expected_executable_sha256[] =
    "{expected_executable_sha256.lower()}";
static const char expected_materializer_model_sha256[] =
    "{expected_materializer_model_sha256.lower()}";
static const char expected_native_helper_model_sha256[] =
    "{expected_native_helper_model_sha256.lower()}";
static const wchar_t status_output[] = {status_literal};
static const wchar_t type_map_output[] = {type_map_literal};
static const wchar_t native_inventory_output[] = {native_inventory_literal};
static const wchar_t native_member_inventory_output[] =
    {native_member_inventory_literal};
static const uint64_t derived_state_slot_rva = {state_slot_rva}ull;
static const uint64_t derived_resolver_helper_rva = {resolver_helper_rva}ull;
static const uint64_t derived_materializer_rva = {materializer_rva}ull;
static const uint32_t derived_descriptor_byte_offset =
    {embedded_descriptor_byte_offset}u;
static const uint32_t required_owner_count = {owner_count}u;
static const uint32_t required_definition_count = {definition_count}u;
static const uint32_t derived_class_name_qword = {class_name_pointer_qword}u;
static const uint32_t derived_parent_class_qword = {parent_class_qword}u;
static const uint32_t derived_parent_class_byte_offset =
    {parent_class_byte_offset}u;
static const uint32_t derived_parent_class_is_low32 =
    {1 if parent_class_pointer_encoding == "same-region-low32" else 0}u;
static const uint32_t derived_class_declaring_qword = {class_declaring_qword}u;
static const uint32_t derived_method_array_qword =
    {method_array_pointer_qword}u;
static const uint32_t derived_method_count_byte_offset =
    {method_count_byte_offset}u;
static const uint32_t derived_method_declaring_qword =
    {method_declaring_class_qword}u;
static const uint32_t derived_method_pointer_qword = {method_pointer_qword}u;
static const uint64_t derived_class_get_methods_rva =
    {class_get_methods_rva}ull;
static const uint64_t derived_class_get_fields_rva = {class_get_fields_rva}ull;
static const uint32_t derived_field_array_byte_offset =
    {field_array_byte_offset}u;
static const uint32_t derived_field_record_stride = {field_record_stride}u;
static const uint64_t derived_class_get_properties_rva =
    {class_get_properties_rva}ull;
static const uint32_t derived_property_array_byte_offset =
    {property_array_byte_offset}u;
static const uint32_t derived_property_record_stride =
    {property_record_stride}u;
static const uint64_t derived_class_get_events_rva = {class_get_events_rva}ull;
static const uint32_t derived_event_array_byte_offset =
    {event_array_byte_offset}u;
static const uint32_t derived_event_record_stride = {event_record_stride}u;
static const alpha_owner required_owners[] = {{
{owner_rows}
}};
static const alpha_definition required_definitions[] = {{
{definition_rows}
}};

_Static_assert(sizeof(alpha_type_map_header) == {_TYPE_MAP_HEADER.size},
    "type map header layout mismatch");
_Static_assert(sizeof(alpha_type_map_record) == {_TYPE_MAP_RECORD.size},
    "type map record layout mismatch");
_Static_assert(
    sizeof(alpha_native_inventory_header) == {_NATIVE_INVENTORY_HEADER.size},
    "native inventory header layout mismatch");
_Static_assert(sizeof(alpha_native_type_record) == {_NATIVE_TYPE_RECORD.size},
    "native type record layout mismatch");
_Static_assert(
    sizeof(alpha_native_method_record) == {_NATIVE_METHOD_RECORD.size},
    "native method record layout mismatch");
_Static_assert(
    sizeof(alpha_native_member_inventory_header) == {_NATIVE_MEMBER_HEADER.size},
    "native member inventory header layout mismatch");
_Static_assert(sizeof(alpha_native_member_record) == {_NATIVE_MEMBER_RECORD.size},
    "native member record layout mismatch");

typedef uintptr_t (*alpha_type_resolver)(
    uintptr_t state,
    const char *namespace_name,
    const char *type_name
);
typedef uintptr_t (*alpha_type_materializer)(uint32_t definition_index);
typedef uintptr_t (*alpha_class_get_methods)(
    uintptr_t class_object,
    uintptr_t *iterator
);

static void digest_hex(const unsigned char digest[32], char output[65]) {{
    static const char alphabet[] = "0123456789abcdef";
    for (int index = 0; index < 32; index++) {{
        output[index * 2] = alphabet[digest[index] >> 4];
        output[index * 2 + 1] = alphabet[digest[index] & 15];
    }}
    output[64] = 0;
}}

static int sha256_file(const wchar_t *path, char output[65]) {{
    HANDLE input = CreateFileW(
        path, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (input == INVALID_HANDLE_VALUE) return 0;
    BCRYPT_ALG_HANDLE algorithm = NULL;
    BCRYPT_HASH_HANDLE hash = NULL;
    DWORD object_size = 0, received = 0;
    unsigned char *object = NULL, *buffer = NULL;
    unsigned char digest[32];
    int ok = BCryptOpenAlgorithmProvider(
        &algorithm, BCRYPT_SHA256_ALGORITHM, NULL, 0
    ) >= 0;
    if (ok) ok = BCryptGetProperty(
        algorithm, BCRYPT_OBJECT_LENGTH,
        (PUCHAR)&object_size, sizeof(object_size), &received, 0
    ) >= 0 && object_size;
    if (ok) object = (unsigned char *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, object_size
    );
    if (!object || BCryptCreateHash(
            algorithm, &hash, object, object_size, NULL, 0, 0
        ) < 0) ok = 0;
    if (ok) buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, ALPHA_HASH_CHUNK
    );
    if (!buffer) ok = 0;
    while (ok) {{
        DWORD bytes = 0;
        if (!ReadFile(input, buffer, ALPHA_HASH_CHUNK, &bytes, NULL)) {{
            ok = 0;
            break;
        }}
        if (!bytes) break;
        if (BCryptHashData(hash, buffer, bytes, 0) < 0) ok = 0;
    }}
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) >= 0)
        digest_hex(digest, output);
    else
        ok = 0;
    if (hash) BCryptDestroyHash(hash);
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    if (object) HeapFree(GetProcessHeap(), 0, object);
    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);
    CloseHandle(input);
    return ok;
}}

static int executable_identity(char output[65]) {{
    wchar_t executable[MAX_PATH * 8];
    DWORD length = GetModuleFileNameW(
        NULL, executable,
        (DWORD)(sizeof(executable) / sizeof(executable[0]))
    );
    return length && length < sizeof(executable) / sizeof(executable[0]) &&
        sha256_file(executable, output);
}}

static int main_image(uintptr_t *base, uint64_t *bytes) {{
    HMODULE module = GetModuleHandleW(NULL);
    if (!module) return 0;
    const unsigned char *image = (const unsigned char *)module;
    if (image[0] != 'M' || image[1] != 'Z') return 0;
    uint32_t pe_offset = 0;
    memcpy(&pe_offset, image + 0x3c, sizeof(pe_offset));
    if (pe_offset > 0x100000u || memcmp(image + pe_offset, "PE\0\0", 4))
        return 0;
    const unsigned char *optional = image + pe_offset + 24;
    uint16_t magic = 0;
    uint32_t image_size = 0;
    memcpy(&magic, optional, sizeof(magic));
    memcpy(&image_size, optional + 56, sizeof(image_size));
    if (magic != 0x20bu || !image_size || image_size > 0x80000000u)
        return 0;
    *base = (uintptr_t)module;
    *bytes = image_size;
    return 1;
}}

static int readable_pointer(uintptr_t value, SIZE_T bytes) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !bytes || value + bytes <= value || !VirtualQuery(
            (const void *)value, &region, sizeof(region)
        ) || region.State != MEM_COMMIT || region.Protect & PAGE_GUARD)
        return 0;
    DWORD protect = region.Protect & 0xffu;
    if (protect == PAGE_NOACCESS || !protect) return 0;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    return end > value && bytes <= end - value;
}}

static int executable_pointer(uintptr_t value) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !VirtualQuery(
            (const void *)value, &region, sizeof(region)
        ) || region.State != MEM_COMMIT) return 0;
    DWORD protect = region.Protect & 0xffu;
    return protect == PAGE_EXECUTE || protect == PAGE_EXECUTE_READ ||
        protect == PAGE_EXECUTE_READWRITE || protect == PAGE_EXECUTE_WRITECOPY;
}}

static uintptr_t class_from_definition_descriptor(
    alpha_type_materializer materialize,
    uintptr_t descriptor
) {{
    uint64_t definition_index = 0;
    if (!readable_pointer(descriptor, sizeof(uint64_t) * 2u)) return 0;
    memcpy(&definition_index, (const void *)descriptor, sizeof(definition_index));
    if (definition_index > UINT32_MAX) return 0;
    return materialize((uint32_t)definition_index);
}}

static int write_materialized_type_map(
    uintptr_t image_base,
    uint64_t image_bytes,
    alpha_type_materializer materialize,
    uint32_t *static_descriptor_count,
    uint32_t *materialized_count,
    uint32_t *embedded_descriptor_count,
    uint32_t *failure_index
) {{
    *static_descriptor_count = 0;
    *materialized_count = 0;
    *embedded_descriptor_count = 0;
    *failure_index = 0;
    _wremove(type_map_output);
    FILE *output = _wfopen(type_map_output, L"wb");
    if (!output) return 0;
    alpha_type_map_header header;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHATM1", 8);
    header.version = {_TYPE_MAP_VERSION}u;
    header.record_bytes = (uint32_t)sizeof(alpha_type_map_record);
    header.record_count = required_definition_count;
    header.image_bytes = image_bytes;
    memcpy(header.executable_sha256, expected_executable_sha256, 64);
    memcpy(header.materializer_model_sha256,
        expected_materializer_model_sha256, 64);
    int complete = fwrite(&header, 1, sizeof(header), output) == sizeof(header);
    for (uint32_t index = 0; complete && index < required_definition_count;
         index++) {{
        const alpha_definition *definition = &required_definitions[index];
        if (definition->descriptor_rva + sizeof(uint64_t) * 2u > image_bytes) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        uintptr_t descriptor = image_base +
            (uintptr_t)definition->descriptor_rva;
        uint64_t static_index = 0, static_flags = 0;
        if (!readable_pointer(descriptor, sizeof(uint64_t) * 2u)) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        memcpy(&static_index, (const void *)descriptor, sizeof(static_index));
        memcpy(&static_flags, (const void *)(descriptor + sizeof(uint64_t)),
            sizeof(static_flags));
        if (static_index != index || static_flags != definition->type_flags) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        (*static_descriptor_count)++;
        uintptr_t class_object = class_from_definition_descriptor(
            materialize, descriptor
        );
        if (!class_object) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        (*materialized_count)++;
        uintptr_t embedded = class_object +
            (uintptr_t)derived_descriptor_byte_offset;
        uint64_t embedded_index = 0, embedded_flags = 0;
        if (embedded < class_object ||
            !readable_pointer(embedded, sizeof(uint64_t) * 2u)) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        memcpy(&embedded_index, (const void *)embedded, sizeof(embedded_index));
        memcpy(&embedded_flags, (const void *)(embedded + sizeof(uint64_t)),
            sizeof(embedded_flags));
        if (embedded_index != index ||
            embedded_flags != definition->type_flags) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        (*embedded_descriptor_count)++;
        alpha_type_map_record record;
        memset(&record, 0, sizeof(record));
        record.definition_index = index;
        record.type_flags = definition->type_flags;
        record.descriptor_rva = definition->descriptor_rva;
        record.class_pointer = class_object;
        if (fwrite(&record, 1, sizeof(record), output) != sizeof(record)) {{
            *failure_index = index + 1u;
            complete = 0;
        }}
    }}
    if (fflush(output)) complete = 0;
    if (fclose(output)) complete = 0;
    if (!complete) {{
        _wremove(type_map_output);
        return 0;
    }}
    _wchmod(type_map_output, 0600);
    return 1;
}}

static uint32_t bounded_name_bytes(uintptr_t value) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD)
        return UINT32_MAX;
    DWORD protect = region.Protect & 0xffu;
    if (protect == PAGE_NOACCESS || !protect) return UINT32_MAX;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    if (end <= value) return UINT32_MAX;
    SIZE_T available = end - value;
    if (available > 4097u) available = 4097u;
    const unsigned char *text = (const unsigned char *)value;
    for (SIZE_T index = 0; index < available; index++) {{
        if (!text[index]) return (uint32_t)index;
    }}
    return UINT32_MAX;
}}

static int write_native_inventory(
    uintptr_t image_base,
    uint64_t image_bytes,
    alpha_type_materializer materialize,
    alpha_class_get_methods get_methods,
    uint32_t *inventoried_type_count,
    uint64_t *inventoried_method_count,
    uint32_t *failure_index
) {{
    *inventoried_type_count = 0;
    *inventoried_method_count = 0;
    *failure_index = 0;
    _wremove(native_inventory_output);
    SIZE_T type_bytes =
        (SIZE_T)required_definition_count * sizeof(alpha_native_type_record);
    SIZE_T name_pointer_bytes =
        (SIZE_T)required_definition_count * sizeof(uintptr_t);
    if (!required_definition_count ||
        type_bytes / sizeof(alpha_native_type_record) !=
            required_definition_count ||
        name_pointer_bytes / sizeof(uintptr_t) != required_definition_count)
        return 0;
    alpha_native_type_record *types =
        (alpha_native_type_record *)HeapAlloc(
            GetProcessHeap(), HEAP_ZERO_MEMORY, type_bytes
        );
    uintptr_t *name_pointers = (uintptr_t *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, name_pointer_bytes
    );
    if (!types || !name_pointers) {{
        if (types) HeapFree(GetProcessHeap(), 0, types);
        if (name_pointers) HeapFree(GetProcessHeap(), 0, name_pointers);
        return 0;
    }}
    int complete = 1;
    uint64_t method_count = 0, name_bytes = 0;
    for (uint32_t index = 0; index < required_definition_count; index++) {{
        const alpha_definition *definition = &required_definitions[index];
        uintptr_t descriptor = image_base +
            (uintptr_t)definition->descriptor_rva;
        uintptr_t class_object = class_from_definition_descriptor(
            materialize, descriptor
        );
        uintptr_t name_address = class_object +
            (uintptr_t)derived_class_name_qword * sizeof(uintptr_t);
        uintptr_t parent_address = class_object +
            (uintptr_t)derived_parent_class_byte_offset;
        uintptr_t method_array_address = class_object +
            (uintptr_t)derived_method_array_qword * sizeof(uintptr_t);
        uintptr_t method_count_address = class_object +
            (uintptr_t)derived_method_count_byte_offset;
        uintptr_t name_pointer = 0, parent_pointer = 0, method_array = 0;
        uint16_t observed_method_count = 0;
        if (!class_object || name_address < class_object ||
            parent_address < class_object || method_array_address < class_object ||
            method_count_address < class_object ||
            !readable_pointer(name_address, sizeof(name_pointer)) ||
            !readable_pointer(parent_address,
                derived_parent_class_is_low32
                    ? sizeof(uint32_t) : sizeof(parent_pointer)) ||
            !readable_pointer(method_array_address, sizeof(method_array)) ||
            !readable_pointer(method_count_address,
                sizeof(observed_method_count))) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        memcpy(&name_pointer, (const void *)name_address, sizeof(name_pointer));
        if (derived_parent_class_is_low32) {{
            uint32_t parent_low = 0;
            memcpy(&parent_low, (const void *)parent_address,
                sizeof(parent_low));
            parent_pointer = parent_low
                ? ((class_object & ~(uintptr_t)UINT32_MAX)
                    | (uintptr_t)parent_low)
                : 0;
        }} else {{
            memcpy(&parent_pointer, (const void *)parent_address,
                sizeof(parent_pointer));
        }}
        memcpy(&method_array, (const void *)method_array_address,
            sizeof(method_array));
        memcpy(&observed_method_count, (const void *)method_count_address,
            sizeof(observed_method_count));
        uintptr_t iterator = 0;
        uint32_t iterator_count = 0;
        for (;;) {{
            uintptr_t method = get_methods(class_object, &iterator);
            if (!method) break;
            iterator_count++;
            if (iterator_count > UINT16_MAX) {{
                *failure_index = index + 1u;
                complete = 0;
                break;
            }}
        }}
        if (!complete) break;
        memcpy(&method_array, (const void *)method_array_address,
            sizeof(method_array));
        memcpy(&observed_method_count, (const void *)method_count_address,
            sizeof(observed_method_count));
        uint32_t observed_name_bytes = bounded_name_bytes(name_pointer);
        if (iterator_count != observed_method_count ||
            observed_name_bytes == UINT32_MAX ||
            (observed_method_count && (!method_array || !readable_pointer(
                method_array,
                (SIZE_T)observed_method_count * sizeof(uintptr_t)
            ))) ||
            method_count + observed_method_count < method_count ||
            method_count + observed_method_count > 10000000ull ||
            name_bytes + observed_name_bytes < name_bytes ||
            name_bytes + observed_name_bytes > 0x10000000ull) {{
            *failure_index = index + 1u;
            complete = 0;
            break;
        }}
        alpha_native_type_record *record = &types[index];
        record->definition_index = index;
        record->name_bytes = observed_name_bytes;
        record->type_flags = definition->type_flags;
        record->descriptor_rva = definition->descriptor_rva;
        record->class_pointer = class_object;
        record->parent_pointer = parent_pointer;
        record->declaring_pointer = 0;
        record->method_count = observed_method_count;
        record->method_start = method_count;
        name_pointers[index] = name_pointer;
        method_count += observed_method_count;
        name_bytes += observed_name_bytes;
        (*inventoried_type_count)++;
    }}
    uint64_t names_start = sizeof(alpha_native_inventory_header) +
        (uint64_t)required_definition_count * sizeof(alpha_native_type_record) +
        method_count * sizeof(alpha_native_method_record);
    if (names_start + name_bytes < names_start) complete = 0;
    uint64_t name_cursor = names_start;
    for (uint32_t index = 0; complete && index < required_definition_count;
         index++) {{
        types[index].name_offset = name_cursor;
        name_cursor += types[index].name_bytes;
    }}
    FILE *output = complete ? _wfopen(native_inventory_output, L"wb") : NULL;
    if (!output) complete = 0;
    alpha_native_inventory_header header;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHANI1", 8);
    header.version = {_NATIVE_INVENTORY_VERSION}u;
    header.type_record_bytes = (uint32_t)sizeof(alpha_native_type_record);
    header.method_record_bytes = (uint32_t)sizeof(alpha_native_method_record);
    header.type_count = required_definition_count;
    header.method_count = method_count;
    header.image_bytes = image_bytes;
    memcpy(header.executable_sha256, expected_executable_sha256, 64);
    memcpy(header.materializer_model_sha256,
        expected_materializer_model_sha256, 64);
    header.class_name_qword = derived_class_name_qword;
    header.parent_class_qword = derived_parent_class_qword;
    header.class_declaring_qword = derived_class_declaring_qword;
    header.method_array_qword = derived_method_array_qword;
    header.method_count_byte_offset = derived_method_count_byte_offset;
    header.method_declaring_qword = derived_method_declaring_qword;
    header.method_pointer_qword = derived_method_pointer_qword;
    if (complete && fwrite(&header, 1, sizeof(header), output) != sizeof(header))
        complete = 0;
    if (complete && fwrite(types, 1, type_bytes, output) != type_bytes)
        complete = 0;
    uint64_t written_methods = 0;
    for (uint32_t type_index = 0;
         complete && type_index < required_definition_count; type_index++) {{
        const alpha_native_type_record *type = &types[type_index];
        uintptr_t array_address = type->class_pointer +
            (uintptr_t)derived_method_array_qword * sizeof(uintptr_t);
        uintptr_t method_array = 0;
        memcpy(&method_array, (const void *)array_address, sizeof(method_array));
        uintptr_t iterator = 0;
        for (uint32_t method_index = 0;
             method_index < type->method_count; method_index++) {{
            uintptr_t metadata_pointer = 0;
            memcpy(&metadata_pointer,
                (const void *)(method_array +
                    (uintptr_t)method_index * sizeof(uintptr_t)),
                sizeof(metadata_pointer));
            uintptr_t declaring_address = metadata_pointer +
                (uintptr_t)derived_method_declaring_qword * sizeof(uintptr_t);
            uintptr_t method_pointer_address = metadata_pointer +
                (uintptr_t)derived_method_pointer_qword * sizeof(uintptr_t);
            uintptr_t declaring_class = 0, method_pointer = 0;
            if (!metadata_pointer || declaring_address < metadata_pointer ||
                method_pointer_address < metadata_pointer ||
                !readable_pointer(declaring_address, sizeof(declaring_class)) ||
                !readable_pointer(method_pointer_address, sizeof(method_pointer))) {{
                *failure_index = type_index + 1u;
                complete = 0;
                break;
            }}
            memcpy(&declaring_class, (const void *)declaring_address,
                sizeof(declaring_class));
            memcpy(&method_pointer, (const void *)method_pointer_address,
                sizeof(method_pointer));
            uintptr_t iterator_method = get_methods(
                type->class_pointer, &iterator
            );
            if (iterator_method != metadata_pointer ||
                declaring_class != type->class_pointer ||
                (method_pointer && !executable_pointer(method_pointer))) {{
                *failure_index = type_index + 1u;
                complete = 0;
                break;
            }}
            alpha_native_method_record method;
            method.definition_index = type_index;
            method.method_index = method_index;
            method.metadata_pointer = metadata_pointer;
            method.method_pointer = method_pointer;
            if (fwrite(&method, 1, sizeof(method), output) != sizeof(method)) {{
                *failure_index = type_index + 1u;
                complete = 0;
                break;
            }}
            written_methods++;
        }}
        if (complete && get_methods(type->class_pointer, &iterator)) {{
            *failure_index = type_index + 1u;
            complete = 0;
        }}
    }}
    if (written_methods != method_count) complete = 0;
    for (uint32_t index = 0; complete && index < required_definition_count;
         index++) {{
        if (fwrite((const void *)name_pointers[index], 1,
                types[index].name_bytes, output) != types[index].name_bytes) {{
            *failure_index = index + 1u;
            complete = 0;
        }}
    }}
    if (output) {{
        if (fflush(output)) complete = 0;
        if (fclose(output)) complete = 0;
    }}
    HeapFree(GetProcessHeap(), 0, name_pointers);
    HeapFree(GetProcessHeap(), 0, types);
    if (!complete) {{
        _wremove(native_inventory_output);
        return 0;
    }}
    _wchmod(native_inventory_output, 0600);
    *inventoried_method_count = method_count;
    return 1;
}}

static int observe_native_member_sequence(
    uintptr_t class_object,
    alpha_class_get_methods get_member,
    uint32_t array_byte_offset,
    uint32_t record_stride,
    uint32_t definition_index,
    uint32_t kind,
    FILE *output,
    uint64_t *observed_count
) {{
    uintptr_t array_address = class_object + array_byte_offset;
    uintptr_t member_array = 0;
    if (!class_object || array_address < class_object ||
        !readable_pointer(array_address, sizeof(member_array)) ||
        !record_stride || record_stride > 48u ||
        record_stride % sizeof(uintptr_t)) return 0;
    memcpy(&member_array, (const void *)array_address, sizeof(member_array));
    uintptr_t iterator = 0;
    uint32_t member_index = 0;
    for (;;) {{
        uintptr_t observed = get_member(class_object, &iterator);
        if (!observed) break;
        if (!member_array) {{
            memcpy(&member_array, (const void *)array_address,
                sizeof(member_array));
        }}
        uintptr_t expected = member_array +
            (uintptr_t)member_index * record_stride;
        if (!member_array || expected < member_array ||
            observed != iterator || observed != expected ||
            !readable_pointer(observed, record_stride)) return 0;
        if (output) {{
            alpha_native_member_record record;
            memset(&record, 0, sizeof(record));
            record.definition_index = definition_index;
            record.member_index = member_index;
            record.metadata_pointer = observed;
            record.kind = kind;
            record.stride = record_stride;
            memcpy(record.payload, (const void *)observed, record_stride);
            if (fwrite(&record, 1, sizeof(record), output) != sizeof(record))
                return 0;
        }}
        member_index++;
        if (member_index > 1000000u) return 0;
    }}
    *observed_count = member_index;
    return 1;
}}

static int write_native_member_inventory(
    uintptr_t image_base,
    uint64_t image_bytes,
    alpha_type_materializer materialize,
    alpha_class_get_methods get_fields,
    alpha_class_get_methods get_properties,
    alpha_class_get_methods get_events,
    uint64_t *field_count,
    uint64_t *property_count,
    uint64_t *event_count,
    uint32_t *failure_type_index,
    uint32_t *failure_kind
) {{
    *field_count = 0;
    *property_count = 0;
    *event_count = 0;
    *failure_type_index = 0;
    *failure_kind = 0;
    _wremove(native_member_inventory_output);
    alpha_class_get_methods helpers[3] = {{
        get_fields, get_properties, get_events
    }};
    uint32_t offsets[3] = {{
        derived_field_array_byte_offset,
        derived_property_array_byte_offset,
        derived_event_array_byte_offset
    }};
    uint32_t strides[3] = {{
        derived_field_record_stride,
        derived_property_record_stride,
        derived_event_record_stride
    }};
    uint64_t *totals[3] = {{field_count, property_count, event_count}};
    for (uint32_t kind = 0; kind < 3; kind++) {{
        for (uint32_t type_index = 0;
             type_index < required_definition_count; type_index++) {{
            uintptr_t descriptor = image_base +
                (uintptr_t)required_definitions[type_index].descriptor_rva;
            uintptr_t class_object = class_from_definition_descriptor(
                materialize, descriptor
            );
            uint64_t count = 0;
            if (!class_object || !observe_native_member_sequence(
                    class_object, helpers[kind], offsets[kind], strides[kind],
                    type_index, kind, NULL, &count
                ) || *totals[kind] + count < *totals[kind] ||
                *totals[kind] + count > 10000000ull) {{
                *failure_type_index = type_index + 1u;
                *failure_kind = kind + 1u;
                return 0;
            }}
            *totals[kind] += count;
        }}
    }}
    FILE *output = _wfopen(native_member_inventory_output, L"wb");
    if (!output) return 0;
    alpha_native_member_inventory_header header;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHANM1", 8);
    header.version = {_NATIVE_MEMBER_VERSION}u;
    header.record_bytes = (uint32_t)sizeof(alpha_native_member_record);
    header.type_count = required_definition_count;
    header.field_count = *field_count;
    header.property_count = *property_count;
    header.event_count = *event_count;
    header.image_bytes = image_bytes;
    memcpy(header.executable_sha256, expected_executable_sha256, 64);
    memcpy(header.materializer_model_sha256,
        expected_materializer_model_sha256, 64);
    memcpy(header.native_helper_model_sha256,
        expected_native_helper_model_sha256, 64);
    header.field_rva = derived_class_get_fields_rva;
    header.field_array_byte_offset = derived_field_array_byte_offset;
    header.field_record_stride = derived_field_record_stride;
    header.property_rva = derived_class_get_properties_rva;
    header.property_array_byte_offset = derived_property_array_byte_offset;
    header.property_record_stride = derived_property_record_stride;
    header.event_rva = derived_class_get_events_rva;
    header.event_array_byte_offset = derived_event_array_byte_offset;
    header.event_record_stride = derived_event_record_stride;
    int complete = fwrite(&header, 1, sizeof(header), output) == sizeof(header);
    uint64_t written[3] = {{0, 0, 0}};
    for (uint32_t kind = 0; complete && kind < 3; kind++) {{
        for (uint32_t type_index = 0;
             complete && type_index < required_definition_count; type_index++) {{
            uintptr_t descriptor = image_base +
                (uintptr_t)required_definitions[type_index].descriptor_rva;
            uintptr_t class_object = class_from_definition_descriptor(
                materialize, descriptor
            );
            uint64_t count = 0;
            if (!class_object || !observe_native_member_sequence(
                    class_object, helpers[kind], offsets[kind], strides[kind],
                    type_index, kind, output, &count
                )) {{
                *failure_type_index = type_index + 1u;
                *failure_kind = kind + 1u;
                complete = 0;
                break;
            }}
            written[kind] += count;
        }}
    }}
    if (written[0] != *field_count || written[1] != *property_count ||
        written[2] != *event_count) complete = 0;
    if (fflush(output)) complete = 0;
    if (fclose(output)) complete = 0;
    if (!complete) {{
        _wremove(native_member_inventory_output);
        return 0;
    }}
    _wchmod(native_member_inventory_output, 0600);
    return 1;
}}

static void write_status(
    const char *status,
    const char *observed_hash,
    uint32_t resolved_owner_count,
    uint32_t index_roundtrip_count,
    uint32_t descriptor_roundtrip_count,
    uint32_t owner_embedded_descriptor_count,
    uint32_t static_definition_descriptor_count,
    uint32_t materialized_definition_count,
    uint32_t definition_embedded_descriptor_count,
    uint32_t failure_index,
    int type_map_written,
    uint32_t inventoried_type_count,
    uint64_t inventoried_method_count,
    uint32_t inventory_failure_index,
    int native_inventory_written,
    uint64_t field_count,
    uint64_t property_count,
    uint64_t event_count,
    uint32_t member_failure_type_index,
    uint32_t member_failure_kind,
    int native_member_inventory_written
) {{
    FILE *output = _wfopen(status_output, L"wb");
    if (!output) return;
    fprintf(
        output,
        "{{\n"
        "  \"schema\": \"{RUNTIME_TYPE_MATERIALIZER_VALIDATION_SCHEMA}\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"executable_hash_matches\": %s,\n"
        "  \"required_owner_count\": %u,\n"
        "  \"resolved_owner_count\": %u,\n"
        "  \"index_roundtrip_count\": %u,\n"
        "  \"descriptor_roundtrip_count\": %u,\n"
        "  \"owner_embedded_descriptor_count\": %u,\n"
        "  \"required_definition_count\": %u,\n"
        "  \"static_definition_descriptor_count\": %u,\n"
        "  \"materialized_definition_count\": %u,\n"
        "  \"definition_embedded_descriptor_count\": %u,\n"
        "  \"failure_index_owner_only\": %u,\n"
        "  \"type_map_written\": %s,\n"
        "  \"inventoried_type_count\": %u,\n"
        "  \"inventoried_method_count\": %llu,\n"
        "  \"inventory_failure_index_owner_only\": %u,\n"
        "  \"native_inventory_written\": %s,\n"
        "  \"field_count\": %llu,\n"
        "  \"property_count\": %llu,\n"
        "  \"event_count\": %llu,\n"
        "  \"member_failure_type_index_owner_only\": %u,\n"
        "  \"member_failure_kind_owner_only\": %u,\n"
        "  \"native_member_inventory_written\": %s,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"raw_runtime_pointers_exposed\": false,\n"
        "  \"saved_address_used\": false,\n"
        "  \"saved_type_index_used\": false,\n"
        "  \"network_used\": false,\n"
        "  \"external_runtime_component_used\": false\n"
        "}}\n",
        status,
        (unsigned long)GetCurrentProcessId(),
        expected_executable_sha256,
        observed_hash ? observed_hash : "",
        observed_hash && !strcmp(
            observed_hash, expected_executable_sha256
        ) ? "true" : "false",
        required_owner_count,
        resolved_owner_count,
        index_roundtrip_count,
        descriptor_roundtrip_count,
        owner_embedded_descriptor_count,
        required_definition_count,
        static_definition_descriptor_count,
        materialized_definition_count,
        definition_embedded_descriptor_count,
        failure_index,
        type_map_written ? "true" : "false",
        inventoried_type_count,
        (unsigned long long)inventoried_method_count,
        inventory_failure_index,
        native_inventory_written ? "true" : "false",
        (unsigned long long)field_count,
        (unsigned long long)property_count,
        (unsigned long long)event_count,
        member_failure_type_index,
        member_failure_kind,
        native_member_inventory_written ? "true" : "false"
    );
    fflush(output);
    fclose(output);
    _wchmod(status_output, 0600);
}}

static DWORD WINAPI worker(void *unused) {{
    (void)unused;
    char observed_hash[65] = {{0}};
    if (!executable_identity(observed_hash) || strcmp(
            observed_hash, expected_executable_sha256
        )) {{
        write_status("executable-identity-mismatch", observed_hash,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0);
        return 1;
    }}
    uintptr_t image_base = 0;
    uint64_t image_bytes = 0;
    if (!main_image(&image_base, &image_bytes) ||
        derived_state_slot_rva + sizeof(uintptr_t) > image_bytes ||
        derived_resolver_helper_rva >= image_bytes ||
        derived_materializer_rva >= image_bytes ||
        derived_class_get_methods_rva >= image_bytes ||
        derived_class_get_fields_rva >= image_bytes ||
        derived_class_get_properties_rva >= image_bytes ||
        derived_class_get_events_rva >= image_bytes) {{
        write_status("image-binding-invalid", observed_hash,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0);
        return 2;
    }}
    uintptr_t state_slot = image_base + (uintptr_t)derived_state_slot_rva;
    uintptr_t resolver_address = image_base +
        (uintptr_t)derived_resolver_helper_rva;
    uintptr_t materializer_address = image_base +
        (uintptr_t)derived_materializer_rva;
    uintptr_t class_get_methods_address = image_base +
        (uintptr_t)derived_class_get_methods_rva;
    uintptr_t class_get_fields_address = image_base +
        (uintptr_t)derived_class_get_fields_rva;
    uintptr_t class_get_properties_address = image_base +
        (uintptr_t)derived_class_get_properties_rva;
    uintptr_t class_get_events_address = image_base +
        (uintptr_t)derived_class_get_events_rva;
    uintptr_t state = 0;
    if (!readable_pointer(state_slot, sizeof(state)) ||
        !executable_pointer(resolver_address) ||
        !executable_pointer(materializer_address) ||
        !executable_pointer(class_get_methods_address) ||
        !executable_pointer(class_get_fields_address) ||
        !executable_pointer(class_get_properties_address) ||
        !executable_pointer(class_get_events_address)) {{
        write_status("helper-binding-invalid", observed_hash,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0);
        return 3;
    }}
    memcpy(&state, (const void *)state_slot, sizeof(state));
    if (!state) {{
        write_status("resolver-state-unavailable", observed_hash,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0);
        return 4;
    }}
    alpha_type_resolver resolve = (alpha_type_resolver)resolver_address;
    alpha_type_materializer materialize =
        (alpha_type_materializer)materializer_address;
    alpha_class_get_methods get_methods =
        (alpha_class_get_methods)class_get_methods_address;
    alpha_class_get_methods get_fields =
        (alpha_class_get_methods)class_get_fields_address;
    alpha_class_get_methods get_properties =
        (alpha_class_get_methods)class_get_properties_address;
    alpha_class_get_methods get_events =
        (alpha_class_get_methods)class_get_events_address;
    uint32_t resolved = 0, index_roundtrips = 0;
    uint32_t descriptor_roundtrips = 0, embedded_descriptors = 0;
    for (uint32_t owner_index = 0;
         owner_index < required_owner_count; owner_index++) {{
        const alpha_owner *owner = &required_owners[owner_index];
        uintptr_t expected_class = resolve(
            state, owner->namespace_name, owner->type_name
        );
        if (!expected_class) break;
        resolved++;
        uintptr_t by_index = materialize(owner->definition_index);
        if (by_index != expected_class) break;
        index_roundtrips++;
        if (owner->descriptor_rva + sizeof(uint64_t) * 2u > image_bytes)
            break;
        uintptr_t descriptor = image_base +
            (uintptr_t)owner->descriptor_rva;
        uint64_t static_index = 0, static_flags = 0;
        if (!readable_pointer(descriptor, sizeof(uint64_t) * 2u)) break;
        memcpy(&static_index, (const void *)descriptor, sizeof(static_index));
        memcpy(&static_flags, (const void *)(descriptor + sizeof(uint64_t)),
            sizeof(static_flags));
        if (static_index != owner->definition_index ||
            static_flags != owner->type_flags ||
            class_from_definition_descriptor(materialize, descriptor)
                != expected_class) break;
        descriptor_roundtrips++;
        uintptr_t embedded = expected_class +
            (uintptr_t)derived_descriptor_byte_offset;
        uint64_t embedded_index = 0, embedded_flags = 0;
        if (embedded < expected_class ||
            !readable_pointer(embedded, sizeof(uint64_t) * 2u)) break;
        memcpy(&embedded_index, (const void *)embedded, sizeof(embedded_index));
        memcpy(&embedded_flags, (const void *)(embedded + sizeof(uint64_t)),
            sizeof(embedded_flags));
        if (embedded_index != owner->definition_index ||
            embedded_flags != owner->type_flags) break;
        embedded_descriptors++;
    }}
    int owner_complete = resolved == required_owner_count &&
        index_roundtrips == required_owner_count &&
        descriptor_roundtrips == required_owner_count &&
        embedded_descriptors == required_owner_count;
    uint32_t static_definitions = 0, materialized_definitions = 0;
    uint32_t definition_embedded_descriptors = 0, failure_index = 0;
    int type_map_written = owner_complete && write_materialized_type_map(
        image_base, image_bytes, materialize,
        &static_definitions, &materialized_definitions,
        &definition_embedded_descriptors, &failure_index
    );
    int complete = owner_complete && type_map_written &&
        static_definitions == required_definition_count &&
        materialized_definitions == required_definition_count &&
        definition_embedded_descriptors == required_definition_count;
    uint32_t inventoried_types = 0, inventory_failure_index = 0;
    uint64_t inventoried_methods = 0;
    int native_inventory_written = complete && write_native_inventory(
        image_base, image_bytes, materialize, get_methods,
        &inventoried_types, &inventoried_methods,
        &inventory_failure_index
    );
    complete = complete && native_inventory_written &&
        inventoried_types == required_definition_count;
    uint64_t field_count = 0, property_count = 0, event_count = 0;
    uint32_t member_failure_type_index = 0, member_failure_kind = 0;
    int native_member_inventory_written = complete &&
        write_native_member_inventory(
            image_base, image_bytes, materialize,
            get_fields, get_properties, get_events,
            &field_count, &property_count, &event_count,
            &member_failure_type_index, &member_failure_kind
        );
    complete = complete && native_member_inventory_written;
    write_status(
        complete ? "complete" : "validation-mismatch",
        observed_hash, resolved, index_roundtrips,
        descriptor_roundtrips, embedded_descriptors,
        static_definitions, materialized_definitions,
        definition_embedded_descriptors, failure_index, type_map_written,
        inventoried_types, inventoried_methods,
        inventory_failure_index, native_inventory_written,
        field_count, property_count, event_count,
        member_failure_type_index, member_failure_kind,
        native_member_inventory_written
    );
    return complete ? 0 : 5;
}}

BOOL WINAPI DllMain(HINSTANCE instance, DWORD reason, LPVOID reserved) {{
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {{
        DisableThreadLibraryCalls(instance);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }}
    return TRUE;
}}
'''


def prepare_runtime_type_materializer_validation(
    *,
    binary: Path,
    bootstrap_model: Path,
    class_model: Path,
    materializer_model: Path,
    native_helper_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
    preloaded_materializer: dict[str, Any] | None = None,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    bootstrap_model = bootstrap_model.expanduser().resolve()
    class_model = class_model.expanduser().resolve()
    materializer_model = materializer_model.expanduser().resolve()
    native_helper_model = native_helper_model.expanduser().resolve()
    output_dir = _owner_directory(output_dir)
    identity, bootstrap, _classes, materializer, native_helpers = (
        _load_bound_inputs(
        binary=binary,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
        materializer_model=materializer_model,
        native_helper_model=native_helper_model,
        preloaded_materializer=preloaded_materializer,
    )
    )
    owner_rows, owner_count = _owner_rows(materializer)
    definition_rows, definition_count = _definition_rows(materializer)
    resolver = materializer.get("resolver")
    layout = materializer.get("layout")
    inventory_layout = materializer.get("inventory_layout")
    if (
        not isinstance(resolver, dict)
        or not isinstance(layout, dict)
        or not isinstance(inventory_layout, dict)
    ):
        raise AcquisitionError("runtime type materializer binding is incomplete")
    status_path = output_dir / "type-materializer-status.private.json"
    type_map_path = output_dir / "runtime-type-map.private.bin"
    native_inventory_path = output_dir / "runtime-native-inventory.private.bin"
    native_member_inventory_path = (
        output_dir / "runtime-native-members.private.bin"
    )
    validated_model_path = (
        output_dir / "runtime-type-materializer.validated.private.json"
    )
    build_dir = _owner_directory(output_dir / "build-type-materializer")
    source_path = build_dir / "runtime-type-materializer-validator.c"
    injector_source_path = build_dir / "runtime-type-materializer-injector.c"
    injector_path = build_dir / "alpha-runtime-type-materializer-injector.exe"
    for stale in (
        status_path,
        type_map_path,
        native_inventory_path,
        native_member_inventory_path,
        validated_model_path,
    ):
        stale.unlink(missing_ok=True)
    _private_text(
        source_path,
        runtime_type_materializer_validator_source(
            expected_executable_sha256=identity["sha256"],
            expected_materializer_model_sha256=file_identity(
                materializer_model
            )["sha256"],
            expected_native_helper_model_sha256=file_identity(
                native_helper_model
            )["sha256"],
            status_path=status_path,
            type_map_path=type_map_path,
            native_inventory_path=native_inventory_path,
            native_member_inventory_path=native_member_inventory_path,
            state_slot_rva=bootstrap["state_slot_rva"],
            resolver_helper_rva=bootstrap["type_resolver_helper_rva"],
            materializer_rva=resolver["type_info_materializer_rva"],
            embedded_descriptor_byte_offset=layout[
                "embedded_descriptor_byte_offset"
            ],
            owner_rows=owner_rows,
            owner_count=owner_count,
            definition_rows=definition_rows,
            definition_count=definition_count,
            class_name_pointer_qword=inventory_layout[
                "class_name_pointer_qword"
            ],
            parent_class_qword=inventory_layout["parent_class_qword"],
            parent_class_byte_offset=inventory_layout.get(
                "parent_class_byte_offset",
                inventory_layout["parent_class_qword"] * 8,
            ),
            parent_class_pointer_encoding=inventory_layout.get(
                "parent_class_pointer_encoding", "native-pointer"
            ),
            class_declaring_qword=inventory_layout["class_declaring_qword"],
            method_array_pointer_qword=inventory_layout[
                "method_array_pointer_qword"
            ],
            method_count_byte_offset=inventory_layout[
                "method_count_byte_offset"
            ],
            method_declaring_class_qword=inventory_layout[
                "method_declaring_class_qword"
            ],
            method_pointer_qword=inventory_layout["method_pointer_qword"],
            class_get_methods_rva=native_helpers["helpers"][
                "class_get_methods"
            ]["function_rva"],
            class_get_fields_rva=native_helpers["helpers"][
                "class_get_fields"
            ]["function_rva"],
            field_array_byte_offset=native_helpers["helpers"][
                "class_get_fields"
            ]["member_array_byte_offset"],
            field_record_stride=native_helpers["helpers"][
                "class_get_fields"
            ]["record_stride"],
            class_get_properties_rva=native_helpers["helpers"][
                "class_get_properties"
            ]["function_rva"],
            property_array_byte_offset=native_helpers["helpers"][
                "class_get_properties"
            ]["member_array_byte_offset"],
            property_record_stride=native_helpers["helpers"][
                "class_get_properties"
            ]["record_stride"],
            class_get_events_rva=native_helpers["helpers"][
                "class_get_events"
            ]["function_rva"],
            event_array_byte_offset=native_helpers["helpers"][
                "class_get_events"
            ]["member_array_byte_offset"],
            event_record_stride=native_helpers["helpers"][
                "class_get_events"
            ]["record_stride"],
        ),
    )
    validator_path = build_dir / (
        "alpha-runtime-type-materializer-"
        + file_identity(source_path)["sha256"][:12]
        + ".dll"
    )
    _private_text(injector_source_path, runtime_injector_source())
    selected_compiler = _compiler(compiler)


    with ThreadPoolExecutor(max_workers=2) as executor:
        validator_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler),
                "-O2",
                "-s",
                "-shared",
                "-Wall",
                "-Wextra",
                "-Wformat=2",
                "-Werror=format",
                str(source_path),
                "-o",
                str(validator_path),
                "-lbcrypt",
            ],
            label="runtime type materializer validator",
            source_path=source_path,
            output_path=validator_path,
        )
        injector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler),
                "-O2",
                "-s",
                "-municode",
                "-Wall",
                "-Wextra",
                "-Wformat=2",
                "-Werror=format",
                str(injector_source_path),
                "-o",
                str(injector_path),
            ],
            label="runtime type materializer injector",
            source_path=injector_source_path,
            output_path=injector_path,
        )
        validator_build.result()
        injector_build.result()
    for artifact in (validator_path, injector_path):
        if not artifact.is_file() or not artifact.stat().st_size:
            raise AcquisitionError(
                f"runtime type materializer build did not produce {artifact.name}"
            )
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_TYPE_MATERIALIZER_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary),
            "executable_sha256": identity["sha256"],
            "executable_bytes": identity["bytes"],
            "process_name": binary.name,
        },
        "inputs": {
            "bootstrap_model_sha256": file_identity(bootstrap_model)["sha256"],
            "class_model_sha256": file_identity(class_model)["sha256"],
            "materializer_model_sha256": file_identity(materializer_model)[
                "sha256"
            ],
            "native_helper_model_sha256": file_identity(native_helper_model)[
                "sha256"
            ],
        },
        "validator": file_identity(validator_path),
        "injector": file_identity(injector_path),
        "outputs": {
            "status": str(status_path),
            "type_map": str(type_map_path),
            "native_inventory": str(native_inventory_path),
            "native_member_inventory": str(native_member_inventory_path),
            "validated_model": str(validated_model_path),
        },
        "contract": {
            "owner_count": owner_count,
            "type_definition_count": definition_count,
        },
        "policy": {
            "current_executable_sha256_embedded": True,
            "fresh_runtime_observation_required": True,
            "index_roundtrip_required": True,
            "descriptor_roundtrip_required": True,
            "embedded_descriptor_cross_check_required": True,
            "all_type_definitions_materialized_required": True,
            "type_map_hash_binding_required": True,
            "native_type_and_method_inventory_required": True,
            "native_field_property_event_inventory_required": True,
            "raw_runtime_pointers_owner_only": True,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "fixed_rva_used": False,
            "fixed_version_used": False,
            "saved_type_index_used": False,
            "external_runtime_component_used": False,
        },
        "native_member_layout": {
            "field": [
                native_helpers["helpers"]["class_get_fields"]["function_rva"],
                native_helpers["helpers"]["class_get_fields"][
                    "member_array_byte_offset"
                ],
                native_helpers["helpers"]["class_get_fields"]["record_stride"],
            ],
            "property": [
                native_helpers["helpers"]["class_get_properties"][
                    "function_rva"
                ],
                native_helpers["helpers"]["class_get_properties"][
                    "member_array_byte_offset"
                ],
                native_helpers["helpers"]["class_get_properties"][
                    "record_stride"
                ],
            ],
            "event": [
                native_helpers["helpers"]["class_get_events"]["function_rva"],
                native_helpers["helpers"]["class_get_events"][
                    "member_array_byte_offset"
                ],
                native_helpers["helpers"]["class_get_events"]["record_stride"],
            ],
        },
    }
    _private_json(output_dir / "type-materializer-plan.private.json", plan)
    return {
        "schema": RUNTIME_TYPE_MATERIALIZER_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_sha256": identity["sha256"],
            "executable_bytes": identity["bytes"],
        },
        "contract": plan["contract"],
        "policy": plan["policy"],
    }


def capture_runtime_type_materializer_validation(
    *,
    binary: Path,
    bootstrap_model: Path,
    class_model: Path,
    materializer_model: Path,
    native_helper_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 120.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    materializer = read_json(materializer_model)
    prepare_runtime_type_materializer_validation(
        binary=binary,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
        materializer_model=materializer_model,
        native_helper_model=native_helper_model,
        output_dir=output_dir,
        compiler=compiler,
        preloaded_materializer=materializer,
    )
    plan = read_json(output_dir / "type-materializer-plan.private.json")
    binary = binary.expanduser().resolve()
    if file_identity(binary)["sha256"] != plan["target"]["executable_sha256"]:
        raise AcquisitionError(
            "target executable changed after type materializer preparation"
        )
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError("selected Wine binary or prefix is unavailable")
    validator = Path(plan["validator"]["path"])
    injector = Path(plan["injector"]["path"])
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine), injector, validator, binary.name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "ALPHA v2 runtime type materializer injector could not run"
        ) from error
    _private_text(
        output_dir / "type-materializer-injector.private.log",
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
        raise AcquisitionError(
            f"ALPHA v2 runtime type materializer injection failed ({injected.returncode})"
        )
    status_path = Path(plan["outputs"]["status"])
    deadline = time.monotonic() + max(1.0, timeout)
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        if status_path.is_file():
            try:
                value = json.loads(status_path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                value = None
            if isinstance(value, dict):
                status = value
                break
        time.sleep(0.25)
    if status is None:
        raise AcquisitionError("ALPHA v2 runtime type materializer validation timed out")
    _seal_runtime_output(status_path)
    type_map_path = Path(plan["outputs"]["type_map"])
    type_map_checks = _inspect_materialized_type_map(
        path=type_map_path,
        plan=plan,
        materializer=materializer,
    )
    if type_map_path.is_file():
        _seal_runtime_output(type_map_path)
    native_inventory_path = Path(plan["outputs"]["native_inventory"])
    native_inventory_checks = _inspect_native_inventory(
        path=native_inventory_path,
        plan=plan,
        materializer=materializer,
    )
    if native_inventory_path.is_file():
        _seal_runtime_output(native_inventory_path)
    native_member_inventory_path = Path(
        plan["outputs"]["native_member_inventory"]
    )
    native_member_inventory_checks = _inspect_native_member_inventory(
        path=native_member_inventory_path,
        plan=plan,
        materializer=materializer,
    )
    if native_member_inventory_path.is_file():
        _seal_runtime_output(native_member_inventory_path)
    owner_count = plan["contract"]["owner_count"]
    definition_count = plan["contract"]["type_definition_count"]
    checks = {
        "schema": status.get("schema")
        == RUNTIME_TYPE_MATERIALIZER_VALIDATION_SCHEMA,
        "complete": status.get("status") == "complete",
        "executable_hash_matches": status.get("executable_hash_matches") is True,
        "expected_hash_matches_plan": status.get("expected_executable_sha256")
        == plan["target"]["executable_sha256"],
        "observed_hash_matches_plan": status.get("observed_executable_sha256")
        == plan["target"]["executable_sha256"],
        "owner_count_matches": status.get("required_owner_count") == owner_count
        and status.get("resolved_owner_count") == owner_count,
        "index_roundtrip_complete": status.get("index_roundtrip_count")
        == owner_count,
        "descriptor_roundtrip_complete": status.get(
            "descriptor_roundtrip_count"
        )
        == owner_count,
        "owner_embedded_descriptor_complete": status.get(
            "owner_embedded_descriptor_count"
        )
        == owner_count,
        "static_definition_descriptors_complete": status.get(
            "static_definition_descriptor_count"
        )
        == definition_count,
        "all_type_definitions_materialized": status.get(
            "materialized_definition_count"
        )
        == definition_count,
        "definition_embedded_descriptors_complete": status.get(
            "definition_embedded_descriptor_count"
        )
        == definition_count,
        "type_map_written": status.get("type_map_written") is True,
        "failure_index_absent": status.get("failure_index_owner_only") == 0,
        "inventoried_type_count_matches": status.get(
            "inventoried_type_count"
        )
        == definition_count,
        "inventoried_method_count_positive": isinstance(
            status.get("inventoried_method_count"), int
        )
        and status["inventoried_method_count"] > 0,
        "inventory_failure_index_absent": status.get(
            "inventory_failure_index_owner_only"
        )
        == 0,
        "native_inventory_written": status.get("native_inventory_written")
        is True,
        "field_count_positive": isinstance(status.get("field_count"), int)
        and status["field_count"] > 0,
        "property_count_positive": isinstance(status.get("property_count"), int)
        and status["property_count"] > 0,
        "event_count_positive": isinstance(status.get("event_count"), int)
        and status["event_count"] > 0,
        "member_failure_type_index_absent": status.get(
            "member_failure_type_index_owner_only"
        )
        == 0,
        "member_failure_kind_absent": status.get(
            "member_failure_kind_owner_only"
        )
        == 0,
        "native_member_inventory_written": status.get(
            "native_member_inventory_written"
        )
        is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "raw_runtime_pointers_absent": status.get("raw_runtime_pointers_exposed")
        is False,
        "saved_address_absent": status.get("saved_address_used") is False,
        "saved_type_index_absent": status.get("saved_type_index_used") is False,
        "network_absent": status.get("network_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    checks.update(type_map_checks)
    checks.update(native_inventory_checks)
    checks.update(native_member_inventory_checks)
    validated = all(checks.values())
    if validated:


        materializer["status"] = "runtime-validated"
        materializer["checks"]["materializer_runtime_validated"] = True
        materializer["checks"]["all_type_definitions_materialized"] = True
        materializer["runtime_validation"] = {
            "status_sha256": file_identity(status_path)["sha256"],
            "process_id": status["process_id"],
            "owner_count": owner_count,
            "index_roundtrip_count": status["index_roundtrip_count"],
            "descriptor_roundtrip_count": status[
                "descriptor_roundtrip_count"
            ],
            "owner_embedded_descriptor_count": status[
                "owner_embedded_descriptor_count"
            ],
            "materialized_definition_count": status[
                "materialized_definition_count"
            ],
            "definition_embedded_descriptor_count": status[
                "definition_embedded_descriptor_count"
            ],
            "type_map": {
                "bytes": file_identity(type_map_path)["bytes"],
                "sha256": file_identity(type_map_path)["sha256"],
            },
            "native_inventory": {
                "bytes": file_identity(native_inventory_path)["bytes"],
                "sha256": file_identity(native_inventory_path)["sha256"],
                "type_count": status["inventoried_type_count"],
                "method_count": status["inventoried_method_count"],
            },
            "native_member_inventory": {
                "bytes": file_identity(native_member_inventory_path)["bytes"],
                "sha256": file_identity(native_member_inventory_path)["sha256"],
                "field_count": status["field_count"],
                "property_count": status["property_count"],
                "event_count": status["event_count"],
            },
            "checks": checks,
        }
        _private_json(Path(plan["outputs"]["validated_model"]), materializer)
    return {
        "schema": RUNTIME_TYPE_MATERIALIZER_VALIDATION_SCHEMA,
        "status": "validated" if validated else "rejected",
        "owner_count": status.get("resolved_owner_count", 0),
        "index_roundtrip_count": status.get("index_roundtrip_count", 0),
        "descriptor_roundtrip_count": status.get(
            "descriptor_roundtrip_count", 0
        ),
        "owner_embedded_descriptor_count": status.get(
            "owner_embedded_descriptor_count", 0
        ),
        "materialized_definition_count": status.get(
            "materialized_definition_count", 0
        ),
        "definition_embedded_descriptor_count": status.get(
            "definition_embedded_descriptor_count", 0
        ),
        "inventoried_type_count": status.get("inventoried_type_count", 0),
        "inventoried_method_count": status.get("inventoried_method_count", 0),
        "field_count": status.get("field_count", 0),
        "property_count": status.get("property_count", 0),
        "event_count": status.get("event_count", 0),
        "checks": checks,
        "raw_rvas_descriptors_and_runtime_pointers_owner_only": True,
        "validated_model": plan["outputs"]["validated_model"]
        if validated
        else None,
    }


import hashlib
import json
from pathlib import Path

from alpha.p12 import _wide_literal, _windows_z_path
from alpha.h01 import AcquisitionError
from alpha.p13 import _safe_path
from alpha.c04 import _verify_files
NH = _NATIVE_INVENTORY_HEADER
NT = _NATIVE_TYPE_RECORD
NM = _NATIVE_METHOD_RECORD
from alpha.h02 import file_identity, read_json


SCHEMA = "alpha.runtime-event-accessors/v1"
CHECKS = {
    "all_event_accessor_rows_closed": True,
    "accessors_reobserved_after_info_fill": True,
    "null_raise_distinguished_from_unresolved_method": True,
    "all_accessor_method_owners_replayed": True,
    "event_source_and_token_replayed": True,
    "original_observation_replayed": True,
    "source_files_unchanged": True,
}


def native_method_owners(raw, *, expected_sha256, executable_sha256, type_count, image_bytes):
    if not isinstance(raw, bytes) or hashlib.sha256(raw).hexdigest() != expected_sha256 or len(raw) < NH.size:
        raise AcquisitionError("event accessor native source digest or header differs")
    h = NH.unpack_from(raw)
    start = NH.size + type_count * NT.size
    pool = start + h[6] * NM.size
    if (h[:6] != (b"ALPHANI1", 1, NT.size, NM.size, 0, type_count) or
        h[7] != image_bytes or h[8] != executable_sha256.encode("ascii") or h[-1] or pool > len(raw)):
        raise AcquisitionError("event accessor native source layout differs")
    owners, cursor = {}, 0


    type_region = memoryview(raw)[NH.size:start]
    method_region = memoryview(raw)[start:pool]
    try:
        type_rows = list(NT.iter_unpack(type_region))
        method_rows = list(NM.iter_unpack(method_region))
    finally:
        type_region.release()
        method_region.release()
    for index, t in enumerate(type_rows):
        if t[0] != index or t[8] or t[9] != cursor or t[10] != pool or t[1] > len(raw) - pool or t[7] > h[6] - cursor:
            raise AcquisitionError("event accessor native type range differs")
        pool += t[1]
        for local in range(t[7]):
            row = method_rows[cursor]
            if row[:2] != (index, local) or not row[2] or row[2] in owners:
                raise AcquisitionError("event accessor native method owner or pointer differs")
            owners[row[2]] = (index, local, cursor)
            cursor += 1
    if cursor != h[6] or pool != len(raw):
        raise AcquisitionError("event accessor native source does not close")
    return owners


def project_event_accessors(*, observation, expected_binding, event_rows, method_owners):

    if (not isinstance(observation, dict) or set(observation) != {"schema", "binding", "rows"} or
        observation.get("schema") != SCHEMA or
        json.dumps(observation.get("binding"), sort_keys=True) != json.dumps(expected_binding, sort_keys=True)):
        raise AcquisitionError("event accessor observation identity or schema differs")
    rows = observation.get("rows")
    if not isinstance(rows, list) or len(rows) != len(event_rows):
        raise AcquisitionError("event accessor observation domain differs")
    raises = []
    for index, (sample, event) in enumerate(zip(rows, event_rows)):
        if (not isinstance(sample, list) or len(sample) != 14 or
            any(type(value) is not int or not 0 <= value < 1 << 64 for value in sample) or
            sample[:5] != [index, event[0], event[1], event[2], event[6]] or
            sample[5:7] != list(event[4:6]) or sample[5:9] != sample[9:13] or sample[13] != 1):
            raise AcquisitionError("event accessor source row or repeated sample differs")
        add, remove, raise_pointer, presence = sample[5:9]
        if not add or not remove or presence != (3 | (4 if raise_pointer else 0)):
            raise AcquisitionError("event accessor null/present evidence differs")
        for pointer in (add, remove, raise_pointer):
            if pointer and (pointer not in method_owners or method_owners[pointer][0] != event[0]):
                raise AcquisitionError("event accessor method is absent or outside its declaring owner")
        raises.append(raise_pointer)
    return tuple(raises)


def validate_event_accessor_files(*, observation_path, identity, inputs, event_path, type_count):
    from alpha.p24 import RUNTIME_EVENT_MODULE_HEADER as EH, RUNTIME_EVENT_MODULE_MODULE as EM, RUNTIME_EVENT_MODULE_EVENT as EE
    from alpha.c10 import ROLES, replay_owners
    source = {role: inputs["semantics" if role == "reflection_semantics" else role] for role in ROLES}
    observation_path = _safe_path(Path(observation_path))
    event_path = _safe_path(Path(event_path))
    records = dict(source, event_module_inventory=file_identity(event_path),
                   event_accessor_observation=file_identity(observation_path))
    _verify_files(records)
    binding = {key: identity[key] for key in ("executable_sha256", "process_id", "creation_filetime")}
    binding["inputs"] = {role: source[role]["sha256"] for role in ROLES}
    raw = event_path.read_bytes()
    if len(raw) < EH.size:
        raise AcquisitionError("event accessor display source is truncated")
    h = EH.unpack_from(raw)
    modules, events = replay_owners(identity_inventory=Path(source["type_identity_inventory"]["path"]).read_bytes(),
        native_member_inventory=Path(source["native_member_inventory"]["path"]).read_bytes(),
        expected_binding=binding, type_count=type_count, event_count=h[6],
        image_base=identity["image_base_owner_only"], image_bytes=identity["image_bytes"])
    start = EH.size + len(modules) * EM.size
    if (h[:7] != (b"ALPHAEM1", 1, EH.size, EM.size, EE.size, len(modules), len(events)) or
        h[8:12] != (identity["image_base_owner_only"], identity["image_bytes"], type_count, 0) or
        h[12:] != tuple(value.encode("ascii") for value in (identity["executable_sha256"],
            source["type_identity_inventory"]["sha256"], source["native_member_inventory"]["sha256"],
            source["native_semantics"]["sha256"])) or start + len(events) * EE.size + h[7] != len(raw)):
        raise AcquisitionError("event accessor display source binding differs")
    event_region = memoryview(raw)[start:start + len(events) * EE.size]
    try:
        event_rows = list(EE.iter_unpack(event_region))
    finally:
        event_region.release()
    if any(row[:3] != owner for row, owner in zip(event_rows, events)):
        raise AcquisitionError("event accessor event owner differs from native member source")
    owners = native_method_owners(Path(source["native_inventory"]["path"]).read_bytes(),
        expected_sha256=source["native_inventory"]["sha256"], executable_sha256=identity["executable_sha256"],
        type_count=type_count, image_bytes=identity["image_bytes"])
    raises = project_event_accessors(observation=read_json(observation_path), expected_binding=binding,
                                     event_rows=event_rows, method_owners=owners)
    _verify_files(records)
    return {"schema": SCHEMA, "identity": identity, "inputs": records,
        "counts": {"events": len(raises), "raise_present": sum(bool(value) for value in raises),
                   "raise_null_observed": sum(not value for value in raises)},
        "raise_pointers_owner_only": list(raises), "checks": dict(CHECKS),
        "event_flags_semantics_proven": False, "metadata_complete": False}


def load_event_accessors(*, model_path, expected_event_inventory, expected_type_identity):

    path = _safe_path(Path(model_path))
    model_record = file_identity(path)
    model = read_json(path)
    proof = model.get("event_accessors")
    if (not isinstance(proof, dict) or proof.get("schema") != SCHEMA or
        model.get("inventory") != expected_event_inventory or
        model.get("inputs", {}).get("type_identity_inventory") != expected_type_identity or
        not isinstance(proof.get("identity"), dict) or
        not isinstance(proof.get("inputs"), dict) or
        not isinstance(proof["inputs"].get("event_accessor_observation"), dict) or
        not isinstance(proof["inputs"]["event_accessor_observation"].get("path"), str) or
        type(model.get("counts", {}).get("type_count")) is not int):
        raise AcquisitionError("event accessor model or explicit source binding is absent")
    replayed = validate_event_accessor_files(
        observation_path=Path(proof["inputs"]["event_accessor_observation"]["path"]),
        identity=proof["identity"], inputs=model["inputs"], event_path=Path(expected_event_inventory["path"]),
        type_count=model["counts"]["type_count"])
    if json.dumps(replayed, sort_keys=True) != json.dumps(proof, sort_keys=True):
        raise AcquisitionError("event accessor normalized proof differs from original observation")
    _verify_files({"event_model": model_record, **replayed["inputs"]})
    return replayed


def bind_output_event_accessors(runtime, *, model_path, event_inventory, type_identity):
    proof = load_event_accessors(model_path=model_path, expected_event_inventory=event_inventory,
                                 expected_type_identity=type_identity)
    if (hashlib.sha256(runtime.events).hexdigest() != event_inventory["sha256"] or
        hashlib.sha256(runtime.identity).hexdigest() != type_identity["sha256"] or
        len(proof["raise_pointers_owner_only"]) != runtime.event_count):
        raise AcquisitionError("event accessor output runtime differs from explicitly selected sources")
    from alpha.p24 import RUNTIME_EVENT_MODULE_EVENT as EE
    for index, pointer in enumerate(proof["raise_pointers_owner_only"]):
        event = EE.unpack_from(runtime.events, runtime.event_start + index * EE.size)
        for value in (event[4], event[5], pointer):
            method = runtime.method_by_pointer.get(value) if value else None
            if value and (method is None or runtime.method_row(method)[0] != event[0]):
                raise AcquisitionError("event accessor output MethodDef correspondence differs")
    runtime.event_raise_pointers = tuple(proof["raise_pointers_owner_only"])
    return proof


def event_raise_pointer(runtime, index):
    pointers = getattr(runtime, "event_raise_pointers", None)
    if pointers is None or len(pointers) != runtime.event_count or not 0 <= index < len(pointers):
        raise AcquisitionError("event raise accessor evidence is absent; absence is not observed null")
    return pointers[index]


def event_local_accessor_indices(runtime, event, *, owner_start, owner_count, raise_pointer):
    result = []
    for pointer in (event[4], event[5], raise_pointer):
        if not pointer:
            result.append(-1)
            continue
        index = runtime.method_by_pointer.get(pointer)
        if (index is None or not owner_start <= index < owner_start + owner_count or
            runtime.method_row(index)[0] != event[0]):
            raise AcquisitionError("event accessor output method is absent or outside its owner")
        result.append(index - owner_start)
    return tuple(result)


def attach_event_accessors(source, *, binding, output_path):

    prefix = json.dumps({"schema": SCHEMA, "binding": binding}, separators=(",", ":"))[:-1] + ',"rows":['
    def once(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise AcquisitionError("event accessor composition seam differs")
        source = source.replace(old, new, 1)
    once("static int validate_event_token_order(void);", _NATIVE_RECORD + "\nstatic int validate_event_token_order(void);")
    once("uintptr_t observed_add=", "uintptr_t observed_raise=raise_object?method_pointer_from_object(raise_object):0;if(raise_object&&!observed_raise){failure_kind=14002u;failure_index=start+j+1;return 0;}uintptr_t observed_add=")
    once("completed_events++;", "if(!record_event_accessors(index,items[j],dst,observed_raise,!!raise_object)){failure_kind=14001u;failure_index=index+1;return 0;}completed_events++;")
    once("static void write_status(", _NATIVE_WRITER.replace("ACCESSOR_PATH", _wide_literal(_windows_z_path(Path(output_path))))
         .replace("ACCESSOR_PREFIX", json.dumps(prefix)) + "\nstatic void write_status(")
    once("int ok=write_raw_event_module_names()&&", "int ok=write_event_accessors()&&write_raw_event_module_names()&&")
    return source


_NATIVE_RECORD = r'''
static uint64_t *event_accessor_rows;
static int record_event_accessors(uint64_t index, uintptr_t object, output_event *event, uintptr_t raised, int raise_present) {
    if (index >= expected_event_count || expected_event_count > SIZE_MAX / (14u * sizeof(uint64_t))) return 0;
    if (!event_accessor_rows) event_accessor_rows = calloc((SIZE_T)expected_event_count * 14u, sizeof(uint64_t));
    if (!event_accessor_rows || event_accessor_rows[index * 14u + 13u]) return 0;
    if (!!raise_present != !!raised) return 0;
    instance_boolarg getters[3] = {(instance_boolarg)event_add_method_pointer,
        (instance_boolarg)event_remove_method_pointer, (instance_boolarg)event_raise_method_pointer};
    uintptr_t metadata[3] = {event_add_method_metadata, event_remove_method_metadata, event_raise_method_metadata};
    uint64_t repeated[3] = {0}; uint64_t presence = 0;
    for (uint32_t i = 0; i < 3u; i++) {
        uintptr_t current = getters[i](object, 1u, metadata[i]);
        if (current) { presence |= 1u << i; repeated[i] = method_pointer_from_object(current); if (!repeated[i]) return 0; }
    }
    uint64_t first_presence = 3u | (raise_present ? 4u : 0u);
    if (presence != first_presence || repeated[0] != event->add_pointer ||
        repeated[1] != event->remove_pointer || repeated[2] != raised) return 0;
    uint64_t *row = event_accessor_rows + index * 14u;
    row[0] = index; row[1] = event->type_index; row[2] = event->member_index;
    row[3] = event->member_pointer; row[4] = event->metadata_token;
    row[5] = event->add_pointer; row[6] = event->remove_pointer; row[7] = raised; row[8] = first_presence;
    row[9] = repeated[0]; row[10] = repeated[1]; row[11] = repeated[2]; row[12] = presence;
    row[13] = 1u; return 1;
}
'''

_NATIVE_WRITER = r'''
static int write_event_accessors(void) {
    if (completed_events != expected_event_count || (expected_event_count && !event_accessor_rows)) return 0;
    static const wchar_t path[] = ACCESSOR_PATH;
    FILE *out = open_private_output(path); if (!out) return 0;
    int ok = fputs(ACCESSOR_PREFIX, out) >= 0;
    for (uint64_t i = 0; ok && i < expected_event_count; i++) {
        if (event_accessor_rows[i * 14u + 13u] != 1u) { ok = 0; break; }
        if (fputs(i ? ",[" : "[", out) < 0) { ok = 0; break; }
        for (uint32_t j = 0; ok && j < 14u; j++)
            ok = fprintf(out, j ? ",%llu" : "%llu", (unsigned long long)event_accessor_rows[i * 14u + j]) >= 0;
        if (ok) ok = fputc(']', out) != EOF;
    }
    if (ok) ok = fputs("]}\n", out) >= 0;
    if (fclose(out)) ok = 0;
    if (!ok) _wremove(path);
    return ok;
}
'''
