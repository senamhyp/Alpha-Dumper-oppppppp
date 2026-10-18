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
from alpha.h01 import (
    AcquisitionError,
    owner_only_path_bits,
    owner_uid,
    same_executable_path,
)
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p30 import RUNTIME_CONSTRUCTED_METHOD_CLASS, RUNTIME_CONSTRUCTED_METHOD_HEADER, RUNTIME_CONSTRUCTED_METHOD_MAGIC, RUNTIME_CONSTRUCTED_METHOD_RECORD, RUNTIME_CONSTRUCTED_METHOD_SCHEMA, RUNTIME_CONSTRUCTED_METHOD_VERSION
from alpha.p22 import RUNTIME_METHOD_DETAIL_HEADER, RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_METHOD, RUNTIME_METHOD_DETAIL_PARAMETER, RUNTIME_METHOD_DETAIL_SCHEMA, RUNTIME_METHOD_DETAIL_VERSION
from alpha.c04 import MappedPE
from alpha.p21 import RUNTIME_TYPE_GRAPH_HEADER, RUNTIME_TYPE_GRAPH_MAGIC, RUNTIME_TYPE_GRAPH_RECORD, RUNTIME_TYPE_GRAPH_SCHEMA, RUNTIME_TYPE_GRAPH_VERSION
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA, _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_RECORD, RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION, TYPE_REFERENCE_INTERFACE, TYPE_REFERENCE_VALUE_TYPE
from alpha.p32 import RUNTIME_VTABLE_INTERFACE_HEADER, RUNTIME_VTABLE_INTERFACE_MAGIC, RUNTIME_VTABLE_INTERFACE_OFFSET, RUNTIME_VTABLE_INTERFACE_RECORD, RUNTIME_VTABLE_INTERFACE_SCHEMA, RUNTIME_VTABLE_INTERFACE_VERSION
from alpha.h02 import atomic_write_json, file_identity, read_json


RUNTIME_INTERFACE_METHOD_MAP_SCHEMA = (
    "alpha.runtime-interface-method-map-inventory/v1"
)
RUNTIME_INTERFACE_METHOD_MAP_STATUS_SCHEMA = (
    "alpha.runtime-interface-method-map-inventory-status/v1"
)
RUNTIME_INTERFACE_METHOD_MAP_MAGIC = b"ALPHAIM1"
RUNTIME_INTERFACE_METHOD_MAP_VERSION = 1
RUNTIME_INTERFACE_METHOD_MAP_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQQQ64s64s64s64s64s64s64s"
)
RUNTIME_INTERFACE_METHOD_MAP_PAIR = struct.Struct("<QIIIIQ")
RUNTIME_INTERFACE_METHOD_MAP_ENTRY = struct.Struct("<IIQQ")

_SEED_MAGIC = b"ALPHAIS1"
_SEED_VERSION = 1
_SEED_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQQQ64s64s64s64s64s64s64s"
)
_SEED_PAIR = struct.Struct("<QQQIIII")
_SEED_METHOD = struct.Struct("<QII")
_PREFLIGHT_REQUIRED = 32
_ARRAY_QWORD_LIMIT = 10
_WRAPPER_QWORD_LIMIT = 8

_REQUIRED_OPERATIONS = (
    "type.interfaces",
    "type.generic_definition",
    "type.element_type",
    "type.declaring_type",
)


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime interface method map {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime interface method map {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime interface method map {label} digest is invalid"
        )
    return value


def _validated_model(
    *,
    model_path: Path,
    inventory_path: Path,
    schema: str,
    executable_sha256: str,
    label: str,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    model_path = _owner_file(model_path, label=f"{label} model")
    inventory_path = _owner_file(inventory_path, label=f"{label} inventory")
    model = read_json(model_path)
    inventory = file_identity(inventory_path)
    if (
        not isinstance(model, dict)
        or model.get("schema") != schema
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or model.get(
            "inventory", model.get("identity_inventory")
        )
        != inventory
        or not model.get("checks")
        or not all(model["checks"].values())
    ):
        raise AcquisitionError(
            f"runtime interface method map {label} binding is stale"
        )
    return model, file_identity(model_path), inventory


def _reference_rows(raw: bytes) -> tuple[tuple[int, ...], dict[int, tuple[int, ...]]]:
    if len(raw) < RUNTIME_TYPE_REFERENCE_HEADER.size:
        raise AcquisitionError(
            "runtime interface method map type references are truncated"
        )
    header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(raw)
    end = (
        RUNTIME_TYPE_REFERENCE_HEADER.size
        + header[5] * RUNTIME_TYPE_REFERENCE_RECORD.size
        + (header[7] + header[8]) * 8
        + header[9]
    )
    if (
        header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or header[2] != RUNTIME_TYPE_REFERENCE_HEADER.size
        or header[3] != RUNTIME_TYPE_REFERENCE_RECORD.size
        or header[4]
        or end != len(raw)
    ):
        raise AcquisitionError(
            "runtime interface method map type reference header is invalid"
        )
    rows: dict[int, tuple[int, ...]] = {}
    for index in range(header[5]):
        row = RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
            raw,
            RUNTIME_TYPE_REFERENCE_HEADER.size
            + index * RUNTIME_TYPE_REFERENCE_RECORD.size,
        )
        if not row[0] or row[0] in rows:
            raise AcquisitionError(
                "runtime interface method map type reference row is invalid"
            )
        rows[row[0]] = row
    return header, rows


def _method_rows(raw: bytes) -> tuple[tuple[int, ...], list[tuple[int, ...]], int]:
    if len(raw) < RUNTIME_METHOD_DETAIL_HEADER.size:
        raise AcquisitionError(
            "runtime interface method map method input is truncated"
        )
    header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(raw)
    parameter_start = (
        RUNTIME_METHOD_DETAIL_HEADER.size
        + header[5] * RUNTIME_METHOD_DETAIL_METHOD.size
    )
    strings_start = (
        parameter_start
        + header[6] * RUNTIME_METHOD_DETAIL_PARAMETER.size
    )
    if (
        header[0] != RUNTIME_METHOD_DETAIL_MAGIC
        or header[1] != RUNTIME_METHOD_DETAIL_VERSION
        or header[2] != RUNTIME_METHOD_DETAIL_HEADER.size
        or header[3] != RUNTIME_METHOD_DETAIL_METHOD.size
        or header[4] != RUNTIME_METHOD_DETAIL_PARAMETER.size
        or strings_start + header[7] != len(raw)
    ):
        raise AcquisitionError(
            "runtime interface method map method header is invalid"
        )
    rows = [
        RUNTIME_METHOD_DETAIL_METHOD.unpack_from(
            raw,
            RUNTIME_METHOD_DETAIL_HEADER.size
            + index * RUNTIME_METHOD_DETAIL_METHOD.size,
        )
        for index in range(header[5])
    ]
    if any(row[1] != index or not row[2] for index, row in enumerate(rows)):
        raise AcquisitionError(
            "runtime interface method map MethodDef row is invalid"
        )
    return header, rows, parameter_start


def _interface_map_call_shape(
    image: MappedPE, method_pointer: int, *, runtime_image_base: int | None = None
) -> tuple[int, int] | None:

    runtime_base = image.image_base if runtime_image_base is None else runtime_image_base
    method_rva = method_pointer - runtime_base
    function = image.containing_function(method_rva)
    if function is None or function.begin_rva != method_rva:
        return None
    bounds = image.bounded_code(function.begin_rva, function.end_rva)
    if bounds is None:
        return None
    begin, end = bounds
    code = bytes(image._mapping[begin:end])
    from alpha.c01 import discover_interface_map_calls

    matches: list[tuple[int, int]] = []
    for call, relative_target in discover_interface_map_calls(code):
        target = method_pointer + relative_target
        if image.executable_rva(target - runtime_base):
            matches.append((call, target))
    return matches[0] if len(matches) == 1 else None


def _derive_interface_map_contract(
    *,
    binary: Path,
    semantics: dict[str, Any],
    method_raw: bytes,
    method_header: tuple[int, ...],
    methods: list[tuple[int, ...]],
    parameter_start: int,
    references: dict[int, tuple[int, ...]],
) -> dict[str, int]:
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
    }
    if set(_REQUIRED_OPERATIONS) - set(operations) or any(
        operations[key].get("semantic_identity_resolved") is not True
        or not isinstance(operations[key].get("metadata_pointer"), int)
        for key in _REQUIRED_OPERATIONS
    ):
        raise AcquisitionError(
            "runtime interface method map reflection operations are incomplete"
        )
    by_metadata = {row[2]: row for row in methods}
    try:
        runtime_owner = by_metadata[
            operations["type.interfaces"]["metadata_pointer"]
        ][0]
        type_descriptors = {
            by_metadata[operations[key]["metadata_pointer"]][4]
            for key in (
                "type.generic_definition",
                "type.element_type",
                "type.declaring_type",
            )
        }
    except KeyError as error:
        raise AcquisitionError(
            "runtime interface method map reflection MethodDef is absent"
        ) from error
    canonical_types = {
        references[descriptor][1]
        for descriptor in type_descriptors
        if descriptor in references
    }
    if len(type_descriptors) != 1 or len(canonical_types) != 1:
        raise AcquisitionError(
            "runtime interface method map Type signature is ambiguous"
        )
    type_descriptor = next(iter(canonical_types))
    candidates: list[tuple[int, tuple[int, ...]]] = []
    for index, row in enumerate(methods):
        if (
            row[0] != runtime_owner
            or row[5] & 0x10
            or row[10] != 1
            or row[11] >= method_header[6]
        ):
            continue
        parameter = RUNTIME_METHOD_DETAIL_PARAMETER.unpack_from(
            method_raw,
            parameter_start
            + row[11] * RUNTIME_METHOD_DETAIL_PARAMETER.size,
        )
        parameter_type = references.get(parameter[2])
        return_type = references.get(row[4])
        if (
            parameter_type is not None
            and parameter_type[1] == type_descriptor
            and return_type is not None
            and return_type[4] & TYPE_REFERENCE_VALUE_TYPE
        ):
            candidates.append((index, row))
    shaped: list[tuple[int, tuple[int, ...], int, int]] = []
    with MappedPE(binary) as image:
        for index, row in candidates:
            result = _interface_map_call_shape(
                image, row[3], runtime_image_base=method_header[8]
            )
            if result is None:
                continue
            call_offset, target = result
            shaped.append((index, row, call_offset, target))
        if len(shaped) != 1:
            raise AcquisitionError(
                "runtime interface method map ABI candidate is not unique "
                f"(signature={len(candidates)}, shaped={len(shaped)})"
            )
        index, row, call_offset, helper = shaped[0]
        helper_rva = helper - method_header[8]
        if not image.executable_rva(helper_rva):
            raise AcquisitionError(
                "runtime interface method map helper is not executable"
            )
    return {
        "method_index": index,
        "method_metadata": row[2],
        "method_pointer": row[3],
        "runtime_owner_definition_index": runtime_owner,
        "type_descriptor": type_descriptor,
        "signature_candidate_count": len(candidates),
        "abi_candidate_count": len(shaped),
        "direct_call_byte_offset": call_offset,
        "helper_rva": helper_rva,
    }


def _binding(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    type_graph_model: Path,
    type_graph_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    vtable_interface_model: Path,
    vtable_interface_inventory: Path,
    constructed_method_model: Path,
    constructed_method_inventory: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    binary_identity = file_identity(binary)
    executable_sha256 = binary_identity["sha256"]
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantics"
    )
    semantics = read_json(semantics_path)
    if (
        not isinstance(semantics, dict)
        or semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary") != binary_identity
        or semantics.get("checks", {}).get("all_operations_resolved")
        is not True
        or semantics.get("checks", {}).get("fixed_rva_used") is not False
        or semantics.get("checks", {}).get("fixed_offset_used") is not False
    ):
        raise AcquisitionError(
            "runtime interface method map reflection binding is stale"
        )
    identity_model_data, identity_model_id, identity_id = _validated_model(
        model_path=type_identity_model,
        inventory_path=type_identity_inventory,
        schema=RUNTIME_TYPE_IDENTITY_SCHEMA,
        executable_sha256=executable_sha256,
        label="type identity",
    )
    graph_model_data, graph_model_id, graph_id = _validated_model(
        model_path=type_graph_model,
        inventory_path=type_graph_inventory,
        schema=RUNTIME_TYPE_GRAPH_SCHEMA,
        executable_sha256=executable_sha256,
        label="type graph",
    )
    reference_model_data, reference_model_id, reference_id = _validated_model(
        model_path=type_reference_model,
        inventory_path=type_reference_inventory,
        schema=RUNTIME_TYPE_REFERENCE_SCHEMA,
        executable_sha256=executable_sha256,
        label="type reference",
    )
    method_model_data, method_model_id, method_id = _validated_model(
        model_path=method_detail_model,
        inventory_path=method_detail_inventory,
        schema=RUNTIME_METHOD_DETAIL_SCHEMA,
        executable_sha256=executable_sha256,
        label="method detail",
    )
    vtable_model_data, vtable_model_id, vtable_id = _validated_model(
        model_path=vtable_interface_model,
        inventory_path=vtable_interface_inventory,
        schema=RUNTIME_VTABLE_INTERFACE_SCHEMA,
        executable_sha256=executable_sha256,
        label="vtable/interface",
    )
    constructed_model_data, constructed_model_id, constructed_id = (
        _validated_model(
            model_path=constructed_method_model,
            inventory_path=constructed_method_inventory,
            schema=RUNTIME_CONSTRUCTED_METHOD_SCHEMA,
            executable_sha256=executable_sha256,
            label="constructed method",
        )
    )
    expected_inputs = {
        "type_identity_inventory": identity_id,
        "type_graph_inventory": graph_id,
        "type_reference_inventory": reference_id,
        "method_detail_inventory": method_id,
    }
    if (
        graph_model_data.get("inputs", {}).get("type_identity_inventory")
        != identity_id
        or reference_model_data.get("inputs", {}).get(
            "type_identity_inventory"
        )
        != identity_id
        or reference_model_data.get("inputs", {}).get("type_graph_inventory")
        != graph_id
        or method_model_data.get("inputs", {}).get(
            "type_identity_inventory"
        )
        != identity_id
        or any(
            vtable_model_data.get("inputs", {}).get(key) != value
            for key, value in expected_inputs.items()
        )
        or constructed_model_data.get("inputs", {}).get(
            "method_detail_inventory"
        )
        != method_id
        or constructed_model_data.get("inputs", {}).get(
            "type_identity_inventory"
        )
        != identity_id
    ):
        raise AcquisitionError(
            "runtime interface method map input graph is inconsistent"
        )

    identity_raw = Path(identity_id["path"]).read_bytes()
    graph_raw = Path(graph_id["path"]).read_bytes()
    reference_raw = Path(reference_id["path"]).read_bytes()
    method_raw = Path(method_id["path"]).read_bytes()
    vtable_raw = Path(vtable_id["path"]).read_bytes()
    constructed_raw = Path(constructed_id["path"]).read_bytes()
    if len(identity_raw) < _IDENTITY_HEADER.size:
        raise AcquisitionError(
            "runtime interface method map identity input is truncated"
        )
    identity_header = _IDENTITY_HEADER.unpack_from(identity_raw)
    graph_header = RUNTIME_TYPE_GRAPH_HEADER.unpack_from(graph_raw)
    reference_header, references = _reference_rows(reference_raw)
    method_header, methods, parameter_start = _method_rows(method_raw)
    vtable_header = RUNTIME_VTABLE_INTERFACE_HEADER.unpack_from(vtable_raw)
    constructed_header = RUNTIME_CONSTRUCTED_METHOD_HEADER.unpack_from(
        constructed_raw
    )
    type_count = identity_header[5]
    process_id = vtable_header[8]
    if (
        identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or identity_header[2] != _IDENTITY_HEADER.size
        or identity_header[3] != _IDENTITY_RECORD.size
        or graph_header[0] != RUNTIME_TYPE_GRAPH_MAGIC
        or graph_header[1] != RUNTIME_TYPE_GRAPH_VERSION
        or graph_header[2] != RUNTIME_TYPE_GRAPH_HEADER.size
        or graph_header[3] != RUNTIME_TYPE_GRAPH_RECORD.size
        or graph_header[5] != type_count
        or reference_header[10] != identity_header[6]
        or reference_header[11] != identity_header[7]
        or method_header[8] != identity_header[6]
        or method_header[9] != identity_header[7]
        or vtable_header[0] != RUNTIME_VTABLE_INTERFACE_MAGIC
        or vtable_header[1] != RUNTIME_VTABLE_INTERFACE_VERSION
        or vtable_header[2] != RUNTIME_VTABLE_INTERFACE_HEADER.size
        or vtable_header[3] != RUNTIME_VTABLE_INTERFACE_RECORD.size
        or vtable_header[5] != type_count
        or constructed_header[0] != RUNTIME_CONSTRUCTED_METHOD_MAGIC
        or constructed_header[1] != RUNTIME_CONSTRUCTED_METHOD_VERSION
        or constructed_header[2] != RUNTIME_CONSTRUCTED_METHOD_HEADER.size
        or constructed_header[3] != RUNTIME_CONSTRUCTED_METHOD_CLASS.size
        or constructed_header[4] != RUNTIME_CONSTRUCTED_METHOD_RECORD.size
        or constructed_header[7] != process_id
        or constructed_header[8] != identity_header[6]
        or constructed_header[9] != identity_header[7]
        or process_id <= 0
        or vtable_model_data.get("target", {}).get("process_id")
        != process_id
        or constructed_model_data.get("target", {}).get("process_id")
        != process_id
        or _digest(identity_header[9], label="identity executable")
        != executable_sha256
        or _digest(method_header[12], label="method executable")
        != executable_sha256
        or _digest(vtable_header[11], label="vtable executable")
        != executable_sha256
        or _digest(constructed_header[11], label="constructed executable")
        != executable_sha256
    ):
        raise AcquisitionError(
            "runtime interface method map input headers are inconsistent"
        )

    identities = [
        _IDENTITY_RECORD.unpack_from(
            identity_raw,
            _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size,
        )
        for index in range(type_count)
    ]
    canonical_to_definitions: dict[int, list[int]] = defaultdict(list)
    for index, row in enumerate(identities):
        reference = references.get(row[2])
        if row[0] != index or reference is None:
            raise AcquisitionError(
                "runtime interface method map identity relation is invalid"
            )
        canonical_to_definitions[reference[1]].append(index)

    def definition_for(descriptor: int) -> int:
        reference = references.get(descriptor)
        if reference is None:
            raise AcquisitionError(
                "runtime interface method map interface type is absent"
            )
        definition_descriptor = reference[14] or reference[1]
        definition_reference = references.get(definition_descriptor)
        canonical = (
            definition_reference[1]
            if definition_reference is not None
            else definition_descriptor
        )
        values = canonical_to_definitions.get(canonical, [])
        if len(values) != 1:
            raise AcquisitionError(
                "runtime interface method map interface definition is ambiguous"
            )
        return values[0]

    methods_by_owner: dict[int, list[int]] = defaultdict(list)
    metadata_map: dict[int, tuple[int, int]] = {}
    for index, row in enumerate(methods):
        if row[0] >= type_count or row[2] in metadata_map:
            raise AcquisitionError(
                "runtime interface method map native metadata domain conflicts"
            )
        metadata_map[row[2]] = (index, row[0])
        methods_by_owner[row[0]].append(index)
    constructed_classes_end = (
        RUNTIME_CONSTRUCTED_METHOD_HEADER.size
        + constructed_header[5] * RUNTIME_CONSTRUCTED_METHOD_CLASS.size
    )
    if (
        constructed_classes_end
        + constructed_header[6] * RUNTIME_CONSTRUCTED_METHOD_RECORD.size
        != len(constructed_raw)
    ):
        raise AcquisitionError(
            "runtime interface method map constructed methods are truncated"
        )
    for index in range(constructed_header[6]):
        row = RUNTIME_CONSTRUCTED_METHOD_RECORD.unpack_from(
            constructed_raw,
            constructed_classes_end
            + index * RUNTIME_CONSTRUCTED_METHOD_RECORD.size,
        )
        method_index = row[1]
        if (
            method_index >= len(methods)
            or row[0] in metadata_map
            or not row[0]
        ):
            raise AcquisitionError(
                "runtime interface method map inflated metadata domain conflicts"
            )
        metadata_map[row[0]] = (method_index, methods[method_index][0])

    records_end = (
        RUNTIME_VTABLE_INTERFACE_HEADER.size
        + vtable_header[5] * RUNTIME_VTABLE_INTERFACE_RECORD.size
    )
    interface_start = records_end + vtable_header[6] * 8
    if (
        interface_start
        + vtable_header[7] * RUNTIME_VTABLE_INTERFACE_OFFSET.size
        != len(vtable_raw)
    ):
        raise AcquisitionError(
            "runtime interface method map vtable input is truncated"
        )
    pairs: list[tuple[int, ...]] = []
    interface_cursor = 0
    for target_index in range(type_count):
        vtable_row = RUNTIME_VTABLE_INTERFACE_RECORD.unpack_from(
            vtable_raw,
            RUNTIME_VTABLE_INTERFACE_HEADER.size
            + target_index * RUNTIME_VTABLE_INTERFACE_RECORD.size,
        )
        if vtable_row[6] != interface_cursor:
            raise AcquisitionError(
                "runtime interface method map interface starts are invalid"
            )
        target_object = identities[target_index][6]
        if not target_object:
            raise AcquisitionError(
                "runtime interface method map target Type object is absent"
            )
        for local_index in range(vtable_row[2]):
            descriptor, offset, reserved = (
                RUNTIME_VTABLE_INTERFACE_OFFSET.unpack_from(
                    vtable_raw,
                    interface_start
                    + (interface_cursor + local_index)
                    * RUNTIME_VTABLE_INTERFACE_OFFSET.size,
                )
            )
            reference = references.get(descriptor)
            interface_definition = definition_for(descriptor)
            if (
                reserved
                or reference is None
                or not reference[2]
                or not reference[4] & TYPE_REFERENCE_INTERFACE
                or not identities[interface_definition][7] & 0x20
                or offset > vtable_row[1]
            ):
                raise AcquisitionError(
                    "runtime interface method map interface pair is invalid "
                    f"(target={target_index}, local={local_index}, "
                    f"descriptor={descriptor:#x}, offset={offset}, "
                    f"definition={interface_definition}, "
                    f"shape={reference[4] if reference else None}, "
                    f"type_object={reference[2] if reference else 0:#x})"
                )
            own_virtual_count = sum(
                methods[index][8] != 0xFFFF
                for index in methods_by_owner[interface_definition]
            )
            pairs.append(
                (
                    target_object,
                    reference[2],
                    descriptor,
                    target_index,
                    interface_definition,
                    offset,
                    own_virtual_count,
                )
            )
        interface_cursor += vtable_row[2]
    if interface_cursor != vtable_header[7] or not pairs:
        raise AcquisitionError(
            "runtime interface method map pair domain is incomplete"
        )

    contract = _derive_interface_map_contract(
        binary=binary,
        semantics=semantics,
        method_raw=method_raw,
        method_header=method_header,
        methods=methods,
        parameter_start=parameter_start,
        references=references,
    )
    return {
        "binary": binary_identity,
        "reflection_semantics": file_identity(semantics_path),
        "type_identity_model": identity_model_id,
        "type_identity_inventory": identity_id,
        "type_graph_model": graph_model_id,
        "type_graph_inventory": graph_id,
        "type_reference_model": reference_model_id,
        "type_reference_inventory": reference_id,
        "method_detail_model": method_model_id,
        "method_detail_inventory": method_id,
        "vtable_interface_model": vtable_model_id,
        "vtable_interface_inventory": vtable_id,
        "constructed_method_model": constructed_model_id,
        "constructed_method_inventory": constructed_id,
        "process_id": process_id,
        "image_base": identity_header[6],
        "image_bytes": identity_header[7],
        "type_count": type_count,
        "pairs": pairs,
        "metadata_map": sorted(
            (pointer, method_index, owner)
            for pointer, (method_index, owner) in metadata_map.items()
        ),
        "interface_map_contract": contract,
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define HASH_CHUNK (1024u*1024u)
#define BATCH_PAIRS 256u
#define ARRAY_QWORD_LIMIT $array_qword_limit
#define WRAPPER_QWORD_LIMIT $wrapper_qword_limit
typedef struct seed_header{char magic[8];uint32_t version,header_bytes,pair_bytes,method_bytes;uint64_t pair_count,method_count,process_id,image_base,image_bytes,helper_rva,map_method_index,map_method_metadata,preflight_required;char executable[64],identity[64],graph[64],references[64],methods[64],vtable[64],constructed[64];}seed_header;
typedef struct seed_pair{uint64_t target_object,interface_object,interface_descriptor;uint32_t target_definition,interface_definition,offset,expected_own_methods;}seed_pair;
typedef struct seed_method{uint64_t metadata;uint32_t method_index,owner;}seed_method;
typedef struct output_header{char magic[8];uint32_t version,header_bytes,pair_bytes,mapping_bytes;uint64_t pair_count,mapping_count,process_id,image_base,image_bytes,helper_rva,wrapper_qword,array_length_qword,array_vector_qword;char executable[64],identity[64],graph[64],references[64],methods[64],vtable[64],constructed[64];}output_header;
typedef struct output_pair{uint64_t interface_descriptor;uint32_t target_definition,interface_definition,offset,method_count;uint64_t mapping_start;}output_pair;
typedef struct output_mapping{uint32_t interface_method,target_method;uint64_t interface_metadata,target_metadata;}output_mapping;
typedef struct observation{output_pair*pairs;output_mapping*mappings;uint64_t mapping_count,mapping_capacity,zero_pairs;}observation;
_Static_assert(sizeof(seed_header)==$seed_header_bytes,"seed header");_Static_assert(sizeof(seed_pair)==$seed_pair_bytes,"seed pair");_Static_assert(sizeof(seed_method)==$seed_method_bytes,"seed method");_Static_assert(sizeof(output_header)==$output_header_bytes,"output header");_Static_assert(sizeof(output_pair)==$output_pair_bytes,"output pair");_Static_assert(sizeof(output_mapping)==$output_mapping_bytes,"output mapping");
static const wchar_t seed_path[]=$seed_path,output_path[]=$output_path,status_path[]=$status_path;static const char expected_seed_sha256[]="$seed_sha256";static seed_header*h;static seed_pair*pairs;static seed_method*method_map;static uint32_t failure_kind;static uint64_t failure_index;static uint32_t selected_length_qword,selected_vector_qword,selected_wrapper_qword,selected_orientation,layout_candidates,layout_samples,orientation_samples;static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_action,callback_complete;static uint64_t capture_index;static observation*active_observation;
typedef void(*interface_map_fn)(uintptr_t,uintptr_t,uintptr_t*,uintptr_t*);
typedef struct observation_evidence { const wchar_t *path; const char *sha256; } observation_evidence;
static const observation_evidence upstream_observations[] = {
$observation_evidence
};
static uint64_t process_creation_filetime;
static int upstream_freshness_verified;
static int readable(uintptr_t p,SIZE_T n){MEMORY_BASIC_INFORMATION m;if(!p||!n||p+n<p||!VirtualQuery((void*)p,&m,sizeof(m))||m.State!=MEM_COMMIT||(m.Protect&(PAGE_NOACCESS|PAGE_GUARD)))return 0;DWORD q=m.Protect&0xffu;if(q!=PAGE_READONLY&&q!=PAGE_READWRITE&&q!=PAGE_WRITECOPY&&q!=PAGE_EXECUTE_READ&&q!=PAGE_EXECUTE_READWRITE&&q!=PAGE_EXECUTE_WRITECOPY)return 0;return p+n<=(uintptr_t)m.BaseAddress+m.RegionSize;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*p,char o[65]){HANDLE f=CreateFileW(p,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE x=NULL;DWORD z=0,g=0;unsigned char d[32],*b=NULL,*q=NULL;int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&z,sizeof(z),&g,0)>=0;if(ok)b=HeapAlloc(GetProcessHeap(),0,z);if(ok)q=HeapAlloc(GetProcessHeap(),0,HASH_CHUNK);if(ok&&(!b||!q))ok=0;if(ok&&BCryptCreateHash(a,&x,b,z,NULL,0,0)<0)ok=0;while(ok){DWORD n=0;if(!ReadFile(f,q,HASH_CHUNK,&n,NULL)){ok=0;break;}if(!n)break;if(BCryptHashData(x,q,n,0)<0)ok=0;}if(ok&&BCryptFinishHash(x,d,sizeof(d),0)<0)ok=0;if(ok)digest_hex(d,o);if(x)BCryptDestroyHash(x);if(a)BCryptCloseAlgorithmProvider(a,0);if(b)HeapFree(GetProcessHeap(),0,b);if(q)HeapFree(GetProcessHeap(),0,q);CloseHandle(f);return ok;}
static int executable_identity(char o[65]){wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,32768);return n&&n<32768&&sha256_file(p,o);}
static uint64_t filetime_value(FILETIME value) {
    return ((uint64_t)value.dwHighDateTime << 32) | value.dwLowDateTime;
}
static int upstream_observations_current(void) {
    FILETIME created, exited, kernel, user;
    if (!GetProcessTimes(GetCurrentProcess(), &created, &exited, &kernel, &user))
        return 0;
    uint64_t current_creation = filetime_value(created);
    if (!current_creation || (process_creation_filetime &&
                             process_creation_filetime != current_creation)) return 0;
    process_creation_filetime = current_creation;
    for (SIZE_T i = 0; i < sizeof(upstream_observations) / sizeof(upstream_observations[0]); i++) {
        WIN32_FILE_ATTRIBUTE_DATA before, after;
        char digest[65];
        const observation_evidence *e = &upstream_observations[i];
        if (!GetFileAttributesExW(e->path, GetFileExInfoStandard, &before) ||
            filetime_value(before.ftLastWriteTime) < current_creation ||
            !sha256_file(e->path, digest) || strcmp(digest, e->sha256) ||
            !GetFileAttributesExW(e->path, GetFileExInfoStandard, &after) ||
            filetime_value(before.ftLastWriteTime) != filetime_value(after.ftLastWriteTime) ||
            before.nFileSizeHigh != after.nFileSizeHigh ||
            before.nFileSizeLow != after.nFileSizeLow) return 0;
    }
    upstream_freshness_verified = 1;
    return 1;
}
static int read_all(const wchar_t*p,uint8_t**d,SIZE_T*n){FILE*f=_wfopen(p,L"rb");if(!f)return 0;if(_fseeki64(f,0,SEEK_END)||(*n=(SIZE_T)_ftelli64(f))==0||_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*d=malloc(*n);int ok=*d&&fread(*d,1,*n,f)==*n&&!fclose(f);if(!ok){free(*d);*d=NULL;}return ok;}
static const seed_method*lookup(uint64_t metadata){uint64_t lo=0,hi=h->method_count;while(lo<hi){uint64_t m=lo+(hi-lo)/2u;if(method_map[m].metadata<metadata)lo=m+1u;else hi=m;}return lo<h->method_count&&method_map[lo].metadata==metadata?&method_map[lo]:NULL;}
static const seed_method*object_method(uintptr_t object,uint32_t qword){uint64_t value=0;if(!readable(object,(SIZE_T)(qword+1u)*8u))return NULL;memcpy(&value,(const void*)(object+(uintptr_t)qword*8u),8u);return lookup(value);}


static int array_view_at(uintptr_t object, uint32_t lq, uint32_t vq,
                         uint64_t *count, uintptr_t *vector) {
    *count = 0;
    *vector = 0;
    if (lq >= ARRAY_QWORD_LIMIT || vq >= ARRAY_QWORD_LIMIT || vq <= lq ||
        object > UINTPTR_MAX - (uintptr_t)vq * 8u ||
        !readable(object, (SIZE_T)(lq + 1u) * 8u)) return 0;
    memcpy(count, (const void *)(object + (uintptr_t)lq * 8u), 8u);
    *vector = object + (uintptr_t)vq * 8u;
    return *count <= 4096u &&
        (!*count || readable(*vector, (SIZE_T)*count * 8u));
}
static int candidate_arrays(uintptr_t first, uintptr_t second,
                            uint32_t lq, uint32_t vq, uint32_t wq) {
    uint64_t n1 = 0, n2 = 0;
    uintptr_t v1 = 0, v2 = 0;
    if (wq >= WRAPPER_QWORD_LIMIT ||
        !array_view_at(first, lq, vq, &n1, &v1) ||
        !array_view_at(second, lq, vq, &n2, &v2) || !n1 || n1 != n2)
        return 0;
    for (uint64_t i = 0; i < n1; i++) {
        uintptr_t a = 0, b = 0;
        memcpy(&a, (const void *)(v1 + i * 8u), 8u);
        memcpy(&b, (const void *)(v2 + i * 8u), 8u);
        if (!object_method(a, wq) || !object_method(b, wq)) return 0;
    }
    return 1;
}
static int array_view(uintptr_t object, uint64_t *count, uintptr_t *vector) {
    return array_view_at(object, selected_length_qword,
                         selected_vector_qword, count, vector);
}
static int call_pair(uint64_t index,uintptr_t*first,uintptr_t*second){seed_pair*p=&pairs[index];*first=0;*second=0;interface_map_fn map=(interface_map_fn)(uintptr_t)(h->image_base+h->helper_rva);map((uintptr_t)p->target_object,(uintptr_t)p->interface_object,first,second);return *first&&*second;}
static int derive_layout(void){uint8_t active[ARRAY_QWORD_LIMIT][ARRAY_QWORD_LIMIT][WRAPPER_QWORD_LIMIT];memset(active,1,sizeof(active));uint32_t samples=0;for(uint64_t i=0;i<h->pair_count&&samples<h->preflight_required;i++){if(!pairs[i].expected_own_methods)continue;uintptr_t first=0,second=0;if(!call_pair(i,&first,&second)){failure_kind=10u;failure_index=i+1u;return 0;}int usable=0;for(uint32_t l=0;l<ARRAY_QWORD_LIMIT;l++)for(uint32_t v=0;v<ARRAY_QWORD_LIMIT;v++)for(uint32_t w=0;w<WRAPPER_QWORD_LIMIT;w++){if(!active[l][v][w])continue;if(!candidate_arrays(first,second,l,v,w))active[l][v][w]=0;else usable=1;}if(usable)samples++;}uint32_t count=0;for(uint32_t l=0;l<ARRAY_QWORD_LIMIT;l++)for(uint32_t v=0;v<ARRAY_QWORD_LIMIT;v++)for(uint32_t w=0;w<WRAPPER_QWORD_LIMIT;w++)if(active[l][v][w]){count++;selected_length_qword=l;selected_vector_qword=v;selected_wrapper_qword=w;}layout_candidates=count;layout_samples=samples;if(samples<h->preflight_required||count!=1u){failure_kind=11u;return 0;}uint32_t orientation=0,orientation_count=0;for(uint64_t i=0;i<h->pair_count&&orientation_count<h->preflight_required;i++){seed_pair*p=&pairs[i];if(!p->expected_own_methods)continue;uintptr_t first=0,second=0,v1=0,v2=0;uint64_t n1=0,n2=0;if(!call_pair(i,&first,&second)||!array_view(first,&n1,&v1)||!array_view(second,&n2,&v2)||n1!=n2){failure_kind=12u;failure_index=i+1u;return 0;}if(n1!=p->expected_own_methods)continue;int first_interface=1,second_interface=1;for(uint64_t j=0;j<n1;j++){uintptr_t a=0,b=0;memcpy(&a,(const void*)(v1+j*8u),8u);memcpy(&b,(const void*)(v2+j*8u),8u);const seed_method*ma=object_method(a,selected_wrapper_qword),*mb=object_method(b,selected_wrapper_qword);if(!ma||!mb){failure_kind=13u;failure_index=i+1u;return 0;}first_interface&=ma->owner==p->interface_definition;second_interface&=mb->owner==p->interface_definition;}if(first_interface==second_interface)continue;uint32_t here=first_interface?1u:2u;if(orientation&&orientation!=here){failure_kind=14u;failure_index=i+1u;return 0;}orientation=here;orientation_count++;}selected_orientation=orientation;orientation_samples=orientation_count;if(!orientation||orientation_count<h->preflight_required){failure_kind=15u;return 0;}return 1;}
static void free_observation(observation*o){free(o->pairs);free(o->mappings);memset(o,0,sizeof(*o));}
static int append_mapping(observation*o,output_mapping value){if(o->mapping_count==o->mapping_capacity){uint64_t cap=o->mapping_capacity?o->mapping_capacity*2u:524288u;if(cap<o->mapping_capacity||cap>8000000u)return 0;void*p=realloc(o->mappings,(SIZE_T)cap*sizeof(*o->mappings));if(!p)return 0;o->mappings=p;o->mapping_capacity=cap;}o->mappings[o->mapping_count++]=value;return 1;}
static int capture_batch(void){uint64_t end=capture_index+BATCH_PAIRS;if(end>h->pair_count)end=h->pair_count;for(;capture_index<end;capture_index++){seed_pair*s=&pairs[capture_index];uintptr_t first=0,second=0,v1=0,v2=0;uint64_t n1=0,n2=0;if(!call_pair(capture_index,&first,&second)||!array_view(first,&n1,&v1)||!array_view(second,&n2,&v2)||n1!=n2){failure_kind=20u;failure_index=capture_index+1u;return 0;}output_pair*p=&active_observation->pairs[capture_index];p->interface_descriptor=s->interface_descriptor;p->target_definition=s->target_definition;p->interface_definition=s->interface_definition;p->offset=s->offset;p->method_count=(uint32_t)n1;p->mapping_start=active_observation->mapping_count;if(!n1)active_observation->zero_pairs++;for(uint64_t j=0;j<n1;j++){uintptr_t a=0,b=0;memcpy(&a,(const void*)(v1+j*8u),8u);memcpy(&b,(const void*)(v2+j*8u),8u);const seed_method*ma=object_method(a,selected_wrapper_qword),*mb=object_method(b,selected_wrapper_qword);if(!ma||!mb){failure_kind=21u;failure_index=capture_index+1u;return 0;}const seed_method*im=selected_orientation==1u?ma:mb,*tm=selected_orientation==1u?mb:ma;output_mapping m={im->method_index,tm->method_index,im->metadata,tm->metadata};if(!append_mapping(active_observation,m)){failure_kind=22u;failure_index=capture_index+1u;return 0;}}}return 1;}
static LRESULT CALLBACK window_proc(HWND window,UINT message,WPARAM wparam,LPARAM lparam){if(message!=message_id)return CallWindowProcW(original_proc,window,message,wparam,lparam);LONG action=InterlockedCompareExchange(&callback_action,0,0);int ok=action==1?derive_layout():action==2?capture_batch():0;InterlockedExchange(&callback_complete,ok?1:-1);return ok;}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;static BOOL CALLBACK select_window(HWND window,LPARAM value){selection*s=(selection*)(uintptr_t)value;DWORD pid=0;RECT bounds;if(!IsWindowVisible(window)||GetWindow(window,GW_OWNER)||!GetWindowRect(window,&bounds)||bounds.right<=bounds.left||bounds.bottom<=bounds.top)return TRUE;GetWindowThreadProcessId(window,&pid);if(pid==s->pid){s->window=window;s->count++;}return TRUE;}
static int dispatch_action(HWND window,LONG action){DWORD_PTR result=0;InterlockedExchange(&callback_action,action);InterlockedExchange(&callback_complete,0);return SendMessageTimeoutW(window,message_id,0,0,SMTO_BLOCK,60000,&result)&&InterlockedCompareExchange(&callback_complete,0,0)==1;}
static int dispatch_capture(observation*first,observation*second){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window){failure_kind=30u;failure_index=s.count;return 0;}message_id=RegisterWindowMessageW(L"ALPHA v2 current runtime interface method map");SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);DWORD error=GetLastError();int ok=message_id&&(original_proc||error==ERROR_SUCCESS);if(ok)ok=dispatch_action(s.window,1);observation*values[2]={first,second};for(uint32_t pass=0;ok&&pass<2u;pass++){active_observation=values[pass];active_observation->pairs=calloc((SIZE_T)h->pair_count,sizeof(output_pair));if(!active_observation->pairs){failure_kind=31u;ok=0;break;}capture_index=0;while(ok&&capture_index<h->pair_count)ok=dispatch_action(s.window,2);}if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);if(!ok&&!failure_kind)failure_kind=32u;return ok;}
static int same_observation(const observation*a,const observation*b){return a->mapping_count==b->mapping_count&&a->zero_pairs==b->zero_pairs&&!memcmp(a->pairs,b->pairs,(SIZE_T)h->pair_count*sizeof(output_pair))&&!memcmp(a->mappings,b->mappings,(SIZE_T)a->mapping_count*sizeof(output_mapping));}
static void write_status(const char*s,const observation*o,int match,int written){FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"pair_count\": %llu,\n  \"mapping_count\": %llu,\n  \"zero_method_pair_count\": %llu,\n  \"layout_candidate_count\": %u,\n  \"layout_sample_count\": %u,\n  \"orientation_sample_count\": %u,\n  \"array_length_qword_owner_only\": %u,\n  \"array_vector_qword_owner_only\": %u,\n  \"method_wrapper_qword_owner_only\": %u,\n  \"array_orientation_owner_only\": %u,\n  \"failure_kind_owner_only\": %u,\n  \"failure_index_owner_only\": %llu,\n  \"two_observations_match\": %s,\n  \"output_written\": %s,\n  \"upstream_observations_after_process_start\": %s,\n  \"process_creation_filetime_owner_only\": %llu,\n  \"main_window_thread_dispatch_used\": true,\n  \"fresh_runtime_observation\": true,\n  \"saved_layout_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"fixed_rva_used\": false,\n  \"fixed_name_used\": false,\n  \"external_runtime_component_used\": false\n}\n",s,(unsigned long)GetCurrentProcessId(),(unsigned long long)h->pair_count,(unsigned long long)(o?o->mapping_count:0),(unsigned long long)(o?o->zero_pairs:0),layout_candidates,layout_samples,orientation_samples,selected_length_qword,selected_vector_qword,selected_wrapper_qword,selected_orientation,failure_kind,(unsigned long long)failure_index,match?"true":"false",written?"true":"false",upstream_freshness_verified?"true":"false",(unsigned long long)process_creation_filetime);fclose(f);}
static int write_output(const observation*o){FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;output_header x={0};memcpy(x.magic,"ALPHAIM1",8);x.version=$output_version;x.header_bytes=sizeof(x);x.pair_bytes=sizeof(output_pair);x.mapping_bytes=sizeof(output_mapping);x.pair_count=h->pair_count;x.mapping_count=o->mapping_count;x.process_id=h->process_id;x.image_base=h->image_base;x.image_bytes=h->image_bytes;x.helper_rva=h->helper_rva;x.wrapper_qword=selected_wrapper_qword;x.array_length_qword=selected_length_qword;x.array_vector_qword=selected_vector_qword;memcpy(x.executable,h->executable,64);memcpy(x.identity,h->identity,64);memcpy(x.graph,h->graph,64);memcpy(x.references,h->references,64);memcpy(x.methods,h->methods,64);memcpy(x.vtable,h->vtable,64);memcpy(x.constructed,h->constructed,64);int ok=fwrite(&x,1,sizeof(x),f)==sizeof(x)&&fwrite(o->pairs,sizeof(output_pair),(SIZE_T)h->pair_count,f)==h->pair_count&&fwrite(o->mappings,sizeof(output_mapping),(SIZE_T)o->mapping_count,f)==o->mapping_count;if(fclose(f))ok=0;if(ok)_wchmod(output_path,0600);else _wremove(output_path);return ok;}
static DWORD WINAPI worker(LPVOID unused) {
    (void)unused;

    if (GetFileAttributesW(output_path) != INVALID_FILE_ATTRIBUTES ||
        GetFileAttributesW(status_path) != INVALID_FILE_ATTRIBUTES) return 0;
    uint8_t *seed = NULL;
    SIZE_T bytes = 0;
    char seed_digest[65], exe_digest[65];
    if (!read_all(seed_path, &seed, &bytes) || bytes < sizeof(seed_header) ||
        !sha256_file(seed_path, seed_digest) || strcmp(seed_digest, expected_seed_sha256)) {
        free(seed);
        return 0;
    }
    h = (seed_header *)seed;
    if (memcmp(h->magic, "ALPHAIS1", 8) || h->version != $seed_version ||
        h->header_bytes != sizeof(*h) || h->pair_bytes != sizeof(seed_pair) ||
        h->method_bytes != sizeof(seed_method) || h->process_id != GetCurrentProcessId() ||
        h->image_base != (uintptr_t)GetModuleHandleW(NULL) ||
        !h->pair_count || h->pair_count > 2000000ull ||
        !h->method_count || h->method_count > 8000000ull ||
        h->preflight_required < 16u || h->preflight_required > 256u ||
        !executable_identity(exe_digest) || memcmp(h->executable, exe_digest, 64)) {
        failure_kind = 101u;
        write_status("identity_mismatch", NULL, 0, 0);
        free(seed);
        return 0;
    }
    SIZE_T required = sizeof(*h) + (SIZE_T)h->pair_count * sizeof(seed_pair) +
        (SIZE_T)h->method_count * sizeof(seed_method);
    if (bytes != required || !upstream_observations_current()) {
        failure_kind = 103u;
        write_status("stale_upstream_observation", NULL, 0, 0);
        free(seed);
        return 0;
    }
    pairs = (seed_pair *)(seed + sizeof(*h));
    method_map = (seed_method *)((uint8_t *)pairs + (SIZE_T)h->pair_count * sizeof(seed_pair));
    for (uint64_t i = 1; i < h->method_count; i++) {
        if (method_map[i-1].metadata >= method_map[i].metadata) {
            failure_kind = 102u;
            write_status("input_invalid", NULL, 0, 0);
            free(seed);
            return 0;
        }
    }
    observation first = {0}, second = {0};
    if (!dispatch_capture(&first, &second)) {
        write_status("capture_failed", &first, 0, 0);
        free_observation(&first); free_observation(&second); free(seed);
        return 0;
    }
    int match = same_observation(&first, &second);
    int identity_ok = upstream_observations_current() && executable_identity(exe_digest) &&
        !memcmp(h->executable, exe_digest, 64);
    if (!identity_ok) failure_kind = 104u;
    int written = match && identity_ok && write_output(&first);
    write_status(written ? "complete" : !identity_ok ? "identity_changed" :
                 match ? "write_failed" : "observation_unstable", &first, match, written);
    free_observation(&first); free_observation(&second); free(seed);
    return 0;
}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def prepare_runtime_interface_method_maps(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    type_graph_model: Path,
    type_graph_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    vtable_interface_model: Path,
    vtable_interface_inventory: Path,
    constructed_method_model: Path,
    constructed_method_inventory: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    seed_path = output_dir / "runtime-interface-method-map-seed.private.bin"
    output_path = output_dir / "runtime-interface-method-map.private.bin"
    status_path = output_dir / "runtime-interface-method-map-status.private.json"
    model_path = output_dir / "runtime-interface-method-map.private.json"
    plan_path = output_dir / "runtime-interface-method-map-plan.private.json"
    if any(path.exists() or path.is_symlink() for path in (
        seed_path, output_path, status_path, model_path, plan_path,
    )):
        raise AcquisitionError(
            "runtime interface method map output already exists; use a new output directory"
        )
    binding = _binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        vtable_interface_model=vtable_interface_model,
        vtable_interface_inventory=vtable_interface_inventory,
        constructed_method_model=constructed_method_model,
        constructed_method_inventory=constructed_method_inventory,
    )
    input_digest_keys = (
        "type_identity_inventory",
        "type_graph_inventory",
        "type_reference_inventory",
        "method_detail_inventory",
        "vtable_interface_inventory",
        "constructed_method_inventory",
    )
    contract = binding["interface_map_contract"]
    seed = bytearray(
        _SEED_HEADER.pack(
            _SEED_MAGIC,
            _SEED_VERSION,
            _SEED_HEADER.size,
            _SEED_PAIR.size,
            _SEED_METHOD.size,
            len(binding["pairs"]),
            len(binding["metadata_map"]),
            binding["process_id"],
            binding["image_base"],
            binding["image_bytes"],
            contract["helper_rva"],
            contract["method_index"],
            contract["method_metadata"],
            _PREFLIGHT_REQUIRED,
            binding["binary"]["sha256"].encode("ascii"),
            *(
                binding[key]["sha256"].encode("ascii")
                for key in input_digest_keys
            ),
        )
    )
    for row in binding["pairs"]:
        seed.extend(_SEED_PAIR.pack(*row))
    for row in binding["metadata_map"]:
        seed.extend(_SEED_METHOD.pack(*row))
    seed_path.write_bytes(seed)
    seed_path.chmod(0o600)
    seed_identity = file_identity(seed_path)
    build_dir = _owner_directory(output_dir / "build-interface-method-map")
    source_path = build_dir / "runtime-interface-method-map.c"
    injector_source_path = (
        build_dir / "runtime-interface-method-map-injector.c"
    )
    collector_path = build_dir / (
        f"alpha-runtime-interface-method-map-{time.time_ns():x}.dll"
    )
    injector_path = build_dir / "alpha-runtime-interface-method-map-injector.exe"
    source = _COLLECTOR.substitute(
        array_qword_limit=_ARRAY_QWORD_LIMIT,
        wrapper_qword_limit=_WRAPPER_QWORD_LIMIT,
        observation_evidence="\n".join(
            "    { " + _wide_literal(_windows_z_path(Path(binding[key]["path"])))
            + ', "' + binding[key]["sha256"] + '" },'
            for key in input_digest_keys
        ),
        seed_header_bytes=_SEED_HEADER.size,
        seed_pair_bytes=_SEED_PAIR.size,
        seed_method_bytes=_SEED_METHOD.size,
        output_header_bytes=RUNTIME_INTERFACE_METHOD_MAP_HEADER.size,
        output_pair_bytes=RUNTIME_INTERFACE_METHOD_MAP_PAIR.size,
        output_mapping_bytes=RUNTIME_INTERFACE_METHOD_MAP_ENTRY.size,
        seed_path=_wide_literal(_windows_z_path(seed_path)),
        output_path=_wide_literal(_windows_z_path(output_path)),
        status_path=_wide_literal(_windows_z_path(status_path)),
        seed_sha256=seed_identity["sha256"],
        status_schema=RUNTIME_INTERFACE_METHOD_MAP_STATUS_SCHEMA,
        seed_version=_SEED_VERSION,
        output_version=RUNTIME_INTERFACE_METHOD_MAP_VERSION,
    )
    _private_text(source_path, source)
    _private_text(injector_source_path, runtime_injector_source())
    cc = _compiler(compiler)
    _build(
        [
            str(cc), "-shared", "-O2", "-s", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror", str(source_path), "-o",
            str(collector_path), "-lbcrypt",
        ],
        label="runtime interface method map collector",
    )
    _build(
        [
            str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror", str(injector_source_path), "-o",
            str(injector_path),
        ],
        label="runtime interface method map injector",
    )
    input_keys = (
        "reflection_semantics",
        "type_identity_model",
        "type_identity_inventory",
        "type_graph_model",
        "type_graph_inventory",
        "type_reference_model",
        "type_reference_inventory",
        "method_detail_model",
        "method_detail_inventory",
        "vtable_interface_model",
        "vtable_interface_inventory",
        "constructed_method_model",
        "constructed_method_inventory",
    )
    plan = {
        "schema": "alpha.runtime-interface-method-map-plan/v1",
        "status": "prepared",
        "target": {
            "executable_path": str(binding["binary"]["path"]),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {key: binding[key] for key in input_keys},
        "contract": {
            "type_count": binding["type_count"],
            "interface_pair_count": len(binding["pairs"]),
            "method_metadata_pointer_count": len(binding["metadata_map"]),
            "preflight_sample_count": _PREFLIGHT_REQUIRED,
        },
        "runtime_contract_owner_only": contract,
        "seed": seed_identity,
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "policy": {
            "method_selected_by_signature_and_abi_data_flow": True,
            "native_helper_derived_from_current_method_body": True,
            "array_and_wrapper_layouts_runtime_derived": True,
            "array_roles_runtime_derived": True,
            "all_typedef_interface_pairs_observed": True,
            "main_window_thread_dispatch_required": True,
            "upstream_observations_must_postdate_current_process": True,
            "upstream_digests_rechecked_before_and_after_capture": True,
            "two_observations_required": True,
            "saved_layout_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "fixed_rva_used": False,
            "fixed_name_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return plan


def _seed_lookup(seed: bytes, header: tuple[int, ...], pointer: int) -> tuple[int, int] | None:
    start = _SEED_HEADER.size + header[5] * _SEED_PAIR.size
    low, high = 0, header[6]
    while low < high:
        middle = low + (high - low) // 2
        row = _SEED_METHOD.unpack_from(
            seed, start + middle * _SEED_METHOD.size
        )
        if row[0] < pointer:
            low = middle + 1
        else:
            high = middle
    if low >= header[6]:
        return None
    row = _SEED_METHOD.unpack_from(seed, start + low * _SEED_METHOD.size)
    return (row[1], row[2]) if row[0] == pointer else None


def _definition_lineages(
    identities: list[tuple[int, ...]],
    graph: list[tuple[int, ...]],
    references: dict[int, tuple[int, ...]],
) -> list[frozenset[int]]:

    definitions: dict[int, int] = {}
    for index, row in enumerate(identities):
        reference = references.get(row[2])
        if row[0] != index or reference is None or reference[1] in definitions:
            raise AcquisitionError("interface map TypeDef identity is ambiguous")
        definitions[reference[1]] = index
    if len(graph) != len(identities):
        raise AcquisitionError("interface map base graph count is inconsistent")
    parents: list[int | None] = []
    for index, row in enumerate(graph):
        if row[0] != index or row[2] != identities[index][2]:
            raise AcquisitionError("interface map base graph identity is inconsistent")
        base = row[3]
        if not base:
            parents.append(None)
            continue
        reference = references.get(base)
        if reference is None:
            raise AcquisitionError("interface map base descriptor is absent")
        nominal = reference[14] or reference[1]
        definition = references.get(nominal)
        if definition is None or definition[1] not in definitions:
            raise AcquisitionError("interface map base definition is absent")
        parents.append(definitions[definition[1]])
    result: list[frozenset[int]] = []
    for index in range(len(identities)):
        seen: set[int] = set()
        current: int | None = index
        while current is not None:
            if current in seen:
                raise AcquisitionError("interface map base graph contains a cycle")
            seen.add(current)
            current = parents[current]
        result.append(frozenset(seen))
    return result


def _pair_method_relations_valid(
    mappings: list[tuple[int, ...]],
    *,
    interface: int,
    target_lineage: frozenset[int],
    methods: list[tuple[int, ...]],
    expected_interface_methods: set[int],
) -> bool:

    return all(_pair_method_relation_checks(
        mappings, interface=interface, target_lineage=target_lineage,
        methods=methods, expected_interface_methods=expected_interface_methods,
    ).values())


def _pair_method_relation_checks(
    mappings: list[tuple[int, ...]], *, interface: int,
    target_lineage: frozenset[int], methods: list[tuple[int, ...]],
    expected_interface_methods: set[int],
) -> dict[str, bool]:

    indexes_valid = all(0 <= row[0] < len(methods) and 0 <= row[1] < len(methods)
                        for row in mappings)
    checks = {
        "mapping_method_indexes_valid": indexes_valid,
        "own_interface_method_domains_exact": indexes_valid and len(mappings) == len(expected_interface_methods),
        "target_methods_in_proven_inheritance_chain": indexes_valid,
        "target_methods_are_instance_nonconstructors": indexes_valid,
        "target_method_arities_match_interfaces": indexes_valid,
    }
    if not indexes_valid:
        return checks
    observed: set[int] = set()
    slots: set[int] = set()
    for interface_method, target_method, _interface_metadata, _target_metadata in mappings:
        declared, implementation = methods[interface_method], methods[target_method]
        if (
            interface_method not in expected_interface_methods
            or interface_method in observed
            or declared[0] != interface
            or declared[8] == 0xFFFF
            or declared[8] in slots
        ):
            checks["own_interface_method_domains_exact"] = False
        checks["target_methods_in_proven_inheritance_chain"] &= implementation[0] in target_lineage
        checks["target_methods_are_instance_nonconstructors"] &= not bool(implementation[5] & 0x10 or implementation[9] & 1)
        checks["target_method_arities_match_interfaces"] &= declared[10] == implementation[10]
        observed.add(interface_method)
        slots.add(declared[8])
    checks["own_interface_method_domains_exact"] &= observed == expected_interface_methods and slots == set(range(len(mappings)))
    return checks


def _validate(
    plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, Any], dict[str, bool]]:
    output_path = _owner_file(Path(plan["output_path"]), label="inventory")
    seed_path = _owner_file(Path(plan["seed"]["path"]), label="seed")
    raw = output_path.read_bytes()
    seed = seed_path.read_bytes()
    if (
        len(raw) < RUNTIME_INTERFACE_METHOD_MAP_HEADER.size
        or len(seed) < _SEED_HEADER.size
    ):
        raise AcquisitionError(
            "runtime interface method map output is truncated"
        )


    for key in (
        "type_identity_inventory", "type_graph_inventory",
        "type_reference_inventory", "method_detail_inventory",
        "vtable_interface_inventory", "constructed_method_inventory",
    ):
        expected = plan["inputs"][key]
        source = _owner_file(Path(expected["path"]), label=key)
        if file_identity(source) != expected:
            raise AcquisitionError(f"runtime interface method map {key} changed")
    header = RUNTIME_INTERFACE_METHOD_MAP_HEADER.unpack_from(raw)
    seed_header = _SEED_HEADER.unpack_from(seed)
    pair_count, mapping_count = header[5:7]
    pairs_end = (
        RUNTIME_INTERFACE_METHOD_MAP_HEADER.size
        + pair_count * RUNTIME_INTERFACE_METHOD_MAP_PAIR.size
    )
    seed_end = (
        _SEED_HEADER.size
        + seed_header[5] * _SEED_PAIR.size
        + seed_header[6] * _SEED_METHOD.size
    )
    digest_keys = (
        "type_identity_inventory",
        "type_graph_inventory",
        "type_reference_inventory",
        "method_detail_inventory",
        "vtable_interface_inventory",
        "constructed_method_inventory",
    )
    header_ok = (
        header[0] == RUNTIME_INTERFACE_METHOD_MAP_MAGIC
        and header[1] == RUNTIME_INTERFACE_METHOD_MAP_VERSION
        and header[2] == RUNTIME_INTERFACE_METHOD_MAP_HEADER.size
        and header[3] == RUNTIME_INTERFACE_METHOD_MAP_PAIR.size
        and header[4] == RUNTIME_INTERFACE_METHOD_MAP_ENTRY.size
        and pair_count == plan["contract"]["interface_pair_count"]
        and header[7] == plan["target"]["process_id"]
        and header[8] == plan["target"]["image_base_owner_only"]
        and header[9] == plan["target"]["image_bytes"]
        and header[10]
        == plan["runtime_contract_owner_only"]["helper_rva"]
        and 0 <= header[11] < _WRAPPER_QWORD_LIMIT
        and 0 <= header[12] < _ARRAY_QWORD_LIMIT
        and 0 <= header[13] < _ARRAY_QWORD_LIMIT
        and _digest(header[14], label="executable")
        == plan["target"]["executable_sha256"]
        and all(
            _digest(header[15 + index], label=key)
            == plan["inputs"][key]["sha256"]
            for index, key in enumerate(digest_keys)
        )
        and pairs_end
        + mapping_count * RUNTIME_INTERFACE_METHOD_MAP_ENTRY.size
        == len(raw)
    )
    seed_ok = (
        hashlib.sha256(seed).hexdigest() == plan["seed"]["sha256"]
        and seed_header[0] == _SEED_MAGIC
        and seed_header[1] == _SEED_VERSION
        and seed_header[2] == _SEED_HEADER.size
        and seed_header[3] == _SEED_PAIR.size
        and seed_header[4] == _SEED_METHOD.size
        and seed_header[5] == pair_count
        and seed_header[6]
        == plan["contract"]["method_metadata_pointer_count"]
        and seed_header[7] == plan["target"]["process_id"]
        and seed_header[8] == plan["target"]["image_base_owner_only"]
        and seed_header[9] == plan["target"]["image_bytes"]
        and seed_header[10]
        == plan["runtime_contract_owner_only"]["helper_rva"]
        and seed_header[11]
        == plan["runtime_contract_owner_only"]["method_index"]
        and seed_header[12]
        == plan["runtime_contract_owner_only"]["method_metadata"]
        and seed_header[13] == plan["contract"]["preflight_sample_count"]
        and _digest(seed_header[14], label="seed executable")
        == plan["target"]["executable_sha256"]
        and all(
            _digest(seed_header[15 + index], label=f"seed {key}")
            == plan["inputs"][key]["sha256"]
            for index, key in enumerate(digest_keys)
        )
        and seed_end == len(seed)
    )
    method_raw = _owner_file(
        Path(plan["inputs"]["method_detail_inventory"]["path"]),
        label="method detail inventory",
    ).read_bytes()
    method_header, methods, _ = _method_rows(method_raw)
    vtable_raw = _owner_file(
        Path(plan["inputs"]["vtable_interface_inventory"]["path"]),
        label="vtable/interface inventory",
    ).read_bytes()
    vtable_header = RUNTIME_VTABLE_INTERFACE_HEADER.unpack_from(vtable_raw)
    identity_raw = Path(plan["inputs"]["type_identity_inventory"]["path"]).read_bytes()
    graph_raw = Path(plan["inputs"]["type_graph_inventory"]["path"]).read_bytes()
    reference_raw = Path(plan["inputs"]["type_reference_inventory"]["path"]).read_bytes()
    _, references = _reference_rows(reference_raw)
    type_count = plan["contract"]["type_count"]
    identities = [
        _IDENTITY_RECORD.unpack_from(identity_raw, _IDENTITY_HEADER.size + i * _IDENTITY_RECORD.size)
        for i in range(type_count)
    ]
    graph = [
        RUNTIME_TYPE_GRAPH_RECORD.unpack_from(graph_raw, RUNTIME_TYPE_GRAPH_HEADER.size + i * RUNTIME_TYPE_GRAPH_RECORD.size)
        for i in range(type_count)
    ]
    lineages = _definition_lineages(identities, graph, references)
    virtual_by_owner: dict[int, set[int]] = defaultdict(set)
    for index, method in enumerate(methods):
        if method[8] != 0xFFFF:
            virtual_by_owner[method[0]].add(index)

    rows_ok = header_ok and seed_ok
    mapping_cursor = 0
    zero_pairs = 0
    mapping_pointer_relations_exact = True
    relation_checks = _pair_method_relation_checks(
        [], interface=0, target_lineage=frozenset(), methods=[], expected_interface_methods=set(),
    )
    relation_failure_count = 0
    relation_counterexamples: list[dict[str, Any]] = []
    pair_keys: set[tuple[int, int]] = set()
    for index in range(pair_count if rows_ok else 0):
        seed_pair = _SEED_PAIR.unpack_from(
            seed, _SEED_HEADER.size + index * _SEED_PAIR.size
        )
        pair = RUNTIME_INTERFACE_METHOD_MAP_PAIR.unpack_from(
            raw,
            RUNTIME_INTERFACE_METHOD_MAP_HEADER.size
            + index * RUNTIME_INTERFACE_METHOD_MAP_PAIR.size,
        )
        descriptor, target, interface, offset, count, start = pair
        key = (target, descriptor)
        vtable_row = RUNTIME_VTABLE_INTERFACE_RECORD.unpack_from(
            vtable_raw,
            RUNTIME_VTABLE_INTERFACE_HEADER.size
            + target * RUNTIME_VTABLE_INTERFACE_RECORD.size,
        ) if target < vtable_header[5] else ()
        if (
            pair[:4] != (seed_pair[2], *seed_pair[3:6])
            or start != mapping_cursor
            or mapping_cursor + count > mapping_count
            or key in pair_keys
            or not vtable_row
            or offset + count > vtable_row[1]
        ):
            rows_ok = False
            break
        pair_keys.add(key)
        zero_pairs += count == 0
        interface_methods: set[int] = set()
        pair_mappings: list[tuple[int, ...]] = []
        for local_index in range(count):
            mapping = RUNTIME_INTERFACE_METHOD_MAP_ENTRY.unpack_from(
                raw,
                pairs_end
                + (mapping_cursor + local_index)
                * RUNTIME_INTERFACE_METHOD_MAP_ENTRY.size,
            )
            interface_method, target_method, interface_metadata, target_metadata = (
                mapping
            )
            interface_seed = _seed_lookup(
                seed, seed_header, interface_metadata
            )
            target_seed = _seed_lookup(seed, seed_header, target_metadata)
            if (
                interface_method >= method_header[5]
                or target_method >= method_header[5]
                or interface_seed is None
                or target_seed is None
                or interface_seed[0] != interface_method
                or target_seed[0] != target_method
                or interface_method in interface_methods
            ):
                mapping_pointer_relations_exact = False
                rows_ok = False
                break
            interface_methods.add(interface_method)
            pair_mappings.append(mapping)
        if not rows_ok:
            break
        current_checks = _pair_method_relation_checks(
            pair_mappings,
            interface=interface,
            target_lineage=lineages[target],
            methods=methods,
            expected_interface_methods=virtual_by_owner[interface],
        )
        for name, value in current_checks.items():
            relation_checks[name] &= value
        if not all(current_checks.values()):
            relation_failure_count += 1
            if len(relation_counterexamples) < 128:
                relation_counterexamples.append({
                    "pair_index": index, "target_definition": target,
                    "interface_definition": interface, "mapping_count": count,
                    "target_attributes": identities[target][7],
                    "checks": current_checks,
                    "target_lineage": sorted(lineages[target]),
                    "mappings_owner_only": [list(row) for row in pair_mappings],
                })
        mapping_cursor += count
    rows_ok = rows_ok and mapping_cursor == mapping_count
    checks = {
        "status_schema": status.get("schema")
        == RUNTIME_INTERFACE_METHOD_MAP_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "header_bound": header_ok,
        "seed_bound": seed_ok,
        "all_interface_pairs_accounted": rows_ok
        and status.get("pair_count") == pair_count,
        "all_mapping_rows_valid": rows_ok and all(relation_checks.values()),
        "mapping_metadata_pointer_relations_exact": (
            mapping_pointer_relations_exact
        ),
        **relation_checks,
        "status_counts_match_inventory": status.get("mapping_count") == mapping_count
        and status.get("zero_method_pair_count") == zero_pairs,
        "status_process_matches_inventory": status.get("process_id") == header[7],
        "upstream_observations_after_process_start": status.get(
            "upstream_observations_after_process_start"
        ) is True and type(status.get("process_creation_filetime_owner_only")) is int
        and status["process_creation_filetime_owner_only"] > 0,
        "status_layout_matches_inventory": status.get("method_wrapper_qword_owner_only") == header[11]
        and status.get("array_length_qword_owner_only") == header[12]
        and status.get("array_vector_qword_owner_only") == header[13],
        "runtime_layout_unique": status.get("layout_candidate_count") == 1,
        "runtime_layout_sampled": status.get("layout_sample_count")
        == plan["contract"]["preflight_sample_count"],
        "runtime_array_orientation_unique": status.get(
            "orientation_sample_count"
        )
        == plan["contract"]["preflight_sample_count"]
        and status.get("array_orientation_owner_only") in (1, 2),
        "main_window_thread_dispatch_used": status.get(
            "main_window_thread_dispatch_used"
        )
        is True,
        "two_observations_match": status.get("two_observations_match")
        is True,
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        )
        is True,
        "saved_layout_absent": status.get("saved_layout_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "fixed_rva_absent": status.get("fixed_rva_used") is False,
        "fixed_name_absent": status.get("fixed_name_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    counts = {
        "interface_pair_count": pair_count,
        "mapping_count": mapping_count,
        "zero_method_pair_count": zero_pairs,
        "nonzero_method_pair_count": pair_count - zero_pairs,
        "method_metadata_pointer_count": seed_header[6],
        "relation_failure_pair_count": relation_failure_count,
        "relation_counterexamples_owner_only": relation_counterexamples,
        "relation_counterexamples_truncated": relation_failure_count > len(relation_counterexamples),
        "inventory_sha256": hashlib.sha256(raw).hexdigest(),
    }
    return counts, checks


def capture_runtime_interface_method_maps(
    *,
    binary: Path,
    reflection_semantics_model: Path,
    type_identity_model: Path,
    type_identity_inventory: Path,
    type_graph_model: Path,
    type_graph_inventory: Path,
    type_reference_model: Path,
    type_reference_inventory: Path,
    method_detail_model: Path,
    method_detail_inventory: Path,
    vtable_interface_model: Path,
    vtable_interface_inventory: Path,
    constructed_method_model: Path,
    constructed_method_inventory: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 1800.0,
    encoded_vtable_model: Path | None = None,
    encoded_vtable_inventory: Path | None = None,
    vtable_declaration_model: Path | None = None,
    vtable_declaration_inventory: Path | None = None,
) -> dict[str, Any]:
    projection_paths = {
        'encoded_vtable_model': encoded_vtable_model,
        'encoded_vtable_inventory': encoded_vtable_inventory,
        'vtable_declaration_model': vtable_declaration_model,
        'vtable_declaration_inventory': vtable_declaration_inventory,
    }
    projected_mode = any(path is not None for path in projection_paths.values())
    if projected_mode and any(path is None for path in projection_paths.values()):
        raise AcquisitionError('interface slot projection requires all four explicit vtable artifacts')
    output_dir = _owner_directory(output_dir)
    semantic_path = output_dir / 'runtime-interface-slot-projection.private.bin'
    if projected_mode and (semantic_path.exists() or semantic_path.is_symlink()):
        raise AcquisitionError('interface semantic inventory already exists; use a new output directory')
    plan = prepare_runtime_interface_method_maps(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        vtable_interface_model=vtable_interface_model,
        vtable_interface_inventory=vtable_interface_inventory,
        constructed_method_model=constructed_method_model,
        constructed_method_inventory=constructed_method_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    declarations = None
    projection_inputs = {}
    if projected_mode:
        from alpha.p13 import _safe_path, _file_record
        from alpha.c01 import current_runtime_process_binding
        from alpha.p29 import load_runtime_vtable_declarations
        current = current_runtime_process_binding()
        current_binary = _safe_path(binary)
        if current is None or not same_executable_path(
            current[2], current_binary
        ):
            raise AcquisitionError('interface slot projection requires a current process session')
        binary_identity = file_identity(current_binary)
        identity = dict(process_id=current[0], creation_filetime=current[1], executable_path=str(current_binary),
            executable_sha256=binary_identity['sha256'], executable_bytes=binary_identity['bytes'])
        for key, path in projection_paths.items():
            path = _safe_path(path)
            projection_inputs[key] = {'path': str(path), **_file_record(path)}
        declarations = load_runtime_vtable_declarations(model_path=vtable_declaration_model,
            inventory_path=vtable_declaration_inventory, expected_identity=identity,
            expected_inputs={'binary': binary_identity, **plan['inputs'],
                'encoded_vtable_model': projection_inputs['encoded_vtable_model'],
                'encoded_vtable_inventory': projection_inputs['encoded_vtable_inventory']})
        if declarations['model'] != projection_inputs['vtable_declaration_model'] or declarations['inventory'] != projection_inputs['vtable_declaration_inventory']:
            raise AcquisitionError('interface declaration inputs changed during load')
        plan['vtable_projection_inputs'] = projection_inputs
        plan['vtable_projection_identity'] = identity
        _private_json(output_dir / 'runtime-interface-method-map-plan.private.json', plan)
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
            "runtime interface method map injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-interface-method-map-injector.private.log",
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
            "runtime interface method map injection failed"
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
        raise AcquisitionError(
            "runtime interface method map capture timed out"
        )
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime interface method map capture failed "
            f"(status={status.get('status')}, "
            f"kind={status.get('failure_kind_owner_only')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"layout_candidates={status.get('layout_candidate_count')})"
        )
    _seal_runtime_output(Path(plan["output_path"]))
    _seal_runtime_output(status_path)
    if declarations is not None:
        from alpha.p28 import validate_interface_projection
        proof = validate_interface_projection(plan=plan, status=status, declarations=declarations,
            expected_identity=identity)
        for key, record in {'binary': binary_identity, **plan['inputs'], **projection_inputs}.items():
            path = _safe_path(Path(record['path']))
            if key != 'binary':
                _file_record(path)
            if file_identity(path) != record:
                raise AcquisitionError('interface projection dependency changed: ' + key)
        with os.fdopen(os.open(semantic_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600), 'wb') as saved:
            saved.write(proof['payload'])
            saved.flush()
            os.fsync(saved.fileno())
        if semantic_path.read_bytes() != proof['payload']:
            raise AcquisitionError('interface semantic inventory byte roundtrip failed')


        model = {'schema': 'alpha.runtime-interface-slot-projection/v1', 'status': 'runtime-slot-projected',
            'target': identity, 'inputs': {**plan['inputs'], **projection_inputs},
            'inventory': file_identity(semantic_path), 'raw_inventory': file_identity(Path(plan['output_path'])),
            'status_receipt': file_identity(status_path), 'projection_inputs': proof['inputs'],
            'counts': proof['counts'], 'checks': {**proof['checks'], 'semantic_inventory_byte_roundtrip_exact': True,
                'all_projection_dependencies_unchanged': True},
            'raw_relation_checks': proof['raw_relation_checks'],
            'raw_relation_failure_pair_count': proof['raw_relation_failure_pair_count'],
            'interface_only_contexts_owner_only': proof['interface_only_contexts_owner_only'],
            'runtime_contract_owner_only': plan['runtime_contract_owner_only'],
            'metadata_complete': False, 'generic_signature_substitution_complete': False,
            'standard_metadata_vtable_reconstruction_complete': False, 'owner_only': True}
        atomic_write_json(Path(plan['model_path']), model)
        Path(plan['model_path']).chmod(0o600)
        return model
    counts, checks = _validate(plan, status)
    if not all(checks.values()):
        _private_json(output_dir / "runtime-interface-method-map-rejected.private.json", {
            "schema": "alpha.runtime-interface-method-map-rejection/v1",
            "status": "rejected", "metadata_complete": False,
            "target": plan["target"], "inputs": plan["inputs"],
            "inventory": file_identity(Path(plan["output_path"])),
            "status_receipt": file_identity(status_path),
            "counts": counts, "checks": checks,
        })
        raise AcquisitionError(
            "runtime interface method map validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    model = {
        "schema": RUNTIME_INTERFACE_METHOD_MAP_SCHEMA,
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
        "runtime_contract_owner_only": {
            **plan["runtime_contract_owner_only"],
            "method_wrapper_qword": status[
                "method_wrapper_qword_owner_only"
            ],
            "array_length_qword": status[
                "array_length_qword_owner_only"
            ],
            "array_vector_qword": status[
                "array_vector_qword_owner_only"
            ],
            "array_orientation": status["array_orientation_owner_only"],
        },
        "policy": plan["policy"],
        "owner_only": True,
    }
    atomic_write_json(Path(plan["model_path"]), model)
    Path(plan["model_path"]).chmod(0o600)
    return model
