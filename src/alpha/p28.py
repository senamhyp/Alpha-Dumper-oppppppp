from concurrent.futures import ThreadPoolExecutor

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

from alpha.p12 import _compiler, _owner_directory, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import (
    AcquisitionError,
    owner_only_path_bits,
    owner_uid,
    same_executable_path,
)
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p22 import METHOD_DETAIL_CONSTRUCTOR, RUNTIME_METHOD_DETAIL_HEADER, RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_METHOD, RUNTIME_METHOD_DETAIL_SCHEMA, RUNTIME_METHOD_DETAIL_VERSION
from alpha.p26 import RUNTIME_METHOD_GENERIC_HEADER, RUNTIME_METHOD_GENERIC_MAGIC, RUNTIME_METHOD_GENERIC_RECORD, RUNTIME_METHOD_GENERIC_SCHEMA, RUNTIME_METHOD_GENERIC_VERSION, load_runtime_method_generic_inventory
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA, _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_RECORD, RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION, TYPE_REFERENCE_ARRAY, TYPE_REFERENCE_BYREF, TYPE_REFERENCE_ENUM, TYPE_REFERENCE_GENERIC_PARAMETER, TYPE_REFERENCE_POINTER
from alpha.p21 import RUNTIME_TYPE_GRAPH_HEADER, RUNTIME_TYPE_GRAPH_MAGIC, RUNTIME_TYPE_GRAPH_RECORD, RUNTIME_TYPE_GRAPH_STATUS_SCHEMA, RUNTIME_TYPE_GRAPH_VERSION
from alpha.h02 import file_identity, read_json
from alpha.h02 import write_new_json as _private_json, write_new_text as _private_text, write_new_bytes
from alpha.p14 import current_capture_scope, assert_current_capture_alive
from alpha.c01 import current_runtime_process_binding


def _verify_generic_capture_sources(plan):
    from alpha.c04 import _verify_files
    current = current_runtime_process_binding()
    target = plan["target"]
    if (type(target.get("process_id")) is not int or type(target.get("creation_filetime")) is not int
        or current is None or current[0] != target.get("process_id")
        or current[1] != target.get("creation_filetime")
        or not same_executable_path(current[2], target.get("executable_path"))):
        raise AcquisitionError("generic detail capture is not bound to the current process instance")
    if file_identity(Path(target["executable_path"]))["sha256"] != target["executable_sha256"]:
        raise AcquisitionError("generic detail capture executable changed")
    records = {role: record for role, record in plan["inputs"].items()
               if not (role == "type_graph_inventory" and record is None)}
    records.update(collector=plan["collector"], injector=plan["injector"])
    _verify_files(records)
    assert_current_capture_alive()


RUNTIME_GENERIC_PARAMETER_DETAIL_PLAN_SCHEMA = (
    "alpha.runtime-generic-parameter-detail-plan/v1"
)
RUNTIME_GENERIC_PARAMETER_DETAIL_STATUS_SCHEMA = (
    "alpha.runtime-generic-parameter-detail-status/v1"
)
RUNTIME_GENERIC_PARAMETER_DETAIL_SCHEMA = (
    "alpha.runtime-generic-parameter-detail-inventory/v1"
)
RUNTIME_GENERIC_PARAMETER_DETAIL_MAGIC = b"ALPHAGP1"
RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION = 1
RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER = struct.Struct(
    "<8sIIIIQQQQ64s64s64s64s64s"
)
RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD = struct.Struct("<QIIQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime generic parameter detail {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime generic parameter detail {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime generic parameter detail {label} digest is invalid"
        )
    return value


def _bound_type_graph_status(reference_model: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:

    from alpha.p13 import _safe_path
    record = reference_model.get("inputs", {}).get("type_graph_status")
    if not isinstance(record, dict) or not isinstance(record.get("path"), str) or not record["path"]:
        raise AcquisitionError("generic detail TypeRef has no bound type graph status source")
    path = _owner_file(_safe_path(Path(record["path"])), label="type graph status")
    actual = file_identity(path)
    if actual != record:
        raise AcquisitionError("runtime generic parameter graph status source identity is stale")
    status = read_json(path)
    if (status.get("schema") != RUNTIME_TYPE_GRAPH_STATUS_SCHEMA or status.get("status") != "complete"
            or type(status.get("process_id")) is not int
            or status["process_id"] != reference_model.get("target", {}).get("process_id")
            or status.get("fresh_runtime_observation") is not True or status.get("saved_type_graph_used") is not False):
        raise AcquisitionError("generic detail bound type graph status is not a current complete observation")
    return actual, status


def _validated_model(
    *, model_path: Path, inventory_path: Path, schema: str,
    executable_sha256: str, label: str,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    model_path = _owner_file(model_path, label=f"{label} model")
    inventory_path = _owner_file(
        inventory_path, label=f"{label} inventory"
    )
    model = read_json(model_path)
    inventory = file_identity(inventory_path)
    if (
        model.get("schema") != schema
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or not model.get("checks")
        or not all(model["checks"].values())
        or model.get("inventory", model.get("identity_inventory", {})).get(
            "sha256"
        )
        != inventory["sha256"]
    ):
        raise AcquisitionError(
            f"runtime generic parameter detail {label} is stale"
        )
    return file_identity(model_path), inventory, model


def _select_candidates(
    *, identity: bytes, references: bytes, methods: bytes,
    runtime_type_class: int, from_handle: dict[str, Any],
    reference_rows_out: dict[str, Any] | None = None,
) -> dict[str, Any]:


    if (len(identity) < _IDENTITY_HEADER.size or len(references) < RUNTIME_TYPE_REFERENCE_HEADER.size
        or len(methods) < RUNTIME_METHOD_DETAIL_HEADER.size):
        raise AcquisitionError("runtime generic candidate topology is truncated")
    identity_header = _IDENTITY_HEADER.unpack_from(identity)
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(references)
    method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(methods)
    if (_IDENTITY_HEADER.size + identity_header[5] * _IDENTITY_RECORD.size > len(identity)
        or RUNTIME_TYPE_REFERENCE_HEADER.size + reference_header[5] * RUNTIME_TYPE_REFERENCE_RECORD.size > len(references)
        or RUNTIME_METHOD_DETAIL_HEADER.size + method_header[5] * RUNTIME_METHOD_DETAIL_METHOD.size > len(methods)
        or type(runtime_type_class) is not int or runtime_type_class <= 0):
        raise AcquisitionError("runtime generic candidate topology bounds differ")
    if any(type(from_handle.get(key)) is not int or from_handle[key] <= 0
           for key in ("metadata_pointer", "method_pointer")):
        raise AcquisitionError("runtime generic candidate factory identity is invalid")


    identity_region = memoryview(identity)[
        _IDENTITY_HEADER.size:_IDENTITY_HEADER.size
        + identity_header[5] * _IDENTITY_RECORD.size
    ]
    owners = [index for index, row in enumerate(
        _IDENTITY_RECORD.iter_unpack(identity_region)
    ) if row[3] == runtime_type_class]
    if len(owners) != 1:
        raise AcquisitionError("runtime generic parameter observed owner is not unique")
    owner = owners[0]
    reference_region = memoryview(references)[
        RUNTIME_TYPE_REFERENCE_HEADER.size:RUNTIME_TYPE_REFERENCE_HEADER.size
        + reference_header[5] * RUNTIME_TYPE_REFERENCE_RECORD.size
    ]
    reference_rows: dict[int, tuple[int, ...]] = {}
    generic_parameters: set[int] = set()
    for row in RUNTIME_TYPE_REFERENCE_RECORD.iter_unpack(reference_region):
        if not row[0] or row[0] in reference_rows:
            raise AcquisitionError("runtime generic candidate descriptors repeat or are absent")
        reference_rows[row[0]] = row
        if row[4] & TYPE_REFERENCE_GENERIC_PARAMETER:
            generic_parameters.add(row[0])

    def aliases(pointer: int) -> tuple[int, ...]:
        row = reference_rows.get(pointer)
        return (pointer, row[1]) if row is not None else (pointer,)

    method_region = memoryview(methods)[
        RUNTIME_METHOD_DETAIL_HEADER.size:RUNTIME_METHOD_DETAIL_HEADER.size
        + method_header[5] * RUNTIME_METHOD_DETAIL_METHOD.size
    ]


    metadata_pointer = from_handle.get("metadata_pointer")
    method_pointer = from_handle.get("method_pointer")
    factories: list[tuple[int, ...]] = []
    owner_rows: list[tuple[int, tuple[int, ...]]] = []
    for index, row in enumerate(
        RUNTIME_METHOD_DETAIL_METHOD.iter_unpack(method_region)
    ):
        if row[2] == metadata_pointer and row[3] == method_pointer:
            factories.append(row)
        if (row[0] == owner and not row[5] & 0x10 and not row[10]
                and not row[9] & METHOD_DETAIL_CONSTRUCTOR
                and row[2] and row[3]):
            owner_rows.append((index, row))
    if (len(factories) != 1 or not factories[0][5] & 0x10 or factories[0][10] != 1
            or factories[0][4] not in reference_rows):
        raise AcquisitionError("runtime generic candidate type factory binding is not unique")
    type_descriptors = set(aliases(factories[0][4]))
    wrappers = TYPE_REFERENCE_ARRAY | TYPE_REFERENCE_BYREF | TYPE_REFERENCE_POINTER
    if reference_rows[factories[0][4]][4] & (wrappers | TYPE_REFERENCE_GENERIC_PARAMETER):
        raise AcquisitionError("runtime generic type factory returns a wrapped or open descriptor")

    def type_array(pointer: int) -> bool:
        row = reference_rows.get(pointer)
        return bool(
            row is not None
            and row[4] & TYPE_REFERENCE_ARRAY
            and not row[4] & (TYPE_REFERENCE_BYREF | TYPE_REFERENCE_POINTER | TYPE_REFERENCE_GENERIC_PARAMETER)
            and row[9] == 1
            and row[13]
            and row[13] in reference_rows
            and not reference_rows[row[13]][4] & (wrappers | TYPE_REFERENCE_GENERIC_PARAMETER)
            and type_descriptors.intersection(aliases(row[13]))
        )

    attributes: list[dict[str, int]] = []
    constraints: list[dict[str, int]] = []
    for index, row in owner_rows:
        candidate = {
            "method_index": index,
            "metadata": row[2],
            "pointer": row[3],
        }
        result = reference_rows.get(row[4])


        public_virtual_property = (row[5] & 7 == 6 and row[5] & 0x840 == 0x840
            and not row[5] & 0x400 and row[8] != 0xFFFF)
        if (result is not None and result[4] & TYPE_REFERENCE_ENUM
                and not result[4] & (wrappers | TYPE_REFERENCE_GENERIC_PARAMETER)
                and public_virtual_property):
            attributes.append(candidate)
        if type_array(row[4]):
            constraints.append(candidate)
    if (
        not 1 <= len(attributes) <= 8
        or not 1 <= len(constraints) <= 8
    ):
        raise AcquisitionError(
            "runtime generic parameter candidate domain is invalid"
        )
    if reference_rows_out is not None:
        reference_rows_out["rows"] = reference_rows
        reference_rows_out["generic_parameters"] = generic_parameters
    return {
        "owner_index": owner,
        "attributes": attributes,
        "constraints": constraints,
        "owner_bound_to_observed_class": True,
        "type_array_element_bound_to_factory_return": True,
        "attribute_candidates_public_virtual_property_getters": True,
        "name_seed_used": False,
        "operation_semantics_proven": False,
    }


def _binding(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
    method_generic_model: Path, method_generic_inventory: Path,
    type_graph_inventory: Path | None = None,
    selection_evidence_plan: Path | None = None,
    selection_evidence_status: Path | None = None,
    reference_regions_out: dict[str, Any] | None = None,
) -> dict[str, Any]:


    shared_reference_rows: dict[str, Any] = (
        {} if reference_regions_out is None else reference_regions_out
    )
    binary = binary.expanduser().resolve()
    binary_identity = file_identity(binary)
    executable_sha256 = binary_identity["sha256"]
    identity_model, identity_inventory, _ = _validated_model(
        model_path=type_identity_model,
        inventory_path=type_identity_inventory,
        schema=RUNTIME_TYPE_IDENTITY_SCHEMA,
        executable_sha256=executable_sha256,
        label="type identity",
    )
    reference_model, reference_inventory, reference_model_raw = (
        _validated_model(
            model_path=type_reference_model,
            inventory_path=type_reference_inventory,
            schema=RUNTIME_TYPE_REFERENCE_SCHEMA,
            executable_sha256=executable_sha256,
            label="type reference",
        )
    )
    method_model, method_inventory, _ = _validated_model(
        model_path=method_detail_model,
        inventory_path=method_detail_inventory,
        schema=RUNTIME_METHOD_DETAIL_SCHEMA,
        executable_sha256=executable_sha256,
        label="method detail",
    )
    generic_model, generic_inventory, _ = _validated_model(
        model_path=method_generic_model,
        inventory_path=method_generic_inventory,
        schema=RUNTIME_METHOD_GENERIC_SCHEMA,
        executable_sha256=executable_sha256,
        label="method generic",
    )
    generic = load_runtime_method_generic_inventory(
        model_path=Path(generic_model["path"]),
        inventory_path=Path(generic_inventory["path"]),
        expected_executable_sha256=executable_sha256,
        expected_method_detail_inventory_sha256=method_inventory["sha256"],
        include_methods=False,
    )
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantics"
    )
    semantics = read_json(semantics_path)
    from_handle = next(
        (
            row
            for row in semantics.get("operations", [])
            if isinstance(row, dict) and row.get("key") == "type.from_handle"
        ),
        None,
    )
    if (
        semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary", {}).get("sha256") != executable_sha256
        or not isinstance(from_handle, dict)
        or from_handle.get("semantic_identity_resolved") is not True
        or not isinstance(from_handle.get("method_pointer"), int)
        or not isinstance(from_handle.get("metadata_pointer"), int)
    ):
        raise AcquisitionError(
            "runtime generic parameter reflection binding is stale"
        )
    identity_plan_path = _owner_file(
        Path(identity_model["path"]).parent
        / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    identity_status_path = _owner_file(
        Path(identity_model["path"]).parent
        / "runtime-type-identity-status.private.json",
        label="type identity status",
    )
    identity_plan = read_json(identity_plan_path)
    identity_status = read_json(identity_status_path)
    current = current_runtime_process_binding()
    if current is None:
        raise AcquisitionError("generic detail preparation requires an explicitly bound current process")
    for target in (identity_plan.get("target", {}), reference_model_raw.get("target", {})):


        if (not same_executable_path(current[2], target.get("executable_path"))
            or not same_executable_path(binary, current[2])
            or target.get("executable_sha256") != executable_sha256):
            raise AcquisitionError("generic detail source belongs to a different process instance")
    from alpha.c04 import _verify_files
    instance_inputs = {"type_identity_plan": file_identity(identity_plan_path),
                       "type_identity_status": file_identity(identity_status_path)}
    for role, record in instance_inputs.items():
        if reference_model_raw.get("inputs", {}).get(role) != record:
            raise AcquisitionError("generic detail identity source is not bound to the selected TypeRef model")
    for role, record in (("type_identity_inventory", identity_inventory), ("method_detail_inventory", method_inventory),
                         ("semantics", file_identity(semantics_path))):
        if reference_model_raw.get("inputs", {}).get(role) != record:
            raise AcquisitionError("generic detail inputs differ from the current TypeRef source")
    _verify_files(instance_inputs)
    plan_process_id = identity_plan.get("target", {}).get("process_id")
    process_id = current[0]
    runtime_type_class = identity_plan.get(
        "runtime_classes_owner_only", {}
    ).get("runtime_type")
    graph_status_identity, graph_status = _bound_type_graph_status(reference_model_raw)
    instance_inputs["type_graph_status"] = graph_status_identity
    length_qword = graph_status.get("array_length_qword_owner_only")
    vector_qword = graph_status.get("array_vector_qword_owner_only")
    if (
        identity_plan.get("status") != "prepared"
        or identity_status.get("status") != "complete"
        or identity_status.get("process_id") != plan_process_id
        or not isinstance(plan_process_id, int)
        or plan_process_id <= 0
        or not isinstance(runtime_type_class, int)
        or runtime_type_class <= 0
        or not isinstance(length_qword, int)
        or not isinstance(vector_qword, int)
        or not 1 <= length_qword < vector_qword < 10
    ):
        raise AcquisitionError(
            "runtime generic parameter process layouts are stale"
        )
    identity_raw = Path(identity_inventory["path"]).read_bytes()
    reference_raw = Path(reference_inventory["path"]).read_bytes()
    method_raw = Path(method_inventory["path"]).read_bytes()
    identity_header = _IDENTITY_HEADER.unpack_from(identity_raw)
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
    method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(method_raw)
    if (
        identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or reference_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or reference_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or method_header[0] != RUNTIME_METHOD_DETAIL_MAGIC
        or method_header[1] != RUNTIME_METHOD_DETAIL_VERSION
        or reference_header[10] != identity_header[6]
        or reference_header[11] != identity_header[7]
        or method_header[8] != identity_header[6]
        or method_header[9] != identity_header[7]
        or _digest(method_header[12], label="method executable") != executable_sha256
        or _digest(method_header[14], label="method type identity") != identity_inventory["sha256"]
        or generic["counts"]["generic_argument_count"] <= 0
    ):
        raise AcquisitionError(
            "runtime generic parameter input headers conflict"
        )
    candidates = _select_candidates(
        identity=identity_raw,
        references=reference_raw,
        methods=method_raw,
        runtime_type_class=runtime_type_class,
        from_handle=from_handle,
        reference_rows_out=shared_reference_rows,
    )


    shared_reference_rows["reference_sha256"] = reference_inventory["sha256"]


    generic_raw = Path(generic_inventory["path"]).read_bytes()
    generic_header = RUNTIME_METHOD_GENERIC_HEADER.unpack_from(generic_raw)
    if (_digest(generic_header[11], label="generic executable") != executable_sha256
        or _digest(generic_header[12], label="generic type identity") != identity_inventory["sha256"]
        or _digest(generic_header[13], label="generic methods") != method_inventory["sha256"]
        or _digest(generic_header[15], label="generic semantics") != file_identity(semantics_path)["sha256"]):
        raise AcquisitionError("generic detail argument sources differ from the current inventories")
    generic_argument_start = (
        RUNTIME_METHOD_GENERIC_HEADER.size
        + generic_header[5] * RUNTIME_METHOD_GENERIC_RECORD.size
    )
    generic_arguments = list(
        struct.unpack_from(
            f"<{generic_header[7]}Q", generic_raw, generic_argument_start
        )
        if generic_header[7]
        else ()
    )


    reference_rows = shared_reference_rows["rows"]
    type_graph_identity: dict[str, Any] | None = None
    if type_graph_inventory is not None:
        graph_path = _owner_file(type_graph_inventory, label="type graph inventory")
        graph_raw = graph_path.read_bytes()
        if len(graph_raw) < RUNTIME_TYPE_GRAPH_HEADER.size:
            raise AcquisitionError("runtime generic parameter type graph is truncated")
        graph_header = RUNTIME_TYPE_GRAPH_HEADER.unpack_from(graph_raw)
        graph_type_count, graph_interface_count, graph_argument_count = (
            graph_header[5:8]
        )
        graph_argument_start = (
            RUNTIME_TYPE_GRAPH_HEADER.size
            + graph_type_count * RUNTIME_TYPE_GRAPH_RECORD.size
            + graph_interface_count * 8
        )
        if (
            graph_header[0] != RUNTIME_TYPE_GRAPH_MAGIC
            or graph_header[1] != RUNTIME_TYPE_GRAPH_VERSION
            or graph_header[2] != RUNTIME_TYPE_GRAPH_HEADER.size
            or graph_header[3] != RUNTIME_TYPE_GRAPH_RECORD.size
            or graph_type_count != identity_header[5]
            or _digest(graph_header[10], label="type graph executable")
            != executable_sha256
            or _digest(graph_header[11], label="type graph identity")
            != identity_inventory["sha256"]
            or graph_argument_start + graph_argument_count * 8 != len(graph_raw)
        ):
            raise AcquisitionError("runtime generic parameter type graph is stale")
        graph_arguments = (
            struct.unpack_from(
                f"<{graph_argument_count}Q", graph_raw, graph_argument_start
            )
            if graph_argument_count
            else ()
        )
        graph_generic_parameter_descriptors = {
            descriptor
            for descriptor in graph_arguments
            if (
                descriptor in reference_rows
                and reference_rows[descriptor][4]
                & TYPE_REFERENCE_GENERIC_PARAMETER
            )
        }
        seen = set(generic_arguments)
        for descriptor in graph_arguments:
            if (
                descriptor in graph_generic_parameter_descriptors
                and descriptor not in seen
            ):
                seen.add(descriptor)
                generic_arguments.append(descriptor)
        type_graph_identity = file_identity(graph_path)
        expected_arguments = (
            set(generic_arguments[:generic_header[7]])
            | graph_generic_parameter_descriptors
        )
        if set(generic_arguments) != expected_arguments:
            missing = len(expected_arguments - set(generic_arguments))
            extra = len(set(generic_arguments) - expected_arguments)
            raise AcquisitionError(
                "runtime generic parameter descriptor closure is incomplete "
                f"(missing={missing}, extra={extra})"
            )


    open_arguments = [
        index
        for index, descriptor in enumerate(generic_arguments)
        if (
            descriptor in reference_rows
            and reference_rows[descriptor][4] & TYPE_REFERENCE_GENERIC_PARAMETER
        )
    ]

    return {
        "binary": binary_identity,
        "semantics": file_identity(semantics_path),
        "type_identity_model": identity_model,
        "type_identity_inventory": identity_inventory,
        "type_reference_model": reference_model,
        "type_reference_inventory": reference_inventory,
        "method_detail_model": method_model,
        "method_detail_inventory": method_inventory,
        "method_generic_model": generic_model,
        "method_generic_inventory": generic_inventory,
        "process_id": process_id,
        "creation_filetime": current[1],
        "instance_inputs": instance_inputs,
        "image_base": identity_header[6],
        "image_bytes": identity_header[7],
        "argument_count": len(generic_arguments),
        "method_argument_count": generic["counts"]["generic_argument_count"],
        "argument_descriptors": tuple(generic_arguments),
        "type_graph_inventory": type_graph_identity,
        "method_count": method_header[5],
        "handle_qword": method_header[10],
        "runtime_type_class": runtime_type_class,
        "array_length_qword": length_qword,
        "array_vector_qword": vector_qword,
        "from_handle": {
            "pointer": from_handle["method_pointer"],
            "metadata": from_handle["metadata_pointer"],
        },
        "candidates": candidates,
        "carried_selection": _carried_selection(
            candidates=candidates,
            selection_evidence_plan=selection_evidence_plan,
            selection_evidence_status=selection_evidence_status,
            executable_sha256=executable_sha256,
            creation_filetime=current[1],
        ),
        "open_arguments": tuple(open_arguments),
        "reference_model_raw": reference_model_raw,
    }


def _carried_selection(
    *, candidates: dict[str, list[dict[str, int]]],
    selection_evidence_plan: Path | None,
    selection_evidence_status: Path | None,
    executable_sha256: str, creation_filetime: int,
) -> dict[str, Any] | None:
    if selection_evidence_plan is None and selection_evidence_status is None:
        return None
    if selection_evidence_plan is None or selection_evidence_status is None:
        raise AcquisitionError(
            "candidate selection evidence requires the plan and the status"
        )
    evidence_plan_path = _owner_file(
        selection_evidence_plan, label="candidate selection evidence plan"
    )
    evidence_status_path = _owner_file(
        selection_evidence_status, label="candidate selection evidence status"
    )
    evidence_plan = read_json(evidence_plan_path)
    evidence_status = read_json(evidence_status_path)
    if (
        not isinstance(evidence_plan, dict)
        or evidence_plan.get("schema")
        != RUNTIME_GENERIC_PARAMETER_DETAIL_PLAN_SCHEMA
        or evidence_plan.get("status") != "prepared"
        or evidence_plan.get("target", {}).get("executable_sha256")
        != executable_sha256
        or evidence_plan.get("target", {}).get("creation_filetime")
        != creation_filetime
        or not isinstance(evidence_status, dict)
        or evidence_status.get("status") != "complete"
        or evidence_status.get("attribute_equivalent_candidate_count") != 1
        or evidence_status.get("constraint_equivalent_candidate_count") != 1
        or evidence_status.get("candidate_selection_carried") is True
    ):
        raise AcquisitionError(
            "candidate selection evidence is not a fresh single-survivor proof"
        )
    evidence_candidates = evidence_plan["contract"][
        "candidate_method_indices_owner_only"
    ]

    def carried(kind: str) -> dict[str, int]:
        index = evidence_status[f"selected_{kind}_candidate_owner_only"]
        base = evidence_candidates[kind + "s"][index]
        for position, candidate in enumerate(candidates[kind + "s"]):
            if ((candidate["metadata"], candidate["pointer"])
                    == (base["metadata"], base["pointer"])):
                return dict(base, position=position)
        raise AcquisitionError(
            "candidate selection evidence topology differs from the "
            f"current {kind} candidates"
        )

    attribute = carried("attribute")
    constraint = carried("constraint")
    return {
        "attribute_index": attribute["position"],
        "constraint_index": constraint["position"],
        "attribute_method_index": attribute["method_index"],
        "constraint_method_index": constraint["method_index"],
        "evidence_plan": file_identity(evidence_plan_path),
        "evidence_status": file_identity(evidence_status_path),
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
static const uint64_t expected_creation=${creation_filetime}ull;
static int generic_instance_current(void) {
    FILETIME creation,exit_time,kernel,user;
    if(GetCurrentProcessId()!=${process_id}u || !GetProcessTimes(GetCurrentProcess(),&creation,&exit_time,&kernel,&user))return 0;
    uint64_t actual=((uint64_t)creation.dwHighDateTime<<32)|creation.dwLowDateTime;
    return actual==expected_creation;
}
static FILE *generic_private_output(const wchar_t *path) {
    int descriptor=_wopen(path,_O_WRONLY|_O_CREAT|_O_EXCL|_O_BINARY,_S_IREAD|_S_IWRITE);
    if(descriptor<0)return NULL;
    FILE *output=_fdopen(descriptor,"wb");
    if(!output){_close(descriptor);_wremove(path);}
    return output;
}
#define ALPHA_BATCH_ARGUMENTS 128u
#define ALPHA_MAX_CONSTRAINTS 64u
typedef struct{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t method_count,generic_method_count,generic_argument_count,image_base,image_bytes,candidate_method_index;char executable[64],identity[64],methods[64],references[64],semantics[64],members[64];}generic_header;
typedef struct{uint32_t method_index,argument_count;uint64_t argument_start;}generic_record;
typedef struct{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t argument_count,constraint_count,image_base,image_bytes;char executable[64],identity[64],generics[64],references[64],semantics[64];}output_header;
typedef struct{uint64_t descriptor;uint32_t attributes,constraint_count;uint64_t constraint_start;}output_record;
_Static_assert(sizeof(generic_header)==$generic_header_bytes,"generic header");
_Static_assert(sizeof(generic_record)==$generic_record_bytes,"generic record");
_Static_assert(sizeof(output_header)==$output_header_bytes,"output header");
_Static_assert(sizeof(output_record)==$output_record_bytes,"output record");
static const char executable_sha256[]="$executable_sha256",identity_sha256[]="$identity_sha256",generic_sha256[]="$generic_sha256",reference_sha256[]="$reference_sha256",semantics_sha256[]="$semantics_sha256";
static const DWORD expected_pid=${process_id}u;static const uint64_t expected_argument_count=${argument_count}ull,expected_method_count=${method_count}ull,expected_image_base=${image_base}ull,expected_image_bytes=${image_bytes}ull;static const uintptr_t runtime_type_class=${runtime_type_class}ull,from_handle_pointer=${from_handle_pointer}ull,from_handle_metadata=${from_handle_metadata}ull;static const uint32_t handle_qword=${handle_qword}u,array_length_qword=${array_length_qword}u,array_vector_qword=${array_vector_qword}u;
static const uintptr_t attribute_pointers[]={$attribute_pointers};static const uintptr_t attribute_metadata[]={$attribute_metadata};static const uintptr_t constraint_pointers[]={$constraint_pointers};static const uintptr_t constraint_metadata[]={$constraint_metadata};
#define ATTRIBUTE_CANDIDATES (sizeof(attribute_pointers)/sizeof(attribute_pointers[0]))
#define CONSTRAINT_CANDIDATES (sizeof(constraint_pointers)/sizeof(constraint_pointers[0]))
static const wchar_t generic_path[]=$generic_path,output_path[]=$output_path,status_path[]=$status_path;
typedef uintptr_t(*static_qword)(uintptr_t,uintptr_t);typedef uintptr_t(*instance_noarg)(uintptr_t,uintptr_t);typedef uint32_t(*instance_dword)(uintptr_t,uintptr_t);
static unsigned char*generic_data;static uint64_t*argument_descriptors;static output_record*records;static uint64_t*constraints;static uint64_t constraint_count,constraint_capacity,capture_index,verify_index,completed_count,verified_count,failure_index,runtime_observed_argument_count,graph_carried_argument_count;static uint32_t failure_kind,selected_attribute,selected_constraint,attribute_equivalent_count,constraint_equivalent_count;static UINT message_id;static WNDPROC original_proc;static volatile LONG action,complete;
static int readable(uintptr_t value,SIZE_T bytes){MEMORY_BASIC_INFORMATION r;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t end=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}
static int object_class(uintptr_t object,uintptr_t expected){uintptr_t value=0;if(!readable(object,8u))return 0;memcpy(&value,(const void*)object,8u);return value==expected;}
static uintptr_t type_object(uint64_t descriptor){static_qword from_handle=(static_qword)from_handle_pointer;uintptr_t object=from_handle(descriptor,from_handle_metadata);return object_class(object,runtime_type_class)?object:0;}
static int type_array(uintptr_t array,uintptr_t**items,uint32_t*count){*items=NULL;*count=0;if(!array||!readable(array,((SIZE_T)array_vector_qword+1u)*8u))return 0;uintptr_t length=0;memcpy(&length,(const void*)(array+(uintptr_t)array_length_qword*8u),8u);if(length>ALPHA_MAX_CONSTRAINTS)return 0;uintptr_t vector=array+(uintptr_t)array_vector_qword*8u;if(length&&!readable(vector,(SIZE_T)length*8u))return 0;for(uint64_t i=0;i<length;i++){uintptr_t item=0;memcpy(&item,(const void*)(vector+i*8u),8u);if(!object_class(item,runtime_type_class))return 0;}*items=(uintptr_t*)vector;*count=(uint32_t)length;return 1;}
static int descriptor_from_type(uintptr_t object,uint64_t*descriptor){*descriptor=0;if(!object_class(object,runtime_type_class)||!readable(object+(uintptr_t)handle_qword*8u,8u))return 0;memcpy(descriptor,(const void*)(object+(uintptr_t)handle_qword*8u),8u);return *descriptor&&!(*descriptor&7u)&&readable(*descriptor,16u);}
static const uint32_t open_argument_indices[]={$open_argument_indices};
static const uint32_t open_argument_count=$open_argument_count;
static int argument_is_open(uint64_t index){
    uint32_t low=0u,high=open_argument_count;
    while(low<high){uint32_t middle=low+(high-low)/2u;if(open_argument_indices[middle]<index)low=middle+1u;else high=middle;}
    return low<open_argument_count&&open_argument_indices[low]==index;
}
$candidate_probe_source
static int append_constraint(uint64_t descriptor){if(!descriptor||constraint_count>=expected_argument_count*ALPHA_MAX_CONSTRAINTS)return 0;if(constraint_count==constraint_capacity){uint64_t next=constraint_capacity?constraint_capacity*2u:4096u;if(next>expected_argument_count*ALPHA_MAX_CONSTRAINTS)next=expected_argument_count*ALPHA_MAX_CONSTRAINTS;uint64_t*grown=realloc(constraints,(SIZE_T)next*8u);if(!grown)return 0;constraints=grown;constraint_capacity=next;}constraints[constraint_count++]=descriptor;return 1;}
static int observe(uint64_t index,uint32_t*attributes,uint64_t values[ALPHA_MAX_CONSTRAINTS],uint32_t*count){*attributes=0;*count=0;uintptr_t object=type_object(argument_descriptors[index]);if(!object)return 0;*attributes=((instance_dword)attribute_pointers[selected_attribute])(object,attribute_metadata[selected_attribute]);if(*attributes&~31u)return 0;uintptr_t array=((instance_noarg)constraint_pointers[selected_constraint])(object,constraint_metadata[selected_constraint]);uintptr_t*items=NULL;if(!type_array(array,&items,count))return 0;for(uint32_t i=0;i<*count;i++){if(!descriptor_from_type(items[i],&values[i]))return 0;for(uint32_t j=0;j<i;j++)if(values[j]==values[i])return 0;}return 1;}
static int capture_batch(void){uint64_t end=capture_index+ALPHA_BATCH_ARGUMENTS;if(end>expected_argument_count)end=expected_argument_count;for(;capture_index<end;capture_index++){output_record*out=&records[capture_index];out->descriptor=argument_descriptors[capture_index];out->constraint_start=constraint_count;uint64_t values[ALPHA_MAX_CONSTRAINTS]={0};uint32_t count=0;if(!observe(capture_index,&out->attributes,values,&count)){if(!argument_is_open(capture_index)){failure_kind=10u;failure_index=capture_index+1u;return 0;}out->attributes=0u;out->constraint_count=0u;graph_carried_argument_count++;completed_count++;continue;}out->constraint_count=count;runtime_observed_argument_count++;for(uint32_t i=0;i<count;i++)if(!append_constraint(values[i])){failure_kind=11u;failure_index=capture_index+1u;return 0;}completed_count++;}return 1;}
static int verify_batch(void){uint64_t end=verify_index+ALPHA_BATCH_ARGUMENTS;if(end>expected_argument_count)end=expected_argument_count;for(;verify_index<end;verify_index++){uint64_t values[ALPHA_MAX_CONSTRAINTS]={0};uint32_t attributes=0,count=0;if(!observe(verify_index,&attributes,values,&count)){if(!argument_is_open(verify_index)){failure_kind=20u;failure_index=verify_index+1u;return 0;}graph_carried_argument_count++;verified_count++;continue;}output_record*out=&records[verify_index];if(attributes!=out->attributes||count!=out->constraint_count){failure_kind=20u;failure_index=verify_index+1u;return 0;}for(uint32_t i=0;i<count;i++)if(values[i]!=constraints[out->constraint_start+i]){failure_kind=21u;failure_index=verify_index+1u;return 0;}verified_count++;}return 1;}
static LRESULT CALLBACK window_proc(HWND window,UINT message,WPARAM wparam,LPARAM lparam){if(message!=message_id)return CallWindowProcW(original_proc,window,message,wparam,lparam);LONG selected=InterlockedCompareExchange(&action,0,0);int ok=selected==1?probe_candidates():selected==2?capture_batch():selected==3?verify_batch():0;InterlockedExchange(&complete,ok?1:-1);return ok;}
typedef struct{DWORD pid;HWND window;uint32_t count;}selection;static BOOL CALLBACK select_window(HWND window,LPARAM value){selection*s=(selection*)(uintptr_t)value;DWORD pid=0;RECT b;if(!IsWindowVisible(window)||GetWindow(window,GW_OWNER)||!GetWindowRect(window,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(window,&pid);if(pid==s->pid){s->window=window;s->count++;}return TRUE;}
static int send_action(HWND window,LONG selected){DWORD_PTR result=0;InterlockedExchange(&action,selected);InterlockedExchange(&complete,0);return SendMessageTimeoutW(window,message_id,0,0,SMTO_BLOCK,60000,&result)&&InterlockedCompareExchange(&complete,0,0)==1;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window){failure_kind=100u;failure_index=s.count;return 0;}message_id=RegisterWindowMessageW(L"ALPHA v2 current runtime generic parameter detail inventory");SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);DWORD error=GetLastError();int ok=message_id&&(original_proc||error==ERROR_SUCCESS);if(ok)ok=send_action(s.window,1);while(ok&&capture_index<expected_argument_count)ok=send_action(s.window,2);while(ok&&verify_index<expected_argument_count)ok=send_action(s.window,3);if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);original_proc=NULL;if(!ok&&!failure_kind)failure_kind=101u;return ok;}
static int read_file(const wchar_t*path,unsigned char**data,SIZE_T*bytes){*data=NULL;*bytes=0;FILE*f=_wfopen(path,L"rb");if(!f||_fseeki64(f,0,SEEK_END))return 0;__int64 size=_ftelli64(f);if(size<0||_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*bytes=(SIZE_T)size;*data=malloc(*bytes?*bytes:1u);int ok=*data&&fread(*data,1,*bytes,f)==*bytes;fclose(f);if(!ok){free(*data);*data=NULL;}return ok;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE input=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(input==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char*object=NULL,*buffer=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;while(ok){DWORD count=0;if(!ReadFile(input,buffer,1048576u,&count,NULL)){ok=0;break;}if(!count)break;if(BCryptHashData(hash,buffer,count,0)<0)ok=0;}if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)<0)ok=0;if(ok)digest_hex(digest,output);if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(input);return ok;}
static int executable_identity(char output[65]){wchar_t path[32768];DWORD n=GetModuleFileNameW(NULL,path,32768);return n&&n<32768&&sha256_file(path,output);}
static void write_status(const char*status,int written){FILE*out=_wfopen(status_path,L"wb");if(!out)return;fprintf(out,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"completed_argument_count\": %llu,\n  \"constraint_reference_count\": %llu,\n  \"verified_argument_count\": %llu,\n  \"runtime_observed_argument_count\": %llu,\n  \"graph_carried_argument_count\": %llu,\n  \"attribute_candidate_count\": %llu,\n  \"constraint_candidate_count\": %llu,\n  \"selected_attribute_candidate_owner_only\": %u,\n  \"selected_constraint_candidate_owner_only\": %u,\n  \"attribute_equivalent_candidate_count\": %u,\n  \"constraint_equivalent_candidate_count\": %u,\n  \"candidate_selection_carried\": %s,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"second_observation\": true,\n  \"candidate_behavior_live_selected\": true,\n  \"saved_generic_parameter_detail_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)completed_count,(unsigned long long)constraint_count,(unsigned long long)verified_count,(unsigned long long)runtime_observed_argument_count,(unsigned long long)graph_carried_argument_count,(unsigned long long)ATTRIBUTE_CANDIDATES,(unsigned long long)CONSTRAINT_CANDIDATES,selected_attribute,selected_constraint,attribute_equivalent_count,constraint_equivalent_count,(carried_attribute<ATTRIBUTE_CANDIDATES&&carried_constraint<CONSTRAINT_CANDIDATES)?"true":"false",(unsigned long long)failure_index,failure_kind,written?"true":"false");fclose(out);}
static int write_output(void){output_header header;memset(&header,0,sizeof(header));memcpy(header.magic,"ALPHAGP1",8);header.version=$output_version;header.header_bytes=sizeof(header);header.record_bytes=sizeof(output_record);header.argument_count=expected_argument_count;header.constraint_count=constraint_count;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;memcpy(header.executable,executable_sha256,64);memcpy(header.identity,identity_sha256,64);memcpy(header.generics,generic_sha256,64);memcpy(header.references,reference_sha256,64);memcpy(header.semantics,semantics_sha256,64);FILE*out=_wfopen(output_path,L"wb");if(!out)return 0;int ok=fwrite(&header,1,sizeof(header),out)==sizeof(header)&&fwrite(records,sizeof(*records),expected_argument_count,out)==expected_argument_count&&fwrite(constraints,8u,constraint_count,out)==constraint_count;if(fclose(out))ok=0;if(!ok)_wremove(output_path);return ok;}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char executable[65],generic_digest[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(executable)||strcmp(executable,executable_sha256)||!sha256_file(generic_path,generic_digest)||strcmp(generic_digest,generic_sha256)){failure_kind=200u;write_status("identity_mismatch",0);return 0;}SIZE_T bytes=0;if(!read_file(generic_path,&generic_data,&bytes)||bytes<sizeof(generic_header)+expected_method_count*sizeof(generic_record)){failure_kind=201u;write_status("input_unavailable",0);return 0;}generic_header*h=(generic_header*)generic_data;if(memcmp(h->magic,"ALPHAMG1",8)||h->version!=1u||h->header_bytes!=sizeof(*h)||h->record_bytes!=sizeof(generic_record)||h->method_count!=expected_method_count||h->generic_argument_count!=expected_argument_count||h->image_base!=expected_image_base||h->image_bytes!=expected_image_bytes||memcmp(h->executable,executable_sha256,64)||memcmp(h->identity,identity_sha256,64)||bytes!=sizeof(*h)+expected_method_count*sizeof(generic_record)+expected_argument_count*8u){failure_kind=202u;write_status("input_invalid",0);return 0;}argument_descriptors=(uint64_t*)(generic_data+sizeof(*h)+expected_method_count*sizeof(generic_record));records=calloc((SIZE_T)expected_argument_count,sizeof(*records));if(!records){failure_kind=203u;write_status("allocation_failed",0);return 0;}if(!dispatch()||completed_count!=expected_argument_count||verified_count!=expected_argument_count){if(!failure_kind)failure_kind=204u;write_status("capture_failed",0);return 0;}int ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def runtime_generic_parameter_detail_source(
    *, binding: dict[str, Any], output_path: Path, status_path: Path,
) -> str:
    from alpha.p01 import NATIVE_PROBE, NATIVE_ATTRIBUTE_VALIDATION
    from alpha.p01 import NATIVE_GLOBALS, NATIVE_WINDOW_PROC, NATIVE_SEND_ACTION, NATIVE_DISPATCH
    attributes = binding["candidates"]["attributes"]
    constraints = binding["candidates"]["constraints"]
    if type(binding.get("creation_filetime")) is not int or not 0 < binding["creation_filetime"] <= 0xFFFFFFFFFFFFFFFF:
        raise AcquisitionError("generic detail source requires a current process creation identity")
    if (type(binding.get("method_argument_count")) is not int
            or type(binding.get("argument_count")) is not int
            or not 0 <= binding["method_argument_count"] <= binding["argument_count"]):
        raise AcquisitionError("generic detail source requires a bound method argument prefix")


    generic_argument_input = binding.get(
        "generic_argument_input", binding["method_generic_inventory"]
    )
    values = {
        "candidate_probe_source": (
            f"static const uint64_t expected_method_argument_count={binding['method_argument_count']}ull;\n"
            + NATIVE_ATTRIBUTE_VALIDATION
            + NATIVE_PROBE.substitute(
                carried_attribute=(binding["carried_selection"] or {}).get(
                    "attribute_index", 0xFFFFFFFF),
                carried_constraint=(binding["carried_selection"] or {}).get(
                    "constraint_index", 0xFFFFFFFF),
            )),
        "generic_header_bytes": RUNTIME_METHOD_GENERIC_HEADER.size,
        "generic_record_bytes": RUNTIME_METHOD_GENERIC_RECORD.size,
        "output_header_bytes": RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size,
        "output_record_bytes": RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size,
        "output_version": RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION,
        "status_schema": RUNTIME_GENERIC_PARAMETER_DETAIL_STATUS_SCHEMA,
        "executable_sha256": binding["binary"]["sha256"],
        "identity_sha256": binding["type_identity_inventory"]["sha256"],
        "generic_sha256": generic_argument_input["sha256"],
        "reference_sha256": binding["type_reference_inventory"]["sha256"],
        "semantics_sha256": binding["semantics"]["sha256"],
        "process_id": binding["process_id"],
        "creation_filetime": binding["creation_filetime"],
        "argument_count": binding["argument_count"],
        "method_count": binding["method_count"],
        "method_argument_count": binding["method_argument_count"],
        "open_argument_indices": ",".join(
            str(index) for index in binding.get("open_arguments", ())
        ) or "0",
        "open_argument_count": len(binding.get("open_arguments", ())),
        "handle_qword": binding["handle_qword"],
        "image_base": binding["image_base"],
        "image_bytes": binding["image_bytes"],
        "runtime_type_class": binding["runtime_type_class"],
        "from_handle_pointer": binding["from_handle"]["pointer"],
        "from_handle_metadata": binding["from_handle"]["metadata"],
        "array_length_qword": binding["array_length_qword"],
        "array_vector_qword": binding["array_vector_qword"],
        "attribute_pointers": ",".join(
            f"{candidate['pointer']}ull" for candidate in attributes
        ),
        "attribute_metadata": ",".join(
            f"{candidate['metadata']}ull" for candidate in attributes
        ),
        "constraint_pointers": ",".join(
            f"{candidate['pointer']}ull" for candidate in constraints
        ),
        "constraint_metadata": ",".join(
            f"{candidate['metadata']}ull" for candidate in constraints
        ),
        "generic_path": _wide_literal(
            _windows_z_path(Path(generic_argument_input["path"]))
        ),
        "output_path": _wide_literal(_windows_z_path(output_path)),
        "status_path": _wide_literal(_windows_z_path(status_path)),
    }
    source = _COLLECTOR.substitute(values)
    seams = (
        ("static LRESULT CALLBACK window_proc(", "\ntypedef struct{DWORD pid;", NATIVE_WINDOW_PROC),
        ("static int send_action(", "\nstatic int dispatch(", NATIVE_SEND_ACTION),
        ("static int dispatch(", "\nstatic int read_file(", NATIVE_DISPATCH),
    )
    for begin, end, replacement in seams:
        if source.count(begin) != 1 or source.count(end) != 1:
            raise AcquisitionError("generic collector guarded dispatch seam differs")
        start = source.index(begin); stop = source.index(end, start)
        source = source[:start] + replacement.strip() + source[stop:]
    source = source.replace("static int readable(", NATIVE_GLOBALS + "\nstatic int readable(", 1)
    replacements = {
        'if(*attributes&~31u)return 0;': 'if(!generic_attributes_valid(index,*attributes))return 0;',
        '_wremove(output_path);_wremove(status_path);':
            'if(GetFileAttributesW(output_path)!=INVALID_FILE_ATTRIBUTES||GetFileAttributesW(status_path)!=INVALID_FILE_ATTRIBUTES)return 0;',
        'FILE*out=_wfopen(output_path,L"wb");': 'FILE*out=generic_private_output(output_path);',
        'FILE*out=_wfopen(status_path,L"wb");': 'FILE*out=generic_private_output(status_path);',
        'GetCurrentProcessId()!=expected_pid||': '!generic_instance_current()||GetCurrentProcessId()!=expected_pid||',
        'int ok=write_output();': 'int ok=generic_instance_current()&&write_output()&&generic_instance_current();',
    }


    for old, new in replacements.items():
        if source.count(old) != 1:
            raise AcquisitionError("generic collector exclusive-output integration seam differs")
        source = source.replace(old, new, 1)
    return source


def prepare_runtime_generic_parameter_detail_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
    method_generic_model: Path, method_generic_inventory: Path,
    output_dir: Path, compiler: Path | None = None,
    type_graph_inventory: Path | None = None,
    selection_evidence_plan: Path | None = None,
    selection_evidence_status: Path | None = None,
    reference_regions_out: dict[str, Any] | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        method_generic_model=method_generic_model,
        method_generic_inventory=method_generic_inventory,
        type_graph_inventory=type_graph_inventory,
        selection_evidence_plan=selection_evidence_plan,
        selection_evidence_status=selection_evidence_status,
        reference_regions_out=reference_regions_out,
    )
    output_path = output_dir / "runtime-generic-parameter-detail.private.bin"
    status_path = (
        output_dir / "runtime-generic-parameter-detail-status.private.json"
    )
    model_path = output_dir / "runtime-generic-parameter-detail.private.json"
    plan_path = output_dir / "runtime-generic-parameter-detail-plan.private.json"
    build_dir = output_dir / "build-generic-parameter-detail"
    generic_argument_input_path = output_dir / "runtime-all-generic-parameters-input.private.bin"
    for existing in (output_path, status_path, model_path, plan_path, generic_argument_input_path, build_dir,
                     output_dir / "runtime-generic-parameter-detail-injector.private.log"):
        if existing.exists() or existing.is_symlink():
            raise AcquisitionError("runtime generic detail requires new capture paths; existing artifacts preserved")
    build_dir = _owner_directory(build_dir)
    source_path = build_dir / "runtime-generic-parameter-detail.c"
    injector_source = build_dir / "runtime-generic-parameter-detail-injector.c"
    injector_path = build_dir / "alpha-generic-parameter-detail-injector.exe"


    original_generic = Path(binding["method_generic_inventory"]["path"]).read_bytes()
    original_header = list(RUNTIME_METHOD_GENERIC_HEADER.unpack_from(original_generic))
    original_header[7] = binding["argument_count"]
    records_end = (
        RUNTIME_METHOD_GENERIC_HEADER.size
        + binding["method_count"] * RUNTIME_METHOD_GENERIC_RECORD.size
    )
    generic_argument_input_path = (
        output_dir / "runtime-all-generic-parameters-input.private.bin"
    )
    generic_argument_input = bytearray(
        RUNTIME_METHOD_GENERIC_HEADER.pack(*original_header)
    )
    generic_argument_input.extend(
        original_generic[RUNTIME_METHOD_GENERIC_HEADER.size:records_end]
    )
    if binding["argument_descriptors"]:
        generic_argument_input.extend(
            struct.pack(
                f"<{binding['argument_count']}Q",
                *binding["argument_descriptors"],
            )
        )
    write_new_bytes(generic_argument_input_path, bytes(generic_argument_input))
    binding["generic_argument_input"] = file_identity(
        generic_argument_input_path
    )
    _private_text(
        source_path,
        runtime_generic_parameter_detail_source(
            binding=binding,
            output_path=output_path,
            status_path=status_path,
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    source_sha256 = file_identity(source_path)["sha256"]
    collector_path = build_dir / (
        "alpha-generic-parameter-detail-"
        + source_sha256[:12]
        + f"-{time.time_ns():x}.dll"
    )
    selected_compiler = _compiler(compiler)


    with ThreadPoolExecutor(max_workers=2) as executor:
        collector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler), "-O2", "-s", "-shared", "-Wall",
                "-Wextra", "-Wformat=2", "-Werror=format", str(source_path),
                "-o", str(collector_path), "-lbcrypt",
            ],
            label="runtime generic parameter detail collector",
            source_path=source_path,
            output_path=collector_path,
        )
        injector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler), "-O2", "-s", "-municode", "-Wall",
                "-Wextra", "-Wformat=2", "-Werror=format",
                str(injector_source), "-o", str(injector_path),
            ],
            label="runtime generic parameter detail injector",
            source_path=injector_source,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_GENERIC_PARAMETER_DETAIL_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "creation_filetime": binding["creation_filetime"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            **binding["instance_inputs"],
            **{
                key: binding[key]
                for key in (
                    "semantics", "type_identity_model",
                    "type_identity_inventory", "type_reference_model",
                    "type_reference_inventory", "method_detail_model",
                    "method_detail_inventory", "method_generic_model",
                    "method_generic_inventory",
                )
            },
            "generic_argument_input": binding["generic_argument_input"],
            "type_graph_inventory": binding["type_graph_inventory"],
            **({
                "selection_evidence_plan": binding["carried_selection"][
                    "evidence_plan"
                ],
                "selection_evidence_status": binding["carried_selection"][
                    "evidence_status"
                ],
            } if binding.get("carried_selection") else {}),
        },
        "generic_argument_input": binding["generic_argument_input"],
        "type_graph_inventory": binding["type_graph_inventory"],
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "contract": {
            "argument_count": binding["argument_count"],
            "method_argument_count": binding["method_argument_count"],
            "type_argument_count": (
                binding["argument_count"] - binding["method_argument_count"]
            ),
            "open_argument_count": len(binding.get("open_arguments", ())),
            "open_argument_policy": "type-graph-carried-open-parameters",
            "record_bytes": RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size,
            "attribute_candidate_count": len(
                binding["candidates"]["attributes"]
            ),
            "constraint_candidate_count": len(
                binding["candidates"]["constraints"]
            ),
            "candidate_method_indices_owner_only": binding["candidates"],
            "candidate_selection_carried_owner_only": (
                None
                if binding.get("carried_selection") is None
                else {
                    "attribute_index": binding["carried_selection"][
                        "attribute_index"
                    ],
                    "constraint_index": binding["carried_selection"][
                        "constraint_index"
                    ],
                    "attribute_method_index": binding["carried_selection"][
                        "attribute_method_index"
                    ],
                    "constraint_method_index": binding["carried_selection"][
                        "constraint_method_index"
                    ],
                    "evidence_plan": binding["carried_selection"][
                        "evidence_plan"
                    ],
                    "evidence_status": binding["carried_selection"][
                        "evidence_status"
                    ],
                }
            ),
            "behavior_selection_required": True,
            "method_variance_rejection_required": True,
            "candidate_selection_policy": "single-survivor-no-ranking/v1",
            "second_observation_required": True,
        },
        "policy": {
            "same_process_required": True,
            "raw_pointers_owner_only": True,
            "saved_generic_parameter_detail_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_GENERIC_PARAMETER_DETAIL_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "argument_count": binding["argument_count"],
        "attribute_candidate_count": len(
            binding["candidates"]["attributes"]
        ),
        "constraint_candidate_count": len(
            binding["candidates"]["constraints"]
        ),
        "policy": plan["policy"],
    }


def _validate_capture(
    *, plan: dict[str, Any], status: dict[str, Any],
    reference_regions: dict[str, Any] | None = None,
) -> tuple[dict[str, Any], dict[str, bool]]:
    from alpha.p01 import generic_attributes_valid
    raw = Path(plan["output_path"]).read_bytes()
    if len(raw) < RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size:
        raise AcquisitionError(
            "runtime generic parameter detail output is truncated"
        )
    header = RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.unpack_from(raw)
    argument_count, constraint_count = header[5:7]
    record_start = RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
    constraint_start = (
        record_start
        + argument_count * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
    )
    header_valid = (
        header[0] == RUNTIME_GENERIC_PARAMETER_DETAIL_MAGIC
        and header[1] == RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION
        and header[2] == RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
        and header[3] == RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
        and header[4] == 0
        and argument_count == plan["contract"]["argument_count"]
        and header[7] == plan["target"]["image_base_owner_only"]
        and header[8] == plan["target"]["image_bytes"]
        and _digest(header[9], label="output executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[10], label="output identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(header[11], label="output generics")
        == plan.get(
            "generic_argument_input",
            plan["inputs"]["method_generic_inventory"],
        )["sha256"]
        and _digest(header[12], label="output references")
        == plan["inputs"]["type_reference_inventory"]["sha256"]
        and _digest(header[13], label="output semantics")
        == plan["inputs"]["semantics"]["sha256"]
        and constraint_start + constraint_count * 8 == len(raw)
    )
    generic_raw = Path(
        plan.get(
            "generic_argument_input",
            plan["inputs"]["method_generic_inventory"],
        )["path"]
    ).read_bytes()
    generic_header = RUNTIME_METHOD_GENERIC_HEADER.unpack_from(generic_raw)
    generic_argument_start = (
        RUNTIME_METHOD_GENERIC_HEADER.size
        + generic_header[5] * RUNTIME_METHOD_GENERIC_RECORD.size
    )
    expected_arguments = struct.unpack_from(
        f"<{argument_count}Q", generic_raw, generic_argument_start
    )
    method_argument_count = plan["contract"].get("method_argument_count")
    if (type(method_argument_count) is not int or not 0 <= method_argument_count <= argument_count):
        raise AcquisitionError("generic detail method argument ownership prefix is invalid")
    original_method_raw = Path(plan["inputs"]["method_generic_inventory"]["path"]).read_bytes()
    if len(original_method_raw) < RUNTIME_METHOD_GENERIC_HEADER.size:
        raise AcquisitionError("generic detail original method argument source is truncated")
    original_method_header = RUNTIME_METHOD_GENERIC_HEADER.unpack_from(original_method_raw)
    original_method_start = RUNTIME_METHOD_GENERIC_HEADER.size + original_method_header[5] * RUNTIME_METHOD_GENERIC_RECORD.size
    if (original_method_header[7] != method_argument_count
            or original_method_start + method_argument_count * 8 != len(original_method_raw)
            or struct.unpack_from(f"<{method_argument_count}Q", original_method_raw, original_method_start)
                != expected_arguments[:method_argument_count]):
        raise AcquisitionError("generic detail method argument prefix differs from original owner inventory")
    constraints = (
        struct.unpack_from(f"<{constraint_count}Q", raw, constraint_start)
        if constraint_count
        else ()
    )
    reference_raw = Path(
        plan["inputs"]["type_reference_inventory"]["path"]
    ).read_bytes()
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
    reference_nodes: dict[int, tuple[int, ...]] = {}
    generic_parameters: set[int] = set()
    reference_limit = max(
        0,
        min(
            reference_header[5],
            (len(reference_raw) - RUNTIME_TYPE_REFERENCE_HEADER.size)
            // RUNTIME_TYPE_REFERENCE_RECORD.size,
        ),
    )


    shared_regions = reference_regions or {}
    shared_rows = shared_regions.get("rows")
    shared_generic_parameters = shared_regions.get("generic_parameters")
    if (shared_rows is not None
            and shared_generic_parameters is not None
            and shared_regions.get("reference_sha256")
            == plan["inputs"]["type_reference_inventory"]["sha256"]):
        reference_nodes = shared_rows
        generic_parameters = shared_generic_parameters
    else:
        reference_region = memoryview(reference_raw)[
            RUNTIME_TYPE_REFERENCE_HEADER.size:RUNTIME_TYPE_REFERENCE_HEADER.size
            + reference_limit * RUNTIME_TYPE_REFERENCE_RECORD.size
        ]
        for row in RUNTIME_TYPE_REFERENCE_RECORD.iter_unpack(reference_region):
            reference_nodes[row[0]] = row
            if row[4] & (1 << 6):
                generic_parameters.add(row[0])
    if reference_limit < reference_header[5]:

        RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
            reference_raw,
            RUNTIME_TYPE_REFERENCE_HEADER.size
            + reference_limit * RUNTIME_TYPE_REFERENCE_RECORD.size,
        )
    rows_valid = header_valid
    cursor = 0
    observed_descriptors: set[int] = set()
    attribute_counts: Counter[int] = Counter()
    constrained_count = 0
    maximum_constraints = 0
    unresolved_constraints: set[int] = set()
    if header_valid:


        record_region = memoryview(raw)[
            record_start:record_start
            + argument_count * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
        ]
        for index, (descriptor, attributes, count, start) in enumerate(
            RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.iter_unpack(record_region)
        ):
            values = constraints[start : start + count]
            if (
                descriptor != expected_arguments[index]
                or not descriptor
                or descriptor & 7
                or not generic_attributes_valid(attributes, method_owned=index < method_argument_count)
                or start != cursor
                or count > 64
                or start + count > constraint_count
                or len(values) != len(set(values))
                or any(not value or value & 7 for value in values)
            ):
                rows_valid = False
                break
            observed_descriptors.add(descriptor)
            attribute_counts[attributes] += 1
            constrained_count += bool(count)
            maximum_constraints = max(maximum_constraints, count)
            unresolved_constraints.update(
                value for value in values if value not in reference_nodes
            )
            cursor += count
    rows_valid = rows_valid and cursor == constraint_count
    counts: dict[str, Any] = {
        "argument_count": argument_count,
        "constraint_reference_count": constraint_count,
        "constrained_argument_count": constrained_count,
        "maximum_constraint_count": maximum_constraints,
        "runtime_observed_argument_count": status.get(
            "runtime_observed_argument_count"
        ),
        "graph_carried_argument_count": status.get(
            "graph_carried_argument_count"
        ),
        "new_constraint_descriptor_count": len(unresolved_constraints),
        "prior_reference_argument_count": len(
            observed_descriptors & generic_parameters
        ),
        "runtime_discovered_argument_count": len(
            observed_descriptors - generic_parameters
        ),
        "attribute_value_counts": {
            str(value): count
            for value, count in sorted(attribute_counts.items())
        },
    }
    checks = {
        "method_owned_parameters_invariant": rows_valid and plan["contract"].get("method_variance_rejection_required") is True,
        "status_schema": status.get("schema")
        == RUNTIME_GENERIC_PARAMETER_DETAIL_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "same_process": status.get("process_id")
        == plan["target"]["process_id"],
        "header_bound": header_valid,
        "all_arguments_captured": status.get("completed_argument_count")
        == argument_count,
        "argument_observation_accounted": (
            type(status.get("runtime_observed_argument_count")) is int
            and type(status.get("graph_carried_argument_count")) is int
            and status["runtime_observed_argument_count"]
            + status["graph_carried_argument_count"]
            == argument_count
        ),
        "records_valid": rows_valid,


        "argument_descriptor_domain_complete": (
            rows_valid
            and len(observed_descriptors) == len(set(expected_arguments))
        ),
        "constraint_count_matches": status.get(
            "constraint_reference_count"
        )
        == constraint_count,
        "second_observation_complete": status.get("second_observation")
        is True
        and status.get("verified_argument_count") == argument_count,
        "candidate_behavior_live_selected": status.get(
            "candidate_behavior_live_selected"
        )
        is True
        and status.get("attribute_candidate_count")
        == plan["contract"]["attribute_candidate_count"]
        and status.get("constraint_candidate_count")
        == plan["contract"]["constraint_candidate_count"]
        and isinstance(
            status.get("selected_attribute_candidate_owner_only"), int
        )
        and 0
        <= status["selected_attribute_candidate_owner_only"]
        < plan["contract"]["attribute_candidate_count"]
        and isinstance(
            status.get("selected_constraint_candidate_owner_only"), int
        )
        and 0
        <= status["selected_constraint_candidate_owner_only"]
        < plan["contract"]["constraint_candidate_count"],
        "candidate_selection_without_ranking": plan["contract"].get("candidate_selection_policy") == "single-survivor-no-ranking/v1"
            and type(status.get("attribute_equivalent_candidate_count")) is int
            and status["attribute_equivalent_candidate_count"] == 1
            and type(status.get("constraint_equivalent_candidate_count")) is int
            and status["constraint_equivalent_candidate_count"] == 1,
        "candidate_selection_carried_verified": (
            (plan["contract"].get("candidate_selection_carried_owner_only") is None
             and status.get("candidate_selection_carried") is False)
            or (isinstance(
                    plan["contract"].get("candidate_selection_carried_owner_only"),
                    dict)
                and status.get("candidate_selection_carried") is True
                and status.get("selected_attribute_candidate_owner_only")
                == plan["contract"]["candidate_selection_carried_owner_only"][
                    "attribute_index"]
                and status.get("selected_constraint_candidate_owner_only")
                == plan["contract"]["candidate_selection_carried_owner_only"][
                    "constraint_index"])
        ),
        "constraint_behavior_nonempty": constraint_count > 0
        and constrained_count > 0,
        "constraint_discovery_descriptors_valid": all(
            value and not value & 7 for value in constraints
        ),
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        )
        is True,
        "saved_detail_absent": status.get(
            "saved_generic_parameter_detail_used"
        )
        is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    return counts, checks


@current_capture_scope
def capture_runtime_generic_parameter_detail_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
    method_generic_model: Path, method_generic_inventory: Path,
    output_dir: Path, wine: Path, wineprefix: Path,
    compiler: Path | None = None, timeout: float = 1800.0,
    type_graph_inventory: Path | None = None,
    selection_evidence_plan: Path | None = None,
    selection_evidence_status: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    reference_regions: dict[str, Any] = {}
    prepare_runtime_generic_parameter_detail_inventory(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        method_generic_model=method_generic_model,
        method_generic_inventory=method_generic_inventory,
        type_graph_inventory=type_graph_inventory,
        selection_evidence_plan=selection_evidence_plan,
        selection_evidence_status=selection_evidence_status,
        reference_regions_out=reference_regions,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan = read_json(
        output_dir / "runtime-generic-parameter-detail-plan.private.json"
    )
    _verify_generic_capture_sources(plan)
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError(
            "runtime generic parameter detail Wine is unavailable"
        )
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "runtime generic parameter detail injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-generic-parameter-detail-injector.private.log",
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
            "runtime generic parameter detail injection failed"
        )
    deadline = time.monotonic() + timeout
    status_path = Path(plan["status_path"])
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        assert_current_capture_alive()
        if status_path.is_file():
            try:
                candidate = read_json(status_path)
            except (OSError, ValueError):
                candidate = None
            if (isinstance(candidate, dict) and candidate.get("status")
                    and candidate["status"] not in ("capturing", "verifying", "running")):
                status = candidate
                break
        time.sleep(0.2)
    if status is None:
        raise AcquisitionError(
            "runtime generic parameter detail capture timed out"
        )
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime generic parameter detail capture failed "
            f"(status={status.get('status')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    _verify_generic_capture_sources(plan)
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    counts, checks = _validate_capture(
        plan=plan, status=status, reference_regions=reference_regions
    )
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime generic parameter detail validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    _verify_generic_capture_sources(plan)
    model = {
        "schema": RUNTIME_GENERIC_PARAMETER_DETAIL_SCHEMA,
        "status": "runtime-validated",
        "target": dict(plan["target"]),
        "inputs": plan["inputs"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "owner_only": True,
        "metadata_complete": False,
        "proof_limits": {"candidate_name_seed_removed": True, "candidate_ranking_removed": True,
                         "operation_semantics_proven": False, "all_native_layouts_proven": False},
    }
    _private_json(Path(plan["model_path"]), model)
    return {
        "schema": RUNTIME_GENERIC_PARAMETER_DETAIL_SCHEMA,
        "status": "runtime-validated",
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "inventory": model["inventory"],
    }


from pathlib import Path
from types import SimpleNamespace
import json
import struct

from alpha.h01 import AcquisitionError
from alpha.p26 import constructed_extent_sources
from alpha.p02 import derive_current_store
from alpha.c07 import _load_types_and_methods
from alpha.c04 import _verify_files
from alpha.p14 import load_runtime_range_observation
from alpha.p25 import _reference_snapshot, _reference_snapshot_file
from alpha.p27 import RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER as H, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD as R, RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD as F
from alpha.h02 import read_json, file_identity


def decode(candidate, raw):
    offset = candidate.get("raw_qword_offset"); key = candidate.get("key")
    if type(offset) is not int or offset < 0 or offset % 8 or offset + 8 > len(raw) or type(key) is not int:
        raise AcquisitionError("field reference native decoder is malformed")
    value = struct.unpack_from("<Q", raw, offset)[0]
    if candidate.get("operation") == "add": value = (value + key) & ((1 << 64) - 1)
    elif candidate.get("operation") == "xor": value ^= key
    else: raise AcquisitionError("field reference native decoder operation is unsupported")
    if not value or value & 7: raise AcquisitionError("field reference native descriptor is invalid")
    return value


def bound_decoder(candidate):
    config = None

    def decode_row(raw):
        nonlocal config
        if config is None:
            offset = candidate.get("raw_qword_offset"); key = candidate.get("key")
            if type(offset) is not int or offset < 0 or offset % 8 or offset + 8 > len(raw) or type(key) is not int:
                raise AcquisitionError("field reference native decoder is malformed")
            operation = candidate.get("operation")
            if operation == "add": config = (offset, key, True)
            elif operation == "xor": config = (offset, key, False)
            else: raise AcquisitionError("field reference native decoder operation is unsupported")
        offset, key, add = config
        if offset + 8 > len(raw):
            raise AcquisitionError("field reference native decoder is malformed")
        value = struct.unpack_from("<Q", raw, offset)[0]
        value = (value + key) & ((1 << 64) - 1) if add else value ^ key
        if not value or value & 7: raise AcquisitionError("field reference native descriptor is invalid")
        return value

    return decode_row


def ordered_field_seeds(*, fields, source_rows, field_counts, base_descriptors, candidate, read, allow_empty=False):
    if type(allow_empty) is not bool:
        raise AcquisitionError("field reference empty-extension policy is invalid")
    if not fields or len(fields) != len(source_rows) or not field_counts:
        raise AcquisitionError("field reference source field domain is empty or incomplete")
    cursors = dict.fromkeys(field_counts, 0); seen_fields = set(); seen = set(); ordered = []; expected = {}
    decode_row = bound_decoder(candidate)
    for row, source in zip(fields, source_rows):
        if (len(source) != 6 or source[0] not in cursors or source[3] != cursors[source[0]] or source[4]
                or source[1] in seen_fields or not source[1] or not isinstance(source[5], bytes)
                or (row.get("generic_index"), row.get("field_ordinal"), row.get("field_metadata_pointer")) != (source[0], source[3], source[1])):
            raise AcquisitionError("field reference native identity/order differs")
        current = read(source[1], len(source[5]))
        if current != source[5]: raise AcquisitionError("field reference native source bytes differ")
        descriptor = decode_row(current)
        if row.get("descriptor") != descriptor: raise AcquisitionError("field reference captured descriptor does not replay")
        prefix = read(descriptor, 16)
        if not isinstance(prefix, bytes) or len(prefix) != 16: raise AcquisitionError("field reference prefix is absent")
        expected[source[1]] = current; expected[descriptor] = prefix
        cursors[source[0]] += 1; seen_fields.add(source[1])
        if descriptor not in seen and descriptor not in base_descriptors: ordered.append(descriptor)
        seen.add(descriptor)
    if cursors != field_counts or (not ordered and not allow_empty) or len(base_descriptors) + len(ordered) > 500000:
        raise AcquisitionError("field reference extension domain is incomplete or exceeds capacity")
    return ordered, expected


_EXTENSION_SOURCE_CACHE: dict[tuple, dict] = {}
_EXTENSION_SOURCE_CACHE_LIMIT = 1


def load_extension_source(field_capture, *, expected_identity, allow_empty=False, include_nominal=False,
                          model=None, model_identity=None):

    if type(include_nominal) is not bool or type(allow_empty) is not bool:
        raise AcquisitionError("field reference domain policy is invalid")
    source = file_identity(field_capture)
    cache_key = (source["sha256"], json.dumps(expected_identity, sort_keys=True), allow_empty, include_nominal)
    entry = _EXTENSION_SOURCE_CACHE.get(cache_key)
    if entry is not None:
        _verify_files(entry["source_inputs"])
        return dict(entry["evidence"])
    if model is not None:


        if model_identity != source:
            raise AcquisitionError("field reference source capture differs from the parsed model")
    else:
        model = read_json(field_capture, maximum_bytes=256 * 1024 * 1024)
    if (model.get("schema") != "alpha.field-type-store-byte-evidence/v1" or model.get("identity") != expected_identity
            or model.get("process_identity_verified") is not True or model.get("two_observations_verified") is not True
            or model.get("all_native_field_bytes_reobserved") is not True or model.get("attribute_counterexample_count") != 0):
        raise AcquisitionError("field reference source lacks current native store observations")
    inputs = dict(model["inputs"]); inputs["field_type_store_observation"] = source
    _verify_files(inputs)
    observation = model["observation"]
    if file_identity(Path(observation["path"])) != observation: raise AcquisitionError("field reference range receipt changed")
    view = load_runtime_range_observation(Path(observation["path"]), expected_identity=expected_identity)


    range_receipt = read_json(Path(observation["path"]))
    inputs["field_type_range_receipt"] = observation
    inputs.update({"field_type_range_" + key: range_receipt[key]
                   for key in ("plan", "source", "observer", "inventory")})
    _verify_files(inputs)
    types, _ = _load_types_and_methods(Path(inputs["native_inventory"]["path"]), executable_sha256=expected_identity["executable_sha256"], expected_identity=inputs["native_inventory"])
    semantics = read_json(Path(inputs["semantics"]["path"]))
    derivation = derive_current_store(binary=Path(inputs["binary"]["path"]), semantics=semantics, types=types,
        snapshot=SimpleNamespace(image_range=(expected_identity["image_base"], expected_identity["image_base"] + expected_identity["image_bytes"]), read=view.read))
    candidate = derivation["candidate"]
    if (json.dumps(candidate, sort_keys=True) != json.dumps(model["derivation"]["decoder"]["candidate"], sort_keys=True)
            or derivation["attributes"] != model["derivation"]["attributes"]):
        raise AcquisitionError("field reference source uses another native type decoder")
    target = {key: expected_identity[key] for key in ("process_id", "creation_filetime", "executable_path", "executable_sha256", "image_bytes")}
    target["image_base_owner_only"] = expected_identity["image_base"]
    _, dependencies = constructed_extent_sources(model_path=Path(inputs["constructed_model"]["path"]), inventory_path=Path(inputs["constructed_inventory"]["path"]),
        expected_target=target, identity_inventory=inputs["type_identity_inventory"], method_inventory=inputs["method_detail_inventory"])
    if any(inputs.get(key) != value for key, value in dependencies.items()):
        raise AcquisitionError("field reference constructed input dependencies differ")
    base_model_record, base_inventory_record = inputs["constructed_type_reference_model"], inputs["constructed_type_reference_inventory"]
    base_model = read_json(Path(base_model_record["path"]))
    if (base_model.get("schema") != "alpha.runtime-type-reference-inventory/v1" or base_model.get("status") != "runtime-validated"
            or base_model.get("target") != target or base_model.get("inventory") != base_inventory_record
            or not base_model.get("checks") or any(value is not True for value in base_model["checks"].values())):
        raise AcquisitionError("field reference base model is not validated/current")
    header, order, nodes = _reference_snapshot_file(Path(base_inventory_record["path"]), label="native field base")
    raw = Path(inputs["constructed_inventory"]["path"]).read_bytes(); h = H.unpack_from(raw); end = H.size + h[5] * R.size
    counts = {row[2]: row[8] for row in R.iter_unpack(raw[H.size:end])}
    fields = list(F.iter_unpack(raw[end:]))
    seeds, expected = ordered_field_seeds(fields=model["constructed_fields"], source_rows=fields, field_counts=counts,
        base_descriptors=set(nodes), candidate=candidate, read=view.read, allow_empty=allow_empty or include_nominal)
    constructed_missing = len(seeds)
    nominal_count = 0
    if include_nominal:
        from alpha.p20 import replay_nominal_field_domain
        nominal, nominal_bytes = replay_nominal_field_domain(model=model, inputs=inputs, identity=expected_identity,
            type_count=len(types), base_descriptors=set(nodes), candidate=candidate, attributes=derivation["attributes"], read=view.read)
        nominal_set = set(nominal)
        seeds = nominal + [pointer for pointer in seeds if pointer not in nominal_set]
        for pointer, value in nominal_bytes.items():
            if pointer in expected and expected[pointer] != value:
                raise AcquisitionError("nominal/constructed field observations disagree")
            expected[pointer] = value
        nominal_count = len(model["nominal_fields"])
    if (not seeds and not allow_empty) or len(nodes) + len(seeds) > 500000:
        raise AcquisitionError("selected field reference domain is empty or exceeds capacity")
    for row in model["code_observations"]:
        code = bytes.fromhex(row["code_hex"])
        if view.read(row["pointer"], len(code)) != code: raise AcquisitionError("field reference source code bytes differ")
        expected[row["pointer"]] = code
    _verify_files(inputs)
    evidence = dict(seed_descriptors=seeds, expected_current_bytes=expected, source_inputs=inputs, field_type_source=source,
        base_type_reference_model=base_model_record, base_type_reference_inventory=base_inventory_record,
        base_type_reference_node_count=header[5], base_type_reference_seed_count=header[6],
        target=target, constructed_field_count=len(fields), candidate=candidate,
        all_constructed_field_descriptors_already_in_base=constructed_missing == 0,
        native_field_domain_scope="nominal-and-constructed" if include_nominal else "constructed",
        nominal_field_count=nominal_count, all_selected_field_descriptors_already_in_base=not seeds,
        role_binding="current-native-field-type-cache-store", metadata_complete=False)
    if len(_EXTENSION_SOURCE_CACHE) >= _EXTENSION_SOURCE_CACHE_LIMIT:
        _EXTENSION_SOURCE_CACHE.clear()
    _EXTENSION_SOURCE_CACHE[cache_key] = {"evidence": dict(evidence), "source_inputs": inputs}
    return evidence


from pathlib import Path
import struct

from alpha.h01 import AcquisitionError
from alpha.p13 import RuntimeProcessProbe, _safe_path
from alpha.p26 import constructed_extent_sources
from alpha.p18 import derive_field_normalization
from alpha.p19 import _implementation_digest
from alpha.c07 import _load_types_and_methods, _load_members
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_HEADER as MH, RUNTIME_NATIVE_MEMBER_DETAIL_FIELD as MF
from alpha.p27 import RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER as H, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD as R, RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD as F
from alpha.c01 import bind_runtime_process
from alpha.c04 import _verify_files
from alpha.p14 import read_current_runtime_ranges, load_runtime_range_observation
from alpha.p15 import merged_ranges
from alpha.c04 import MappedPE
from alpha.p04 import bounded_current_body
from alpha.h02 import write_new_bytes, write_new_json
from alpha.h02 import read_json, file_identity
from alpha.p02 import trace, getter_offset, derive_store_decoder, derive_attribute_load


def derive_codes(binary, semantics, types, image_base):
    selected = {}
    for key in ("field.from_handle", "field.type", "field.attributes"):
        matches = [row for row in semantics.get("operations", []) if row.get("key") == key]
        if len(matches) != 1 or matches[0].get("semantic_identity_resolved") is not True:
            raise AcquisitionError("field store semantic source is not uniquely resolved")
        selected[key] = matches[0]["method_pointer"]
    pointers = sorted({pointer for row in types for pointer in row.method_pointers if pointer})
    following = dict(zip(pointers, pointers[1:])); codes = {}; offsets = {}
    with MappedPE(binary) as image:
        for key, width in (("field.type", 8), ("field.attributes", 4)):
            pointer = selected[key]; end = following.get(pointer)
            if end is None or not 0 < end - pointer <= 65536 or not image.executable_rva(pointer - image_base):
                raise AcquisitionError("field store getter lacks current bounded method extent")
            bounds = image.bounded_code(pointer - image_base, end - image_base)
            if bounds is None or bounds[1] - bounds[0] != end - pointer:
                raise AcquisitionError("field store getter source mapping differs")
            codes[pointer] = bytes(image._mapping[bounds[0]:bounds[1]])
            offsets[key] = getter_offset(codes[pointer], width=width)
        entry, code, thunks = bounded_current_body(image, selected["field.from_handle"], image_base=image_base)
        codes[entry] = code
        for thunk in thunks: codes[thunk["pointer"]] = bytes.fromhex(thunk["code_hex"])
        targets = {row["target_pointer"] for row in trace(code, entry, field_argument="rcx")["calls"]
                   if row["rdx"] == ("field",) and row["target_pointer"] is not None}
        if len(targets) != 1: raise AcquisitionError("field store factory helper is not unique")
        helper, body, thunks = bounded_current_body(image, targets.pop(), image_base=image_base)
        codes[helper] = body
        for thunk in thunks: codes[thunk["pointer"]] = bytes.fromhex(thunk["code_hex"])
        decoder = derive_store_decoder(body, helper, offsets["field.type"])
        attributes = derive_attribute_load(body, helper, candidate=decoder["candidate"], attribute_object_offset=offsets["field.attributes"])
        type_entry, type_body, thunks = bounded_current_body(image, decoder["candidate"]["type_object_helper"], image_base=image_base)
        codes[type_entry] = type_body
        for thunk in thunks: codes[thunk["pointer"]] = bytes.fromhex(thunk["code_hex"])
    return dict(decoder=decoder, attributes=attributes, factory_helper=helper, source_operations=selected), codes


def decode_native(candidate, raw):
    offset = candidate["raw_qword_offset"]
    if offset < 0 or offset + 8 > len(raw): raise AcquisitionError("field store native load is out of range")
    word = struct.unpack_from("<Q", raw, offset)[0]
    descriptor = ((word + candidate["key"]) & ((1 << 64) - 1)) if candidate["operation"] == "add" else word ^ candidate["key"] if candidate["operation"] == "xor" else 0
    if not descriptor or descriptor & 7: raise AcquisitionError("field store decoded pointer is invalid")
    return descriptor


def _decode_store_descriptor(slots, offset, operation, key):


    if offset < 0 or offset + 8 > len(slots) * 8: raise AcquisitionError("field store native load is out of range")
    slot_index = offset >> 3
    shift = (offset & 7) * 8
    if shift:
        word = ((slots[slot_index] >> shift) | (slots[slot_index + 1] << (64 - shift))) & _MASK64
    else:
        word = slots[slot_index]
    descriptor = ((word + key) & _MASK64) if operation == "add" else word ^ key if operation == "xor" else 0
    if not descriptor or descriptor & 7: raise AcquisitionError("field store decoded pointer is invalid")
    return descriptor


def compare_nominal(records, prefixes, attribute_load):
    offset, width = attribute_load["descriptor_attribute_offset"], attribute_load["descriptor_attribute_bytes"]
    if not 0 <= offset < offset + width <= 16: raise AcquisitionError("field store attribute load exceeds observed prefix")
    exact = shape = attributes = 0; counterexamples = []
    head, tail = offset, offset + width
    for row in records:
        descriptor = row["descriptor"]
        incoming, reflected = prefixes[descriptor], prefixes[row["reflection_descriptor"]]
        if len(incoming) != 16 or len(reflected) != 16: raise AcquisitionError("field store prefix is incomplete")
        exact += descriptor == row["reflection_descriptor"]


        equal = incoming[:head] == reflected[:head] and incoming[tail:] == reflected[tail:]
        attr_equal = int.from_bytes(incoming[head:tail], "little") == row["reflection_attributes"]
        shape += equal; attributes += attr_equal
        if (not equal or not attr_equal) and len(counterexamples) < 12:
            counterexamples.append(dict(row, prefix_type_equal=equal, attributes_equal=attr_equal,
                incoming_prefix=incoming.hex(), reflected_prefix=reflected.hex()))
    return dict(nominal_field_count=len(records), descriptor_pointer_exact_matches=exact,
        type_prefix_except_field_attributes_matches=shape, field_attributes_exact_matches=attributes,
        type_prefix_counterexample_count=len(records) - shape, attribute_counterexample_count=len(records) - attributes,
        representative_counterexamples=counterexamples, nominal_type_prefix_and_attributes_complete=bool(records) and shape == attributes == len(records))


def capture(event_plan, member_plan, constructed_model, constructed_inventory, output, wine, wineprefix,
            *, compiler=None, timeout=1800.0):
    event_plan, member_plan, constructed_model, constructed_inventory, output = (_safe_path(Path(p)) for p in
        (event_plan, member_plan, constructed_model, constructed_inventory, output))
    selected = {"event_plan": file_identity(event_plan), "member_plan": file_identity(member_plan)}
    event, members = read_json(event_plan), read_json(member_plan)
    target = event["target"]
    if members["target"] != target: raise AcquisitionError("field store source process domains differ")
    selected.update(event["inputs"])
    for key, record in members["inputs"].items():
        if key in selected and any(selected[key].get(field) != record.get(field) for field in ("path", "bytes", "sha256")): raise AcquisitionError("field store source artifacts differ")
        if key not in selected: selected[key] = record
    selected["member_detail_inventory"] = file_identity(Path(members["output_path"]))
    _, extra = constructed_extent_sources(model_path=constructed_model, inventory_path=constructed_inventory,
        expected_target=target, identity_inventory=selected["type_identity_inventory"], method_inventory=selected["method_detail_inventory"])
    selected.update(extra); _verify_files(selected)
    binary = Path(target["executable_path"]); selected["binary"] = file_identity(binary)
    if selected["binary"]["sha256"] != target["executable_sha256"]: raise AcquisitionError("field store executable changed")
    if any(output.is_relative_to(Path(record["path"]).parent) for record in selected.values()):
        raise AcquisitionError("field store output must not modify source evidence")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        raise AcquisitionError("field store capture requires an empty stage directory")
    output.mkdir(mode=0o700, parents=True, exist_ok=True)
    probe = RuntimeProcessProbe(binary=binary, wine=wine, wineprefix=wineprefix, compiler=compiler, build_dir=output / "probe")
    current = probe()
    for key, value in target.items():
        actual = current.get("image_base" if key == "image_base_owner_only" else key)
        if type(actual) is not type(value) or actual != value: raise AcquisitionError("field store source process is stale")
    implementation = _implementation_digest()
    drivers = {name: file_identity(Path(__file__).with_name(name)) for name in (Path(__file__).name, "p02.py")}
    for name, record in drivers.items():
        write_new_bytes(output / "drivers" / name, Path(record["path"]).read_bytes())
        selected["driver_" + name] = file_identity(output / "drivers" / name)
    normalization = derive_field_normalization(binary=binary, inputs=members["inputs"], inventory=selected["member_detail_inventory"], target=target)
    types, _ = _load_types_and_methods(Path(selected["native_inventory"]["path"]), executable_sha256=target["executable_sha256"], expected_identity=selected["native_inventory"])
    domains, _ = _load_members(Path(selected["native_member_inventory"]["path"]), executable_sha256=target["executable_sha256"], expected_identity=selected["native_member_inventory"], type_count=len(types))
    semantics = read_json(Path(selected["semantics"]["path"]))
    if semantics.get("status") != "resolved" or semantics.get("binary") != selected["binary"]:
        raise AcquisitionError("field store semantics are not bound to current binary")
    derivation, codes = derive_codes(binary, semantics, types, current["image_base"])
    candidate = derivation["decoder"]["candidate"]
    candidate_offset = candidate["raw_qword_offset"]; candidate_operation = candidate["operation"]; candidate_key = candidate["key"]
    raw = Path(selected["member_detail_inventory"]["path"]).read_bytes(); mh = MH.unpack_from(raw)
    details = list(MF.iter_unpack(raw[MH.size:MH.size + mh[5] * MF.size]))
    if len(details) != len(domains[0]) or not details: raise AcquisitionError("field store nominal domain count differs")


    nominal, constructed, native = [], [], {}
    for member, detail in zip(domains[0], details):
        if member.kind or member.definition_index != detail[0] or member.member_index != detail[1] or member.pointer != detail[2]:
            raise AcquisitionError("field store nominal field identity differs")
        slots = member.slots
        raw = struct.pack(f"<{len(slots)}Q", *slots); native[member.pointer] = raw
        descriptor = _decode_store_descriptor(slots, candidate_offset, candidate_operation, candidate_key)
        nominal.append(dict(type_index=member.definition_index, field_ordinal=member.member_index,
            field_metadata_pointer=member.pointer, descriptor=descriptor, reflection_descriptor=detail[3], reflection_attributes=detail[5]))
    raw = constructed_inventory.read_bytes(); header = H.unpack_from(raw); end = H.size + header[5] * R.size
    counts = {row[2]: row[8] for row in R.iter_unpack(raw[H.size:end])}; cursors = dict.fromkeys(counts, 0)
    for row in F.iter_unpack(raw[end:]):
        owner, pointer, offset, ordinal, reserved, data = row
        if owner not in cursors or ordinal != cursors[owner] or reserved or pointer in native:
            raise AcquisitionError("field store constructed native domain differs")
        cursors[owner] += 1; native[pointer] = data
        constructed.append(dict(generic_index=owner, field_ordinal=ordinal, field_metadata_pointer=pointer, descriptor=decode_native(candidate, data)))
    if cursors != counts: raise AcquisitionError("field store constructed field count differs")
    descriptors = {row["descriptor"] for row in nominal + constructed} | {row["reflection_descriptor"] for row in nominal}
    observed_native = {**native, **codes}
    requests = merged_ranges([(p, len(raw)) for p, raw in observed_native.items()] + [(p, 16) for p in descriptors])
    def unchanged():
        _verify_files(selected); _verify_files(drivers)
        if _implementation_digest() != implementation: raise AcquisitionError("field store implementation changed")
    unchanged()
    with bind_runtime_process(current):
        read_current_runtime_ranges(binary=binary, ranges=requests, output_dir=output / "ranges", wine=wine, wineprefix=wineprefix,
                                    compiler=compiler)
    receipt = output / "ranges" / "runtime-ranges.private.json"
    view = load_runtime_range_observation(receipt, expected_identity=current)
    for pointer, expected in observed_native.items():
        if view.read(pointer, len(expected)) != expected: raise AcquisitionError("field store current native/code bytes changed")
    helper = derivation["factory_helper"]
    replay = derive_store_decoder(view.read(helper, len(codes[helper])), helper, candidate["object_field_offset"])
    if replay != derivation["decoder"]: raise AcquisitionError("field store sealed decoder replay differs")
    prefixes = {p: view.read(p, 16) for p in descriptors}
    if any(not isinstance(raw, bytes) or len(raw) != 16 for raw in prefixes.values()): raise AcquisitionError("field store descriptor prefix is missing")
    result = compare_nominal(nominal, prefixes, derivation["attributes"])
    unchanged()
    if probe() != current: raise AcquisitionError("field store current process changed")
    unchanged()
    result.update(schema="alpha.field-type-store-byte-evidence/v1", identity=current, inputs=selected, implementation=implementation,
        derivation=derivation, observation=file_identity(receipt), field_normalization=normalization,
        nominal_fields=nominal, constructed_fields=constructed, descriptor_prefixes={p: raw.hex() for p, raw in prefixes.items()},
        constructed_field_count=len(constructed), incoming_descriptor_count=len({row["descriptor"] for row in nominal + constructed}),
        code_observations=[dict(pointer=p, code_hex=raw.hex()) for p, raw in codes.items()],
        process_identity_verified=True, two_observations_verified=True, all_native_field_bytes_reobserved=True,
        descriptor_size_proven=False, constructed_field_type_graph_complete=False, inherited_bootstrap_semantic_assumptions=True,
        target_code_injection_used=False, target_method_invoked=False, metadata_complete=False, fresh_one_command_success=False)
    result["status"] = "runtime-observed"
    write_new_json(output / "runtime-field-type-store.private.json", result)
    return {key: value for key, value in result.items() if isinstance(value, (bool, int))} | {
        "status": result["status"], "model": file_identity(output / "runtime-field-type-store.private.json")
    }


def capture_runtime_field_type_store(*, binary, event_capture_plan, member_capture_plan,
        constructed_generic_model, constructed_generic_inventory, output_dir, wine, wineprefix,
        compiler=None, timeout=1800.0):

    target = read_json(event_capture_plan).get("target", {})
    if (str(binary.expanduser().resolve()) != target.get("executable_path")
            or file_identity(binary)["sha256"] != target.get("executable_sha256")):
        raise AcquisitionError("field store selected executable differs from the current capture plan")
    return capture(event_capture_plan, member_capture_plan, constructed_generic_model,
        constructed_generic_inventory, output_dir, wine, wineprefix, compiler=compiler, timeout=timeout)


import hashlib
import json
import struct
from collections import Counter
from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.c01 import project_interface_pair
from alpha.h02 import file_identity
from alpha import p36 as source


_HEADER = struct.Struct('<8sIIIIQQQQ64s64s')
_ENTRY = struct.Struct('<IIIIIIIB3xQQ')
_MAGIC = b'ALPHAIP1'
_ABSENT = 0xFFFFFFFF
_MASK64 = (1 << 64) - 1
_SOURCE_SEMANTIC_CHECKS = frozenset({
    'all_mapping_rows_valid', 'target_methods_in_proven_inheritance_chain',
    'target_methods_are_instance_nonconstructors', 'target_method_arities_match_interfaces'})


def validate_interface_projection(*, plan, status, declarations, expected_identity):

    target = plan['target']
    if (any(target.get(key) != expected_identity[key] for key in
            ('process_id', 'executable_path', 'executable_sha256'))
        or status.get('process_creation_filetime_owner_only') != expected_identity['creation_filetime']):
        raise AcquisitionError('interface projection process instance differs')
    encoded = declarations['encoded']
    bound_inputs = {key: value for key, value in encoded['binding'].items()
                    if isinstance(value, dict) and 'path' in value and key != 'binary'}
    if plan['inputs'] != bound_inputs:
        raise AcquisitionError('interface projection source input topology differs')
    counts, raw_checks = source._validate(plan, status)
    if any(value is not True for key, value in raw_checks.items() if key not in _SOURCE_SEMANTIC_CHECKS):
        raise AcquisitionError('interface projection physical source validation failed')
    for key in ('model', 'inventory'):
        record = declarations[key]
        if file_identity(Path(record['path'])) != record:
            raise AcquisitionError('interface projection declaration artifact changed')
    path = Path(plan['output_path'])
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != counts['inventory_sha256']:
        raise AcquisitionError('interface projection raw inventory changed during validation')
    raw_identity = file_identity(path)
    header = source.RUNTIME_INTERFACE_METHOD_MAP_HEADER.unpack_from(raw)
    pairs, mappings = header[5:7]
    mapping_start = source.RUNTIME_INTERFACE_METHOD_MAP_HEADER.size + pairs * source.RUNTIME_INTERFACE_METHOD_MAP_PAIR.size
    expected = {contract.interface: set(contract.methods) for contract in declarations['interface_contracts']}
    inputs = {'raw_interface_inventory': raw_identity, 'vtable_declaration_model': declarations['model'],
              'vtable_declaration_inventory': declarations['inventory']}
    digest = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    payload = bytearray(_HEADER.pack(_MAGIC, 1, _HEADER.size, _ENTRY.size, 0, pairs, mappings,
        expected_identity['process_id'], expected_identity['creation_filetime'],
        expected_identity['executable_sha256'].encode(), digest.encode()))
    payload.extend(bytes(mappings * _ENTRY.size))
    semantic_counts, interface_only = Counter(), []
    for index in range(pairs):
        descriptor, target, interface, offset, count, first = source.RUNTIME_INTERFACE_METHOD_MAP_PAIR.unpack_from(raw,
            source.RUNTIME_INTERFACE_METHOD_MAP_HEADER.size + index * source.RUNTIME_INTERFACE_METHOD_MAP_PAIR.size)
        rows = [source.RUNTIME_INTERFACE_METHOD_MAP_ENTRY.unpack_from(raw,
            mapping_start + (first + j) * source.RUNTIME_INTERFACE_METHOD_MAP_ENTRY.size) for j in range(count)]
        projected = project_interface_pair(rows, target=target, interface=interface, descriptor=descriptor, offset=offset,
            expected_interface_methods=expected[interface], methods=declarations['methods'],
            target_lineage=declarations['lineages'][target], records=encoded['records'], words=encoded['words'],
            projection=declarations['projection'], metadata_indexes=declarations['metadata_indexes'])
        semantic_counts['pair_count'] += 1
        for local, row in enumerate(projected):
            fields = (row.interface_method, row.observed_source_method, row.declaration_method,
                _ABSENT if row.class_declaration_method is None else row.class_declaration_method,
                _ABSENT if row.implementation_method is None else row.implementation_method,
                row.virtual_slot, index, row.declaration_role, row.observed_interface_metadata, row.observed_source_metadata)
            at = _HEADER.size + (first + local) * _ENTRY.size
            _ENTRY.pack_into(payload, at, *fields)
            if _ENTRY.unpack_from(payload, at) != fields:
                raise AcquisitionError('interface projection row roundtrip differs')
            semantic_counts['mapping_count'] += 1
            semantic_counts['implemented_slots' if row.implementation_method is not None else 'abstract_unimplemented_slots'] += 1
            if row.declaration_role == 2:
                interface_only.append({'pair_index': index, 'target': target, 'descriptor': descriptor, **vars(row)})
    if semantic_counts['mapping_count'] != mappings or semantic_counts['pair_count'] != pairs:
        raise AcquisitionError('interface projection full domain is not closed')
    if file_identity(path) != raw_identity:
        raise AcquisitionError('interface projection source inventory changed')
    for key in ('model', 'inventory'):
        if file_identity(Path(declarations[key]['path'])) != declarations[key]:
            raise AcquisitionError('interface projection declaration changed during validation')
    return {'payload': payload, 'inputs': inputs, 'counts': dict(semantic_counts),


        'checks': {**{'raw_source_' + key: value for key, value in raw_checks.items() if key not in _SOURCE_SEMANTIC_CHECKS},
            'all_mapping_source_methoddefs_match_current_vtables': True,
            'all_mapping_source_methodinfos_match_current_vtables': True,
            'all_resolved_class_declarations_in_lineage': True,
            'all_resolved_declaration_arities_match': True,
            'all_interface_only_contexts_proven': True, 'no_synthetic_implementations': True,
            'all_semantic_rows_accounted': True, 'semantic_row_roundtrip_exact': True},
        'raw_relation_checks': {key: raw_checks[key] for key in _SOURCE_SEMANTIC_CHECKS},
        'raw_relation_failure_pair_count': counts['relation_failure_pair_count'],
        'interface_only_contexts_owner_only': interface_only, 'metadata_complete': False,
        'generic_signature_substitution_complete': False, 'standard_metadata_vtable_reconstruction_complete': False}
