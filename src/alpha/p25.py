from alpha.h02 import windows_run as _host_run

import json
import os
import stat
import struct
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import _build, _compiler, _owner_directory, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import (
    AcquisitionError,
    owner_only_path_bits,
    owner_uid,
    same_executable_path,
)
from alpha.p14 import current_capture_scope, assert_current_capture_alive
from alpha.p01 import string_layout_replay_scope
from alpha.c01 import current_runtime_process_binding
from alpha.h02 import write_new_bytes as _private_bytes, write_new_json as _private_json, write_new_text as _private_text
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p24 import RUNTIME_EVENT_MODULE_EVENT, RUNTIME_EVENT_MODULE_HEADER, RUNTIME_EVENT_MODULE_MAGIC, RUNTIME_EVENT_MODULE_MODULE, RUNTIME_EVENT_MODULE_SCHEMA, RUNTIME_EVENT_MODULE_VERSION
from alpha.p22 import RUNTIME_METHOD_DETAIL_HEADER, RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_METHOD, RUNTIME_METHOD_DETAIL_PARAMETER, RUNTIME_METHOD_DETAIL_SCHEMA, RUNTIME_METHOD_DETAIL_VERSION
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER, RUNTIME_NATIVE_MEMBER_DETAIL_MAGIC, RUNTIME_NATIVE_MEMBER_DETAIL_SCHEMA, RUNTIME_NATIVE_MEMBER_DETAIL_VERSION
from alpha.p21 import RUNTIME_TYPE_GRAPH_HEADER, RUNTIME_TYPE_GRAPH_MAGIC, RUNTIME_TYPE_GRAPH_RECORD, RUNTIME_TYPE_GRAPH_SCHEMA, RUNTIME_TYPE_GRAPH_VERSION, _binding as _graph_binding
from alpha.p19 import _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.h02 import file_identity, read_json


RUNTIME_TYPE_REFERENCE_PLAN_SCHEMA = "alpha.runtime-type-reference-plan/v1"
RUNTIME_TYPE_REFERENCE_STATUS_SCHEMA = "alpha.runtime-type-reference-status/v1"
RUNTIME_TYPE_REFERENCE_SCHEMA = "alpha.runtime-type-reference-inventory/v1"
RUNTIME_TYPE_REFERENCE_MAGIC = b"ALPHATR1"
RUNTIME_TYPE_REFERENCE_VERSION = 1
RUNTIME_TYPE_REFERENCE_HEADER = struct.Struct(
    "<8sIIIIQQQQQQQ64s64s64s64s64s"
)
RUNTIME_TYPE_REFERENCE_RECORD = struct.Struct("<QQQIIIIIIIIQQQQQQQQ")
RUNTIME_TYPE_REFERENCE_SEED_MAGIC = b"ALPHARS1"
RUNTIME_TYPE_REFERENCE_SEED_VERSION = 3
RUNTIME_TYPE_REFERENCE_SEED_HEADER = struct.Struct(
    "<8sIIQ64s64s64s64s64s64s64s64s"
)


_QWORD = struct.Struct("<Q")


_QWORD_RUN_PACKERS: dict[int, struct.Struct] = {}


def _qword_run(raw: bytes, start: int, count: int) -> tuple[int, ...]:
    if not count:
        return ()
    end = start + count * 8
    if start < 0 or end > len(raw):
        return tuple(
            struct.unpack_from("<Q", raw, start + index * 8)[0]
            for index in range(count)
        )
    packer = _QWORD_RUN_PACKERS.get(count)
    if packer is None:
        packer = _QWORD_RUN_PACKERS[count] = struct.Struct(f"<{count}Q")
    return tuple(packer.unpack_from(raw, start))

TYPE_REFERENCE_ENUM = 1 << 0
TYPE_REFERENCE_VALUE_TYPE = 1 << 1
TYPE_REFERENCE_GENERIC = 1 << 2
TYPE_REFERENCE_GENERIC_DEFINITION = 1 << 3
TYPE_REFERENCE_BYREF = 1 << 4
TYPE_REFERENCE_INTERFACE = 1 << 5
TYPE_REFERENCE_GENERIC_PARAMETER = 1 << 6
TYPE_REFERENCE_ARRAY = 1 << 7
TYPE_REFERENCE_POINTER = 1 << 8
TYPE_REFERENCE_SHAPE_MASK = (1 << 9) - 1

_REQUIRED_OPERATIONS = (
    "type.from_handle",
    "type.name",
    "type.namespace",
    "type.base_type",
    "type.declaring_type",
    "type.element_type",
    "type.interfaces",
    "type.is_enum",
    "type.is_value_type",
    "type.is_byref",
    "type.is_generic",
    "type.is_generic_definition",
    "type.generic_definition",
    "type.generic_arguments",
    "type.attributes",
)

_EMPTY_INPUT_SHA256 = "0" * 64

_REFERENCE_PROOF_LIMITS = {
    "all_native_layouts_current_derived": False,
    "lossless_type_reference_names": True,
    "string_fields_current_code_derived": True,
    "pointer_free_empty_name_aliases": True,
    "metadata_complete": False,
}


class _DescriptorDiscoveryOrder:

    def __init__(self):
        self._values: dict[int, None] = {}

    def add(self, descriptor):
        self._values.setdefault(descriptor, None)

    def update(self, descriptors):
        if isinstance(descriptors, (set, frozenset)):
            raise AcquisitionError("reference discovery requires source order, not an unordered pointer set")
        for descriptor in descriptors:
            self.add(descriptor)

    def __iter__(self):
        return iter(self._values)

    def __len__(self):
        return len(self._values)


def _bind_reference_instance(binding, binary):
    from alpha.p24 import _validate_current_identity_source
    from alpha.c04 import _verify_files
    current = current_runtime_process_binding()
    if current is None:
        raise AcquisitionError("type-reference preparation requires an explicitly bound current process")
    if (
        type(binding["process_id"]) is not int
        or binding["process_id"] != current[0]
        or not same_executable_path(binary, current[2])
    ):
        raise AcquisitionError("type-reference source process differs from current instance")
    type_plan = read_json(Path(binding["type_identity_plan"]["path"]))
    native = type_plan.get("inputs", {}).get("native_inventory")
    if not isinstance(native, dict):
        raise AcquisitionError("type-reference original native type source is absent")
    replay = _validate_current_identity_source(dict(binding, native_inventory=native), current)
    records = dict(replay, native_inventory=native, type_identity_plan=binding["type_identity_plan"],
                   type_identity_status=binding["type_identity_status"], snapshot=binding["snapshot"])
    from alpha.p18 import load_runtime_string_layout_candidate
    event_model = read_json(Path(binding["event_module_model"]["path"]))
    layout_record = event_model.get("inputs", {}).get("string_layout_model")
    _verify_files({"layout": layout_record})
    layout = load_runtime_string_layout_candidate(model_path=Path(layout_record["path"]),
        expected_identity={"executable_path": str(
            Path(current[2]).expanduser().resolve()
        ), "executable_sha256": binding["binary"]["sha256"],
            "process_id": current[0], "creation_filetime": current[1], "image_base": binding["image_base"],
            "image_bytes": binding["image_bytes"]},
        expected_inputs={"snapshot": binding["snapshot"], "native_inventory": native})
    if layout["class_pointer"] != binding["string_class"]:
        raise AcquisitionError("TypeRef String class differs from current derived layout")
    records["string_layout_model"] = layout_record
    _verify_files(records)
    binding["string_layout_model"] = layout_record
    binding["string_layout_contract"] = layout
    binding["capture_identity_inputs"] = records
    binding["creation_filetime"] = current[1]
    from alpha.p14 import derive_current_contract
    binding["descriptor_byref_contract"] = derive_current_contract(binding)


def _verify_reference_capture_sources(plan):
    from alpha.c04 import _verify_files
    current = current_runtime_process_binding()
    target = plan["target"]
    if (type(target.get("process_id")) is not int or type(target.get("creation_filetime")) is not int or
        current is None or current[0] != target.get("process_id") or
        current[1] != target.get("creation_filetime") or
        not same_executable_path(current[2], target.get("executable_path"))):
        raise AcquisitionError("type-reference plan is not bound to the current process instance")
    records = {}
    empty = {"path": None, "sha256": _EMPTY_INPUT_SHA256, "bytes": 0, "role": "not-applicable-in-base-bootstrap"}
    for role, record in plan["inputs"].items():
        if record == empty and role in ("method_generic_inventory", "generic_parameter_detail_inventory"):
            continue
        records[role] = record
    records.update(seed=plan["seed"], collector=plan["collector"], injector=plan["injector"])
    _verify_files(records)
    assert_current_capture_alive()


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime type reference {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime type reference {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime type reference {label} digest is invalid"
        )
    return value


def _validated_model(
    *, model_path: Path, inventory_path: Path, schema: str,
    executable_sha256: str, label: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    model_path = _owner_file(model_path, label=f"{label} model")
    inventory_path = _owner_file(inventory_path, label=f"{label} inventory")
    model = read_json(model_path)
    identity = file_identity(inventory_path)
    if (
        not isinstance(model, dict)
        or model.get("schema") != schema
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or not all(model.get("checks", {}).values())
        or model.get("inventory", model.get("identity_inventory", {})).get(
            "sha256"
        )
        != identity["sha256"]
    ):
        raise AcquisitionError(f"runtime type reference {label} is stale")
    return file_identity(model_path), identity


def _seed_inventory(
    *, executable_sha256: str, identity_path: Path, method_path: Path,
    native_path: Path, event_path: Path, graph_path: Path,
    method_generic_path: Path | None = None,
    generic_parameter_detail_path: Path | None = None,
) -> tuple[list[int], tuple[str, ...], set[int], set[int]]:
    identity_raw = identity_path.read_bytes()
    method_raw = method_path.read_bytes()
    native_raw = native_path.read_bytes()
    event_raw = event_path.read_bytes()
    graph_raw = graph_path.read_bytes()
    if (
        method_generic_path is None
        and generic_parameter_detail_path is not None
    ):
        raise AcquisitionError(
            "runtime type reference generic seed inputs are incomplete"
        )
    method_generic_raw = (
        method_generic_path.read_bytes()
        if method_generic_path is not None
        else b""
    )
    generic_parameter_detail_raw = (
        generic_parameter_detail_path.read_bytes()
        if generic_parameter_detail_path is not None
        else b""
    )
    seeds = _DescriptorDiscoveryOrder()

    if len(identity_raw) < _IDENTITY_HEADER.size:
        raise AcquisitionError("runtime type reference identity is truncated")
    identity_header = _IDENTITY_HEADER.unpack_from(identity_raw)
    type_count = identity_header[5]
    if (
        identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or identity_header[2] != _IDENTITY_HEADER.size
        or identity_header[3] != _IDENTITY_RECORD.size
        or _digest(identity_header[9], label="identity executable")
        != executable_sha256
        or _IDENTITY_HEADER.size + type_count * _IDENTITY_RECORD.size
        > len(identity_raw)
    ):
        raise AcquisitionError("runtime type reference identity is invalid")
    for row in _IDENTITY_RECORD.iter_unpack(
        memoryview(identity_raw)[
            _IDENTITY_HEADER.size :
            _IDENTITY_HEADER.size + type_count * _IDENTITY_RECORD.size
        ]
    ):
        descriptor = row[2]
        if not descriptor:
            raise AcquisitionError("runtime type reference identity descriptor is absent")
        seeds.add(descriptor)

    if len(method_raw) < RUNTIME_METHOD_DETAIL_HEADER.size:
        raise AcquisitionError("runtime type reference methods are truncated")
    method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(method_raw)
    method_count, parameter_count = method_header[5:7]
    parameter_start = (
        RUNTIME_METHOD_DETAIL_HEADER.size
        + method_count * RUNTIME_METHOD_DETAIL_METHOD.size
    )
    if (
        method_header[0] != RUNTIME_METHOD_DETAIL_MAGIC
        or method_header[1] != RUNTIME_METHOD_DETAIL_VERSION
        or method_header[2] != RUNTIME_METHOD_DETAIL_HEADER.size
        or method_header[3] != RUNTIME_METHOD_DETAIL_METHOD.size
        or method_header[4] != RUNTIME_METHOD_DETAIL_PARAMETER.size
        or _digest(method_header[12], label="method executable")
        != executable_sha256
        or parameter_start
        + parameter_count * RUNTIME_METHOD_DETAIL_PARAMETER.size
        > len(method_raw)
    ):
        raise AcquisitionError("runtime type reference methods are invalid")
    for row in RUNTIME_METHOD_DETAIL_METHOD.iter_unpack(
        memoryview(method_raw)[
            RUNTIME_METHOD_DETAIL_HEADER.size :
            RUNTIME_METHOD_DETAIL_HEADER.size
            + method_count * RUNTIME_METHOD_DETAIL_METHOD.size
        ]
    ):
        descriptor = row[4]
        if descriptor:
            seeds.add(descriptor)
    for row in RUNTIME_METHOD_DETAIL_PARAMETER.iter_unpack(
        memoryview(method_raw)[
            parameter_start :
            parameter_start
            + parameter_count * RUNTIME_METHOD_DETAIL_PARAMETER.size
        ]
    ):
        descriptor = row[2]
        if not descriptor:
            raise AcquisitionError("runtime type reference parameter type is absent")
        seeds.add(descriptor)

    if len(native_raw) < RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size:
        raise AcquisitionError("runtime type reference fields are truncated")
    native_header = RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.unpack_from(native_raw)
    field_count = native_header[5]
    if (
        native_header[0] != RUNTIME_NATIVE_MEMBER_DETAIL_MAGIC
        or native_header[1] != RUNTIME_NATIVE_MEMBER_DETAIL_VERSION
        or native_header[2] != RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
        or native_header[3] != RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size
        or _digest(native_header[12], label="native member executable")
        != executable_sha256
        or RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
        + field_count * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size
        > len(native_raw)
    ):
        raise AcquisitionError("runtime type reference fields are invalid")
    for row in RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.iter_unpack(
        memoryview(native_raw)[
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size :
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + field_count * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size
        ]
    ):
        descriptor = row[3]
        if not descriptor:
            raise AcquisitionError("runtime type reference field type is absent")
        seeds.add(descriptor)

    if len(event_raw) < RUNTIME_EVENT_MODULE_HEADER.size:
        raise AcquisitionError("runtime type reference events are truncated")
    event_header = RUNTIME_EVENT_MODULE_HEADER.unpack_from(event_raw)
    module_count, event_count = event_header[5:7]
    event_start = (
        RUNTIME_EVENT_MODULE_HEADER.size
        + module_count * RUNTIME_EVENT_MODULE_MODULE.size
    )
    if (
        event_header[0] != RUNTIME_EVENT_MODULE_MAGIC
        or event_header[1] != RUNTIME_EVENT_MODULE_VERSION
        or event_header[2] != RUNTIME_EVENT_MODULE_HEADER.size
        or event_header[4] != RUNTIME_EVENT_MODULE_EVENT.size
        or _digest(event_header[12], label="event executable")
        != executable_sha256
        or event_start + event_count * RUNTIME_EVENT_MODULE_EVENT.size
        > len(event_raw)
    ):
        raise AcquisitionError("runtime type reference events are invalid")
    for row in RUNTIME_EVENT_MODULE_EVENT.iter_unpack(
        memoryview(event_raw)[
            event_start : event_start + event_count * RUNTIME_EVENT_MODULE_EVENT.size
        ]
    ):
        descriptor = row[3]
        if not descriptor:
            raise AcquisitionError("runtime type reference event type is absent")
        seeds.add(descriptor)

    if len(graph_raw) < RUNTIME_TYPE_GRAPH_HEADER.size:
        raise AcquisitionError("runtime type reference graph is truncated")
    graph_header = RUNTIME_TYPE_GRAPH_HEADER.unpack_from(graph_raw)
    graph_types, interface_count, argument_count = graph_header[5:8]
    graph_record_start = RUNTIME_TYPE_GRAPH_HEADER.size
    interface_start = (
        graph_record_start + graph_types * RUNTIME_TYPE_GRAPH_RECORD.size
    )
    argument_start = interface_start + interface_count * 8
    if (
        graph_header[0] != RUNTIME_TYPE_GRAPH_MAGIC
        or graph_header[1] != RUNTIME_TYPE_GRAPH_VERSION
        or graph_header[2] != RUNTIME_TYPE_GRAPH_HEADER.size
        or graph_header[3] != RUNTIME_TYPE_GRAPH_RECORD.size
        or graph_types != type_count
        or _digest(graph_header[10], label="graph executable")
        != executable_sha256
        or argument_start + argument_count * 8 != len(graph_raw)
    ):
        raise AcquisitionError("runtime type reference graph is invalid")
    for row in RUNTIME_TYPE_GRAPH_RECORD.iter_unpack(
        memoryview(graph_raw)[
            graph_record_start :
            graph_record_start + graph_types * RUNTIME_TYPE_GRAPH_RECORD.size
        ]
    ):
        seeds.update(value for value in row[2:6] if value)
    for (value,) in _QWORD.iter_unpack(
        memoryview(graph_raw)[
            interface_start : interface_start + interface_count * 8
        ]
    ):
        seeds.add(value)
    for (value,) in _QWORD.iter_unpack(
        memoryview(graph_raw)[
            argument_start : argument_start + argument_count * 8
        ]
    ):
        seeds.add(value)

    if method_generic_path is None:
        if (
            not seeds
            or len(seeds) > 500_000
            or any(not value or value & 7 for value in seeds)
        ):
            raise AcquisitionError(
                "runtime type reference core seed domain is invalid"
            )
        return (
            list(seeds),
            tuple(
                file_identity(path)["sha256"]
                for path in (
                    identity_path,
                    method_path,
                    native_path,
                    event_path,
                    graph_path,
                )
            ),
            set(),
            set(),
        )


    from alpha.p26 import RUNTIME_METHOD_GENERIC_HEADER, RUNTIME_METHOD_GENERIC_MAGIC, RUNTIME_METHOD_GENERIC_RECORD, RUNTIME_METHOD_GENERIC_VERSION
    if len(method_generic_raw) < RUNTIME_METHOD_GENERIC_HEADER.size:
        raise AcquisitionError(
            "runtime type reference method generics are truncated"
        )
    method_generic_header = RUNTIME_METHOD_GENERIC_HEADER.unpack_from(
        method_generic_raw
    )
    generic_method_count = method_generic_header[5]
    generic_argument_count = method_generic_header[7]
    generic_argument_start = (
        RUNTIME_METHOD_GENERIC_HEADER.size
        + generic_method_count * RUNTIME_METHOD_GENERIC_RECORD.size
    )
    if (
        method_generic_header[0] != RUNTIME_METHOD_GENERIC_MAGIC
        or method_generic_header[1] != RUNTIME_METHOD_GENERIC_VERSION
        or method_generic_header[2] != RUNTIME_METHOD_GENERIC_HEADER.size
        or method_generic_header[3] != RUNTIME_METHOD_GENERIC_RECORD.size
        or method_generic_header[4] != 0
        or _digest(
            method_generic_header[11], label="method generic executable"
        )
        != executable_sha256
        or _digest(
            method_generic_header[13], label="method generic methods"
        )
        != file_identity(method_path)["sha256"]
        or generic_argument_start + generic_argument_count * 8
        != len(method_generic_raw)
    ):
        raise AcquisitionError(
            "runtime type reference method generics are invalid"
        )
    method_generic_descriptors: set[int] = set()
    for (descriptor,) in _QWORD.iter_unpack(
        memoryview(method_generic_raw)[
            generic_argument_start : generic_argument_start + generic_argument_count * 8
        ]
    ):
        if not descriptor:
            raise AcquisitionError(
                "runtime type reference method generic argument is absent"
            )
        seeds.add(descriptor)
        method_generic_descriptors.add(descriptor)

    if generic_parameter_detail_path is None:
        if (
            not seeds
            or len(seeds) > 500_000
            or any(not value or value & 7 for value in seeds)
        ):
            raise AcquisitionError(
                "runtime type reference method generic seed domain is invalid"
            )
        return (
            list(seeds),
            tuple(
                file_identity(path)["sha256"]
                for path in (
                    identity_path,
                    method_path,
                    native_path,
                    event_path,
                    graph_path,
                    method_generic_path,
                )
            ),
            method_generic_descriptors,
            set(),
        )

    from alpha.p28 import RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER, RUNTIME_GENERIC_PARAMETER_DETAIL_MAGIC, RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD, RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION
    if (
        len(generic_parameter_detail_raw)
        < RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
    ):
        raise AcquisitionError(
            "runtime type reference generic parameter detail is truncated"
        )
    detail_header = RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.unpack_from(
        generic_parameter_detail_raw
    )
    detail_argument_count, detail_constraint_count = detail_header[5:7]
    detail_constraint_start = (
        RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
        + detail_argument_count
        * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
    )
    detail_plan_path = (
        generic_parameter_detail_path.parent
        / "runtime-generic-parameter-detail-plan.private.json"
    )
    detail_plan = (
        read_json(detail_plan_path) if detail_plan_path.is_file() else {}
    )
    detail_generic_input = detail_plan.get(
        "generic_argument_input",
        {"sha256": file_identity(method_generic_path)["sha256"]},
    )
    if (
        detail_header[0] != RUNTIME_GENERIC_PARAMETER_DETAIL_MAGIC
        or detail_header[1] != RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION
        or detail_header[2] != RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
        or detail_header[3] != RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
        or detail_header[4] != 0
        or detail_argument_count < generic_argument_count
        or detail_argument_count
        != detail_plan.get("contract", {}).get(
            "argument_count", detail_argument_count
        )
        or _digest(
            detail_header[9], label="generic parameter detail executable"
        )
        != executable_sha256
        or _digest(
            detail_header[11], label="generic parameter detail generics"
        )
        != detail_generic_input.get("sha256")
        or detail_constraint_start + detail_constraint_count * 8
        != len(generic_parameter_detail_raw)
    ):
        raise AcquisitionError(
            "runtime type reference generic parameter detail is invalid"
        )
    detail_constraint_order = (
        struct.unpack_from(
            f"<{detail_constraint_count}Q",
            generic_parameter_detail_raw,
            detail_constraint_start,
        )
        if detail_constraint_count
        else ()
    )
    detail_constraint_descriptors = set(detail_constraint_order)
    if any(
        not descriptor or descriptor & 7
        for descriptor in detail_constraint_descriptors
    ):
        raise AcquisitionError(
            "runtime type reference constraint seed is invalid"
        )
    seeds.update(detail_constraint_order)
    if (
        not seeds
        or len(seeds) > 500_000
        or any(not value or value & 7 for value in seeds)
    ):
        raise AcquisitionError("runtime type reference seed domain is invalid")
    digests = tuple(
        file_identity(path)["sha256"]
        for path in (
            identity_path, method_path, native_path, event_path, graph_path,
            method_generic_path,
            generic_parameter_detail_path,
        )
    )
    return (
        list(seeds), digests, method_generic_descriptors,
        detail_constraint_descriptors,
    )


def _base_binding(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    ancestry_inventory: Path, method_detail_model: Path,
    method_detail_inventory: Path, native_member_detail_model: Path,
    native_member_detail_inventory: Path, event_module_model: Path,
    event_module_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path,
) -> dict[str, Any]:

    base = _graph_binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        ancestry_inventory=ancestry_inventory,
    )
    executable_sha256 = base["binary"]["sha256"]
    method_model, method_inventory = _validated_model(
        model_path=method_detail_model,
        inventory_path=method_detail_inventory,
        schema=RUNTIME_METHOD_DETAIL_SCHEMA,
        executable_sha256=executable_sha256,
        label="method detail",
    )
    native_model, native_inventory = _validated_model(
        model_path=native_member_detail_model,
        inventory_path=native_member_detail_inventory,
        schema=RUNTIME_NATIVE_MEMBER_DETAIL_SCHEMA,
        executable_sha256=executable_sha256,
        label="native member detail",
    )
    event_model, event_inventory = _validated_model(
        model_path=event_module_model,
        inventory_path=event_module_inventory,
        schema=RUNTIME_EVENT_MODULE_SCHEMA,
        executable_sha256=executable_sha256,
        label="event module",
    )
    graph_model, graph_inventory = _validated_model(
        model_path=type_graph_model,
        inventory_path=type_graph_inventory,
        schema=RUNTIME_TYPE_GRAPH_SCHEMA,
        executable_sha256=executable_sha256,
        label="type graph",
    )
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantics"
    )
    semantics = read_json(semantics_path)
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
    } if isinstance(semantics, dict) else {}
    if (
        semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or set(_REQUIRED_OPERATIONS) - set(operations)
        or any(
            operations[key].get("semantic_identity_resolved") is not True
            or not isinstance(operations[key].get("method_pointer"), int)
            or operations[key]["method_pointer"] <= 0
            or not isinstance(operations[key].get("metadata_pointer"), int)
            or operations[key]["metadata_pointer"] <= 0
            for key in _REQUIRED_OPERATIONS
        )
    ):
        raise AcquisitionError(
            "runtime base type reference semantics are stale"
        )
    type_plan = read_json(Path(base["type_identity_plan"]["path"]))
    graph_status_path = _owner_file(
        Path(graph_model["path"]).parent
        / "runtime-type-graph-status.private.json",
        label="type graph status",
    )
    graph_status = read_json(graph_status_path)
    runtime_classes = type_plan.get("runtime_classes_owner_only", {})
    length_qword = graph_status.get("array_length_qword_owner_only")
    vector_qword = graph_status.get("array_vector_qword_owner_only")
    if (
        not isinstance(runtime_classes.get("runtime_type"), int)
        or runtime_classes["runtime_type"] <= 0
        or not isinstance(runtime_classes.get("string"), int)
        or runtime_classes["string"] <= 0
        or not isinstance(length_qword, int)
        or not isinstance(vector_qword, int)
        or not 1 <= length_qword < vector_qword < 10
        or graph_status.get("status") != "complete"
    ):
        raise AcquisitionError(
            "runtime base type reference layouts are unavailable"
        )
    seeds, source_digests, _, _ = _seed_inventory(
        executable_sha256=executable_sha256,
        identity_path=Path(base["type_identity_inventory"]["path"]),
        method_path=Path(method_inventory["path"]),
        native_path=Path(native_inventory["path"]),
        event_path=Path(event_inventory["path"]),
        graph_path=Path(graph_inventory["path"]),
    )
    if source_digests != (
        base["type_identity_inventory"]["sha256"],
        method_inventory["sha256"],
        native_inventory["sha256"],
        event_inventory["sha256"],
        graph_inventory["sha256"],
    ):
        raise AcquisitionError(
            "runtime base type reference seed binding is stale"
        )
    empty_input = {
        "path": None,
        "sha256": _EMPTY_INPUT_SHA256,
        "bytes": 0,
        "role": "not-applicable-in-base-bootstrap",
    }
    return {
        **base,
        "method_detail_model": method_model,
        "method_detail_inventory": method_inventory,
        "native_member_detail_model": native_model,
        "native_member_detail_inventory": native_inventory,
        "event_module_model": event_model,
        "event_module_inventory": event_inventory,
        "type_graph_model": graph_model,
        "type_graph_inventory": graph_inventory,
        "type_graph_status": file_identity(graph_status_path),
        "method_generic_inventory": dict(empty_input),
        "generic_parameter_detail_inventory": dict(empty_input),
        "string_class": runtime_classes["string"],
        "array_length_qword": length_qword,
        "array_vector_qword": vector_qword,
        "seed_descriptors": seeds,
        "operations": {
            key: {
                "pointer": operations[key]["method_pointer"],
                "metadata": operations[key]["metadata_pointer"],
            }
            for key in _REQUIRED_OPERATIONS
        },
    }


def _binding(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    ancestry_inventory: Path, method_detail_model: Path,
    method_detail_inventory: Path, native_member_detail_model: Path,
    native_member_detail_inventory: Path, event_module_model: Path,
    event_module_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path, method_generic_model: Path,
    method_generic_inventory: Path, base_type_reference_model: Path,
    base_type_reference_inventory: Path,
    generic_parameter_detail_model: Path | None,
    generic_parameter_detail_inventory: Path | None,
) -> dict[str, Any]:
    base = _graph_binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        ancestry_inventory=ancestry_inventory,
    )
    executable_sha256 = base["binary"]["sha256"]
    method_model, method_inventory = _validated_model(
        model_path=method_detail_model,
        inventory_path=method_detail_inventory,
        schema=RUNTIME_METHOD_DETAIL_SCHEMA,
        executable_sha256=executable_sha256,
        label="method detail",
    )
    native_model, native_inventory = _validated_model(
        model_path=native_member_detail_model,
        inventory_path=native_member_detail_inventory,
        schema=RUNTIME_NATIVE_MEMBER_DETAIL_SCHEMA,
        executable_sha256=executable_sha256,
        label="native member detail",
    )
    event_model, event_inventory = _validated_model(
        model_path=event_module_model,
        inventory_path=event_module_inventory,
        schema=RUNTIME_EVENT_MODULE_SCHEMA,
        executable_sha256=executable_sha256,
        label="event module",
    )
    graph_model, graph_inventory = _validated_model(
        model_path=type_graph_model,
        inventory_path=type_graph_inventory,
        schema=RUNTIME_TYPE_GRAPH_SCHEMA,
        executable_sha256=executable_sha256,
        label="type graph",
    )
    from alpha.p26 import RUNTIME_METHOD_GENERIC_SCHEMA
    method_generic_model_identity, method_generic_inventory_identity = (
        _validated_model(
            model_path=method_generic_model,
            inventory_path=method_generic_inventory,
            schema=RUNTIME_METHOD_GENERIC_SCHEMA,
            executable_sha256=executable_sha256,
            label="method generic",
        )
    )
    base_reference_model_identity, base_reference_inventory_identity = (
        _validated_model(
            model_path=base_type_reference_model,
            inventory_path=base_type_reference_inventory,
            schema=RUNTIME_TYPE_REFERENCE_SCHEMA,
            executable_sha256=executable_sha256,
            label="base type reference",
        )
    )
    if (generic_parameter_detail_model is None) != (
        generic_parameter_detail_inventory is None
    ):
        raise AcquisitionError(
            "runtime type reference generic parameter inputs are incomplete"
        )
    if generic_parameter_detail_model is None:
        empty_detail = {
            "path": None,
            "sha256": _EMPTY_INPUT_SHA256,
            "bytes": 0,
            "role": "pending-method-generic-extension",
        }
        detail_model_identity = dict(empty_detail)
        detail_inventory_identity = dict(empty_detail)
    else:
        from alpha.p28 import RUNTIME_GENERIC_PARAMETER_DETAIL_SCHEMA
        detail_model_identity, detail_inventory_identity = _validated_model(
            model_path=generic_parameter_detail_model,
            inventory_path=generic_parameter_detail_inventory,
            schema=RUNTIME_GENERIC_PARAMETER_DETAIL_SCHEMA,
            executable_sha256=executable_sha256,
            label="generic parameter detail",
        )
        detail_model = read_json(Path(detail_model_identity["path"]))
        if (
            detail_model.get("inputs", {})
            .get("type_reference_inventory", {})
            .get("sha256")
            != base_reference_inventory_identity["sha256"]
            or detail_model.get("inputs", {})
            .get("method_generic_inventory", {})
            .get("sha256")
            != method_generic_inventory_identity["sha256"]
        ):
            raise AcquisitionError(
                "runtime type reference generic parameter discovery is stale"
            )
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantics"
    )
    semantics = read_json(semantics_path)
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
    } if isinstance(semantics, dict) else {}
    if (
        semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or set(_REQUIRED_OPERATIONS) - set(operations)
        or any(
            operations[key].get("semantic_identity_resolved") is not True
            or not isinstance(operations[key].get("method_pointer"), int)
            or operations[key]["method_pointer"] <= 0
            or not isinstance(operations[key].get("metadata_pointer"), int)
            or operations[key]["metadata_pointer"] <= 0
            for key in _REQUIRED_OPERATIONS
        )
    ):
        raise AcquisitionError("runtime type reference semantics are stale")
    type_plan = read_json(Path(base["type_identity_plan"]["path"]))
    type_status = read_json(Path(base["type_identity_status"]["path"]))
    graph_status_path = _owner_file(
        Path(graph_model["path"]).parent / "runtime-type-graph-status.private.json",
        label="type graph status",
    )
    graph_status = read_json(graph_status_path)
    runtime_classes = type_plan.get("runtime_classes_owner_only", {})
    length_qword = graph_status.get("array_length_qword_owner_only")
    vector_qword = graph_status.get("array_vector_qword_owner_only")
    if (
        not isinstance(runtime_classes.get("runtime_type"), int)
        or runtime_classes["runtime_type"] <= 0
        or not isinstance(runtime_classes.get("string"), int)
        or runtime_classes["string"] <= 0
        or not isinstance(length_qword, int)
        or not isinstance(vector_qword, int)
        or not 1 <= length_qword < vector_qword < 10
        or graph_status.get("status") != "complete"
    ):
        raise AcquisitionError("runtime type reference layouts are unavailable")
    (
        seeds,
        source_digests,
        method_generic_descriptors,
        detail_constraint_descriptors,
    ) = _seed_inventory(
        executable_sha256=executable_sha256,
        identity_path=Path(base["type_identity_inventory"]["path"]),
        method_path=Path(method_inventory["path"]),
        native_path=Path(native_inventory["path"]),
        event_path=Path(event_inventory["path"]),
        graph_path=Path(graph_inventory["path"]),
        method_generic_path=Path(method_generic_inventory_identity["path"]),
        generic_parameter_detail_path=(
            Path(detail_inventory_identity["path"])
            if detail_inventory_identity["path"] is not None
            else None
        ),
    )
    expected_source_digests = (
        base["type_identity_inventory"]["sha256"],
        method_inventory["sha256"], native_inventory["sha256"],
        event_inventory["sha256"], graph_inventory["sha256"],
        method_generic_inventory_identity["sha256"],
    ) + (
        (detail_inventory_identity["sha256"],)
        if detail_inventory_identity["path"] is not None
        else ()
    )
    if source_digests != expected_source_digests:
        raise AcquisitionError("runtime type reference seed binding is stale")
    base_reference_model = read_json(
        Path(base_reference_model_identity["path"])
    )
    expected_base_inputs = {
        "type_identity_inventory": base["type_identity_inventory"]["sha256"],
        "method_detail_inventory": method_inventory["sha256"],
        "native_member_detail_inventory": native_inventory["sha256"],
        "event_module_inventory": event_inventory["sha256"],
        "type_graph_inventory": graph_inventory["sha256"],
    }
    if any(
        base_reference_model.get("inputs", {}).get(key, {}).get("sha256")
        != digest
        for key, digest in expected_base_inputs.items()
    ):
        raise AcquisitionError(
            "runtime type reference base inventory inputs are stale"
        )
    base_raw = Path(base_reference_inventory_identity["path"]).read_bytes()
    if len(base_raw) < RUNTIME_TYPE_REFERENCE_HEADER.size:
        raise AcquisitionError(
            "runtime type reference base inventory is truncated"
        )
    base_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(base_raw)
    base_node_count, base_interface_count, base_argument_count = (
        base_header[5], base_header[7], base_header[8]
    )
    base_string_bytes = base_header[9]
    base_record_start = RUNTIME_TYPE_REFERENCE_HEADER.size
    base_interface_start = (
        base_record_start
        + base_node_count * RUNTIME_TYPE_REFERENCE_RECORD.size
    )
    base_argument_start = base_interface_start + base_interface_count * 8
    base_string_start = base_argument_start + base_argument_count * 8
    if (
        base_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or base_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or base_header[2] != RUNTIME_TYPE_REFERENCE_HEADER.size
        or base_header[3] != RUNTIME_TYPE_REFERENCE_RECORD.size
        or base_header[4] != 0
        or base_header[10] != base["image_base"]
        or base_header[11] != base["image_bytes"]
        or _digest(base_header[12], label="base executable")
        != executable_sha256
        or _digest(base_header[14], label="base identity")
        != base["type_identity_inventory"]["sha256"]
        or _digest(base_header[15], label="base graph")
        != graph_inventory["sha256"]
        or _digest(base_header[16], label="base semantics")
        != base["semantics"]["sha256"]
        or base_string_start + base_string_bytes != len(base_raw)
    ):
        raise AcquisitionError(
            "runtime type reference base inventory is invalid"
        )
    base_descriptors = {
        RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
            base_raw,
            base_record_start + index * RUNTIME_TYPE_REFERENCE_RECORD.size,
        )[0]
        for index in range(base_node_count)
    }
    if len(base_descriptors) != base_node_count:
        raise AcquisitionError(
            "runtime type reference base descriptors repeat"
        )
    extension_seeds = [descriptor for descriptor in seeds if descriptor not in base_descriptors]
    discovery_descriptors = (
        method_generic_descriptors | detail_constraint_descriptors
    )
    if (
        not extension_seeds
        or not set(extension_seeds) <= discovery_descriptors
        or not discovery_descriptors
        <= base_descriptors | set(extension_seeds)
    ):
        raise AcquisitionError(
            "runtime type reference method generic extension is invalid"
        )
    return {
        **base,
        "method_detail_model": method_model,
        "method_detail_inventory": method_inventory,
        "native_member_detail_model": native_model,
        "native_member_detail_inventory": native_inventory,
        "event_module_model": event_model,
        "event_module_inventory": event_inventory,
        "type_graph_model": graph_model,
        "type_graph_inventory": graph_inventory,
        "type_graph_status": file_identity(graph_status_path),
        "method_generic_model": method_generic_model_identity,
        "method_generic_inventory": method_generic_inventory_identity,
        "base_type_reference_model": base_reference_model_identity,
        "base_type_reference_inventory": base_reference_inventory_identity,
        "generic_parameter_detail_model": detail_model_identity,
        "generic_parameter_detail_inventory": detail_inventory_identity,
        "base_type_reference_seed_count": base_header[6],
        "base_type_reference_node_count": base_node_count,
        "string_class": runtime_classes["string"],
        "array_length_qword": length_qword,
        "array_vector_qword": vector_qword,
        "seed_descriptors": extension_seeds,
        "operations": {
            key: {
                "pointer": operations[key]["method_pointer"],
                "metadata": operations[key]["metadata_pointer"],
            }
            for key in _REQUIRED_OPERATIONS
        },
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// 512 nodes per window message: the reference capture walks hundreds of
// thousands of nodes (2026-10-01 round 0: 111k seeds grew to 326k nodes),
// so the wine message round trip dominated at 64/message (~5100 messages
// per capture).  Per-node observation, records, and validation are
// unchanged -- only the transport amortizes; a node that faults fails the
// capture loudly at either batch size, and the 60s per-message budget
// covers a 512-node batch with 60-100x margin (the dispatcher retries the
// same window from capture_index, whose records are idempotent).
#define ALPHA_BATCH_NODES 512u
#define ALPHA_MAX_NODES 500000u
#define ALPHA_HASH_SLOTS 1048576u
#define ALPHA_MAX_RELATIONS 8000000u
#define ALPHA_MAX_TEXT 16384u

typedef struct seed_header {
    char magic[8]; uint32_t version, reserved; uint64_t seed_count;
    char executable_sha256[64], identity_sha256[64], method_sha256[64];
    char native_sha256[64], event_sha256[64], graph_sha256[64];
    char method_generic_sha256[64];
    char generic_parameter_detail_sha256[64];
} seed_header;
typedef struct output_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t node_count, seed_count, interface_count, generic_argument_count;
    uint64_t string_bytes, image_base, image_bytes;
    char executable_sha256[64], seed_sha256[64], identity_sha256[64];
    char graph_sha256[64], semantics_sha256[64];
} output_header;
typedef struct output_record {
    uint64_t descriptor, canonical_descriptor, type_object;
    uint32_t attributes, shape, name_bytes, namespace_bytes;
    uint32_t interface_count, generic_argument_count, element_rank, reserved;
    uint64_t base_descriptor, declaring_descriptor, element_descriptor;
    uint64_t generic_definition_descriptor, interface_start;
    uint64_t generic_argument_start, name_offset, namespace_offset;
} output_record;

_Static_assert(sizeof(seed_header) == $seed_header_bytes, "seed header");
_Static_assert(sizeof(output_header) == $output_header_bytes, "output header");
_Static_assert(sizeof(output_record) == $output_record_bytes, "output record");

static const char executable_sha256[]="$executable_sha256";
static const char seed_sha256[]="$seed_sha256";
static const char identity_sha256[]="$identity_sha256";
static const char graph_sha256[]="$graph_sha256";
static const char semantics_sha256[]="$semantics_sha256";
static const char method_generic_sha256[]="$method_generic_sha256";
static const char generic_parameter_detail_sha256[]="$generic_parameter_detail_sha256";
static const DWORD expected_pid=${process_id}u;
static const uintptr_t expected_image_base=${image_base}ull;
static const uint64_t expected_image_bytes=${image_bytes}ull;
static const uint64_t expected_seed_count=${seed_count}ull;
static const uintptr_t runtime_type_class=${runtime_type_class}ull;
static const uintptr_t string_class=${string_class}ull;
static const uint32_t handle_qword=${handle_qword}u;
static const uint32_t array_length_qword=${array_length_qword}u;
static const uint32_t array_vector_qword=${array_vector_qword}u;
static const wchar_t seed_path[]=$seed_path;
static const wchar_t output_path[]=$output_path;
static const wchar_t status_path[]=$status_path;

static const uintptr_t from_handle_pointer=${from_handle_pointer}ull,from_handle_metadata=${from_handle_metadata}ull;
static const uintptr_t name_pointer=${name_pointer}ull,name_metadata=${name_metadata}ull;
static const uintptr_t namespace_pointer=${namespace_pointer}ull,namespace_metadata=${namespace_metadata}ull;
static const uintptr_t base_pointer=${base_pointer}ull,base_metadata=${base_metadata}ull;
static const uintptr_t declaring_pointer=${declaring_pointer}ull,declaring_metadata=${declaring_metadata}ull;
static const uintptr_t element_pointer=${element_pointer}ull,element_metadata=${element_metadata}ull;
static const uintptr_t interfaces_pointer=${interfaces_pointer}ull,interfaces_metadata=${interfaces_metadata}ull;
static const uintptr_t enum_pointer=${enum_pointer}ull,enum_metadata=${enum_metadata}ull;
static const uintptr_t value_pointer=${value_pointer}ull,value_metadata=${value_metadata}ull;
static const uintptr_t byref_pointer=${byref_pointer}ull,byref_metadata=${byref_metadata}ull;
static const uintptr_t generic_pointer=${generic_pointer}ull,generic_metadata=${generic_metadata}ull;
static const uintptr_t generic_definition_shape_pointer=${generic_definition_shape_pointer}ull,generic_definition_shape_metadata=${generic_definition_shape_metadata}ull;
static const uintptr_t generic_definition_pointer=${generic_definition_pointer}ull,generic_definition_metadata=${generic_definition_metadata}ull;
static const uintptr_t generic_arguments_pointer=${generic_arguments_pointer}ull,generic_arguments_metadata=${generic_arguments_metadata}ull;
static const uintptr_t attributes_pointer=${attributes_pointer}ull,attributes_metadata=${attributes_metadata}ull;

typedef uintptr_t(*static_qword)(uintptr_t,uintptr_t);
typedef uintptr_t(*instance_noarg)(uintptr_t,uintptr_t);
typedef uint32_t(*instance_dword)(uintptr_t,uintptr_t);
typedef uint8_t(*instance_bool)(uintptr_t,uintptr_t);
static output_record *records;static uint64_t *queue,*hash_slots,*interfaces,*generic_arguments;
static uint64_t node_count,capture_index,completed_nodes,interface_count,interface_capacity,generic_argument_count,generic_argument_capacity;
static char *strings;static uint64_t string_bytes,string_capacity;
static uint64_t enum_count,value_count,generic_count,generic_definition_count,byref_count,array_count,pointer_count,generic_parameter_count;
static uint64_t failure_index;static uint32_t failure_kind;static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_complete;

static int readable(uintptr_t value,SIZE_T bytes){MEMORY_BASIC_INFORMATION region;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&region,sizeof(region))||region.State!=MEM_COMMIT||region.Protect&PAGE_GUARD)return 0;DWORD protect=region.Protect&0xffu;uintptr_t end=(uintptr_t)region.BaseAddress+region.RegionSize;return protect&&protect!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}
static int object_class(uintptr_t object,uintptr_t expected){uintptr_t value=0;if(!readable(object,8u))return 0;memcpy(&value,(const void*)object,8u);return value==expected;}
static int managed_utf8(uintptr_t object,int allow_empty,char**output,uint32_t*bytes){*output=NULL;*bytes=0;if(!object)return allow_empty;if(!object_class(object,string_class)||!readable(object+16u,4u))return 0;int32_t length=0;memcpy(&length,(const void*)(object+16u),4u);if(length<0||length>(int32_t)ALPHA_MAX_TEXT||(length&&!readable(object+20u,(SIZE_T)length*2u)))return 0;if(!length)return allow_empty;int required=WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,(const wchar_t*)(object+20u),length,NULL,0,NULL,NULL);if(required<=0||required>4*(int)ALPHA_MAX_TEXT)return 0;char*value=malloc((SIZE_T)required);if(!value||WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,(const wchar_t*)(object+20u),length,value,required,NULL,NULL)!=required){free(value);return 0;}*output=value;*bytes=(uint32_t)required;return 1;}
static int append_text(const char*value,uint32_t bytes,uint64_t*offset){if(!bytes){*offset=string_bytes;return 1;}if(!value||string_bytes+bytes<string_bytes)return 0;uint64_t required=string_bytes+bytes;if(required>string_capacity){uint64_t capacity=string_capacity?string_capacity:65536u;while(capacity<required)capacity*=2u;char*grown=realloc(strings,(SIZE_T)capacity);if(!grown)return 0;strings=grown;string_capacity=capacity;}*offset=string_bytes;memcpy(strings+string_bytes,value,bytes);string_bytes+=bytes;return 1;}
static int descriptor_from_type(uintptr_t object,uintptr_t*descriptor){*descriptor=0;if(!object)return 1;if(!object_class(object,runtime_type_class))return 0;memcpy(descriptor,(const void*)(object+(uintptr_t)handle_qword*8u),8u);return readable(*descriptor,16u);}
static uint64_t descriptor_hash(uint64_t value){value^=value>>30;value*=0xbf58476d1ce4e5b9ull;value^=value>>27;value*=0x94d049bb133111ebull;return value^(value>>31);}
static int enqueue(uint64_t descriptor){if(!descriptor||!readable((uintptr_t)descriptor,16u))return 0;uint64_t slot=descriptor_hash(descriptor)&(ALPHA_HASH_SLOTS-1u);for(uint64_t probe=0;probe<ALPHA_HASH_SLOTS;probe++){uint64_t*cell=&hash_slots[(slot+probe)&(ALPHA_HASH_SLOTS-1u)];if(*cell==descriptor)return 1;if(!*cell){if(node_count>=ALPHA_MAX_NODES)return 0;*cell=descriptor;queue[node_count++]=descriptor;return 1;}}return 0;}
static int append_relation(uint64_t**pool,uint64_t*count,uint64_t*capacity,uint64_t descriptor){if(!descriptor||*count>=ALPHA_MAX_RELATIONS||!enqueue(descriptor))return 0;if(*count==*capacity){uint64_t next=*capacity?*capacity*2u:65536u;if(next>ALPHA_MAX_RELATIONS)next=ALPHA_MAX_RELATIONS;uint64_t*grown=realloc(*pool,(SIZE_T)next*8u);if(!grown)return 0;*pool=grown;*capacity=next;}(*pool)[(*count)++]=descriptor;return 1;}
static int type_array(uintptr_t array,uintptr_t**items,uint32_t*count){*items=NULL;*count=0;if(!array||!readable(array,((SIZE_T)array_vector_qword+1u)*8u))return 0;uintptr_t length=0;memcpy(&length,(const void*)(array+(uintptr_t)array_length_qword*8u),8u);if(length>65536u)return 0;uintptr_t vector=array+(uintptr_t)array_vector_qword*8u;if(length&&!readable(vector,(SIZE_T)length*8u))return 0;for(uint64_t i=0;i<length;i++){uintptr_t item=0;memcpy(&item,(const void*)(vector+i*8u),8u);if(!object_class(item,runtime_type_class))return 0;}*items=(uintptr_t*)vector;*count=(uint32_t)length;return 1;}
static uint32_t array_rank_from_name(const char*name,uint32_t bytes){if(!name||bytes<2||name[bytes-1]!=']')return 0;uint32_t open=bytes-1;while(open&&name[open]!='[')open--;if(name[open]!='[')return 0;uint32_t rank=1;for(uint32_t i=open+1;i+1<bytes;i++){if(name[i]==',')rank++;else return 0;}return rank;}

static int capture_batch(void){static_qword from_handle=(static_qword)from_handle_pointer;instance_noarg get_name=(instance_noarg)name_pointer,get_namespace=(instance_noarg)namespace_pointer,get_base=(instance_noarg)base_pointer,get_declaring=(instance_noarg)declaring_pointer,get_element=(instance_noarg)element_pointer,get_interfaces=(instance_noarg)interfaces_pointer,get_definition=(instance_noarg)generic_definition_pointer,get_arguments=(instance_noarg)generic_arguments_pointer;instance_bool get_enum=(instance_bool)enum_pointer,get_value=(instance_bool)value_pointer,get_byref=(instance_bool)byref_pointer,get_generic=(instance_bool)generic_pointer,get_definition_shape=(instance_bool)generic_definition_shape_pointer;instance_dword get_attributes=(instance_dword)attributes_pointer;uint64_t end=capture_index+ALPHA_BATCH_NODES;if(end>node_count)end=node_count;for(;capture_index<end;capture_index++){output_record*target=&records[capture_index];target->descriptor=queue[capture_index];uint64_t source_bits=0;memcpy(&source_bits,(const void*)(target->descriptor+8u),8u);uint8_t source_byref=!!(source_bits&(1ull<<30));uintptr_t object=from_handle(target->descriptor,from_handle_metadata);if(!object_class(object,runtime_type_class)||!descriptor_from_type(object,&target->canonical_descriptor)||!enqueue(target->canonical_descriptor)){failure_index=capture_index+1u;failure_kind=1;return 0;}target->type_object=object;char*name=NULL,*space=NULL;uint32_t name_bytes=0,space_bytes=0;if(!managed_utf8(get_name(object,name_metadata),1,&name,&name_bytes)||!managed_utf8(get_namespace(object,namespace_metadata),1,&space,&space_bytes)){free(name);free(space);failure_index=capture_index+1u;failure_kind=2;return 0;}for(uint32_t i=0;i<name_bytes;i++)if((unsigned char)name[i]<0x20u)name[i]='_';for(uint32_t i=0;i<space_bytes;i++)if((unsigned char)space[i]<0x20u)space[i]='_';if(!name_bytes){char synthetic[48];int count=snprintf(synthetic,sizeof(synthetic),"EmptyTypeRef_%llX",(unsigned long long)target->descriptor);if(count<=0||count>=(int)sizeof(synthetic)){free(name);free(space);return 0;}name=malloc((SIZE_T)count);if(!name){free(space);return 0;}memcpy(name,synthetic,(SIZE_T)count);name_bytes=(uint32_t)count;}target->name_bytes=name_bytes;target->namespace_bytes=space_bytes;if(!append_text(name,name_bytes,&target->name_offset)||!append_text(space,space_bytes,&target->namespace_offset)){free(name);free(space);return 0;}free(name);free(space);
uintptr_t base=get_base(object,base_metadata),declaring=get_declaring(object,declaring_metadata),element=get_element(object,element_metadata);uintptr_t definition=0;uint8_t is_enum=get_enum(object,enum_metadata),is_value=get_value(object,value_metadata),is_byref=get_byref(object,byref_metadata),is_generic=get_generic(object,generic_metadata),is_definition=get_definition_shape(object,generic_definition_shape_metadata);if(is_enum>1||is_value>1||is_byref>1||is_generic>1||is_definition>1||(is_definition&&!is_generic)){failure_index=capture_index+1u;failure_kind=3;return 0;}if(is_generic)definition=get_definition(object,generic_definition_metadata);if(!descriptor_from_type(base,&target->base_descriptor)||!descriptor_from_type(declaring,&target->declaring_descriptor)||!descriptor_from_type(element,&target->element_descriptor)||!descriptor_from_type(definition,&target->generic_definition_descriptor)){failure_index=capture_index+1u;failure_kind=4;return 0;}uint64_t bits=0;memcpy(&bits,(const void*)(target->canonical_descriptor+8u),8u);uint32_t code=(uint32_t)((bits>>16)&0xffu);if(source_byref)target->element_descriptor=target->canonical_descriptor;uint32_t shape=(is_enum?1u:0u)|(is_value?2u:0u)|(is_generic?4u:0u)|(is_definition?8u:0u)|(source_byref?16u:0u);if(get_attributes(object,attributes_metadata)&0x20u)shape|=32u;if(!source_byref&&(code==0x13u||code==0x1eu))shape|=64u;if(!source_byref&&(code==0x14u||code==0x1du))shape|=128u;if(!source_byref&&code==0x0fu)shape|=256u;if(!source_byref&&is_byref){failure_index=capture_index+1u;failure_kind=5;return 0;}target->shape=shape;target->attributes=get_attributes(object,attributes_metadata);if(shape&128u){target->element_rank=array_rank_from_name(strings+target->name_offset,target->name_bytes);if(!target->element_rank){failure_index=capture_index+1u;failure_kind=6;return 0;}}if(!!target->element_descriptor!=!!(shape&(16u|128u|256u))){failure_index=capture_index+1u;failure_kind=7;return 0;}uintptr_t interface_array=get_interfaces(object,interfaces_metadata),argument_array=get_arguments(object,generic_arguments_metadata);uintptr_t*interface_items=NULL,*argument_items=NULL;uint32_t interfaces_here=0,arguments_here=0;if(!type_array(interface_array,&interface_items,&interfaces_here)||!type_array(argument_array,&argument_items,&arguments_here)||(!is_generic&&arguments_here)||is_generic&&!arguments_here||is_generic&&!target->generic_definition_descriptor){failure_index=capture_index+1u;failure_kind=8;return 0;}target->interface_start=interface_count;target->interface_count=interfaces_here;for(uint32_t i=0;i<interfaces_here;i++){uintptr_t descriptor=0;if(!descriptor_from_type(interface_items[i],&descriptor)||!append_relation(&interfaces,&interface_count,&interface_capacity,descriptor)){failure_index=capture_index+1u;failure_kind=9;return 0;}}target->generic_argument_start=generic_argument_count;target->generic_argument_count=arguments_here;for(uint32_t i=0;i<arguments_here;i++){uintptr_t descriptor=0;if(!descriptor_from_type(argument_items[i],&descriptor)||!append_relation(&generic_arguments,&generic_argument_count,&generic_argument_capacity,descriptor)){failure_index=capture_index+1u;failure_kind=10;return 0;}}uint64_t singles[4]={target->base_descriptor,target->declaring_descriptor,target->element_descriptor,target->generic_definition_descriptor};for(uint32_t i=0;i<4;i++)if(singles[i]&&!enqueue(singles[i])){failure_index=capture_index+1u;failure_kind=11;return 0;}enum_count+=!!is_enum;value_count+=!!is_value;byref_count+=!!source_byref;generic_count+=!!is_generic;generic_definition_count+=!!is_definition;generic_parameter_count+=!!(shape&64u);array_count+=!!(shape&128u);pointer_count+=!!(shape&256u);completed_nodes++;}return 1;}
static volatile LONG current_request, request_sequence, callback_active;
static LRESULT CALLBACK window_proc(HWND window,UINT message,WPARAM wparam,LPARAM lparam){
    if(message!=message_id)return CallWindowProcW(original_proc,window,message,wparam,lparam);
    LONG request=InterlockedCompareExchange(&current_request,0,0);
    if(!request||(LONG)wparam!=request||InterlockedCompareExchange(&callback_active,1,0))return 0;
    if(InterlockedCompareExchange(&current_request,0,0)!=request){InterlockedExchange(&callback_active,0);return 0;}
    int ok=capture_batch();
    InterlockedExchange(&callback_complete,ok?1:-1);
    InterlockedExchange(&callback_active,0);
    return ok;
}
typedef struct selection{DWORD pid;HWND window;uint32_t count;}selection;static BOOL CALLBACK select_window(HWND window,LPARAM value){selection*s=(selection*)(uintptr_t)value;DWORD pid=0;RECT bounds;if(!IsWindowVisible(window)||GetWindow(window,GW_OWNER)||!GetWindowRect(window,&bounds)||bounds.right<=bounds.left||bounds.bottom<=bounds.top)return TRUE;GetWindowThreadProcessId(window,&pid);if(pid==s->pid){s->window=window;s->count++;}return TRUE;}
static int dispatch_capture(void){
    selection s={0};s.pid=GetCurrentProcessId();
    if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window){failure_kind=100;failure_index=s.count;return 0;}
    message_id=RegisterWindowMessageW(L"ALPHA v2 current runtime type reference inventory");
    if(!message_id){failure_kind=102;failure_index=GetLastError();return 0;}
    SetLastError(0);
    original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);
    DWORD error=GetLastError();
    if(!original_proc||error!=ERROR_SUCCESS){failure_kind=103;failure_index=error;return 0;}
    int ok=1;uint32_t retries=0;
    while(ok&&capture_index<node_count){
        DWORD_PTR result=0;uint64_t before=capture_index;
        LONG request=InterlockedIncrement(&request_sequence);
        InterlockedExchange(&callback_complete,0);
        InterlockedExchange(&current_request,request);
        SetLastError(0);
        int sent=SendMessageTimeoutW(s.window,message_id,(WPARAM)request,0,SMTO_BLOCK,60000,&result)!=0;
        error=GetLastError();


        InterlockedExchange(&current_request,0);
        for(uint32_t wait=0;InterlockedCompareExchange(&callback_active,0,0)&&wait<2000u;wait++)Sleep(1);
        if(InterlockedCompareExchange(&callback_active,0,0)){failure_kind=104;ok=0;break;}
        LONG complete=InterlockedCompareExchange(&callback_complete,0,0);
        if(complete==1){
            if(capture_index<=before){failure_kind=108;ok=0;break;}
            retries=0;continue;
        }
        if(complete<0||failure_kind){if(!failure_kind)failure_kind=105;ok=0;break;}
        if(!sent&&retries++<16u){Sleep(250);continue;}
        failure_kind=101;failure_index=error;ok=0;
    }
    InterlockedExchange(&current_request,0);
    SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);


    return ok;
}
static void digest_hex(const unsigned char digest[32],char output[65]){static const char alphabet[]="0123456789abcdef";for(int i=0;i<32;i++){output[i*2]=alphabet[digest[i]>>4];output[i*2+1]=alphabet[digest[i]&15];}output[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE input=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(input==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char*object=NULL,*buffer=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;while(ok){DWORD count=0;if(!ReadFile(input,buffer,1048576u,&count,NULL)){ok=0;break;}if(!count)break;if(BCryptHashData(hash,buffer,count,0)<0)ok=0;}if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)<0)ok=0;if(ok)digest_hex(digest,output);if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(input);return ok;}
static int executable_identity(char output[65]){wchar_t path[32768];DWORD length=GetModuleFileNameW(NULL,path,32768);return length&&length<32768&&sha256_file(path,output);}
static void write_status(const char*status,int written){FILE*out=_wfopen(status_path,L"wb");if(!out)return;fprintf(out,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"seed_count\": %llu,\n  \"node_count\": %llu,\n  \"completed_node_count\": %llu,\n  \"interface_reference_count\": %llu,\n  \"generic_argument_reference_count\": %llu,\n  \"enum_count\": %llu,\n  \"value_type_count\": %llu,\n  \"generic_type_count\": %llu,\n  \"generic_definition_count\": %llu,\n  \"generic_parameter_count\": %llu,\n  \"byref_count\": %llu,\n  \"array_count\": %llu,\n  \"pointer_count\": %llu,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"saved_type_reference_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)expected_seed_count,(unsigned long long)node_count,(unsigned long long)completed_nodes,(unsigned long long)interface_count,(unsigned long long)generic_argument_count,(unsigned long long)enum_count,(unsigned long long)value_count,(unsigned long long)generic_count,(unsigned long long)generic_definition_count,(unsigned long long)generic_parameter_count,(unsigned long long)byref_count,(unsigned long long)array_count,(unsigned long long)pointer_count,(unsigned long long)failure_index,failure_kind,written?"true":"false");fclose(out);}
static int write_output(void){uint64_t fixed=sizeof(output_header)+node_count*sizeof(output_record)+(interface_count+generic_argument_count)*8u;for(uint64_t i=0;i<node_count;i++){records[i].name_offset+=fixed;records[i].namespace_offset+=fixed;}output_header header;memset(&header,0,sizeof(header));memcpy(header.magic,"ALPHATR1",8);header.version=$output_version;header.header_bytes=sizeof(header);header.record_bytes=sizeof(output_record);header.node_count=node_count;header.seed_count=expected_seed_count;header.interface_count=interface_count;header.generic_argument_count=generic_argument_count;header.string_bytes=string_bytes;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;memcpy(header.executable_sha256,executable_sha256,64);memcpy(header.seed_sha256,seed_sha256,64);memcpy(header.identity_sha256,identity_sha256,64);memcpy(header.graph_sha256,graph_sha256,64);memcpy(header.semantics_sha256,semantics_sha256,64);FILE*out=_wfopen(output_path,L"wb");if(!out)return 0;int ok=fwrite(&header,1,sizeof(header),out)==sizeof(header)&&fwrite(records,sizeof(*records),node_count,out)==node_count&&fwrite(interfaces,8u,interface_count,out)==interface_count&&fwrite(generic_arguments,8u,generic_argument_count,out)==generic_argument_count&&fwrite(strings,1,string_bytes,out)==string_bytes;if(fclose(out))ok=0;if(!ok)_wremove(output_path);return ok;}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char executable[65],seed_digest[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(executable)||strcmp(executable,executable_sha256)||!sha256_file(seed_path,seed_digest)||strcmp(seed_digest,seed_sha256)){failure_kind=200;write_status("identity_mismatch",0);return 0;}FILE*input=_wfopen(seed_path,L"rb");seed_header header;if(!input||fread(&header,1,sizeof(header),input)!=sizeof(header)||memcmp(header.magic,"ALPHARS1",8)||header.version!=$seed_version||header.reserved||header.seed_count!=expected_seed_count||memcmp(header.executable_sha256,executable_sha256,64)||memcmp(header.identity_sha256,identity_sha256,64)||memcmp(header.graph_sha256,graph_sha256,64)||memcmp(header.method_generic_sha256,method_generic_sha256,64)||memcmp(header.generic_parameter_detail_sha256,generic_parameter_detail_sha256,64)){if(input)fclose(input);failure_kind=201;write_status("seed_invalid",0);return 0;}records=calloc(ALPHA_MAX_NODES,sizeof(*records));queue=calloc(ALPHA_MAX_NODES,sizeof(*queue));hash_slots=calloc(ALPHA_HASH_SLOTS,sizeof(*hash_slots));if(!records||!queue||!hash_slots){fclose(input);failure_kind=202;write_status("allocation_failed",0);return 0;}for(uint64_t i=0;i<expected_seed_count;i++){uint64_t descriptor=0;if(fread(&descriptor,1,8u,input)!=8u||!enqueue(descriptor)){fclose(input);failure_kind=203;failure_index=i+1u;write_status("seed_load_failed",0);return 0;}}int trailing=fgetc(input);fclose(input);if(trailing!=EOF||node_count!=expected_seed_count){failure_kind=204;write_status("seed_domain_failed",0);return 0;}if(!dispatch_capture()||completed_nodes!=node_count){if(!failure_kind)failure_kind=205;write_status("capture_failed",0);return 0;}int ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def runtime_type_reference_source(
    *, binding: dict[str, Any], seed_path: Path,
    seed_identity: dict[str, Any], output_path: Path, status_path: Path,
) -> str:
    operation = binding["operations"]
    values: dict[str, Any] = {
        "seed_header_bytes": RUNTIME_TYPE_REFERENCE_SEED_HEADER.size,
        "seed_version": RUNTIME_TYPE_REFERENCE_SEED_VERSION,
        "output_header_bytes": RUNTIME_TYPE_REFERENCE_HEADER.size,
        "output_record_bytes": RUNTIME_TYPE_REFERENCE_RECORD.size,
        "output_version": RUNTIME_TYPE_REFERENCE_VERSION,
        "status_schema": RUNTIME_TYPE_REFERENCE_STATUS_SCHEMA,
        "executable_sha256": binding["binary"]["sha256"],
        "seed_sha256": seed_identity["sha256"],
        "identity_sha256": binding["type_identity_inventory"]["sha256"],
        "graph_sha256": binding["type_graph_inventory"]["sha256"],
        "semantics_sha256": binding["semantics"]["sha256"],
        "method_generic_sha256": binding["method_generic_inventory"][
            "sha256"
        ],
        "generic_parameter_detail_sha256": binding[
            "generic_parameter_detail_inventory"
        ]["sha256"],
        "process_id": binding["process_id"],
        "image_base": binding["image_base"],
        "image_bytes": binding["image_bytes"],
        "seed_count": len(binding["seed_descriptors"]),
        "runtime_type_class": binding["runtime_type_class"],
        "string_class": binding["string_class"],
        "handle_qword": binding["handle_qword"],
        "array_length_qword": binding["array_length_qword"],
        "array_vector_qword": binding["array_vector_qword"],
        "seed_path": _wide_literal(_windows_z_path(seed_path)),
        "output_path": _wide_literal(_windows_z_path(output_path)),
        "status_path": _wide_literal(_windows_z_path(status_path)),
    }
    aliases = {
        "from_handle": "type.from_handle", "name": "type.name",
        "namespace": "type.namespace", "base": "type.base_type",
        "declaring": "type.declaring_type", "element": "type.element_type",
        "interfaces": "type.interfaces", "enum": "type.is_enum",
        "value": "type.is_value_type", "byref": "type.is_byref",
        "generic": "type.is_generic",
        "generic_definition_shape": "type.is_generic_definition",
        "generic_definition": "type.generic_definition",
        "generic_arguments": "type.generic_arguments",
        "attributes": "type.attributes",
    }
    for alias, key in aliases.items():
        values[f"{alias}_pointer"] = operation[key]["pointer"]
        values[f"{alias}_metadata"] = operation[key]["metadata"]
    from alpha.c01 import protect_reference_source
    from alpha.p15 import attach_reference_names
    from alpha.p14 import attach_reference_byref
    source = protect_reference_source(_COLLECTOR.substitute(values), creation_filetime=binding["creation_filetime"])
    source = attach_reference_byref(source, binding=binding)
    return attach_reference_names(source, binding=binding, seed_identity=seed_identity,
        raw_path=output_path.parent / "runtime-type-reference-raw-observation.private.bin",
        io_path=output_path.parent / "runtime-type-reference-string-io.private.json")


def prepare_runtime_base_type_reference_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    ancestry_inventory: Path, method_detail_model: Path,
    method_detail_inventory: Path, native_member_detail_model: Path,
    native_member_detail_inventory: Path, event_module_model: Path,
    event_module_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path, output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _base_binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        ancestry_inventory=ancestry_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        native_member_detail_model=native_member_detail_model,
        native_member_detail_inventory=native_member_detail_inventory,
        event_module_model=event_module_model,
        event_module_inventory=event_module_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
    )
    _bind_reference_instance(binding, binary)
    seed_path = output_dir / "runtime-type-reference-seeds.private.bin"
    output_path = output_dir / "runtime-type-reference.private.bin"
    status_path = output_dir / "runtime-type-reference-status.private.json"
    model_path = output_dir / "runtime-type-reference.private.json"
    plan_path = output_dir / "runtime-type-reference-plan.private.json"
    raw_observation_path = output_dir / "runtime-type-reference-raw-observation.private.bin"
    raw_names_path = output_dir / "runtime-type-reference-raw-names.private.bin"
    string_io_path = output_dir / "runtime-type-reference-string-io.private.json"
    build_dir = _owner_directory(output_dir / "build-type-reference")
    source_path = build_dir / "runtime-type-reference.c"
    injector_source = build_dir / "runtime-type-reference-injector.c"
    injector_path = build_dir / "alpha-runtime-type-reference-injector.exe"
    for existing in (output_path, status_path, model_path, plan_path, seed_path, source_path, injector_source, injector_path,
                     raw_observation_path, raw_names_path, string_io_path):
        if existing.exists() or existing.is_symlink():
            raise AcquisitionError("type-reference capture requires new private staging files")
    source_records = (
        binding["type_identity_inventory"],
        binding["method_detail_inventory"],
        binding["native_member_detail_inventory"],
        binding["event_module_inventory"],
        binding["type_graph_inventory"],
        binding["method_generic_inventory"],
        binding["generic_parameter_detail_inventory"],
    )
    seed_header = RUNTIME_TYPE_REFERENCE_SEED_HEADER.pack(
        RUNTIME_TYPE_REFERENCE_SEED_MAGIC,
        RUNTIME_TYPE_REFERENCE_SEED_VERSION,
        0,
        len(binding["seed_descriptors"]),
        binding["binary"]["sha256"].encode("ascii"),
        *(record["sha256"].encode("ascii") for record in source_records),
    )
    seed_body = struct.pack(
        f"<{len(binding['seed_descriptors'])}Q",
        *binding["seed_descriptors"],
    )
    _private_bytes(seed_path, seed_header + seed_body)
    seed_identity = file_identity(seed_path)
    _private_text(
        source_path,
        runtime_type_reference_source(
            binding=binding,
            seed_path=seed_path,
            seed_identity=seed_identity,
            output_path=output_path,
            status_path=status_path,
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-base-type-reference-"
        + file_identity(source_path)["sha256"][:12]
        + f"-{time.time_ns():x}"
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
            label="runtime base type reference collector",
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
            label="runtime base type reference injector",
            source_path=injector_source,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_TYPE_REFERENCE_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "creation_filetime": binding["creation_filetime"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {**binding["capture_identity_inputs"], **{
            key: binding[key]
            for key in (
                "semantics", "type_identity_model", "type_identity_inventory",
                "ancestry_inventory", "method_detail_model",
                "method_detail_inventory", "native_member_detail_model",
                "native_member_detail_inventory", "event_module_model",
                "event_module_inventory", "type_graph_model",
                "type_graph_inventory", "type_graph_status",
                "method_generic_inventory",
                "generic_parameter_detail_inventory",
            )
        }},
        "seed": seed_identity,
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "raw_observation_path": str(raw_observation_path),
        "raw_names_path": str(raw_names_path),
        "string_layout_io_path": str(string_io_path),
        "contract": {
            "seed_count": len(binding["seed_descriptors"]),
            "record_bytes": RUNTIME_TYPE_REFERENCE_RECORD.size,
            "recursive_reference_closure_required": True,
            "source_order_discovery_without_pointer_sort": True,
            "lossless_reference_names_required": True,
            "current_instance_and_lifetime_required": True,
            "base_reference_bootstrap": True,
            "descriptor_byref": binding["descriptor_byref_contract"],
            "method_generic_arguments_seeded": False,
        },
        "policy": {
            "same_process_required": True,
            "raw_pointers_owner_only": True,
            "saved_type_reference_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": True,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_TYPE_REFERENCE_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "seed_count": len(binding["seed_descriptors"]),
        "base_reference_bootstrap": True,
        "policy": plan["policy"],
    }


def prepare_runtime_type_reference_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    ancestry_inventory: Path, method_detail_model: Path,
    method_detail_inventory: Path, native_member_detail_model: Path,
    native_member_detail_inventory: Path, event_module_model: Path,
    event_module_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path, method_generic_model: Path,
    method_generic_inventory: Path, base_type_reference_model: Path,
    base_type_reference_inventory: Path, output_dir: Path,
    generic_parameter_detail_model: Path,
    generic_parameter_detail_inventory: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    binding = _binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        ancestry_inventory=ancestry_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        native_member_detail_model=native_member_detail_model,
        native_member_detail_inventory=native_member_detail_inventory,
        event_module_model=event_module_model,
        event_module_inventory=event_module_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        method_generic_model=method_generic_model,
        method_generic_inventory=method_generic_inventory,
        base_type_reference_model=base_type_reference_model,
        base_type_reference_inventory=base_type_reference_inventory,
        generic_parameter_detail_model=generic_parameter_detail_model,
        generic_parameter_detail_inventory=generic_parameter_detail_inventory,
    )
    return _prepare_reference_extension(
        binary=binary, binding=binding, output_dir=output_dir, compiler=compiler
    )


def _prepare_reference_extension(*, binary, binding, output_dir, compiler=None):

    output_dir = _owner_directory(output_dir)
    _bind_reference_instance(binding, binary)
    additional = binding.get("additional_evidence_inputs", {})
    if additional:
        from alpha.c04 import _verify_files
        _verify_files(additional)
        if any(key in binding["capture_identity_inputs"] and binding["capture_identity_inputs"][key] != value
               for key, value in additional.items()):
            raise AcquisitionError("type-reference additional evidence conflicts with source binding")
        binding["capture_identity_inputs"].update(additional)
    seed_path = output_dir / "runtime-type-reference-seeds.private.bin"
    extension_path = (
        output_dir / "runtime-type-reference-extension.private.bin"
    )
    output_path = output_dir / "runtime-type-reference.private.bin"
    status_path = output_dir / "runtime-type-reference-status.private.json"
    model_path = output_dir / "runtime-type-reference.private.json"
    plan_path = output_dir / "runtime-type-reference-plan.private.json"
    raw_observation_path = output_dir / "runtime-type-reference-raw-observation.private.bin"
    raw_names_path = output_dir / "runtime-type-reference-raw-names.private.bin"
    string_io_path = output_dir / "runtime-type-reference-string-io.private.json"
    build_dir = _owner_directory(output_dir / "build-type-reference")
    source_path = build_dir / "runtime-type-reference.c"
    injector_source = build_dir / "runtime-type-reference-injector.c"
    injector_path = build_dir / "alpha-runtime-type-reference-injector.exe"
    for existing in (extension_path, output_path, status_path, model_path, plan_path, seed_path, source_path, injector_source, injector_path,
                     raw_observation_path, raw_names_path, string_io_path):
        if existing.exists() or existing.is_symlink():
            raise AcquisitionError("type-reference capture requires new private staging files")
    source_records = (
        binding["type_identity_inventory"],
        binding["method_detail_inventory"],
        binding["native_member_detail_inventory"],
        binding["event_module_inventory"],
        binding["type_graph_inventory"],
        binding["method_generic_inventory"],
        binding["generic_parameter_detail_inventory"],
    )
    seed_header = RUNTIME_TYPE_REFERENCE_SEED_HEADER.pack(
        RUNTIME_TYPE_REFERENCE_SEED_MAGIC,
        RUNTIME_TYPE_REFERENCE_SEED_VERSION,
        0,
        len(binding["seed_descriptors"]),
        binding["binary"]["sha256"].encode("ascii"),
        *(record["sha256"].encode("ascii") for record in source_records),
    )
    seed_body = struct.pack(
        f"<{len(binding['seed_descriptors'])}Q",
        *binding["seed_descriptors"],
    )
    _private_bytes(seed_path, seed_header + seed_body)
    seed_identity = file_identity(seed_path)
    _private_text(
        source_path,
        runtime_type_reference_source(
            binding=binding,
            seed_path=seed_path,
            seed_identity=seed_identity,
            output_path=extension_path,
            status_path=status_path,
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-type-reference-"
        + file_identity(source_path)["sha256"][:12]
        + f"-{time.time_ns():x}"
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
            label="runtime type reference collector",
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
            label="runtime type reference injector",
            source_path=injector_source,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_TYPE_REFERENCE_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary.expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "creation_filetime": binding["creation_filetime"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {**binding["capture_identity_inputs"], **{
            key: binding[key]
            for key in (
                "semantics", "type_identity_model", "type_identity_inventory",
                "ancestry_inventory", "method_detail_model",
                "method_detail_inventory", "native_member_detail_model",
                "native_member_detail_inventory", "event_module_model",
                "event_module_inventory", "type_graph_model",
                "type_graph_inventory", "type_graph_status",
                "method_generic_model", "method_generic_inventory",
                "base_type_reference_model",
                "base_type_reference_inventory",
                "generic_parameter_detail_model",
                "generic_parameter_detail_inventory",
            )
        }},
        "seed": seed_identity,
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(extension_path),
        "merged_output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "raw_observation_path": str(raw_observation_path),
        "raw_names_path": str(raw_names_path),
        "string_layout_io_path": str(string_io_path),
        "contract": {
            "seed_count": len(binding["seed_descriptors"]),
            "record_bytes": RUNTIME_TYPE_REFERENCE_RECORD.size,
            "recursive_reference_closure_required": True,
            "source_order_discovery_without_pointer_sort": True,
            "lossless_reference_names_required": True,
            "current_instance_and_lifetime_required": True,
            "method_generic_arguments_seeded": not binding.get("field_type_extension", False),
            "native_field_type_extension": binding.get("field_type_extension", False),
            "native_field_domain_scope": binding.get("native_field_domain_scope", "constructed"),
            "validated_base_inventory_merge_required": True,
            "descriptor_byref": binding["descriptor_byref_contract"],
        },
        "policy": {
            "same_process_required": True,
            "raw_pointers_owner_only": True,
            "saved_type_reference_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": True,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_TYPE_REFERENCE_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "seed_count": len(binding["seed_descriptors"]),
        "policy": plan["policy"],
    }


def _discovery_seed_contract(plan, seed_raw):
    contract = plan.get("contract", {})
    method = contract.get("method_generic_arguments_seeded")
    base = contract.get("base_reference_bootstrap")
    field = contract.get("native_field_type_extension", False)
    if field is True:
        scope = contract.get("native_field_domain_scope", "constructed")
        if method is not False or base is True or scope not in ("constructed", "nominal-and-constructed"):
            return False
        from alpha.p28 import load_extension_source
        source = plan["inputs"].get("field_extension_field_capture")
        if not isinstance(source, dict) or file_identity(Path(source["path"])) != source:
            return False
        model = read_json(Path(source["path"]), maximum_bytes=256 * 1024 * 1024)
        identity = model.get("identity", {})
        if any(type(identity.get("image_base" if key == "image_base_owner_only" else key)) is not type(value)
               or identity.get("image_base" if key == "image_base_owner_only" else key) != value
               for key, value in plan["target"].items()):
            return False


        options = {"allow_empty": True, "include_nominal": True} if scope == "nominal-and-constructed" else {"allow_empty": True}
        evidence = load_extension_source(Path(source["path"]), expected_identity=identity, **options)
        if any(evidence[key] != plan["inputs"].get(key) for key in ("base_type_reference_model", "base_type_reference_inventory")):
            return False


        expected_seeds: list[int] = list(evidence["seed_descriptors"])
        constraint_record = plan["inputs"].get("field_extension_constraint_seed_model")
        if constraint_record is None:
            for key, value in plan["inputs"].items():
                if key.endswith("constraint_seed_model"):
                    constraint_record = value
                    break
        if isinstance(constraint_record, dict):
            try:
                record_path = constraint_record.get("path")
                if not isinstance(record_path, str) or file_identity(Path(record_path)) != constraint_record:
                    return False
            except (OSError, ValueError, TypeError, KeyError, AcquisitionError):
                return False
            from alpha.h01 import AcquisitionError as _SeedAcquisitionError
            try:
                from alpha.p35 import _constraint_seed_descriptors
                constraint_seeds = _constraint_seed_descriptors(Path(record_path))
            except _SeedAcquisitionError:


                return False
            known = set(expected_seeds)
            for descriptor in constraint_seeds:
                if descriptor not in known:
                    known.add(descriptor)
                    expected_seeds.append(descriptor)
        body = seed_raw[RUNTIME_TYPE_REFERENCE_SEED_HEADER.size:]
        if len(body) % 8 == 0 and [row[0] for row in struct.iter_unpack("<Q", body)] == expected_seeds:
            return True

        if constraint_record is not None:
            return len(body) % 8 == 0 and [row[0] for row in struct.iter_unpack("<Q", body)] == evidence["seed_descriptors"]
        return False
    if field is not False:
        return False
    return method is True or (base is True and method is False)


def _validate(
    plan: dict[str, Any], status: dict[str, Any]
) -> tuple[dict[str, int], dict[str, bool]]:
    raw = Path(plan["output_path"]).read_bytes()
    seed_raw = Path(plan["seed"]["path"]).read_bytes()
    if len(raw) < RUNTIME_TYPE_REFERENCE_HEADER.size:
        raise AcquisitionError("runtime type reference output is truncated")
    header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(raw)
    (
        node_count, seed_count, interface_count, argument_count,
        string_bytes, image_base, image_bytes,
    ) = header[5:12]
    record_start = RUNTIME_TYPE_REFERENCE_HEADER.size
    interface_start = record_start + node_count * RUNTIME_TYPE_REFERENCE_RECORD.size
    argument_start = interface_start + interface_count * 8
    string_start = argument_start + argument_count * 8
    header_ok = (
        header[0] == RUNTIME_TYPE_REFERENCE_MAGIC
        and header[1] == RUNTIME_TYPE_REFERENCE_VERSION
        and header[2] == RUNTIME_TYPE_REFERENCE_HEADER.size
        and header[3] == RUNTIME_TYPE_REFERENCE_RECORD.size
        and header[4] == 0
        and seed_count == plan["contract"]["seed_count"]
        and seed_count <= node_count <= 500_000
        and image_base == plan["target"]["image_base_owner_only"]
        and image_bytes == plan["target"]["image_bytes"]
        and _digest(header[12], label="executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[13], label="seed") == plan["seed"]["sha256"]
        and _digest(header[14], label="identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(header[15], label="graph")
        == plan["inputs"]["type_graph_inventory"]["sha256"]
        and _digest(header[16], label="semantics")
        == plan["inputs"]["semantics"]["sha256"]
        and string_start + string_bytes == len(raw)
    )
    seed_header = RUNTIME_TYPE_REFERENCE_SEED_HEADER.unpack_from(seed_raw)
    expected_seeds = (
        struct.unpack_from(
            f"<{seed_count}Q", seed_raw, RUNTIME_TYPE_REFERENCE_SEED_HEADER.size
        )
        if header_ok else ()
    )
    records_ok = header_ok
    descriptors: set[int] = set()
    relations: set[int] = set()
    observed_interfaces = observed_arguments = 0
    shape_counts = {
        "enum_count": 0, "value_type_count": 0, "generic_type_count": 0,
        "generic_definition_count": 0, "generic_parameter_count": 0,
        "byref_count": 0, "array_count": 0, "pointer_count": 0,
    }


    record_rows = (
        RUNTIME_TYPE_REFERENCE_RECORD.iter_unpack(
            memoryview(raw)[
                record_start :
                record_start + node_count * RUNTIME_TYPE_REFERENCE_RECORD.size
            ]
        )
        if header_ok
        else ()
    )
    for index, row in enumerate(record_rows):
        (
            descriptor, canonical, type_object, attributes, shape,
            name_bytes, namespace_bytes, interfaces_here, arguments_here,
            rank, reserved, base, declaring, element, generic_definition,
            interfaces_at, arguments_at, name_offset, namespace_offset,
        ) = row
        if (
            not descriptor or descriptor & 7 or descriptor in descriptors
            or not canonical or canonical & 7 or not type_object or type_object & 7
            or shape & ~TYPE_REFERENCE_SHAPE_MASK or reserved
            or not name_bytes or name_bytes > 65_536 or namespace_bytes > 65_536
            or name_offset < string_start or name_offset + name_bytes > len(raw)
            or namespace_offset < string_start
            or namespace_offset + namespace_bytes > len(raw)
            or interfaces_at != observed_interfaces
            or arguments_at != observed_arguments
            or interfaces_at + interfaces_here > interface_count
            or arguments_at + arguments_here > argument_count
            or bool(shape & TYPE_REFERENCE_GENERIC_DEFINITION)
            and not bool(shape & TYPE_REFERENCE_GENERIC)
            or bool(shape & TYPE_REFERENCE_GENERIC) != bool(arguments_here)
            or bool(shape & TYPE_REFERENCE_GENERIC) != bool(generic_definition)
            or bool(shape & TYPE_REFERENCE_ARRAY) != bool(rank)
            or bool(element)
            != bool(shape & (
                TYPE_REFERENCE_BYREF | TYPE_REFERENCE_ARRAY | TYPE_REFERENCE_POINTER
            ))
            or sum(
                bool(shape & bit)
                for bit in (TYPE_REFERENCE_BYREF, TYPE_REFERENCE_ARRAY, TYPE_REFERENCE_POINTER)
            ) > 1
            or rank > 32
        ):
            records_ok = False
            break
        try:
            name = raw[name_offset:name_offset + name_bytes].decode("utf-8")
            namespace = raw[
                namespace_offset:namespace_offset + namespace_bytes
            ].decode("utf-8")
        except UnicodeDecodeError:
            records_ok = False
            break
        if (
            not name


            or min(name) < " "
            or (bool(namespace) and min(namespace) < " ")
            or index < seed_count and descriptor != expected_seeds[index]
        ):
            records_ok = False
            break
        descriptors.add(descriptor)
        relations.update(filter(None, (canonical, base, declaring, element, generic_definition)))


        if interfaces_here:
            for (value,) in _QWORD.iter_unpack(
                memoryview(raw)[
                    interface_start + interfaces_at * 8 :
                    interface_start + (interfaces_at + interfaces_here) * 8
                ]
            ):
                if not value:
                    records_ok = False
                    break
                relations.add(value)
        if arguments_here and records_ok:
            for (value,) in _QWORD.iter_unpack(
                memoryview(raw)[
                    argument_start + arguments_at * 8 :
                    argument_start + (arguments_at + arguments_here) * 8
                ]
            ):
                if not value:
                    records_ok = False
                    break
                relations.add(value)
        if not records_ok:
            break
        observed_interfaces += interfaces_here
        observed_arguments += arguments_here
        for label, bit in (
            ("enum_count", TYPE_REFERENCE_ENUM),
            ("value_type_count", TYPE_REFERENCE_VALUE_TYPE),
            ("generic_type_count", TYPE_REFERENCE_GENERIC),
            ("generic_definition_count", TYPE_REFERENCE_GENERIC_DEFINITION),
            ("generic_parameter_count", TYPE_REFERENCE_GENERIC_PARAMETER),
            ("byref_count", TYPE_REFERENCE_BYREF),
            ("array_count", TYPE_REFERENCE_ARRAY),
            ("pointer_count", TYPE_REFERENCE_POINTER),
        ):
            shape_counts[label] += bool(shape & bit)
    closure_ok = (
        records_ok
        and observed_interfaces == interface_count
        and observed_arguments == argument_count
        and relations <= descriptors
        and len(descriptors) == node_count
    )
    counts = {
        "seed_count": seed_count,
        "node_count": node_count,
        "interface_reference_count": interface_count,
        "generic_argument_reference_count": argument_count,
        "string_bytes": string_bytes,
        **shape_counts,
    }
    from alpha.p14 import verify_plan_contract
    checks = {
        "descriptor_byref_current_code_derived": verify_plan_contract(plan),
        "descriptor_byref_live_code_matches": status.get("descriptor_byref_live_code_matches") is True,
        "status_schema": status.get("schema") == RUNTIME_TYPE_REFERENCE_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "status_current_instance_matches": all(
            type(status.get(key)) is int and status[key] == plan["target"].get(key)
            for key in ("process_id", "creation_filetime")
        ),
        "header_bound": header_ok,
        "seed_header_bound": seed_header[0] == RUNTIME_TYPE_REFERENCE_SEED_MAGIC
        and seed_header[1] == RUNTIME_TYPE_REFERENCE_SEED_VERSION
        and seed_header[2] == 0
        and seed_header[3] == seed_count
        and _digest(seed_header[4], label="seed executable")
        == plan["target"]["executable_sha256"]
        and _digest(seed_header[5], label="seed identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(seed_header[6], label="seed methods")
        == plan["inputs"]["method_detail_inventory"]["sha256"]
        and _digest(seed_header[7], label="seed native members")
        == plan["inputs"]["native_member_detail_inventory"]["sha256"]
        and _digest(seed_header[8], label="seed events")
        == plan["inputs"]["event_module_inventory"]["sha256"]
        and _digest(seed_header[9], label="seed graph")
        == plan["inputs"]["type_graph_inventory"]["sha256"]
        and _digest(seed_header[10], label="seed method generics")
        == plan["inputs"]["method_generic_inventory"]["sha256"]
        and _digest(
            seed_header[11], label="seed generic parameter detail"
        )
        == plan["inputs"]["generic_parameter_detail_inventory"]["sha256"],
        "records_valid": records_ok,
        "recursive_reference_closure_complete": closure_ok,
        "discovery_stage_seed_contract_valid": _discovery_seed_contract(plan, seed_raw),
        "all_nodes_captured": status.get("completed_node_count") == node_count,
        "status_node_count_matches": status.get("node_count") == node_count,
        "status_interface_count_matches": status.get("interface_reference_count") == interface_count,
        "status_generic_argument_count_matches": status.get("generic_argument_reference_count") == argument_count,
        "status_shape_counts_match": all(status.get(key) == value for key, value in shape_counts.items()),
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "saved_type_reference_absent": status.get("saved_type_reference_used") is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_layout_limitation_disclosed": status.get("fixed_offset_used") is True,
        "external_runtime_component_absent": status.get("external_runtime_component_used") is False,
    }
    return counts, checks


@string_layout_replay_scope()
@current_capture_scope
def capture_runtime_base_type_reference_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    ancestry_inventory: Path, method_detail_model: Path,
    method_detail_inventory: Path, native_member_detail_model: Path,
    native_member_detail_inventory: Path, event_module_model: Path,
    event_module_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path, output_dir: Path, wine: Path,
    wineprefix: Path, compiler: Path | None = None,
    timeout: float = 1800.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_base_type_reference_inventory(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        ancestry_inventory=ancestry_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        native_member_detail_model=native_member_detail_model,
        native_member_detail_inventory=native_member_detail_inventory,
        event_module_model=event_module_model,
        event_module_inventory=event_module_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan = read_json(
        output_dir / "runtime-type-reference-plan.private.json"
    )
    _verify_reference_capture_sources(plan)
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
            "runtime base type reference injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-type-reference-injector.private.log",
        json.dumps(
            {
                "returncode": injected.returncode,
                "stdout": injected.stdout,
                "stderr": injected.stderr,
            },
            ensure_ascii=False,
            indent=2,
        ) + "\n",
    )
    if injected.returncode:
        raise AcquisitionError(
            "runtime base type reference injection failed"
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
            "runtime base type reference capture timed out"
        )
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime base type reference capture failed "
            f"(status={status.get('status')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    _verify_reference_capture_sources(plan)
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    counts, checks = _validate(plan, status)
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime base type reference validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    model = {
        "schema": RUNTIME_TYPE_REFERENCE_SCHEMA,
        "status": "runtime-validated",
        "target": dict(plan["target"]),
        "inputs": plan["inputs"],
        "seed": plan["seed"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "base_reference_bootstrap": True,
        "owner_only": True,
    }
    _verify_reference_capture_sources(plan)
    model["metadata_complete"] = False
    model["proof_limits"] = dict(_REFERENCE_PROOF_LIMITS)
    model["descriptor_byref_contract"] = plan["contract"]["descriptor_byref"]
    from alpha.c05 import normalize_reference_names
    model["raw_names"] = normalize_reference_names(plan=plan, output_path=output_path)
    _verify_reference_capture_sources(plan)
    _private_json(Path(plan["model_path"]), model)
    return {
        "schema": RUNTIME_TYPE_REFERENCE_SCHEMA,
        "status": "runtime-validated",
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "inventory": model["inventory"],
        "base_reference_bootstrap": True,
    }


_REFERENCE_SNAPSHOT_MEMO: dict[str, Any] | None = None
_REFERENCE_SNAPSHOT_STAT_KEYS = ("st_size", "st_mtime_ns", "st_ctime_ns")


def _reference_snapshot_file(path: Path, *, label: str) -> tuple[
    tuple[Any, ...], list[int], dict[int, dict[str, Any]]
]:
    global _REFERENCE_SNAPSHOT_MEMO
    path = Path(path)

    def fingerprint() -> tuple[int, ...]:
        status = path.stat()
        return (
            status.st_dev, status.st_ino,
            *(getattr(status, key) for key in _REFERENCE_SNAPSHOT_STAT_KEYS),
        )

    key = str(path)
    before = fingerprint()
    memo = _REFERENCE_SNAPSHOT_MEMO
    if memo is not None and memo["path"] == key and memo["fingerprint"] == before:
        return memo["header"], memo["order"], memo["nodes"]
    snapshot = _reference_snapshot(path.read_bytes(), label=label)
    if fingerprint() == before:
        _REFERENCE_SNAPSHOT_MEMO = {
            "path": key, "fingerprint": before,
            "header": snapshot[0], "order": snapshot[1], "nodes": snapshot[2],
        }
    return snapshot


def _reference_snapshot(raw: bytes, *, label: str) -> tuple[
    tuple[Any, ...], list[int], dict[int, dict[str, Any]]
]:
    if len(raw) < RUNTIME_TYPE_REFERENCE_HEADER.size:
        raise AcquisitionError(
            f"runtime type reference {label} snapshot is truncated"
        )
    header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(raw)
    node_count, interface_count, argument_count, string_bytes = (
        header[5], header[7], header[8], header[9]
    )
    record_start = RUNTIME_TYPE_REFERENCE_HEADER.size
    interface_start = (
        record_start + node_count * RUNTIME_TYPE_REFERENCE_RECORD.size
    )
    argument_start = interface_start + interface_count * 8
    string_start = argument_start + argument_count * 8
    if (
        header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or header[2] != RUNTIME_TYPE_REFERENCE_HEADER.size
        or header[3] != RUNTIME_TYPE_REFERENCE_RECORD.size
        or header[4] != 0
        or header[6] > node_count
        or string_start + string_bytes != len(raw)
    ):
        raise AcquisitionError(
            f"runtime type reference {label} snapshot is invalid"
        )
    order: list[int] = []
    nodes: dict[int, dict[str, Any]] = {}


    order_append = order.append
    qword_run = _qword_run
    for row in RUNTIME_TYPE_REFERENCE_RECORD.iter_unpack(
        memoryview(raw)[
            record_start :
            record_start + node_count * RUNTIME_TYPE_REFERENCE_RECORD.size
        ]
    ):
        (descriptor, canonical, type_object, attributes, shape, name_length,
         namespace_length, interface_count, argument_count, rank, reserved,
         base, declaring, element, generic_definition, interface_offset,
         argument_offset, name_offset, namespace_offset) = row
        try:
            name = raw[name_offset : name_offset + name_length].decode("utf-8")
            namespace = raw[namespace_offset : namespace_offset + namespace_length].decode("utf-8")
        except UnicodeDecodeError as error:
            raise AcquisitionError(
                f"runtime type reference {label} text is invalid"
            ) from error
        interfaces = qword_run(raw, interface_start + interface_offset * 8, interface_count)
        arguments = qword_run(raw, argument_start + argument_offset * 8, argument_count)
        node = {
            "descriptor": descriptor,
            "canonical": canonical,
            "type_object": type_object,
            "attributes": attributes,
            "shape": shape,
            "name": name,
            "namespace": namespace,
            "interfaces": interfaces,
            "arguments": arguments,
            "rank": rank,
            "base": base,
            "declaring": declaring,
            "element": element,
            "generic_definition": generic_definition,
        }
        if (
            not descriptor
            or descriptor & 7
            or descriptor in nodes
            or not name


            or min(name) < " "
            or (bool(namespace) and min(namespace) < " ")
        ):
            raise AcquisitionError(
                f"runtime type reference {label} node is invalid"
            )
        order_append(descriptor)
        nodes[descriptor] = node
    return header, order, nodes


def _nominal_reference_resolver(
    nodes: dict[int, dict[str, Any]], raw_names: dict[int, tuple[Any, Any]],
) -> Any:
    cache: dict[int, tuple[Any, ...]] = {}
    active: set[int] = set()

    def resolve(descriptor: int) -> tuple[Any, ...] | None:
        if not descriptor:
            return None
        cached = cache.get(descriptor)
        if cached is not None:
            return cached
        node = nodes.get(descriptor)
        if node is None:
            raise AcquisitionError(
                "runtime type reference nominal relation is absent"
            )


        raw = raw_names[descriptor]
        local = (
            raw[1], raw[0], node["shape"], node["rank"]
        )
        if node["shape"] & TYPE_REFERENCE_GENERIC_PARAMETER:
            cache[descriptor] = local
            return local
        if descriptor in active:
            return ("recursive", *local)
        active.add(descriptor)
        value = (
            *local,
            resolve(node["declaring"]),
            resolve(node["element"]),
            tuple(resolve(argument) for argument in node["arguments"]),
        )
        active.remove(descriptor)
        cache[descriptor] = value
        return value

    return resolve


def _nominal_node_semantics(
    node: dict[str, Any], raw: tuple[Any, Any], resolve: Any,
) -> tuple[Any, ...]:
    return (
        node["attributes"], node["shape"], raw[0], raw[1],
        node["rank"], resolve(node["canonical"]),
        resolve(node["base"]), resolve(node["declaring"]),
        resolve(node["element"]), resolve(node["generic_definition"]),
        tuple(resolve(value) for value in node["interfaces"]),
        tuple(resolve(value) for value in node["arguments"]),
    )


def _merge_reference_snapshots(
    *, plan: dict[str, Any], extension_path: Path,
) -> tuple[dict[str, int], dict[str, bool]]:
    base_path = Path(
        plan["inputs"]["base_type_reference_inventory"]["path"]
    )
    base_header, base_order, base_nodes = _reference_snapshot_file(base_path, label="base")
    extension_header, extension_order, extension_nodes = _reference_snapshot_file(
        extension_path, label="extension"
    )
    if (
        base_header[10:12] != extension_header[10:12]
        or _digest(base_header[12], label="base executable")
        != _digest(extension_header[12], label="extension executable")
        or _digest(base_header[14], label="base identity")
        != _digest(extension_header[14], label="extension identity")
        or _digest(base_header[15], label="base graph")
        != _digest(extension_header[15], label="extension graph")
        or _digest(base_header[16], label="base semantics")
        != _digest(extension_header[16], label="extension semantics")
    ):
        raise AcquisitionError(
            "runtime type reference merge identities conflict"
        )
    from alpha.c05 import raw_values_for_merge, display_name_bytes
    base_raw_names, extension_raw_names = raw_values_for_merge(plan)
    if set(base_raw_names) != set(base_nodes) or set(extension_raw_names) != set(extension_nodes):
        raise AcquisitionError("raw TypeRef merge names do not cover both descriptor domains")


    duplicate_nodes = base_nodes.keys() & extension_nodes.keys()
    duplicate_count = 0
    base_resolve = _nominal_reference_resolver(base_nodes, base_raw_names)
    extension_resolve = _nominal_reference_resolver(extension_nodes, extension_raw_names)
    for descriptor in duplicate_nodes:
        duplicate_count += 1
        if _nominal_node_semantics(
            base_nodes[descriptor], base_raw_names[descriptor], base_resolve
        ) != _nominal_node_semantics(
            extension_nodes[descriptor], extension_raw_names[descriptor], extension_resolve
        ):
            raise AcquisitionError(
                "runtime type reference duplicate nominal semantics conflict"
            )
    merged_nodes = dict(base_nodes)
    merged_nodes.update(
        (descriptor, node)
        for descriptor, node in extension_nodes.items()
        if descriptor not in merged_nodes
    )
    base_seeds = base_order[: base_header[6]]
    extension_seeds = extension_order[: extension_header[6]]
    prefix = list(dict.fromkeys(base_seeds + extension_seeds))
    prefix_set = set(prefix)
    order = prefix + [
        descriptor
        for descriptor in base_order + extension_order
        if descriptor not in prefix_set
    ]
    order = list(dict.fromkeys(order))
    if set(order) != set(merged_nodes):
        raise AcquisitionError(
            "runtime type reference merged order is incomplete"
        )
    descriptors = set(merged_nodes)
    relations: set[int] = set()
    for node in merged_nodes.values():


        relations.update(filter(None, (
            node["canonical"], node["base"], node["declaring"],
            node["element"], node["generic_definition"],
            *node["interfaces"], *node["arguments"],
        )))
    if not relations <= descriptors:
        raise AcquisitionError(
            "runtime type reference merged closure is incomplete"
        )

    interfaces: list[int] = []
    arguments: list[int] = []
    strings = bytearray()
    packed_nodes: list[tuple[Any, ...]] = []
    merged_raw_names = dict(base_raw_names)
    merged_raw_names.update(extension_raw_names)


    total_interface_slots = sum(len(node["interfaces"]) for node in merged_nodes.values())
    total_argument_slots = sum(len(node["arguments"]) for node in merged_nodes.values())
    fixed_bytes = (
        RUNTIME_TYPE_REFERENCE_HEADER.size
        + len(order) * RUNTIME_TYPE_REFERENCE_RECORD.size
        + (total_interface_slots + total_argument_slots) * 8
    )
    for index, descriptor in enumerate(order):
        node = merged_nodes[descriptor]
        interface_at = len(interfaces)
        argument_at = len(arguments)
        interfaces.extend(node["interfaces"])
        arguments.extend(node["arguments"])
        name = display_name_bytes(merged_raw_names[descriptor][0], index)
        namespace = display_name_bytes(merged_raw_names[descriptor][1], index, namespace=True)
        name_offset = len(strings)
        strings.extend(name)
        namespace_offset = len(strings)
        strings.extend(namespace)
        packed_nodes.append(
            (
                descriptor, node["canonical"], node["type_object"],
                node["attributes"], node["shape"], len(name),
                len(namespace), len(node["interfaces"]),
                len(node["arguments"]), node["rank"], 0, node["base"],
                node["declaring"], node["element"],
                node["generic_definition"], interface_at, argument_at,
                name_offset + fixed_bytes, namespace_offset + fixed_bytes,
            )
        )
    input_records = plan["inputs"]
    seed_path = Path(plan["merged_output_path"]).with_name(
        "runtime-type-reference-seeds-merged.private.bin"
    )
    seed_header = RUNTIME_TYPE_REFERENCE_SEED_HEADER.pack(
        RUNTIME_TYPE_REFERENCE_SEED_MAGIC,
        RUNTIME_TYPE_REFERENCE_SEED_VERSION,
        0,
        len(prefix),
        plan["target"]["executable_sha256"].encode("ascii"),
        input_records["type_identity_inventory"]["sha256"].encode("ascii"),
        input_records["method_detail_inventory"]["sha256"].encode("ascii"),
        input_records["native_member_detail_inventory"]["sha256"].encode(
            "ascii"
        ),
        input_records["event_module_inventory"]["sha256"].encode("ascii"),
        input_records["type_graph_inventory"]["sha256"].encode("ascii"),
        input_records["method_generic_inventory"]["sha256"].encode("ascii"),
        input_records["generic_parameter_detail_inventory"]["sha256"].encode(
            "ascii"
        ),
    )
    _private_bytes(
        seed_path,
        seed_header + struct.pack(f"<{len(prefix)}Q", *prefix),
    )
    seed_identity = file_identity(seed_path)
    header = RUNTIME_TYPE_REFERENCE_HEADER.pack(
        RUNTIME_TYPE_REFERENCE_MAGIC,
        RUNTIME_TYPE_REFERENCE_VERSION,
        RUNTIME_TYPE_REFERENCE_HEADER.size,
        RUNTIME_TYPE_REFERENCE_RECORD.size,
        0,
        len(packed_nodes),
        len(prefix),
        len(interfaces),
        len(arguments),
        len(strings),
        base_header[10],
        base_header[11],
        plan["target"]["executable_sha256"].encode("ascii"),
        seed_identity["sha256"].encode("ascii"),
        input_records["type_identity_inventory"]["sha256"].encode("ascii"),
        input_records["type_graph_inventory"]["sha256"].encode("ascii"),
        input_records["semantics"]["sha256"].encode("ascii"),
    )
    body = bytearray(header)


    pack_record = RUNTIME_TYPE_REFERENCE_RECORD.pack
    for row in packed_nodes:
        body += pack_record(*row)
    if interfaces:
        body.extend(struct.pack(f"<{len(interfaces)}Q", *interfaces))
    if arguments:
        body.extend(struct.pack(f"<{len(arguments)}Q", *arguments))
    body.extend(strings)
    merged_path = Path(plan["merged_output_path"])
    _private_bytes(merged_path, bytes(body))
    merged_counts = {
        "seed_count": len(prefix),
        "node_count": len(packed_nodes),
        "interface_reference_count": len(interfaces),
        "generic_argument_reference_count": len(arguments),
        "string_bytes": len(strings),
        "base_node_count": len(base_nodes),
        "extension_node_count": len(extension_nodes),
        "extension_unique_node_count": len(extension_nodes) - duplicate_count,
        "duplicate_semantics_match_count": duplicate_count,
    }
    merged_checks = {
        "validated_base_inventory_merged": bool(base_nodes),
        "runtime_extension_inventory_merged": bool(extension_nodes),
        "duplicate_nominal_semantics_exact": duplicate_count
        == len(duplicate_nodes),
        "merged_descriptor_union_exact": len(merged_nodes)
        == len(base_nodes) + len(extension_nodes) - duplicate_count,
        "merged_recursive_reference_closure_complete": relations
        <= descriptors,
        "method_generic_extension_seeds_preserved": all(
            descriptor in merged_nodes for descriptor in extension_seeds
        ),
        "merged_seed_header_bound": file_identity(seed_path)["sha256"]
        == _digest(
            RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(body)[13],
            label="merged seed",
        ),
    }
    return merged_counts, merged_checks


@current_capture_scope
def capture_runtime_type_reference_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    ancestry_inventory: Path, method_detail_model: Path,
    method_detail_inventory: Path, native_member_detail_model: Path,
    native_member_detail_inventory: Path, event_module_model: Path,
    event_module_inventory: Path, type_graph_model: Path,
    type_graph_inventory: Path, method_generic_model: Path,
    method_generic_inventory: Path, base_type_reference_model: Path,
    base_type_reference_inventory: Path, output_dir: Path, wine: Path,
    generic_parameter_detail_model: Path,
    generic_parameter_detail_inventory: Path,
    wineprefix: Path, compiler: Path | None = None,
    timeout: float = 1800.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_type_reference_inventory(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        ancestry_inventory=ancestry_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        native_member_detail_model=native_member_detail_model,
        native_member_detail_inventory=native_member_detail_inventory,
        event_module_model=event_module_model,
        event_module_inventory=event_module_inventory,
        type_graph_model=type_graph_model,
        type_graph_inventory=type_graph_inventory,
        method_generic_model=method_generic_model,
        method_generic_inventory=method_generic_inventory,
        base_type_reference_model=base_type_reference_model,
        base_type_reference_inventory=base_type_reference_inventory,
        generic_parameter_detail_model=generic_parameter_detail_model,
        generic_parameter_detail_inventory=generic_parameter_detail_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    return _capture_prepared_reference_extension(
        output_dir=output_dir, wine=wine, wineprefix=wineprefix, timeout=timeout
    )


def _capture_prepared_reference_extension(*, output_dir, wine, wineprefix, timeout=1800.0):

    plan = read_json(output_dir / "runtime-type-reference-plan.private.json")
    _verify_reference_capture_sources(plan)
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
            "runtime type reference injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-type-reference-injector.private.log",
        json.dumps(
            {
                "returncode": injected.returncode,
                "stdout": injected.stdout,
                "stderr": injected.stderr,
            },
            ensure_ascii=False,
            indent=2,
        ) + "\n",
    )
    if injected.returncode:
        raise AcquisitionError("runtime type reference injection failed")
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
        raise AcquisitionError("runtime type reference capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime type reference capture failed "
            f"(status={status.get('status')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    _verify_reference_capture_sources(plan)
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    extension_counts, extension_checks = _validate(plan, status)
    if not all(extension_checks.values()):
        raise AcquisitionError(
            "runtime type reference validation failed: "
            + ", ".join(
                sorted(
                    key
                    for key, value in extension_checks.items()
                    if not value
                )
            )
        )
    merged_counts, merged_checks = _merge_reference_snapshots(
        plan=plan, extension_path=output_path
    )
    checks = {
        **{
            f"runtime_extension_{key}": value
            for key, value in extension_checks.items()
        },
        **merged_checks,
    }
    if not all(checks.values()):
        raise AcquisitionError(
            "runtime type reference merge validation failed: "
            + ", ".join(
                sorted(key for key, value in checks.items() if not value)
            )
        )
    counts = {
        **merged_counts,
        **{
            f"runtime_extension_{key}": value
            for key, value in extension_counts.items()
        },
    }
    merged_output_path = Path(plan["merged_output_path"])
    _seal_runtime_output(merged_output_path)
    model = {
        "schema": RUNTIME_TYPE_REFERENCE_SCHEMA,
        "status": "runtime-validated",
        "target": dict(plan["target"]),
        "inputs": plan["inputs"],
        "seed": plan["seed"],
        "inventory": file_identity(merged_output_path),
        "runtime_extension_inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "owner_only": True,
    }
    _verify_reference_capture_sources(plan)
    model["metadata_complete"] = False
    model["proof_limits"] = dict(_REFERENCE_PROOF_LIMITS)
    model["descriptor_byref_contract"] = plan["contract"]["descriptor_byref"]
    from alpha.c05 import normalize_reference_names
    model["raw_names"] = normalize_reference_names(plan=plan, output_path=merged_output_path,
        base_model=read_json(Path(plan["inputs"]["base_type_reference_model"]["path"])))
    _verify_reference_capture_sources(plan)
    _private_json(Path(plan["model_path"]), model)
    return {
        "schema": RUNTIME_TYPE_REFERENCE_SCHEMA,
        "status": "runtime-validated",
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "inventory": model["inventory"],
    }
