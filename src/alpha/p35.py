import json
import os
import stat
import struct
import tempfile
from pathlib import Path
from typing import Any, TextIO

from alpha.p12 import _owner_directory, _private_json
from alpha.h01 import AcquisitionError, ContractViolation, owner_uid, owner_only_path_bits, set_private_descriptor_mode
from alpha.p01 import reflection_contract
from alpha.p24 import RUNTIME_EVENT_MODULE_EVENT
from alpha.p17 import event_raise_pointer
from alpha.p28 import RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER, RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD
from alpha.p22 import METHOD_DETAIL_CONSTRUCTOR
from alpha.p26 import RUNTIME_METHOD_GENERIC_HEADER, RUNTIME_METHOD_GENERIC_RECORD
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER, RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY
from alpha.p33 import RUNTIME_NATIVE_OUTPUT_COMPLETE_STATUS, RUNTIME_NATIVE_OUTPUT_SCHEMA, _RuntimeOutput, _optional_text, _text
from alpha.c04 import MappedPE
from alpha.p25 import TYPE_REFERENCE_GENERIC_PARAMETER
from alpha.h02 import file_identity, read_json


RUNTIME_DUMMY_BUNDLE_SCHEMA = "alpha.runtime-dummy-bundle/v1"
RUNTIME_DUMMY_IMAGE_SCHEMA = "alpha.runtime-dummy-image/v1"
RUNTIME_DUMMY_BUNDLE_RECEIPT_SCHEMA = "alpha.runtime-dummy-bundle-receipt/v1"
RUNTIME_DUMMY_OUTPUT_SCHEMA = "alpha.runtime-dummy-dll-output/v1"


class _AtomicJsonStream:
    def __init__(self, path: Path):
        self.path = path
        self.temporary: Path | None = None
        self.stream: TextIO | None = None

    def __enter__(self) -> TextIO:
        descriptor, temporary = tempfile.mkstemp(
            prefix=f".{self.path.name}.", dir=self.path.parent
        )
        set_private_descriptor_mode(descriptor, 0o600)
        self.temporary = Path(temporary)
        self.stream = os.fdopen(
            descriptor,
            "w",
            encoding="utf-8",
            newline="\n",
            buffering=1024 * 1024,
        )
        return self.stream

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        assert self.stream is not None and self.temporary is not None
        try:
            if exc_type is None:
                self.stream.flush()
                os.fsync(self.stream.fileno())
            self.stream.close()
            if exc_type is None:
                os.replace(self.temporary, self.path)
                self.path.chmod(0o600)
        finally:
            self.temporary.unlink(missing_ok=True)


def _compact(record: dict[str, Any]) -> str:
    return json.dumps(record, ensure_ascii=False, separators=(",", ":"))


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime DummyDll {label} is not owner-only")
    return path


def _validated_native_receipt(
    path: Path, *, allow_type_method_metadata: bool = False
) -> tuple[dict[str, Any], dict[str, Path]]:
    path = _owner_file(path, label="native output receipt")
    receipt = read_json(path)
    accepted_statuses = {
        RUNTIME_NATIVE_OUTPUT_COMPLETE_STATUS,


        "structural-string-and-all-metadata-output-complete",
        "structural-string-literal-constants-and-all-metadata-output-complete",
    }
    if allow_type_method_metadata:


        accepted_statuses.add(
            "structural-string-and-type-method-metadata-output-complete-members-pending"
        )


        accepted_statuses.add(
            "structural-string-and-all-metadata-output-complete-enum-constants-pending"
        )
        accepted_statuses.add(
            "structural-string-and-all-metadata-output-complete-assembly-identities-pending"
        )
    if (
        receipt.get("schema") != RUNTIME_NATIVE_OUTPUT_SCHEMA
        or receipt.get("status") not in accepted_statuses
        or not isinstance(receipt.get("checks"), dict)
        or not receipt["checks"]
        or not all(receipt["checks"].values())
    ):
        raise AcquisitionError("runtime DummyDll native output receipt is incomplete")
    inputs = receipt.get("inputs")
    if not isinstance(inputs, dict):
        raise AcquisitionError("runtime DummyDll input bindings are unavailable")
    required = {
        "binary",
        "type_identity_inventory",
        "type_graph_inventory",
        "type_reference_inventory",
        "method_detail_inventory",
        "native_member_detail_inventory",
        "event_module_inventory",
        "method_generic_inventory",
        "generic_parameter_detail_inventory",
    }
    paths: dict[str, Path] = {}
    for key, binding in inputs.items():


        if (
            allow_type_method_metadata
            and key == "metadata_usage_state"
            and isinstance(binding, str)
        ):
            continue
        if not isinstance(binding, dict) or not isinstance(binding.get("path"), str):
            raise AcquisitionError("runtime DummyDll input binding is invalid")
        candidate = Path(binding["path"]).expanduser().resolve()
        if key == "binary":
            if not candidate.is_file() or candidate.is_symlink():
                raise AcquisitionError("runtime DummyDll binary is unavailable")
        else:
            candidate = _owner_file(candidate, label=key.replace("_", " "))
        if file_identity(candidate) != binding:
            raise AcquisitionError(f"runtime DummyDll {key} binding is stale")
        paths[key] = candidate
    if required - set(paths):
        raise AcquisitionError("runtime DummyDll required inputs are incomplete")
    executable_sha256 = receipt.get("target", {}).get("executable_sha256")
    if executable_sha256 != inputs["binary"].get("sha256"):
        raise AcquisitionError("runtime DummyDll executable binding differs")
    return receipt, paths


def _parameter_map(
    runtime: _RuntimeOutput, descriptors: list[int]
) -> dict[int, int]:
    result: dict[int, int] = {}
    for index, descriptor in enumerate(descriptors):
        row = runtime.renderer.reference_row(
            runtime.renderer.node_by_descriptor[descriptor]
        )
        if not row[4] & TYPE_REFERENCE_GENERIC_PARAMETER:
            raise ContractViolation(
                "runtime DummyDll generic argument is not a parameter"
            )
        for candidate in (descriptor, row[1]):
            previous = result.get(candidate)
            if previous is not None and previous != index:
                raise ContractViolation(
                    "runtime DummyDll generic parameter aliases collide"
                )
            result[candidate] = index
    return result


def _type_generic_descriptors(
    runtime: _RuntimeOutput, type_index: int
) -> list[int]:
    row = runtime.renderer.graph_row(type_index)
    return [
        struct.unpack_from(
            "<Q",
            runtime.graph,
            runtime.renderer.graph_argument_start + (row[9] + offset) * 8,
        )[0]
        for offset in range(row[7])
    ]


def _type_generic_parameters(
    runtime: _RuntimeOutput,
    descriptors: list[int],
    parameter_map: dict[int, int],
) -> tuple[list[dict[str, Any]], int, int]:
    records: list[dict[str, Any]] = []
    for descriptor in descriptors:
        detail = runtime.generic_detail_by_descriptor.get(descriptor)
        if (detail is None or detail[0] != descriptor or detail[1] & ~31 or
            detail[3] + detail[2] > runtime.generic_constraint_count):
            raise ContractViolation("runtime DummyDll type generic parameter detail is absent or invalid")
        from alpha.c05 import metadata_reference_name
        name = (metadata_reference_name(runtime, descriptor) if hasattr(runtime, "raw_reference_names") else
                runtime.renderer.render(descriptor))
        constraints: list[str] = []
        for offset in range(detail[2]):
            related = struct.unpack_from(
                "<Q",
                runtime.generic_parameter_details,
                runtime.generic_constraint_start + (detail[3] + offset) * 8,
            )[0]
            constraints.append(runtime.renderer.render_signature(
                related, type_parameters=parameter_map
            ))
        records.append(
            {
                "name": name,
                "attributes": detail[1],
                "constraints": constraints,
            }
        )


    return records, 0, 0


def _method_generic_parameters(
    runtime: _RuntimeOutput,
    method_index: int,
    type_parameters: dict[int, int],
) -> tuple[list[dict[str, Any]], dict[int, int]]:
    from alpha.c05 import metadata_reference_name
    recorded_index, count, start = RUNTIME_METHOD_GENERIC_RECORD.unpack_from(
        runtime.method_generics,
        RUNTIME_METHOD_GENERIC_HEADER.size
        + method_index * RUNTIME_METHOD_GENERIC_RECORD.size,
    )
    if recorded_index != method_index or start + count > runtime.method_generic_argument_count:
        raise ContractViolation("runtime DummyDll method generic range is invalid")
    descriptors = [
        struct.unpack_from(
            "<Q",
            runtime.method_generics,
            runtime.method_generic_argument_start + (start + offset) * 8,
        )[0]
        for offset in range(count)
    ]
    method_parameters = _parameter_map(runtime, descriptors)
    records: list[dict[str, Any]] = []
    for offset, descriptor in enumerate(descriptors):
        detail = RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.unpack_from(
            runtime.generic_parameter_details,
            RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
            + (start + offset) * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size,
        )
        if detail[0] != descriptor or detail[3] + detail[2] > runtime.generic_constraint_count:
            raise ContractViolation(
                "runtime DummyDll generic parameter detail range is invalid"
            )
        constraints: list[str] = []
        for constraint_offset in range(detail[2]):
            related = struct.unpack_from(
                "<Q",
                runtime.generic_parameter_details,
                runtime.generic_constraint_start
                + (detail[3] + constraint_offset) * 8,
            )[0]
            constraints.append(
                runtime.renderer.render_signature(
                    related,
                    type_parameters=type_parameters,
                    method_parameters=method_parameters,
                )
            )
        records.append(
            {
                "name": (metadata_reference_name(runtime, descriptor) if hasattr(runtime, "raw_reference_names") else
                         runtime.renderer.render(descriptor)),
                "attributes": detail[1],
                "constraints": constraints,
            }
        )
    return records, method_parameters


def _observed_name(runtime, domain, index, display):
    if hasattr(runtime, "raw_metadata_names"):
        from alpha.c05 import original_metadata_name
        return original_metadata_name(runtime, domain, index)
    return display


def _observed_images(runtime, receipt, paths):
    from alpha.p46 import load_runtime_assembly_identities
    from alpha.c05 import original_module_name
    roles = ("assembly_identity_model", "assembly_identity_inventory")
    if any(role not in paths for role in roles):
        raise AcquisitionError("runtime DummyDll requires observed assembly identities")
    identities = load_runtime_assembly_identities(model_path=paths[roles[0]], inventory_path=paths[roles[1]],
        expected_executable_sha256=receipt["target"]["executable_sha256"])
    if (identities["inputs"]["event_module_inventory"] != receipt["inputs"]["event_module_inventory"]
        or identities["counts"]["assembly_count"] != runtime.module_count):
        raise AcquisitionError("runtime DummyDll assembly module binding differs")
    by_module = {}
    for row in identities["assemblies"]:
        module = row["module_name"]
        if module in by_module:
            raise AcquisitionError("runtime DummyDll assembly module repeats")
        version = row["version"]
        if (not isinstance(version, list) or len(version) != 4
            or any(type(value) is not int or not 0 <= value <= 65535 for value in version)
            or any(type(row[key]) is not int or not 0 <= row[key] <= 0xFFFFFFFF for key in ("flags", "hash_algorithm"))
            or any(not isinstance(row[key], str) or "\0" in row[key] for key in ("name", "culture"))
            or not row["name"]):
            raise AcquisitionError("runtime DummyDll assembly identity is not representable")
        for key in ("public_key", "public_key_token"):
            try:
                value = bytes.fromhex(row[key])
            except (ValueError, TypeError) as error:
                raise AcquisitionError("runtime DummyDll assembly key encoding differs") from error
            if value.hex() != row[key] or key == "public_key_token" and len(value) not in (0, 8):
                raise AcquisitionError("runtime DummyDll assembly key encoding differs")
        if bool(row["flags"] & 1) != bool(row["public_key"]):
            raise AcquisitionError("runtime DummyDll assembly public-key flag differs from observed blob")
        by_module[module] = row
    names = [original_module_name(runtime, pointer) for pointer in runtime.module_names]
    if len(set(names)) != len(names) or set(by_module) != set(names):
        raise AcquisitionError("runtime DummyDll assembly identities do not close the module domain")
    images = []
    for index, name in enumerate(names):
        row = by_module[name]
        images.append({"id": f"image-{index}", "name": name, "assembly_name": row["name"],
            "version": ".".join(str(value) for value in row["version"]), "culture": row["culture"],
            "attributes": row["flags"], "hash_algorithm": row["hash_algorithm"],
            "public_key": row["public_key"], "public_key_token": row["public_key_token"],
            "assembly_identity_observed": True})
    return images


def _type_skeleton(
    runtime: _RuntimeOutput,
    type_index: int,
    image_id_by_pointer: dict[int, str],
) -> dict[str, Any]:
    identity = runtime.renderer.identity_row(type_index)
    name = _text(runtime.identity, identity[11], identity[8], label="type name")
    namespace = _optional_text(
        runtime.identity, identity[12], identity[9], label="type namespace"
    )
    signature_name, signature_namespace = name, namespace
    name = _observed_name(runtime, "type", type_index, name)
    namespace = _observed_name(runtime, "type_namespace", type_index, namespace)
    declaring_type_id = None
    if identity[5]:
        declaring = runtime.renderer.root_by_descriptor.get(identity[5])
        if declaring is None:
            raise ContractViolation("runtime DummyDll nested owner is absent")
        declaring_type_id = f"type-{declaring}"
    try:
        image_id = image_id_by_pointer[identity[4]]
    except KeyError as error:
        raise ContractViolation("runtime DummyDll type module is absent") from error
    return {
        "id": f"type-{type_index}",
        "image_id": image_id,
        "type_definition_index": type_index,
        "namespace": namespace,
        "name": name,
        "signature_name": signature_name,
        "signature_namespace": signature_namespace,
        "attributes": identity[7],
        "token": identity[10],
        "declaring_type_id": declaring_type_id,
        "is_enum": bool(identity[1] & 0x20),
        "is_value_type": bool(identity[1] & 0x40),
        "is_interface": bool(identity[7] & 0x20),
    }


def _method_id(runtime: _RuntimeOutput, pointer: int) -> str | None:
    if not pointer:
        return None
    index = runtime.method_by_pointer.get(pointer)
    if index is None:
        raise ContractViolation("runtime DummyDll accessor method is absent")
    return f"method-{index}"


def _property_descriptor(
    runtime: _RuntimeOutput, getter: int, setter: int
) -> int:
    pointer = getter or setter
    method_index = runtime.method_by_pointer.get(pointer)
    if method_index is None:
        raise ContractViolation("runtime DummyDll property accessor is absent")
    method = runtime.method_row(method_index)
    if getter:
        if not method[4]:
            raise ContractViolation("runtime DummyDll property getter has no return type")
        return method[4]
    if not method[10]:
        raise ContractViolation("runtime DummyDll property setter has no value")
    return runtime.parameter_row(method[11] + method[10] - 1)[2]


def _complete_type(
    *,
    runtime: _RuntimeOutput,
    pe: MappedPE,
    type_index: int,
    skeleton: dict[str, Any],
    cursors: dict[str, int],
) -> tuple[dict[str, Any], dict[str, int]]:
    graph = runtime.renderer.graph_row(type_index)
    type_descriptors = _type_generic_descriptors(runtime, type_index)
    type_parameter_map = _parameter_map(runtime, type_descriptors)
    generic_parameters, inferred_attributes, inferred_constraints = (
        _type_generic_parameters(runtime, type_descriptors, type_parameter_map)
    )
    record = dict(skeleton)
    record["base_type"] = (
        runtime.renderer.render_signature(
            graph[3], type_parameters=type_parameter_map
        )
        if graph[3]
        else None
    )
    record["interfaces"] = [
        runtime.renderer.render_signature(
            struct.unpack_from(
                "<Q",
                runtime.graph,
                runtime.renderer.graph_interface_start
                + (graph[8] + offset) * 8,
            )[0],
            type_parameters=type_parameter_map,
        )
        for offset in range(graph[6])
    ]
    record["generic_parameters"] = generic_parameters

    fields: list[dict[str, Any]] = []
    while cursors["field"] < runtime.field_count:
        index = cursors["field"]
        row = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        if row[0] != type_index:
            break
        fields.append(
            {
                "id": f"field-{index}",
                "name": _observed_name(runtime, "field", index,
                    _text(runtime.native, row[9], row[7], label="field name")),
                "type": runtime.renderer.render_signature(
                    row[3], type_parameters=type_parameter_map
                ),
                "attributes": row[5],
                "token": row[6],
                "offset": row[4] & 0xFFFFFFFF,
            }
        )
        cursors["field"] += 1
    record["fields"] = fields

    properties: list[dict[str, Any]] = []
    while cursors["property"] < runtime.property_count:
        index = cursors["property"]
        row = RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.unpack_from(
            runtime.native,
            runtime.property_start + index * RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size,
        )
        if row[0] != type_index:
            break
        properties.append(
            {
                "id": f"property-{index}",
                "name": _observed_name(runtime, "property", index, _text(
                    runtime.native, row[9], row[6], label="property name"
                )),
                "type": runtime.renderer.render_signature(
                    _property_descriptor(runtime, row[3], row[4]),
                    type_parameters=type_parameter_map,
                ),
                "attributes": row[7],
                "token": row[5],
                "has_getter": bool(row[3]),
                "has_setter": bool(row[4]),
                "getter_method_id": _method_id(runtime, row[3]),
                "setter_method_id": _method_id(runtime, row[4]),
            }
        )
        cursors["property"] += 1
    record["properties"] = properties

    methods: list[dict[str, Any]] = []
    while cursors["method"] < runtime.method_count:
        index = cursors["method"]
        row = runtime.method_row(index)
        if row[0] != type_index:
            break
        method_generics, method_parameter_map = _method_generic_parameters(
            runtime, index, type_parameter_map
        )
        return_type = (
            "System.Void"
            if row[9] & METHOD_DETAIL_CONSTRUCTOR
            else runtime.renderer.render_signature(
                row[4],
                type_parameters=type_parameter_map,
                method_parameters=method_parameter_map,
            )
        )
        parameters: list[dict[str, Any]] = []
        for parameter_index in range(row[11], row[11] + row[10]):
            parameter = runtime.parameter_row(parameter_index)
            parameters.append(
                {
                    "id": f"parameter-{parameter_index}",
                    "name": _observed_name(runtime, "parameter", parameter_index, _text(
                        runtime.methods,
                        parameter[7],
                        parameter[5],
                        label="parameter name",
                    )),
                    "type": runtime.renderer.render_signature(
                        parameter[2],
                        type_parameters=type_parameter_map,
                        method_parameters=method_parameter_map,
                    ),
                    "attributes": parameter[3],
                }
            )
        pointer = row[3]
        image_base = runtime.identity_header[6]
        image_bytes = runtime.identity_header[7]
        rva = pointer - image_base if image_base <= pointer < image_base + image_bytes else 0
        offset = pe.rva_to_offset(rva) if rva else None
        method_record: dict[str, Any] = {
            "id": f"method-{index}",
            "name": _observed_name(runtime, "method", index, runtime.method_name(index, row)),
            "return_type": return_type,
            "attributes": row[5],
            "impl_attributes": row[6],
            "token": row[7],
            "rva": rva,
            "offset": offset if offset is not None else 0,
            "va": pointer if rva else 0,
            "generic_parameters": method_generics,
            "parameters": parameters,
        }
        if row[8] != 0xFFFF:
            method_record["slot"] = row[8]
        methods.append(method_record)
        cursors["method"] += 1
    record["methods"] = methods

    events: list[dict[str, Any]] = []
    while cursors["event"] < runtime.event_count:
        index = cursors["event"]
        row = RUNTIME_EVENT_MODULE_EVENT.unpack_from(
            runtime.events,
            runtime.event_start + index * RUNTIME_EVENT_MODULE_EVENT.size,
        )
        if row[0] != type_index:
            break
        events.append(
            {
                "id": f"event-{index}",
                "name": _observed_name(runtime, "event", index, _text(
                    runtime.events, row[10], row[7], label="event name"
                )),
                "type": runtime.renderer.render_signature(
                    row[3], type_parameters=type_parameter_map
                ),
                "attributes": row[8],
                "token": row[6],
                "add_method_id": _method_id(runtime, row[4]),
                "remove_method_id": _method_id(runtime, row[5]),
                "raise_method_id": _method_id(runtime, event_raise_pointer(runtime, index)),
            }
        )
        cursors["event"] += 1
    record["events"] = events
    return record, {
        "inferred_type_generic_attribute_count": inferred_attributes,
        "inferred_type_generic_constraint_count": inferred_constraints,
    }


def write_runtime_dummy_bundle(
    *, native_output_receipt: Path, output_dir: Path
) -> dict[str, Any]:
    receipt, paths = _validated_native_receipt(native_output_receipt)
    if "event_module_model" not in paths:
        raise AcquisitionError("runtime DummyDll requires explicit Event raise accessor evidence")
    output_dir = _owner_directory(output_dir)
    final_bundle = output_dir / "runtime-dummy-bundle.private"
    if final_bundle.exists() or final_bundle.is_symlink():
        raise AcquisitionError("runtime DummyDll requires a new bundle destination; existing bundle preserved")
    with tempfile.TemporaryDirectory(
        prefix=".runtime-dummy-bundle.", dir=output_dir
    ) as temporary:
        bundle = Path(temporary).resolve()
        bundle.chmod(0o700)
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
        from alpha.p17 import bind_output_event_accessors
        bind_output_event_accessors(runtime, model_path=paths["event_module_model"],
            event_inventory=receipt["inputs"]["event_module_inventory"],
            type_identity=receipt["inputs"]["type_identity_inventory"])
        from alpha.c05 import bind_output_reference_names
        if "model" not in paths or bind_output_reference_names(model_path=paths["model"],
                inventory=receipt["inputs"]["type_reference_inventory"],
                executable_sha256=receipt["target"]["executable_sha256"], runtime=runtime) is None:
            raise AcquisitionError("DummyDll requires original TypeRef names, not display aliases")
        from alpha.c05 import bind_output_raw_names
        bind_output_raw_names(runtime, reference_model_path=paths["model"], selected=receipt["inputs"], required=True)
        module_order = list(runtime.module_names)
        image_id_by_pointer = {
            pointer: f"image-{index}" for index, pointer in enumerate(module_order)
        }
        images = _observed_images(runtime, receipt, paths)
        skeletons = [
            _type_skeleton(runtime, index, image_id_by_pointer)
            for index in range(runtime.type_count)
        ]
        image_documents: list[dict[str, Any]] = []
        cursors = {"field": 0, "property": 0, "method": 0, "event": 0}
        type_cursor = 0
        inferred_type_attributes = inferred_type_constraints = 0
        with MappedPE(paths["binary"], require_runtime_functions=False) as pe:
            for image_index, pointer in enumerate(module_order):
                image_id = image_id_by_pointer[pointer]
                file_name = f"image-{image_index:03d}.private.json"
                path = bundle / file_name
                counts = {
                    "type_count": 0,
                    "field_count": 0,
                    "property_count": 0,
                    "method_count": 0,
                    "event_count": 0,
                }
                with _AtomicJsonStream(path) as stream:
                    stream.write(
                        '{"schema":"'
                        + RUNTIME_DUMMY_IMAGE_SCHEMA
                        + '","status":"complete","image_id":'
                        + json.dumps(image_id)
                        + ',"types":['
                    )
                    first = True
                    while type_cursor < runtime.type_count:
                        identity = runtime.renderer.identity_row(type_cursor)
                        if identity[4] != pointer:
                            break
                        complete, inference = _complete_type(
                            runtime=runtime,
                            pe=pe,
                            type_index=type_cursor,
                            skeleton=skeletons[type_cursor],
                            cursors=cursors,
                        )
                        if not first:
                            stream.write(",")
                        stream.write(_compact(complete))
                        first = False
                        counts["type_count"] += 1
                        counts["field_count"] += len(complete["fields"])
                        counts["property_count"] += len(complete["properties"])
                        counts["method_count"] += len(complete["methods"])
                        counts["event_count"] += len(complete["events"])
                        inferred_type_attributes += inference[
                            "inferred_type_generic_attribute_count"
                        ]
                        inferred_type_constraints += inference[
                            "inferred_type_generic_constraint_count"
                        ]
                        type_cursor += 1
                    stream.write("]}")
                image_documents.append(
                    {
                        "image_id": image_id,
                        "file_name": file_name,
                        "sha256": file_identity(path)["sha256"],
                        **counts,
                    }
                )
        expected_cursors = {
            "field": runtime.field_count,
            "property": runtime.property_count,
            "method": runtime.method_count,
            "event": runtime.event_count,
        }
        if type_cursor != runtime.type_count or cursors != expected_cursors:
            raise AcquisitionError("runtime DummyDll bundle cursors are incomplete")
        counts = {
            "image_count": len(images),
            "type_count": runtime.type_count,
            "field_count": runtime.field_count,
            "property_count": runtime.property_count,
            "method_count": runtime.method_count,
            "parameter_count": runtime.parameter_count,
            "event_count": runtime.event_count,
            "type_generic_parameter_count": sum(
                runtime.renderer.graph_row(index)[7]
                for index in range(runtime.type_count)
            ),
            "method_generic_parameter_count": runtime.method_generic_argument_count,
            "method_generic_constraint_count": runtime.generic_constraint_count,
            "inferred_type_generic_attribute_count": inferred_type_attributes,
            "inferred_type_generic_constraint_count": inferred_type_constraints,
        }
        contract = reflection_contract()
        manifest = {
            "schema": RUNTIME_DUMMY_BUNDLE_SCHEMA,
            "status": "complete",
            "target": receipt["target"],
            "reflection": {
                "contract_id": contract["contract_id"],
                "operation_count": contract["operation_count"],
                "all_operations_uniquely_resolved": True,
                "fresh_runtime_observation": True,
            },
            "images": images,
            "types": skeletons,
            "image_documents": image_documents,
            "counts": counts,
            "fidelity": {
                "assembly_identity_projection": "dedicated-runtime-inventory",
                "method_generic_parameter_attributes": "exact-runtime-observation",
                "method_generic_parameter_constraints": "exact-runtime-observation",
                "type_generic_parameter_names": "exact-runtime-observation",
                "type_generic_parameter_base_and_interface_constraints": "exact-runtime-observation",
                "type_generic_reference_and_default_constructor_attributes": "exact-runtime-observation",
                "type_generic_variance_attributes": "exact-runtime-observation",
            },
            "source_native_output_receipt": file_identity(
                _owner_file(native_output_receipt, label="native output receipt")
            ),
            "checks": {
                "native_output_receipt_complete": True,
                "all_runtime_images_partitioned": len(images) == runtime.module_count,
                "all_runtime_types_partitioned": type_cursor == runtime.type_count,
                "all_runtime_members_partitioned": cursors == expected_cursors,
                "method_generic_details_exact": True,
                "type_generic_details_not_inferred": inferred_type_attributes == inferred_type_constraints == 0,
                "saved_reference_generation_seed_absent": True,
                "external_runtime_component_absent": True,
            },
        }
        manifest["metadata_complete"] = False
        manifest_path = bundle / "manifest.private.json"
        with _AtomicJsonStream(manifest_path) as stream:
            stream.write(_compact(manifest))
        if not all(manifest["checks"].values()):
            raise AcquisitionError("runtime DummyDll bundle validation failed")
        if _validated_native_receipt(native_output_receipt) != (receipt, paths):
            raise AcquisitionError("DummyDll source receipt changed during bundle generation")
        if _observed_images(runtime, receipt, paths) != images:
            raise AcquisitionError("DummyDll observed assembly identities changed during bundle generation")
        from alpha.h02 import publish_new_directory
        publish_new_directory(bundle, final_bundle)
        final_bundle.chmod(0o700)
    return {
        "schema": RUNTIME_DUMMY_BUNDLE_RECEIPT_SCHEMA,
        "status": "complete",
        "metadata_complete": False,
        "target": receipt["target"],
        "bundle": {
            "path": str(final_bundle),
            "manifest": file_identity(final_bundle / "manifest.private.json"),
        },
        "counts": counts,
        "fidelity": manifest["fidelity"],
        "checks": manifest["checks"],
    }


def build_runtime_dummy_output(
    *,
    native_output_receipt: Path,
    output_dir: Path,
    dotnet: str | None = None,
    timeout: int = 1800,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    bundle = write_runtime_dummy_bundle(
        native_output_receipt=native_output_receipt,
        output_dir=output_dir,
    )
    from .dummy_dll import build_runtime_dummy_dlls

    dummy = build_runtime_dummy_dlls(
        Path(bundle["bundle"]["path"]),
        output_dir=output_dir / "DummyDll",
        dotnet=dotnet,
        timeout=timeout,
    )
    checks = {
        "runtime_bundle_complete": bundle["status"] == "complete"
        and all(bundle["checks"].values()),
        "dummy_dll_complete": dummy["status"] == "complete"
        and all(dummy["checks"].values()),
        "target_binding_matches": bundle["target"] == dummy["target"],
        "inventory_counts_match": all(
            bundle["counts"][key] == dummy["counts"][key]
            for key in (
                "image_count",
                "type_count",
                "field_count",
                "property_count",
                "method_count",
                "event_count",
            )
        ),
        "assembly_partitioned_memory_bound": dummy["emitter"].get(
            "assembly_partitioned_input"
        )
        is True,
        "saved_reference_generation_seed_absent": True,
        "external_runtime_component_absent": True,
    }
    if not all(checks.values()):
        raise AcquisitionError("runtime DummyDll final output validation failed")
    result = {
        "schema": RUNTIME_DUMMY_OUTPUT_SCHEMA,
        "status": "complete",
        "target": bundle["target"],
        "bundle": bundle["bundle"],
        "dummy_dll": dummy,
        "counts": dummy["counts"],
        "fidelity": bundle["fidelity"],
        "checks": checks,
        "metadata_complete": False,
        "remaining_stages": ["all_metadata_domains_proven", "current_native_layouts_proven",
                             "descriptor_qualified_signature_closure", "fresh_full_output_end_to_end"],
    }
    _private_json(
        output_dir / "alpha-runtime-dummy-dll-receipt.private.json", result
    )
    return result


import inspect
from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.p13 import RuntimeProcessProbe, _safe_path
from alpha.p14 import current_capture_scope
from alpha.p19 import _implementation_digest
from alpha.c01 import bind_runtime_process
from alpha.c04 import _verify_files
from alpha.p14 import read_current_runtime_ranges, load_runtime_range_observation
from alpha.p15 import merged_ranges
from alpha.h02 import write_new_bytes, write_new_json
from alpha.p25 import _binding, _prepare_reference_extension, _capture_prepared_reference_extension, _reference_snapshot, _reference_snapshot_file
from alpha.h02 import read_json, file_identity
from alpha.p28 import load_extension_source


@current_capture_scope
def capture_prepared_with_lifetime(*, binary, output_dir, wine, wineprefix, compiler=None, timeout=1800.0):
    return _capture_prepared_reference_extension(output_dir=output_dir, wine=wine, wineprefix=wineprefix, timeout=timeout)


def _constraint_seed_descriptors(path: Path) -> list[int]:
    from alpha.p28 import (
        RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER,
        RUNTIME_GENERIC_PARAMETER_DETAIL_MAGIC,
        RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD,
        RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION,
    )
    inventory = _owner_file(path, label="generic parameter detail inventory")
    raw = inventory.read_bytes()
    if raw[:1] == b"{":
        model = read_json(inventory)
        record = model.get("inventory") if isinstance(model, dict) else None
        if not isinstance(record, dict) or not isinstance(record.get("path"), str):
            raise AcquisitionError(
                "generic parameter detail model does not name an inventory"
            )
        inventory = _owner_file(
            Path(record["path"]), label="generic parameter detail inventory"
        )
        if file_identity(inventory) != record:
            raise AcquisitionError(
                "generic parameter detail inventory changed since sealing"
            )
        raw = inventory.read_bytes()
    if len(raw) < RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size:
        raise AcquisitionError(
            "generic parameter detail inventory is truncated"
        )
    header = RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.unpack_from(raw)
    argument_count, constraint_count = header[5], header[6]
    constraint_start = (
        RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
        + argument_count * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
    )
    if (
        header[0] != RUNTIME_GENERIC_PARAMETER_DETAIL_MAGIC
        or header[1] != RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION
        or header[2] != RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
        or header[3] != RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
        or header[4] != 0
        or constraint_start + constraint_count * 8 != len(raw)
    ):
        raise AcquisitionError(
            "generic parameter detail inventory layout is invalid"
        )
    constraints = struct.unpack_from(
        f"<{constraint_count}Q", raw, constraint_start
    )
    ordered: list[int] = []
    seen: set[int] = set()
    for descriptor in constraints:
        if descriptor and descriptor not in seen:
            seen.add(descriptor)
            ordered.append(descriptor)
    return ordered


def capture(field_capture, reference_plan, output, wine, wineprefix, *, compiler=None, timeout=1800.0, constraint_seed_model=None):
    field_capture, reference_plan, output = (_safe_path(p) for p in (field_capture, reference_plan, output))
    plan = read_json(reference_plan)
    field_model = read_json(field_capture, maximum_bytes=256 * 1024 * 1024)
    inputs = {"field_capture": file_identity(field_capture), "reference_plan": file_identity(reference_plan)}
    constraint_seed_record = None
    if constraint_seed_model is not None:
        constraint_seed_model = _safe_path(constraint_seed_model)
        constraint_seed_record = file_identity(constraint_seed_model)
        inputs["constraint_seed_model"] = constraint_seed_record
    inputs.update({"reference_" + key: value for key, value in plan["inputs"].items()})
    inputs.update({"field_" + key: value for key, value in field_model["inputs"].items()})
    _verify_files(inputs)
    if any(output.is_relative_to(Path(record["path"]).parent) for record in inputs.values()):
        raise AcquisitionError("field reference extension output must not modify source evidence")
    if output.exists() and (not output.is_dir() or any(output.iterdir())):
        raise AcquisitionError("field reference capture requires an empty stage directory")
    output.mkdir(mode=0o700, parents=True, exist_ok=True)
    binary = Path(plan["target"]["executable_path"])
    probe = RuntimeProcessProbe(binary=binary, wine=wine, wineprefix=wineprefix, compiler=compiler, build_dir=output / "probe")
    identity = probe()
    if identity != field_model.get("identity"): raise AcquisitionError("field reference source process is stale")
    for key, expected in plan["target"].items():
        actual = identity.get("image_base" if key == "image_base_owner_only" else key)
        if type(actual) is not type(expected) or actual != expected: raise AcquisitionError("field reference plan process differs")
    implementation = _implementation_digest()
    drivers = {name: file_identity(Path(__file__).with_name(name)) for name in (Path(__file__).name, "p28.py")}
    for name in drivers:
        write_new_bytes(output / "drivers" / name, Path(drivers[name]["path"]).read_bytes())
        inputs["driver_" + name] = file_identity(output / "drivers" / name)
    source = load_extension_source(field_capture, expected_identity=identity, allow_empty=True, include_nominal=True)
    inputs.update({"replayed_field_" + key: value for key, value in source["source_inputs"].items()})
    constraint_seed_count = 0
    if constraint_seed_model is not None:


        constraint_seeds = _constraint_seed_descriptors(constraint_seed_model)
        merged = list(source["seed_descriptors"])
        known = set(merged)
        for descriptor in constraint_seeds:
            if descriptor not in known:
                known.add(descriptor)
                merged.append(descriptor)
        source["seed_descriptors"] = merged
        constraint_seed_count = len(constraint_seeds)
    def unchanged():
        _verify_files(inputs); _verify_files(drivers)
        if _implementation_digest() != implementation: raise AcquisitionError("field reference extension implementation changed")
    unchanged()
    expected = source["expected_current_bytes"]
    with bind_runtime_process(identity):
        read_current_runtime_ranges(binary=binary, ranges=merged_ranges([(p, len(raw)) for p, raw in expected.items()]),
            output_dir=output / "current-field-bytes", wine=wine, wineprefix=wineprefix, compiler=compiler)
        receipt = output / "current-field-bytes" / "runtime-ranges.private.json"
        view = load_runtime_range_observation(receipt, expected_identity=identity)
        if any(view.read(p, len(raw)) != raw for p, raw in expected.items()):
            raise AcquisitionError("field reference seed bytes changed in the current process")
        inputs["current_field_bytes"] = file_identity(receipt)
        if not source["seed_descriptors"]:
            from alpha.p20 import preserve_observed_reference_domain
            result = preserve_observed_reference_domain(source=source, current_inputs=inputs, output=output / "references")
        else:
            arguments = {}
            for key in inspect.signature(_binding).parameters:
                if key == "binary": arguments[key] = binary
                else: arguments[key] = Path(plan["inputs"]["semantics" if key == "reflection_semantics_model" else key]["path"])
            binding = _binding(**arguments)
            if binding["binary"]["sha256"] != identity["executable_sha256"]:
                raise AcquisitionError("field reference operation binding uses another executable")
            base_model = read_json(Path(source["base_type_reference_model"]["path"]))
            for key in ("semantics", "type_identity_inventory", "type_graph_inventory", "method_detail_inventory", "native_member_detail_inventory"):
                if base_model["inputs"].get(key) != binding.get(key):
                    raise AcquisitionError("field reference base graph belongs to another source domain")
            binding.update({key: source[key] for key in ("seed_descriptors", "base_type_reference_model", "base_type_reference_inventory",
                "base_type_reference_node_count", "base_type_reference_seed_count")})
            binding["field_type_extension"] = True
            binding["native_field_domain_scope"] = source["native_field_domain_scope"]
            binding["additional_evidence_inputs"] = {"field_extension_" + key: value for key, value in inputs.items()}
            unchanged()
            _prepare_reference_extension(binary=binary, binding=binding, output_dir=output / "references", compiler=compiler)
            unchanged()
            print({"capturing_new_field_type_descriptors": len(source["seed_descriptors"]), "constructed_field_count": source["constructed_field_count"]}, flush=True)
            result = capture_prepared_with_lifetime(binary=binary, output_dir=output / "references", wine=wine, wineprefix=wineprefix, compiler=compiler, timeout=timeout)
    unchanged()
    if probe() != identity: raise AcquisitionError("field reference process changed across extension")
    unchanged()
    reference_model = read_json(output / "references" / "runtime-type-reference.private.json")
    _, _, nodes = _reference_snapshot_file(Path(reference_model["inventory"]["path"]), label="field extension result")
    if any(row["descriptor"] not in nodes for row in field_model["nominal_fields"] + field_model["constructed_fields"]):
        raise AcquisitionError("field reference result did not close all observed field types")
    verification = dict(schema="alpha.native-field-type-reference-extension/v1", identity=identity, inputs=inputs,
        implementation=implementation, reference_model=file_identity(output / "references" / "runtime-type-reference.private.json"),
        stage_result=result, new_seed_count=len(source["seed_descriptors"]), constructed_field_count=source["constructed_field_count"],
        merged_reference_count=len(nodes), all_constructed_native_field_types_in_reference_graph=True,
        all_nominal_native_field_types_in_reference_graph=True, nominal_field_count=source["nominal_field_count"],
        native_field_domain_scope=source["native_field_domain_scope"],
        current_native_seed_bytes_reobserved=True, source_order_preserved=True, template_substitution_used_as_observation=False,
        metadata_complete=False, fresh_one_command_success=False)
    verification["status"] = "field-domain-closed" if not source["seed_descriptors"] else "runtime-validated"
    verification["field_reference_fixed_point_observed"] = not source["seed_descriptors"]
    if constraint_seed_model is not None:
        verification["constraint_seed_model"] = constraint_seed_record
        verification["constraint_seed_count"] = constraint_seed_count
    write_new_json(output / "verification.private.json", verification)
    return {key: value for key, value in verification.items() if isinstance(value, (bool, int))} | {
        "status": verification["status"], "native_field_domain_scope": verification["native_field_domain_scope"], "reference_model": verification["reference_model"],
        "reference_inventory": reference_model["inventory"], "verification": file_identity(output / "verification.private.json")
    }


def capture_runtime_field_reference_extension(*, binary, field_type_store_model, reference_capture_plan,
        output_dir, wine, wineprefix, compiler=None, timeout=1800.0, constraint_seed_model=None):

    target = read_json(reference_capture_plan).get("target", {})
    if (str(binary.expanduser().resolve()) != target.get("executable_path")
            or file_identity(binary)["sha256"] != target.get("executable_sha256")):
        raise AcquisitionError("field reference selected executable differs from capture plan")
    return capture(field_type_store_model, reference_capture_plan, output_dir, wine, wineprefix,
                   compiler=compiler, timeout=timeout, constraint_seed_model=constraint_seed_model)


from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.p13 import _safe_path
from alpha.p28 import load_extension_source
from alpha.p20 import bind_original_names, compare_nominal_aliases
from alpha.p19 import _implementation_digest
from alpha.p14 import require_reference_extension
from alpha.c04 import _verify_files
from alpha.c05 import load_reference_names
from alpha.h02 import write_new_json
from alpha.p25 import _reference_snapshot, _reference_snapshot_file
from alpha.h02 import file_identity, read_json


def verify_runtime_nominal_field_aliases(*, binary, field_type_store_model,
                                        type_reference_model, type_reference_inventory, output):
    binary, field_path, reference_path, inventory_path, output = (
        _safe_path(Path(p)) for p in (binary, field_type_store_model,
            type_reference_model, type_reference_inventory, output))
    if output.exists():
        raise AcquisitionError("nominal field alias output already exists")
    selected = dict(binary=file_identity(binary), field_capture=file_identity(field_path),
        reference_model=file_identity(reference_path), reference_inventory=file_identity(inventory_path))
    _verify_files(selected)
    field = read_json(field_path, maximum_bytes=256*1024*1024)
    refs = read_json(reference_path)
    if (field.get("inputs", {}).get("binary") != selected["binary"]
            or refs.get("inventory") != selected["reference_inventory"]
            or refs.get("status") != "runtime-validated" or not refs.get("checks")
            or any(value is not True for value in refs["checks"].values())):
        raise AcquisitionError("nominal field aliases require the selected binary and validated graph")
    implementation = _implementation_digest()


    source = load_extension_source(field_path, expected_identity=field["identity"],
                                   allow_empty=True, include_nominal=True,
                                   model=field, model_identity=selected["field_capture"])
    if refs.get("target") != source["target"]:
        raise AcquisitionError("nominal field alias reference process differs")
    selected.update({"field_"+key: value for key, value in source["source_inputs"].items()})
    raw_identity = dict(source["target"], image_base=source["target"]["image_base_owner_only"])
    proof = refs.get("raw_names")
    original_names = load_reference_names(model=proof, expected_identity=raw_identity,
                                          expected_inventory=refs["inventory"])


    selected["raw_name_inventory"] = proof["inventory"]
    for index, capture in enumerate(proof["captures"]):
        for key, record in dict(capture["inputs"], observation=capture["observation"],
                               display=capture["display"], string_io=capture["string_io"]).items():
            selected[f"raw_name_{index}_{key}"] = record
    if any(output.is_relative_to(Path(record["path"]).parent) for record in selected.values()):
        raise AcquisitionError("nominal field alias output must preserve all source evidence")
    _, order, nodes = _reference_snapshot_file(inventory_path, label="nominal aliases")
    raw_names = bind_original_names(order, original_names)
    del original_names
    _, _, base = _reference_snapshot_file(Path(source["base_type_reference_inventory"]["path"]),
                                     label="nominal alias source")
    require_reference_extension(base, nodes)
    del base, source["expected_current_bytes"]
    result = compare_nominal_aliases(field["nominal_fields"], nodes, raw_names=raw_names)
    _verify_files(selected)
    if _implementation_digest() != implementation:
        raise AcquisitionError("nominal field alias verification source changed")
    result.update(schema="alpha.runtime-nominal-field-aliases/v1", inputs=selected,
        identity=field["identity"], implementation=implementation, all_native_source_bytes_replayed=True,
        fresh_process_observation_performed=False, fresh_one_command_success=False,
        status="observed-aliases-agree" if result["all_nominal_field_aliases_agree"] else "unresolved")
    write_new_json(output, result)
    if not result["all_nominal_field_aliases_agree"]:
        raise AcquisitionError("nominal field alias equality remains unproven; diagnostic receipt preserved")
    return {key: value for key, value in result.items() if isinstance(value, (bool, int))} | {
        "status": result["status"], "model": file_identity(output)}
