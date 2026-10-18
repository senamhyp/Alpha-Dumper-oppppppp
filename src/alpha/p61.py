import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any, Iterable

from alpha.h01 import AcquisitionError, ContractViolation
from alpha.h03 import EXPECTED_PROTO_BANNER, inspect_standard_output
from alpha.p01 import reflection_contract
from alpha.h02 import atomic_write_json, file_identity, sha256_file


DUMP_IR_SCHEMA = "alpha.il2cpp-dump-ir/v1"
DUMP_OUTPUT_SCHEMA = "alpha.il2cpp-standard-output/v1"
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _required_string(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not value or any(ord(char) < 0x20 for char in value):
        raise ContractViolation(f"dump IR {label} is invalid")
    return value


def _nonnegative_integer(value: Any, *, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise ContractViolation(f"dump IR {label} is invalid")
    return value


def _member_list(value: Any, *, label: str) -> list[dict[str, Any]]:
    if not isinstance(value, list) or any(not isinstance(item, dict) for item in value):
        raise ContractViolation(f"dump IR {label} must be a list of objects")
    return value


def _optional_nonnegative_integer(value: Any, *, label: str) -> int | None:
    if value is None:
        return None
    return _nonnegative_integer(value, label=label)


def _optional_member_id(value: Any, *, label: str) -> str | None:
    if value is None:
        return None
    return _required_string(value, label=label)


def _generic_parameters(value: Any, *, label: str) -> list[dict[str, Any]]:
    parameters = _member_list(value, label=label)
    for parameter in parameters:


        _required_string(parameter.get("name"), label=f"{label} name")
        _nonnegative_integer(
            parameter.get("attributes", 0), label=f"{label} attributes"
        )
        constraints = parameter.get("constraints", [])
        if not isinstance(constraints, list):
            raise ContractViolation(f"dump IR {label} constraints are invalid")
        for constraint in constraints:
            _required_string(constraint, label=f"{label} constraint")
    return parameters


def validate_dump_ir(payload: dict[str, Any]) -> dict[str, int]:
    contract = reflection_contract()
    if payload.get("schema") != DUMP_IR_SCHEMA or payload.get("status") != "complete":
        raise ContractViolation("dump IR schema or status is invalid")
    target = payload.get("target")
    reflection = payload.get("reflection")
    if not isinstance(target, dict) or not isinstance(reflection, dict):
        raise ContractViolation("dump IR bindings are unavailable")
    executable_sha256 = target.get("executable_sha256")
    if not isinstance(executable_sha256, str) or not _SHA256.fullmatch(
        executable_sha256
    ):
        raise ContractViolation("dump IR executable binding is invalid")
    if (
        reflection.get("contract_id") != contract["contract_id"]
        or reflection.get("operation_count") != contract["operation_count"]
        or reflection.get("all_operations_uniquely_resolved") is not True
        or reflection.get("fresh_runtime_observation") is not True
    ):
        raise ContractViolation("dump IR reflection contract is incomplete")
    images = payload.get("images")
    types = payload.get("types")
    strings = payload.get("string_literals", [])
    if (
        not isinstance(images, list)
        or not images
        or any(not isinstance(item, dict) for item in images)
        or not isinstance(types, list)
        or not types
        or any(not isinstance(item, dict) for item in types)
        or not isinstance(strings, list)
        or any(not isinstance(item, dict) for item in strings)
    ):
        raise ContractViolation("dump IR inventories are invalid")

    image_ids: set[str] = set()
    for image in images:
        image_id = _required_string(image.get("id"), label="image id")
        _required_string(image.get("name"), label="image name")
        if image_id in image_ids:
            raise ContractViolation("dump IR image ids are not unique")
        image_ids.add(image_id)
        for key in ("assembly_name", "version", "culture"):
            if image.get(key) is not None:
                _required_string(image[key], label=f"image {key}")
        _nonnegative_integer(image.get("attributes", 0), label="image attributes")

    type_ids: set[str] = set()
    types_by_id: dict[str, dict[str, Any]] = {}
    totals = {
        "image_count": len(images),
        "type_count": len(types),
        "field_count": 0,
        "property_count": 0,
        "method_count": 0,
        "event_count": 0,
        "string_literal_count": len(strings),
    }
    method_rvas: set[int] = set()
    for index, type_record in enumerate(types):
        type_id = _required_string(type_record.get("id"), label="type id")
        if type_id in type_ids:
            raise ContractViolation("dump IR type ids are not unique")
        type_ids.add(type_id)
        types_by_id[type_id] = type_record
        if type_record.get("image_id") not in image_ids:
            raise ContractViolation("dump IR type image reference is invalid")
        _required_string(type_record.get("name"), label="type name")
        namespace = type_record.get("namespace", "")
        if not isinstance(namespace, str) or any(ord(char) < 0x20 for char in namespace):
            raise ContractViolation("dump IR type namespace is invalid")
        if type_record.get("type_definition_index") != index:
            raise ContractViolation("dump IR type definition indexes are not contiguous")
        _nonnegative_integer(type_record.get("attributes", 0), label="type attributes")
        _optional_nonnegative_integer(type_record.get("token"), label="type token")
        if type_record.get("base_type") is not None:
            _required_string(type_record["base_type"], label="type base type")
        interfaces = type_record.get("interfaces", [])
        if not isinstance(interfaces, list):
            raise ContractViolation("dump IR type interfaces are invalid")
        for interface in interfaces:
            _required_string(interface, label="type interface")
        declaring_type_id = type_record.get("declaring_type_id")
        if declaring_type_id is not None:
            _required_string(declaring_type_id, label="declaring type id")
        for key in ("is_enum", "is_value_type", "is_interface"):
            if key in type_record and not isinstance(type_record[key], bool):
                raise ContractViolation(f"dump IR {key} is invalid")
        for key in ("script_c_type", "script_metadata_signature"):
            if type_record.get(key) is not None:
                _required_string(type_record[key], label=f"type {key}")
        _optional_nonnegative_integer(
            type_record.get("metadata_rva"), label="type metadata RVA"
        )
        _optional_nonnegative_integer(
            type_record.get("metadata_offset"), label="type metadata offset"
        )
        _generic_parameters(
            type_record.get("generic_parameters", []),
            label="type generic parameters",
        )
        fields = _member_list(type_record.get("fields", []), label="fields")
        properties = _member_list(
            type_record.get("properties", []), label="properties"
        )
        methods = _member_list(type_record.get("methods", []), label="methods")
        events = _member_list(type_record.get("events", []), label="events")
        totals["field_count"] += len(fields)
        totals["property_count"] += len(properties)
        totals["method_count"] += len(methods)
        totals["event_count"] += len(events)
        field_ids: set[str] = set()
        for field in fields:
            field_id = _optional_member_id(field.get("id"), label="field id")
            if field_id is not None and field_id in field_ids:
                raise ContractViolation("dump IR field ids are not unique per type")
            if field_id is not None:
                field_ids.add(field_id)
            _required_string(field.get("name"), label="field name")
            _required_string(field.get("type"), label="field type")
            _nonnegative_integer(field.get("attributes", 0), label="field attributes")
            _optional_nonnegative_integer(field.get("token"), label="field token")
            _optional_nonnegative_integer(field.get("offset"), label="field offset")
            _optional_nonnegative_integer(
                field.get("metadata_offset"), label="field metadata offset"
            )
        property_ids: set[str] = set()
        for property_record in properties:
            property_id = _optional_member_id(
                property_record.get("id"), label="property id"
            )
            if property_id is not None and property_id in property_ids:
                raise ContractViolation("dump IR property ids are not unique per type")
            if property_id is not None:
                property_ids.add(property_id)
            _required_string(property_record.get("name"), label="property name")
            _required_string(property_record.get("type"), label="property type")
            _nonnegative_integer(
                property_record.get("attributes", 0), label="property attributes"
            )
            _optional_nonnegative_integer(
                property_record.get("token"), label="property token"
            )
            _optional_nonnegative_integer(
                property_record.get("metadata_offset"),
                label="property metadata offset",
            )
            for key in ("has_getter", "has_setter"):
                if key in property_record and not isinstance(property_record[key], bool):
                    raise ContractViolation(f"dump IR property {key} is invalid")
            for key in ("getter_method_id", "setter_method_id"):
                _optional_member_id(
                    property_record.get(key), label=f"property {key}"
                )
        event_ids: set[str] = set()
        for event in events:
            event_id = _optional_member_id(event.get("id"), label="event id")
            if event_id is not None and event_id in event_ids:
                raise ContractViolation("dump IR event ids are not unique per type")
            if event_id is not None:
                event_ids.add(event_id)
            _required_string(event.get("name"), label="event name")
            _required_string(event.get("type"), label="event type")
            _nonnegative_integer(event.get("attributes", 0), label="event attributes")
            _optional_nonnegative_integer(event.get("token"), label="event token")
            _optional_nonnegative_integer(
                event.get("metadata_offset"), label="event metadata offset"
            )
            for key in ("add_method_id", "remove_method_id", "raise_method_id"):
                _optional_member_id(event.get(key), label=f"event {key}")
        method_keys: set[tuple[str, str, int, tuple[str, ...]]] = set()
        method_ids: set[str] = set()
        for method in methods:
            method_id = _optional_member_id(method.get("id"), label="method id")
            if method_id is not None and method_id in method_ids:
                raise ContractViolation("dump IR method ids are not unique per type")
            if method_id is not None:
                method_ids.add(method_id)
            method_name = _required_string(method.get("name"), label="method name")
            return_type = _required_string(
                method.get("return_type"), label="method return type"
            )
            parameters = _member_list(method.get("parameters", []), label="parameters")
            parameter_types: list[str] = []
            parameter_ids: set[str] = set()
            for parameter in parameters:
                parameter_id = _optional_member_id(
                    parameter.get("id"), label="parameter id"
                )
                if parameter_id is not None and parameter_id in parameter_ids:
                    raise ContractViolation(
                        "dump IR parameter ids are not unique per method"
                    )
                if parameter_id is not None:
                    parameter_ids.add(parameter_id)
                _required_string(parameter.get("name"), label="parameter name")
                parameter_types.append(
                    _required_string(parameter.get("type"), label="parameter type")
                )
                _nonnegative_integer(
                    parameter.get("attributes", 0), label="parameter attributes"
                )
                _optional_nonnegative_integer(
                    parameter.get("token"), label="parameter token"
                )
                _optional_nonnegative_integer(
                    parameter.get("metadata_offset"),
                    label="parameter metadata offset",
                )
                if parameter.get("script_c_type") is not None:
                    _required_string(
                        parameter["script_c_type"], label="parameter script C type"
                    )
                if parameter.get("type_code") is not None:
                    type_code = _required_string(
                        parameter["type_code"], label="parameter script type code"
                    )
                    if not re.fullmatch(r"[ifdj]", type_code):
                        raise ContractViolation(
                            "dump IR parameter script type code is invalid"
                        )
            _nonnegative_integer(method.get("attributes", 0), label="method attributes")
            _nonnegative_integer(
                method.get("impl_attributes", 0), label="method implementation attributes"
            )
            _optional_nonnegative_integer(method.get("token"), label="method token")
            rva = _nonnegative_integer(method.get("rva", 0), label="method RVA")
            _optional_nonnegative_integer(method.get("offset"), label="method offset")
            _optional_nonnegative_integer(method.get("va"), label="method VA")
            _optional_nonnegative_integer(method.get("slot"), label="method slot")
            _optional_nonnegative_integer(
                method.get("metadata_offset"), label="method metadata offset"
            )
            generic_parameters = _generic_parameters(
                method.get("generic_parameters", []),
                label="method generic parameters",
            )


            signature = (
                method_name,
                return_type,
                len(generic_parameters),
                tuple(parameter_types),
            )
            if signature in method_keys:
                raise ContractViolation(
                    "dump IR CLR method signatures are not unique per type"
                )
            method_keys.add(signature)
            if "is_static" in method and not isinstance(method["is_static"], bool):
                raise ContractViolation("dump IR method static flag is invalid")
            if method.get("script_signature") is not None:
                _required_string(
                    method["script_signature"], label="method script signature"
                )
            if method.get("return_script_c_type") is not None:
                _required_string(
                    method["return_script_c_type"],
                    label="method return script C type",
                )
            if method.get("return_type_code") is not None:
                return_type_code = _required_string(
                    method["return_type_code"],
                    label="method return script type code",
                )
                if not re.fullmatch(r"[vifdj]", return_type_code):
                    raise ContractViolation(
                        "dump IR method return script type code is invalid"
                    )
            if "metadata_method" in method and not isinstance(
                method["metadata_method"], bool
            ):
                raise ContractViolation("dump IR metadata method flag is invalid")
            _optional_nonnegative_integer(
                method.get("metadata_rva"), label="method metadata RVA"
            )
            if method.get("metadata_method_name") is not None:
                _required_string(
                    method["metadata_method_name"],
                    label="method metadata method name",
                )
            if method.get("type_signature") is not None:
                type_signature = _required_string(
                    method["type_signature"], label="method type signature"
                )
                expected_type_count = (
                    1
                    + (0 if method.get("is_static") else 1)
                    + len(parameters)
                    + 1
                )
                if (
                    not re.fullmatch(r"[vifdj]+", type_signature)
                    or len(type_signature) != expected_type_count
                ):
                    raise ContractViolation(
                        "dump IR method type signature does not match its ABI"
                    )
            if rva:
                method_rvas.add(rva)
        for property_record in properties:
            for key in ("getter_method_id", "setter_method_id"):
                accessor_id = property_record.get(key)
                if accessor_id is not None and accessor_id not in method_ids:
                    raise ContractViolation(
                        "dump IR property accessor does not reference a method id"
                    )
        for event in events:
            for key in ("add_method_id", "remove_method_id", "raise_method_id"):
                accessor_id = event.get(key)
                if accessor_id is not None and accessor_id not in method_ids:
                    raise ContractViolation(
                        "dump IR event accessor does not reference a method id"
                    )

    for type_record in types:
        declaring_type_id = type_record.get("declaring_type_id")
        if declaring_type_id is None:
            continue
        declaring = types_by_id.get(declaring_type_id)
        if (
            declaring is None
            or declaring is type_record
            or declaring.get("image_id") != type_record.get("image_id")
        ):
            raise ContractViolation("dump IR nested type owner is invalid")
        visited = {type_record["id"]}
        current = declaring
        while current.get("declaring_type_id") is not None:
            owner_id = current["declaring_type_id"]
            if owner_id in visited:
                raise ContractViolation("dump IR nested type ownership is cyclic")
            visited.add(owner_id)
            current = types_by_id.get(owner_id)
            if current is None:
                raise ContractViolation("dump IR nested type owner is invalid")

    string_rvas: set[int] = set()
    for literal in strings:
        rva = _nonnegative_integer(literal.get("rva"), label="string literal RVA")
        _required_string(literal.get("value"), label="string literal value")
        if not rva or rva in string_rvas:
            raise ContractViolation("dump IR string literal RVAs are not unique")
        string_rvas.add(rva)

    metadata_type_usages = payload.get("metadata_type_usages", [])
    if not isinstance(metadata_type_usages, list) or any(
        not isinstance(record, dict) for record in metadata_type_usages
    ):
        raise ContractViolation("dump IR metadata type usages are invalid")
    metadata_type_rvas: set[int] = set()
    for record in metadata_type_usages:
        rva = _nonnegative_integer(
            record.get("rva"), label="metadata type usage RVA"
        )
        if not rva or rva in metadata_type_rvas:
            raise ContractViolation(
                "dump IR metadata type usage RVAs are not unique"
            )
        metadata_type_rvas.add(rva)
        _required_string(record.get("name"), label="metadata type usage name")
        _nonnegative_integer(
            record.get("destination_index"),
            label="metadata type usage destination index",
        )
        _nonnegative_integer(
            record.get("source_index"),
            label="metadata type usage source index",
        )
        _optional_nonnegative_integer(
            record.get("node_index"), label="metadata type usage node index"
        )
        if record.get("signature") is not None:
            _required_string(
                record["signature"], label="metadata type usage signature"
            )

    counts = payload.get("counts")
    if not isinstance(counts, dict) or any(counts.get(key) != value for key, value in totals.items()):
        raise ContractViolation("dump IR declared counts do not match inventories")
    totals["unique_method_rva_count"] = len(method_rvas)
    return totals


def _atomic_text(path: Path, value: str) -> None:
    path = path.expanduser().resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as sink:
            sink.write(value)
            sink.flush()
            os.fsync(sink.fileno())
        os.replace(temporary_path, path)
    finally:
        temporary_path.unlink(missing_ok=True)


def _visibility(attributes: int, *, field: bool = False) -> str:
    access = attributes & 0x7
    if field:
        return {
            1: "private",
            2: "private protected",
            3: "internal",
            4: "protected",
            5: "protected internal",
            6: "public",
        }.get(access, "private")
    return {
        1: "private",
        2: "private protected",
        3: "internal",
        4: "protected",
        5: "protected internal",
        6: "public",
    }.get(access, "private")


def _type_declaration(record: dict[str, Any]) -> str:
    attributes = record.get("attributes", 0)
    visibility = "public" if attributes & 0x7 in {1, 2} else "internal"
    kind = "enum" if record.get("is_enum") else "struct" if record.get("is_value_type") else "interface" if record.get("is_interface") else "class"
    inheritance: list[str] = []
    if isinstance(record.get("base_type"), str) and record["base_type"]:
        inheritance.append(record["base_type"])
    inheritance.extend(
        value
        for value in record.get("interfaces", [])
        if isinstance(value, str) and value
    )
    suffix = f" : {', '.join(inheritance)}" if inheritance else ""
    return f"{visibility} {kind} {record['name']}{suffix}"


def render_dump_cs(payload: dict[str, Any]) -> str:
    validate_dump_ir(payload)
    lines = [EXPECTED_PROTO_BANNER, ""]
    types_by_image: dict[str, list[dict[str, Any]]] = {
        image["id"]: [] for image in payload["images"]
    }
    for type_record in payload["types"]:
        types_by_image[type_record["image_id"]].append(type_record)
    for image_index, image in enumerate(payload["images"]):
        lines.extend([f"// Image {image_index}: {image['name']} - {image_index}", ""])
        for type_record in types_by_image[image["id"]]:
            lines.append(f"// Namespace: {type_record.get('namespace', '')}")
            lines.append(
                f"{_type_declaration(type_record)} // TypeDefIndex: "
                f"{type_record['type_definition_index']}"
            )
            lines.append("{")
            fields = type_record.get("fields", [])
            if fields:
                lines.append("\t// Fields")
                for field in fields:
                    static = " static" if field.get("is_static") else ""
                    field_offset = field.get("offset")
                    if not isinstance(field_offset, int):
                        field_offset = 0
                    lines.append(
                        f"\t{_visibility(field.get('attributes', 0), field=True)}"
                        f"{static} {field['type']} {field['name']}; // 0x{field_offset:X}"
                    )
                lines.append("")
            properties = type_record.get("properties", [])
            if properties:
                lines.append("\t// Properties")
                for property_record in properties:
                    accessors = []
                    if property_record.get("has_getter", True):
                        accessors.append("get;")
                    if property_record.get("has_setter", False):
                        accessors.append("set;")
                    lines.append(
                        f"\tpublic {property_record['type']} "
                        f"{property_record['name']} {{ {' '.join(accessors)} }}"
                    )
                lines.append("")
            methods = type_record.get("methods", [])
            if methods:
                lines.append("\t// Methods")
                for method in methods:
                    rva = method.get("rva", 0)
                    offset = method.get("offset", rva)
                    va = method.get("va", rva)
                    slot = method.get("slot")
                    slot_suffix = (
                        f" Slot: {slot}" if isinstance(slot, int) else ""
                    )
                    lines.append(
                        f"\t// RVA: 0x{rva:X} Offset: 0x{offset:X} "
                        f"VA: 0x{va:X}{slot_suffix}"
                    )
                    parameters = ", ".join(
                        f"{parameter['type']} {parameter['name']}"
                        for parameter in method.get("parameters", [])
                    )
                    static = " static" if method.get("is_static") else ""
                    lines.append(
                        f"\t{_visibility(method.get('attributes', 0))}{static} "
                        f"{method['return_type']} {method['name']}({parameters}) {{ }}"
                    )
                    lines.append("")
            lines.append("}")
            lines.append("")
    return "\n".join(lines)


def _qualified_type(record: dict[str, Any]) -> str:
    namespace = record.get("namespace", "")
    return f"{namespace}.{record['name']}" if namespace else record["name"]


def _script_fix_name(value: str) -> str:
    fixed = re.sub(r"[^a-zA-Z0-9_]", "_", value)
    return f"_{fixed}" if fixed and fixed[0].isdigit() else fixed


_SCRIPT_PRIMITIVE_C_TYPES = {
    "System.Void": "void",
    "System.Boolean": "bool",
    "System.Char": "uint16_t",
    "System.SByte": "int8_t",
    "System.Byte": "uint8_t",
    "System.Int16": "int16_t",
    "System.UInt16": "uint16_t",
    "System.Int32": "int32_t",
    "System.UInt32": "uint32_t",
    "System.Int64": "int64_t",
    "System.UInt64": "uint64_t",
    "System.Single": "float",
    "System.Double": "double",
    "System.IntPtr": "intptr_t",
    "System.UIntPtr": "uintptr_t",
    "System.String": "System_String_o*",
    "System.Object": "Il2CppObject*",
}


def _script_c_type(type_name: str, explicit: Any = None) -> str:
    if explicit is not None:
        return _required_string(explicit, label="script C type")
    byref = type_name.endswith("&")
    pointer = type_name.endswith("*")
    base = type_name[:-1] if byref or pointer else type_name
    if base.endswith("[]"):
        value = f"{_script_fix_name(base[:-2])}_array*"
    else:
        value = _SCRIPT_PRIMITIVE_C_TYPES.get(base)
        if value is None:
            value = f"{_script_fix_name(base)}_o*"
    return f"{value}*" if byref or pointer else value


def _script_type_code(type_name: str, explicit: Any = None) -> str:
    if explicit is not None:
        code = _required_string(explicit, label="script type code")
        if not re.fullmatch(r"[vifdj]", code):
            raise ContractViolation("dump IR script type code is invalid")
        return code
    if type_name.endswith(("&", "*")):
        return "i"
    return {
        "System.Void": "v",
        "System.Boolean": "i",
        "System.Char": "i",
        "System.SByte": "i",
        "System.Byte": "i",
        "System.Int16": "i",
        "System.UInt16": "i",
        "System.Int32": "i",
        "System.UInt32": "i",
        "System.Int64": "j",
        "System.UInt64": "j",
        "System.Single": "f",
        "System.Double": "d",
    }.get(type_name, "i")


def _script_method_contract(
    type_record: dict[str, Any], method: dict[str, Any]
) -> tuple[str, str]:
    qualified = _qualified_type(type_record)
    full_name = f"{qualified}$${method['name']}"
    parameters: list[str] = []
    type_codes = [
        _script_type_code(
            method["return_type"], method.get("return_type_code")
        )
    ]
    if not method.get("is_static"):
        declaring_c_type = type_record.get("script_c_type")
        if declaring_c_type is None:
            suffix = "_o" if type_record.get("is_value_type") else "_o*"
            declaring_c_type = f"{_script_fix_name(qualified)}{suffix}"
        parameters.append(f"{declaring_c_type} __this")
        type_codes.append("i")
    for parameter in method.get("parameters", []):
        parameters.append(
            f"{_script_c_type(parameter['type'], parameter.get('script_c_type'))} "
            f"{_script_fix_name(parameter['name'])}"
        )
        type_codes.append(
            _script_type_code(parameter["type"], parameter.get("type_code"))
        )
    parameters.append("const MethodInfo* method")
    type_codes.append("i")
    signature = method.get("script_signature")
    if signature is None:
        signature = (
            f"{_script_c_type(method['return_type'], method.get('return_script_c_type'))} "
            f"{_script_fix_name(full_name)} ({', '.join(parameters)});"
        )
    type_signature = method.get("type_signature") or "".join(type_codes)
    return signature, type_signature


def build_script_json(payload: dict[str, Any]) -> dict[str, Any]:
    validate_dump_ir(payload)
    script_methods: list[dict[str, Any]] = []
    addresses: set[int] = set()
    metadata_methods: list[dict[str, Any]] = []
    metadata: list[dict[str, Any]] = []
    metadata_type_usages = payload.get("metadata_type_usages")
    if metadata_type_usages:
        for type_usage in metadata_type_usages:
            qualified = type_usage["name"]
            metadata.append(
                {
                    "Address": type_usage["rva"],
                    "Name": f"{qualified}_TypeInfo",
                    "Signature": type_usage.get(
                        "signature", f"{_script_fix_name(qualified)}_c*"
                    ),
                }
            )
    for type_record in payload["types"]:
        qualified = _qualified_type(type_record)
        metadata_rva = type_record.get("metadata_rva", 0)
        if metadata_rva and not metadata_type_usages:
            metadata.append(
                {
                    "Address": metadata_rva,
                    "Name": f"{qualified}_TypeInfo",
                    "Signature": type_record.get(
                        "script_metadata_signature",
                        f"{_script_fix_name(qualified)}_c*",
                    ),
                }
            )
        for method in type_record.get("methods", []):
            rva = method.get("rva", 0)
            signature, type_signature = _script_method_contract(
                type_record, method
            )
            script_methods.append(
                {
                    "Address": rva,
                    "Name": f"{qualified}$${method['name']}",
                    "Signature": signature,
                    "TypeSignature": type_signature,
                }
            )
            if rva:
                addresses.add(rva)
            if method.get("metadata_method"):
                metadata_methods.append(
                    {
                        "Address": method.get("metadata_rva", rva),
                        "Name": method.get(
                            "metadata_method_name",
                            f"Method${qualified}.{method['name']}()",
                        ),
                        "MethodAddress": rva,
                    }
                )
    return {
        "ScriptMethod": script_methods,
        "ScriptString": [
            {"Address": literal["rva"], "Value": literal["value"]}
            for literal in payload.get("string_literals", [])
        ],
        "ScriptMetadata": metadata,
        "ScriptMetadataMethod": metadata_methods,
        "Addresses": sorted(addresses),
    }


def render_il2cpp_h(payload: dict[str, Any]) -> str:
    validate_dump_ir(payload)
    lines = [
        f"// {EXPECTED_PROTO_BANNER.removeprefix('// ')}",
        "#pragma once",
        "#include <stdint.h>",
        "",
    ]
    for record in payload["types"]:
        qualified = _qualified_type(record).replace(".", "_").replace("`", "_")
        lines.append(f"typedef struct {qualified} {qualified};")
    lines.append("")
    return "\n".join(lines)


def render_standard_output(
    payload: dict[str, Any],
    *,
    current_executable: Path,
    output_dir: Path,
) -> dict[str, Any]:
    totals = validate_dump_ir(payload)
    current_executable = current_executable.expanduser().resolve()
    if (
        not current_executable.is_file()
        or sha256_file(current_executable) != payload["target"]["executable_sha256"]
    ):
        raise AcquisitionError("dump IR target binding is stale")
    output_dir = output_dir.expanduser().resolve()
    if output_dir.exists() and (output_dir.is_symlink() or not output_dir.is_dir()):
        raise AcquisitionError("standard dump output boundary is invalid")
    output_dir.mkdir(parents=True, exist_ok=True)
    _atomic_text(output_dir / "dump.cs", render_dump_cs(payload))
    atomic_write_json(output_dir / "script.json", build_script_json(payload))
    _atomic_text(output_dir / "il2cpp.h", render_il2cpp_h(payload))
    atomic_write_json(
        output_dir / "stringliteral.json",
        [
            {"address": literal["rva"], "value": literal["value"]}
            for literal in payload.get("string_literals", [])
        ],
    )
    from alpha.p62 import build_synthetic_gameassembly

    synthetic_assembly = build_synthetic_gameassembly(
        payload,
        output=output_dir / "GameAssembly.dll",
    )
    from alpha.dummy_dll import build_dummy_dlls

    dummy_dll = build_dummy_dlls(
        payload,
        output_dir=output_dir / "DummyDll",
    )
    measured = inspect_standard_output(output_dir)
    receipt = {
        "schema": DUMP_OUTPUT_SCHEMA,
        "status": "complete",
        "target": payload["target"],
        "reflection": payload["reflection"],
        "counts": totals,
        "artifacts": {
            "standard": measured,
            "GameAssembly.dll": synthetic_assembly,
            "DummyDll": dummy_dll,
        },
        "checks": {
            "target_binding_matches": True,
            "reflection_contract_complete": True,
            "dump_type_count_matches_ir": measured["dump_counts"][
                "type_definition_count"
            ]
            == totals["type_count"],
            "dump_method_count_matches_ir": measured["dump_counts"][
                "method_rva_count"
            ]
            == totals["method_count"],
            "script_method_count_matches_ir": measured["script_counts"].get(
                "ScriptMethod"
            )
            == totals["method_count"],
            "string_literal_count_matches_ir": measured["script_counts"].get(
                "ScriptString"
            )
            == totals["string_literal_count"],
            "synthetic_gameassembly_matches_ir": synthetic_assembly["counts"]
            == totals,
            "synthetic_gameassembly_is_valid_pe32_plus": synthetic_assembly[
                "valid_pe32_plus"
            ]
            is True,
            "dummy_dll_count_matches_images_plus_helper": measured[
                "dummy_dll_count"
            ]
            == totals["image_count"] + 1,
            "dummy_dll_inventory_matches_ir": dummy_dll["counts"]
            == {
                "type_count": totals["type_count"],
                "field_count": totals["field_count"],
                "property_count": totals["property_count"],
                "method_count": totals["method_count"],
                "event_count": totals["event_count"],
                "image_count": totals["image_count"],
            },
            "dummy_dll_managed_metadata_valid": all(
                dummy_dll["checks"].values()
            ),
            "external_runtime_component_absent": True,
            "saved_reference_generation_seed_absent": True,
        },
        "source_ir": payload.get("identity"),
        "current_executable": file_identity(current_executable),
    }
    if not all(receipt["checks"].values()):
        raise AcquisitionError("standard dump output does not match its runtime IR")
    atomic_write_json(output_dir / "alpha-output-receipt.json", receipt)
    return receipt
