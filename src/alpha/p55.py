import os
import struct
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

from alpha.h01 import AcquisitionError, ContractViolation
from alpha.p44 import load_runtime_enum_constants
from alpha.p46 import (
    load_runtime_assembly_identities,
)
from alpha.p54 import (
    load_runtime_parameter_defaults,
)
from alpha.p24 import (
    RUNTIME_EVENT_MODULE_EVENT,
)
from alpha.p28 import (
    RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER,
    RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD,
)
from alpha.p56 import (
    METADATA_MAGIC,
    _V24_2_TABLES,
    parse_global_metadata,
)
from alpha.p04 import (
    METHOD_DETAIL_CONSTRUCTOR,
)
from alpha.p26 import (
    RUNTIME_METHOD_GENERIC_HEADER,
    RUNTIME_METHOD_GENERIC_RECORD,
)
from alpha.p23 import (
    RUNTIME_NATIVE_MEMBER_DETAIL_FIELD,
    RUNTIME_NATIVE_MEMBER_DETAIL_HEADER,
    RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY,
)
from alpha.p33 import (
    _MetadataUsageTypeRenderer,
    _RuntimeOutput,
    _TypeRenderer,
    _text,
)
from alpha.p29 import _runtime
from alpha.c04 import MappedPE
from alpha.p20 import (
    load_runtime_metadata_usage_member_inventory,
    load_runtime_metadata_usage_pair_inventory,
    load_runtime_metadata_usage_value_inventory,
    load_runtime_string_literal_inventory,
)
from alpha.p39 import (
    load_runtime_type_descriptor_values,
)
from alpha.p25 import (
    RUNTIME_TYPE_REFERENCE_HEADER,
    RUNTIME_TYPE_REFERENCE_MAGIC,
    RUNTIME_TYPE_REFERENCE_RECORD,
    RUNTIME_TYPE_REFERENCE_SCHEMA,
    RUNTIME_TYPE_REFERENCE_VERSION,
    TYPE_REFERENCE_GENERIC_PARAMETER,
)
from alpha.h02 import atomic_write_json, file_identity, read_json


RUNTIME_GLOBAL_METADATA_RECONSTRUCTION_SCHEMA = (
    "alpha.runtime-global-metadata-reconstruction/v1"
)


_STRING_LITERAL = struct.Struct("<Ii")
_EVENT = struct.Struct("<IiiiiI")
_PROPERTY = struct.Struct("<IiiII")
_METHOD = struct.Struct("<IiiiiIHHHH")
_DEFAULT = struct.Struct("<iii")
_PARAMETER = struct.Struct("<IIi")
_FIELD = struct.Struct("<IiI")
_GENERIC_PARAMETER = struct.Struct("<iIhhHH")
_GENERIC_CONTAINER = struct.Struct("<iiii")
_INTERFACE_OFFSET = struct.Struct("<ii")
_TYPE_DEFINITION = struct.Struct("<IIiiiiiiIiiiiiiiiHHHHHHHHII")
_IMAGE = struct.Struct("<IiiIiIiIiI")
_ASSEMBLY = struct.Struct("<iIiiIIIIiIiiii8s")
_METADATA_USAGE_LIST = struct.Struct("<II")
_METADATA_USAGE_PAIR = struct.Struct("<II")
_FIELD_REF = struct.Struct("<ii")
_CUSTOM_ATTRIBUTE_RANGE = struct.Struct("<Iii")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or path.stat().st_uid != os.getuid()
        or path.stat().st_mode & 0o077
    ):
        raise AcquisitionError(
            f"runtime global metadata {label} is not owner-only"
        )
    return path


def _write_bytes(path: Path, value: bytes) -> None:
    from alpha.h02 import write_new_bytes
    write_new_bytes(path, value)


class _StringHeap:
    def __init__(self) -> None:

        self.data = bytearray(b"\0")
        self.index: dict[str, int] = {"": 0}

    def add(self, value: str) -> int:
        previous = self.index.get(value)
        if previous is not None:
            return previous
        encoded = value.encode("utf-8", errors="surrogatepass")
        if b"\0" in encoded:
            raise ContractViolation("metadata string contains an embedded NUL")
        offset = len(self.data)
        self.data.extend(encoded)
        self.data.append(0)
        self.index[value] = offset
        return offset

    def add_blob(self, value: bytes) -> int:
        if not value:
            return 0
        offset = len(self.data)
        self.data.extend(value)
        return offset


def _append_generic_parameter_record(metadata, strings, descriptor_indexes, *, descriptor,
        container_index, number, name, constraint_start, constraint_count, attributes):
    if descriptor in descriptor_indexes:
        raise ContractViolation("generic descriptor repeats across parameter positions; contextual owner proof is required")
    container_count = len(metadata.tables["generic_containers"]) // _GENERIC_CONTAINER.size
    if (type(container_index) is not int or not 0 <= container_index < container_count or
        type(number) is not int or not 0 <= number <= 65535 or
        type(constraint_count) is not int or not 0 <= constraint_count <= 32767 or
        type(constraint_start) is not int or not -1 <= constraint_start <= 32767 or
        (constraint_start == -1) != (constraint_count == 0) or
        type(attributes) is not int or not 0 <= attributes <= 31):
        raise ContractViolation("generic parameter owner, position or selected-format range is invalid")
    container = _GENERIC_CONTAINER.unpack_from(metadata.tables["generic_containers"], container_index * _GENERIC_CONTAINER.size)
    index = len(metadata.tables["generic_parameters"]) // _GENERIC_PARAMETER.size
    if number >= container[1] or index != container[3] + number:
        raise ContractViolation("generic parameter container range is not contiguous")
    index = metadata.append("generic_parameters", _GENERIC_PARAMETER,
        container_index, strings.add(name), constraint_start, constraint_count, number, attributes)
    descriptor_indexes[descriptor] = index
    return index


def _validate_generic_table_ownership(metadata):
    parameters = metadata.tables["generic_parameters"]
    containers = metadata.tables["generic_containers"]
    if len(parameters) % _GENERIC_PARAMETER.size or len(containers) % _GENERIC_CONTAINER.size:
        raise ContractViolation("generic table record extents are invalid")
    count = len(parameters) // _GENERIC_PARAMETER.size
    cursor = 0
    owners = set()
    for index, (owner, arity, is_method, start) in enumerate(_GENERIC_CONTAINER.iter_unpack(containers)):
        if (owner < 0 or arity <= 0 or is_method not in (0, 1) or (is_method, owner) in owners or
            start != cursor or arity > count - start):
            raise ContractViolation("generic container ownership or range does not close")
        owners.add((is_method, owner))
        for number in range(arity):
            row = _GENERIC_PARAMETER.unpack_from(parameters, (start + number) * _GENERIC_PARAMETER.size)
            if row[0] != index or row[4] != number:
                raise ContractViolation("generic parameter back-reference or local position differs")
        cursor += arity
    if cursor != count:
        raise ContractViolation("generic parameter table contains unowned records")
    return True


class _MetadataFile:
    def __init__(self) -> None:
        self.tables: dict[str, bytearray] = {
            name: bytearray() for name in _V24_2_TABLES
        }

    def append(self, name: str, record: struct.Struct, *values: Any) -> int:
        table = self.tables[name]
        index = len(table) // record.size
        table.extend(record.pack(*values))
        return index

    def extend_i32(self, name: str, values: Iterable[int]) -> int:
        table = self.tables[name]
        start = len(table) // 4
        for value in values:
            table.extend(struct.pack("<i", value))
        return start

    def extend_u32(self, name: str, values: Iterable[int]) -> int:
        table = self.tables[name]
        start = len(table) // 4
        for value in values:
            table.extend(struct.pack("<I", value))
        return start

    def build(self) -> tuple[bytes, dict[str, dict[str, int]]]:
        header_size = 8 + len(_V24_2_TABLES) * 8
        if header_size != 264:
            raise AssertionError("v24.4 metadata header size changed")
        body = bytearray()
        directory: dict[str, dict[str, int]] = {}
        cursor = header_size
        for name in _V24_2_TABLES:
            while cursor & 3:
                body.append(0)
                cursor += 1
            data = self.tables[name]
            directory[name] = {"offset": cursor, "size": len(data)}
            body.extend(data)
            cursor += len(data)
        header = bytearray(struct.pack("<II", METADATA_MAGIC, 24))
        for name in _V24_2_TABLES:
            row = directory[name]
            header.extend(struct.pack("<II", row["offset"], row["size"]))
        result = bytes(header + body)
        parsed = parse_global_metadata(result)
        if parsed.header_size != 264 or parsed.version != 24:
            raise ContractViolation("reconstructed metadata self-parse failed")
        return result, directory


@dataclass(frozen=True)
class _DescriptorDomain:
    by_descriptor: dict[int, int]
    by_current_pointer: dict[int, int]
    by_value: dict[tuple[int, int], tuple[int, ...]]
    descriptors: tuple[int, ...]
    values: tuple[tuple[int, int, int, int], ...]
    byref_by_element: dict[int, int]
    void: int


def _descriptor_domain(
    runtime: _RuntimeOutput, descriptor_values: dict[str, Any]
) -> _DescriptorDomain:
    records = tuple(descriptor_values["records"])
    if len(records) != runtime.renderer.node_count:
        raise ContractViolation("descriptor and type-reference domains differ")
    by_descriptor: dict[int, int] = {}
    by_current_pointer: dict[int, int] = {}
    by_value_lists: dict[tuple[int, int], list[int]] = defaultdict(list)
    descriptors: list[int] = []
    byref_by_element: dict[int, int] = {}
    void_indexes: list[int] = []
    for index, record in enumerate(records):
        descriptor, current, _data, bits = record
        reference = runtime.renderer.reference_row(index)
        if reference[0] != descriptor or descriptor in by_descriptor:
            raise ContractViolation("descriptor inventory order is inconsistent")
        by_descriptor[descriptor] = index
        if current in by_current_pointer:
            raise ContractViolation("current descriptor pointers repeat")
        by_current_pointer[current] = index
        by_value_lists[(_data, bits)].append(index)
        descriptors.append(descriptor)
        code = (bits >> 16) & 0xFF
        if code == 1:
            void_indexes.append(index)
        if (bits >> 30) & 1:
            element = reference[13]
            if not element or element in byref_by_element:
                raise ContractViolation("by-reference descriptor is ambiguous")
            byref_by_element[element] = index
    if len(void_indexes) != 1:
        raise ContractViolation("void descriptor is ambiguous")
    missing_roots = [
        runtime.renderer.identity_row(index)[2]
        for index in range(runtime.type_count)
        if runtime.renderer.identity_row(index)[2] not in by_descriptor
    ]
    if missing_roots:
        raise ContractViolation("root descriptors are absent from closure")
    return _DescriptorDomain(
        by_descriptor=by_descriptor,
        by_current_pointer=by_current_pointer,
        by_value={key: tuple(value) for key, value in by_value_lists.items()},
        descriptors=tuple(descriptors),
        values=records,
        byref_by_element=byref_by_element,
        void=void_indexes[0],
    )


def _type_index(domain: _DescriptorDomain, descriptor: int) -> int:
    try:
        return domain.by_descriptor[descriptor]
    except KeyError as error:
        raise ContractViolation(
            f"descriptor is absent from exact closure: {descriptor:#x}"
        ) from error


def _member_ranges(
    owner_count: int, rows: Iterable[tuple[int, ...]], *, label: str
) -> tuple[list[int], list[int], list[tuple[int, ...]]]:
    materialized = list(rows)
    starts = [-1] * owner_count
    counts = [0] * owner_count
    previous = -1
    for index, row in enumerate(materialized):
        owner = int(row[0])
        if not 0 <= owner < owner_count or owner < previous:
            raise ContractViolation(f"{label} owner order is invalid")
        if starts[owner] < 0:
            starts[owner] = index
        counts[owner] += 1
        previous = owner
    return starts, counts, materialized


def _method_generic_details(
    runtime: _RuntimeOutput,
    detail_bytes: bytes | None = None,
) -> tuple[dict[int, tuple[int, int]], dict[int, tuple[int, tuple[int, ...]]]]:
    detail_bytes = detail_bytes or runtime.generic_parameter_details
    detail_header = RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.unpack_from(
        detail_bytes
    )
    detail_argument_count, detail_constraint_count = detail_header[5:7]
    detail_constraint_start = (
        RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
        + detail_argument_count * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
    )
    if (
        detail_header[0] != b"BALV2GP1"
        or detail_header[1] != 1
        or detail_argument_count < runtime.method_generic_argument_count
        or detail_constraint_start + detail_constraint_count * 8
        != len(detail_bytes)
    ):
        raise ContractViolation("generic parameter detail domain is invalid")
    containers: dict[int, tuple[int, int]] = {}
    details: dict[int, tuple[int, tuple[int, ...]]] = {}
    for method_index in range(runtime.method_count):
        index, count, start = RUNTIME_METHOD_GENERIC_RECORD.unpack_from(
            runtime.method_generics,
            RUNTIME_METHOD_GENERIC_HEADER.size
            + method_index * RUNTIME_METHOD_GENERIC_RECORD.size,
        )
        if index != method_index or start + count > runtime.method_generic_argument_count:
            raise ContractViolation("method generic range is invalid")
        if count:
            containers[method_index] = (start, count)
        for offset in range(count):
            argument = start + offset
            descriptor = struct.unpack_from(
                "<Q",
                runtime.method_generics,
                runtime.method_generic_argument_start + argument * 8,
            )[0]
            detail = RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.unpack_from(
                detail_bytes,
                RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
                + argument * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size,
            )
            if detail[0] != descriptor or detail[3] + detail[2] > detail_constraint_count:
                raise ContractViolation("method generic detail is invalid")
            constraints = tuple(
                struct.unpack_from(
                    "<Q",
                    detail_bytes,
                    detail_constraint_start + (detail[3] + i) * 8,
                )[0]
                for i in range(detail[2])
            )
            details[descriptor] = (detail[1], constraints)
    return containers, details


def _literal_data(constant: dict[str, Any]) -> bytes | None:
    if constant["value_kind"] in ("missing", "runtime_object"):
        raise ContractViolation(
            "non-materialized runtime default has no metadata literal payload"
        )
    if constant["value_kind"] == "null":
        return None
    if constant["value_kind"] == "string":
        value = constant["string_value"]
        if value is None:
            return None
        encoded = value.encode("utf-8", errors="surrogatepass")
        return struct.pack("<i", len(encoded)) + encoded
    width = int(constant["width"])
    if width not in (1, 2, 4, 8):
        raise ContractViolation("constant width is invalid")
    return int(constant["raw_value"]).to_bytes(width, "little")


def _metadata_inputs(
    receipt: dict[str, Any], runtime: _RuntimeOutput
) -> tuple[
    dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any],
    dict[str, Any], dict[str, Any] | None, dict[str, Any] | None,
]:
    inputs = receipt["inputs"]
    executable_sha256 = receipt["target"]["executable_sha256"]
    literals = load_runtime_string_literal_inventory(
        model_path=Path(inputs["string_literal_model"]["path"]),
        inventory_path=Path(inputs["string_literal_inventory"]["path"]),
        expected_executable_sha256=executable_sha256,
    )
    usage_pairs = load_runtime_metadata_usage_pair_inventory(
        model_path=Path(inputs["metadata_usage_pair_model"]["path"]),
        inventory_path=Path(inputs["metadata_usage_pair_inventory"]["path"]),
        expected_executable_sha256=executable_sha256,
        expected_string_literal_inventory_sha256=literals["identity"]["sha256"],
    )
    usage_values = load_runtime_metadata_usage_value_inventory(
        model_path=Path(inputs["metadata_usage_value_model"]["path"]),
        inventory_path=Path(inputs["metadata_usage_value_inventory"]["path"]),
        expected_executable_sha256=executable_sha256,
        expected_metadata_usage_pair_inventory_sha256=usage_pairs["identity"]["sha256"],
    )
    usage_members = load_runtime_metadata_usage_member_inventory(
        model_path=Path(inputs["metadata_usage_member_model"]["path"]),
        inventory_path=Path(inputs["metadata_usage_member_inventory"]["path"]),
        expected_executable_sha256=executable_sha256,
        expected_metadata_usage_pair_inventory_sha256=usage_pairs["identity"]["sha256"],
    )
    constants = load_runtime_enum_constants(
        model_path=Path(inputs["enum_constant_model"]["path"]),
        inventory_path=Path(inputs["enum_constant_inventory"]["path"]),
        expected_executable_sha256=executable_sha256,
    )
    if (
        "parameter_default_model" in inputs
        and "parameter_default_inventory" in inputs
    ):
        parameter_defaults = load_runtime_parameter_defaults(
            model_path=Path(inputs["parameter_default_model"]["path"]),
            inventory_path=Path(
                inputs["parameter_default_inventory"]["path"]
            ),
            expected_executable_sha256=executable_sha256,
        )
    elif (
        "parameter_default_model" in inputs
        or "parameter_default_inventory" in inputs
    ):
        raise ContractViolation(
            "metadata parameter default input pair is incomplete"
        )
    else:
        parameter_defaults = None
    if (
        "assembly_identity_model" in inputs
        and "assembly_identity_inventory" in inputs
    ):
        assembly_identities = load_runtime_assembly_identities(
            model_path=Path(inputs["assembly_identity_model"]["path"]),
            inventory_path=Path(
                inputs["assembly_identity_inventory"]["path"]
            ),
            expected_executable_sha256=executable_sha256,
        )
    elif (
        "assembly_identity_model" in inputs
        or "assembly_identity_inventory" in inputs
    ):
        raise ContractViolation(
            "metadata assembly identity input pair is incomplete"
        )
    else:
        assembly_identities = None
    if any(
        value["target"]["executable_sha256"] != executable_sha256
        for value in (
            literals, usage_pairs, usage_values, usage_members, constants,
            *([parameter_defaults] if parameter_defaults is not None else []),
            *([assembly_identities] if assembly_identities is not None else []),
        )
    ):
        raise ContractViolation("metadata input target bindings differ")
    if runtime.type_count != receipt["counts"]["type_count"]:
        raise ContractViolation("metadata runtime receipt count differs")
    return (
        literals, usage_pairs, usage_values, usage_members, constants,
        parameter_defaults, assembly_identities,
    )


def reconstruct_runtime_global_metadata(
    *, native_output_receipt: Path,
    type_descriptor_value_model: Path,
    type_descriptor_value_inventory: Path,
    output_dir: Path,
    allow_incomplete: bool = False,
    type_reference_model: Path | None = None,
    type_reference_inventory: Path | None = None,
    full_generic_parameter_detail_model: Path | None = None,
    full_generic_parameter_detail_inventory: Path | None = None,
    domain_evidence: dict[str, Any] | None = None,
) -> dict[str, Any]:
    receipt, paths, runtime = _runtime(native_output_receipt)
    from alpha.p17 import bind_output_event_accessors, event_raise_pointer, event_local_accessor_indices
    if "event_module_model" in paths:
        bind_output_event_accessors(runtime, model_path=paths["event_module_model"],
            event_inventory=receipt["inputs"]["event_module_inventory"],
            type_identity=receipt["inputs"]["type_identity_inventory"])
    executable_sha256 = receipt["target"]["executable_sha256"]
    if (type_reference_model is None) != (type_reference_inventory is None):
        raise AcquisitionError("type reference override inputs are incomplete")
    if type_reference_model is not None and type_reference_inventory is not None:
        direct_rows = runtime.renderer.direct_interface_rows
        direct_descriptors = runtime.renderer.direct_interface_descriptors
        reference_model_path = _owner_file(
            type_reference_model, label="type reference model"
        )
        reference_path = _owner_file(
            type_reference_inventory, label="type reference inventory"
        )
        reference_model_data = read_json(reference_model_path)
        reference_raw = reference_path.read_bytes()
        reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
        if (
            reference_model_data.get("schema") != RUNTIME_TYPE_REFERENCE_SCHEMA
            or reference_model_data.get("status") != "runtime-validated"
            or reference_model_data.get("target", {}).get("executable_sha256")
            != executable_sha256
            or reference_model_data.get("inventory") != file_identity(reference_path)
            or not reference_model_data.get("checks")
            or not all(reference_model_data["checks"].values())
            or reference_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
            or reference_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        ):
            raise AcquisitionError("type reference override is stale")
        runtime.references = reference_raw
        runtime.renderer = _TypeRenderer(runtime.identity, runtime.graph, reference_raw)
        runtime.renderer.direct_interface_rows = direct_rows
        runtime.renderer.direct_interface_descriptors = direct_descriptors
        paths["type_reference_inventory"] = reference_path
    from alpha.c05 import bind_output_reference_names, metadata_reference_name
    raw_reference_model_path = reference_model_path if type_reference_model is not None else paths.get("model")
    if raw_reference_model_path is not None:
        bind_output_reference_names(model_path=raw_reference_model_path,
            inventory=file_identity(paths["type_reference_inventory"]), executable_sha256=executable_sha256,
            runtime=runtime)
        from alpha.c05 import bind_output_raw_names
        raw_selected = dict(receipt["inputs"], model=file_identity(raw_reference_model_path),
                            type_reference_inventory=file_identity(paths["type_reference_inventory"]))
        bind_output_raw_names(runtime, reference_model_path=raw_reference_model_path, selected=raw_selected)
    from alpha.c05 import original_metadata_name
    def projected_name(domain, index, display):
        return original_metadata_name(runtime, domain, index) if hasattr(runtime, "raw_metadata_names") else display
    if (
        full_generic_parameter_detail_model is None
    ) != (full_generic_parameter_detail_inventory is None):
        raise AcquisitionError("full generic parameter detail inputs are incomplete")
    full_generic_detail_bytes: bytes | None = None
    if (
        full_generic_parameter_detail_model is not None
        and full_generic_parameter_detail_inventory is not None
    ):
        detail_model_path = _owner_file(
            full_generic_parameter_detail_model,
            label="full generic parameter detail model",
        )
        detail_inventory_path = _owner_file(
            full_generic_parameter_detail_inventory,
            label="full generic parameter detail inventory",
        )
        detail_model_data = read_json(detail_model_path)
        if (
            detail_model_data.get("schema")
            != "alpha.runtime-generic-parameter-detail-inventory/v1"
            or detail_model_data.get("status") != "runtime-validated"
            or detail_model_data.get("target", {}).get("executable_sha256")
            != executable_sha256
            or detail_model_data.get("inventory")
            != file_identity(detail_inventory_path)
            or not detail_model_data.get("checks")
            or not all(detail_model_data["checks"].values())
        ):
            raise AcquisitionError("full generic parameter detail is stale")
        full_generic_detail_bytes = detail_inventory_path.read_bytes()
    descriptor_values = load_runtime_type_descriptor_values(
        model_path=type_descriptor_value_model,
        inventory_path=type_descriptor_value_inventory,
        expected_executable_sha256=executable_sha256,
    )
    if (
        descriptor_values["inputs"]["type_reference_inventory"]["sha256"]
        != file_identity(paths["type_reference_inventory"])["sha256"]
    ):
        raise AcquisitionError("descriptor values use a different type closure")
    domain = _descriptor_domain(runtime, descriptor_values)
    (
        literals, usage_pairs, usage_values, usage_members, constants,
        parameter_defaults, assembly_identities,
    ) = (
        _metadata_inputs(receipt, runtime)
    )


    declared_domains = (
        *(("raw_core_metadata_names",) if not hasattr(runtime, "raw_metadata_names") else ()),
        *(("raw_generic_parameter_names",) if not hasattr(runtime, "raw_reference_names") else ()),
        *(("event_raise_accessors",) if not hasattr(runtime, "event_raise_pointers") else ()),
        "event_attribute_bit_semantics",
        "current_metadata_header_table_format",


        "module_name_operation_semantics",
        "image_file_name_identity",
        "module_image_assembly_ownership_graph",
        *(() if parameter_defaults is not None else (
            "parameter_default_values",
        )),
        "custom_attribute_type_ranges",
        "custom_attribute_types",
        "vtable_methods",
        "interface_offsets",
        "native_type_sizes_and_packing",
        "field_offset_storage_origins",
        "value_type_payload_origin",
        *(() if assembly_identities is not None else (
            "assembly_identity_details",
        )),
        "assembly_reference_graph",
        "image_entry_points_and_exported_types",
        "field_marshaled_sizes",
        "unresolved_virtual_call_signatures",
        "windows_runtime_type_names",
    )
    proven_domains = {
        name
        for name, record in (domain_evidence or {}).items()
        if isinstance(record, dict)
        and record.get("status") in ("proven", "proven-empty")
    }
    pending_domains = tuple(
        name for name in declared_domains if name not in proven_domains
    )
    if pending_domains and not allow_incomplete:
        raise AcquisitionError(
            "runtime global metadata completion domains are absent: "
            + ", ".join(pending_domains)
        )

    output_dir = output_dir.expanduser().resolve()
    output_dir.mkdir(parents=True, exist_ok=True)
    output_dir.chmod(0o700)
    metadata = _MetadataFile()
    strings = _StringHeap()

    identity_rows = [
        runtime.renderer.identity_row(index) for index in range(runtime.type_count)
    ]
    root_index = {row[2]: index for index, row in enumerate(identity_rows)}
    if len(root_index) != runtime.type_count:
        raise ContractViolation("type-definition descriptors repeat")
    contextual_type_specs: dict[tuple[int, int], dict[str, Any]] = {}

    def contextual_type_index(descriptor: int, attributes: int = 0) -> int:
        base = _type_index(domain, descriptor)
        if not 0 <= attributes <= 0xFFFF:
            raise ContractViolation("type usage attributes exceed uint16")
        base_bits = domain.values[base][3]
        if base_bits & 0xFFFF == attributes:
            return base
        key = base, attributes
        existing = contextual_type_specs.get(key)
        if existing is not None:
            return int(existing["index"])
        index = len(domain.descriptors) + len(contextual_type_specs)
        contextual_type_specs[key] = {
            "index": index,
            "kind": "attribute_clone",
            "clone_index": base,
            "attributes": attributes,
            "bits": (base_bits & ~0xFFFF) | attributes,
            "name": runtime.renderer.render(descriptor),
        }
        return index

    field_starts, field_counts, field_rows = _member_ranges(
        runtime.type_count,
        (
            RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
                runtime.native,
                RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
                + index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
            )
            for index in range(runtime.field_count)
        ),
        label="field",
    )
    property_starts, property_counts, property_rows = _member_ranges(
        runtime.type_count,
        (
            RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.unpack_from(
                runtime.native,
                runtime.property_start
                + index * RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size,
            )
            for index in range(runtime.property_count)
        ),
        label="property",
    )
    method_starts, method_counts, method_rows = _member_ranges(
        runtime.type_count,
        (runtime.method_row(index) for index in range(runtime.method_count)),
        label="method",
    )
    event_starts, event_counts, event_rows = _member_ranges(
        runtime.type_count,
        (
            RUNTIME_EVENT_MODULE_EVENT.unpack_from(
                runtime.events,
                runtime.event_start + index * RUNTIME_EVENT_MODULE_EVENT.size,
            )
            for index in range(runtime.event_count)
        ),
        label="event",
    )
    parameter_starts = [row[11] if row[10] else -1 for row in method_rows]


    nested_by_owner: dict[int, list[int]] = defaultdict(list)
    for index, row in enumerate(identity_rows):
        if row[5]:
            owner = root_index.get(row[5])
            if owner is None:
                raise ContractViolation("nested type owner is absent")
            nested_by_owner[owner].append(index)
    nested_ranges: dict[int, tuple[int, int]] = {}
    for owner in range(runtime.type_count):
        values = nested_by_owner.get(owner, [])
        start = metadata.extend_i32("nested_types", values) if values else -1
        nested_ranges[owner] = (start, len(values))

    if runtime.renderer.direct_interface_rows is None:
        raise AcquisitionError(
            "direct InterfaceImpl inventory is required for metadata reconstruction"
        )
    interface_ranges: dict[int, tuple[int, int]] = {}
    for owner in range(runtime.type_count):
        values = [
            contextual_type_index(descriptor)
            for descriptor in runtime.renderer.root_interface_descriptors(owner)
        ]
        if identity_rows[owner][1] & 0x20 and values:
            raise ContractViolation("enum has a direct InterfaceImpl entry")
        start = metadata.extend_i32("interfaces", values) if values else -1
        interface_ranges[owner] = (start, len(values))


    vtable_ranges: dict[int, tuple[int, int]] = {
        owner: (-1, 0) for owner in range(runtime.type_count)
    }

    method_generic_ranges, method_generic_details = _method_generic_details(
        runtime, full_generic_detail_bytes
    )
    all_generic_details = dict(method_generic_details)
    detail_source = full_generic_detail_bytes if full_generic_detail_bytes is not None else runtime.generic_parameter_details
    if detail_source is not None:
        detail_header = RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.unpack_from(
            detail_source
        )
        detail_constraint_start = (
            RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
            + detail_header[5] * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
        )
        if (detail_header[:5] != (b"BALV2GP1", 1, RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size,
                RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size, 0) or
            detail_constraint_start + detail_header[6] * 8 != len(detail_source)):
            raise ContractViolation("full generic parameter observation header is invalid")
        seen_details = set()
        for argument in range(detail_header[5]):
            detail = RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.unpack_from(
                detail_source,
                RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
                + argument * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size,
            )
            if (not detail[0] or detail[0] in seen_details or detail[1] & ~31 or
                detail[3] + detail[2] > detail_header[6]):
                raise ContractViolation("full generic parameter observation record is invalid")
            seen_details.add(detail[0])
            constraints = tuple(
                struct.unpack_from(
                    "<Q", detail_source,
                    detail_constraint_start + (detail[3] + offset) * 8,
                )[0]
                for offset in range(detail[2])
            )
            current = (detail[1], constraints)
            previous = all_generic_details.get(detail[0])
            if previous is not None and previous != current:
                raise ContractViolation(
                    "generic parameter detail repeats inconsistently"
                )
            all_generic_details[detail[0]] = current
    generic_parameter_by_descriptor: dict[int, int] = {}
    generic_container_by_type: dict[int, int] = {}
    generic_container_by_method: dict[int, int] = {}

    def append_generic_parameter(
        *, descriptor: int, owner: int, number: int,
        attributes: int, constraints: tuple[int, ...],
    ) -> int:
        reference_index = runtime.renderer.node_by_descriptor.get(descriptor)
        if reference_index is None:
            raise ContractViolation("generic parameter reference is absent")
        reference = runtime.renderer.reference_row(reference_index)
        if not reference[4] & TYPE_REFERENCE_GENERIC_PARAMETER:
            raise ContractViolation("generic parameter shape is invalid")
        name = (metadata_reference_name(runtime, descriptor) if hasattr(runtime, "raw_reference_names") else
            _text(runtime.references, reference[17], reference[5], label="incomplete generic parameter display name"))
        constraint_start = (
            metadata.extend_i32(
                "generic_parameter_constraints",
                (contextual_type_index(value) for value in constraints),
            )
            if constraints else -1
        )
        return _append_generic_parameter_record(metadata, strings, generic_parameter_by_descriptor,
            descriptor=descriptor, container_index=owner, number=number, name=name,
            constraint_start=constraint_start, constraint_count=len(constraints), attributes=attributes)


    for owner in range(runtime.type_count):
        graph = runtime.renderer.graph_row(owner)
        if not (graph[1] & 8):
            continue
        argument_count = graph[7]
        if not argument_count:
            continue
        first = len(metadata.tables["generic_parameters"]) // _GENERIC_PARAMETER.size
        container_index = metadata.append("generic_containers", _GENERIC_CONTAINER, owner, argument_count, 0, first)
        for number in range(argument_count):
            descriptor = struct.unpack_from(
                "<Q",
                runtime.graph,
                runtime.renderer.graph_argument_start
                + (graph[9] + number) * 8,
            )[0]
            if descriptor not in all_generic_details:
                raise ContractViolation("type generic attributes and constraints have no runtime observation")
            attributes, constraints = all_generic_details[descriptor]
            append_generic_parameter(
                descriptor=descriptor, owner=container_index, number=number,
                attributes=attributes, constraints=constraints,
            )
        generic_container_by_type[owner] = container_index

    for method_index, (argument_start, count) in method_generic_ranges.items():
        first = len(metadata.tables["generic_parameters"]) // _GENERIC_PARAMETER.size
        container_index = metadata.append("generic_containers", _GENERIC_CONTAINER, method_index, count, 1, first)
        for number in range(count):
            descriptor = struct.unpack_from(
                "<Q", runtime.method_generics,
                runtime.method_generic_argument_start
                + (argument_start + number) * 8,
            )[0]
            attributes, constraints = all_generic_details[descriptor]
            append_generic_parameter(
                descriptor=descriptor, owner=container_index, number=number,
                attributes=attributes, constraints=constraints,
            )
        generic_container_by_method[method_index] = container_index

    _validate_generic_table_ownership(metadata)


    field_type_indexes = [
        contextual_type_index(field[3], field[5] & 0xFFFF)
        for field in field_rows
    ]
    parameter_type_indexes = [
        contextual_type_index(
            parameter[2],
            parameter[3] & 0xFFFF,
        )
        for parameter in (
            runtime.parameter_row(index)
            for index in range(runtime.parameter_count)
        )
    ]
    for index, field in enumerate(field_rows):
        name = projected_name("field", index, _text(runtime.native, field[9], field[7], label="field name"))
        metadata.append(
            "fields", _FIELD,
            strings.add(name), field_type_indexes[index],
            field[6],
        )
    for index in range(runtime.parameter_count):
        parameter = runtime.parameter_row(index)
        name = _text(
            runtime.methods, parameter[7], parameter[5], label="parameter name"
        )
        name = projected_name("parameter", index, name)
        metadata.append(
            "parameters", _PARAMETER,
            strings.add(name), parameter[6],
            parameter_type_indexes[index],
        )
    for index, method in enumerate(method_rows):
        name = projected_name("method", index, runtime.method_name(index, method))
        return_type = (
            domain.void
            if method[9] & METHOD_DETAIL_CONSTRUCTOR
            else contextual_type_index(method[4])
        )
        metadata.append(
            "methods", _METHOD,
            strings.add(name), method[0], return_type,
            parameter_starts[index], generic_container_by_method.get(index, -1),
            method[7], method[5] & 0xFFFF,
            method[6] & 0xFFFF, method[8] & 0xFFFF, method[10],
        )
    for index, prop in enumerate(property_rows):
        name = projected_name("property", index, _text(runtime.native, prop[9], prop[6], label="property name"))
        owner_method_start = method_starts[prop[0]]
        getter_global = (
            runtime.method_by_pointer.get(prop[3], -1) if prop[3] else -1
        )
        setter_global = (
            runtime.method_by_pointer.get(prop[4], -1) if prop[4] else -1
        )
        getter = (
            getter_global - owner_method_start if getter_global >= 0 else -1
        )
        setter = (
            setter_global - owner_method_start if setter_global >= 0 else -1
        )
        if getter < 0 and setter < 0:
            raise ContractViolation("property has no accessor")
        if any(
            value >= method_counts[prop[0]] for value in (getter, setter)
        ):
            raise ContractViolation("property accessor is outside its owner")
        metadata.append(
            "properties", _PROPERTY,
            strings.add(name), getter, setter, prop[7] & 0xFFFF,
            prop[5],
        )
    for index, event in enumerate(event_rows):
        name = projected_name("event", index, _text(runtime.events, event[10], event[7], label="event name"))
        owner_method_start = method_starts[event[0]]


        raised = event_raise_pointer(runtime, index) if hasattr(runtime, "event_raise_pointers") else 0
        add, remove, raise_index = event_local_accessor_indices(runtime, event,
            owner_start=owner_method_start, owner_count=method_counts[event[0]], raise_pointer=raised)
        metadata.append(
            "events", _EVENT,
            strings.add(name), contextual_type_index(event[3]),
            add, remove, raise_index, event[6],
        )


    constants_by_field = {
        int(value["field_index"]): value for value in constants["constants"]
    }
    default_blob = metadata.tables["field_and_parameter_default_value_data"]
    for field_index in sorted(constants_by_field):
        constant = constants_by_field[field_index]
        field = field_rows[field_index]
        value = _literal_data(constant)
        data_index = -1 if value is None else len(default_blob)
        if value is not None:
            default_blob.extend(value)
        metadata.append(
            "field_default_values", _DEFAULT,
            field_index, field_type_indexes[field_index], data_index,
        )

    defaults_by_parameter = {
        int(value["parameter_index"]): value
        for value in (
            parameter_defaults["defaults"]
            if parameter_defaults is not None else []
        )
    }
    if parameter_defaults is not None:
        expected_default_parameters = {
            index
            for index in range(runtime.parameter_count)
            if runtime.parameter_row(index)[3] & 0x1000
        }
        if (
            set(defaults_by_parameter) != expected_default_parameters
            or len(defaults_by_parameter)
            != parameter_defaults["counts"]["default_count"]
        ):
            raise ContractViolation(
                "parameter default reconstruction domain is incomplete"
            )
        for parameter_index in sorted(defaults_by_parameter):
            constant = defaults_by_parameter[parameter_index]
            if constant["value_kind"] == "missing":
                continue
            value = _literal_data(constant)
            data_index = -1 if value is None else len(default_blob)
            if value is not None:
                default_blob.extend(value)
            metadata.append(
                "parameter_default_values", _DEFAULT,
                parameter_index,
                contextual_type_index(
                    int(constant["value_type_descriptor"])
                ),
                data_index,
            )


    literal_blob = metadata.tables["string_literal_data"]
    for literal in literals["literals"]:
        value = literal["value"].encode("utf-8", errors="surrogatepass")
        metadata.append(
            "string_literals", _STRING_LITERAL, len(value), len(literal_blob)
        )
        literal_blob.extend(value)


    for owner, identity in enumerate(identity_rows):
        graph = runtime.renderer.graph_row(owner)
        name = _text(runtime.identity, identity[11], identity[8], label="type name")
        namespace = _text(
            runtime.identity, identity[12], identity[9], label="type namespace"
        ) if identity[9] else ""
        name = projected_name("type", owner, name)
        namespace = projected_name("type_namespace", owner, namespace)


        declaring = contextual_type_index(identity[5]) if identity[5] else -1
        parent = contextual_type_index(graph[3]) if graph[3] else -1
        element = -1
        if identity[1] & 0x20:
            candidates = [
                field
                for field in field_rows[
                    (field_starts[owner] if field_starts[owner] >= 0 else 0):
                    (field_starts[owner] if field_starts[owner] >= 0 else 0)
                    + field_counts[owner]
                ]
                if field[5] & 0x600 == 0x600 and not field[5] & 0x50
            ]
            if len(candidates) != 1:
                raise ContractViolation("enum underlying type is ambiguous")
            element = contextual_type_index(candidates[0][3])
        nested_start, nested_count = nested_ranges[owner]
        interface_start, interface_count = interface_ranges[owner]
        vtable_start, vtable_count = vtable_ranges[owner]
        counts16 = (
            method_counts[owner], property_counts[owner], field_counts[owner],
            event_counts[owner], nested_count, vtable_count, interface_count, 0,
        )
        if any(not 0 <= value <= 0xFFFF for value in counts16):
            raise ContractViolation("TypeDef relationship count exceeds v24")
        bitfield = (1 if identity[1] & 0x40 else 0) | (
            2 if identity[1] & 0x20 else 0
        )
        metadata.append(
            "type_definitions", _TYPE_DEFINITION,
            strings.add(name), strings.add(namespace),
            contextual_type_index(identity[2]),
            (
                contextual_type_index(
                    domain.descriptors[domain.byref_by_element[identity[2]]]
                )
                if identity[2] in domain.byref_by_element else -1
            ),
            declaring, parent, element,
            generic_container_by_type.get(owner, -1), identity[7],
            field_starts[owner], method_starts[owner], event_starts[owner],
            property_starts[owner], nested_start, interface_start,
            vtable_start, -1, *counts16, bitfield,
            identity[10],
        )


    image_rows: list[tuple[int, str, int, int]] = []
    cursor = 0
    while cursor < runtime.type_count:
        module = identity_rows[cursor][4]
        end = cursor + 1
        while end < runtime.type_count and identity_rows[end][4] == module:
            end += 1
        name = runtime.module_names.get(module)
        if name is None:
            raise ContractViolation("module name is absent")
        if hasattr(runtime, "raw_metadata_names"):
            from alpha.c05 import original_module_name
            name = original_module_name(runtime, module)
        image_rows.append((module, name, cursor, end - cursor))
        cursor = end
    if len(image_rows) != runtime.module_count:
        raise ContractViolation("module/type image domains differ")
    assemblies_by_module: dict[str, dict[str, Any]] = {}
    if assembly_identities is not None:
        for assembly in assembly_identities["assemblies"]:
            module_name = str(assembly["module_name"])
            if module_name in assemblies_by_module:
                raise ContractViolation("assembly module identity repeats")
            assemblies_by_module[module_name] = assembly
        if set(assemblies_by_module) != {
            name for _module, name, _start, _count in image_rows
        }:
            raise ContractViolation(
                "assembly identities do not cover the exact image domain"
            )
    for index, (_module, name, start, count) in enumerate(image_rows):
        metadata.append(
            "images", _IMAGE,
            strings.add(name), index, start, count, -1, 0, -1, 1, -1, 0,
        )
        assembly = assemblies_by_module.get(name)
        if assembly is None:
            assembly_name = name.rsplit(".", 1)[0]
            culture_index = public_key_index = hash_algorithm = hash_length = 0
            flags = 0
            version = (0, 0, 0, 0)
            public_key_token = b"\0" * 8
        else:
            assembly_name = str(assembly["name"])
            culture_index = strings.add(str(assembly["culture"]))
            public_key = bytes.fromhex(str(assembly["public_key"]))
            public_key_index = strings.add_blob(public_key)
            hash_algorithm = int(assembly["hash_algorithm"])
            hash_length = len(public_key)
            flags = int(assembly["flags"])
            version = tuple(int(value) for value in assembly["version"])
            if len(version) != 4:
                raise ContractViolation("assembly version arity is invalid")
            token = bytes.fromhex(str(assembly["public_key_token"]))
            if len(token) not in (0, 8):
                raise ContractViolation("assembly public-key token is invalid")
            public_key_token = token or b"\0" * 8
        metadata.append(
            "assemblies", _ASSEMBLY,
            index, 0x20000000 | (index + 1), -1, 0,
            strings.add(assembly_name), culture_index, public_key_index,
            hash_algorithm, hash_length, flags, *version, public_key_token,
        )


    usage_value_by_first = {
        value["first_occurrence_index"]: value
        for value in usage_values["type_usages"]
    }
    field_ref_index: dict[int, int] = {}
    with MappedPE(paths["binary"], require_runtime_functions=False) as image:
        for value in usage_members["field_refs"]:
            first = value["first_occurrence_index"]
            type_rva = (
                usage_members["type_record_base_rva"]
                + value["type_source_index"]
                * usage_members["type_record_stride"]
            )
            offset = image.rva_to_offset(type_rva)
            if offset is None or offset + 16 > len(image._mapping):
                raise ContractViolation("field-ref owner type has no PE bytes")
            owner, bits = struct.unpack_from("<QQ", image._mapping, offset)
            code = (bits >> 16) & 0xFF
            if code not in (0x11, 0x12) or owner >= runtime.type_count:
                raise ContractViolation("field-ref owner type is invalid")
            field_ref_index[first] = metadata.append(
                "field_refs", _FIELD_REF,
                contextual_type_index(identity_rows[owner][2]),
                value["field_index"],
            )


    method_spec_index = {
        value["first_occurrence_index"]: index
        for index, value in enumerate(usage_members["method_specs"])
    }
    pair_by_first = {
        value["first_occurrence_index"]: value
        for value in usage_pairs["usages"]
    }
    if len(pair_by_first) != usage_pairs["counts"]["usage_count"]:
        raise ContractViolation("usage first-occurrence indexes repeat")
    semantic_type_indexes: dict[tuple[str, int, int], tuple[int, ...]] | None = None
    semantic_relaxed_indexes: dict[tuple[str, int], tuple[int, ...]] | None = None
    extra_usage_type_indexes: dict[tuple[str, int, int], int] = {}
    extra_usage_type_specs: dict[int, dict[str, Any]] = {}
    method_generic_inst_arguments: dict[int, list[int]] = {}

    def semantic_key(
        name: str, bits: int, data_value: int, descriptor: int | None = None,
    ) -> tuple[str, int, int]:
        code = (bits >> 16) & 0xFF
        definition = -1
        if code == 0x15:
            if not data_value >> 32 and data_value < len(
                usage_values["generic_records_owner_only"]
            ):
                definition = int(
                    usage_values["generic_records_owner_only"][data_value][0]
                )
            elif descriptor is not None:
                reference_index = runtime.renderer.node_by_descriptor.get(descriptor)
                reference = (
                    runtime.renderer.reference_row(reference_index)
                    if reference_index is not None else None
                )
                definition = (
                    runtime.renderer.root_by_descriptor.get(reference[14], -1)
                    if reference is not None else -1
                )
                if definition < 0:
                    raise ContractViolation("generic definition is absent")
            else:
                raise ContractViolation("generic type record index is invalid")
        return name, bits & 0xC000FFFF, definition
    with _MetadataUsageTypeRenderer(
        binary=paths["binary"], renderer=runtime.renderer,
        generic_records=usage_values["generic_records_owner_only"],
    ) as usage_type_renderer:
        def ensure_semantic_indexes() -> None:
            nonlocal semantic_type_indexes, semantic_relaxed_indexes
            if semantic_type_indexes is not None:
                return
            grouped: dict[tuple[str, int, int], list[int]] = defaultdict(list)
            for descriptor_index, row in enumerate(domain.values):
                grouped[
                    semantic_key(
                        runtime.renderer.render(row[0]),
                        row[3],
                        row[2],
                        row[0],
                    )
                ].append(descriptor_index)
            semantic_type_indexes = {
                key: tuple(indexes) for key, indexes in grouped.items()
            }
            relaxed_grouped: dict[tuple[str, int], list[int]] = defaultdict(list)
            for key, indexes in semantic_type_indexes.items():
                relaxed_grouped[(key[0], key[2])].extend(indexes)
            semantic_relaxed_indexes = {
                key: tuple(indexes) for key, indexes in relaxed_grouped.items()
            }

        def resolve_usage_type(pointer: int, data_value: int, bits: int) -> int:
            direct = domain.by_current_pointer.get(pointer)
            if direct is not None:
                return direct
            matches = domain.by_value.get((data_value, bits), ())
            if matches:
                return min(matches)
            rendered = usage_type_renderer.render(pointer, data_value, bits)
            usage_key = semantic_key(rendered, bits, data_value)
            ensure_semantic_indexes()
            assert semantic_type_indexes is not None
            assert semantic_relaxed_indexes is not None
            matches = semantic_type_indexes.get(usage_key, ())
            if matches:
                return min(matches)
            previous = extra_usage_type_indexes.get(usage_key)
            if previous is not None:
                return previous

            source = (
                len(domain.descriptors)
                + len(contextual_type_specs)
                + len(extra_usage_type_indexes)
            )
            extra_usage_type_indexes[usage_key] = source
            code = (bits >> 16) & 0xFF
            spec: dict[str, Any] = {
                "index": source,
                "bits": bits,
                "name": rendered,
            }
            relaxed = semantic_relaxed_indexes.get(
                (usage_key[0], usage_key[2]), ()
            )
            if relaxed:
                spec.update(kind="clone", clone_index=min(relaxed))
            elif code in (
                0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x16, 0x18,
                0x19, 0x1C,
            ):
                spec.update(kind="raw", data=data_value)
            elif code in (0x11, 0x12):
                if data_value >> 32 or data_value >= runtime.type_count:
                    raise ContractViolation(
                        "metadata usage definition index is invalid"
                    )
                spec.update(kind="definition", definition_index=data_value)
            elif code in (0x0F, 0x10, 0x1D):
                child_data, child_bits = usage_type_renderer._type_record(
                    data_value
                )
                spec.update(
                    kind="element",
                    element_index=resolve_usage_type(
                        data_value, child_data, child_bits
                    ),
                )
            elif code == 0x14:
                element_pointer = usage_type_renderer._qword(data_value)
                rank = usage_type_renderer._qword(data_value + 8) & 0xFF
                if not 1 <= rank <= 32:
                    raise ContractViolation(
                        "metadata usage array rank is invalid"
                    )
                child_data, child_bits = usage_type_renderer._type_record(
                    element_pointer
                )
                spec.update(
                    kind="array",
                    rank=rank,
                    element_index=resolve_usage_type(
                        element_pointer, child_data, child_bits
                    ),
                )
            elif code == 0x15:
                generic_index = data_value & 0xFFFFFFFF
                generic_records = usage_values["generic_records_owner_only"]
                if data_value >> 32 or generic_index >= len(generic_records):
                    raise ContractViolation(
                        "metadata usage generic index is invalid"
                    )
                definition, instance, _cached_type, _cached_class = (
                    generic_records[generic_index]
                )
                if definition >> 32 or definition >= runtime.type_count:
                    raise ContractViolation(
                        "metadata usage generic definition is invalid"
                    )
                argument_count = usage_type_renderer._qword(instance)
                arguments_pointer = usage_type_renderer._qword(instance + 8)
                if not 1 <= argument_count <= 64:
                    raise ContractViolation(
                        "metadata usage generic arity is invalid"
                    )
                arguments: list[int] = []
                for argument_index in range(argument_count):
                    argument_pointer = usage_type_renderer._qword(
                        arguments_pointer + argument_index * 8
                    )
                    argument_data, argument_bits = (
                        usage_type_renderer._type_record(argument_pointer)
                    )
                    arguments.append(
                        resolve_usage_type(
                            argument_pointer, argument_data, argument_bits
                        )
                    )
                spec.update(
                    kind="genericinst",
                    definition_index=definition,
                    argument_indexes=arguments,
                )
            else:
                raise ContractViolation(
                    f"metadata usage type cannot be reconstructed: {code}"
                )
            extra_usage_type_specs[source] = spec
            return source

        for destination, first in enumerate(sorted(pair_by_first)):
            value = pair_by_first[first]
            kind = value["usage_kind"]
            source = value["source_index"]
            if kind == 1:
                typed = usage_value_by_first.get(first)
                if typed is None:
                    raise ContractViolation("type usage value is absent")
                current = runtime.identity_header[6] + typed["type_record_rva"]
                source = resolve_usage_type(
                    current,
                    typed["type_data_owner_only"],
                    typed["type_bits_owner_only"],
                )
            elif kind == 4:
                source = field_ref_index[first]
            elif kind == 6:
                source = method_spec_index[first]
            elif kind not in (3, 5):
                raise ContractViolation(f"unsupported metadata usage kind: {kind}")
            if not 0 <= source < (1 << 29):
                raise ContractViolation("metadata usage source exceeds v24 encoding")
            metadata.append(
                "metadata_usage_pairs", _METADATA_USAGE_PAIR,
                destination, (kind << 29) | source,
            )


        generic_inst_base = (
            runtime.identity_header[6]
            + usage_members["generic_inst_base_rva"]
        )
        generic_inst_stride = usage_members["generic_inst_stride"]
        for method_spec in usage_members["method_specs"]:
            for source_index in (
                method_spec["class_inst_index"],
                method_spec["method_inst_index"],
            ):
                if source_index == -1 or source_index in method_generic_inst_arguments:
                    continue
                if source_index < 0:
                    raise ContractViolation(
                        "method generic instance source is invalid"
                    )
                instance = generic_inst_base + source_index * generic_inst_stride
                argument_count = usage_type_renderer._qword(instance)
                arguments_pointer = usage_type_renderer._qword(instance + 8)
                if not 1 <= argument_count <= 64:
                    raise ContractViolation(
                        "method generic instance arity is invalid"
                    )
                argument_indexes: list[int] = []
                for argument_index in range(argument_count):
                    argument_pointer = usage_type_renderer._qword(
                        arguments_pointer + argument_index * 8
                    )
                    argument_data, argument_bits = (
                        usage_type_renderer._type_record(argument_pointer)
                    )
                    argument_indexes.append(
                        resolve_usage_type(
                            argument_pointer, argument_data, argument_bits
                        )
                    )
                method_generic_inst_arguments[source_index] = argument_indexes
    metadata.append(
        "metadata_usage_lists", _METADATA_USAGE_LIST,
        0, usage_pairs["counts"]["usage_count"],
    )

    metadata.tables["metadata_strings"] = strings.data
    data, directory = metadata.build()
    output_path = output_dir / "global-metadata.dat"
    _write_bytes(output_path, data)
    counts = {
        "type_definitions": runtime.type_count,
        "type_descriptors": len(domain.descriptors)
        + len(contextual_type_specs)
        + len(extra_usage_type_indexes),
        "type_descriptor_closure_records": len(domain.descriptors),
        "contextual_type_records": len(contextual_type_specs),
        "extra_metadata_usage_type_records": len(extra_usage_type_indexes),
        "methods": runtime.method_count,
        "parameters": runtime.parameter_count,
        "fields": runtime.field_count,
        "properties": runtime.property_count,
        "events": runtime.event_count,
        "images": len(image_rows),
        "assemblies": len(image_rows),
        "assembly_identities": len(assemblies_by_module),
        "string_literals": len(literals["literals"]),
        "field_defaults": len(constants_by_field),
        "parameter_default_states": len(defaults_by_parameter),
        "parameter_defaults": len(
            metadata.tables["parameter_default_values"]
        ) // _DEFAULT.size,
        "parameter_missing_defaults": sum(
            value["value_kind"] == "missing"
            for value in defaults_by_parameter.values()
        ),
        "generic_parameters": len(metadata.tables["generic_parameters"])
        // _GENERIC_PARAMETER.size,
        "generic_containers": len(metadata.tables["generic_containers"])
        // _GENERIC_CONTAINER.size,
        "metadata_usage_pairs": usage_pairs["counts"]["usage_count"],
        "field_refs": len(field_ref_index),
        "method_specs_for_companion": len(method_spec_index),
        "direct_interfaces": len(metadata.tables["interfaces"]) // 4,
    }
    checks = {
        "target_binding_matches": True,
        "generic_container_parameter_ownership_roundtrip": _validate_generic_table_ownership(metadata),
        "standard_v24_4_header": True,
        "all_type_definitions_projected": counts["type_definitions"] == runtime.type_count,
        "all_methods_projected": counts["methods"] == runtime.method_count,
        "all_parameters_projected": counts["parameters"] == runtime.parameter_count,
        "all_fields_projected": counts["fields"] == runtime.field_count,
        "all_properties_projected": counts["properties"] == runtime.property_count,
        "all_events_projected": counts["events"] == runtime.event_count,
        "all_images_projected": counts["images"] == runtime.module_count,
        "all_assemblies_projected": counts["assemblies"]
        == runtime.module_count,
        "all_assembly_identities_projected": (
            assembly_identities is None
            or counts["assembly_identities"]
            == assembly_identities["counts"]["assembly_count"]
            == runtime.module_count
        ),
        "all_string_literals_projected": counts["string_literals"]
        == literals["counts"]["literal_count"],
        "all_literal_field_defaults_projected": counts["field_defaults"]
        == constants["counts"]["constant_count"],
        "all_parameter_defaults_projected": (
            parameter_defaults is None
            or (
                counts["parameter_default_states"]
                == parameter_defaults["counts"]["default_count"]
                and counts["parameter_defaults"]
                == parameter_defaults["counts"][
                    "materialized_default_count"
                ]
                and counts["parameter_missing_defaults"]
                == parameter_defaults["counts"]["missing_default_count"]
                and parameter_defaults["counts"][
                    "runtime_object_default_count"
                ] == 0
            )
        ),
        "all_metadata_usages_projected": counts["metadata_usage_pairs"]
        == usage_pairs["counts"]["usage_count"],
        "all_field_refs_projected": counts["field_refs"]
        == usage_members["counts"]["field_ref_count"],
        "all_method_specs_accounted_for_companion": counts[
            "method_specs_for_companion"
        ] == usage_members["counts"]["method_spec_count"],
        "all_direct_interfaces_projected": counts["direct_interfaces"]
        == receipt["counts"]["direct_interface_count"],
        "incomplete_domains_explicit": bool(pending_domains),
    }
    payload = {
        "schema": RUNTIME_GLOBAL_METADATA_RECONSTRUCTION_SCHEMA,
        "status": (
            "structural-reconstruction-incomplete"
            if pending_domains else "complete"
        ),
        "target": receipt["target"],
        "inputs": {
            "native_output_receipt": file_identity(
                native_output_receipt.expanduser().resolve()
            ),
            "type_descriptor_value_model": file_identity(
                _owner_file(type_descriptor_value_model, label="descriptor model")
            ),
            "type_descriptor_value_inventory": file_identity(
                _owner_file(type_descriptor_value_inventory, label="descriptor inventory")
            ),
            "direct_interface_model": receipt["inputs"][
                "direct_interface_model"
            ],
            "direct_interface_inventory": receipt["inputs"][
                "direct_interface_inventory"
            ],
            **(
                {
                    "assembly_identity_model": receipt["inputs"][
                        "assembly_identity_model"
                    ],
                    "assembly_identity_inventory": receipt["inputs"][
                        "assembly_identity_inventory"
                    ],
                }
                if assembly_identities is not None else {}
            ),
        },
        "artifact": file_identity(output_path),
        "directory": directory,
        "counts": counts,
        "checks": checks,
        "pending_domains": list(pending_domains),
        "domain_evidence": domain_evidence or {},
        "declared_domain_count": len(declared_domains),
        "proven_domain_count": len(proven_domains),
        "policy": {
            "contiguous_decrypted_metadata_search_used": False,
            "runtime_domains_repacked_as_standard_v24_4": True,
            "unobserved_values_fabricated": False,
            "structural_incomplete_mode_explicit": allow_incomplete,
        },
        "companion_contract": {
            "type_descriptor_count": counts["type_descriptors"],
            "generic_parameter_by_descriptor": [
                {"descriptor": descriptor, "index": index}
                for descriptor, index in sorted(
                    generic_parameter_by_descriptor.items(),
                    key=lambda item: item[1],
                )
            ],
            "extra_usage_types": [
                value
                for value in sorted(
                    [
                        *contextual_type_specs.values(),
                        *extra_usage_type_specs.values(),
                    ],
                    key=lambda item: int(item["index"]),
                )
            ],
            "method_spec_count": counts["method_specs_for_companion"],
            "method_generic_instances": [
                {
                    "source_index": source_index,
                    "argument_indexes": argument_indexes,
                }
                for source_index, argument_indexes in sorted(
                    method_generic_inst_arguments.items()
                )
            ],
            "metadata_usage_count": counts["metadata_usage_pairs"],
        },
    }
    receipt_path = output_dir / "global-metadata-reconstruction.private.json"
    atomic_write_json(receipt_path, payload)
    receipt_path.chmod(0o600)
    return {**payload, "receipt": file_identity(receipt_path)}
