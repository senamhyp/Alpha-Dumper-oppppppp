import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.p02 import runtime_inventory_contract
from alpha.p04 import load_runtime_member_detail_observation
from alpha.c03 import MAXIMUM_IDENTITY_STRING_BYTES, MAXIMUM_TYPE_RELATIONS, TYPE_SHAPE_GENERIC, TYPE_SHAPE_GENERIC_DEFINITION, TYPE_SHAPE_MASK, load_runtime_type_identity_observation
from alpha.h02 import file_identity, sha256_file


RUNTIME_TYPE_GRAPH_SCHEMA = "alpha.runtime-type-graph-observation/v1"
RUNTIME_TYPE_GRAPH_MAGIC = b"ALPHATG1"
RUNTIME_TYPE_GRAPH_VERSION = 1
RUNTIME_TYPE_GRAPH_HEADER = struct.Struct(
    "<8sIIII64s64s64s64s64sQQ"
)
RUNTIME_TYPE_GRAPH_ENTRY = struct.Struct("<Q10I4Q")
TYPE_SHAPE_GENERIC_PARAMETER = 1 << 6
TYPE_SHAPE_ARRAY = 1 << 7
TYPE_SHAPE_POINTER = 1 << 8
TYPE_GRAPH_SHAPE_MASK = (
    TYPE_SHAPE_MASK
    | TYPE_SHAPE_GENERIC_PARAMETER
    | TYPE_SHAPE_ARRAY
    | TYPE_SHAPE_POINTER
)
NO_GENERIC_PARAMETER_POSITION = 0xFFFFFFFF
MAXIMUM_TYPE_GRAPH_NODES = 2_000_000
MAXIMUM_TYPE_GRAPH_RELATIONS = 16_000_000
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(f"runtime type graph {label} is invalid") from error
    if not _SHA256.fullmatch(value):
        raise AcquisitionError(f"runtime type graph {label} is invalid")
    return value


def _text(data: bytes, position: int, length: int, *, label: str, empty: bool) -> tuple[str, int]:
    if length > MAXIMUM_IDENTITY_STRING_BYTES or (not empty and not length):
        raise AcquisitionError(f"runtime type graph {label} length is invalid")
    end = position + length
    if end > len(data):
        raise AcquisitionError(f"runtime type graph {label} is truncated")
    try:
        value = data[position:end].decode("utf-8")
    except UnicodeDecodeError as error:
        raise AcquisitionError(f"runtime type graph {label} is invalid") from error
    if (not empty and not value) or any(ord(character) < 0x20 for character in value):
        raise AcquisitionError(f"runtime type graph {label} is invalid")
    return value, end


def _detail_type_references(details: dict[str, Any]) -> set[int]:
    references: set[int] = set()
    for type_record in details["types"]:
        references.update(
            field["type_object"] for field in type_record["fields"]
        )
        for category in ("methods", "constructors"):
            for method in type_record[category]:
                if method["return_type"] is not None:
                    references.add(method["return_type"])
                references.update(
                    parameter["type_object"]
                    for parameter in method["parameters"]
                )
                references.update(method["generic_arguments"])
        references.update(
            event["handler_type"] for event in type_record["events"]
        )
    return references


def _node_references(record: dict[str, Any]) -> tuple[int, ...]:
    return tuple(
        reference
        for reference in (
            record["base_type"],
            record["declaring_type"],
            record["element_type"],
            record["generic_definition"],
            *record["interfaces"],
            *record["generic_arguments"],
            *record["generic_parameter_constraints"],
        )
        if reference is not None
    )


def load_runtime_type_graph_observation(
    path: Path,
    *,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    type_observation_path = type_observation_path.expanduser().resolve()
    member_observation_path = member_observation_path.expanduser().resolve()
    type_identity_observation_path = type_identity_observation_path.expanduser().resolve()
    member_detail_observation_path = member_detail_observation_path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime type graph observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError("runtime type graph observation is not owner-only")
    identities = load_runtime_type_identity_observation(
        type_identity_observation_path,
        type_observation_path=type_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    details = load_runtime_member_detail_observation(
        member_detail_observation_path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    try:
        data = path.read_bytes()
    except OSError as error:
        raise AcquisitionError("runtime type graph observation is unreadable") from error
    if len(data) < RUNTIME_TYPE_GRAPH_HEADER.size:
        raise AcquisitionError("runtime type graph observation is truncated")
    (
        magic,
        version,
        header_bytes,
        pointer_bytes,
        reserved,
        executable_raw,
        inventory_raw,
        roots_raw,
        identities_raw,
        details_raw,
        node_count,
        root_count,
    ) = RUNTIME_TYPE_GRAPH_HEADER.unpack_from(data)
    executable_sha256 = _digest(executable_raw, label="target digest")
    inventory_sha256 = _digest(inventory_raw, label="inventory digest")
    roots_sha256 = _digest(roots_raw, label="type-root digest")
    identities_sha256 = _digest(identities_raw, label="type-identity digest")
    details_sha256 = _digest(details_raw, label="member-detail digest")
    inventory = runtime_inventory_contract()
    if (
        magic != RUNTIME_TYPE_GRAPH_MAGIC
        or version != RUNTIME_TYPE_GRAPH_VERSION
        or header_bytes != RUNTIME_TYPE_GRAPH_HEADER.size
        or pointer_bytes != 8
        or reserved != 0
        or executable_sha256 != identities["target"]["executable_sha256"]
        or executable_sha256 != details["target"]["executable_sha256"]
        or inventory_sha256 != inventory["contract_id"].rsplit(":", 1)[-1]
        or roots_sha256 != sha256_file(type_observation_path)
        or identities_sha256 != sha256_file(type_identity_observation_path)
        or details_sha256 != sha256_file(member_detail_observation_path)
        or root_count != identities["type_count"]
        or not root_count <= node_count <= MAXIMUM_TYPE_GRAPH_NODES
    ):
        raise AcquisitionError("runtime type graph header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime type graph target binding is stale")

    position = header_bytes
    records: list[dict[str, Any]] = []
    pointers: set[int] = set()
    relation_count = 0
    for node_index in range(node_count):
        end = position + RUNTIME_TYPE_GRAPH_ENTRY.size
        if end > len(data):
            raise AcquisitionError("runtime type graph node is truncated")
        (
            type_object,
            name_bytes,
            namespace_bytes,
            attributes,
            shape,
            generic_parameter_position,
            generic_parameter_attributes,
            interface_count,
            generic_argument_count,
            constraint_count,
            element_rank,
            base_type,
            declaring_type,
            element_type,
            generic_definition,
        ) = RUNTIME_TYPE_GRAPH_ENTRY.unpack_from(data, position)
        position = end
        generic_parameter = bool(shape & TYPE_SHAPE_GENERIC_PARAMETER)
        if (
            not type_object
            or type_object & 7
            or type_object in pointers
            or shape & ~TYPE_GRAPH_SHAPE_MASK
            or bool(shape & TYPE_SHAPE_GENERIC_DEFINITION)
            and not shape & TYPE_SHAPE_GENERIC
            or generic_parameter
            != (generic_parameter_position != NO_GENERIC_PARAMETER_POSITION)
            or not generic_parameter and generic_parameter_attributes
            or bool(shape & TYPE_SHAPE_ARRAY) != bool(element_rank)
            or element_rank > 32
            or sum(
                bool(shape & bit)
                for bit in (
                    TYPE_SHAPE_ARRAY,
                    TYPE_SHAPE_POINTER,
                    1 << 4,
                )
            )
            > 1
            or interface_count > MAXIMUM_TYPE_RELATIONS
            or generic_argument_count > MAXIMUM_TYPE_RELATIONS
            or constraint_count > MAXIMUM_TYPE_RELATIONS
        ):
            raise AcquisitionError("runtime type graph node shape is invalid")
        pointers.add(type_object)
        name, position = _text(
            data, position, name_bytes, label="type name", empty=False
        )
        namespace, position = _text(
            data,
            position,
            namespace_bytes,
            label="type namespace",
            empty=True,
        )
        local_relation_count = (
            interface_count + generic_argument_count + constraint_count
        )
        relation_count += local_relation_count
        if relation_count > MAXIMUM_TYPE_GRAPH_RELATIONS:
            raise AcquisitionError("runtime type graph has too many relations")
        relation_end = position + local_relation_count * pointer_bytes
        if relation_end > len(data):
            raise AcquisitionError("runtime type graph relations are truncated")
        relations = (
            struct.unpack_from(f"<{local_relation_count}Q", data, position)
            if local_relation_count
            else ()
        )
        position = relation_end
        raw_references = (
            base_type,
            declaring_type,
            element_type,
            generic_definition,
            *relations,
        )
        if any(reference and reference & 7 for reference in raw_references):
            raise AcquisitionError("runtime type graph reference is invalid")
        interfaces_end = interface_count
        arguments_end = interfaces_end + generic_argument_count
        records.append(
            {
                "node_index": node_index,
                "type_object": type_object,
                "name": name,
                "namespace": namespace,
                "attributes": attributes,
                "shape": shape,
                "generic_parameter_position": (
                    generic_parameter_position if generic_parameter else None
                ),
                "generic_parameter_attributes": generic_parameter_attributes,
                "element_rank": element_rank,
                "base_type": base_type or None,
                "declaring_type": declaring_type or None,
                "element_type": element_type or None,
                "generic_definition": generic_definition or None,
                "interfaces": list(relations[:interfaces_end]),
                "generic_arguments": list(
                    relations[interfaces_end:arguments_end]
                ),
                "generic_parameter_constraints": list(
                    relations[arguments_end:]
                ),
            }
        )
        current = records[-1]
        if bool(
            current["shape"]
            & (TYPE_SHAPE_ARRAY | TYPE_SHAPE_POINTER | (1 << 4))
        ) != bool(current["element_type"]):
            raise AcquisitionError(
                "runtime type graph element shape is inconsistent"
            )
    if position != len(data):
        raise AcquisitionError("runtime type graph has a trailer")

    by_pointer = {record["type_object"]: record for record in records}
    if any(
        reference not in by_pointer
        for record in records
        for reference in _node_references(record)
    ):
        raise AcquisitionError("runtime type graph is not reference-closed")
    for index, identity in enumerate(identities["types"]):
        graph = records[index]
        if (
            graph["type_object"] != identity["type_object"]
            or graph["name"] != identity["name"]
            or graph["namespace"] != identity["namespace"]
            or graph["attributes"] != identity["attributes"]
            or graph["shape"] & TYPE_SHAPE_MASK != identity["shape"]
            or graph["base_type"] != identity["base_type"]
            or graph["declaring_type"] != identity["declaring_type"]
            or graph["element_type"] != identity["element_type"]
            or graph["generic_definition"] != identity["generic_definition"]
            or graph["interfaces"] != identity["interfaces"]
            or graph["generic_arguments"] != identity["generic_arguments"]
        ):
            raise AcquisitionError(
                "runtime type graph roots do not match type identities"
            )
    detail_references = _detail_type_references(details)
    if not detail_references.issubset(by_pointer):
        raise AcquisitionError(
            "runtime type graph does not resolve every member type"
        )
    pending = [
        *(record["type_object"] for record in records[:root_count]),
        *detail_references,
    ]
    reachable: set[int] = set()
    while pending:
        pointer = pending.pop()
        if pointer in reachable:
            continue
        reachable.add(pointer)
        pending.extend(_node_references(by_pointer[pointer]))
    if reachable != pointers:
        raise AcquisitionError("runtime type graph contains unreachable nodes")
    return {
        "schema": RUNTIME_TYPE_GRAPH_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contract": {
            "inventory_contract_id": inventory["contract_id"],
            "type_observation_sha256": roots_sha256,
            "type_identity_observation_sha256": identities_sha256,
            "member_detail_observation_sha256": details_sha256,
        },
        "root_count": root_count,
        "node_count": node_count,
        "external_node_count": node_count - root_count,
        "relation_count": relation_count,
        "member_type_reference_count": len(detail_references),
        "nodes": records,
        "identity": file_identity(path),
        "raw_runtime_type_objects_owner_only": True,
        "reference_closure_complete": True,
    }


def inspect_runtime_type_graph_observation(
    path: Path,
    *,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_type_graph_observation(
        path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        member_detail_observation_path=member_detail_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_TYPE_GRAPH_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contract": model["contract"],
        "root_count": model["root_count"],
        "node_count": model["node_count"],
        "external_node_count": model["external_node_count"],
        "relation_count": model["relation_count"],
        "member_type_reference_count": model["member_type_reference_count"],
        "reference_closure_complete": model["reference_closure_complete"],
        "identity": model["identity"],
        "raw_runtime_type_objects_exposed": False,
    }


import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, ContractViolation
from alpha.p04 import load_runtime_member_detail_observation
from alpha.c03 import load_runtime_type_identity_observation
from alpha.h02 import atomic_write_json, file_identity


RUNTIME_METADATA_MAPPING_SCHEMA = "alpha.runtime-metadata-definition-mapping/v1"
METADATA_MAGIC = 0xFAB11BAF
MAXIMUM_METADATA_BYTES = 1024 * 1024 * 1024
MAXIMUM_DEFINITION_STRIDE = 128
_IMAGE_SUFFIX = re.compile(r"\.(?:dll|exe)$", re.IGNORECASE)


def _metadata_tables(
    data: bytes,
) -> tuple[int, int, list[dict[str, int]]]:
    if len(data) < 0x80 or len(data) > MAXIMUM_METADATA_BYTES:
        raise AcquisitionError("runtime metadata definition source has invalid bounds")
    magic, version, header_bytes = struct.unpack_from("<III", data)
    if (
        magic != METADATA_MAGIC
        or header_bytes < 0x80
        or header_bytes > min(len(data), 0x4000)
        or (header_bytes - 8) % 8
    ):
        raise AcquisitionError("runtime metadata definition header is invalid")
    tables: list[dict[str, int]] = []
    for pair_index in range((header_bytes - 8) // 8):
        offset, size = struct.unpack_from("<II", data, 8 + pair_index * 8)
        if not size:
            if offset:
                raise AcquisitionError(
                    "runtime metadata definition empty table has an offset"
                )
            continue
        if offset < header_bytes or offset + size < offset or offset + size > len(data):
            raise AcquisitionError("runtime metadata definition table is invalid")
        tables.append({"pair_index": pair_index, "offset": offset, "bytes": size})
    if len(tables) < 4:
        raise AcquisitionError("runtime metadata definition directory is incomplete")
    ordered = sorted(tables, key=lambda item: item["offset"])
    if any(
        left["offset"] + left["bytes"] > right["offset"]
        for left, right in zip(ordered, ordered[1:])
    ):
        raise AcquisitionError("runtime metadata definition tables overlap")
    return version, header_bytes, tables


def _string_at(
    data: bytes,
    table: dict[str, int],
    index: int,
    cache: dict[tuple[int, int], str | None],
) -> str | None:
    key = (table["pair_index"], index)
    if key in cache:
        return cache[key]
    if index < 0 or index >= table["bytes"]:
        cache[key] = None
        return None
    start = table["offset"] + index
    end = data.find(b"\0", start, table["offset"] + table["bytes"])
    if end < 0 or end - start > 16_384:
        cache[key] = None
        return None
    try:
        value = data[start:end].decode("utf-8")
    except UnicodeDecodeError:
        value = None
    cache[key] = value
    return value


def _probe_indexes(count: int) -> tuple[int, ...]:


    return tuple(range(count))


def _assembly_key(value: str) -> str:
    simple = value.split(",", 1)[0].strip()
    simple = _IMAGE_SUFFIX.sub("", simple).casefold()
    if not simple:
        raise ContractViolation("runtime assembly identity is invalid")
    return simple


def _image_order_candidates(
    data: bytes,
    tables: list[dict[str, int]],
    assemblies: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    expected = {
        _assembly_key(assembly["full_name"]): assembly["assembly_index"]
        for assembly in assemblies
    }
    if len(expected) != len(assemblies):
        raise ContractViolation("runtime assembly simple names are not unique")
    count = len(assemblies)
    if not count:
        raise ContractViolation("runtime assembly inventory is empty")
    string_cache: dict[tuple[int, int], str | None] = {}
    candidates: list[dict[str, Any]] = []
    for record_table in tables:
        if record_table["bytes"] % count:
            continue
        stride = record_table["bytes"] // count
        if stride < 8 or stride > MAXIMUM_DEFINITION_STRIDE or stride % 4:
            continue
        for name_dword in range(stride // 4):
            for string_table in tables:
                if string_table is record_table:
                    continue
                order: list[int] = []
                for index in range(count):
                    string_index = struct.unpack_from(
                        "<I",
                        data,
                        record_table["offset"] + index * stride + name_dword * 4,
                    )[0]
                    observed = _string_at(
                        data, string_table, string_index, string_cache
                    )
                    if observed is None:
                        break
                    try:
                        observed_key = _assembly_key(observed)
                    except ContractViolation:
                        break
                    assembly_index = expected.get(observed_key)
                    if assembly_index is None:
                        break
                    order.append(assembly_index)
                if len(order) != count or len(set(order)) != count:
                    continue
                candidates.append(
                    {
                        "record_pair_index": record_table["pair_index"],
                        "record_offset": record_table["offset"],
                        "record_stride": stride,
                        "string_pair_index": string_table["pair_index"],
                        "name_dword_index": name_dword,
                        "assembly_order": order,
                    }
                )
    return candidates


def _unique_image_order(
    candidates: list[dict[str, Any]],
) -> tuple[list[int], list[dict[str, int]]]:
    orders = {tuple(candidate["assembly_order"]) for candidate in candidates}
    if len(orders) != 1:
        raise AcquisitionError(
            f"runtime metadata image order is not unique ({len(orders)})"
        )
    order = list(next(iter(orders)))
    evidence = [
        {key: value for key, value in candidate.items() if key != "assembly_order"}
        for candidate in candidates
        if candidate["assembly_order"] == order
    ]
    unique_evidence = {
        tuple(sorted(candidate.items())): candidate for candidate in evidence
    }
    return order, list(unique_evidence.values())


def _definition_layouts(
    data: bytes,
    tables: list[dict[str, int]],
    records: list[dict[str, Any]],
    *,
    token_required: bool,
) -> list[dict[str, int]]:
    count = len(records)
    if not count:
        raise ContractViolation("runtime metadata definition inventory is empty")
    probes = _probe_indexes(count)
    string_cache: dict[tuple[int, int], str | None] = {}
    candidates: list[dict[str, int]] = []
    for record_table in tables:
        if record_table["bytes"] % count:
            continue
        stride = record_table["bytes"] // count
        if stride < 8 or stride > MAXIMUM_DEFINITION_STRIDE or stride % 4:
            continue
        dwords = stride // 4
        token_slots: list[int | None] = [None]
        if token_required:
            token_slots = []
            for token_dword in range(dwords):
                if all(
                    struct.unpack_from(
                        "<I",
                        data,
                        record_table["offset"] + index * stride + token_dword * 4,
                    )[0]
                    == records[index]["token"]
                    for index in probes
                ):
                    token_slots.append(token_dword)
        for token_dword in token_slots:
            if token_required and not all(
                struct.unpack_from(
                    "<I",
                    data,
                    record_table["offset"] + index * stride + int(token_dword) * 4,
                )[0]
                == record["token"]
                for index, record in enumerate(records)
            ):
                continue
            for name_dword in range(dwords):
                if token_dword is not None and name_dword == token_dword:
                    continue
                for string_table in tables:
                    if string_table is record_table:
                        continue
                    if not all(
                        _string_at(
                            data,
                            string_table,
                            struct.unpack_from(
                                "<I",
                                data,
                                record_table["offset"]
                                + index * stride
                                + name_dword * 4,
                            )[0],
                            string_cache,
                        )
                        == records[index]["name"]
                        for index in probes
                    ):
                        continue
                    if not all(
                        _string_at(
                            data,
                            string_table,
                            struct.unpack_from(
                                "<I",
                                data,
                                record_table["offset"]
                                + index * stride
                                + name_dword * 4,
                            )[0],
                            string_cache,
                        )
                        == record["name"]
                        for index, record in enumerate(records)
                    ):
                        continue
                    candidates.append(
                        {
                            "record_pair_index": record_table["pair_index"],
                            "record_offset": record_table["offset"],
                            "record_stride": stride,
                            "string_pair_index": string_table["pair_index"],
                            "name_dword_index": name_dword,
                            "token_dword_index": (
                                int(token_dword) if token_dword is not None else -1
                            ),
                        }
                    )
    return candidates


def _type_definition_layouts(
    data: bytes,
    tables: list[dict[str, int]],
    records: list[dict[str, Any]],
) -> list[dict[str, int]]:
    count = len(records)
    if not count:
        raise ContractViolation("runtime type definition inventory is empty")
    probes = _probe_indexes(count)
    string_cache: dict[tuple[int, int], str | None] = {}
    candidates: list[dict[str, int]] = []
    for record_table in tables:
        if record_table["bytes"] % count:
            continue
        stride = record_table["bytes"] // count
        if stride < 12 or stride > MAXIMUM_DEFINITION_STRIDE or stride % 4:
            continue
        dwords = stride // 4
        attribute_slots = [
            attribute_dword
            for attribute_dword in range(dwords)
            if all(
                struct.unpack_from(
                    "<I",
                    data,
                    record_table["offset"] + index * stride + attribute_dword * 4,
                )[0]
                == records[index]["attributes"]
                for index in probes
            )
        ]
        for attribute_dword in attribute_slots:
            if not all(
                struct.unpack_from(
                    "<I",
                    data,
                    record_table["offset"] + index * stride + attribute_dword * 4,
                )[0]
                == record["attributes"]
                for index, record in enumerate(records)
            ):
                continue
            for name_dword in range(dwords):
                if name_dword == attribute_dword:
                    continue
                for namespace_dword in range(dwords):
                    if namespace_dword in {name_dword, attribute_dword}:
                        continue
                    for string_table in tables:
                        if string_table is record_table:
                            continue
                        if not all(
                            _string_at(
                                data,
                                string_table,
                                struct.unpack_from(
                                    "<I",
                                    data,
                                    record_table["offset"]
                                    + index * stride
                                    + name_dword * 4,
                                )[0],
                                string_cache,
                            )
                            == records[index]["name"]
                            and _string_at(
                                data,
                                string_table,
                                struct.unpack_from(
                                    "<I",
                                    data,
                                    record_table["offset"]
                                    + index * stride
                                    + namespace_dword * 4,
                                )[0],
                                string_cache,
                            )
                            == records[index]["namespace"]
                            for index in probes
                        ):
                            continue
                        if not all(
                            _string_at(
                                data,
                                string_table,
                                struct.unpack_from(
                                    "<I",
                                    data,
                                    record_table["offset"]
                                    + index * stride
                                    + name_dword * 4,
                                )[0],
                                string_cache,
                            )
                            == record["name"]
                            and _string_at(
                                data,
                                string_table,
                                struct.unpack_from(
                                    "<I",
                                    data,
                                    record_table["offset"]
                                    + index * stride
                                    + namespace_dword * 4,
                                )[0],
                                string_cache,
                            )
                            == record["namespace"]
                            for index, record in enumerate(records)
                        ):
                            continue
                        candidates.append(
                            {
                                "record_pair_index": record_table["pair_index"],
                                "record_offset": record_table["offset"],
                                "record_stride": stride,
                                "string_pair_index": string_table["pair_index"],
                                "name_dword_index": name_dword,
                                "namespace_dword_index": namespace_dword,
                                "attributes_dword_index": attribute_dword,
                            }
                        )
    return candidates


def _string_literal_candidates(
    data: bytes,
    tables: list[dict[str, int]],
) -> list[tuple[dict[str, int], list[dict[str, Any]]]]:
    candidates: list[tuple[dict[str, int], list[dict[str, Any]]]] = []
    for record_table in tables:
        for stride in range(8, MAXIMUM_DEFINITION_STRIDE + 1, 4):
            if record_table["bytes"] % stride:
                continue
            count = record_table["bytes"] // stride
            if not count:
                continue
            dwords = stride // 4
            for length_dword in range(dwords):
                for data_index_dword in range(dwords):
                    if data_index_dword == length_dword:
                        continue
                    first_length = struct.unpack_from(
                        "<I",
                        data,
                        record_table["offset"] + length_dword * 4,
                    )[0]
                    first_index = struct.unpack_from(
                        "<I",
                        data,
                        record_table["offset"] + data_index_dword * 4,
                    )[0]
                    if first_index != 0:
                        continue
                    last_record = record_table["offset"] + (count - 1) * stride
                    last_length = struct.unpack_from(
                        "<I", data, last_record + length_dword * 4
                    )[0]
                    last_index = struct.unpack_from(
                        "<I", data, last_record + data_index_dword * 4
                    )[0]
                    if last_index + last_length < last_index:
                        continue
                    for data_table in tables:
                        if data_table is record_table:
                            continue
                        if last_index + last_length != data_table["bytes"]:
                            continue
                        entries: list[tuple[int, int]] = []
                        cursor = 0
                        valid = True
                        for index in range(count):
                            position = record_table["offset"] + index * stride
                            length = struct.unpack_from(
                                "<I", data, position + length_dword * 4
                            )[0]
                            data_index = struct.unpack_from(
                                "<I", data, position + data_index_dword * 4
                            )[0]
                            if data_index != cursor or length > data_table["bytes"] - cursor:
                                valid = False
                                break
                            entries.append((data_index, length))
                            cursor += length
                        if not valid or cursor != data_table["bytes"]:
                            continue
                        literals: list[dict[str, Any]] = []
                        for index, (data_index, length) in enumerate(entries):
                            start = data_table["offset"] + data_index
                            try:
                                value = data[start : start + length].decode("utf-8")
                            except UnicodeDecodeError:
                                valid = False
                                break
                            literals.append(
                                {
                                    "index": index,
                                    "data_offset": start,
                                    "value": value,
                                }
                            )
                        if not valid:
                            continue
                        candidates.append(
                            (
                                {
                                    "record_pair_index": record_table["pair_index"],
                                    "record_offset": record_table["offset"],
                                    "record_stride": stride,
                                    "length_dword_index": length_dword,
                                    "data_index_dword_index": data_index_dword,
                                    "data_pair_index": data_table["pair_index"],
                                    "data_offset": data_table["offset"],
                                    "data_bytes": data_table["bytes"],
                                },
                                literals,
                            )
                        )
    return candidates


def _unique_string_literals(
    candidates: list[tuple[dict[str, int], list[dict[str, Any]]]],
) -> tuple[dict[str, int], list[dict[str, Any]]]:
    unique = {
        tuple(sorted(layout.items())): (layout, literals)
        for layout, literals in candidates
    }
    if len(unique) != 1:
        raise AcquisitionError(
            f"runtime metadata string literal layout is not unique ({len(unique)})"
        )
    return next(iter(unique.values()))


def _metadata_usage_pair_candidates(
    data: bytes,
    tables: list[dict[str, int]],
    *,
    string_literal_count: int,
    method_definition_count: int,
) -> list[tuple[dict[str, int], list[dict[str, int]]]]:
    candidates: list[tuple[dict[str, int], list[dict[str, int]]]] = []
    for table in tables:
        for stride in range(8, MAXIMUM_DEFINITION_STRIDE + 1, 4):
            if table["bytes"] % stride:
                continue
            count = table["bytes"] // stride
            if not count:
                continue
            probes = _probe_indexes(count)
            dwords = stride // 4
            for destination_dword in range(dwords):
                for encoded_dword in range(dwords):
                    if encoded_dword == destination_dword:
                        continue
                    probe_destinations: set[int] = set()
                    valid = True
                    for index in probes:
                        position = table["offset"] + index * stride
                        destination = struct.unpack_from(
                            "<I", data, position + destination_dword * 4
                        )[0]
                        encoded = struct.unpack_from(
                            "<I", data, position + encoded_dword * 4
                        )[0]
                        kind = encoded >> 29
                        source_index = encoded & 0x1FFFFFFF
                        if (
                            destination >= count
                            or destination in probe_destinations
                            or kind not in range(1, 7)
                            or kind == 5
                            and source_index >= string_literal_count
                            or kind == 3
                            and source_index >= method_definition_count
                        ):
                            valid = False
                            break
                        probe_destinations.add(destination)
                    if not valid:
                        continue
                    destinations: set[int] = set()
                    pairs: list[dict[str, int]] = []
                    for index in range(count):
                        position = table["offset"] + index * stride
                        destination = struct.unpack_from(
                            "<I", data, position + destination_dword * 4
                        )[0]
                        encoded = struct.unpack_from(
                            "<I", data, position + encoded_dword * 4
                        )[0]
                        kind = encoded >> 29
                        source_index = encoded & 0x1FFFFFFF
                        if (
                            destination >= count
                            or destination in destinations
                            or kind not in range(1, 7)
                            or kind == 5
                            and source_index >= string_literal_count
                            or kind == 3
                            and source_index >= method_definition_count
                        ):
                            valid = False
                            break
                        destinations.add(destination)
                        pairs.append(
                            {
                                "destination_index": destination,
                                "usage_kind": kind,
                                "source_index": source_index,
                            }
                        )
                    if not valid or destinations != set(range(count)):
                        continue
                    pairs.sort(key=lambda record: record["destination_index"])
                    candidates.append(
                        (
                            {
                                "pair_index": table["pair_index"],
                                "offset": table["offset"],
                                "bytes": table["bytes"],
                                "stride": stride,
                                "destination_dword_index": destination_dword,
                                "encoded_dword_index": encoded_dword,
                            },
                            pairs,
                        )
                    )
    return candidates


def _metadata_usage_list_layouts(
    data: bytes,
    tables: list[dict[str, int]],
    *,
    pair_table_index: int,
    pair_count: int,
) -> list[dict[str, int]]:
    layouts: list[dict[str, int]] = []
    for table in tables:
        if table["pair_index"] == pair_table_index:
            continue
        for stride in range(8, MAXIMUM_DEFINITION_STRIDE + 1, 4):
            if table["bytes"] % stride:
                continue
            list_count = table["bytes"] // stride
            if not list_count:
                continue
            dwords = stride // 4
            for start_dword in range(dwords):
                for count_dword in range(dwords):
                    if count_dword == start_dword:
                        continue
                    cursor = 0
                    valid = True
                    for index in range(list_count):
                        position = table["offset"] + index * stride
                        start = struct.unpack_from(
                            "<I", data, position + start_dword * 4
                        )[0]
                        count = struct.unpack_from(
                            "<I", data, position + count_dword * 4
                        )[0]
                        if start != cursor or count > pair_count - cursor:
                            valid = False
                            break
                        cursor += count
                    if not valid or cursor != pair_count:
                        continue
                    layouts.append(
                        {
                            "pair_index": table["pair_index"],
                            "offset": table["offset"],
                            "bytes": table["bytes"],
                            "stride": stride,
                            "list_count": list_count,
                            "start_dword_index": start_dword,
                            "count_dword_index": count_dword,
                        }
                    )
    return layouts


def _unique_metadata_usages(
    data: bytes,
    tables: list[dict[str, int]],
    *,
    string_literal_count: int,
    method_definition_count: int,
) -> tuple[dict[str, Any], list[dict[str, int]]]:
    matches: list[tuple[dict[str, Any], list[dict[str, int]]]] = []
    for pair_layout, pairs in _metadata_usage_pair_candidates(
        data,
        tables,
        string_literal_count=string_literal_count,
        method_definition_count=method_definition_count,
    ):
        list_layouts = _metadata_usage_list_layouts(
            data,
            tables,
            pair_table_index=pair_layout["pair_index"],
            pair_count=len(pairs),
        )
        for list_layout in list_layouts:
            matches.append(
                (
                    {"pairs": pair_layout, "lists": list_layout},
                    pairs,
                )
            )
    unique = {
        (
            tuple(sorted(layout["pairs"].items())),
            tuple(sorted(layout["lists"].items())),
        ): (layout, pairs)
        for layout, pairs in matches
    }
    if len(unique) != 1:
        raise AcquisitionError(
            f"runtime metadata usage layout is not unique ({len(unique)})"
        )
    return next(iter(unique.values()))


def _unique_layout(
    candidates: list[dict[str, int]], *, label: str
) -> dict[str, int]:
    unique = {tuple(sorted(candidate.items())): candidate for candidate in candidates}
    if len(unique) != 1:
        raise AcquisitionError(
            f"runtime metadata {label} layout is not unique ({len(unique)})"
        )
    return next(iter(unique.values()))


def _runtime_records(
    identities: dict[str, Any],
    details: dict[str, Any],
) -> tuple[
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[dict[str, Any]],
    list[dict[str, Any]],
]:
    types: list[dict[str, Any]] = []
    fields: list[dict[str, Any]] = []
    methods: list[dict[str, Any]] = []
    parameters: list[dict[str, Any]] = []
    properties: list[dict[str, Any]] = []
    events: list[dict[str, Any]] = []
    for identity, detail in zip(identities["types"], details["types"], strict=True):
        assembly_index = identity["assembly_index"]
        type_index = identity["type_index"]
        types.append(
            {
                "identity": type_index,
                "assembly_index": assembly_index,
                "type_index": type_index,
                "name": identity["name"],
                "namespace": identity["namespace"],
                "attributes": identity["attributes"],
            }
        )
        for field_index, field in enumerate(detail["fields"]):
            fields.append(
                {
                    "identity": (type_index, field_index),
                    "assembly_index": assembly_index,
                    "type_index": type_index,
                    "member_index": field_index,
                    "name": field["name"],
                    "token": field["metadata_token"],
                }
            )
        type_methods = [*detail["methods"], *detail["constructors"]]
        for method_index, method in enumerate(type_methods):
            methods.append(
                {
                    "identity": (type_index, method_index),
                    "assembly_index": assembly_index,
                    "type_index": type_index,
                    "method_index": method_index,
                    "name": method["name"],
                    "token": method["metadata_token"],
                    "attributes": method["attributes"],
                }
            )
            for parameter_index, parameter in enumerate(method["parameters"]):
                parameters.append(
                    {
                        "identity": (type_index, method_index, parameter_index),
                        "assembly_index": assembly_index,
                        "type_index": type_index,
                        "method_index": method_index,
                        "method_token": method["metadata_token"],
                        "parameter_index": parameter_index,
                        "name": parameter["name"],
                    }
                )
        for property_index, property_record in enumerate(detail["properties"]):
            properties.append(
                {
                    "identity": (type_index, property_index),
                    "assembly_index": assembly_index,
                    "type_index": type_index,
                    "property_index": property_index,
                    "name": property_record["name"],
                    "token": property_record["metadata_token"],
                }
            )
        for event_index, event in enumerate(detail["events"]):
            events.append(
                {
                    "identity": (type_index, event_index),
                    "assembly_index": assembly_index,
                    "type_index": type_index,
                    "event_index": event_index,
                    "name": event["name"],
                    "token": event["metadata_token"],
                }
            )
    if len(types) != identities["type_count"]:
        raise ContractViolation("runtime type definition inventory is inconsistent")
    if len(fields) != details["counts"]["fields"]:
        raise ContractViolation("runtime field definition inventory is inconsistent")
    if len(methods) != (
        details["counts"]["methods"] + details["counts"]["constructors"]
    ):
        raise ContractViolation("runtime method definition inventory is inconsistent")
    if len(parameters) != details["parameter_count"]:
        raise ContractViolation("runtime parameter definition inventory is inconsistent")
    if len(properties) != details["counts"]["properties"]:
        raise ContractViolation("runtime property definition inventory is inconsistent")
    if len(events) != details["counts"]["events"]:
        raise ContractViolation("runtime event definition inventory is inconsistent")
    return types, fields, methods, parameters, properties, events


def discover_runtime_metadata_mapping(
    *,
    metadata_path: Path,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    member_detail_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    metadata_path = metadata_path.expanduser().resolve()
    if not metadata_path.is_file() or metadata_path.is_symlink():
        raise AcquisitionError("runtime metadata definition source is unavailable")
    if owner_only_path_bits(metadata_path):
        raise AcquisitionError("runtime metadata definition source is not owner-only")
    try:
        data = metadata_path.read_bytes()
    except OSError as error:
        raise AcquisitionError("runtime metadata definition source is unreadable") from error
    version, header_bytes, tables = _metadata_tables(data)
    identities = load_runtime_type_identity_observation(
        type_identity_observation_path,
        type_observation_path=type_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    details = load_runtime_member_detail_observation(
        member_detail_observation_path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    types, fields, methods, parameters, properties, events = _runtime_records(
        identities, details
    )
    image_order, image_evidence = _unique_image_order(
        _image_order_candidates(data, tables, identities["assemblies"])
    )
    assembly_rank = {
        assembly_index: rank for rank, assembly_index in enumerate(image_order)
    }
    type_order = sorted(
        types,
        key=lambda record: (
            assembly_rank[record["assembly_index"]],
            record["type_index"],
        ),
    )
    field_order = sorted(
        fields,
        key=lambda record: (
            assembly_rank[record["assembly_index"]],
            record["token"],
            record["type_index"],
            record["member_index"],
        ),
    )
    method_order = sorted(
        methods,
        key=lambda record: (
            assembly_rank[record["assembly_index"]],
            record["token"],
            record["type_index"],
            record["method_index"],
        ),
    )
    parameter_order = sorted(
        parameters,
        key=lambda record: (
            assembly_rank[record["assembly_index"]],
            record["method_token"],
            record["parameter_index"],
            record["type_index"],
            record["method_index"],
        ),
    )
    property_order = sorted(
        properties,
        key=lambda record: (
            assembly_rank[record["assembly_index"]],
            record["token"],
            record["type_index"],
            record["property_index"],
        ),
    )
    event_order = sorted(
        events,
        key=lambda record: (
            assembly_rank[record["assembly_index"]],
            record["token"],
            record["type_index"],
            record["event_index"],
        ),
    )
    type_layout = _unique_layout(
        _type_definition_layouts(data, tables, type_order),
        label="type definition",
    )
    field_layout = _unique_layout(
        _definition_layouts(data, tables, field_order, token_required=True),
        label="field definition",
    )
    method_layout = _unique_layout(
        _definition_layouts(data, tables, method_order, token_required=True),
        label="method definition",
    )
    parameter_layout = _unique_layout(
        _definition_layouts(data, tables, parameter_order, token_required=False),
        label="parameter definition",
    )
    property_layout = _unique_layout(
        _definition_layouts(data, tables, property_order, token_required=True),
        label="property definition",
    )
    event_layout = _unique_layout(
        _definition_layouts(data, tables, event_order, token_required=True),
        label="event definition",
    )
    string_literal_layout, string_literals = _unique_string_literals(
        _string_literal_candidates(data, tables)
    )
    metadata_usage_layout, metadata_usage_pairs = _unique_metadata_usages(
        data,
        tables,
        string_literal_count=len(string_literals),
        method_definition_count=len(method_order),
    )
    metadata_usage_kind_counts = {
        str(kind): sum(
            record["usage_kind"] == kind for record in metadata_usage_pairs
        )
        for kind in range(1, 7)
        if any(record["usage_kind"] == kind for record in metadata_usage_pairs)
    }
    type_offsets = {
        record["identity"]: (
            index,
            type_layout["record_offset"] + index * type_layout["record_stride"],
        )
        for index, record in enumerate(type_order)
    }
    field_offsets = {
        record["identity"]: field_layout["record_offset"]
        + index * field_layout["record_stride"]
        for index, record in enumerate(field_order)
    }
    method_offsets = {
        record["identity"]: method_layout["record_offset"]
        + index * method_layout["record_stride"]
        for index, record in enumerate(method_order)
    }
    method_definition_indexes = {
        record["identity"]: index
        for index, record in enumerate(method_order)
    }
    parameter_offsets = {
        record["identity"]: parameter_layout["record_offset"]
        + index * parameter_layout["record_stride"]
        for index, record in enumerate(parameter_order)
    }
    property_offsets = {
        record["identity"]: property_layout["record_offset"]
        + index * property_layout["record_stride"]
        for index, record in enumerate(property_order)
    }
    event_offsets = {
        record["identity"]: event_layout["record_offset"]
        + index * event_layout["record_stride"]
        for index, record in enumerate(event_order)
    }
    return {
        "schema": RUNTIME_METADATA_MAPPING_SCHEMA,
        "status": "complete",
        "target": identities["target"],
        "metadata": {
            **file_identity(metadata_path),
            "version_observed": version,
            "header_bytes_observed": header_bytes,
            "table_pair_count": (header_bytes - 8) // 8,
        },
        "bindings": {
            "type_identity": identities["identity"],
            "member_detail": details["identity"],
        },
        "image_order": image_order,
        "image_order_evidence": image_evidence,
        "type_layout": type_layout,
        "field_layout": field_layout,
        "method_layout": method_layout,
        "parameter_layout": parameter_layout,
        "property_layout": property_layout,
        "event_layout": event_layout,
        "string_literal_layout": string_literal_layout,
        "metadata_usage_layout": metadata_usage_layout,
        "types": [
            {
                "type_index": record["type_index"],
                "type_definition_index": type_offsets[record["identity"]][0],
                "metadata_offset": type_offsets[record["identity"]][1],
            }
            for record in types
        ],
        "fields": [
            {
                "type_index": record["type_index"],
                "field_index": record["member_index"],
                "metadata_offset": field_offsets[record["identity"]],
            }
            for record in fields
        ],
        "methods": [
            {
                "type_index": record["type_index"],
                "method_index": record["method_index"],
                "method_definition_index": method_definition_indexes[
                    record["identity"]
                ],
                "metadata_offset": method_offsets[record["identity"]],
            }
            for record in methods
        ],
        "parameters": [
            {
                "type_index": record["type_index"],
                "method_index": record["method_index"],
                "parameter_index": record["parameter_index"],
                "metadata_offset": parameter_offsets[record["identity"]],
            }
            for record in parameters
        ],
        "properties": [
            {
                "type_index": record["type_index"],
                "property_index": record["property_index"],
                "metadata_offset": property_offsets[record["identity"]],
            }
            for record in properties
        ],
        "events": [
            {
                "type_index": record["type_index"],
                "event_index": record["event_index"],
                "metadata_offset": event_offsets[record["identity"]],
            }
            for record in events
        ],
        "string_literals": string_literals,
        "metadata_usage_pairs": metadata_usage_pairs,
        "metadata_usage_kind_counts": metadata_usage_kind_counts,
        "counts": {
            "assembly_count": len(identities["assemblies"]),
            "type_count": len(types),
            "field_count": len(fields),
            "method_count": len(methods),
            "parameter_count": len(parameters),
            "property_count": len(properties),
            "event_count": len(events),
            "string_literal_count": len(string_literals),
            "metadata_usage_count": len(metadata_usage_pairs),
        },
        "fixed_metadata_version_used": False,
        "fixed_table_pair_index_used": False,
        "fixed_definition_stride_used": False,
        "saved_reference_generation_seed_used": False,
    }


def write_runtime_metadata_mapping(
    *,
    output: Path,
    **arguments: Any,
) -> dict[str, Any]:
    payload = discover_runtime_metadata_mapping(**arguments)
    output = output.expanduser().resolve()
    atomic_write_json(output, payload)
    output.chmod(0o600)
    if owner_only_path_bits(output):
        raise AcquisitionError("runtime metadata mapping is not owner-only")
    return {
        "schema": RUNTIME_METADATA_MAPPING_SCHEMA,
        "status": payload["status"],
        "target": payload["target"],
        "counts": payload["counts"],
        "image_order_candidate_count": len(payload["image_order_evidence"]),
        "type_layout": payload["type_layout"],
        "field_layout": payload["field_layout"],
        "method_layout": payload["method_layout"],
        "parameter_layout": payload["parameter_layout"],
        "property_layout": payload["property_layout"],
        "event_layout": payload["event_layout"],
        "string_literal_layout": payload["string_literal_layout"],
        "metadata_usage_layout": payload["metadata_usage_layout"],
        "metadata_usage_kind_counts": payload["metadata_usage_kind_counts"],
        "output": file_identity(output),
        "raw_runtime_objects_exposed": False,
    }
