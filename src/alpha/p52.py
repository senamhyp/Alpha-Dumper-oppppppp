
import hashlib
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict
from dataclasses import dataclass, field as dataclass_field
from pathlib import Path
from typing import Any, Iterable, Mapping

from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity


REFERENCE_SEMANTIC_SCHEMA = "alpha.reference-semantic-names/v1"

_SCALAR_BY_DESCRIPTOR = {
    1: "double", 2: "float", 3: "int64", 4: "uint64", 5: "int32",
    6: "fixed64", 7: "fixed32", 8: "bool", 9: "string", 12: "bytes",
    13: "uint32", 15: "sfixed32", 16: "sfixed64", 17: "sint32", 18: "sint64",
}
_OBFUSCATED = re.compile(r"[A-Z]{10,16}\Z")
_LOWERCASE = re.compile(r"[a-z]")
_COMMAND_SUFFIXES = ("Req", "Rsp", "Notify")


@dataclass(frozen=True)
class _Field:
    number: int
    cardinality: str
    atom: str
    reference: str | None = None
    key_atom: str | None = None
    name: str = ""


@dataclass(frozen=True)
class _Shape:
    name: str
    kind: str
    fields: tuple[_Field, ...] = ()
    enum_numbers: tuple[int, ...] = ()
    enum_names: tuple[str, ...] = ()
    is_command: bool = dataclass_field(default=False)


def semantic_name(value: str) -> bool:
    return bool(_LOWERCASE.search(value)) and not _OBFUSCATED.fullmatch(value)


def _packet_reference(shape: _Shape) -> bool:
    return shape.name.endswith(_COMMAND_SUFFIXES)


def _reference_protos(root: Path) -> list[Path]:
    root = root.expanduser().resolve()
    if root.is_file() and root.suffix == ".proto" and not root.is_symlink():
        return [root]
    if not root.is_dir() or root.is_symlink():
        raise AcquisitionError("semantic reference is not a proto file or directory")
    for candidate in (
        root / "deobf" / "all-in-one.proto",
        root / "all-in-one.proto",
    ):
        if candidate.is_file() and not candidate.is_symlink():
            return [candidate]
    protos = sorted(
        path for path in root.glob("*.proto")
        if path.is_file() and not path.is_symlink()
    )
    if protos:
        return protos
    raise AcquisitionError("semantic reference directory has no proto files")


def _compile_descriptor(protos: list[Path]) -> Any:
    try:
        from google.protobuf import descriptor_pb2
    except ImportError as error:
        raise AcquisitionError(
            "semantic reference requires the protobuf runtime"
        ) from error
    proto_path = protos[0].parent
    if any(path.parent != proto_path for path in protos):
        raise AcquisitionError("semantic reference proto files span directories")
    with tempfile.TemporaryDirectory(prefix="alpha-semantic-reference-") as temporary:
        descriptor = Path(temporary) / "reference.pb"
        process = subprocess.run(
            [
                sys.executable, "-m", "grpc_tools.protoc",
                f"--proto_path={proto_path}",
                f"--descriptor_set_out={descriptor}",
                *[str(path) for path in protos],
            ],
            capture_output=True,
            text=True,
        )
        if process.returncode or not descriptor.is_file():
            reason = process.stderr.strip().splitlines()
            raise AcquisitionError(
                "semantic reference protobuf compilation failed: "
                + (reason[-1] if reason else "protoc returned no output")
            )
        result = descriptor_pb2.FileDescriptorSet()
        result.ParseFromString(descriptor.read_bytes())
        return result


def _descriptor_shapes(descriptor: Any) -> tuple[dict[str, _Shape], set[str]]:
    messages: dict[str, Any] = {}
    enums: dict[str, Any] = {}

    def collect_message(message: Any, prefix: str) -> None:
        full = f"{prefix}.{message.name}" if prefix else message.name
        messages[full] = message
        for enum in message.enum_type:
            enums[f"{full}.{enum.name}"] = enum
        for nested in message.nested_type:
            collect_message(nested, full)

    for file in descriptor.file:
        prefix = file.package
        for message in file.message_type:
            collect_message(message, prefix)
        for enum in file.enum_type:
            enums[f"{prefix}.{enum.name}" if prefix else enum.name] = enum
    map_entries = {
        name: value for name, value in messages.items() if value.options.map_entry
    }
    shapes: dict[str, _Shape] = {}
    for full, message in messages.items():
        if message.options.map_entry:
            continue
        fields: list[_Field] = []
        for item in message.field:
            cardinality = "repeated" if item.label == 3 else "singular"
            atom = _SCALAR_BY_DESCRIPTOR.get(item.type)
            reference = None
            key_atom = None
            target = item.type_name.lstrip(".")
            if target in map_entries:
                entry = map_entries[target]
                key, value = entry.field
                cardinality = "map"
                key_atom = _SCALAR_BY_DESCRIPTOR.get(
                    key.type, "enum" if key.type == 14 else "message"
                )
                atom = _SCALAR_BY_DESCRIPTOR.get(value.type)
                if atom is None:
                    atom = "enum" if value.type == 14 else "message"
                    reference = value.type_name.lstrip(".")
            elif atom is None:
                atom = "enum" if item.type == 14 else "message"
                reference = target
            if item.proto3_optional:
                cardinality = "optional"
            elif item.HasField("oneof_index"):
                cardinality = "oneof"
            fields.append(
                _Field(
                    int(item.number),
                    cardinality,
                    atom,
                    reference,
                    key_atom,
                    str(item.name),
                )
            )
        name = full.rsplit(".", 1)[-1]
        shapes[full] = _Shape(
            name,
            "message",
            tuple(sorted(fields, key=lambda value: value.number)),
            is_command=name.endswith(_COMMAND_SUFFIXES),
        )
    for full, enum in enums.items():
        shapes[full] = _Shape(
            full.rsplit(".", 1)[-1],
            "enum",
            enum_numbers=tuple(sorted(value.number for value in enum.value)),
            enum_names=tuple(value.name for value in enum.value),
        )
    semantic = {full for full, shape in shapes.items() if semantic_name(shape.name)}
    return shapes, semantic


def _reference_shapes(
    references: Iterable[Path],
) -> tuple[dict[str, _Shape], set[str], dict[str, Any]]:
    shapes: dict[str, _Shape] = {}
    semantic: set[str] = set()
    inputs: dict[str, Any] = {}
    for root in references:
        protos = _reference_protos(Path(root))
        candidate_shapes, candidate_semantic = _descriptor_shapes(
            _compile_descriptor(protos)
        )
        duplicate = set(shapes) & set(candidate_shapes)
        conflicting = sorted(
            name for name in duplicate
            if shapes[name] != candidate_shapes[name]
        )
        if conflicting:
            raise AcquisitionError(
                "semantic references define the same type twice with "
                "different structure: " + ", ".join(conflicting[:4])
            )
        for name in duplicate:
            candidate_shapes.pop(name)
        shapes.update(candidate_shapes)
        semantic |= candidate_semantic
        for proto in protos:
            inputs[str(proto)] = file_identity(proto)
    return shapes, semantic, {
        "status": "complete",
        "inputs": inputs,
        "reference_type_count": len(shapes),
        "semantic_reference_type_count": len(semantic),
    }


def _current_shapes(items: Iterable[Mapping[str, Any]]) -> dict[str, _Shape]:
    rows = list(items)
    kind = {str(row["name"]): str(row["kind"]) for row in rows}
    result: dict[str, _Shape] = {}
    for row in rows:
        name = str(row["name"])
        if row["kind"] == "enum":
            result[name] = _Shape(
                name,
                "enum",
                enum_numbers=tuple(
                    sorted(value["number"] for value in row["values"])
                ),
                enum_names=tuple(str(value["name"]) for value in row["values"]),
            )
            continue
        fields = list(row["fields"])
        oneof_numbers: set[int] = set()
        for oneof in row["oneofs"]:
            fields.extend(oneof["cases"])
            oneof_numbers.update(int(case["number"]) for case in oneof["cases"])
        converted: list[_Field] = []
        for item in fields:
            cardinality = str(item.get("cardinality", "singular"))
            if int(item["number"]) in oneof_numbers:
                cardinality = "oneof"
            elif item.get("optional") is True:
                cardinality = "optional"
            if cardinality == "map":
                value = str(item["value_type"])
                atom = value if value not in kind else kind[value]
                converted.append(
                    _Field(
                        int(item["number"]),
                        cardinality,
                        atom,
                        value if value in kind else None,
                        str(item["key_type"]),
                        str(item["name"]),
                    )
                )
            else:
                value = str(item["type"])
                atom = value if value not in kind else kind[value]
                converted.append(
                    _Field(
                        int(item["number"]),
                        cardinality,
                        atom,
                        value if value in kind else None,
                        None,
                        str(item["name"]),
                    )
                )
        result[name] = _Shape(
            name,
            "message",
            tuple(sorted(converted, key=lambda value: value.number)),
            is_command=row.get("cmd_id") is not None,
        )
    return result


def _local_signature(shape: _Shape) -> tuple[Any, ...]:
    if shape.kind == "enum":
        return ("enum", shape.enum_numbers)
    return (
        "message",
        tuple(
            (item.number, item.cardinality, item.atom, item.key_atom)
            for item in shape.fields
        ),
    )


def _wire_layout_signature(shape: _Shape) -> tuple[Any, ...]:
    if shape.kind == "enum":
        return ("enum", len(shape.enum_numbers))
    return (
        "message",
        tuple(
            sorted(
                (item.cardinality, item.atom, item.key_atom)
                for item in shape.fields
            )
        ),
    )


def _graph_children(
    shape: _Shape, signatures: Mapping[str, str]
) -> tuple[tuple[Any, ...], ...]:
    return tuple(
        (item.number, signatures.get(item.reference or "", item.atom))
        for item in shape.fields
        if item.reference is not None
    )


def _wire_graph_signatures(shapes: Mapping[str, _Shape]) -> dict[str, str]:
    local = {
        name: hashlib.sha256(repr(_wire_layout_signature(shape)).encode()).hexdigest()
        for name, shape in shapes.items()
    }
    return {
        name: hashlib.sha256(
            repr((
                _wire_layout_signature(shape),
                tuple(sorted(
                    (
                        item.cardinality,
                        item.atom,
                        local.get(item.reference or "", ""),
                    )
                    for item in shape.fields
                    if item.reference is not None
                )),
            )).encode()
        ).hexdigest()
        for name, shape in shapes.items()
    }


def _layout_similarity(left: _Shape, right: _Shape) -> float:
    a = Counter(
        (item.cardinality, item.atom, item.key_atom) for item in left.fields
    )
    b = Counter(
        (item.cardinality, item.atom, item.key_atom) for item in right.fields
    )
    union = sum((a | b).values())
    return sum((a & b).values()) / union if union else 1.0


def _field_links(parent: _Shape) -> dict[tuple[Any, ...], list[str]]:
    links: dict[tuple[Any, ...], list[str]] = defaultdict(list)
    for item in parent.fields:
        if item.reference is not None:
            links[
                (item.number, item.cardinality, item.atom, item.key_atom)
            ].append(item.reference)
    return links


def _anchored_signature(
    shape: _Shape, anchors: Mapping[str, str], *, numbered: bool
) -> tuple[Any, ...] | None:
    rows: list[tuple[Any, ...]] = []
    anchored = False
    for item in shape.fields:
        child = anchors.get(item.reference or "")
        anchored |= child is not None
        row = (item.cardinality, item.atom, item.key_atom, child)
        rows.append((item.number, *row) if numbered else row)
    if not anchored:
        return None
    return (shape.kind, tuple(sorted(rows, key=repr)))


def _field_signature(item: _Field, anchors: Mapping[str, str]) -> tuple[Any, ...]:
    return (
        item.cardinality,
        item.atom,
        item.key_atom,
        anchors.get(item.reference or ""),
    )


def infer_reference_semantic_names(
    *,
    items: list[Mapping[str, Any]],
    current_rows: list[Mapping[str, Any]],
    reference_paths: Iterable[Path] | None = None,
    descriptor_corpus: Any = None,
    descriptor_report: Mapping[str, Any] | None = None,
) -> tuple[
    dict[str, tuple[str, str, dict[str, Any]]],
    dict[str, dict[str, tuple[str, dict[str, Any]]]],
    dict[str, Any],
]:
    current = _current_shapes(items)
    if descriptor_corpus is not None:
        if reference_paths is not None or descriptor_report is None:
            raise AcquisitionError("semantic descriptor corpus binding is ambiguous")
        reference, semantic_reference = _descriptor_shapes(descriptor_corpus)
        report = dict(descriptor_report)
    else:
        if not reference_paths:
            raise AcquisitionError("semantic reference input is absent")
        reference, semantic_reference, report = _reference_shapes(reference_paths)
    reference_by_semantic: dict[str, list[str]] = defaultdict(list)
    for full in sorted(semantic_reference):
        reference_by_semantic[reference[full].name].append(full)
    baseline = {str(row["original_name"]): row for row in current_rows}
    current_to_reference: dict[str, str] = {}
    assigned_semantic: dict[str, str] = {}
    proposals: dict[str, tuple[str, str, dict[str, Any]]] = {}
    strong = {
        "current-operational", "current-literal", "current-metadata",
        "current-callgraph", "current-runtime-function",
        "current-pair-inference", "current-pair-response",
    }

    def assign(
        current_name: str, reference_name: str, confidence: str, basis: str
    ) -> bool:
        if (
            reference_name not in semantic_reference
            or current_name in current_to_reference
            or reference_name in current_to_reference.values()
        ):
            return False
        semantic = reference[reference_name].name
        if semantic in assigned_semantic.values():
            return False
        current_to_reference[current_name] = reference_name
        assigned_semantic[current_name] = semantic
        proposals[current_name] = (
            semantic,
            confidence,
            {
                "reference_type": reference_name,
                "reference_simple_name": semantic,
                "basis": basis,
                "reference_domain_type_count": len(reference),
            },
        )
        return True

    for original, row in baseline.items():
        if str(row.get("confidence")) not in strong:
            continue
        candidates = reference_by_semantic.get(str(row.get("semantic_name")), [])
        if len(candidates) != 1:
            continue
        candidate = candidates[0]
        if current[original].kind == reference[candidate].kind:
            assign(
                original,
                candidate,
                "reference-name-agreement",
                "current-runtime semantic name has one reference definition",
            )

    def propagate() -> int:
        additions = 0
        for current_parent, reference_parent in list(current_to_reference.items()):
            left = _field_links(current[current_parent])
            right = _field_links(reference[reference_parent])
            for signature in sorted(left.keys() & right.keys(), key=repr):
                if len(left[signature]) != 1 or len(right[signature]) != 1:
                    continue
                current_child = left[signature][0]
                reference_child = right[signature][0]
                if current_child not in current or reference_child not in reference:
                    continue
                if current[current_child].kind != reference[reference_child].kind:
                    continue
                additions += assign(
                    current_child,
                    reference_child,
                    "reference-anchored-structure",
                    f"unique field link from {reference[reference_parent].name}",
                )
        return additions

    while propagate():
        pass

    def match_unique_command_shapes(*, numbered: bool) -> int:
        signature = _local_signature if numbered else _wire_layout_signature
        current_groups: dict[tuple[Any, ...], list[str]] = defaultdict(list)
        reference_groups: dict[tuple[Any, ...], list[str]] = defaultdict(list)
        for name, shape in current.items():
            if name not in current_to_reference and shape.is_command:
                current_groups[signature(shape)].append(name)
        for name, shape in reference.items():
            if name not in current_to_reference.values():
                reference_groups[signature(shape)].append(name)
        additions = 0
        for reference_name in sorted(semantic_reference):
            shape = reference[reference_name]
            if (
                reference_name in current_to_reference.values()
                or not shape.is_command
                or (not numbered and len(shape.fields) < 2)
            ):
                continue
            key = signature(shape)
            if len(reference_groups[key]) == len(current_groups.get(key, ())) == 1:
                confidence = (
                    "reference-unique-command-structure"
                    if numbered
                    else "reference-unique-command-wire-layout"
                )
                if assign(
                    current_groups[key][0],
                    reference_name,
                    confidence,
                    "unique packet shape across the complete current and "
                    "reference domains",
                ):
                    additions += 1
        return additions

    command_structure_count = match_unique_command_shapes(numbered=True)
    command_layout_count = match_unique_command_shapes(numbered=False)
    while propagate():
        pass

    current_wire_graph = _wire_graph_signatures(current)
    reference_wire_graph = _wire_graph_signatures(reference)
    current_wire_groups: dict[str, list[str]] = defaultdict(list)
    reference_wire_groups: dict[str, list[str]] = defaultdict(list)
    for name, shape in current.items():
        if name not in current_to_reference and shape.is_command:
            current_wire_groups[current_wire_graph[name]].append(name)
    for name in reference:
        if name not in current_to_reference.values():
            reference_wire_groups[reference_wire_graph[name]].append(name)
    wire_graph_count = 0
    for reference_name in sorted(semantic_reference):
        shape = reference[reference_name]
        key = reference_wire_graph[reference_name]
        if (
            reference_name not in current_to_reference.values()
            and shape.is_command
            and len(reference_wire_groups[key])
            == len(current_wire_groups.get(key, ())) == 1
            and assign(
                current_wire_groups[key][0],
                reference_name,
                "reference-unique-command-wire-graph",
                "unique packet and one-hop referenced wire graph in both "
                "complete domains",
            )
        ):
            wire_graph_count += 1
    while propagate():
        pass

    mutual_fuzzy_count = 0
    available_current = [
        name for name, shape in current.items()
        if name not in current_to_reference
        and not shape.is_command
        and len(shape.fields) >= 8
    ]
    available_reference = [
        name for name in sorted(semantic_reference)
        if name not in current_to_reference.values()
        and not _packet_reference(reference[name])
        and reference[name].kind == "message"
        and len(reference[name].fields) >= 8
    ]
    current_rankings: dict[str, list[tuple[float, str]]] = {}
    for current_name in available_current:
        current_rankings[current_name] = sorted(
            (
                (_layout_similarity(current[current_name], reference[name]), name)
                for name in available_reference
            ),
            reverse=True,
        )
    for reference_name in available_reference:
        ranked = sorted(
            (
                (_layout_similarity(reference[reference_name], current[name]), name)
                for name in available_current
            ),
            reverse=True,
        )
        if len(ranked) < 2 or ranked[0][0] < 0.80 or ranked[0][0] - ranked[1][0] < 0.10:
            continue
        score, current_name = ranked[0]
        reverse_ranked = current_rankings[current_name]
        if (
            len(reverse_ranked) >= 2
            and reverse_ranked[0][1] == reference_name
            and reverse_ranked[0][0] - reverse_ranked[1][0] >= 0.10
            and assign(
                current_name,
                reference_name,
                "reference-mutual-fuzzy-structure",
                f"mutual unique large-layout match with {score:.3f} "
                "multiset overlap",
            )
        ):
            mutual_fuzzy_count += 1
    while propagate():
        pass

    fuzzy_anchor_count = 0
    inverse_now = {value: key for key, value in current_to_reference.items()}
    for reference_name in sorted(semantic_reference):
        shape = reference[reference_name]
        if (
            reference_name in inverse_now
            or shape.kind != "message"
            or len(shape.fields) < 3
        ):
            continue
        anchored_edges = [
            (item.cardinality, inverse_now[item.reference])
            for item in shape.fields
            if item.reference in inverse_now
        ]
        if not anchored_edges:
            continue
        candidates: list[tuple[float, str]] = []
        for current_name, candidate in current.items():
            if current_name in current_to_reference or candidate.kind != "message":
                continue
            if candidate.is_command != _packet_reference(shape):
                continue
            if not all(
                any(
                    item.cardinality == cardinality and item.reference == child
                    for item in candidate.fields
                )
                for cardinality, child in anchored_edges
            ):
                continue
            candidates.append((_layout_similarity(shape, candidate), current_name))
        candidates.sort(reverse=True)
        if (
            candidates
            and candidates[0][0] >= 0.75
            and (len(candidates) == 1 or candidates[0][0] - candidates[1][0] >= 0.10)
            and assign(
                candidates[0][1],
                reference_name,
                "reference-fuzzy-anchored-structure",
                "unique version-evolved structure sharing an aligned child; "
                f"overlap {candidates[0][0]:.3f}",
            )
        ):
            fuzzy_anchor_count += 1
    while propagate():
        pass

    reverse_anchor_count = 0
    for numbered in (True, False):
        current_groups: dict[tuple[Any, ...], list[str]] = defaultdict(list)
        reference_groups: dict[tuple[Any, ...], list[str]] = defaultdict(list)
        for name, shape in current.items():
            if name in current_to_reference:
                continue
            key = _anchored_signature(shape, current_to_reference, numbered=numbered)
            if key is not None:
                current_groups[(shape.is_command, key)].append(name)
        for name, shape in reference.items():
            if name in current_to_reference.values():
                continue
            key = _anchored_signature(shape, inverse_now, numbered=numbered)
            if key is not None:
                reference_groups[(shape.is_command, key)].append(name)
        for group, current_names in sorted(current_groups.items(), key=repr):
            reference_names = reference_groups.get(group, [])
            if len(current_names) == len(reference_names) == 1:
                if assign(
                    current_names[0],
                    reference_names[0],
                    "reference-reverse-anchored-structure",
                    "unique parent matching an already anchored child domain",
                ):
                    reverse_anchor_count += 1
                    inverse_now = {
                        value: key for key, value in current_to_reference.items()
                    }
    while propagate():
        pass

    field_proposals: dict[str, dict[str, tuple[str, dict[str, Any]]]] = {}
    field_name_count = 0
    ambiguous_field_shape_count = 0
    inverse_final = {value: key for key, value in current_to_reference.items()}
    for current_name, reference_name in sorted(current_to_reference.items()):
        current_shape = current[current_name]
        reference_shape = reference[reference_name]
        if current_shape.kind != "message" or reference_shape.kind != "message":
            continue
        current_by_signature: dict[tuple[Any, ...], list[_Field]] = defaultdict(list)
        for item in current_shape.fields:
            current_by_signature[
                _field_signature(item, current_to_reference)
            ].append(item)
        reference_by_signature: dict[tuple[Any, ...], list[_Field]] = defaultdict(list)
        for item in reference_shape.fields:
            reference_by_signature[
                _field_signature(item, inverse_final)
            ].append(item)
        current_names = {item.name for item in current_shape.fields}
        for signature, current_items in sorted(
            current_by_signature.items(), key=repr
        ):
            reference_items = reference_by_signature.get(signature, [])
            if len(current_items) != 1 or len(reference_items) != 1:
                if len(reference_items) > 1:
                    ambiguous_field_shape_count += 1
                continue
            current_item = current_items[0]
            reference_item = reference_items[0]
            if not semantic_name(reference_item.name):
                continue
            if semantic_name(current_item.name):
                continue
            if reference_item.name in current_names:
                continue
            field_proposals.setdefault(current_name, {})[current_item.name] = (
                reference_item.name,
                {
                    "reference_type": reference_name,
                    "reference_field_number": reference_item.number,
                    "basis": "unique field shape inside an anchored message",
                    "field_signature": repr(signature),
                },
            )
            field_name_count += 1
    report.update(
        {
            "schema": REFERENCE_SEMANTIC_SCHEMA,
            "current_type_count": len(current),
            "anchored_type_count": len(current_to_reference),
            "adopted_field_name_count": field_name_count,
            "ambiguous_field_shape_count": ambiguous_field_shape_count,
            "confidence_counts": dict(sorted(Counter(
                confidence for _name, confidence, _evidence in proposals.values()
            ).items())),
            "tier_counts": {
                "reference-name-agreement": sum(
                    1 for _n, c, _e in proposals.values()
                    if c == "reference-name-agreement"
                ),
                "reference-anchored-structure": sum(
                    1 for _n, c, _e in proposals.values()
                    if c == "reference-anchored-structure"
                ),
                "reference-unique-command-structure": command_structure_count,
                "reference-unique-command-wire-layout": command_layout_count,
                "reference-unique-command-wire-graph": wire_graph_count,
                "reference-mutual-fuzzy-structure": mutual_fuzzy_count,
                "reference-fuzzy-anchored-structure": fuzzy_anchor_count,
                "reference-reverse-anchored-structure": reverse_anchor_count,
            },
            "policy": {
                "ambiguous_candidates_rejected": True,
                "unique_match_required": True,
                "fixed_names_or_numbers_used": False,
                "reference_used_as_candidate_catalog_only": True,
            },
        }
    )
    return proposals, field_proposals, report
