import copy
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any, Mapping

from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity
from alpha.p02 import (
    _SCALARS,
    _atomic_write_text,
    _format_field,
    _format_rva,
    _json_text,
    dump_artifact_context,
    normalize_proto_items,
    proto_artifact_names,
    validate_runtime_proto_static_model_for_publication,
)


SEMANTIC_NAME_SCHEMA = "alpha.current-runtime-semantic-names/v3"
NAMEPROTO_RECEIPT_SCHEMA = "alpha.runtime-nameproto-output/v2"
_OBFUSCATED = re.compile(r"[A-Z]{10,16}\Z")
_IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\Z")
_WINDOWS_RESERVED = {
    "con", "prn", "aux", "nul",
    *(f"com{number}" for number in range(1, 10)),
    *(f"lpt{number}" for number in range(1, 10)),
}


def _stable_type_indexes(source: list[Mapping[str, Any]]) -> list[int]:
    indexes: list[int] = []
    seen: set[int] = set()
    for item in source:
        value = item.get("type_index_owner_only")
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise AcquisitionError("nameproto runtime type index is absent")
        if value in seen:
            raise AcquisitionError("nameproto runtime type index is duplicated")
        seen.add(value)
        indexes.append(value)
    return indexes


def _semantic_translation(
    source: list[Mapping[str, Any]], normalized: list[Mapping[str, Any]],
    static_model: Path | None = None,
    semantic_references: list[Path] | None = None,
) -> tuple[
    dict[str, str],
    list[dict[str, Any]],
    dict[str, Any],
    dict[str, dict[str, str]],
]:
    indexes = _stable_type_indexes(source)
    if static_model is not None:
        from alpha.p48 import infer_current_semantic_names

        semantic = infer_current_semantic_names(
            items=source,
            static_model=static_model,
            semantic_operational_classpath=None,
            semantic_references=semantic_references,
        )
        evidence = semantic.get("evidence")
        semantic_checks = semantic.get("checks")
        if (
            semantic.get("schema") != SEMANTIC_NAME_SCHEMA
            or semantic.get("status") != "complete"
            or not isinstance(evidence, Mapping)
            or evidence.get("status") != "complete"
            or not isinstance(semantic_checks, Mapping)
            or semantic_checks.get("all_types_named_once") is not True
            or semantic_checks.get("semantic_names_unique") is not True
        ):
            raise AcquisitionError(
                "nameproto current-process semantic evidence is unavailable"
            )
        rows = [dict(row) for row in semantic.get("translations", [])]
        if (
            len(rows) != len(normalized)
            or [row.get("original_name") for row in rows]
            != [item["name"] for item in normalized]
        ):
            raise AcquisitionError("nameproto runtime semantic domain differs")

        _apply_graph_context_names(normalized, rows)


        for row, item in zip(rows, normalized):
            if row.get("confidence") == "structural-fallback":
                row["semantic_name"] = item["name"]
                row["confidence"] = "runtime-name-preserved-no-semantic-evidence"
        priority = {
            "current-packet-endpoint": -1,
            "current-literal": 0,
            "current-metadata": 0,
            "current-callgraph": 0,
            "current-pair-inference": 0,
            "current-pair-response": 0,
            "current-runtime-function": 0,
            "inferred": 1,
            "runtime-graph-context": 2,
            "runtime-name-preserved-no-semantic-evidence": 2,
        }
        order = sorted(
            range(len(rows)),
            key=lambda offset: (priority.get(str(rows[offset].get("confidence")), 1), offset),
        )
        used: set[str] = set()
        used_files: set[str] = set()
        for offset in order:
            row = rows[offset]
            candidate = str(row.get("semantic_name", ""))
            index = indexes[offset]
            if (
                not _IDENTIFIER.fullmatch(candidate)
                or len(candidate.encode("utf-8")) > 180
                or candidate.casefold() in _WINDOWS_RESERVED
            ):
                candidate = f"RuntimeType{index}"
                row["confidence"] = "portable-runtime-index-fallback"
            stem = candidate
            if candidate in used or candidate.casefold() in used_files:
                candidate = f"{stem}Type{index}"
            suffix = 2
            while candidate in used or candidate.casefold() in used_files:
                candidate = f"{stem}Type{index}_{suffix}"
                suffix += 1
            row["semantic_name"] = candidate
            used.add(candidate)
            used_files.add(candidate.casefold())
        translation = {
            str(row["original_name"]): str(row["semantic_name"])
            for row in rows
        }
        if len(translation) != len(normalized) or len(set(translation.values())) != len(normalized):
            raise AcquisitionError("nameproto runtime semantic translation is incomplete")
        field_translations = {
            str(owner): {
                str(original): str(value)
                for original, value in fields.items()
            }
            for owner, fields in (semantic.get("field_translations") or {}).items()
        }
        semantic_evidence = dict(evidence)
        reference_evidence = semantic.get("reference_semantic_evidence")
        if isinstance(reference_evidence, Mapping):
            semantic_evidence["reference_semantic"] = dict(reference_evidence)
        return translation, rows, semantic_evidence, field_translations

    proposed: list[tuple[str, str]] = []
    for item, index in zip(normalized, indexes):
        original = str(item["name"])
        if (
            _IDENTIFIER.fullmatch(original)
            and not _OBFUSCATED.fullmatch(original)
            and len(original.encode("utf-8")) <= 180
            and original.casefold() not in _WINDOWS_RESERVED
        ):
            proposed.append((original, "runtime-readable"))
        elif item["kind"] == "message" and isinstance(item.get("cmd_id"), int):
            proposed.append((f"Command{item['cmd_id']}Message", "structural-fallback"))
        elif item["kind"] == "message":
            proposed.append((f"RuntimeData{abs(index)}Info", "structural-fallback"))
        else:
            proposed.append((f"RuntimeEnum{abs(index)}", "structural-fallback"))

    counts = Counter(name for name, _confidence in proposed)
    used: set[str] = set()
    used_filenames: set[str] = set()
    translation: dict[str, str] = {}
    rows: list[dict[str, Any]] = []
    for item, index, (base, confidence) in zip(normalized, indexes, proposed):
        candidate = base
        if counts[base] > 1 or candidate in used or candidate.casefold() in used_filenames:
            candidate = f"{base}Type{abs(index)}"
            confidence = "collision-safe-structural-fallback"
        suffix = 1
        stem = candidate
        while candidate in used or candidate.casefold() in used_filenames:
            candidate = f"{stem}_{suffix}"
            suffix += 1
        if not _IDENTIFIER.fullmatch(candidate):
            raise AcquisitionError("nameproto generated an invalid identifier")
        used.add(candidate)
        used_filenames.add(candidate.casefold())
        original = str(item["name"])
        translation[original] = candidate
        rows.append({
            "kind": item["kind"],
            "type_index_owner_only": index,
            "original_name": original,
            "semantic_name": candidate,
            "confidence": confidence,
            "meaning_verified": confidence == "runtime-readable",
            "cmd_id": item.get("cmd_id") if item["kind"] == "message" else None,
        })
    reference_evidence: dict[str, Any] = {"status": "not-requested"}
    field_translations: dict[str, dict[str, str]] = {}
    if semantic_references:
        from alpha.p48 import apply_reference_semantic_names

        field_translations, reference_evidence = apply_reference_semantic_names(
            items=[dict(item) for item in normalized],
            rows=rows,
            semantic_references=list(semantic_references),
        )
        claimed: set[str] = set()
        order = sorted(
            range(len(rows)),
            key=lambda offset: (
                0
                if str(rows[offset]["confidence"]).startswith(
                    ("current-", "reference-", "runtime-readable")
                )
                else 1,
                offset,
            ),
        )
        for offset in order:
            row = rows[offset]
            candidate = str(row["semantic_name"])
            unique = candidate
            duplicate = 2
            while unique in claimed:
                unique = f"{candidate}Type{row['type_index_owner_only']}_{duplicate}"
                duplicate += 1
            row["semantic_name"] = unique
            claimed.add(unique)
        translation = {
            str(row["original_name"]): str(row["semantic_name"]) for row in rows
        }
    if len(translation) != len(normalized) or len(set(translation.values())) != len(normalized):
        raise AcquisitionError("nameproto semantic translation is incomplete")
    return translation, rows, {
        "status": "not-required-for-model-only-test",
        "current_process_or_current_artifacts_only": True,
        "reference_semantic": reference_evidence,
    }, field_translations


def _field_context_token(field: Mapping[str, Any]) -> str:
    name = str(field.get("name", ""))
    if (
        _IDENTIFIER.fullmatch(name)
        and not _OBFUSCATED.fullmatch(name)
        and not re.fullmatch(r"field_?\d+", name, flags=re.IGNORECASE)
    ):
        words = [word for word in re.split(r"_+", name) if word]
        token = "".join(word[:1].upper() + word[1:] for word in words)
        if token and _IDENTIFIER.fullmatch(token):
            return token
    return f"Field{int(field['number'])}"


def _apply_graph_context_names(
    items: list[Mapping[str, Any]], rows: list[dict[str, Any]]
) -> None:
    by_name = {str(item["name"]): item for item in items}
    row_by_name = {str(row["original_name"]): row for row in rows}
    incoming: dict[str, list[dict[str, Any]]] = {
        name: [] for name in by_name
    }
    for parent in items:
        if parent["kind"] != "message":
            continue
        fields = list(parent.get("fields", []))
        for oneof in parent.get("oneofs", []):
            fields.extend(oneof.get("cases", []))
        for field in fields:
            targets = []
            if field.get("type") in by_name:
                targets.append(str(field["type"]))
            if field.get("value_type") in by_name:
                targets.append(str(field["value_type"]))
            for target in set(targets):
                incoming[target].append({
                    "parent": str(parent["name"]),
                    "field_number": int(field["number"]),
                    "field_name": str(field.get("name", "")),
                    "cardinality": str(field.get("cardinality", "singular")),
                    "map_value": field.get("value_type") == target,
                })

    unresolved = {
        str(row["original_name"])
        for row in rows
        if row.get("confidence") == "structural-fallback"
    }
    changed = True
    while changed:
        changed = False
        for name in sorted(tuple(unresolved)):
            child = by_name[name]
            proposals: dict[str, list[dict[str, Any]]] = {}
            for edge in incoming.get(name, []):
                parent_row = row_by_name[edge["parent"]]
                if parent_row.get("confidence") in {
                    "structural-fallback", "runtime-graph-context",
                }:
                    continue
                parent_name = str(parent_row["semantic_name"])
                token = _field_context_token({
                    "name": edge["field_name"],
                    "number": edge["field_number"],
                })
                if child["kind"] == "enum":
                    role = "Type"
                elif edge["map_value"]:
                    role = "Value"
                elif edge["cardinality"] == "repeated":
                    role = "Entry"
                else:
                    role = "Data"
                candidate = f"{parent_name}{token}{role}"
                if (
                    len(candidate.encode("utf-8")) <= 120
                    and _IDENTIFIER.fullmatch(candidate)
                ):
                    proposals.setdefault(candidate, []).append(edge)
            if len(proposals) != 1:
                continue
            candidate, evidence = next(iter(proposals.items()))
            row = row_by_name[name]
            row["semantic_name"] = candidate
            row["confidence"] = "runtime-graph-context"
            row["current_runtime_graph_evidence"] = evidence
            unresolved.remove(name)
            changed = True


def _rename_items(
    normalized: list[Mapping[str, Any]],
    translation: Mapping[str, str],
    field_translations: Mapping[str, Mapping[str, str]] | None = None,
) -> list[dict[str, Any]]:
    result = copy.deepcopy(normalized)
    for item in result:
        original_owner = item["name"]
        original = original_owner
        item["name"] = translation[original]
        item.pop("declaring_path", None)
        if item["kind"] != "message":
            continue
        fields = list(item["fields"])
        for oneof in item["oneofs"]:
            fields.extend(oneof["cases"])
        names = field_translations.get(original_owner, {}) if field_translations else {}
        if names:
            taken = {str(field["name"]) for field in fields}
            for field in fields:
                value = names.get(str(field["name"]))
                if value is None or value == field["name"]:
                    continue
                if value in taken:
                    continue
                taken.discard(str(field["name"]))
                taken.add(value)
                field["name"] = value
        for field in fields:
            for key in ("type", "key_type", "value_type"):
                if field.get(key) in translation:
                    field[key] = translation[field[key]]
    return normalize_proto_items(result)


def _applied_field_translations(
    named: list[Mapping[str, Any]],
    field_translations: Mapping[str, Mapping[str, str]],
) -> dict[str, dict[str, str]]:
    applied: dict[str, dict[str, str]] = {}
    for item in named:
        if item["kind"] != "message":
            continue
        names = {
            str(field["name"]) for field in item["fields"]
        } | {
            str(case["name"])
            for oneof in item["oneofs"]
            for case in oneof["cases"]
        }
        for owner, fields in field_translations.items():
            for original, semantic in fields.items():
                if semantic in names:
                    applied.setdefault(owner, {})[original] = semantic
    total = sum(len(fields) for fields in field_translations.values())
    adopted = sum(len(fields) for fields in applied.values())
    if adopted != total:
        raise AcquisitionError(
            "nameproto field name adoption did not reach the rendered corpus"
        )
    return applied


def _references(item: Mapping[str, Any], names: set[str]) -> list[str]:
    if item["kind"] != "message":
        return []
    fields = list(item["fields"])
    for oneof in item["oneofs"]:
        fields.extend(oneof["cases"])
    result: set[str] = set()
    for field in fields:
        values = [field.get("type"), field.get("key_type"), field.get("value_type")]
        for value in values:
            if value in names and value != item["name"] and value not in _SCALARS:
                result.add(str(value))
    return sorted(result)


def _components(items: list[Mapping[str, Any]]) -> list[list[str]]:
    names = {str(item["name"]) for item in items}
    graph = {str(item["name"]): _references(item, names) for item in items}
    cursor = 0
    indexes: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    stacked: set[str] = set()
    result: list[list[str]] = []

    def visit(name: str) -> None:
        nonlocal cursor
        indexes[name] = low[name] = cursor
        cursor += 1
        stack.append(name)
        stacked.add(name)
        for child in graph[name]:
            if child not in indexes:
                visit(child)
                low[name] = min(low[name], low[child])
            elif child in stacked:
                low[name] = min(low[name], indexes[child])
        if low[name] == indexes[name]:
            component: list[str] = []
            while True:
                child = stack.pop()
                stacked.remove(child)
                component.append(child)
                if child == name:
                    break
            result.append(sorted(component))

    for name in sorted(graph):
        if name not in indexes:
            visit(name)
    return sorted(result, key=lambda row: row[0])


def _declaration(item: Mapping[str, Any]) -> list[str]:
    if item["kind"] == "enum":
        lines = [f"enum {item['name']} {{"]
        numbers = [value["number"] for value in item["values"]]
        if len(numbers) != len(set(numbers)):
            lines.append("  option allow_alias = true;")
        for value in item["values"]:
            lines.append(f"  {value['name']} = {value['number']};")
        lines.append("}")
        return lines
    cmd_id = item.get("cmd_id")
    lines = [
        "// CmdId: "
        + (str(cmd_id) if isinstance(cmd_id, int) else "-")
        + " | MergeFrom: " + _format_rva(item.get("merge_from_rva"))
        + " | WriteTo: " + _format_rva(item.get("write_to_rva")),
        f"message {item['name']} {{",
    ]
    lines.extend(_format_field(field, indent="  ") for field in item["fields"])
    for oneof in item["oneofs"]:
        lines.append(f"  oneof {oneof['name']} {{")
        lines.extend(_format_field(case, indent="    ") for case in oneof["cases"])
        lines.append("  }")
    lines.append("}")
    return lines


def _preamble(context: Mapping[str, Any], java_package: str) -> list[str]:
    return [
        str(context["banner"]),
        str(context["discord_line"]),
        'syntax = "proto3";',
        f'option java_package = "{java_package}";',
        "",
    ]


def _render_corpus(
    items: list[Mapping[str, Any]], context: Mapping[str, Any], java_package: str
) -> tuple[dict[str, str], list[list[str]]]:
    names = {str(item["name"]) for item in items}
    by_name = {str(item["name"]): item for item in items}
    cyclic = [component for component in _components(items) if len(component) > 1]
    member_to_canonical = {name: row[0] for row in cyclic for name in row}
    rendered: dict[str, str] = {}
    for item in items:
        name = str(item["name"])
        canonical = member_to_canonical.get(name)
        if canonical is not None and name != canonical:
            lines = _preamble(context, java_package)
            lines.extend([f'import public "{canonical}.proto";', ""])
            rendered[f"{name}.proto"] = "\n".join(lines)
            continue
        component = [name] if canonical is None else next(row for row in cyclic if row[0] == canonical)
        external = sorted({
            reference
            for member in component
            for reference in _references(by_name[member], names)
            if reference not in component
        })
        lines = _preamble(context, java_package)
        lines.extend(f'import "{reference}.proto";' for reference in external)
        if external:
            lines.append("")
        for offset, member in enumerate(component):
            if offset:
                lines.append("")
            lines.extend(_declaration(by_name[member]))
        lines.append("")
        rendered[f"{name}.proto"] = "\n".join(lines)
    return rendered, cyclic


def _compile_declarations(directory: Path, filenames: set[str]) -> dict[tuple[str, str], bytes]:
    from google.protobuf.descriptor_pb2 import FileDescriptorSet

    with tempfile.TemporaryDirectory(prefix="alpha-nameproto-compile-") as temporary:
        temporary_root = Path(temporary)
        entry = temporary_root / "__alpha_all.proto"
        entry.write_text(
            'syntax = "proto3";\n'
            + "".join(f'import "{name}";\n' for name in sorted(filenames)),
            encoding="utf-8",
        )
        output = temporary_root / "descriptors.pb"
        process = subprocess.run(
            [sys.executable, "-m", "grpc_tools.protoc", f"--proto_path={temporary_root}",
             f"--proto_path={directory}", f"--descriptor_set_out={output}",
             "--include_imports", entry.name],
            cwd=temporary_root, capture_output=True, text=True, timeout=240, check=False,
        )
        if process.returncode or not output.is_file():
            reason = (
                process.stderr.strip().splitlines()[-1]
                if process.stderr.strip()
                else "compiler produced no diagnostic"
            )
            raise AcquisitionError(f"nameproto compilation failed: {reason}")
        descriptor_set = FileDescriptorSet.FromString(output.read_bytes())
    declarations: dict[tuple[str, str], bytes] = {}
    for descriptor in descriptor_set.file:
        if descriptor.name == entry.name:
            continue
        for message in descriptor.message_type:
            key = ("message", message.name)
            if key in declarations:
                raise AcquisitionError("nameproto compiled duplicate message")
            declarations[key] = message.SerializeToString(deterministic=True)
        for enum in descriptor.enum_type:
            key = ("enum", enum.name)
            if key in declarations:
                raise AcquisitionError("nameproto compiled duplicate enum")
            declarations[key] = enum.SerializeToString(deterministic=True)
    return declarations


def _validate_compiled_model(
    directory: Path, rendered: Mapping[str, str], items: list[Mapping[str, Any]],
    context: Mapping[str, Any], java_package: str,
) -> None:
    observed = _compile_declarations(directory, set(rendered))
    with tempfile.TemporaryDirectory(prefix="alpha-nameproto-canonical-") as temporary:
        root = Path(temporary)
        lines = _preamble(context, java_package)
        for item in items:
            lines.extend(_declaration(item))
            lines.append("")
        name = "canonical.proto"
        (root / name).write_text("\n".join(lines), encoding="utf-8")
        expected = _compile_declarations(root, {name})
    if observed != expected:
        raise AcquisitionError("nameproto compiled schema differs from renamed runtime model")


def write_nameproto_outputs(
    *, model: Mapping[str, Any], output_dir: Path,
    static_model: Path | None = None,
    nameeproto_previous: Path | None = None,
    nameeproto_rejected_ledger: Path | None = None,
    nameeproto_options: Mapping[str, Any] | None = None,
    semantic_references: list[Path] | None = None,
    allow_partial_wire_contract: bool = False,
) -> dict[str, Any]:
    validate_runtime_proto_static_model_for_publication(
        model, allow_partial_wire_contract=allow_partial_wire_contract,
    )
    source = [*model["messages_owner_only"], *model["enums_owner_only"]]
    normalized = normalize_proto_items(source)
    translation, rows, semantic_evidence, field_translations = _semantic_translation(
        source, normalized, static_model, semantic_references
    )
    named = _rename_items(normalized, translation, field_translations)
    applied_field_translations = _applied_field_translations(
        named, field_translations
    )
    reference_evidence = semantic_evidence.get("reference_semantic")
    semantic_evidence = dict(semantic_evidence)
    semantic_evidence.pop("reference_semantic", None)
    context = dump_artifact_context(model["target"])
    names = proto_artifact_names(model["target"])
    java_package = "emu.grasscutter.net.proto"
    root = output_dir / names["nameproto"]
    root.mkdir(parents=True, exist_ok=False)
    rendered, cyclic = _render_corpus(named, context, java_package)
    identities: dict[str, Any] = {}
    for filename, text in rendered.items():
        path = root / filename
        _atomic_write_text(path, text)
        identities[filename] = file_identity(path)
    _validate_compiled_model(root, rendered, named, context, java_package)
    confidence = Counter(row["confidence"] for row in rows)
    evidence_bound = sum(
        str(row.get("confidence", "")).startswith("current-")
        or row.get("confidence") == "runtime-readable"
        for row in rows
    )
    advisory_semantics = sum(
        row.get("confidence") in {"inferred", "runtime-graph-context"}
        for row in rows
    )
    opaque_runtime_identity = sum(
        row.get("confidence") in {
            "runtime-name-preserved-no-semantic-evidence",
            "portable-runtime-index-fallback",
            "structural-fallback",
            "collision-safe-structural-fallback",
        }
        for row in rows
    )
    manifest = {
        "schema": SEMANTIC_NAME_SCHEMA,
        "status": "complete",
        "dump_metadata": {key: context[key] for key in (
            "producer", "client_version", "client_build", "version_label",
            "banner", "discord", "executable_sha256",
        )},
        "type_count": len(named),
        "confidence_counts": dict(sorted(confidence.items())),
        "translations": rows,
        "current_runtime_semantic_evidence": semantic_evidence,
        "reference_semantic_evidence": reference_evidence,
        "field_translations": applied_field_translations,
        "field_translation_count": sum(
            len(fields) for fields in applied_field_translations.values()
        ),
        "cyclic_components": cyclic,
        "limitations": {
            "human_semantic_name_bound_count": evidence_bound,
            "opaque_runtime_identity_count": opaque_runtime_identity,
            "identity_classification_complete": (
                evidence_bound + advisory_semantics + opaque_runtime_identity
                == len(rows)
            ),
            "opaque_runtime_identities_preserve_runtime_names": True,
            "numeric_command_placeholders_emitted": False,
            "historic_inputs_used": bool(semantic_references),
            "historic_reference_used_as_candidate_catalog_only": bool(
                semantic_references
            ),
            "historic_wire_values_used": False,
            "historic_field_numbers_used": False,
        },
        "checks": {
            "one_filename_per_runtime_type": len(rendered) == len(named),
            "translation_total_and_injective": len(translation) == len(named) == len(set(translation.values())),
            "imports_derived_from_current_field_references": True,
            "cyclic_imports_collapsed_without_declaration_loss": True,
            "compiled_schema_matches_renamed_runtime_model": True,
            "current_runtime_semantic_evidence_bound": (
                static_model is None or semantic_evidence.get("status") == "complete"
            ),
            "reference_anchoring_unique_structure_only": True,
            "reference_field_names_verified_in_rendered_corpus": True,
        },
    }
    manifest_path = output_dir / names["semantic_names"]
    _atomic_write_text(manifest_path, _json_text(manifest))
    from alpha.p49 import write_nameeproto_outputs

    nameeproto = write_nameeproto_outputs(
        model=model,
        semantic_rows=rows,
        output_dir=output_dir,
        directory_name=names["nameeproto"],
        previous=nameeproto_previous,
        rejected_ledger_path=nameeproto_rejected_ledger,
        options=nameeproto_options,
    )
    manifest["checks"].update(nameeproto["checks"])
    manifest["checks"]["nameeproto_output_complete"] = True
    _atomic_write_text(manifest_path, _json_text(manifest))
    return {
        "schema": NAMEPROTO_RECEIPT_SCHEMA,
        "status": "complete",
        "directory": names["nameproto"],
        "manifest": file_identity(manifest_path),
        "files": identities,
        "nameeproto_output": nameeproto,
        "counts": {
            "type_count": len(named),
            "file_count": len(rendered),
            "cyclic_component_count": len(cyclic),
            "structural_fallback_count": sum("fallback" in row["confidence"] for row in rows),
            "runtime_evidence_bound_semantic_count": evidence_bound,
            "advisory_runtime_semantic_count": advisory_semantics,
            "opaque_runtime_identity_count": opaque_runtime_identity,
        },
        "checks": dict(manifest["checks"]),
    }


def verify_nameproto_outputs(
    *, model: Mapping[str, Any], output_dir: Path,
    static_model: Path | None = None,
    nameeproto_previous: Path | None = None,
    nameeproto_rejected_ledger: Path | None = None,
    nameeproto_options: Mapping[str, Any] | None = None,
    semantic_references: list[Path] | None = None,
) -> dict[str, Any]:
    names = proto_artifact_names(model["target"])
    root = output_dir / names["nameproto"]
    manifest_path = output_dir / names["semantic_names"]
    if root.is_symlink() or not root.is_dir() or manifest_path.is_symlink() or not manifest_path.is_file():
        raise AcquisitionError("nameproto output is missing or unsafe")
    source = [*model["messages_owner_only"], *model["enums_owner_only"]]
    normalized = normalize_proto_items(source)
    translation, rows, semantic_evidence, field_translations = _semantic_translation(
        source, normalized, static_model, semantic_references
    )
    named = _rename_items(normalized, translation, field_translations)
    _applied_field_translations(named, field_translations)
    context = dump_artifact_context(model["target"])
    rendered, cyclic = _render_corpus(named, context, "emu.grasscutter.net.proto")
    entries = list(root.iterdir())
    if {path.name for path in entries} != set(rendered) or any(
        not path.is_file() or path.is_symlink() for path in entries
    ):
        raise AcquisitionError("nameproto file domain differs from runtime model")
    for filename, expected in rendered.items():
        try:
            observed = (root / filename).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as error:
            raise AcquisitionError(f"nameproto file is unreadable: {filename}") from error
        if observed != expected:
            raise AcquisitionError(f"nameproto file differs from runtime model: {filename}")
    _validate_compiled_model(root, rendered, named, context, "emu.grasscutter.net.proto")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if (
        manifest.get("schema") != SEMANTIC_NAME_SCHEMA
        or manifest.get("status") != "complete"
        or manifest.get("translations") != rows
        or manifest.get("current_runtime_semantic_evidence") != semantic_evidence
        or manifest.get("cyclic_components") != cyclic
        or manifest.get("type_count") != len(named)
        or not all(manifest.get("checks", {}).values())
    ):
        raise AcquisitionError("nameproto semantic manifest differs from runtime model")
    from alpha.p49 import verify_nameeproto_outputs

    nameeproto = verify_nameeproto_outputs(
        model=model,
        semantic_rows=rows,
        output_dir=output_dir,
        directory_name=names["nameeproto"],
        previous=nameeproto_previous,
        rejected_ledger_path=nameeproto_rejected_ledger,
        options=nameeproto_options,
    )
    return {
        "status": "complete",
        "files": {filename: file_identity(root / filename) for filename in rendered},
        "manifest": file_identity(manifest_path),
        "nameeproto_output": nameeproto,
        "checks": {
            "nameproto_exactly_reconstructed": True,
            "nameproto_corpus_compiles": True,
            "nameproto_descriptor_agreement": True,
            "nameproto_type_domain_complete": True,
            "nameeproto_output_complete": True,
        },
    }
