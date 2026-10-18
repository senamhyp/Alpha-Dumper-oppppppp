import hashlib
import json
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity
from alpha.p02 import _atomic_write_text, _json_text


CORPUS_SCHEMA = "alpha.nameeproto-corpus/v1"
VERSION_DIFF_SCHEMA = "alpha.nameeproto-version-diff/v1"
REJECTED_LEDGER_SCHEMA = "alpha.nameeproto-rejected-candidates/v1"
SESSION_SEQUENCE_SCHEMA = "alpha.nameeproto-session-sequence/v1"
OPENSTATE_SCHEMA = "alpha.nameeproto-openstate/v1"

_SCALAR_WIRE = {
    **{name: 0 for name in (
        "int32", "int64", "uint32", "uint64", "sint32", "sint64", "bool",
    )},
    **{name: 1 for name in ("fixed64", "sfixed64", "double")},
    "string": 2,
    "bytes": 2,
    **{name: 5 for name in ("fixed32", "sfixed32", "float")},
}
_PACKABLE = frozenset(name for name in _SCALAR_WIRE if name not in {"string", "bytes"})
_WIRE_NAME = {0: "varint", 1: "fixed64", 2: "length_delimited", 5: "fixed32"}
_CMD_COMMENT = re.compile(r"//\s*CmdId:\s*(\d+|-)\s*\|")
_DECLARATION = re.compile(r"^(message|enum)\s+([A-Za-z_][A-Za-z0-9_]*)\s*\{")
_ENDPOINT_COMMENT = re.compile(
    r"MergeFrom:\s*(0x[0-9A-Fa-f]+|-)\s*\|\s*WriteTo:\s*(0x[0-9A-Fa-f]+|-)"
)
_DATA_ROOT = Path(__file__).with_name("data")


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _short(name: str) -> str:
    return str(name).rsplit(".", 1)[-1]


def _natural_wire(
    type_name: str, *, repeated: bool, packed: bool | None, enum_names: set[str],
) -> int:
    short = _short(type_name)
    if type_name in _SCALAR_WIRE:
        wire = _SCALAR_WIRE[type_name]
        packable = type_name in _PACKABLE
    elif short in enum_names:
        wire, packable = 0, True
    else:
        wire, packable = 2, False
    if repeated and packable and packed is not False:
        return 2
    return wire


def _field_signature(field: Mapping[str, Any]) -> list[Any]:
    return [
        int(field["number"]),
        str(field.get("cardinality", "singular")),
        int(field["wire_type"]),
        field.get("oneof"),
    ]


def _record_signature(fields: Sequence[Mapping[str, Any]]) -> str:
    payload = sorted(
        (int(field["number"]), str(field.get("cardinality", "singular")),
         int(field["wire_type"]), field.get("oneof"))
        for field in fields
    )
    return json.dumps(payload, separators=(",", ":"))


def _enum_signature(values: Sequence[Mapping[str, Any]]) -> str:
    payload = sorted(
        (int(value["number"]), str(value.get("name", ""))) for value in values
    )
    return json.dumps(payload, separators=(",", ":"))


def _record_name(logical: str | None, obfuscated: str) -> str:
    return str(logical) if logical else str(obfuscated)


def _load_json(path: Path, maximum_bytes: int = 512 * 1024 * 1024) -> Any:
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise AcquisitionError(f"corpus input is unreadable: {path.name}") from error
    if len(raw) > maximum_bytes:
        raise AcquisitionError(f"corpus input is too large: {path.name}")
    try:
        return json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AcquisitionError(f"corpus input is not json: {path.name}") from error


def _corpus_root(path: Path) -> Path:
    root = Path(path).expanduser()
    if root.is_symlink():
        raise AcquisitionError("corpus input is a symlink")
    root = root.resolve()
    if not root.exists():
        raise AcquisitionError(f"corpus input is missing: {root}")
    return root


def _nameeproto_directory(root: Path) -> Path | None:
    if root.is_file() and root.name == "all.nameeproto":
        return root
    if root.is_dir():
        candidate = root / "all.nameeproto"
        if candidate.is_file() and not candidate.is_symlink():
            return candidate
        if root.name.startswith("nameeproto_") and (root / "manifest.json").is_file():
            return root / "manifest.json"
    return None


def load_nameeproto_corpus(path: Path) -> dict[str, Any]:
    root = _corpus_root(path)
    source = _nameeproto_directory(root)
    if source is None:
        raise AcquisitionError("nameeproto corpus has no all.nameeproto")
    document = _load_json(source)
    if not isinstance(document, Mapping):
        raise AcquisitionError("nameeproto corpus is not an object")
    meta = document.get("dump_metadata") if isinstance(document.get("dump_metadata"), Mapping) else {}
    messages: list[dict[str, Any]] = []
    for row in document.get("messages") or []:
        fields = []
        for field in row.get("fields") or []:
            fields.append({
                "number": int(field["number"]),
                "name": str(field.get("runtime_name") or field.get("obfuscated_name") or ""),
                "protobuf_type": str(field.get("protobuf_type", "bytes")),
                "cardinality": (
                    "map" if field.get("map") else
                    "repeated" if field.get("repeated") else "singular"
                ),
                "packed": field.get("packed"),
                "map": bool(field.get("map")),
                "map_key_type": field.get("map_key_type"),
                "map_value_type": field.get("map_value_type"),
                "oneof": field.get("oneof"),
                "optional": bool(field.get("optional")),
                "wire_type": int(field.get("wire_type", 2)),
            })
        logical = row.get("logical_name")
        obfuscated = str(row.get("obfuscated_name") or row.get("runtime_name") or "")
        if not obfuscated:
            raise AcquisitionError("nameeproto message has no runtime identity")
        messages.append({
            "kind": "message",
            "logical_name": str(logical) if logical else None,
            "obfuscated_name": obfuscated,
            "name": _record_name(logical, obfuscated),
            "cmd_id": row.get("cmd_id") if isinstance(row.get("cmd_id"), int) else None,
            "fields": fields,
            "signature": _record_signature(fields),
            "merge_from": bool(isinstance(row.get("parser_entry"), Mapping)),
            "write_to": bool(isinstance(row.get("serializer_entry"), Mapping)),
            "source": "runtime-nameeproto",
        })
    enums: list[dict[str, Any]] = []
    for row in document.get("enums") or []:
        values = [
            {"name": str(value.get("name", "")), "number": int(value["number"])}
            for value in row.get("values") or []
        ]
        logical = row.get("logical_name")
        obfuscated = str(row.get("obfuscated_name") or row.get("runtime_name") or "")
        enums.append({
            "kind": "enum",
            "logical_name": str(logical) if logical else None,
            "obfuscated_name": obfuscated,
            "name": _record_name(logical, obfuscated),
            "cmd_id": None,
            "values": values,
            "signature": _enum_signature(values),
            "source": "runtime-nameeproto",
        })
    return {
        "schema": CORPUS_SCHEMA,
        "version": str(meta.get("client_version") or root.name),
        "client_executable_sha256": meta.get("executable_sha256"),
        "source": {
            "kind": "nameeproto-directory",
            **{key: value for key, value in file_identity(source).items()},
        },
        "messages": messages,
        "enums": enums,
    }


def _compile_proto_descriptor(proto: Path) -> Any:
    try:
        from google.protobuf import descriptor_pb2
    except ImportError as error:
        raise AcquisitionError("legacy proto import requires the protobuf runtime") from error
    with tempfile.TemporaryDirectory(prefix="alpha-nameeproto-import-") as temporary:
        output = Path(temporary) / "descriptor.pb"
        process = subprocess.run(
            [sys.executable, "-m", "grpc_tools.protoc",
             f"--proto_path={proto.parent}", f"--descriptor_set_out={output}",
             "--include_imports", proto.name],
            capture_output=True, text=True, timeout=900,
        )
        if process.returncode or not output.is_file():
            reason = (
                process.stderr.strip().splitlines()[-1]
                if process.stderr.strip() else "compiler produced no diagnostic"
            )
            raise AcquisitionError(f"legacy proto compilation failed: {reason}")
        descriptor = descriptor_pb2.FileDescriptorSet()
        descriptor.ParseFromString(output.read_bytes())
        return descriptor


def _comment_command_ids(text: str) -> dict[str, int]:
    commands: dict[str, int] = {}
    pending: int | None = None
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("//"):
            match = _CMD_COMMENT.search(stripped)
            if match:
                pending = int(match.group(1)) if match.group(1) != "-" else None
            continue
        declaration = _DECLARATION.match(stripped)
        if declaration and declaration.group(1) == "message" and pending is not None:
            commands.setdefault(declaration.group(2), pending)
        if declaration:
            pending = None
    return commands


def _legacy_proto_and_packet_ids(root: Path) -> tuple[Path, Path | None]:
    if root.is_file() and root.suffix == ".proto":
        candidate_ids = root.with_name("packetIds.json")
        return root, candidate_ids if candidate_ids.is_file() else None
    protos = sorted(
        path for path in root.glob("*.proto")
        if path.is_file() and not path.is_symlink()
    )
    preferred = [path for path in protos if path.name in {"Genshin.proto", "Genshin_sorted.proto"}]
    chosen = (preferred or protos)[:1]
    if not chosen:
        raise AcquisitionError("legacy dump has no proto file")
    identifiers = sorted(
        path for path in root.glob("*.json")
        if path.is_file() and not path.is_symlink()
        and path.name.lower().replace("_", "") in {"packetids.json", "packetid.json"}
    )
    return chosen[0], identifiers[0] if identifiers else None


def _declared_type_name(field: Any) -> str:
    from google.protobuf import descriptor_pb2

    raw = descriptor_pb2.FieldDescriptorProto.Type.Name(field.type)
    return raw[len("TYPE_"):].lower()


def _descriptor_field(
    field: Any, *, enum_names: set[str], map_entries: dict[str, Any],
    oneof_names: Sequence[str],
) -> dict[str, Any]:
    type_name = (
        field.type_name.lstrip(".") if field.type_name else _declared_type_name(field)
    )
    repeated = field.label == field.LABEL_REPEATED
    packed: bool | None = None
    if repeated:
        packed = bool(field.options.packed) if field.options.HasField("packed") else None
    oneof = None
    if field.HasField("oneof_index") and not field.proto3_optional:
        index = int(field.oneof_index)
        if 0 <= index < len(oneof_names):
            oneof = str(oneof_names[index])
    entry = map_entries.get(field.type_name.lstrip("."))
    record = {
        "number": int(field.number),
        "name": str(field.name),
        "protobuf_type": type_name,
        "cardinality": "singular",
        "packed": packed,
        "map": False,
        "map_key_type": None,
        "map_value_type": None,
        "oneof": oneof,
        "optional": bool(field.proto3_optional),
    }
    if entry is not None:
        keys = {inner.name: inner for inner in entry.field}
        record.update({
            "cardinality": "map",
            "map": True,
            "map_key_type": _declared_type_name(keys["key"]),
            "map_value_type": (
                keys["value"].type_name.lstrip(".") if keys["value"].type_name
                else _declared_type_name(keys["value"])
            ),
            "protobuf_type": "map",
            "wire_type": 2,
        })
        return record
    record["wire_type"] = _natural_wire(
        type_name, repeated=repeated, packed=packed, enum_names=enum_names,
    )
    record["cardinality"] = "repeated" if repeated else "singular"
    return record


def _descriptor_corpus(descriptor: Any, commands: Mapping[str, int]) -> dict[str, Any]:
    messages: list[dict[str, Any]] = []
    enums: list[dict[str, Any]] = []
    enum_names: set[str] = set()
    map_entries: dict[str, Any] = {}

    def declare(message: Any, prefix: str) -> None:
        full = f"{prefix}.{message.name}" if prefix else message.name
        for nested in message.nested_type:
            nested_full = f"{full}.{nested.name}"
            if nested.options.map_entry:
                map_entries[nested_full] = nested
            declare(nested, full)
        for enum in message.enum_type:
            enum_names.add(f"{full}.{enum.name}")
            enum_names.add(enum.name)

    for file in descriptor.file:
        for enum in file.enum_type:
            enum_names.add(f"{file.package}.{enum.name}" if file.package else enum.name)
            enum_names.add(enum.name)
        for message in file.message_type:
            declare(message, file.package)
    for file in descriptor.file:
        def walk(message: Any, prefix: str) -> None:
            full = f"{prefix}.{message.name}" if prefix else message.name
            for nested in message.nested_type:
                if not nested.options.map_entry:
                    walk(nested, full)
            fields = [
                _descriptor_field(
                    field, enum_names=enum_names, map_entries=map_entries,
                    oneof_names=[decl.name for decl in message.oneof_decl],
                )
                for field in message.field
            ]
            messages.append({
                "kind": "message",
                "logical_name": None,
                "obfuscated_name": full,
                "name": full,
                "cmd_id": commands.get(full) or commands.get(message.name),
                "fields": fields,
                "signature": _record_signature(fields),
                "merge_from": None,
                "write_to": None,
                "source": "legacy-proto-dump",
            })

        for message in file.message_type:
            walk(message, file.package)

    for file in descriptor.file:
        def walk_enum(enum: Any, prefix: str) -> None:
            full = f"{prefix}.{enum.name}" if prefix else enum.name
            values = [
                {"name": str(value.name), "number": int(value.number)}
                for value in enum.value
            ]
            enums.append({
                "kind": "enum",
                "logical_name": None,
                "obfuscated_name": full,
                "name": full,
                "cmd_id": None,
                "values": values,
                "signature": _enum_signature(values),
                "source": "legacy-proto-dump",
            })

        def walk_message_enums(message: Any, prefix: str) -> None:
            full = f"{prefix}.{message.name}" if prefix else message.name
            for enum in message.enum_type:
                walk_enum(enum, full)
            for nested in message.nested_type:
                walk_message_enums(nested, full)

        for enum in file.enum_type:
            walk_enum(enum, file.package)
        for message in file.message_type:
            walk_message_enums(message, file.package)

    messages = [row for row in messages if row["obfuscated_name"] not in map_entries]
    return {
        "schema": CORPUS_SCHEMA,
        "version": None,
        "client_executable_sha256": None,
        "source": {},
        "messages": messages,
        "enums": enums,
    }


def load_legacy_dump_corpus(path: Path, *, version: str | None = None) -> dict[str, Any]:
    root = _corpus_root(path)
    proto, packet_ids = _legacy_proto_and_packet_ids(root)
    try:
        text = proto.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeDecodeError) as error:
        raise AcquisitionError("legacy proto dump is unreadable") from error
    commands = _comment_command_ids(text)
    endpoint_comments = sum(bool(_ENDPOINT_COMMENT.search(line)) for line in text.splitlines())
    if packet_ids is not None:
        declared = _load_json(packet_ids)
        if not isinstance(declared, Mapping):
            raise AcquisitionError("packet id table is not an object")
        for name, identifier in declared.items():
            if isinstance(identifier, int):
                commands[str(name)] = int(identifier)
    if not commands:
        raise AcquisitionError("legacy dump exposes no command identity")
    corpus = _descriptor_corpus(_compile_proto_descriptor(proto), commands)
    corpus["version"] = version or root.name
    corpus["source"] = {
        "kind": "legacy-proto-dump",
        "proto": file_identity(proto),
        **({"packet_ids": file_identity(packet_ids)} if packet_ids is not None else {}),
    }
    corpus["declared_command_ids"] = len(commands)
    corpus["endpoint_comment_count"] = endpoint_comments
    return corpus


def load_corpus(path: Path, *, version: str | None = None) -> dict[str, Any]:
    root = _corpus_root(path)
    if _nameeproto_directory(root) is not None:
        corpus = load_nameeproto_corpus(root)
        if version:
            corpus["version"] = version
        return corpus
    return load_legacy_dump_corpus(root, version=version)


def corpus_from_analysis(analysis: Mapping[str, Any], *, version: str | None = None) -> dict[str, Any]:
    messages = []
    for row in analysis.get("messages") or []:
        fields = []
        for field in row.get("fields") or []:
            fields.append({
                "number": int(field["number"]),
                "name": str(field.get("runtime_name") or ""),
                "protobuf_type": str(field.get("protobuf_type", "bytes")),
                "cardinality": (
                    "map" if field.get("map") else
                    "repeated" if field.get("repeated") else "singular"
                ),
                "packed": field.get("packed"),
                "map": bool(field.get("map")),
                "map_key_type": field.get("map_key_type"),
                "map_value_type": field.get("map_value_type"),
                "oneof": field.get("oneof"),
                "optional": bool(field.get("optional")),
                "wire_type": int(field.get("wire_type", 2)),
            })
        messages.append({
            "kind": "message",
            "logical_name": row.get("logical_name"),
            "obfuscated_name": str(row.get("obfuscated_name") or ""),
            "name": _record_name(row.get("logical_name"), str(row.get("obfuscated_name"))),
            "cmd_id": row.get("cmd_id") if isinstance(row.get("cmd_id"), int) else None,
            "fields": fields,
            "signature": _record_signature(fields),
            "merge_from": bool(isinstance(row.get("parser_entry"), Mapping)),
            "write_to": bool(isinstance(row.get("serializer_entry"), Mapping)),
            "source": "runtime-nameeproto",
        })
    enums = []
    for row in analysis.get("enums") or []:
        values = [
            {"name": str(value.get("name", "")), "number": int(value["number"])}
            for value in row.get("values") or []
        ]
        enums.append({
            "kind": "enum",
            "logical_name": row.get("logical_name"),
            "obfuscated_name": str(row.get("obfuscated_name") or ""),
            "name": _record_name(row.get("logical_name"), str(row.get("obfuscated_name"))),
            "cmd_id": None,
            "values": values,
            "signature": _enum_signature(values),
            "source": "runtime-nameeproto",
        })
    context = analysis.get("dump_metadata") or {}
    return {
        "schema": CORPUS_SCHEMA,
        "version": version or context.get("client_version"),
        "client_executable_sha256": context.get("executable_sha256"),
        "source": {"kind": "runtime-analysis"},
        "messages": messages,
        "enums": enums,
    }


def _index(records: Iterable[Mapping[str, Any]], key: str) -> dict[Any, list[Mapping[str, Any]]]:
    result: dict[Any, list[Mapping[str, Any]]] = {}
    for row in records:
        result.setdefault(row.get(key), []).append(row)
    return result


def _unique(mapping: Mapping[Any, list[Mapping[str, Any]]], key: Any) -> Mapping[str, Any] | None:
    rows = mapping.get(key)
    return rows[0] if rows and len(rows) == 1 else None


def _field_changes(
    previous: Mapping[str, Any], current: Mapping[str, Any],
) -> tuple[list[dict[str, Any]], int]:
    old = {int(field["number"]): field for field in previous["fields"]}
    new = {int(field["number"]): field for field in current["fields"]}
    unmapped_old = {number: field for number, field in old.items() if number not in new}
    unmapped_new = {number: field for number, field in new.items() if number not in old}
    changes: list[dict[str, Any]] = []
    changed = 0
    for number in sorted(set(old) & set(new)):
        before, after = old[number], new[number]
        keys = [
            key for key in ("protobuf_type", "wire_type", "cardinality", "oneof")
            if (before.get(key) or None) != (after.get(key) or None)
        ]
        if keys:
            changed += 1
            changes.append({
                "role": str(after.get("name") or before.get("name") or number),
                "oldField": number,
                "newField": number,
                "oldType": before.get("protobuf_type"),
                "newType": after.get("protobuf_type"),
                "oldWireType": before.get("wire_type"),
                "newWireType": after.get("wire_type"),
                "change": ",".join(keys),
            })
    for number in sorted(unmapped_old):
        before = unmapped_old[number]
        candidates = [
            other for other in unmapped_new.values()
            if str(other.get("name") or "") == str(before.get("name") or "") != ""
            or (
                other.get("protobuf_type") == before.get("protobuf_type")
                and other.get("cardinality") == before.get("cardinality")
                and other.get("wire_type") == before.get("wire_type")
            )
        ]
        if len(candidates) == 1:
            after = candidates[0]
            unmapped_new.pop(int(after["number"]), None)
            changed += 1
            changes.append({
                "role": str(before.get("name") or number),
                "oldField": number,
                "newField": int(after["number"]),
                "oldType": before.get("protobuf_type"),
                "newType": after.get("protobuf_type"),
                "oldWireType": before.get("wire_type"),
                "newWireType": after.get("wire_type"),
                "change": "moved",
            })
            continue
        changed += 1
        changes.append({
            "role": str(before.get("name") or number),
            "oldField": number,
            "newField": None,
            "oldType": before.get("protobuf_type"),
            "newType": None,
            "oldWireType": before.get("wire_type"),
            "newWireType": None,
            "change": "removed",
        })
    for number in sorted(unmapped_new):
        after = unmapped_new[number]
        changed += 1
        changes.append({
            "role": str(after.get("name") or number),
            "oldField": None,
            "newField": number,
            "oldType": None,
            "newType": after.get("protobuf_type"),
            "oldWireType": None,
            "newWireType": after.get("wire_type"),
            "change": "added",
        })
    return changes, changed


def _server_update(class_: str, *, opcode: bool, schema: bool) -> str:
    if class_ == "resource_only":
        return "resource_only"
    if opcode and schema:
        return "opcode_and_schema"
    if opcode:
        return "opcode"
    if schema:
        return "schema"
    return "no_change"


def _diff_pair(
    previous: Mapping[str, Any], current: Mapping[str, Any], *, evidence: str,
    confidence: str, feature: str, resource_only: bool,
) -> dict[str, Any]:
    old_opcode = previous.get("cmd_id")
    new_opcode = current.get("cmd_id")
    opcode_changed = old_opcode != new_opcode and (
        isinstance(old_opcode, int) or isinstance(new_opcode, int)
    )
    mapping, changed = _field_changes(previous, current)
    schema_changed = previous["signature"] != current["signature"]
    update = _server_update(
        "resource_only" if resource_only else "wire_contract",
        opcode=opcode_changed, schema=schema_changed,
    )
    if (
        update not in {"resource_only", "no_change"}
        and feature == "authentication"
        and isinstance(new_opcode, int)
    ):
        update = "crypto_contract"
    return {
        "logicalName": current.get("logical_name") or previous.get("logical_name"),
        "oldLogicalName": previous.get("logical_name"),
        "newLogicalName": current.get("logical_name"),
        "oldObfuscatedName": previous.get("obfuscated_name"),
        "newObfuscatedName": current.get("obfuscated_name"),
        "oldOpcode": old_opcode,
        "newOpcode": new_opcode,
        "opcodeChanged": bool(opcode_changed),
        "schemaChanged": bool(schema_changed),
        "fieldMappings": mapping,
        "changedFieldCount": changed,
        "featureGroup": feature,
        "evidence": [{"kind": evidence}],
        "confidence": confidence,
        "serverUpdateRequired": update,
        "resourceDependency": [] if not resource_only else ["unreferenced-by-any-packet"],
    }


def _feature_of(name: str | None) -> str:
    from alpha.p49 import _feature

    return _feature(name)


def _packet_domain(corpus: Mapping[str, Any]) -> set[str]:
    names = {row["name"]: row for row in corpus["messages"]}
    short_index: dict[str, str] = {}
    for name in names:
        short_index.setdefault(_short(name), name)

    def resolve(type_name: str) -> str | None:
        if type_name in names:
            return type_name
        return short_index.get(_short(type_name))

    graph: dict[str, list[str]] = {}
    for name, row in names.items():
        children = set()
        for field in row.get("fields") or []:
            child = resolve(str(field.get("protobuf_type") or ""))
            if child is not None and child != name:
                children.add(child)
        graph[name] = sorted(children)
    by_name = {name for name, row in names.items() if row.get("cmd_id") is not None}
    reachable: set[str] = set(by_name)
    queue = list(by_name)
    while queue:
        name = queue.pop()
        for child in graph.get(name, ()):
            if child not in reachable:
                reachable.add(child)
                queue.append(child)
    return reachable


def _deep_fingerprints(
    corpus: Mapping[str, Any], anchors: Mapping[str, str], *, depth: int = 4,
) -> dict[str, str]:
    records = {str(row["name"]): row for row in corpus["messages"]}
    short: dict[str, str] = {}
    for name in records:
        short.setdefault(_short(name), name)
    memo: dict[tuple[str, int], str] = {}

    def child_of(type_name: str) -> str | None:
        if not type_name or type_name in _SCALAR_WIRE:
            return None
        if type_name in records:
            return type_name
        return short.get(_short(type_name))

    def shallow(record: Mapping[str, Any]) -> str:
        payload = sorted(
            [int(field["number"]), str(field.get("cardinality", "singular")),
             int(field["wire_type"]), field.get("oneof")]
            for field in record.get("fields") or []
        )
        return "S:" + hashlib.sha256(
            json.dumps(payload, separators=(",", ":")).encode()
        ).hexdigest()[:16]

    def compute(name: str, remaining: int, stack: frozenset[str]) -> str:
        if name in anchors:
            return "A:" + anchors[name]
        token = (name, remaining)
        if token in memo:
            return memo[token]
        record = records.get(name)
        if record is None:
            return "U:" + _short(name)
        if remaining <= 0 or name in stack:
            value = shallow(record)
            memo[token] = value
            return value
        parts = []
        for field in record.get("fields") or []:
            child = child_of(str(field.get("protobuf_type") or ""))
            if child is None:
                child_key = "T:" + str(field.get("protobuf_type"))
            elif child == name:
                child_key = "self"
            else:
                child_key = compute(child, remaining - 1, stack | {name})
            parts.append([
                int(field["number"]), str(field.get("cardinality", "singular")),
                int(field["wire_type"]), field.get("oneof"), child_key,
            ])
        value = "H:" + hashlib.sha256(
            json.dumps(sorted(parts), separators=(",", ":")).encode()
        ).hexdigest()[:32]
        memo[token] = value
        return value

    return {
        name: compute(name, depth, frozenset())
        for name in records
    }


def diff_corpora(previous: Mapping[str, Any], current: Mapping[str, Any]) -> dict[str, Any]:
    previous_domain = _packet_domain(previous)
    current_domain = _packet_domain(current)
    previous_by_name = _index(previous["messages"], "name")
    current_by_name = _index(current["messages"], "name")
    previous_by_opcode = _index(
        (row for row in previous["messages"] if isinstance(row.get("cmd_id"), int)), "cmd_id",
    )
    current_by_opcode = _index(
        (row for row in current["messages"] if isinstance(row.get("cmd_id"), int)), "cmd_id",
    )
    previous_by_signature = _index(previous["messages"], "signature")
    current_by_signature = _index(current["messages"], "signature")
    used_previous: set[int] = set()
    used_current: set[int] = set()
    pairs: list[tuple[Mapping[str, Any], Mapping[str, Any], str, str]] = []

    def previous_record(name: str) -> Mapping[str, Any] | None:
        return _unique(previous_by_name, name)

    def current_record(name: str) -> Mapping[str, Any] | None:
        return _unique(current_by_name, name)

    def resolve(record: Mapping[str, Any], type_name: str, lookup: Any) -> Mapping[str, Any] | None:
        if type_name in _SCALAR_WIRE:
            return None
        found = lookup(type_name)
        if found is not None:
            return found
        short = _short(type_name)
        return lookup(short) if short != type_name else None

    def take(
        before: Mapping[str, Any] | None, after: Mapping[str, Any] | None,
        evidence: str, confidence: str, *, same_role: bool = False,
    ) -> bool:
        if before is None or after is None:
            return False
        if id(before) in used_previous or id(after) in used_current:
            return False
        if same_role and (before.get("cmd_id") is None) != (after.get("cmd_id") is None):
            return False
        used_previous.add(id(before))
        used_current.add(id(after))
        pairs.append((before, after, evidence, confidence))
        return True

    for record in current["messages"]:
        if record.get("logical_name"):
            take(
                _unique(previous_by_name, record["logical_name"]), record,
                "logical-name", "confirmed",
            )
    for record in current["messages"]:
        if id(record) in used_current or not isinstance(record.get("cmd_id"), int):
            continue
        candidates = previous_by_opcode.get(record["cmd_id"]) or []
        if not candidates:
            continue
        exact = [row for row in candidates if row["signature"] == record["signature"]]
        if len(exact) == 1:
            take(exact[0], record, "command-id-and-signature", "confirmed")
        elif len(candidates) == 1:
            take(candidates[0], record, "command-id", "high")
    for record in current["messages"]:
        if id(record) in used_current:
            continue
        take(
            _unique(previous_by_name, record["obfuscated_name"]), record,
            "obfuscated-name", "high",
        )
    for record in current["messages"]:
        if id(record) in used_current:
            continue
        take(
            _unique(previous_by_signature, record["signature"]), record,
            "structural-signature", "medium", same_role=True,
        )


    while True:
        votes: list[tuple[str, str, str]] = []
        for before, after, evidence, confidence in pairs:
            old = {int(field["number"]): field for field in before["fields"]}
            new = {int(field["number"]): field for field in after["fields"]}
            for number in sorted(set(old) & set(new)):
                old_child = resolve(before, str(old[number].get("protobuf_type")), previous_record)
                new_child = resolve(after, str(new[number].get("protobuf_type")), current_record)
                if old_child is None or new_child is None:
                    continue
                if old_child is new_child:
                    continue
                votes.append((old_child["name"], new_child["name"], evidence))
        forward: dict[str, set[str]] = {}
        backward: dict[str, set[str]] = {}
        for old_name, new_name, _ in votes:
            forward.setdefault(old_name, set()).add(new_name)
            backward.setdefault(new_name, set()).add(old_name)
        progressed = False
        for old_name, targets in sorted(forward.items()):
            if len(targets) != 1:
                continue
            new_name = next(iter(targets))
            if len(backward.get(new_name, ())) != 1:
                continue
            before = previous_record(old_name) or previous_by_name.get(old_name, [None])[0]
            after = current_record(new_name) or current_by_name.get(new_name, [None])[0]
            if take(before, after, "parent-field-anchor", "medium", same_role=True):
                progressed = True
        if not progressed:
            break


    anchors = {before["name"]: after["name"] for before, after, _, _ in pairs}
    previous_deep = _deep_fingerprints(previous, anchors)
    current_deep = _deep_fingerprints(
        current, {name: name for name in anchors.values()},
    )
    previous_by_deep: dict[str, list[Mapping[str, Any]]] = {}
    for row in previous["messages"]:
        if id(row) in used_previous:
            continue
        previous_by_deep.setdefault(previous_deep[row["name"]], []).append(row)
    for record in current["messages"]:
        if id(record) in used_current:
            continue
        candidates = [
            row for row in previous_by_deep.get(current_deep[record["name"]], [])
            if id(row) not in used_previous
        ]
        if len(candidates) == 1:
            take(
                candidates[0], record, "deep-structural-fingerprint", "medium",
                same_role=True,
            )

    packets: list[dict[str, Any]] = []
    for before, after, evidence, confidence in pairs:
        resource_only = (
            before["name"] not in previous_domain and after["name"] not in current_domain
        )
        packets.append(_diff_pair(
            before, after, evidence=evidence, confidence=confidence,
            feature=_feature_of(after.get("logical_name") or before.get("logical_name")),
            resource_only=resource_only,
        ))
    packets.sort(key=lambda row: (
        row["newOpcode"] if isinstance(row["newOpcode"], int) else -1,
        str(row["logicalName"] or row["newObfuscatedName"]),
    ))
    added = [
        {
            "obfuscatedName": row["obfuscated_name"],
            "logicalName": row.get("logical_name"),
            "cmdId": row.get("cmd_id"),
            "fieldCount": len(row.get("fields") or []),
            "serverUpdateRequired": (
                "opcode_and_schema" if isinstance(row.get("cmd_id"), int)
                else "schema"
            ),
        }
        for row in current["messages"] if id(row) not in used_current
    ]
    removed = [
        {
            "obfuscatedName": row["obfuscated_name"],
            "logicalName": row.get("logical_name"),
            "cmdId": row.get("cmd_id"),
            "fieldCount": len(row.get("fields") or []),
            "serverUpdateRequired": "removal_review",
        }
        for row in previous["messages"] if id(row) not in used_previous
    ]
    added.sort(key=lambda row: str(row["obfuscatedName"]))
    removed.sort(key=lambda row: str(row["obfuscatedName"]))
    counts = {
        "previousMessageCount": len(previous["messages"]),
        "currentMessageCount": len(current["messages"]),
        "matchedCount": len(packets),
        "addedCount": len(added),
        "removedCount": len(removed),
        "opcodeChangedCount": sum(row["opcodeChanged"] for row in packets),
        "schemaChangedCount": sum(row["schemaChanged"] for row in packets),
        "obfuscationRenamedCount": sum(
            row["oldObfuscatedName"] != row["newObfuscatedName"]
            and not row["opcodeChanged"] and not row["schemaChanged"]
            for row in packets
        ),
        "unchangedCount": sum(
            not row["opcodeChanged"] and not row["schemaChanged"] for row in packets
        ),
        "serverUpdateRequiredCount": sum(
            row["serverUpdateRequired"] in {
                "opcode", "schema", "opcode_and_schema", "crypto_contract",
            }
            for row in packets
        ),
        "resourceOnlyCount": sum(
            row["serverUpdateRequired"] == "resource_only" for row in packets
        ),
        "confidence": {
            key: sum(row["confidence"] == key for row in packets)
            for key in ("confirmed", "high", "medium", "low")
        },
    }
    return {
        "schema": VERSION_DIFF_SCHEMA,
        "previous": {
            "version": previous.get("version"),
            "source": previous.get("source"),
            "messageCount": len(previous["messages"]),
        },
        "current": {
            "version": current.get("version"),
            "source": current.get("source"),
            "messageCount": len(current["messages"]),
        },
        "packets": packets,
        "added": added,
        "removed": removed,
        "counts": counts,
        "checks": {
            "matched_plus_added_covers_current": len(packets) + len(added) == len(current["messages"]),
            "matched_plus_removed_covers_previous": len(packets) + len(removed) == len(previous["messages"]),
            "resource_only_excluded_from_update_required": True,
        },
    }


def diff_corpus_paths(previous: Path, current: Path) -> dict[str, Any]:
    return diff_corpora(load_corpus(previous), load_corpus(current))


def empty_ledger() -> dict[str, Any]:
    return {"schema": REJECTED_LEDGER_SCHEMA, "entries": []}


def read_rejected_ledger(path: Path | None) -> dict[str, Any]:
    if path is None:
        return empty_ledger()
    root = Path(path).expanduser()
    if root.is_symlink():
        raise AcquisitionError("rejected candidate ledger is a symlink")
    if not root.is_file():
        raise AcquisitionError("rejected candidate ledger is missing")
    document = _load_json(root.resolve(), maximum_bytes=64 * 1024 * 1024)
    if (
        not isinstance(document, Mapping)
        or document.get("schema") != REJECTED_LEDGER_SCHEMA
        or not isinstance(document.get("entries"), list)
    ):
        raise AcquisitionError("rejected candidate ledger schema differs")
    return dict(document)


def write_rejected_ledger(path: Path, ledger: Mapping[str, Any]) -> None:
    entries = sorted(
        ledger.get("entries") or [],
        key=lambda row: (
            str(row.get("version", "")), str(row.get("message", "")),
            str(row.get("candidate_logical_name", "")),
            int(row.get("candidate_opcode") or 0),
        ),
    )
    _atomic_write_text(
        Path(path),
        _json_text({
            "schema": REJECTED_LEDGER_SCHEMA,
            "entries": entries,
            "count": len(entries),
        }),
    )


def candidate_blocks(
    entry: Mapping[str, Any], *, version: str | None, client_hash: str | None,
    proto_source_sha256: str | None,
) -> bool:
    if entry.get("rejected") is not True or entry.get("retry_allowed") is True:
        return False
    if client_hash and entry.get("client_hash") == client_hash:
        return True
    if proto_source_sha256 and entry.get("proto_source_sha256") == proto_source_sha256:
        return True
    return bool(version) and entry.get("version") == version and not client_hash


def record_rejection(
    ledger: dict[str, Any], *, version: str | None, client_hash: str | None,
    proto_source_sha256: str | None, message: str, candidate_logical_name: str,
    candidate_opcode: Any, candidate_field_mapping: Sequence[Mapping[str, Any]],
    reason: str, test_result: str, client_reaction: str,
    retry_allowed: bool = False, timestamp: str | None = None,
) -> dict[str, Any]:
    entry = {
        "version": version,
        "client_hash": client_hash,
        "proto_source_sha256": proto_source_sha256,
        "message": message,
        "candidate_logical_name": candidate_logical_name,
        "candidate_opcode": candidate_opcode,
        "candidate_field_mapping": [dict(row) for row in candidate_field_mapping],
        "reason": reason,
        "timestamp": timestamp or _now(),
        "test_result": test_result,
        "client_reaction": client_reaction,
        "rejected": True,
        "retry_allowed": bool(retry_allowed),
    }
    ledger.setdefault("schema", REJECTED_LEDGER_SCHEMA)
    ledger.setdefault("entries", []).append(entry)
    return entry


def _candidate_index(ledger: Mapping[str, Any]) -> dict[tuple[str, str], Mapping[str, Any]]:
    index: dict[tuple[str, str], Mapping[str, Any]] = {}
    for entry in ledger.get("entries") or []:
        key = (str(entry.get("message", "")), str(entry.get("candidate_logical_name", "")))
        index.setdefault(key, entry)
    return index


def candidate_mappings(
    previous: Mapping[str, Any], current: Mapping[str, Any], *,
    ledger: Mapping[str, Any] | None = None, client_hash: str | None = None,
    proto_source_sha256: str | None = None, maximum: int = 8,
) -> dict[str, dict[str, list[dict[str, Any]]]]:
    blocked = _candidate_index(ledger or empty_ledger())
    previous_by_signature = _index(previous["messages"], "signature")
    result: dict[str, dict[str, list[dict[str, Any]]]] = {}
    for row in current["messages"]:
        if row.get("logical_name") or row.get("cmd_id") is None:
            continue
        candidates = previous_by_signature.get(row["signature"]) or []
        accepted: list[dict[str, Any]] = []
        rejected: list[dict[str, Any]] = []
        for candidate in sorted(
            candidates,
            key=lambda item: str(item.get("logical_name") or item.get("obfuscated_name")),
        ):
            logical = candidate.get("logical_name") or candidate.get("obfuscated_name")
            evidence = {
                "candidate_logical_name": logical,
                "candidate_opcode": candidate.get("cmd_id"),
                "evidence": [{"kind": "structural-signature"}],
                "confidence": "low",
            }
            entry = blocked.get((row["name"], str(logical)))
            if entry is not None and candidate_blocks(
                entry, version=previous.get("version"),
                client_hash=client_hash, proto_source_sha256=proto_source_sha256,
            ):
                rejected.append({
                    **evidence,
                    "reason": entry.get("reason"),
                    "test_result": entry.get("test_result"),
                })
                continue
            accepted.append(evidence)
        if accepted or rejected:
            result[resp_key(row)] = {
                "candidates": accepted[:maximum],
                "rejected": rejected[:maximum],
                "candidate_count": len(accepted),
                "rejected_count": len(rejected),
            }
    return result


def resp_key(row: Mapping[str, Any]) -> str:
    return str(row.get("obfuscated_name") or row.get("name"))


def _load_seed(name: str) -> dict[str, Any]:
    path = _DATA_ROOT / name
    if not path.is_file():
        raise AcquisitionError(f"seed data is missing: {name}")
    return _load_json(path, maximum_bytes=8 * 1024 * 1024)


def session_sequence(analysis: Mapping[str, Any]) -> dict[str, Any]:
    seed = _load_seed("session-sequence-v1.json")
    by_logical = {
        str(row["logical_name"]): row
        for row in analysis["messages"] if row.get("logical_name")
    }
    states = []
    for state in seed["states"]:
        entries = []
        for name in state["packets"]:
            row = by_logical.get(name)
            if row is None:
                entries.append({
                    "logical_name": name,
                    "obfuscated_name": None,
                    "cmd_id": None,
                    "direction": None,
                    "binding_confidence": "not_bound_in_current_runtime",
                    "binding_classification_final": True,
                    "sequence_confidence": state.get("confidence", "specified"),
                    "note": "not present in the current runtime model",
                })
                continue
            entries.append({
                "logical_name": name,
                "obfuscated_name": row["obfuscated_name"],
                "cmd_id": row.get("cmd_id"),
                "direction": row.get("direction"),
                "binding_confidence": row.get("confidence"),
                "sequence_confidence": state.get("confidence", "specified"),
                "note": None,
            })
        states.append({
            "state": state["state"],
            "packets": entries,
            "resolved": sum(entry["binding_confidence"] == "confirmed" for entry in entries),
            "total": len(entries),
        })
    return {
        "schema": SESSION_SEQUENCE_SCHEMA,
        "seed": seed.get("schema"),
        "order_evidence": "specification seed; runtime model supplies opcode and identity binding only",
        "states": states,
        "not_bound_packets": sorted({
            entry["logical_name"]
            for state in states for entry in state["packets"]
            if entry["binding_confidence"] == "not_bound_in_current_runtime"
        }),
    }


def openstate(analysis: Mapping[str, Any]) -> dict[str, Any]:
    seed = _load_seed("openstate-v1.json")
    by_logical: dict[str, Mapping[str, Any]] = {
        str(row["logical_name"]): row
        for row in analysis["messages"] if row.get("logical_name")
    }
    by_logical.update({
        str(row["logical_name"]): row
        for row in analysis.get("enums") or [] if row.get("logical_name")
    })
    packets = []
    for name in seed["packets"]:
        row = by_logical.get(name)
        packets.append({
            "logical_name": name,
            "obfuscated_name": row["obfuscated_name"] if row else None,
            "cmd_id": row.get("cmd_id") if row else None,
            "direction": row.get("direction") if row else None,
            "binding_confidence": (
                row.get("confidence") if row else "not_bound_in_current_runtime"
            ),
            "binding_classification_final": True,
        })
    enum_row = next(
        (
            row for row in analysis.get("enums") or []
            if row.get("logical_name") == "OpenState"
        ),
        None,
    )
    return {
        "schema": OPENSTATE_SCHEMA,
        "wire_contract": {
            "packets": packets,
            "not_bound_packets": sorted(
                packet["logical_name"] for packet in packets
                if packet["binding_confidence"] == "not_bound_in_current_runtime"
            ),
            "enum": ({
                "logical_name": enum_row["logical_name"],
                "obfuscated_name": enum_row["obfuscated_name"],
                "values": [
                    {"name": value.get("name"), "number": value.get("number")}
                    for value in enum_row.get("values") or []
                ],
            } if enum_row else None),
        },
        "resource_metadata": {
            "status": "not_supplied",
            "reason": "no resource table supplied; open state meanings are not inferred",
            "id_roles": [
                {"role": role["role"], "meaning_source": role.get("meaning_source", "resource")}
                for role in seed["id_roles"]
            ],
        },
    }
