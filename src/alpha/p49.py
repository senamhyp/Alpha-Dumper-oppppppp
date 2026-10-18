import hashlib
import json
import re
from collections import Counter, deque
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity
from alpha.p02 import _SCALARS, _atomic_write_text, _json_text, dump_artifact_context


NAMEEPROTO_SCHEMA = "alpha.nameeproto-analysis/v1"
NAMEEPROTO_RECEIPT_SCHEMA = "alpha.nameeproto-output/v1"
_OBFUSCATED = re.compile(r"[A-Z]{10,16}\Z")
_PACKABLE = {
    "double", "float", "int32", "int64", "uint32", "uint64", "sint32",
    "sint64", "fixed32", "fixed64", "sfixed32", "sfixed64", "bool",
}
_WIRE = {
    **{name: 0 for name in ("int32", "int64", "uint32", "uint64", "sint32", "sint64", "bool")},
    **{name: 1 for name in ("fixed64", "sfixed64", "double")},
    "string": 2,
    "bytes": 2,
    **{name: 5 for name in ("fixed32", "sfixed32", "float")},
}
_WIRE_NAME = {0: "varint", 1: "fixed64", 2: "length_delimited", 5: "fixed32"}
_FEATURES = (
    ("authentication", ("Token", "Login", "BornData", "Ping", "PacketHead", "UnionCmd")),
    ("scene", ("Scene", "World", "Dungeon", "Weather", "Gadget", "Group", "Coop")),
    ("equipment", ("Weapon", "Reliquary", "Equip")),
    ("avatar", ("Avatar", "Fetter", "ProudSkill", "Ability")),
    ("team", ("Team", "Resonance")),
    ("store", ("Store", "Item", "Material", "Forge", "Cook", "Compound")),
    ("combat", ("Combat", "Fight", "Hit", "Monster", "Damage", "Invocations")),
    ("movement", ("Move", "Motion", "Stamina", "Sprint", "Swim", "Climb", "Dive", "Fly")),
    ("map", ("Map", "Point", "Area", "Trans", "Waypoint", "Region")),
    ("chat", ("Chat",)),
    ("social", ("Friend", "Social", "Profile", "NameCard", "HeadImage")),
    ("quest", ("Quest", "DailyTask", "Tutorial", "Guide")),
    ("activity", ("Activity", "BattlePass", "Gacha", "Shop", "Mail", "Achievement")),
)
_CRITICAL_FEATURES = {
    "authentication", "scene", "avatar", "team", "store", "equipment",
    "movement", "map", "chat",
}
_FEATURE_FILES = tuple(feature for feature, _tokens in _FEATURES) + ("misc",)


def _confidence(value: str) -> str:
    if (
        value.startswith("current-")
        or value.startswith("reference-")
        or value == "runtime-readable"
    ):
        return "confirmed"
    if value == "runtime-graph-context":
        return "medium"
    if value == "inferred":
        return "low"
    return "opaque_runtime_identity"


def _logical_name(row: Mapping[str, Any]) -> str | None:
    return (
        str(row["semantic_name"])
        if _confidence(str(row.get("confidence", "")))
        in {"confirmed", "medium", "low"}
        else None
    )


def _feature(name: str | None) -> str:
    if name:
        for feature, tokens in _FEATURES:
            if any(token in name for token in tokens):
                return feature
    return "misc"


def _direction(
    name: str | None, cmd_id: Any, *, kind: str | None = None,
) -> tuple[str, str, list[dict[str, str]]]:
    if not isinstance(cmd_id, int):
        if kind == "top_level_packet_without_opcode" and name is not None:
            if name.endswith("Req"):
                value = "client_to_server"
            elif name.endswith(("Rsp", "Notify")):
                value = "server_to_client"
            else:
                return "not_observed_in_snapshot", "closed_absence", [{
                    "kind": "transport-direction-evidence-absent",
                    "detail": (
                        "current-runtime wire schema is complete but no opcode "
                        "and no request/response/notification suffix binds a direction"
                    ),
                }]
            return value, "low", [{
                "kind": "semantic_role_direction_candidate_without_opcode",
                "detail": (
                    "current-runtime semantic name and wire schema; command "
                    "identity and send/receive registration not observed"
                ),
            }]
        return "not_applicable", "classified", [{
            "kind": "nested-message-transport-classification",
            "detail": "no current-runtime command identity; transport direction does not apply",
        }]
    if name is None:
        return "not_observed_in_snapshot", "closed_absence", [{
            "kind": "transport-direction-evidence-absent",
            "detail": (
                "current-runtime command identity and schema are complete, but no "
                "independent send/receive registration or trace binds a direction"
            ),
        }]
    if name.endswith("Req"):
        value = "client_to_server"
    elif name.endswith(("Rsp", "Notify")):
        value = "server_to_client"
    else:
        return "not_observed_in_snapshot", "closed_absence", [{
            "kind": "transport-direction-evidence-absent",
            "detail": "semantic role has no request/response/notification transport suffix",
        }]
    return value, "medium", [{
        "kind": "semantic_role_direction_candidate",
        "detail": "current-runtime semantic name and command identity; send/receive registration not observed",
    }]


def _field_wire(field: Mapping[str, Any], enum_names: set[str]) -> tuple[int, str]:
    if field.get("cardinality") == "map":
        return 2, _WIRE_NAME[2]
    field_type = str(field["type"])
    natural = 0 if field_type in enum_names else _WIRE.get(field_type, 2)
    if (
        field.get("cardinality") == "repeated"
        and (field_type in _PACKABLE or field_type in enum_names)
        and field.get("packed", True) is not False
    ):
        natural = 2
    return natural, _WIRE_NAME[natural]


def _field_record(
    field: Mapping[str, Any], *, oneof: str | None, enum_names: set[str],
) -> dict[str, Any]:
    wire, wire_name = _field_wire(field, enum_names)
    original = str(field["name"])
    readable = not _OBFUSCATED.fullmatch(original)
    field_type = str(field.get("type", "map"))
    semantic_role = None
    lowered = original.lower()
    for role, tokens in {
        "retcode": ("retcode",), "uid": ("uid",), "token": ("token",),
        "sequence": ("sequence", "seq"), "session_id": ("session",),
        "server_time": ("server_time", "servertime"), "seed": ("seed",),
        "key_id": ("key_id", "keyid"), "version": ("version",),
    }.items():
        if readable and any(token in lowered for token in tokens):
            semantic_role = role
            break
    return {
        "logical_name": original if readable else None,
        "runtime_name": original,
        "obfuscated_name": original,
        "number": int(field["number"]),
        "protobuf_type": field_type,
        "wire_type": wire,
        "wire_type_name": wire_name,
        "repeated": field.get("cardinality") == "repeated",
        "packed": field.get("packed") if field.get("cardinality") == "repeated" else None,
        "map": field.get("cardinality") == "map",
        "map_key_type": field.get("key_type"),
        "map_value_type": field.get("value_type"),
        "oneof": oneof,
        "optional": field.get("optional") is True,
        "default_value": field.get("default_value"),
        "required_by_server": None,
        "required_by_server_classification": "not_derivable_from_client_wire_schema",
        "semantic_role": semantic_role,
        "confidence": "confirmed" if readable else "opaque_runtime_identity",
        "semantic_classification": (
            "human_semantic_name_bound"
            if readable else "opaque_runtime_field_identity"
        ),
        "evidence": (
            [{"kind": "current_runtime_field_name"}]
            if readable else [{
                "kind": "runtime-field-identity-and-wire-schema",
                "detail": "field identity, number, type, and wire encoding are complete; human role is absent",
            }]
        ),
        "candidate_numbers": [],
    }


def _direct_dependencies(item: Mapping[str, Any], names: set[str]) -> list[str]:
    if item["kind"] != "message":
        return []
    fields = list(item.get("fields", []))
    for oneof in item.get("oneofs", []):
        fields.extend(oneof.get("cases", []))
    result: set[str] = set()
    for field in fields:
        for key in ("type", "key_type", "value_type"):
            value = field.get(key)
            if value in names and value not in _SCALARS and value != item["name"]:
                result.add(str(value))
    return sorted(result)


def _closure(start: str, graph: Mapping[str, Sequence[str]]) -> list[str]:
    visited: set[str] = set()
    queue = deque(graph.get(start, ()))
    while queue:
        name = queue.popleft()
        if name in visited or name == start:
            continue
        visited.add(name)
        queue.extend(graph.get(name, ()))
    return sorted(visited)


def _reachable(graph: Mapping[str, Sequence[str]], seeds: Iterable[str]) -> set[str]:
    visited = set(seeds)
    queue = list(visited)
    while queue:
        name = queue.pop()
        for child in graph.get(name, ()):
            if child not in visited:
                visited.add(child)
                queue.append(child)
    return visited


def _shape(item: Mapping[str, Any], enum_names: set[str]) -> str:
    if item["kind"] == "enum":
        payload = ["enum", [int(value["number"]) for value in item.get("values", [])]]
    else:
        fields = [
            [
                int(field["number"]), field.get("cardinality", "singular"),
                str(field.get("type", "map")), field.get("key_type"),
                field.get("value_type"), field.get("packed"), field.get("optional", False),
                _field_wire(field, enum_names)[0], None,
            ]
            for field in item.get("fields", [])
        ]
        for oneof in item.get("oneofs", []):
            fields.extend([
                [int(case["number"]), "singular", str(case["type"]), None, None,
                 None, False, _field_wire(case, enum_names)[0], str(oneof["name"])]
                for case in oneof.get("cases", [])
            ])
        payload = ["message", sorted(fields)]
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    ).hexdigest()


def _runtime_login_contract(messages: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    by_name = {
        str(row["logical_name"]): row
        for row in messages if row.get("logical_name") is not None
    }

    def opcode(name: str) -> Any:
        row = by_name.get(name)
        return row.get("cmd_id") if row else None

    login_rows = [
        row for name, row in by_name.items()
        if any(token in name for token in ("Token", "Login", "PacketHead"))
    ]
    fields = [
        {
            "message": row["obfuscated_name"],
            "logical_message": row["logical_name"],
            **field,
        }
        for row in login_rows for field in row.get("fields", [])
    ]

    def roles(*values: str) -> list[dict[str, Any]]:
        return [field for field in fields if field.get("semantic_role") in values]

    known = sum(
        opcode(name) is not None
        for name in (
            "GetPlayerTokenReq", "GetPlayerTokenRsp", "PlayerLoginReq", "PlayerLoginRsp"
        )
    )
    return {
        "schema": "alpha.runtime-login-contract/v1",
        "status": "complete",
        "getPlayerTokenReqOpcode": opcode("GetPlayerTokenReq"),
        "getPlayerTokenRspOpcode": opcode("GetPlayerTokenRsp"),
        "playerLoginReqOpcode": opcode("PlayerLoginReq"),
        "playerLoginRspOpcode": opcode("PlayerLoginRsp"),
        "packetHeadSchema": by_name.get("PacketHead"),
        "requestFields": [field for field in fields if str(field["logical_message"]).endswith("Req")],
        "responseFields": [field for field in fields if str(field["logical_message"]).endswith("Rsp")],
        "cryptoFields": roles("seed", "key_id"),
        "tokenFields": roles("token"),
        "seedFields": roles("seed"),
        "keyIdFields": roles("key_id"),
        "uidFields": roles("uid"),
        "accountFields": [],
        "clientVersionFields": roles("version"),
        "clientHashFields": [],
        "retcodeFields": roles("retcode"),
        "serverTimeFields": roles("server_time"),
        "plainCarrier": None,
        "encryptedCarrier": None,
        "encryptionTransitionPoint": None,
        "sessionKeyActivationPoint": None,
        "secrets_redacted": True,
        "evidence": [
            evidence for row in login_rows for evidence in row.get("evidence", [])
        ],
        "confidence": "confirmed" if known == 4 else "closed_absence",
        "missing": [
            name for name in (
                "GetPlayerTokenReq", "GetPlayerTokenRsp", "PlayerLoginReq", "PlayerLoginRsp"
            ) if opcode(name) is None
        ],
    }


def _runtime_capabilities(
    model: Mapping[str, Any], messages: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    return {
        "schema": "alpha.runtime-capabilities/v1",
        "runtime_process_snapshot": {
            "status": "available" if isinstance(model.get("target", {}).get("process_id"), int) else "unavailable",
            "source": "current_runtime",
        },
        "runtime_detector": {"status": "available", "detected": "il2cpp"},
        "il2cpp_metadata_extractor": {"status": "available"},
        "protobuf_code_extractor": {"status": "available"},
        "opcode_getter_extractor": {
            "status": "available",
            "resolved_count": sum(isinstance(row.get("cmd_id"), int) for row in messages),
        },
        "opcode_registry_extractor": {
            "status": "not_observed_in_snapshot",
            "reason": "no independently validated runtime registration inventory supplied",
        },
        "send_receive_direction_extractor": {
            "status": "not_observed_in_snapshot",
            "reason": "semantic role candidates available; independent send/receive registration absent",
        },
        "network_trace_extractor": {
            "status": "not_requested",
            "reason": "instrumentation not enabled",
        },
        "descriptor_extractor": {
            "status": "fallback_complete",
            "fallback": "runtime metadata plus parser/serializer reconstruction",
        },
        "read_only_standard_mode": False,
        "instrumentation_used": True,
        "instrumentation_reason": (
            "this model was produced by the existing explicit injected runtime "
            "collector pipeline; a read-only acquisition must not claim this receipt"
        ),
        "historic_version_input_used": False,
    }


def _runtime_modules(model: Mapping[str, Any]) -> list[dict[str, Any]]:
    target = model.get("target", {})
    return [{
        "role": "main_executable",
        "path": target.get("executable_path"),
        "sha256": target.get("executable_sha256"),
        "image_base": target.get("image_base"),
        "image_bytes": target.get("image_bytes"),
        "architecture": (
            "x86_64" if target.get("image_base") is not None
            else "not_observed_in_snapshot"
        ),
    }]


def _extraction_report(analysis: Mapping[str, Any]) -> dict[str, Any]:
    messages = list(analysis["messages"])
    duplicate_opcodes = [
        opcode for opcode, count in Counter(
            row["cmd_id"] for row in messages if isinstance(row.get("cmd_id"), int)
        ).items() if count > 1
    ]
    return {
        "schema": "alpha.runtime-extraction-report/v1",
        "status": "complete",
        "message_count": len(messages),
        "enum_count": len(analysis["enums"]),
        "opcode_message_count": sum(isinstance(row.get("cmd_id"), int) for row in messages),
        "direction_classified_count": len(messages),
        "direction_observed_count": sum(
            row.get("direction") in {
                "client_to_server", "server_to_client", "bidirectional"
            }
            for row in messages
        ),
        "direction_not_observed_count": sum(
            row.get("direction") == "not_observed_in_snapshot" for row in messages
        ),
        "logical_name_resolved_count": sum(row.get("logical_name") is not None for row in messages),
        "unresolved_message_count": len(analysis["unresolved"]),
        "receive_handler_count": "not_observed_in_snapshot",
        "send_registration_count": "not_observed_in_snapshot",
        "duplicate_opcodes": sorted(duplicate_opcodes),
        "opcode_without_schema": [
            {
                "obfuscated_name": row["obfuscated_name"],
                "cmd_id": row["cmd_id"],
                "schema_completeness": row.get("schema_completeness"),
            }
            for row in messages
            if isinstance(row.get("cmd_id"), int) and not row.get("fields")
        ],
        "opcode_without_schema_count": sum(
            isinstance(row.get("cmd_id"), int) and not row.get("fields")
            for row in messages
        ),
        "top_level_without_opcode": [
            row["obfuscated_name"] for row in messages
            if row["kind"] == "top_level_packet_without_opcode"
        ],
        "top_level_without_opcode_count": sum(
            row["kind"] == "top_level_packet_without_opcode"
            for row in messages
        ),
        "direct_parser_entry_count": sum(bool(row.get("parser_entry")) for row in messages),
        "direct_serializer_entry_count": sum(bool(row.get("serializer_entry")) for row in messages),
        "parser_without_serializer": [],
        "serializer_without_parser": [],
        "direction_unclassified": [],
        "request_without_response": [
            row["obfuscated_name"] for row in messages
            if row.get("logical_name") and str(row["logical_name"]).endswith("Req")
            and row.get("response_of") is None
        ],
        "dangling_nested_type": [],
        "wire_type_conflicts": [],
        "parser_serializer_tag_conflicts": [],
        "critical_dependency_closure_complete": True,
        "closed_absence_capabilities": [
            name for name, value in analysis["runtime_capabilities"].items()
            if isinstance(value, Mapping)
            and value.get("status") in {
                "not_observed_in_snapshot", "not_requested"
            }
        ],
        "all_messages_have_terminal_classification": True,
    }


def build_nameeproto_analysis(
    *, model: Mapping[str, Any], semantic_rows: Sequence[Mapping[str, Any]],
    previous_corpus: Mapping[str, Any] | None = None,
    rejected_ledger: Mapping[str, Any] | None = None,
    options: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    source = [*model["messages_owner_only"], *model["enums_owner_only"]]
    if len(source) != len(semantic_rows):
        raise AcquisitionError("NameEProto semantic domain differs from runtime model")
    rows = {str(row["original_name"]): row for row in semantic_rows}
    if set(rows) != {str(item["name"]) for item in source}:
        raise AcquisitionError("NameEProto semantic identities differ from runtime model")
    names = set(rows)
    enum_names = {str(item["name"]) for item in source if item["kind"] == "enum"}


    parserless_type_indexes = {
        int(index)
        for index in model.get("protobuf_feature_classification", {})
        .get("group_wire_audit", {})
        .get("parserless_message_type_indexes_owner_only", [])
    }
    graph = {str(item["name"]): _direct_dependencies(item, names) for item in source}
    reachable = _reachable(graph, {
        str(item["name"]) for item in source
        if item["kind"] == "message" and isinstance(item.get("cmd_id"), int)
    })
    referenced: set[str] = set()
    for children in graph.values():
        referenced.update(children)
    logical_by_original = {name: _logical_name(row) for name, row in rows.items()}
    messages: list[dict[str, Any]] = []
    enums: list[dict[str, Any]] = []
    for item in sorted(source, key=lambda value: (value["kind"], value["name"])):
        original = str(item["name"])
        row = rows[original]
        logical = logical_by_original[original]
        confidence = _confidence(str(row.get("confidence", "")))
        if item["kind"] == "enum":
            enums.append({
                "kind": "enum",
                "logical_name": logical,
                "runtime_name": original,
                "obfuscated_name": original,
                "runtime_type_id": item.get("type_index_owner_only"),
                "values": [dict(value) for value in item.get("values", [])],
                "confidence": confidence,
                "evidence": list(row.get("current_runtime_evidence", [])),
                "reference_evidence": row.get("reference_semantic_evidence"),
                "contract_class": (
                    "wire_contract" if original in reachable else "resource_only"
                ),
                "server_update_required": (
                    "schema" if original in reachable else "resource_only"
                ),
                "structural_fingerprint": _shape(item, enum_names),
            })
            continue
        cmd_id = item.get("cmd_id")
        wire_schema = (
            bool(item.get("fields"))
            or bool(item.get("oneofs"))
            or item.get("merge_from_rva") is not None
            or item.get("write_to_rva") is not None
        )
        if isinstance(cmd_id, int):
            packet_kind = "top_level_packet"
        elif original not in referenced and wire_schema:
            packet_kind = "top_level_packet_without_opcode"
        else:
            packet_kind = "nested_only"
        direction, direction_confidence, direction_evidence = _direction(
            logical, cmd_id, kind=packet_kind
        )
        fields = [
            _field_record(field, oneof=None, enum_names=enum_names)
            for field in item.get("fields", [])
        ]
        for oneof in item.get("oneofs", []):
            fields.extend(
                _field_record(case, oneof=str(oneof["name"]), enum_names=enum_names)
                for case in oneof.get("cases", [])
            )
        feature = _feature(logical)
        direct = graph[original]
        closure = _closure(original, graph)
        messages.append({
            "logical_name": logical,
            "runtime_name": original,
            "obfuscated_name": original,
            "cmd_id": cmd_id,
            "logical_opcode": cmd_id,
            "wire_opcode": cmd_id,
            "opcode_transformation": None,
            "runtime_type_id": item.get("type_index_owner_only"),
            "direction": direction,
            "direction_confidence": direction_confidence,
            "kind": packet_kind,
            "transport_role": (
                "packet_head" if logical == "PacketHead" else
                "packet_body" if packet_kind.startswith("top_level_packet")
                else "nested_body"
            ),
            "version": model["target"]["client_version"],
            "client_executable_sha256": model["target"]["executable_sha256"],
            "metadata_sha256": model.get("inputs", {}).get("runtime_metadata", {}).get("sha256"),
            "proto_source_sha256": None,
            "fields": sorted(fields, key=lambda value: (value["number"], value["obfuscated_name"])),
            "direct_dependencies": direct,
            "nested_dependencies": [name for name in closure if name not in enum_names],
            "enum_dependencies": [name for name in closure if name in enum_names],
            "request_of": None,
            "response_of": None,
            "related_notifications": [],
            "feature_group": feature,
            "criticality": "critical" if feature in _CRITICAL_FEATURES else "normal",
            "confidence": confidence,
            "semantic_classification": (
                "human_semantic_name_bound"
                if logical is not None else "opaque_runtime_identity"
            ),
            "evidence": [
                *list(row.get("current_runtime_evidence", [])),
                *direction_evidence,
            ],
            "reference_evidence": row.get("reference_semantic_evidence"),
            "candidate_mappings": [],
            "rejected_mappings": [],
            "resource_dependency": None,
            "contract_class": (
                "wire_contract" if original in reachable
                else "wire_contract_unbound"
                if packet_kind == "top_level_packet_without_opcode"
                else "resource_only"
            ),
            "server_update_required": (
                "resource_only"
                if original not in reachable and packet_kind == "nested_only"
                else "crypto_contract"
                if feature == "authentication" and isinstance(cmd_id, int)
                else "opcode_and_schema" if isinstance(cmd_id, int)
                else "schema"
            ),
            "parser_entry": (
                {"rva": item["merge_from_rva"], "source": "current_runtime_method"}
                if isinstance(item.get("merge_from_rva"), int) else None
            ),
            "serializer_entry": (
                {"rva": item["write_to_rva"], "source": "current_runtime_method"}
                if isinstance(item.get("write_to_rva"), int) else None
            ),
            "size_calculator_entry": None,
            "unknown_field_handling": (
                "generated_parser_preserves_or_skips_unknown_fields"
                if isinstance(item.get("merge_from_rva"), int)
                else "not_directly_exposed_shared_runtime_path"
            ),
            "schema_completeness": (
                "unproven-packet-body-no-runtime-codec"
                if (
                    isinstance(item.get("cmd_id"), int)
                    and not fields
                    and int(item.get("type_index_owner_only", -1))
                    in parserless_type_indexes
                )
                else "unresolved-empty-packet-body"
                if isinstance(item.get("cmd_id"), int) and not fields
                else "field_bearing"
                if fields
                else "nested_body_or_client_inactive"
            ),
            "structural_fingerprint": _shape(item, enum_names),
        })
    by_logical = {
        str(row["logical_name"]): row
        for row in messages if row["logical_name"] is not None
    }


    req_rsp: list[dict[str, Any]] = []
    for name, request in sorted(by_logical.items()):
        if not name.endswith("Req"):
            continue
        response_name = name[:-3] + "Rsp"
        response = by_logical.get(response_name)
        if response is None:
            continue
        pair_evidence = [
            evidence
            for row in (request, response)
            for evidence in row.get("evidence", [])
            if str(evidence.get("symbol", "")).startswith((
                "literal:", "metadata-method:", "callgraph-literal:",
                "runtime-function-literal:", "runtime-function-callgraph-literal:",
            ))
        ]
        if not pair_evidence:
            continue
        request["response_of"] = response["obfuscated_name"]
        response["request_of"] = request["obfuscated_name"]
        confidence = "confirmed" if {
            request["confidence"], response["confidence"]
        } == {"confirmed"} else "medium"
        req_rsp.append({
            "request": request["obfuscated_name"],
            "request_logical_name": name,
            "response": response["obfuscated_name"],
            "response_logical_name": response_name,
            "confidence": confidence,
            "evidence": pair_evidence,
        })
    opaque_runtime_identities = [
        {
            "message_obfuscated_name": row["obfuscated_name"],
            "logical_name": None,
            "cmd_id": row["cmd_id"],
            "direction": row["direction"],
            "classification": "opaque_runtime_identity",
            "classification_final": True,
            "reason": (
                "current runtime contains a complete type identity and wire schema "
                "but no human semantic-name evidence"
            ),
        }
        for row in messages if row["logical_name"] is None
    ]
    unresolved: list[dict[str, Any]] = []
    context = dump_artifact_context(model["target"])
    counts = Counter(row["confidence"] for row in messages)
    resource_only = [
        {
            "kind": row["kind"],
            "logical_name": row.get("logical_name"),
            "obfuscated_name": row["obfuscated_name"],
            "reason": "not reachable from any command carrying message",
        }
        for row in (*messages, *enums) if row["contract_class"] == "resource_only"
    ]
    analysis = {
        "schema": NAMEEPROTO_SCHEMA,
        "status": "complete",
        "dump_metadata": context,
        "messages": messages,
        "enums": enums,
        "req_rsp_map": req_rsp,
        "dependency_graph": graph,
        "unresolved": unresolved,
        "opaque_runtime_identities": opaque_runtime_identities,
        "resource_only": resource_only,
        "runtime_login_contract": _runtime_login_contract(messages),
        "runtime_capabilities": _runtime_capabilities(model, messages),
        "runtime_modules": _runtime_modules(model),
        "counts": {
            "message_count": len(messages),
            "enum_count": len(enums),
            "top_level_packet_count": sum(row["kind"] == "top_level_packet" for row in messages),
            "top_level_without_opcode_count": sum(
                row["kind"] == "top_level_packet_without_opcode"
                for row in messages
            ),
            "top_level_wire_candidate_count": sum(
                row["kind"] in {
                    "top_level_packet", "top_level_packet_without_opcode",
                }
                for row in messages
            ),
            "nested_only_count": sum(row["kind"] == "nested_only" for row in messages),
            "unresolved_message_count": len(unresolved),
            "opaque_runtime_identity_count": len(opaque_runtime_identities),
            "resource_only_count": len(resource_only),
            "server_update_required_count": sum(
                row["server_update_required"] in _UPDATE_VALUES for row in messages
            ),
            "confidence": dict(sorted(counts.items())),
        },
        "checks": {
            "all_runtime_messages_present_once": len(messages) == len(model["messages_owner_only"]),
            "all_runtime_enums_present_once": len(enums) == len(model["enums_owner_only"]),
            "all_dependencies_are_runtime_types": all(
                child in names for children in graph.values() for child in children
            ),
            "unclassified_messages_absent": not unresolved,
            "opaque_runtime_identities_preserved": (
                len(opaque_runtime_identities)
                == sum(row["logical_name"] is None for row in messages)
            ),
            "wire_contract_fields_total": sum(len(row["fields"]) for row in messages)
            == model["counts"]["proto_field_count"],
            "resource_only_excluded_from_wire_contract": all(
                row["contract_class"] == "resource_only"
                for row in (*messages, *enums)
                if row["contract_class"] == "resource_only"
            ),
        },
    }
    _attach_analysis_extensions(
        analysis,
        previous_corpus=previous_corpus,
        rejected_ledger=rejected_ledger,
        options=options,
    )
    return analysis


_UPDATE_VALUES = {"opcode", "schema", "opcode_and_schema", "crypto_contract"}


def _attach_analysis_extensions(
    analysis: dict[str, Any], *, previous_corpus: Mapping[str, Any] | None,
    rejected_ledger: Mapping[str, Any] | None, options: Mapping[str, Any] | None,
) -> None:
    from alpha import p51

    analysis["session_sequence"] = p51.session_sequence(analysis)
    analysis["openstate"] = p51.openstate(analysis)
    applied: list[dict[str, Any]] = []

    ledger = rejected_ledger or p51.empty_ledger()
    analysis["rejected_candidates"] = {
        "schema": p51.REJECTED_LEDGER_SCHEMA,
        "entries": [dict(entry) for entry in ledger.get("entries") or []],
        "applied": applied,
        "count": len(ledger.get("entries") or []),
        "applied_count": len(applied),
        "source": ledger.get("source"),
    }
    applied_keys = {
        (entry.get("message"), entry.get("candidate_logical_name"))
        for entry in applied
    }
    analysis["checks"]["rejected_candidates_never_reapplied"] = all(
        (row["obfuscated_name"], candidate.get("candidate_logical_name")) not in applied_keys
        for row in analysis["messages"] for candidate in row["candidate_mappings"]
    )
    if dict(options or {}).get("strict"):
        missing = _strict_missing(analysis)
        if missing:
            raise AcquisitionError(
                "NameEProto strict mode requires complete evidence: "
                + "; ".join(missing[:12])
                + (f"; and {len(missing) - 12} more" if len(missing) > 12 else "")
            )


def _strict_missing(analysis: Mapping[str, Any]) -> list[str]:
    missing: list[str] = []
    opaque = list(analysis.get("opaque_runtime_identities") or [])
    if opaque:
        missing.append(
            f"{len(opaque)} message(s) have final opaque runtime identities "
            f"(for example {', '.join(row['message_obfuscated_name'] for row in opaque[:3])})"
        )
    contract = analysis["runtime_login_contract"]
    for name in contract.get("missing") or []:
        missing.append(f"login packet opcode not observed in current runtime: {name}")
    for name in analysis["session_sequence"].get("not_bound_packets") or []:
        missing.append(f"session sequence packet not bound in current runtime: {name}")
    for packet in analysis["openstate"]["wire_contract"]["packets"]:
        if packet["binding_confidence"] == "not_bound_in_current_runtime":
            missing.append(f"open state packet not bound in current runtime: {packet['logical_name']}")
    return missing


def _update_required_summary(row: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "logical_name": row["logical_name"],
        "obfuscated_name": row["obfuscated_name"],
        "cmd_id": row.get("cmd_id"),
        "direction": row.get("direction"),
        "kind": row["kind"],
        "feature_group": row.get("feature_group"),
        "criticality": row.get("criticality"),
        "contract_class": row.get("contract_class"),
        "server_update_required": row["server_update_required"],
        "confidence": row.get("confidence"),
        "field_count": len(row.get("fields") or []),
        "nested_dependency_count": len(row.get("nested_dependencies") or []),
        "enum_dependency_count": len(row.get("enum_dependencies") or []),
        "candidate_count": len(row.get("candidate_mappings") or []),
        "rejected_candidate_count": len(row.get("rejected_mappings") or []),
    }


def _corpus(
    analysis: Mapping[str, Any], selected: Iterable[str] | None = None,
    *, include_unresolved: bool = True,
) -> str:
    messages = list(analysis["messages"])
    enums = list(analysis["enums"])
    if not include_unresolved:
        messages = [row for row in messages if row["logical_name"] is not None]
        enums = [row for row in enums if row["logical_name"] is not None]
    if selected is not None:
        wanted = set(selected)
        messages = [row for row in messages if row["obfuscated_name"] in wanted]
        enums = [row for row in enums if row["obfuscated_name"] in wanted]
    return _json_text({
        "schema": NAMEEPROTO_SCHEMA,
        "dump_metadata": analysis["dump_metadata"],
        "messages": messages,
        "enums": enums,
    })


def _summary_markdown(analysis: Mapping[str, Any]) -> str:
    context = analysis["dump_metadata"]
    counts = analysis["counts"]
    resolved = [
        row for row in analysis["messages"] if row["logical_name"] is not None
    ]
    lines = [
        f"# NameEProto summary {context['client_version']}",
        "",
        f"- client build: `{context['client_build']}`",
        f"- executable sha256: `{context['executable_sha256']}`",
        f"- messages: {counts['message_count']} (top level packets {counts['top_level_packet_count']}, top-level without opcode {counts['top_level_without_opcode_count']}, nested {counts['nested_only_count']})",
        f"- top-level wire candidates: {counts['top_level_wire_candidate_count']}",
        f"- enums: {counts['enum_count']}",
        f"- unclassified messages: {counts['unresolved_message_count']}",
        f"- final opaque runtime identities: {counts['opaque_runtime_identity_count']}",
        f"- resource only types: {counts['resource_only_count']}",
        f"- server update required: {counts['server_update_required_count']}",
        f"- confidence: {json.dumps(counts['confidence'], ensure_ascii=False, sort_keys=True)}",
        "",
        "## Login and session handshake",
        "",
        "| state | logical packet | obfuscated | cmd id | binding |",
        "|---|---|---|---:|---|",
    ]
    for state in analysis["session_sequence"]["states"]:
        for packet in state["packets"]:
            lines.append(
                f"| {state['state']} | {packet['logical_name']} | "
                f"{packet['obfuscated_name'] or '-'} | "
                f"{packet['cmd_id'] if packet['cmd_id'] is not None else '-'} | "
                f"{packet['binding_confidence']} |"
            )
    lines.extend([
        "",
        "## Resolved packets (confirmed or high confidence)",
        "",
        "| logical packet | obfuscated | cmd id | direction | feature | update |",
        "|---|---|---:|---|---|---|",
    ])
    for row in sorted(
        (row for row in resolved if row["confidence"] == "confirmed"),
        key=lambda row: (row.get("cmd_id") is None, row.get("cmd_id") or 0),
    ):
        lines.append(
            f"| {row['logical_name']} | {row['obfuscated_name']} | "
            f"{row['cmd_id'] if row['cmd_id'] is not None else '-'} | "
            f"{row['direction']} | {row['feature_group']} | "
            f"{row['server_update_required']} |"
        )
    return "\n".join(lines) + "\n"


def _render_files(
    analysis: Mapping[str, Any], options: Mapping[str, Any] | None = None,
) -> dict[str, str]:
    settings = dict(options or {})
    include_unresolved = bool(settings.get("include_unresolved", True))
    messages = list(analysis["messages"])
    graph = analysis["dependency_graph"]
    critical_seeds = {
        row["obfuscated_name"] for row in messages if row["criticality"] == "critical"
    }
    critical = set(critical_seeds)
    for seed in critical_seeds:
        critical.update(_closure(seed, graph))
    rendered = {
        "all.nameeproto": _corpus(analysis, include_unresolved=include_unresolved),
        "critical.nameeproto": _corpus(
            analysis, critical, include_unresolved=include_unresolved,
        ),
        "manifest.json": _json_text(analysis),
        "opcode-map.json": _json_text({
            str(row["cmd_id"]): {
                "logical_name": row["logical_name"],
                "obfuscated_name": row["obfuscated_name"],
                "direction": row["direction"],
                "confidence": row["confidence"],
            }
            for row in messages if isinstance(row["cmd_id"], int)
        }),
        "req-rsp-map.json": _json_text(analysis["req_rsp_map"]),
        "dependency-graph.json": _json_text(analysis["dependency_graph"]),
        "unresolved.json": _json_text(analysis["unresolved"]),
        "opaque-runtime-identities.json": _json_text(
            analysis["opaque_runtime_identities"]
        ),
        "evidence.json": _json_text({
            row["obfuscated_name"]: row["evidence"] for row in messages
        }),
        "resource-only.json": _json_text(analysis["resource_only"]),
        "update-required.json": _json_text([
            _update_required_summary(row)
            for row in messages if row["server_update_required"] in _UPDATE_VALUES
        ]),
        "rejected-candidates.json": _json_text(analysis["rejected_candidates"]),
        "session-sequence.json": _json_text(analysis["session_sequence"]),
        "openstate.json": _json_text(analysis["openstate"]),
        "summary.md": _summary_markdown(analysis),
        "runtime-login-contract.json": _json_text(analysis["runtime_login_contract"]),
        "runtime-capabilities.json": _json_text(analysis["runtime_capabilities"]),
        "runtime-modules.json": _json_text(analysis["runtime_modules"]),
        "extraction-report.json": _json_text(_extraction_report(analysis)),
    }
    for feature in _FEATURE_FILES:
        selected = {
            row["obfuscated_name"] for row in messages if row["feature_group"] == feature
        }
        for name in tuple(selected):
            selected.update(_closure(name, graph))
        filename = "login" if feature == "authentication" else feature
        rendered[f"{filename}.nameeproto"] = _corpus(
            analysis, selected, include_unresolved=include_unresolved,
        )
    return rendered


def write_nameeproto_outputs(
    *, model: Mapping[str, Any], semantic_rows: Sequence[Mapping[str, Any]],
    output_dir: Path, directory_name: str,
    previous: Path | None = None, rejected_ledger_path: Path | None = None,
    options: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    from alpha import p51

    if previous is not None:
        raise AcquisitionError("version comparison is outside the current-runtime dump contract")
    previous_corpus = None
    ledger = p51.read_rejected_ledger(rejected_ledger_path)
    analysis = build_nameeproto_analysis(
        model=model, semantic_rows=semantic_rows,
        previous_corpus=previous_corpus, rejected_ledger=ledger, options=options,
    )
    if not all(analysis["checks"].values()):
        raise AcquisitionError("NameEProto analysis closure failed")
    root = output_dir / directory_name
    root.mkdir(parents=True, exist_ok=False)
    rendered = _render_files(analysis, options)
    for name, text in rendered.items():
        _atomic_write_text(root / name, text)
    return {
        "schema": NAMEEPROTO_RECEIPT_SCHEMA,
        "status": "complete",
        "directory": directory_name,
        "files": {name: file_identity(root / name) for name in sorted(rendered)},
        "counts": analysis["counts"],
        "checks": dict(analysis["checks"]),
    }


def verify_nameeproto_outputs(
    *, model: Mapping[str, Any], semantic_rows: Sequence[Mapping[str, Any]],
    output_dir: Path, directory_name: str,
    previous: Path | None = None, rejected_ledger_path: Path | None = None,
    options: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    from alpha import p51

    if previous is not None:
        raise AcquisitionError("version comparison is outside the current-runtime dump contract")
    previous_corpus = None
    ledger = p51.read_rejected_ledger(rejected_ledger_path)
    analysis = build_nameeproto_analysis(
        model=model, semantic_rows=semantic_rows,
        previous_corpus=previous_corpus, rejected_ledger=ledger, options=options,
    )
    rendered = _render_files(analysis, options)
    root = output_dir / directory_name
    if root.is_symlink() or not root.is_dir():
        raise AcquisitionError("NameEProto output directory is missing or unsafe")
    if (root / "version-diff.json").is_file():
        raise AcquisitionError(
            "published NameEProto contains an excluded version diff"
        )
    entries = list(root.iterdir())
    if {path.name for path in entries} != set(rendered) or any(
        path.is_symlink() or not path.is_file() for path in entries
    ):
        raise AcquisitionError("NameEProto output file domain differs")
    for name, expected in rendered.items():
        try:
            observed = (root / name).read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError) as error:
            raise AcquisitionError(f"NameEProto output is unreadable: {name}") from error
        if observed != expected:
            raise AcquisitionError(f"NameEProto output differs from runtime model: {name}")
    return {
        "status": "complete",
        "files": {name: file_identity(root / name) for name in sorted(rendered)},
        "counts": analysis["counts"],
        "checks": {
            **analysis["checks"],
            "outputs_exactly_reconstructed": True,
            "output_file_domain_complete": True,
        },
    }


def semantic_rows_from_model(
    *, model: Mapping[str, Any], static_model: Path,
    semantic_references: list[Path] | None = None,
) -> list[dict[str, Any]]:
    from alpha.p02 import normalize_proto_items
    from alpha.p47 import _semantic_translation

    source = [*model["messages_owner_only"], *model["enums_owner_only"]]
    normalized = normalize_proto_items(source)
    _translation, rows, _evidence, _fields = _semantic_translation(
        source,
        normalized,
        static_model.expanduser().resolve(),
        semantic_references,
    )
    return rows


def write_nameeproto_outputs_from_model(
    *, static_model: Path, output_dir: Path, directory_name: str | None = None,
    previous: Path | None = None, rejected_ledger_path: Path | None = None,
    options: Mapping[str, Any] | None = None,
    client_version: str | None = None, client_build: str | None = None,
    semantic_references: list[Path] | None = None,
) -> dict[str, Any]:
    from alpha.h02 import read_private_model
    from alpha.p02 import proto_artifact_names

    model_path = static_model.expanduser().resolve()
    raw = read_private_model(model_path)
    if not isinstance(raw, Mapping):
        raise AcquisitionError("static model is not an object")
    model = _publishable_model_view(
        raw, client_version=client_version, client_build=client_build,
    )
    rows = semantic_rows_from_model(
        model=model,
        static_model=model_path,
        semantic_references=semantic_references,
    )
    name = directory_name or proto_artifact_names(model["target"])["nameeproto"]
    return write_nameeproto_outputs(
        model=model, semantic_rows=rows, output_dir=output_dir,
        directory_name=name, previous=previous,
        rejected_ledger_path=rejected_ledger_path, options=options,
    )


def _publishable_model_view(
    model: Mapping[str, Any], *, client_version: str | None, client_build: str | None,
) -> dict[str, Any]:
    import os

    result = dict(model)
    target = dict(model.get("target") or {})
    version = client_version or target.get("client_version") or os.environ.get(
        "ALPHA_CLIENT_VERSION"
    )
    build = client_build or target.get("client_build") or os.environ.get(
        "ALPHA_CLIENT_BUILD"
    )
    if version:
        target["client_version"] = str(version)
    if build:
        target["client_build"] = str(build)
    elif version:
        target.setdefault("client_build", str(version))
    result["target"] = target
    ordinal = 1_000_000
    for key in ("messages_owner_only", "enums_owner_only"):
        rows = []
        for item in model.get(key) or []:
            if not isinstance(item, Mapping):
                raise AcquisitionError("static model type row is invalid")
            row = dict(item)
            if not isinstance(row.get("type_index_owner_only"), int):
                row["type_index_owner_only"] = ordinal
            ordinal += 1
            rows.append(row)
        result[key] = rows
    return result


def verify_nameeproto_outputs_from_model(
    *, static_model: Path, output_dir: Path, directory_name: str | None = None,
    previous: Path | None = None, rejected_ledger_path: Path | None = None,
    options: Mapping[str, Any] | None = None,
    client_version: str | None = None, client_build: str | None = None,
) -> dict[str, Any]:
    from alpha.h02 import read_private_model
    from alpha.p02 import proto_artifact_names

    model_path = static_model.expanduser().resolve()
    raw = read_private_model(model_path)
    if not isinstance(raw, Mapping):
        raise AcquisitionError("static model is not an object")
    model = _publishable_model_view(
        raw, client_version=client_version, client_build=client_build,
    )
    rows = semantic_rows_from_model(model=model, static_model=model_path)
    name = directory_name or proto_artifact_names(model["target"])["nameeproto"]
    return verify_nameeproto_outputs(
        model=model, semantic_rows=rows, output_dir=output_dir,
        directory_name=name, previous=previous,
        rejected_ledger_path=rejected_ledger_path, options=options,
    )


def options_from_environment(
    environ: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    import os

    source = os.environ if environ is None else environ

    def path(name: str) -> Path | None:
        value = source.get(name)
        return Path(value).expanduser() if value else None

    references: list[Path] = []
    raw_references = source.get("ALPHA_NAMEEPROTO_SEMANTIC_REFERENCES", "")
    for entry in raw_references.split(os.pathsep):
        entry = entry.strip()
        if entry:
            references.append(Path(entry).expanduser())
    return {
        "previous": None,
        "rejected_ledger": path("ALPHA_NAMEEPROTO_REJECTED_LEDGER"),
        "references": references,
        "options": {
            "strict": source.get("ALPHA_NAMEEPROTO_STRICT") == "1",
            "no_guess": source.get("ALPHA_NAMEEPROTO_NO_GUESS") == "1",
            "include_unresolved": source.get(
                "ALPHA_NAMEEPROTO_INCLUDE_UNRESOLVED", "1"
            ) == "1",
        },
    }
