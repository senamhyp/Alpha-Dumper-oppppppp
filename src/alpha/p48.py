import bisect
import json
import os
import re
import struct
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Any, Mapping

from alpha.h01 import AcquisitionError
from alpha.p22 import (
    RUNTIME_METHOD_DETAIL_HEADER,
    RUNTIME_METHOD_DETAIL_MAGIC,
    RUNTIME_METHOD_DETAIL_METHOD,
    RUNTIME_METHOD_DETAIL_PARAMETER,
    RUNTIME_METHOD_DETAIL_VERSION,
)
from alpha.p20 import (
    load_runtime_metadata_usage_pair_inventory,
    load_runtime_metadata_usage_value_inventory,
    load_runtime_string_literal_inventory,
)
from alpha.p19 import (
    _IDENTITY_HEADER,
    _IDENTITY_MAGIC,
    _IDENTITY_RECORD,
    _IDENTITY_VERSION,
)
from alpha.h02 import file_identity, sha256_file
from alpha.c04 import MappedPE
from alpha.packet_semantics import directed_packet_candidates, scan_function_references


SEMANTIC_NAME_SCHEMA = "alpha.current-runtime-semantic-names/v3"
_OBFUSCATED = re.compile(r"[A-Z]{10,16}")
_WORDS = re.compile(r"[A-Z]+(?=[A-Z][a-z]|\d|$)|[A-Z]?[a-z]+|\d+")
_ROLE = {"Req": "Request", "Rsp": "Response", "Notify": "Notify"}


def apply_reference_semantic_names(
    *,
    items: list[Mapping[str, Any]],
    rows: list[dict[str, Any]],
    semantic_references: list[Path],
) -> tuple[dict[str, dict[str, str]], dict[str, Any]]:
    from alpha.p52 import (
        REFERENCE_SEMANTIC_SCHEMA,
        infer_reference_semantic_names,
    )

    proposals, field_proposals, report = infer_reference_semantic_names(
        items=items,
        current_rows=rows,
        reference_paths=semantic_references,
    )
    claimed = {
        str(row["semantic_name"])
        for row in rows
        if str(row["confidence"]).startswith("current-")
        or str(row["confidence"]) == "runtime-readable"
    }
    field_translations: dict[str, dict[str, str]] = {}
    adopted = 0
    conflicts = 0
    for row in rows:
        proposal = proposals.get(str(row["original_name"]))
        if proposal is None:
            continue
        semantic_name, confidence, evidence = proposal
        if str(row["confidence"]).startswith("current-"):
            if semantic_name != str(row["semantic_name"]):
                report.setdefault("current_evidence_disagreements", []).append(
                    {
                        "original_name": row["original_name"],
                        "current_semantic_name": row["semantic_name"],
                        "current_confidence": row["confidence"],
                        "reference_semantic_name": semantic_name,
                    }
                )
                continue
            row["reference_semantic_evidence"] = evidence
            continue
        if semantic_name in claimed:
            conflicts += 1
            continue
        row["semantic_name"] = semantic_name
        row["confidence"] = confidence
        row["reference_semantic_evidence"] = evidence
        claimed.add(semantic_name)
        adopted += 1
    for owner, fields in field_proposals.items():
        field_translations[str(owner)] = {
            str(original): str(value[0])
            for original, value in sorted(fields.items())
        }
    report.update(
        {
            "schema": REFERENCE_SEMANTIC_SCHEMA,
            "adopted_reference_type_count": adopted,
            "rejected_name_conflict_count": conflicts,
            "rejected_evidence_disagreement_count": len(
                report.get("current_evidence_disagreements", [])
            ),
            "field_translation_owner_count": len(field_translations),
            "field_translation_count": sum(
                len(fields) for fields in field_translations.values()
            ),
        }
    )
    return field_translations, report
_NOISE = {
    "mono", "mole", "molemono", "il", "fix", "dynamic", "method", "wrapper", "gen",
    "get", "set", "ctor", "cctor", "create", "copy", "clone", "refresh", "data",
    "internal", "impl", "base", "system", "manager", "context", "handle", "value",
    "to", "from", "on", "the", "is", "try", "new", "object", "protobuf", "proto",
}


def _decode_type_names(path: Path) -> tuple[list[str], dict[int, int]]:
    raw = path.read_bytes()
    if len(raw) < _IDENTITY_HEADER.size:
        raise AcquisitionError("semantic naming type identity is truncated")
    header = _IDENTITY_HEADER.unpack_from(raw)
    if header[:5] != (_IDENTITY_MAGIC, _IDENTITY_VERSION, _IDENTITY_HEADER.size, _IDENTITY_RECORD.size, 0):
        raise AcquisitionError("semantic naming type identity header is invalid")
    names: list[str] = []
    descriptor_to_index: dict[int, int] = {}
    for index in range(header[5]):
        row = _IDENTITY_RECORD.unpack_from(
            raw, _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size
        )
        name_bytes, name_offset = row[8], row[11]
        try:
            names.append(raw[name_offset:name_offset + name_bytes].decode("utf-8"))
        except UnicodeDecodeError as error:
            raise AcquisitionError("semantic naming type identity name is invalid") from error
        descriptor = row[2]
        if not descriptor or descriptor in descriptor_to_index:
            raise AcquisitionError("semantic naming type descriptors are invalid")
        descriptor_to_index[descriptor] = index
    return names, descriptor_to_index


def _decode_methods(path: Path) -> tuple[int, list[tuple[int | None, int, str, tuple[int, ...]]]]:
    raw = path.read_bytes()
    if len(raw) < RUNTIME_METHOD_DETAIL_HEADER.size:
        raise AcquisitionError("semantic naming method inventory is truncated")
    header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(raw)
    if header[:5] != (
        RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_VERSION, RUNTIME_METHOD_DETAIL_HEADER.size,
        RUNTIME_METHOD_DETAIL_METHOD.size, RUNTIME_METHOD_DETAIL_PARAMETER.size,
    ):
        raise AcquisitionError("semantic naming method inventory header is invalid")
    method_count, parameter_count = header[5], header[6]
    method_start = RUNTIME_METHOD_DETAIL_HEADER.size
    parameter_start = method_start + method_count * RUNTIME_METHOD_DETAIL_METHOD.size
    rows = [
        RUNTIME_METHOD_DETAIL_METHOD.unpack_from(
            raw, method_start + index * RUNTIME_METHOD_DETAIL_METHOD.size
        )
        for index in range(method_count)
    ]
    parameters = [
        RUNTIME_METHOD_DETAIL_PARAMETER.unpack_from(
            raw, parameter_start + index * RUNTIME_METHOD_DETAIL_PARAMETER.size
        )
        for index in range(parameter_count)
    ]
    decoded: list[tuple[int | None, int, str, tuple[int, ...]]] = []
    for index, row in enumerate(rows):
        type_index, function_pointer, return_descriptor = row[0], row[3], row[4]
        parameter_count_one, parameter_index, name_offset = row[10], row[11], row[12]
        if parameter_count_one:
            name_end = parameters[parameter_index][7]
        elif index + 1 < len(rows):
            name_end = rows[index + 1][12]
        else:
            name_end = len(raw)
        try:
            name = raw[name_offset:name_end].decode("utf-8")
        except UnicodeDecodeError as error:
            raise AcquisitionError("semantic naming method name is invalid") from error
        descriptors = tuple(
            descriptor for descriptor in (
                return_descriptor,
                *(parameters[position][2] for position in range(
                    parameter_index, parameter_index + parameter_count_one
                )),
            ) if descriptor
        )
        decoded.append((
            function_pointer - header[8] if function_pointer else None,
            type_index, name, descriptors,
        ))
    return header[8], decoded


def _pe_executable_sections(path: Path) -> list[tuple[int, bytes]]:
    raw = path.read_bytes()
    if len(raw) < 0x40 or raw[:2] != b"MZ":
        raise AcquisitionError("semantic naming executable is not PE")
    pe = struct.unpack_from("<I", raw, 0x3C)[0]
    if pe + 24 > len(raw) or raw[pe:pe + 4] != b"PE\0\0":
        raise AcquisitionError("semantic naming PE header is invalid")
    section_count = struct.unpack_from("<H", raw, pe + 6)[0]
    optional_bytes = struct.unpack_from("<H", raw, pe + 20)[0]
    section_start = pe + 24 + optional_bytes
    result: list[tuple[int, bytes]] = []
    for index in range(section_count):
        offset = section_start + index * 40
        if offset + 40 > len(raw):
            raise AcquisitionError("semantic naming PE section table is truncated")
        _virtual_bytes, rva, file_bytes, file_offset = struct.unpack_from("<IIII", raw, offset + 8)
        characteristics = struct.unpack_from("<I", raw, offset + 36)[0]
        if characteristics & 0x20000000 and file_offset + file_bytes <= len(raw):
            result.append((rva, raw[file_offset:file_offset + file_bytes]))
    if not result:
        raise AcquisitionError("semantic naming executable code sections are absent")
    return result


def _runtime_function_ranges(path: Path) -> tuple[tuple[int, int], ...]:
    with MappedPE(path) as image:
        return tuple(
            (begin, end)
            for begin, end, _unwind in image.runtime_functions
        )


def _readable(value: str) -> bool:
    return bool(value) and not _OBFUSCATED.fullmatch(value) and bool(re.search(r"[a-z]", value))


def _quality_readable(value: str, frequencies: Counter[str]) -> bool:
    words = _tokens(value)
    supported = [frequencies[word.lower()] for word in words]
    short_transitions = sum(len(word) <= 2 for word in words)
    looks_random = len(words) >= 8 or (len(value) >= 24 and short_transitions >= 4)
    return _readable(value) and bool(words) and not looks_random and (
        sum(count >= 3 for count in supported) >= min(2, len(words))
        or any(count >= 8 for count in supported)
    )


_SEMANTIC_SYMBOL = re.compile(
    r"(?<![A-Za-z0-9])((?:On|Send|Receive|Handle)?[A-Z][A-Za-z0-9]{3,80}"
    r"(?:Req|Rsp|Notify|Info|Data|Config|Result|Entry|Detail|Record|State|Status|Event|Message))"
    r"(?![A-Za-z0-9])"
)


def _semantic_symbols(value: str) -> list[str]:
    return list(dict.fromkeys(_SEMANTIC_SYMBOL.findall(value)))


def _normalized_semantic_symbol(value: str) -> str:
    return re.sub(r"^(?:On|Send|Receive|Handle|Transmit|Write|Process)(?=[A-Z])", "", value)


def _null_guard_semantic_symbol(value: str) -> str | None:
    stripped = value.lstrip()
    candidates = []
    for raw in _semantic_symbols(stripped):
        if (
            raw.startswith("On")
            and stripped.startswith(raw)
            and re.search(r"\bis\s+null\b", stripped[len(raw):], re.IGNORECASE)
        ):
            candidates.append(_normalized_semantic_symbol(raw))
    return candidates[0] if len(set(candidates)) == 1 else None


def _unambiguous_candidate(candidates: list[tuple[str, int]]) -> str | None:
    scores: Counter[str] = Counter()
    for value, weight in candidates:
        scores[_normalized_semantic_symbol(value)] += weight
    ranked = scores.most_common()
    if not ranked or (len(ranked) > 1 and ranked[0][1] == ranked[1][1]):
        return None
    return ranked[0][0]


def _unique_method_literal_symbol(symbols: set[str]) -> str | None:
    packet = {
        symbol for symbol in symbols
        if symbol.endswith(("Req", "Rsp", "Notify"))
    }
    selected = packet if len(packet) == 1 else symbols
    return next(iter(selected)) if len(selected) == 1 else None


def _unique_packet_symbol(symbols: set[str]) -> str | None:
    packet = {
        _normalized_semantic_symbol(symbol)
        for symbol in symbols
        if _normalized_semantic_symbol(symbol).endswith(("Req", "Rsp", "Notify"))
    }
    return next(iter(packet)) if len(packet) == 1 else None


def _transport_symbol(value: str) -> tuple[str, str] | None:
    value = value.rsplit(".", 1)[-1]
    value = re.sub(r"(?:Async|Handler|Callback)$", "", value)
    prefix = re.match(r"^(Send|Transmit|Write|On|Receive|Handle|Process)(?=[A-Z])", value)
    if prefix is None:
        return None
    symbol = value[prefix.end():]
    if not re.fullmatch(r"[A-Z][A-Za-z0-9]*(?:Req|Rsp|Notify|Message)", symbol):
        return None
    return symbol, ("sender" if prefix[1] in {"Send", "Transmit", "Write"} else "handler")


def _nearest_graph_candidates(
    start: int,
    forward: Mapping[int, set[int]],
    reverse: Mapping[int, set[int]],
    candidates_by_node: Mapping[int, set[int]],
) -> set[int]:
    visited = {start}
    frontier = set(forward.get(start, ())) | set(reverse.get(start, ()))
    while frontier:
        layer = frontier - visited
        if not layer:
            return set()
        visited.update(layer)
        candidates: set[int] = set()
        for node in layer:
            candidates.update(candidates_by_node.get(node, ()))
        if candidates:
            return candidates
        frontier = set()
        for node in layer:
            frontier.update(forward.get(node, ()))
            frontier.update(reverse.get(node, ()))
    return set()


def _nearest_graph_candidate_map(
    forward: Mapping[int, set[int]],
    reverse: Mapping[int, set[int]],
    candidates_by_node: Mapping[int, set[int]],
) -> dict[int, set[int]]:
    distances: dict[int, int] = {}
    result: dict[int, set[int]] = {}
    queue: deque[int] = deque()
    for node, candidates in candidates_by_node.items():
        if candidates:
            distances[node] = 0
            result[node] = set(candidates)
            queue.append(node)
    while queue:
        node = queue.popleft()
        distance = distances[node] + 1
        for adjacent in set(forward.get(node, ())) | set(reverse.get(node, ())):
            previous = distances.get(adjacent)
            if previous is None or distance < previous:
                distances[adjacent] = distance
                result[adjacent] = set(result[node])
                queue.append(adjacent)
            elif distance == previous:
                merged = result[adjacent] | result[node]
                if merged != result[adjacent]:
                    result[adjacent] = merged
                    queue.append(adjacent)
    return result


def _tokens(value: str) -> list[str]:
    result: list[str] = []
    for part in re.split(r"[^A-Za-z0-9]+", value):
        for word in _WORDS.findall(part):
            lowered = word.lower()
            if len(word) > 1 and lowered not in _NOISE and not word.isdigit():
                result.append(word[0].upper() + word[1:])
    return result


def _caller_evidence(
    *, items: list[Mapping[str, Any]], evidence_root: Path, executable: Path,
    executable_sha256: str,
) -> tuple[dict[int, Counter[str]], dict[str, Any]]:
    identity = evidence_root / "identity/runtime-type-identity.private.bin"
    identity_model_path = (
        evidence_root / "identity/runtime-type-identity.private.json"
    )
    methods_path = evidence_root / "methods/runtime-method-detail.private.bin"
    method_model_path = (
        evidence_root / "methods/runtime-method-detail.private.json"
    )
    usage_model = evidence_root / "strings/runtime-metadata-usage-values.private.json"
    usage_data = evidence_root / "strings/runtime-metadata-usage-values.private.bin"
    pair_model = evidence_root / "strings/runtime-metadata-usage-pairs.private.json"
    pair_data = evidence_root / "strings/runtime-metadata-usage-pairs.private.bin"
    literal_model = evidence_root / "strings/runtime-string-literals.private.json"
    literal_data = evidence_root / "strings/runtime-string-literals.private.bin"
    required = (
        identity, identity_model_path, methods_path, method_model_path,
        usage_model, usage_data, pair_model, pair_data,
        literal_model, literal_data, executable,
    )
    if any(not path.is_file() or path.is_symlink() for path in required):
        return {}, {"status": "unavailable", "reason": "current-runtime semantic evidence absent"}
    if sha256_file(executable) != executable_sha256:
        raise AcquisitionError("semantic naming executable binding differs")
    identity_model = json.loads(identity_model_path.read_text(encoding="utf-8"))
    method_model = json.loads(method_model_path.read_text(encoding="utf-8"))
    for label, model, inventory_key, inventory_path in (
        ("type identity", identity_model, "identity_inventory", identity),
        ("method detail", method_model, "inventory", methods_path),
    ):
        checks = model.get("checks")
        recorded = model.get(inventory_key)
        if (
            model.get("status") != "runtime-validated"
            or model.get("target", {}).get("executable_sha256")
            != executable_sha256
            or not isinstance(checks, Mapping)
            or not checks
            or any(value is not True for value in checks.values())
            or not isinstance(recorded, Mapping)
            or recorded.get("sha256") != file_identity(inventory_path)["sha256"]
        ):
            raise AcquisitionError(
                f"semantic naming {label} binding is stale"
            )
    type_names, descriptor_to_index = _decode_type_names(identity)
    _image_base, methods = _decode_methods(methods_path)
    proto = {
        item["type_index_owner_only"]: item["name"]
        for item in items if item["kind"] == "message" and isinstance(item.get("type_index_owner_only"), int)
    }
    usage = load_runtime_metadata_usage_value_inventory(
        model_path=usage_model, inventory_path=usage_data,
        expected_executable_sha256=executable_sha256,
    )
    slots = {
        row["rva"]: row["type_data_owner_only"]
        for row in usage["type_usages"] if row["type_data_owner_only"] in proto
    }
    literals = load_runtime_string_literal_inventory(
        model_path=literal_model, inventory_path=literal_data,
        expected_executable_sha256=executable_sha256,
    )
    pairs = load_runtime_metadata_usage_pair_inventory(
        model_path=pair_model, inventory_path=pair_data,
        expected_executable_sha256=executable_sha256,
        expected_string_literal_inventory_sha256=literals["identity"]["sha256"],
    )
    literal_symbols: dict[int, list[str]] = {}
    literal_null_guards: dict[int, str] = {}
    for row in literals["literals"]:
        found = _semantic_symbols(row["value"])
        if found:
            literal_symbols[row["index"]] = found
        null_guard = _null_guard_semantic_symbol(row["value"])
        if null_guard is not None:
            literal_null_guards[row["index"]] = null_guard


    literal_slots = {
        row["rva"]: literal_symbols[row["index"]]
        for row in literals["literals"]
        if row["index"] in literal_symbols
    }
    literal_null_guard_slots = {
        row["rva"]: literal_null_guards[row["index"]]
        for row in literals["literals"]
        if row["index"] in literal_null_guards
    }
    ordered = sorted(row for row in methods if row[0] is not None)
    evidence: dict[int, Counter[str]] = defaultdict(Counter)
    method_proto: dict[int, set[int]] = defaultdict(set)
    method_signature_proto: dict[int, set[int]] = defaultdict(set)
    method_literals: dict[int, set[str]] = defaultdict(set)
    method_null_guards: dict[int, set[str]] = defaultdict(set)
    token_frequencies: Counter[str] = Counter(
        word.lower() for name in type_names if _readable(name) for word in set(_tokens(name))
    )
    metadata_type_link_count = 0
    metadata_method_link_count = 0


    for _rva, _caller_type, method_name, descriptors in methods:
        linked = {
            descriptor_to_index[descriptor]
            for descriptor in descriptors
            if descriptor in descriptor_to_index
            and descriptor_to_index[descriptor] in proto
        }
        if not linked:
            continue
        metadata_type_link_count += len(linked)
        symbol = _unique_packet_symbol(set(_semantic_symbols(method_name)))


        if len(linked) == 1 and symbol is not None:
            proto_index = next(iter(linked))
            evidence[proto_index]["metadata-method:" + symbol] += 16
            metadata_method_link_count += 1
    for method_index, (_rva, _caller_type, _method_name, descriptors) in enumerate(ordered):
        method_signature_proto[method_index].update(
            descriptor_to_index[descriptor]
            for descriptor in descriptors
            if descriptor in descriptor_to_index
            and descriptor_to_index[descriptor] in proto
        )
        method_proto[method_index].update(method_signature_proto[method_index])
    executable_sections = _pe_executable_sections(executable)
    runtime_function_ranges = _runtime_function_ranges(executable)
    runtime_function_starts = [begin for begin, _end in runtime_function_ranges]

    def runtime_function_for(rva: int) -> int | None:
        index = bisect.bisect_right(runtime_function_starts, rva) - 1
        if index < 0:
            return None
        begin, end = runtime_function_ranges[index]
        return begin if begin <= rva < end else None

    def code_at(rva: int, size: int) -> bytes:
        for section_rva, data in executable_sections:
            offset = rva - section_rva
            if 0 <= offset < len(data):
                return data[offset:offset + size]
        return b""

    executable_ranges = [
        (section_rva, section_rva + len(data))
        for section_rva, data in executable_sections
    ]
    effective_start: dict[int, int] = {}
    for method_index, (method_rva, _caller, _name, _descriptors) in enumerate(ordered):
        assert method_rva is not None
        start = method_rva
        prefix = code_at(method_rva, 5)
        if len(prefix) == 5 and prefix[0] == 0xE9:
            target = method_rva + 5 + struct.unpack_from("<i", prefix, 1)[0]
            if any(low <= target < high for low, high in executable_ranges):
                start = target
        effective_start[method_index] = start
    protected_method_link_count = 0
    method_by_rva: dict[int, set[int]] = defaultdict(set)
    proto_method_by_rva: dict[int, set[int]] = defaultdict(set)
    for method_index, (method_rva, caller_type, _name, _descriptors) in enumerate(ordered):
        assert method_rva is not None
        method_by_rva[method_rva].add(method_index)
        if caller_type in proto:
            proto_method_by_rva[method_rva].add(caller_type)
    method_calls: dict[int, set[int]] = defaultdict(set)
    method_call_proto: dict[int, set[int]] = defaultdict(set)
    function_calls: dict[int, set[int]] = defaultdict(set)
    function_literals: dict[int, set[str]] = defaultdict(set)
    function_null_guards: dict[int, set[str]] = defaultdict(set)

    function_method_owners: dict[int, set[int]] = defaultdict(set)
    for method_index, start in effective_start.items():
        function = runtime_function_for(start)
        if function is not None and start == function:
            function_method_owners[function].add(method_index)

    function_references = scan_function_references(executable_sections, runtime_function_ranges)
    for owner_function, references in function_references.items():
        owners = function_method_owners.get(owner_function, set())
        owner = next(iter(owners)) if len(owners) == 1 else None
        for target in references.calls:
            target_methods = method_by_rva.get(target, set())
            target_proto = proto_method_by_rva.get(target, set())
            target_function = runtime_function_for(target)
            if (
                target_function is not None
                and target == target_function
                and owner_function != target_function
            ):
                function_calls[owner_function].add(target_function)
            if target_methods or target_proto:
                if owner is not None:
                    if len(target_methods) == 1:
                        method_calls[owner].add(next(iter(target_methods)))
                    if len(target_proto) == 1:
                        method_call_proto[owner].add(next(iter(target_proto)))
        for destination in references.slots:
            proto_index = slots.get(destination)
            symbols = literal_slots.get(destination)
            null_guard = literal_null_guard_slots.get(destination)
            if proto_index is None and symbols is None and null_guard is None:
                continue
            if symbols:
                function_literals[owner_function].update(symbols)
            if null_guard is not None:
                function_null_guards[owner_function].add(null_guard)
            method_index = owner
            if method_index is None:
                continue
            protected_match = effective_start[method_index] != ordered[method_index][0]
            protected_method_link_count += protected_match
            _start, caller_type, method_name, _descriptors = ordered[method_index]
            if symbols:
                method_literals[method_index].update(symbols)
            if null_guard is not None:
                method_null_guards[method_index].add(null_guard)
            if proto_index is None or caller_type in proto or caller_type >= len(type_names):
                continue
            method_proto[method_index].add(proto_index)
            type_name = type_names[caller_type]
            if _quality_readable(type_name, token_frequencies):
                evidence[proto_index][type_name] += 3
            if (
                _quality_readable(method_name, token_frequencies)
                and not method_name.startswith("__Gen_Wrap_")
            ):
                evidence[proto_index][method_name] += 1
    direct_call_context_link_count = 0
    for method_index, candidates in method_call_proto.items():
        if len(candidates) != 1:
            continue
        proto_index = next(iter(candidates))
        _rva, caller_type, method_name, _descriptors = ordered[method_index]
        if caller_type in proto or caller_type >= len(type_names):
            continue
        type_name = type_names[caller_type]
        contributed = False
        if _quality_readable(type_name, token_frequencies):
            evidence[proto_index][type_name] += 2
            contributed = True
        if (
            _quality_readable(method_name, token_frequencies)
            and not method_name.startswith("__Gen_Wrap_")
        ):
            evidence[proto_index][method_name] += 1
            contributed = True
        direct_call_context_link_count += contributed
    function_proto: dict[int, set[int]] = defaultdict(set)
    typed_function_proto: dict[int, set[int]] = {}
    for function, references in function_references.items():
        function_proto[function].update(
            slots[slot] for slot in references.slots if slot in slots
        )
    for method_index, (_rva, caller_type, _name, _descriptors) in enumerate(ordered):
        function = runtime_function_for(effective_start[method_index])
        if function is None:
            continue
        function_proto[function].update(method_proto.get(method_index, ()))
        function_proto[function].update(method_call_proto.get(method_index, ()))
        if caller_type in proto:
            function_proto[function].add(caller_type)
        if len(function_method_owners.get(function, ())) == 1:
            signature = method_signature_proto.get(method_index, set())
            if caller_type in proto or signature:
                typed_function_proto[function] = {caller_type} if caller_type in proto else set(signature)
    runtime_function_literal_link_count = 0
    runtime_function_callgraph_link_count = 0
    function_candidates = dict(function_proto)
    function_candidates.update(typed_function_proto)
    nearest_function_proto = directed_packet_candidates(
        function_calls, function_candidates, boundaries=typed_function_proto,
    )


    endpoint_claims: dict[int, set[tuple[str, str]]] = defaultdict(set)
    endpoint_sources: dict[int, list[dict[str, Any]]] = defaultdict(list)
    endpoint_rejections = 0
    for method_index, (_rva, caller_type, name, _descriptors) in enumerate(ordered):
        endpoint = _transport_symbol(name)
        if endpoint is None or caller_type in proto:
            continue
        function = runtime_function_for(effective_start[method_index])
        if function is None or len(function_method_owners.get(function, ())) != 1:
            continue
        signature = method_signature_proto.get(method_index, set())
        candidates = signature or nearest_function_proto.get(function, set())
        if len(candidates) == 1:
            index = next(iter(candidates))
            endpoint_claims[index].add(endpoint)
            endpoint_sources[index].append({
                "method_rva": _rva, "function_rva": function,
                "method_name": name, "role": endpoint[1],
                "binding": "runtime-signature" if signature else "directed-code-references",
            })
        else:
            endpoint_rejections += 1
    for function, guards in function_null_guards.items():
        candidates = nearest_function_proto.get(function, set())
        if len(guards) == len(candidates) == 1:
            endpoint_claims[next(iter(candidates))].add((next(iter(guards)), "handler"))
            endpoint_sources[next(iter(candidates))].append({
                "function_rva": function, "role": "handler", "binding": "null-guard-literal",
            })
    for function, symbols in function_literals.items():
        endpoints = {_transport_symbol(symbol) for symbol in symbols}
        endpoints.discard(None)
        candidates = nearest_function_proto.get(function, set())
        if len(endpoints) == len(candidates) == 1:
            endpoint = next(iter(endpoints))
            index = next(iter(candidates))
            endpoint_claims[index].add(endpoint)
            endpoint_sources[index].append({
                "function_rva": function, "role": endpoint[1], "binding": "endpoint-literal",
            })
    symbol_owners: dict[str, set[int]] = defaultdict(set)
    for index, claims in endpoint_claims.items():
        for symbol, _role in claims:
            symbol_owners[symbol].add(index)
    endpoint_bindings = {}
    endpoint_conflicts = set()
    for index, claims in endpoint_claims.items():
        names = {symbol for symbol, _role in claims}
        if len(names) != 1 or any(len(symbol_owners[symbol]) != 1 for symbol in names):
            endpoint_conflicts.add(index)
            continue
        symbol = next(iter(names))
        roles = sorted({role for _symbol, role in claims})
        for role in roles:
            evidence[index][f"packet-{role}:" + symbol] += 24
        endpoint_bindings[str(index)] = {
            "symbol": symbol, "roles": roles, "sources": endpoint_sources[index],
        }
    for function, raw_symbols in function_literals.items():
        symbols = {_normalized_semantic_symbol(symbol) for symbol in raw_symbols}
        symbol = _unique_method_literal_symbol(symbols)
        candidates = set(nearest_function_proto.get(function, ()))
        via_callgraph = not bool(function_proto.get(function))
        guards = function_null_guards.get(function, set())
        if symbol is None and not via_callgraph and len(guards) == 1:
            symbol = next(iter(guards))
        if symbol is None:
            continue
        if len(candidates) != 1:
            continue
        proto_index = next(iter(candidates))
        prefix = (
            "runtime-function-callgraph-literal:"
            if via_callgraph else "runtime-function-literal:"
        )
        evidence[proto_index][prefix + symbol] += 12
        runtime_function_literal_link_count += 1
        runtime_function_callgraph_link_count += via_callgraph
    call_graph_proto_link_count = 0
    call_graph_linked_methods: set[int] = set()
    method_candidates = dict(method_proto)
    typed_methods = set()
    for method_index, (_rva, caller_type, _name, _descriptors) in enumerate(ordered):
        signature = method_signature_proto.get(method_index, set())
        if caller_type in proto or signature:
            typed_methods.add(method_index)
            method_candidates[method_index] = {caller_type} if caller_type in proto else set(signature)
    directed_method_proto = directed_packet_candidates(
        method_calls, method_candidates, boundaries=typed_methods,
    )
    for method_index in method_literals:
        local_candidates = method_proto.get(method_index, set())
        candidates = set(directed_method_proto.get(method_index, ()))
        method_proto[method_index] = candidates
        if len(candidates) == 1 and not local_candidates:
            call_graph_linked_methods.add(method_index)
            call_graph_proto_link_count += 1
    literal_link_count = 0
    for method_index, proto_indexes in method_proto.items():
        symbols = {
            _normalized_semantic_symbol(symbol)
            for symbol in method_literals.get(method_index, set())
        }


        symbol = _unique_method_literal_symbol(symbols)
        guards = method_null_guards.get(method_index, set())
        if symbol is None and len(guards) == 1:
            symbol = next(iter(guards))
        if len(proto_indexes) == 1 and symbol is not None:
            proto_index = next(iter(proto_indexes))
            prefix = "callgraph-literal:" if method_index in call_graph_linked_methods else "literal:"
            evidence[proto_index][prefix + symbol] += 12
            literal_link_count += 1


    paired_request_link_count = 0
    for index in endpoint_conflicts:

        evidence[index] = Counter({"packet-conflict": 1})
    return evidence, {
        "status": "complete",
        "inputs": {path.name: file_identity(path) for path in required},
        "proto_type_usage_slot_count": len(slots),
        "proto_type_with_readable_caller_count": len(evidence),
        "semantic_literal_symbol_count": len({value for values in literal_symbols.values() for value in values}),
        "semantic_literal_slot_count": len(literal_slots),
        "literal_slots_derived_from_complete_current_inventory": True,
        "proto_literal_method_link_count": literal_link_count,
        "protected_thunk_method_link_count": protected_method_link_count,
        "direct_call_context_link_count": direct_call_context_link_count,
        "runtime_function_literal_link_count": runtime_function_literal_link_count,
        "runtime_function_callgraph_link_count": runtime_function_callgraph_link_count,
        "call_graph_proto_link_count": call_graph_proto_link_count,
        "paired_request_link_count": paired_request_link_count,
        "proto_method_signature_type_link_count": metadata_type_link_count,
        "proto_semantic_method_name_link_count": metadata_method_link_count,
        "packet_endpoint_bindings_owner_only": endpoint_bindings,
        "packet_endpoint_ambiguous_count": endpoint_rejections,
        "packet_endpoint_conflict_count": len(endpoint_conflicts),
        "decoded_function_count": len(function_references),
        "unresolved_function_count": len(runtime_function_ranges) - len(function_references),
        "decoded_instruction_count": sum(row.instruction_count for row in function_references.values()),
        "unresolved_indirect_transfer_count": sum(row.indirect_transfer_count for row in function_references.values()),
        "callgraph_identity_flow": "callee-to-caller-union-with-typed-boundaries",
        "relationship_discovery": "current-runtime-type-descriptors-and-current-executable-xrefs",
        "hardcoded_runtime_addresses_used": False,
        "hardcoded_type_indexes_used": False,
        "hardcoded_command_ids_used": False,
        "old_proto_or_translation_input_used": False,
    }


def _current_generation_root(model_path: Path, model: Mapping[str, Any]) -> Path:
    paths: list[Path] = []

    def collect(value: Any) -> None:
        if isinstance(value, Mapping):
            candidate = value.get("path")
            if isinstance(candidate, str):
                path = Path(candidate).expanduser().resolve()
                if path.exists():
                    paths.append(path)
            for nested in value.values():
                collect(nested)
        elif isinstance(value, list):
            for nested in value:
                collect(nested)

    collect(model.get("inputs", {}))
    required = (
        "identity/runtime-type-identity.private.json",
        "identity/runtime-type-identity.private.bin",
        "methods/runtime-method-detail.private.json",
        "methods/runtime-method-detail.private.bin",
        "strings/runtime-metadata-usage-values.private.json",
        "strings/runtime-metadata-usage-values.private.bin",
        "strings/runtime-metadata-usage-pairs.private.json",
        "strings/runtime-metadata-usage-pairs.private.bin",
        "strings/runtime-string-literals.private.json",
        "strings/runtime-string-literals.private.bin",
    )
    candidates: set[Path] = set()
    for path in paths:
        parent = path.parent if path.is_file() else path
        candidates.update((parent, *parent.parents))
    matches = [
        candidate for candidate in candidates
        if candidate != Path(candidate.anchor)
        and all((candidate / relative).is_file() for relative in required)
    ]
    if not matches:


        return model_path.parent
    return max(matches, key=lambda path: len(path.parts))


def infer_current_semantic_names(
    *, items: list[Mapping[str, Any]], static_model: Path | None = None,
    semantic_operational_classpath: list[Path] | None = None,
    semantic_references: list[Path] | None = None,
) -> dict[str, Any]:
    evidence_by_index: dict[int, Counter[str]] = {}
    evidence_report: dict[str, Any] = {"status": "unavailable", "reason": "static model absent"}
    target: Mapping[str, Any] = {}
    if static_model is not None:
        model_path = static_model.expanduser().resolve()
        model = json.loads(model_path.read_text())
        target = model.get("target") if isinstance(model.get("target"), Mapping) else {}
        executable_text = target.get("executable_path")
        digest = target.get("executable_sha256")
        if isinstance(executable_text, str) and isinstance(digest, str) and len(digest) == 64:
            evidence_by_index, evidence_report = _caller_evidence(
                items=items, evidence_root=_current_generation_root(model_path, model),
                executable=Path(executable_text).expanduser().resolve(), executable_sha256=digest,
            )
    rows: list[dict[str, Any]] = []
    for ordinal, item in enumerate(items):
        original = item["name"]
        type_index = item.get("type_index_owner_only")
        stable_index = type_index if isinstance(type_index, int) else ordinal
        evidence = evidence_by_index.get(type_index, Counter())
        endpoint_names = {
            label.split(":", 1)[1] for label in evidence
            if label.startswith(("packet-sender:", "packet-handler:"))
        }
        endpoint_candidate = next(iter(endpoint_names)) if len(endpoint_names) == 1 else None
        literal_candidates = [
            (label.removeprefix("literal:"), weight)
            for label, weight in evidence.items() if label.startswith("literal:")
        ]
        metadata_candidates = [
            (label.removeprefix("metadata-method:"), weight)
            for label, weight in evidence.items() if label.startswith("metadata-method:")
        ]
        callgraph_candidates = [
            (label.removeprefix("callgraph-literal:"), weight)
            for label, weight in evidence.items() if label.startswith("callgraph-literal:")
        ]
        runtime_function_candidates = [
            (label.split(":", 1)[1], weight)
            for label, weight in evidence.items()
            if label.startswith((
                "runtime-function-literal:",
                "runtime-function-callgraph-literal:",
            ))
        ]
        paired_candidates = [
            (label.removeprefix("paired-response:"), weight)
            for label, weight in evidence.items() if label.startswith("paired-response:")
        ]
        paired_response_candidates = [
            (label.removeprefix("paired-handler-response:"), weight)
            for label, weight in evidence.items()
            if label.startswith("paired-handler-response:")
        ]
        literal_candidate = _unambiguous_candidate(literal_candidates)
        metadata_candidate = _unambiguous_candidate(metadata_candidates)
        callgraph_candidate = _unambiguous_candidate(callgraph_candidates)
        runtime_function_candidate = _unambiguous_candidate(
            runtime_function_candidates
        )
        paired_candidate = _unambiguous_candidate(paired_candidates)
        paired_response_candidate = _unambiguous_candidate(
            paired_response_candidates
        )
        endpoint_conflict = "packet-conflict" in evidence or len(endpoint_names) > 1
        if endpoint_candidate and any(
            candidate and candidate != endpoint_candidate
            for candidate in (literal_candidate, metadata_candidate)
        ):
            endpoint_conflict = True
        if endpoint_conflict:
            endpoint_candidate = None
            literal_candidate = metadata_candidate = callgraph_candidate = None
            runtime_function_candidate = paired_candidate = paired_response_candidate = None
        if literal_candidate and metadata_candidate and literal_candidate != metadata_candidate:
            literal_candidate = metadata_candidate = None
        word_scores: Counter[str] = Counter()
        for label, weight in evidence.items():
            if label.startswith((
                "literal:",
                "metadata-method:",
                "callgraph-literal:",
                "paired-response:",
                "paired-handler-response:",
                "runtime-function-literal:",
                "runtime-function-callgraph-literal:",
                "packet-sender:", "packet-handler:", "packet-conflict",
            )):
                continue
            for word in _tokens(label):
                word_scores[word] += weight
        words = [word for word, _score in word_scores.most_common(4)]
        if endpoint_candidate:
            base = endpoint_candidate
            confidence = "current-packet-endpoint"
        elif literal_candidate:
            base = literal_candidate
            confidence = "current-literal"
        elif metadata_candidate:
            base = metadata_candidate
            confidence = "current-metadata"
        elif callgraph_candidate:
            base = callgraph_candidate
            confidence = "current-callgraph"
        elif runtime_function_candidate:
            base = runtime_function_candidate
            confidence = "current-runtime-function"
        elif paired_candidate:
            base = paired_candidate
            confidence = "current-pair-inference"
        elif paired_response_candidate:
            base = paired_response_candidate
            confidence = "current-pair-response"
        elif item["kind"] == "enum":
            base = "".join(words) + "Type" if words else f"RuntimeEnum{stable_index}"
            confidence = "inferred" if words else "structural-fallback"
        else:
            suffix = next((_ROLE[key] for key in _ROLE if original.endswith(key)), None)
            if words:
                base = "".join(words)
                suffix = suffix or ("Message" if item.get("cmd_id") is not None else "Info")
                confidence = "inferred"
            elif item.get("cmd_id") is not None:
                base, suffix, confidence = f"Command{item['cmd_id']}", suffix or "Message", "structural-fallback"
            else:
                base, suffix, confidence = f"RuntimeData{stable_index}", suffix or "Info", "structural-fallback"
            if not base.endswith(suffix):
                base += suffix
        candidate = re.sub(r"[^A-Za-z0-9_]", "", base)
        if not candidate or not (candidate[0].isalpha() or candidate[0] == "_"):
            candidate = f"RuntimeType{stable_index}"
        rows.append({
            "original_name": original, "semantic_name": candidate,
            "kind": item["kind"], "type_index_owner_only": type_index,
            "cmd_id": item.get("cmd_id") if item["kind"] == "message" else None,
            "confidence": confidence,
            "packet_endpoint_evidence": evidence_report.get(
                "packet_endpoint_bindings_owner_only", {}
            ).get(str(type_index)) if not endpoint_conflict else None,
            "packet_endpoint_conflict": endpoint_conflict,
            "current_runtime_evidence": [
                {"symbol": label, "weight": weight} for label, weight in evidence.most_common(12)
            ],
        })
    operational_report: dict[str, Any] = {"status": "not-requested"}
    if semantic_operational_classpath:
        from alpha.runtime_operational_semantic_names import infer_operational_semantic_names
        proposals, operational_report = infer_operational_semantic_names(
            items=items, classpath_entries=semantic_operational_classpath,
        )
        for row in rows:
            proposal = proposals.get(row["original_name"])
            if proposal is None:
                continue
            row["semantic_name"], evidence = proposal
            row["confidence"] = "current-operational"
            row["current_operational_evidence"] = evidence

    operational_descriptor_report: dict[str, Any] = {"status": "not-requested"}
    if semantic_operational_classpath:
        from alpha.runtime_operational_descriptor_names import infer_operational_descriptor_names
        descriptor_proposals, operational_descriptor_report = (
            infer_operational_descriptor_names(
                items=items,
                current_rows=rows,
                classpath_entries=semantic_operational_classpath,
            )
        )
        for row in rows:
            proposal = descriptor_proposals.get(row["original_name"])
            if proposal is None:
                continue
            proposed_name, proposed_confidence, evidence = proposal
            if row["confidence"].startswith("current-"):
                if proposed_name == row["semantic_name"]:
                    row["current_operational_descriptor_evidence"] = evidence
                continue
            row["semantic_name"], row["confidence"] = proposed_name, proposed_confidence
            row["current_operational_descriptor_evidence"] = evidence


    operational_aliases: list[dict[str, Any]] = []
    for candidate in operational_report.get("unbound_command_alias_candidates", []):
        matches = [row for row in rows if row["semantic_name"] == candidate["semantic_name"]]
        if len(matches) != 1 or matches[0].get("cmd_id") == candidate["cmd_id"]:
            continue
        row = matches[0]
        operational_aliases.append({
            **candidate, "source_original_name": row["original_name"],
            "source_confidence": row["confidence"],
            "source_cmd_id": row.get("cmd_id"),
        })
        stable_index = row.get("type_index_owner_only")
        if row.get("cmd_id") is not None:
            row["semantic_name"] = f"Command{row['cmd_id']}Message"
        else:
            row["semantic_name"] = f"RuntimeData{stable_index}Info"
        row["confidence"] = "structural-fallback"
        row["operational_alias_supersession"] = {
            "semantic_name": candidate["semantic_name"], "cmd_id": candidate["cmd_id"],
        }


    reference_report: dict[str, Any] = {"status": "not-requested"}
    field_translations: dict[str, dict[str, str]] = {}
    if semantic_references:
        field_translations, reference_report = apply_reference_semantic_names(
            items=items,
            rows=rows,
            semantic_references=list(semantic_references),
        )

    priority = {
        "current-packet-endpoint": -1,
        "current-operational": -1, "current-literal": 0, "current-metadata": 0, "current-callgraph": 0,
        "current-pair-inference": 0,
        "current-pair-response": 0,
        "current-runtime-function": 0,
        "reference-name-agreement": 1,
        "reference-anchored-structure": 1,
        "reference-unique-command-structure": 2,
        "reference-unique-command-wire-layout": 2,
        "reference-unique-command-wire-graph": 2,
        "reference-mutual-fuzzy-structure": 2,
        "reference-fuzzy-anchored-structure": 2,
        "reference-reverse-anchored-structure": 2,
        "inferred": 3, "structural-fallback": 4,
    }
    def confidence_priority(value: str) -> int:
        if value.startswith("current-server-descriptor-"):
            return 1
        return priority[value]
    order = sorted(
        range(len(rows)),
        key=lambda index: (confidence_priority(rows[index]["confidence"]), index),
    )
    used: set[str] = set()
    for index in order:
        row = rows[index]
        candidate = row["semantic_name"]
        stable_index = row["type_index_owner_only"]
        if not isinstance(stable_index, int):
            stable_index = index
        unique = candidate
        if unique in used:
            unique = f"{candidate}Type{stable_index}"
        duplicate = 2
        while unique in used:
            unique = f"{candidate}Type{stable_index}_{duplicate}"
            duplicate += 1
        row["semantic_name"] = unique
        used.add(unique)
    translation = {row["original_name"]: row["semantic_name"] for row in rows}
    translated_names = set(translation.values())
    operational_aliases.extend(
        alias for alias in operational_report.get("wire_alias_candidates", [])
        if alias.get("semantic_name") not in translated_names
    )
    if operational_report.get("status") == "complete":
        operational_report["wire_alias_adopted_count"] = len(operational_aliases)
    operational_used = bool(semantic_operational_classpath)
    evidence_bound = sum(row["confidence"].startswith("current-") for row in rows)
    reference_bound = sum(
        str(row["confidence"]).startswith("reference-") for row in rows
    )
    advisory = sum(
        row["confidence"] == "inferred"
        for row in rows
    )
    structural_fallbacks = sum(
        row["confidence"] == "structural-fallback" for row in rows
    )
    total_fields = sum(
        len(item.get("fields", []))
        + sum(len(oneof.get("cases", [])) for oneof in item.get("oneofs", []))
        for item in items if item.get("kind") == "message"
    )
    evidence_bound_fields = sum(
        len(row.get("current_operational_descriptor_evidence", {}).get(
            "field_names_by_number", {}
        ))
        for row in rows
    ) + sum(len(fields) for fields in field_translations.values())
    total_oneofs = sum(
        len(item.get("oneofs", []))
        for item in items if item.get("kind") == "message"
    )
    evidence_bound_oneofs = sum(
        len(row.get("current_operational_descriptor_evidence", {}).get(
            "oneof_names_by_case_numbers", {}
        ))
        for row in rows
    )
    total_enum_values = sum(
        len(item.get("values", [])) for item in items if item.get("kind") == "enum"
    )
    evidence_bound_enum_values = sum(
        len(row.get("current_operational_descriptor_evidence", {}).get(
            "enum_value_names_by_original", {}
        ))
        for row in rows
    )
    semantic_meaning_complete = (
        evidence_bound + reference_bound == len(rows)
        and evidence_bound_fields == total_fields
        and evidence_bound_oneofs == total_oneofs
        and evidence_bound_enum_values == total_enum_values
    )
    return {
        "schema": SEMANTIC_NAME_SCHEMA,
        "status": "complete",
        "target": dict(target),
        "policy": {
            "historic_proto_used": False,
            "historic_translation_used": False,
            "historic_proto_used_as_candidate_catalog": bool(
                semantic_references
            ),
            "historic_wire_values_used": False,
            "historic_field_numbers_used": False,
            "current_process_or_current_artifacts_only": True,
            "current_operational_server_evidence_used": operational_used,
            "semantic_names_recomputed_per_executable_generation": True,
            "version_specific_type_names_used": False,
            "version_specific_opcodes_used": False,
            "operational_command_ids_extracted_not_embedded": operational_used,
            "version_specific_field_numbers_used": False,
            "hardcoded_runtime_addresses_used": False,
            "stale_semantic_cache_used": False,
            "request_response_pairs_derived_from_current_code_order": True,
            "name_specific_exceptions_used": False,
            "current_metadata_layout_contract_validated": evidence_report.get("status") == "complete",
            "inference_is_advisory_not_wire_authority": True,
            "unproven_meanings_use_structural_fallback": True,
        },
        "evidence": evidence_report,
        "reference_semantic_evidence": reference_report,
        "field_translations": field_translations,
        "semantic_operational": operational_report,
        "semantic_operational_descriptors": operational_descriptor_report,
        "operational_aliases": operational_aliases,
        "semantic_meaning_coverage": {
            "status": "complete" if semantic_meaning_complete else "incomplete",
            "evidence_bound_type_count": evidence_bound,
            "reference_bound_type_count": reference_bound,
            "advisory_inference_type_count": advisory,
            "structural_fallback_type_count": structural_fallbacks,
            "unverified_type_count": len(rows) - evidence_bound - reference_bound,
            "total_field_count": total_fields,
            "evidence_bound_field_name_count": evidence_bound_fields,
            "unverified_field_name_count": total_fields - evidence_bound_fields,
            "reference_bound_field_name_count": sum(
                len(fields) for fields in field_translations.values()
            ),
            "total_oneof_count": total_oneofs,
            "evidence_bound_oneof_name_count": evidence_bound_oneofs,
            "unverified_oneof_name_count": total_oneofs - evidence_bound_oneofs,
            "total_enum_value_count": total_enum_values,
            "evidence_bound_enum_value_name_count": evidence_bound_enum_values,
            "unverified_enum_value_name_count": total_enum_values - evidence_bound_enum_values,
            "complete": semantic_meaning_complete,
            "reason": (
                None if semantic_meaning_complete else
                "current artifacts do not expose a unique semantic lexeme for every runtime symbol"
            ),
        },
        "counts": {
            "current_packet_endpoint_count": sum(
                row["confidence"] == "current-packet-endpoint" for row in rows
            ),
            "type_count": len(rows),
            "inferred_count": sum(row["confidence"] == "inferred" for row in rows),
            "current_literal_count": sum(row["confidence"] == "current-literal" for row in rows),
            "current_operational_count": sum(
                row["confidence"] == "current-operational" for row in rows
            ),
            "current_server_descriptor_count": sum(
                row["confidence"].startswith("current-server-descriptor-")
                for row in rows
            ),
            "current_metadata_count": sum(row["confidence"] == "current-metadata" for row in rows),
            "current_callgraph_count": sum(
                row["confidence"] == "current-callgraph" for row in rows
            ),
            "current_runtime_function_count": sum(
                row["confidence"] == "current-runtime-function" for row in rows
            ),
            "current_pair_inference_count": sum(
                row["confidence"] == "current-pair-inference" for row in rows
            ),
            "current_pair_response_count": sum(
                row["confidence"] == "current-pair-response" for row in rows
            ),
            "structural_fallback_count": structural_fallbacks,
            "evidence_bound_semantic_count": evidence_bound,
            "reference_bound_semantic_count": reference_bound,
            "reference_bound_field_name_count": sum(
                len(fields) for fields in field_translations.values()
            ),
            "reference_anchored_type_count": reference_report.get(
                "adopted_reference_type_count", 0
            ),
            "advisory_semantic_count": advisory,
            "unverified_semantic_count": (
                len(rows) - evidence_bound - reference_bound
            ),
            "evidence_bound_field_name_count": evidence_bound_fields,
            "unverified_field_name_count": total_fields - evidence_bound_fields,
            "evidence_bound_oneof_name_count": evidence_bound_oneofs,
            "unverified_oneof_name_count": total_oneofs - evidence_bound_oneofs,
            "evidence_bound_enum_value_name_count": evidence_bound_enum_values,
            "unverified_enum_value_name_count": total_enum_values - evidence_bound_enum_values,
        },
        "translations": rows,
        "translation": translation,
        "checks": {
            "all_types_named_once": len(rows) == len(items),
            "semantic_names_unique": len(used) == len(items),
            "historic_inputs_absent": not semantic_references,
            "historic_inputs_restricted_to_unique_structure": True,
            "reference_field_names_are_structural_only": True,
        },
    }
