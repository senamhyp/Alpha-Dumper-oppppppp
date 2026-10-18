import array
import hashlib
import json
import os
import re
import struct
import sys
from collections import Counter
from dataclasses import asdict
from pathlib import Path

from alpha.p12 import _owner_directory, _private_json
from alpha.h01 import AcquisitionError, same_executable_path
from alpha.p13 import _safe_path, _file_record
from alpha.p04 import derive_encoded_vtable_contract
from alpha.c03 import evaluate
from alpha.p15 import resolve_native_read_graph, reobserve_native_read_graph, specialize_expression
from alpha.c01 import current_runtime_process_binding
from alpha.p14 import read_current_runtime_ranges, load_runtime_range_observation
from alpha.c04 import MappedPE
from alpha.p19 import _IDENTITY_HEADER, _IDENTITY_RECORD
from alpha.p32 import load_runtime_vtable_interfaces
from alpha.p36 import _binding, _method_rows
from alpha.h02 import file_identity


_HEADER = struct.Struct("<8sIIIIQQQQ64s64s")
_TYPE = struct.Struct("<IIIIQQQ")
_MAGIC = b"ALPHAEV2"
_SCHEMA = "alpha.runtime-encoded-vtable-inventory/v2"
_INPUT_KEYS = {"reflection_semantics_model", *(
    prefix + suffix for prefix in ("type_identity", "type_graph", "type_reference", "method_detail", "vtable_interface", "constructed_method")
    for suffix in ("_model", "_inventory"))}


def _current_code_contract(binary, binding):
    with MappedPE(binary) as image:
        rva = binding["interface_map_contract"]["helper_rva"]
        function = image.containing_function(rva)
        if not function or function.begin_rva != rva:
            raise AcquisitionError("encoded vtable helper has no exact function boundary")
        bounds = image.bounded_code(rva, function.end_rva)
        if bounds is None:
            raise AcquisitionError("encoded vtable helper bounds are unavailable")
        code = bytes(image._mapping[bounds[0]:bounds[1]])
        return derive_encoded_vtable_contract(code, current_code_va=binding["image_base"] + rva)


def _parse_inventory(raw, *, identity, inputs):
    if len(raw) < _HEADER.size:
        raise AcquisitionError("encoded vtable inventory is truncated")
    header = _HEADER.unpack_from(raw)
    dependency_sha = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    if (header[:5] != (_MAGIC, 2, _HEADER.size, _TYPE.size, 8)
        or header[7:] != (identity['process_id'], identity['creation_filetime'],
                           identity['executable_sha256'].encode(), dependency_sha.encode())
        or not header[5] or not header[6]
        or _HEADER.size + header[5] * _TYPE.size + header[6] * 8 != len(raw)):
        raise AcquisitionError("encoded vtable inventory header/binding differs")
    records = []
    cursor = 0
    classes = set()
    for definition in range(header[5]):
        row = _TYPE.unpack_from(raw, _HEADER.size + definition * _TYPE.size)
        owner, attributes, kind, reserved, klass, first, count = row
        if (owner != definition or reserved or not klass or klass in classes or first != cursor
            or cursor + count > header[6] or kind not in (0, 1, 2) or (kind == 0) != (count == 0)):
            raise AcquisitionError("encoded vtable inventory class/ranges differ")
        classes.add(klass)
        cursor += count
        records.append(row)
    if cursor != header[6]:
        raise AcquisitionError("encoded vtable inventory has unaccounted slots")
    words = array.array('Q')
    words.frombytes(raw[_HEADER.size + header[5] * _TYPE.size:])
    if sys.byteorder != 'little':
        words.byteswap()
    for row in records:
        if row[2] == 1 and any(words[row[5] + slot] > 0xFFFFFFFF for slot in range(row[6])):
            raise AcquisitionError("encoded vtable inventory word exceeds uint32")
        if row[2] == 2 and any(not words[row[5] + slot] for slot in range(row[6])):
            raise AcquisitionError("encoded vtable inventory contains a null MethodInfo")
    return records, words


def _replay_words(contract, records, words, observation):

    for owner, attributes, kind, reserved, klass, first, count in records:
        if not count:
            continue
        values = {contract.class_input: klass, contract.slot_input: 0}
        encoded = (evaluate(contract.read.guard, values, observation) == 0) == contract.read.guard_zero_required
        if encoded != (kind == 1):
            raise AcquisitionError("encoded vtable replay guard differs")
        read = contract.read if encoded else contract.alternative_pointer_read
        if read is None:
            raise AcquisitionError("encoded vtable replay alternate branch is absent")
        if not encoded and evaluate(contract.alternative_count_expression, values, observation) != count:
            raise AcquisitionError("encoded vtable replay pointer count differs")
        expr = specialize_expression(read.expression, {contract.class_input: klass}, observation)
        for slot in range(count):
            actual = evaluate(expr, {contract.slot_input: slot}, observation)
            if actual != words[first + slot]:
                raise AcquisitionError("encoded vtable slot differs from native observation")


def load_runtime_encoded_vtables(*, model_path: Path, inventory_path: Path,
                                 expected_identity: dict, expected_inputs: dict):

    model_path, inventory_path = _safe_path(model_path), _safe_path(inventory_path)
    model_id, inventory_id = _file_record(model_path), _file_record(inventory_path)
    model = json.loads(model_path.read_text())
    target = {key: expected_identity[key] for key in ('executable_sha256', 'process_id', 'creation_filetime')}
    expected_keys = {'binary', 'reflection_semantics', *(_INPUT_KEYS - {'reflection_semantics_model'})}
    if (set(expected_inputs) != expected_keys or model.get('schema') != _SCHEMA
        or model.get('status') != 'runtime-observed' or model.get('target') != target
        or model.get('inputs') != expected_inputs or model.get('inventory') != {'path': str(inventory_path), **inventory_id}
        or not model.get('checks') or any(value is not True for value in model['checks'].values())):
        raise AcquisitionError('encoded vtable receipt binding/checks differ')
    binary = _safe_path(Path(expected_identity['executable_path']))
    if expected_inputs['binary'] != {'path': str(binary), 'bytes': expected_identity['executable_bytes'], 'sha256': target['executable_sha256']}:
        raise AcquisitionError('encoded vtable executable identity differs')
    def verify_inputs():
        for name, record in expected_inputs.items():
            path = _safe_path(Path(record['path']))
            if name != 'binary':
                _file_record(path)
                if path.stat().st_mtime_ns // 100 + 116444736000000000 < target['creation_filetime']:
                    raise AcquisitionError('encoded vtable input predates process instance')
            if file_identity(path) != record:
                raise AcquisitionError('encoded vtable input identity changed: ' + name)
    verify_inputs()
    binding = _binding(binary=binary, **{key: Path(expected_inputs['reflection_semantics' if key == 'reflection_semantics_model' else key]['path']) for key in _INPUT_KEYS})
    if binding['process_id'] != target['process_id']:
        raise AcquisitionError('encoded vtable upstream process differs')
    contract = _current_code_contract(binary, binding)
    if json.loads(json.dumps(asdict(contract))) != model.get('code_contract_owner_only'):
        raise AcquisitionError('encoded vtable code contract cannot be rederived')
    raw = inventory_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != inventory_id['sha256']:
        raise AcquisitionError('encoded vtable inventory changed while reading')
    records, words = _parse_inventory(raw, identity=expected_identity, inputs=expected_inputs)
    vtables = load_runtime_vtable_interfaces(
        model_path=Path(expected_inputs['vtable_interface_model']['path']),
        inventory_path=Path(expected_inputs['vtable_interface_inventory']['path']),
        expected_executable_sha256=target['executable_sha256'],
        expected_type_identity_inventory_sha256=expected_inputs['type_identity_inventory']['sha256'],
        expected_type_graph_inventory_sha256=expected_inputs['type_graph_inventory']['sha256'],
        expected_method_detail_inventory_sha256=expected_inputs['method_detail_inventory']['sha256'])
    iraw = Path(expected_inputs['type_identity_inventory']['path']).read_bytes()
    if len(records) != binding['type_count'] or len(records) != len(vtables['records']):
        raise AcquisitionError('encoded vtable TypeDef domain differs')
    for index, row in enumerate(records):
        source = _IDENTITY_RECORD.unpack_from(iraw, _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size)
        if (row[0], row[1], row[4]) != (source[0], source[7], source[3]):
            raise AcquisitionError('encoded vtable TypeDef identity differs')
        native = vtables['records'][index]
        if (row[4], row[5], row[6]) != (native[0], native[5], native[1]):
            raise AcquisitionError('encoded vtable independently observed ranges differ')
    observations = model.get('observations')
    if not isinstance(observations, list) or not observations:
        raise AcquisitionError('encoded vtable native observations are absent')
    view = None
    for record in observations:
        path = _safe_path(Path(record['path']))
        if {'path': str(path), **_file_record(path)} != record:
            raise AcquisitionError('encoded vtable native receipt changed')
        view = load_runtime_range_observation(path, expected_identity=expected_identity)
    _replay_words(contract, records, words, view)
    known = {row[0] for row in binding['metadata_map']}
    method_count = max(row[1] for row in binding['metadata_map']) + 1
    counts = Counter(type_count=len(records), vtable_word_count=len(words), all_slot_addresses_verified=len(words))
    tags = Counter()
    for row in records:
        if row[2] == 2 and any(words[row[5] + slot] not in known for slot in range(row[6])):
            raise AcquisitionError('encoded vtable MethodInfo domain differs')
        if row[2] == 2:
            counts['native_method_pointer_count'] += row[6]
            counts['pointer_branch_type_count'] += 1
        elif row[2] == 1:
            counts['encoded_word_count'] += row[6]
            counts['encoded_branch_type_count'] += 1
            for slot in range(row[6]):
                word = words[row[5] + slot]
                tag = word & contract.dispatch.tag_mask
                if tag != contract.dispatch.compared_tag and word & contract.dispatch.index_mask >= method_count:
                    raise AcquisitionError('encoded vtable direct MethodDef domain differs')
                counts['raw_zero_word_count'] += word == 0
                tags[tag] += 1
    for key in ('native_method_pointer_count', 'pointer_branch_type_count', 'encoded_word_count', 'encoded_branch_type_count', 'raw_zero_word_count'):
        counts.setdefault(key, 0)
    if (any(model.get('counts', {}).get(key) != count for key, count in counts.items())
        or model.get('counts', {}).get('raw_tag_counts') != {str(tag): count for tag, count in sorted(tags.items())}):
        raise AcquisitionError('encoded vtable receipt counts differ')
    verify_inputs()
    if _file_record(model_path) != model_id or _file_record(inventory_path) != inventory_id:
        raise AcquisitionError('encoded vtable artifacts changed during replay')
    return {'records': records, 'words': words, 'contract': contract,
            'model': {'path': str(model_path), **model_id}, 'inventory': {'path': str(inventory_path), **inventory_id},
            'observation': view, 'binding': binding, 'vtables': vtables}


def _collect_words(contract, rows, *, capture, method_count, known_method_pointers=frozenset()):

    nonempty = [row for row in rows if row[3]]
    if not nonempty:
        raise AcquisitionError("encoded vtable domain has no slots")
    def inputs(row, slot=0):
        return {contract.class_input: row[2], contract.slot_input: slot}
    guards = [(contract.read.guard, inputs(row)) for row in nonempty]
    graph = resolve_native_read_graph(guards, capture=capture)
    guard_view = graph.view()
    branches = {}
    for row in nonempty:
        actual_zero = evaluate(contract.read.guard, inputs(row), guard_view) == 0
        if actual_zero == contract.read.guard_zero_required:
            branches[row[0]] = 1
        elif contract.alternative_pointer_read is not None:
            branches[row[0]] = 2
        else:
            raise AcquisitionError(f"native vtable code guard rejects nominal definition {row[0]}")
    def expression(row):
        return contract.read.expression if branches[row[0]] == 1 else contract.alternative_pointer_read.expression
    addresses = [(expression(row)[1], inputs(row)) for row in nonempty]
    addresses.extend((contract.alternative_count_expression, inputs(row)) for row in nonempty if branches[row[0]] == 2)
    graph = resolve_native_read_graph(addresses, capture=capture, initial=graph)
    dependencies = graph.view()
    planned = {}
    ranges = []
    for row in nonempty:
        address_expression, width = expression(row)[1:]
        if branches[row[0]] == 2 and evaluate(contract.alternative_count_expression, inputs(row), dependencies) != row[3]:
            raise AcquisitionError("native method-pointer array boundary differs from observed vtable count")
        expr = specialize_expression(address_expression, {contract.class_input: row[2]}, dependencies)
        first = evaluate(expr, {contract.slot_input: 0}, dependencies) & ((1 << 64) - 1)

        for slot in range(row[3]):
            address = evaluate(expr, {contract.slot_input: slot}, dependencies) & ((1 << 64) - 1)
            if address != first + slot * width:
                raise AcquisitionError("native vtable current slot addresses are not contiguous")
        if first <= 0 or first + row[3] * width > 1 << 64:
            raise AcquisitionError("native vtable current slot range is invalid")
        planned[row[0]] = first
        ranges.append((first, row[3] * width))


    current = reobserve_native_read_graph(graph, extra_ranges=ranges, capture=capture, max_gap=256)
    words = array.array("Q")
    type_records = []
    tags = Counter()
    zeros = 0
    encoded_count = 0
    pointer_count = 0
    for row in rows:
        definition, attributes, klass, count = row
        start = len(words)
        kind = branches.get(definition, 0)
        if count:
            encoded_branch = (evaluate(contract.read.guard, inputs(row), current) == 0) == contract.read.guard_zero_required
            if encoded_branch != (kind == 1):
                raise AcquisitionError("native vtable guard changed")
            address_expression, width = expression(row)[1:]
            if kind == 2 and evaluate(contract.alternative_count_expression, inputs(row), current) != count:
                raise AcquisitionError("native method-pointer boundary changed")
            address = evaluate(address_expression, inputs(row), current) & ((1 << 64) - 1)
            if address != planned[definition]:
                raise AcquisitionError("native vtable planned address changed")
            data = current.read(address, count * width)
            if data is None:
                raise AcquisitionError("native vtable final word range is absent")
            values = struct.unpack(f"<{count}{'I' if kind == 1 else 'Q'}", data)
            for word in values:
                if kind == 1:
                    tag = word & contract.dispatch.tag_mask
                    index = word & contract.dispatch.index_mask
                    if tag != contract.dispatch.compared_tag and index >= method_count:
                        raise AcquisitionError("native vtable direct branch index exceeds MethodDef inventory")
                    tags[tag] += 1
                    zeros += word == 0
                    encoded_count += 1
                else:
                    if not word or word not in known_method_pointers:
                        raise AcquisitionError("native vtable method pointer is outside the current metadata domain")
                    pointer_count += 1
            words.extend(values)
        type_records.append((definition, attributes, kind, 0, klass, start, count))
    return type_records, words, {"type_count": len(rows), "vtable_word_count": len(words),
        "raw_zero_word_count": zeros, "raw_tag_counts": {str(tag): count for tag, count in sorted(tags.items())},
        "encoded_word_count": encoded_count, "native_method_pointer_count": pointer_count,
        "encoded_branch_type_count": sum(kind == 1 for kind in branches.values()),
        "pointer_branch_type_count": sum(kind == 2 for kind in branches.values()),
        "discovery_wave_count": graph.discovery_waves, "all_slot_addresses_verified": len(words)}


def capture_runtime_encoded_vtables(*, binary: Path, output_dir: Path, wine: Path,
                                    wineprefix: Path, compiler: Path | None = None,
                                    timeout: float = 900.0, **inputs):
    del timeout
    if set(inputs) != _INPUT_KEYS:
        raise AcquisitionError("encoded vtable acquisition inputs are incomplete or unexpected")
    binary = _safe_path(binary)
    current = current_runtime_process_binding()
    if current is None or not same_executable_path(current[2], binary):
        raise AcquisitionError("encoded vtable capture requires the current process session")
    output_dir = _owner_directory(_safe_path(output_dir))
    if any(output_dir.iterdir()):
        raise AcquisitionError("encoded vtable output directory is not empty")
    binding = _binding(binary=binary, **inputs)
    if binding["process_id"] != current[0]:
        raise AcquisitionError("encoded vtable source process differs")
    identities = {key: value for key, value in binding.items() if isinstance(value, dict) and "path" in value}
    for key, identity in identities.items():
        if key == "binary":
            continue
        path = _safe_path(Path(identity["path"]))
        _file_record(path)


        if path.stat().st_mtime_ns // 100 + 116444736000000000 < current[1]:
            raise AcquisitionError("encoded vtable source predates the current process")
    known_method_pointers = frozenset(row[0] for row in binding["metadata_map"])
    del binding["metadata_map"], binding["pairs"]
    iraw = Path(identities["type_identity_inventory"]["path"]).read_bytes()
    ih = _IDENTITY_HEADER.unpack_from(iraw)
    identity_rows = [_IDENTITY_RECORD.unpack_from(iraw, _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size) for index in range(ih[5])]
    vtables = load_runtime_vtable_interfaces(
        model_path=inputs["vtable_interface_model"], inventory_path=inputs["vtable_interface_inventory"],
        expected_executable_sha256=binding["binary"]["sha256"],
        expected_type_identity_inventory_sha256=identities["type_identity_inventory"]["sha256"],
        expected_type_graph_inventory_sha256=identities["type_graph_inventory"]["sha256"],
        expected_method_detail_inventory_sha256=identities["method_detail_inventory"]["sha256"])
    if len(vtables["records"]) != len(identity_rows):
        raise AcquisitionError("encoded vtable TypeDef counts differ")
    rows, cursor = [], 0
    for index, (identity, native) in enumerate(zip(identity_rows, vtables["records"])):
        if identity[0] != index or identity[3] != native[0] or native[5] != cursor or native[3] or native[4]:
            raise AcquisitionError("encoded vtable source class/range relation differs")
        rows.append((index, identity[7], native[0], native[1]))
        cursor += native[1]
    if cursor != len(vtables["vtable_entries"]):
        raise AcquisitionError("encoded vtable source slots are not closed")
    method_header, _, _ = _method_rows(Path(identities["method_detail_inventory"]["path"]).read_bytes())
    helper = binding["interface_map_contract"]
    contract = _current_code_contract(binary, binding)
    _private_json(output_dir / "runtime-encoded-vtable-plan.private.json", {
        "schema": "alpha.runtime-encoded-vtable-plan/v1", "target": binding["binary"],
        "process_id": current[0], "creation_filetime": current[1], "inputs": identities,
        "helper_owner_only": helper, "code_contract_owner_only": asdict(contract),
        "type_count": len(rows), "vtable_word_count": cursor,
        "source_snapshot_used": False, "metadata_complete": False})
    captures = []
    def capture(ranges):
        directory = output_dir / f"observation-{len(captures) + 1:03d}"
        observed = read_current_runtime_ranges(binary=binary, ranges=ranges, output_dir=directory,
            wine=wine, wineprefix=wineprefix, compiler=compiler)
        captures.append(file_identity(directory / "runtime-ranges.private.json"))
        return observed
    records, words, counts = _collect_words(contract, rows, capture=capture, method_count=method_header[5],
                                           known_method_pointers=known_method_pointers)
    if len(records) != len(rows) or len(words) != cursor:
        raise AcquisitionError("encoded vtable observation does not close its full source domain")
    for key, identity in identities.items():
        if file_identity(Path(identity["path"])) != identity:
            raise AcquisitionError("encoded vtable input changed: " + key)
    dependency_sha = hashlib.sha256(json.dumps(identities, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    header = _HEADER.pack(_MAGIC, 2, _HEADER.size, _TYPE.size, 8, len(rows), len(words), current[0], current[1],
                          binding["binary"]["sha256"].encode(), dependency_sha.encode())
    if sys.byteorder != "little":
        words.byteswap()
    payload = header + b"".join(_TYPE.pack(*record) for record in records) + words.tobytes()
    path = output_dir / "runtime-encoded-vtables.private.bin"
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "wb") as output:
        output.write(payload)
        output.flush()
        os.fsync(output.fileno())
    if path.read_bytes() != payload:
        raise AcquisitionError("encoded vtable output byte roundtrip failed")
    model = {"schema": _SCHEMA, "status": "runtime-observed",
        "target": {"executable_sha256": binding["binary"]["sha256"], "process_id": current[0], "creation_filetime": current[1]},
        "inputs": identities, "inventory": file_identity(path), "counts": counts,
        "code_contract_owner_only": asdict(contract), "observations": captures,
        "checks": {"current_code_contract_unique": True, "all_nonempty_source_guards_match_selected_branch": True,
                   "all_slot_addresses_verified": True, "all_source_slots_accounted": True,
                   "native_pointer_array_boundaries_match_vtable_counts": True,
                   "all_native_method_pointers_in_current_metadata_domain": True,
                   "all_pointer_dependencies_reobserved": True, "all_observations_two_passes": True,
                   "direct_branch_indexes_in_range": True, "input_identities_unchanged": True,
                   "byte_roundtrip_exact": True, "no_snapshot_dependency": True},
        "metadata_complete": False, "semantic_projection_complete": False,
        "pending_domains": ["native tag semantic roles", "raw zero slot semantics", "MethodSpec/GenericInst closure"]}
    _private_json(output_dir / "runtime-encoded-vtables.private.json", model)
    return model


from pathlib import Path

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError
from alpha.p35 import _owner_file, _validated_native_receipt as legacy_receipt
from alpha.h02 import file_identity, read_json

SCHEMA = "alpha.runtime-proto-input/v1"
SOURCES = {
    "model": ("references", "runtime-type-reference.private.json"),
    "type_reference_inventory": ("references", "runtime-type-reference.private.bin"),
    "type_identity_inventory": ("identity", "runtime-type-identity.private.bin"),
    "type_graph_inventory": ("type-graph", "runtime-type-graph.private.bin"),
    "method_detail_inventory": ("methods", "runtime-method-detail.private.bin"),
    "native_member_detail_inventory": ("members", "runtime-native-member-detail.private.bin"),
    "event_module_inventory": ("events", "runtime-event-module.private.bin"),
    "method_generic_inventory": ("method-generics", "runtime-method-generics.private.bin"),
    "generic_parameter_detail_inventory": ("generic-parameters", "runtime-generic-parameter-detail.private.bin"),
    "metadata_usage_pair_inventory": ("strings", "runtime-metadata-usage-pairs.private.bin"),
    "metadata_usage_value_model": ("strings", "runtime-metadata-usage-values.private.json"),
    "metadata_usage_value_inventory": ("strings", "runtime-metadata-usage-values.private.bin"),
}
_CLIENT_VERSION = re.compile(r"^[0-9]+(?:\.[0-9]+){2,3}$")


def _validated_version_target(value):
    if not isinstance(value, dict):
        raise AcquisitionError("proto input target is absent")
    version = value.get("client_version")
    build = value.get("client_build")
    if (
        not isinstance(version, str)
        or not _CLIENT_VERSION.fullmatch(version)
        or not isinstance(build, str)
        or not (build == version or build.startswith(version + "_"))
    ):
        raise AcquisitionError("proto input target version is invalid")
    return value


def _client_version_evidence(executable: Path) -> dict[str, Any]:
    from alpha.h02 import bundle_version, file_identity

    executable = executable.expanduser()
    data_dir = executable.parent / f"{executable.stem}_Data"
    managers = data_dir / "globalgamemanagers"
    if not managers.is_file() or managers.is_symlink():
        raise AcquisitionError("proto input target version is unavailable")
    unity = bundle_version(managers)
    return {
        "client_version": unity["version"],
        "client_build": unity["build"],
        "version_authority": unity["authority"],
        "version_source": file_identity(managers),
    }


def proto_input_target(identity):
    if not isinstance(identity, dict):
        raise AcquisitionError("proto input target is absent")
    target = dict(identity)
    executable_text = target.get("executable_path")
    if isinstance(executable_text, str) and executable_text:
        derived = _client_version_evidence(Path(executable_text))
        for key in ("client_version", "client_build"):
            recorded = target.get(key)
            if recorded is not None and recorded != derived[key]:
                raise AcquisitionError(
                    "proto input target version conflicts with the running client"
                )
            target[key] = derived[key]
        target["version_authority"] = derived["version_authority"]
        target["version_source"] = derived["version_source"]
    return _validated_version_target(target)


def write_proto_input(*, session, output_dir):
    session.assert_current()
    target = proto_input_target(session.journal.get("identity"))
    stages = sorted({stage for stage, name in SOURCES.values()})


    visited = set()
    def verify(stage):
        if stage in visited:
            return
        visited.add(stage)
        session._verify_stage(stage)
        for dependency in session.journal["stages"][stage]["dependencies"]:
            verify(dependency)
    for stage in stages:
        verify(stage)
    inputs = {key: file_identity(session.root / stage / name)
              for key, (stage, name) in SOURCES.items()}
    inputs["binary"] = file_identity(Path(session.journal["identity"]["executable_path"]))
    evidence = {stage: session.journal["stages"][stage] for stage in sorted(visited)}
    receipt = {"schema": SCHEMA, "status": "runtime-inventory-validated",
               "target": target, "inputs": inputs,
               "source_root": str(session.root), "stages": evidence,
               "checks": {"upstream_artifacts_verified": True, "current_process_verified": True},
               "metadata_artifacts_required": False, "proto_complete": False}
    session.assert_current()
    path = output_dir / "runtime-proto-input.private.json"
    _private_json(path, receipt)
    return {"status": "complete", "receipt": file_identity(path)}


def validated_proto_receipt(path, *, allow_type_method_metadata=False):
    path = _owner_file(path, label="proto input")
    receipt = read_json(path)
    if receipt.get("schema") != SCHEMA:
        return legacy_receipt(path, allow_type_method_metadata=allow_type_method_metadata)
    checks = receipt.get("checks")
    if (receipt.get("status") != "runtime-inventory-validated"
            or not isinstance(checks, dict) or not checks
            or not all(value is True for value in checks.values())):
        raise AcquisitionError("proto input validation is incomplete")
    _validated_version_target(receipt.get("target"))
    inputs = receipt.get("inputs")
    if not isinstance(inputs, dict) or set(inputs) != set(SOURCES) | {"binary"}:
        raise AcquisitionError("proto input domains are incomplete")
    paths = {}
    for key, record in inputs.items():
        if not isinstance(record, dict) or not isinstance(record.get("path"), str):
            raise AcquisitionError("proto input binding is invalid")
        candidate = Path(record["path"])
        if key != "binary":
            candidate = _owner_file(candidate, label=key)
        if candidate.is_symlink() or file_identity(candidate) != record:
            raise AcquisitionError(f"proto input changed: {key}")
        paths[key] = candidate
    if inputs["binary"]["sha256"] != receipt.get("target", {}).get("executable_sha256"):
        raise AcquisitionError("proto input executable differs")
    return receipt, paths
