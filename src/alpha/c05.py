from pathlib import Path
import hashlib
import json

from alpha.h01 import AcquisitionError
from alpha.c04 import _verify_files
from alpha.h02 import file_identity, read_json


def _sources(proof, parent, reference, selected, *, output_role, selected_role):
    records = proof.get("inputs")
    if not isinstance(records, dict):
        raise AcquisitionError("raw output name source records are absent")
    anchors = dict(parent.get("inputs", {}))
    for role in ("native_inventory", "type_identity_inventory", "raw_type_observation"):
        if role in reference["inputs"]:
            anchors[role] = reference["inputs"][role]
    anchors["type_identity_inventory"] = selected["type_identity_inventory"]
    anchors["reflection_semantics"] = reference["inputs"]["semantics"]
    anchors[output_role] = selected[selected_role]
    for role, expected in anchors.items():
        if role in records and records[role] != expected:
            raise AcquisitionError("raw output name source differs from selected capture inputs")
    if records.get(output_role) != selected[selected_role]:
        raise AcquisitionError("raw output name display inventory is not independently bound")
    _verify_files(records)
    return records


def bind_output_raw_names(runtime, *, reference_model_path, selected, required=False):
    from alpha.c06 import load_raw_type_names
    from alpha.c02 import load_raw_method_parameter_names
    from alpha.c04 import load_raw_member_names
    from alpha.c10 import load_raw_event_module_names
    record = file_identity(reference_model_path)
    reference = read_json(reference_model_path)
    if record != selected["model"] or reference.get("inventory") != selected["type_reference_inventory"]:
        raise AcquisitionError("raw output name root model differs from selected inputs")
    if not isinstance(reference.get("raw_names"), dict):
        if required:
            raise AcquisitionError("raw output names require current TypeRef source evidence")
        return None
    target = reference["target"]
    if target.get("executable_sha256") != selected["binary"]["sha256"]:
        raise AcquisitionError("raw output name executable differs")
    identity = dict(target, image_base=target["image_base_owner_only"])
    for field, role in (("identity", "type_identity_inventory"), ("methods", "method_detail_inventory"),
                        ("native", "native_member_detail_inventory"), ("events", "event_module_inventory"),
                        ("references", "type_reference_inventory")):
        if hashlib.sha256(getattr(runtime, field)).hexdigest() != selected[role]["sha256"]:
            raise AcquisitionError("raw output name runtime bytes differ from selected inventory")
    roles = (("type_identity_model", "type_identity_inventory", "type_identity_inventory"),
             ("method_detail_model", "method_detail_inventory", "method_detail_inventory"),
             ("native_member_detail_model", "member_detail_inventory", "native_member_detail_inventory"),
             ("event_module_model", "event_module_inventory", "event_module_inventory"))
    models = {}
    for role, _, selected_role in roles:
        source = reference["inputs"][role]
        _verify_files({role: source})
        model = read_json(Path(source["path"]))
        if model.get("inventory", model.get("identity_inventory")) != selected[selected_role]:
            raise AcquisitionError("raw output domain model has a different inventory")
        if not isinstance(model.get("raw_names"), dict):
            raise AcquisitionError("raw output domain model has no original names")
        models[role] = model
    rid_base = models["type_identity_model"].get("counts", {}).get("metadata_token_rid_base")
    if type(rid_base) is not int or rid_base not in (0, 1):
        raise AcquisitionError("raw output metadata token convention is absent")
    all_names = {key: {} for key in ("type", "type_namespace", "method", "parameter", "field", "property", "event", "module")}
    inventories = {}
    for role, output_role, selected_role in roles:
        parent = models[role]; proof = parent["raw_names"]
        records = _sources(proof, parent, reference, selected, output_role=output_role, selected_role=selected_role)
        arguments = dict(model=proof, inventory_path=Path(proof["inventory"]["path"]),
                         expected_identity=identity, expected_inputs=records)
        if role == "type_identity_model":
            names, _ = load_raw_type_names(**arguments, expected_count=runtime.type_count)
        elif role == "method_detail_model":
            names, _ = load_raw_method_parameter_names(**arguments,
                expected_counts={"method": runtime.method_count, "parameter": runtime.parameter_count})
        elif role == "native_member_detail_model":
            names, _ = load_raw_member_names(**arguments,
                expected_counts={"field": runtime.field_count, "property": runtime.property_count},
                expected_type_count=runtime.type_count, expected_rid_base=rid_base)
        else:
            names, _ = load_raw_event_module_names(**arguments,
                expected_counts={"event": runtime.event_count, "module": runtime.module_count},
                type_count=runtime.type_count, rid_base=rid_base)
        for name in names:
            domain = all_names.setdefault(name.domain, {})
            if name.index in domain:
                raise AcquisitionError("raw output name domains overlap")
            domain[name.index] = name.value
        inventories[role] = proof["inventory"]
    _verify_files({role: reference["inputs"][role] for role, _, _ in roles} | {"root": record})
    runtime.raw_metadata_names = all_names
    return {"inventories": inventories, "counts": {key: len(value) for key, value in all_names.items()},
            "original_source_replay": True, "metadata_complete": False}


def original_metadata_name(runtime, domain, index):
    names = getattr(runtime, "raw_metadata_names", {})
    if domain not in names or index not in names[domain]:
        raise AcquisitionError("metadata name has no original observation in the selected domain")
    value = names[domain][index]


    if value is None and domain == "type_namespace":
        return ""
    if value is None or b"\0" in value:
        raise AcquisitionError("original metadata name cannot be represented by this string-index format")
    try:
        return value.decode("utf-8", errors="strict")
    except UnicodeError as error:
        raise AcquisitionError("original metadata name is not representable as strict UTF-8") from error


def original_module_name(runtime, pointer):


    for index, observed_pointer in enumerate(runtime.module_names):
        if observed_pointer == pointer:
            return original_metadata_name(runtime, "module", index)
    raise AcquisitionError("metadata module has no observed owner")


from pathlib import Path
import struct

from alpha.h01 import AcquisitionError
from alpha.c01 import RawMetadataName, _binding_digest, encode_raw_metadata_names, decode_raw_metadata_names
from alpha.c04 import _verify_files
from alpha.h02 import write_new_bytes
from alpha.p01 import string_layout_replay_scope
from alpha.c01 import source_verification_scope
from alpha.h02 import file_identity, read_json

HEADER = struct.Struct("<8sIIIIQQ32s")
ROW = struct.Struct("<QQIIIIQQ")
DOMAINS = ("type_reference", "type_reference_namespace")


_DOMAIN_RANK = {domain: rank for rank, domain in enumerate(DOMAINS)}
ROLES = ("semantics", "type_identity_inventory", "type_graph_inventory", "seed", "string_layout_model")
SCOPE = "type-reference-raw-names"
CHECKS = {"original_observations_replayed": True, "raw_duplicate_names_match": True,
          "display_projection_exact": True, "string_io_replayed": True,
          "byte_roundtrip": True, "semantic_roundtrip": True, "source_files_unchanged": True}


def capture_binding(identity, inputs):
    return {key: identity[key] for key in ("executable_sha256", "process_id", "creation_filetime")} | {
        "inputs": {role: inputs[role]["sha256"] for role in ROLES}}


def transport_digest(binding):
    return _binding_digest(binding, dict.fromkeys(DOMAINS, 0))


_DISPLAY_NAME_CACHE: dict[tuple[bytes, bool], bytes] = {}
_DISPLAY_NAME_CACHE_LIMIT = 1 << 19


def display_name_bytes(value, index, *, namespace=False):
    if value:
        cache_key = (value, namespace)
        cached = _DISPLAY_NAME_CACHE.get(cache_key)
        if cached is not None:
            return cached
        if min(value) >= 32:


            display = bytes(value)
        else:
            display = bytes(95 if byte < 32 else byte for byte in value)
        if len(_DISPLAY_NAME_CACHE) >= _DISPLAY_NAME_CACHE_LIMIT:
            _DISPLAY_NAME_CACHE.clear()
        _DISPLAY_NAME_CACHE[cache_key] = display
        return display
    display = bytes(95 if byte < 32 else byte for byte in (value or b""))
    return display if display or namespace else f"EmptyTypeRef_{index:X}".encode("ascii")


def decode_observation(raw, *, binding):
    if not isinstance(raw, bytes) or len(raw) < HEADER.size:
        raise AcquisitionError("raw TypeRef observation is truncated")
    h = HEADER.unpack_from(raw)
    count, size = h[5:7]
    start = HEADER.size + count * ROW.size
    if (h[:5] != (b"ALPHATN1", 1, HEADER.size, ROW.size, 0) or not 0 < count <= 500000 or
        size > 268435456 or start + size != len(raw) or h[7] != transport_digest(binding)):
        raise AcquisitionError("raw TypeRef header, extent or source binding differs")
    pairs, cursor = {}, 0


    for index, (descriptor, observed_index, null_name, null_space, n, s, no, so) in enumerate(
        ROW.iter_unpack(memoryview(raw)[HEADER.size : HEADER.size + count * ROW.size])
    ):
        if (not descriptor or descriptor & 7 or descriptor in pairs or observed_index != index or
            null_name not in (0, 1) or null_space not in (0, 1) or null_name and n or null_space and s or
            no != cursor or so != cursor + n or n > 65536 or s > 65536 or n + s > size - cursor):
            raise AcquisitionError("raw TypeRef descriptor, order or pool range differs")
        values = (None if null_name else raw[start + no:start + no + n],
                  None if null_space else raw[start + so:start + so + s])
        for value in values:
            if value is not None:
                try:
                    value.decode("utf-8", errors="strict")
                except UnicodeError as error:
                    raise AcquisitionError("raw TypeRef managed name is not strict UTF-8") from error
        pairs[descriptor] = values
        cursor += n + s
    if cursor != size:
        raise AcquisitionError("raw TypeRef pool is not closed")
    return pairs


def project_display(raw, pairs, *, executable_sha256):
    from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER as H, RUNTIME_TYPE_REFERENCE_RECORD as R
    if len(raw) < H.size:
        raise AcquisitionError("TypeRef display header is truncated")
    h = H.unpack_from(raw)
    cursor = H.size + h[5] * R.size + (h[7] + h[8]) * 8
    if (h[:5] != (b"ALPHATR1", 1, H.size, R.size, 0) or h[5] != len(pairs) or
        h[6] > h[5] or cursor + h[9] != len(raw) or h[12] != executable_sha256.encode("ascii")):
        raise AcquisitionError("TypeRef display domain or executable differs")
    names, seen = [], set()


    name_domain, namespace_domain = DOMAINS
    append_name = names.append
    seen_add = seen.add
    display_cache = _DISPLAY_NAME_CACHE
    pairs_get = pairs.get
    for index, row in enumerate(
        R.iter_unpack(memoryview(raw)[H.size : H.size + h[5] * R.size])
    ):
        descriptor = row[0]
        entry = pairs_get(descriptor)
        if descriptor in seen or entry is None:
            raise AcquisitionError("TypeRef display descriptor differs from raw observation")
        seen_add(descriptor)
        value, namespace = entry


        display = display_cache.get((value, False))
        if display is None:
            display = display_name_bytes(value, index)
        offset, length = row[17], row[5]
        if offset != cursor or length != len(display) or raw[offset:offset + length] != display:
            raise AcquisitionError("TypeRef raw name does not project to exact display bytes")
        append_name(RawMetadataName(name_domain, index, value))
        cursor += length
        display = display_cache.get((namespace, True))
        if display is None:
            display = display_name_bytes(namespace, index, namespace=True)
        offset, length = row[18], row[6]
        if offset != cursor or length != len(display) or raw[offset:offset + length] != display:
            raise AcquisitionError("TypeRef raw name does not project to exact display bytes")
        append_name(RawMetadataName(namespace_domain, index, namespace))
        cursor += length
    if cursor != len(raw):
        raise AcquisitionError("TypeRef display pool does not close")
    return tuple(names)


_REPLAY_CAPTURE_CACHE: dict[tuple, dict] = {}
_REPLAY_CAPTURE_CACHE_LIMIT = 16


def _replay_capture(capture, identity):
    from alpha.p18 import load_runtime_string_layout_candidate
    from alpha.c04 import validate_string_layout_io
    inputs = capture["inputs"]
    records = dict(inputs, observation=capture["observation"], display=capture["display"], string_io=capture["string_io"])
    _verify_files(records)
    binding = capture_binding(identity, inputs)
    if capture.get("binding") != binding:
        raise AcquisitionError("raw TypeRef capture source identities differ")
    cache_key = (
        binding["executable_sha256"], binding["process_id"], binding["creation_filetime"],
        identity["image_base"], identity["image_bytes"],
        capture["observation"]["sha256"], capture["display"]["sha256"],
        capture["string_io"]["sha256"],
    )
    cached = _REPLAY_CAPTURE_CACHE.get(cache_key)
    if cached is not None:
        return dict(cached), cache_key
    pairs = decode_observation(Path(capture["observation"]["path"]).read_bytes(), binding=binding)
    display = Path(capture["display"]["path"]).read_bytes()
    names = project_display(display, pairs,
                            executable_sha256=identity["executable_sha256"])
    from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER as H
    h = H.unpack_from(display)
    if (h[10:12] != (identity["image_base"], identity["image_bytes"]) or
        h[13:17] != tuple(inputs[key]["sha256"].encode("ascii") for key in
                          ("seed", "type_identity_inventory", "type_graph_inventory", "semantics"))):
        raise AcquisitionError("raw TypeRef display source header differs")
    contract = load_runtime_string_layout_candidate(model_path=Path(inputs["string_layout_model"]["path"]),
        expected_identity=identity, expected_inputs={key: inputs[key] for key in ("snapshot", "native_inventory")})
    validate_string_layout_io(observation=read_json(Path(capture["string_io"]["path"])), names=names,
        expected_process_id=identity["process_id"], contract=contract, expected_scope=SCOPE)
    _verify_files(records)
    if len(_REPLAY_CAPTURE_CACHE) >= _REPLAY_CAPTURE_CACHE_LIMIT:
        _REPLAY_CAPTURE_CACHE.clear()
    _REPLAY_CAPTURE_CACHE[cache_key] = pairs
    return pairs, cache_key


_REPLAY_NAMES_CACHE: dict[tuple, tuple] = {}
_REPLAY_NAMES_CACHE_LIMIT = 2


def _identity_cache_key(identity):
    return json.dumps(identity, sort_keys=True, ensure_ascii=True)


@string_layout_replay_scope()
@source_verification_scope()
def _replay(captures, identity, output):

    if not isinstance(captures, list) or not 1 <= len(captures) <= 256:
        raise AcquisitionError("raw TypeRef capture chain is absent or exceeds the replay bound")
    seen = set()
    for capture in captures:
        if not isinstance(capture, dict) or not isinstance(capture.get("observation"), dict):
            raise AcquisitionError("raw TypeRef capture chain record is malformed")
        digest = capture["observation"].get("sha256")
        if not isinstance(digest, str) or len(digest) != 64 or digest in seen:
            raise AcquisitionError("raw TypeRef capture chain repeats or lacks an observation")
        seen.add(digest)
    pairs = {}
    capture_keys = []
    for capture in captures:
        capture_pairs, capture_key = _replay_capture(capture, identity)
        capture_keys.append(capture_key)
        for descriptor, values in capture_pairs.items():
            if descriptor in pairs and pairs[descriptor] != values:
                raise AcquisitionError("raw TypeRef duplicate names differ across captures")
            pairs[descriptor] = values
    _verify_files({"output": output})
    replay_key = (_identity_cache_key(identity), tuple(capture_keys), output["sha256"])
    cached_names = _REPLAY_NAMES_CACHE.get(replay_key)
    if cached_names is not None:
        return cached_names
    names = project_display(Path(output["path"]).read_bytes(), pairs,
                            executable_sha256=identity["executable_sha256"])
    _verify_files({"output": output})
    if len(_REPLAY_NAMES_CACHE) >= _REPLAY_NAMES_CACHE_LIMIT:
        _REPLAY_NAMES_CACHE.clear()
    _REPLAY_NAMES_CACHE[replay_key] = names
    return names


def _normalized_binding(identity, captures, output):
    sources = {"output": output["sha256"]}
    for index, capture in enumerate(captures):
        for role in ("observation", "display", "string_io"):
            sources[f"capture_{index}_{role}"] = capture[role]["sha256"]
        for role, record in capture["inputs"].items():
            sources[f"capture_{index}_input_{role}"] = record["sha256"]
    return {key: identity[key] for key in ("executable_sha256", "process_id", "creation_filetime")} | {"inputs": sources}


def _capture_record(plan):
    from alpha.p12 import _seal_runtime_output
    if plan.get("contract", {}).get("lossless_reference_names_required") is not True:
        raise AcquisitionError("TypeRef plan has no required lossless name contract")
    identity = dict(plan["target"], image_base=plan["target"]["image_base_owner_only"])
    records = {key: value for key, value in plan["inputs"].items() if value.get("path") is not None}
    records["seed"] = plan["seed"]
    for key in ("raw_observation_path", "string_layout_io_path"):
        if not _seal_runtime_output(Path(plan[key])):
            raise AcquisitionError("raw TypeRef required observation is absent")
    return {"inputs": records, "binding": capture_binding(identity, records),
        "observation": file_identity(Path(plan["raw_observation_path"])),
        "display": file_identity(Path(plan["output_path"])),
        "string_io": file_identity(Path(plan["string_layout_io_path"]))}


@string_layout_replay_scope()
@source_verification_scope()
def raw_values_for_merge(plan):
    identity = dict(plan["target"], image_base=plan["target"]["image_base_owner_only"])
    _verify_files({key: plan["inputs"][key] for key in ("base_type_reference_model", "base_type_reference_inventory")})
    base = read_json(Path(plan["inputs"]["base_type_reference_model"]["path"]))
    if base.get("inventory") != plan["inputs"]["base_type_reference_inventory"]:
        raise AcquisitionError("raw TypeRef base merge inventory differs")
    proof = base.get("raw_names")
    names = load_reference_names(model=proof, expected_identity=identity, expected_inventory=base["inventory"])
    from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER as H, RUNTIME_TYPE_REFERENCE_RECORD as R
    data = Path(base["inventory"]["path"]).read_bytes()
    count = len(names) // 2
    pairs = {R.unpack_from(data, H.size + index * R.size)[0]: (names[index].value, names[count + index].value)
             for index in range(count)}
    extension, _extension_key = _replay_capture(_capture_record(plan), identity)
    for descriptor in pairs.keys() & extension.keys():
        if pairs[descriptor] != extension[descriptor]:
            raise AcquisitionError("raw TypeRef duplicate names differ across captures")
    _verify_files({"base": base["inventory"]})
    return pairs, extension


@string_layout_replay_scope()
@source_verification_scope()
def normalize_reference_names(*, plan, output_path, base_model=None):
    identity = dict(plan["target"], image_base=plan["target"]["image_base_owner_only"])
    captures = []
    if base_model is not None:
        load_reference_names(model=base_model["raw_names"], expected_identity=identity,
                             expected_inventory=base_model["inventory"])
        captures.extend(base_model["raw_names"]["captures"])
    captures.append(_capture_record(plan))
    output = file_identity(output_path)
    names = _replay(captures, identity, output)
    counts = dict.fromkeys(DOMAINS, len(names) // 2)
    binding = _normalized_binding(identity, captures, output)
    encoded = encode_raw_metadata_names(names, binding=binding, expected_counts=counts)
    normalized_path = Path(plan["raw_names_path"])
    write_new_bytes(normalized_path, encoded)
    model = {"schema": "alpha.raw-reference-names/v1", "identity": identity, "captures": captures,
        "output": output, "inventory": file_identity(normalized_path), "counts": counts,
        "checks": dict(CHECKS), "metadata_complete": False}


    load_reference_names(model=model, expected_identity=identity, expected_inventory=output,
                         _expected_encoding=encoded)
    return model


_REFERENCE_NAMES_LOAD_CACHE: dict[bytes, tuple] = {}
_REFERENCE_NAMES_LOAD_CACHE_LIMIT = 2


def load_reference_names(*, model, expected_identity, expected_inventory, _expected_encoding=None):
    if (not isinstance(model, dict) or model.get("schema") != "alpha.raw-reference-names/v1" or
        model.get("identity") != expected_identity or model.get("output") != expected_inventory or
        model.get("checks") != CHECKS or model.get("metadata_complete") is not False):
        raise AcquisitionError("raw TypeRef model or explicitly selected identity differs")
    load_key = json.dumps([model, expected_identity, expected_inventory],
                          sort_keys=True, ensure_ascii=True).encode("ascii")
    _verify_files({"normalized": model["inventory"]})
    cached = _REFERENCE_NAMES_LOAD_CACHE.get(load_key)
    if cached is not None:
        return cached
    names = _replay(model["captures"], expected_identity, expected_inventory)
    counts = dict.fromkeys(DOMAINS, len(names) // 2)
    if model.get("counts") != counts:
        raise AcquisitionError("raw TypeRef normalized domain differs")
    binding = _normalized_binding(expected_identity, model["captures"], expected_inventory)
    _verify_files({"normalized": model["inventory"]})
    raw = Path(model["inventory"]["path"]).read_bytes()
    decoded = decode_raw_metadata_names(raw, expected_binding=binding, expected_counts=counts)
    domain_rank = _DOMAIN_RANK
    canonical = tuple(sorted(names, key=lambda name: (domain_rank[name.domain], name.index)))
    if decoded != canonical or (_expected_encoding if _expected_encoding is not None else
                                encode_raw_metadata_names(names, binding=binding, expected_counts=counts)) != raw:
        raise AcquisitionError("raw TypeRef normalized byte or semantic roundtrip differs")
    _verify_files({"normalized": model["inventory"]})
    if len(_REFERENCE_NAMES_LOAD_CACHE) >= _REFERENCE_NAMES_LOAD_CACHE_LIMIT:
        _REFERENCE_NAMES_LOAD_CACHE.clear()
    _REFERENCE_NAMES_LOAD_CACHE[load_key] = decoded
    return decoded


def bind_output_reference_names(*, model_path, inventory, executable_sha256, runtime=None):
    record = file_identity(model_path)
    model = read_json(model_path)
    if model.get("inventory") != inventory or model.get("target", {}).get("executable_sha256") != executable_sha256:
        raise AcquisitionError("output TypeRef inventory or executable differs")
    proof = model.get("raw_names")
    if proof is None:
        if model.get("proof_limits", {}).get("lossless_type_reference_names") is True:
            raise AcquisitionError("output TypeRef model claims absent raw name proof")
        return None
    identity = dict(model["target"], image_base=model["target"]["image_base_owner_only"])
    names = load_reference_names(model=proof, expected_identity=identity, expected_inventory=inventory)
    if runtime is not None:
        import hashlib
        from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER as H, RUNTIME_TYPE_REFERENCE_RECORD as R
        if hashlib.sha256(runtime.references).hexdigest() != inventory["sha256"]:
            raise AcquisitionError("output TypeRef memory differs from selected raw name inventory")
        count = len(names) // 2
        runtime.raw_reference_names = {
            R.unpack_from(runtime.references, H.size + index * R.size)[0]: names[index].value
            for index in range(count)}
    _verify_files({"model": record})
    return {"inventory": proof["inventory"], "counts": proof["counts"], "checks": dict(CHECKS),
        "null_names": sum(name.value is None for name in names),
        "empty_names": sum(name.value == b"" for name in names),
        "metadata_complete": False}


def metadata_reference_name(runtime, descriptor):
    names = getattr(runtime, "raw_reference_names", None)
    if not isinstance(names, dict) or descriptor not in names:
        raise AcquisitionError("metadata TypeRef name has no original observation")
    value = names[descriptor]
    if value is None:
        raise AcquisitionError("absent TypeRef name cannot be silently converted to an empty metadata string")
    if b"\0" in value:
        raise AcquisitionError("original TypeRef name cannot fit a NUL-terminated metadata string")
    return value.decode("utf-8", errors="strict")
