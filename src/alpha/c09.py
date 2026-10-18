import hashlib
import json
from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.c02 import validate_probe
from alpha.c08 import derive_bound_operations
from alpha.c04 import _verify_files
from alpha.h02 import file_identity, read_json


SOURCE_ROLES = ("type_identity_inventory", "type_identity_model", "type_identity_plan",
    "native_inventory", "native_semantics", "semantics", "string_layout_model")


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def getter_binding(*, native, inputs, operation, identity):
    sources = dict(inputs, **{key: native[key] for key in SOURCE_ROLES})
    return {"process_id": identity["process_id"], "creation_filetime": identity["creation_filetime"],
        "executable_sha256": native["binary"]["sha256"],
        "inputs": {key: value["sha256"] for key, value in sources.items()},
        "operation_sha256": hashlib.sha256(canonical(operation).encode("ascii")).hexdigest()}


def validate_module_getter_evidence(*, plan, names):
    from alpha.p12 import _seal_runtime_output
    if (plan.get("contract", {}).get("module_getter_observations_required") is not True
            or not isinstance(plan.get("module_getter_observation_path"), str)):
        raise AcquisitionError("event/module plan lacks code-derived Module getter evidence")
    _verify_files(plan["inputs"])
    binary = Path(plan["target"]["executable_path"])
    executable = file_identity(binary)
    if executable["sha256"] != plan["target"]["executable_sha256"]:
        raise AcquisitionError("Module getter executable changed after capture")
    type_plan = read_json(Path(plan["inputs"]["type_identity_plan"]["path"]))
    if canonical(type_plan.get("target")) != canonical(plan["target"]):
        raise AcquisitionError("Module getter TypeDef source process identity differs")
    native = dict(plan["inputs"], binary=executable, type_count=plan["contract"]["type_count"],
        image_base=plan["target"]["image_base_owner_only"], image_bytes=plan["target"]["image_bytes"],
        string_class=type_plan.get("runtime_classes_owner_only", {}).get("string"))
    operation, inputs, modules = derive_bound_operations(native=native, binary=binary,
        **{key: Path(plan["inputs"][key]["path"]) for key in
           ("method_detail_model", "method_detail_inventory", "ancestry_inventory")}, process_identity=plan["target"])
    binding = getter_binding(native=native, inputs=inputs, operation=operation, identity=plan["target"])
    if (canonical(operation) != canonical(plan.get("module_getter_operation_owner_only"))
            or canonical(binding) != canonical(plan.get("module_getter_binding"))
            or len(modules) != plan["contract"]["module_count"]):
        raise AcquisitionError("Module getter operation or explicit source binding changed")
    path = Path(plan["module_getter_observation_path"])
    if not _seal_runtime_output(path):
        raise AcquisitionError("Module getter I/O observation is absent")
    record = file_identity(path)
    observed, checks = validate_probe(read_json(path), model=operation, modules=modules, binding=binding)
    expected = tuple(name for name in names if name.domain == "module")
    if observed != expected:
        raise AcquisitionError("Module getter names differ from independently replayed raw output")
    _verify_files(dict(plan["inputs"], module_getter_observation=record))
    return {"inventory": record, "operation": operation, "binding": binding, "evidence": checks,
        "checks": {"module_getter_rederived_from_current_sources": True,
                   "module_getter_repeated_io_replayed": True,
                   "module_getter_raw_output_exact": True},
        "module_name_role_proven": False, "image_file_name_role_proven": False, "metadata_complete": False}
