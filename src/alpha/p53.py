import re
import shutil
import tempfile
from pathlib import Path
from typing import Any, Callable

from alpha.h01 import AcquisitionError
from alpha.p35 import build_runtime_dummy_output
from alpha.p46 import capture_runtime_assembly_identities
from alpha.p31 import capture_runtime_direct_interfaces
from alpha.p44 import capture_runtime_enum_constants
from alpha.p55 import (
    reconstruct_runtime_global_metadata,
)
from alpha.p33 import (
    RUNTIME_NATIVE_OUTPUT_COMPLETE_STATUS, RUNTIME_NATIVE_OUTPUT_STATUSES,
    render_runtime_native_output,
)
from alpha.p54 import capture_runtime_parameter_defaults
from alpha.h02 import publish_new_directory, write_new_json


RUNTIME_METADATA_OUTPUT_SCHEMA = "alpha.runtime-metadata-output/v1"

_CLOSURE_STAGE = re.compile(r"field-references(?:-(\d{3}))?$")


def _complete_stage(journal: dict[str, Any], name: str) -> dict[str, Any]:
    stage = (journal.get("stages") or {}).get(name)
    if not isinstance(stage, dict) or stage.get("status") != "complete":
        raise AcquisitionError(
            f"runtime metadata stage requires a completed inventory stage: {name}"
        )
    return stage


def _latest_closure_stage(journal: dict[str, Any]) -> str:
    rows = [
        (stage.get("started_ns") or 0, name)
        for name, stage in (journal.get("stages") or {}).items()
        if _CLOSURE_STAGE.fullmatch(name)
        and isinstance(stage, dict)
        and stage.get("status") == "complete"
    ]
    if not rows:
        raise AcquisitionError(
            "runtime metadata stages require the completed field reference fixed point"
        )
    return max(rows)[1]


def inventory_binding(root: Path, journal: dict[str, Any]) -> dict[str, Any]:
    root = root.expanduser().absolute()
    references_stage = _latest_closure_stage(journal)
    suffix = _CLOSURE_STAGE.fullmatch(references_stage).group(1)
    suffix = "" if suffix is None else "-" + suffix
    closure = {
        "descriptor_values": f"descriptor-values{suffix}",
        "constructed_layout": f"constructed-layout{suffix}",
        "field_type_store": f"field-type-store{suffix}",
        "references": references_stage,
    }
    for name in (
        "identity", "type-graph", "methods", "members", "events", "strings",
        "method-generics", "generic-parameters-full", "materializer-live",
        closure["descriptor_values"], closure["constructed_layout"],
        closure["field_type_store"], closure["references"],
    ):
        _complete_stage(journal, name)
    reference_dir = root / references_stage / "references"
    paths: dict[str, Any] = {
        "stages": {
            **closure,
            "strings": "strings",
            "generic_parameters_full": "generic-parameters-full",
        },
        "type_reference_model": reference_dir / "runtime-type-reference.private.json",
        "type_reference_inventory": reference_dir / "runtime-type-reference.private.bin",
        "type_identity_inventory": root / "identity/runtime-type-identity.private.bin",
        "type_identity_model": root / "identity/runtime-type-identity.private.json",
        "type_graph_inventory": root / "type-graph/runtime-type-graph.private.bin",
        "type_graph_model": root / "type-graph/runtime-type-graph.private.json",
        "method_detail_inventory": root / "methods/runtime-method-detail.private.bin",
        "native_member_detail_inventory":
            root / "members/runtime-native-member-detail.private.bin",
        "event_module_inventory": root / "events/runtime-event-module.private.bin",
        "event_module_model": root / "events/runtime-event-module.private.json",
        "string_literal_model": root / "strings/runtime-string-literals.private.json",
        "string_literal_inventory": root / "strings/runtime-string-literals.private.bin",
        "metadata_usage_pair_model":
            root / "strings/runtime-metadata-usage-pairs.private.json",
        "metadata_usage_pair_inventory":
            root / "strings/runtime-metadata-usage-pairs.private.bin",
        "metadata_usage_value_model":
            root / "strings/runtime-metadata-usage-values.private.json",
        "metadata_usage_value_inventory":
            root / "strings/runtime-metadata-usage-values.private.bin",
        "metadata_usage_member_model":
            root / "strings/runtime-metadata-usage-members.private.json",
        "metadata_usage_member_inventory":
            root / "strings/runtime-metadata-usage-members.private.bin",
        "method_generic_model":
            root / "method-generics/runtime-method-generics.private.json",
        "method_generic_inventory":
            root / "method-generics/runtime-method-generics.private.bin",
        "generic_parameter_detail_model": root / "generic-parameters-full" /
            "runtime-generic-parameter-detail.private.json",
        "generic_parameter_detail_inventory": root / "generic-parameters-full" /
            "runtime-generic-parameter-detail.private.bin",
        "constructed_generic_layout_model": root / closure["constructed_layout"] /
            "runtime-constructed-generic-layout.private.json",
        "constructed_generic_layout_inventory": root / closure["constructed_layout"] /
            "runtime-constructed-generic-layout.private.bin",
        "constructed_field_capture": root / closure["field_type_store"] /
            "runtime-field-type-store.private.json",
        "descriptor_value_model": root / closure["descriptor_values"] /
            "runtime-type-descriptor-values.private.json",
        "descriptor_value_inventory": root / closure["descriptor_values"] /
            "runtime-type-descriptor-values.private.bin",
        "materializer_model": root / "materializer-live" /
            "runtime-type-materializer.validated.private.json",
    }
    for key, path in paths.items():
        if key == "stages":
            continue
        if not isinstance(path, Path) or not path.is_file() or path.is_symlink():
            raise AcquisitionError(
                f"runtime metadata inventory artifact is unavailable: {key}"
            )
    return paths


def capture_metadata_stages(*, session, live, output_dir: Path,
                            progress: Callable[[str], None] | None = None,
                            reconstruct: bool = True,
                            domain_observations: tuple[Path, ...] = ()) -> dict[str, Any]:
    root = session.root
    binding = inventory_binding(root, session.journal)
    output_dir = output_dir.expanduser().absolute()
    if session.journal.get("metadata_output_dir") != str(output_dir):
        session.journal["metadata_output_dir"] = str(output_dir)
        session._save()

    def report(name: str) -> None:
        if progress:
            progress(name)

    def run(name: str, callback, dependencies: tuple[str, ...], **options):
        session.register_planned_stage("acquisition", name)
        return session.run(name, callback, dependencies=dependencies, **options)

    inventory_dependencies = (
        "identity", "type-graph", "methods", "members", "events", "strings",
        "method-generics", "generic-parameters-full",
        binding["stages"]["descriptor_values"],
        binding["stages"]["constructed_layout"],
        binding["stages"]["field_type_store"],
        binding["stages"]["references"],
    )
    render_inputs = {key: value for key, value in binding.items() if key != "stages"}

    def render(output: Path, *, enum=None, parameters=None, assembly=None,
               direct=None,
               receipt_name="alpha-native-output-receipt.private.json"):
        return render_runtime_native_output(
            binary=live["binary"],
            type_reference_model=render_inputs["type_reference_model"],
            type_reference_inventory=render_inputs["type_reference_inventory"],
            type_identity_inventory=render_inputs["type_identity_inventory"],
            type_graph_inventory=render_inputs["type_graph_inventory"],
            method_detail_inventory=render_inputs["method_detail_inventory"],
            native_member_detail_inventory=render_inputs["native_member_detail_inventory"],
            event_module_inventory=render_inputs["event_module_inventory"],
            event_module_model=render_inputs["event_module_model"],
            string_literal_model=render_inputs["string_literal_model"],
            string_literal_inventory=render_inputs["string_literal_inventory"],
            metadata_usage_pair_model=render_inputs["metadata_usage_pair_model"],
            metadata_usage_pair_inventory=render_inputs["metadata_usage_pair_inventory"],
            metadata_usage_value_model=render_inputs["metadata_usage_value_model"],
            metadata_usage_value_inventory=render_inputs["metadata_usage_value_inventory"],
            metadata_usage_member_model=render_inputs["metadata_usage_member_model"],
            metadata_usage_member_inventory=render_inputs["metadata_usage_member_inventory"],
            method_generic_model=render_inputs["method_generic_model"],
            method_generic_inventory=render_inputs["method_generic_inventory"],
            generic_parameter_detail_model=render_inputs["generic_parameter_detail_model"],
            generic_parameter_detail_inventory=render_inputs["generic_parameter_detail_inventory"],
            constructed_generic_layout_model=render_inputs["constructed_generic_layout_model"],
            constructed_generic_layout_inventory=render_inputs[
                "constructed_generic_layout_inventory"],
            constructed_field_capture=render_inputs["constructed_field_capture"],
            direct_interface_model=(
                direct / "runtime-direct-interface.private.json" if direct else None
            ),
            direct_interface_inventory=(
                direct / "runtime-direct-interface.private.bin" if direct else None
            ),
            enum_constant_model=enum,
            enum_constant_inventory=enum.with_suffix(".bin") if enum is not None else None,
            parameter_default_model=parameters,
            parameter_default_inventory=(
                parameters.with_suffix(".bin") if parameters is not None else None
            ),
            assembly_identity_model=assembly,
            assembly_identity_inventory=(
                assembly.with_suffix(".bin") if assembly is not None else None
            ),
            output_dir=output,
        )

    report("metadata-direct-interfaces")
    run(
        "direct-interfaces",
        lambda out: capture_runtime_direct_interfaces(
            binary=live["binary"],
            type_identity_model=render_inputs["type_identity_model"],
            type_identity_inventory=render_inputs["type_identity_inventory"],
            type_graph_model=render_inputs["type_graph_model"],
            type_graph_inventory=render_inputs["type_graph_inventory"],
            type_reference_model=render_inputs["type_reference_model"],
            type_reference_inventory=render_inputs["type_reference_inventory"],
            constructed_generic_model=render_inputs["constructed_generic_layout_model"],
            constructed_generic_inventory=render_inputs[
                "constructed_generic_layout_inventory"],
            output_dir=out, wine=live["wine"], wineprefix=live["wineprefix"],
            compiler=live["compiler"], timeout=live["timeout"],
        ),
        inventory_dependencies,
        accepted_statuses=("runtime-validated",),
    )

    report("metadata-native-output-initial")
    initial = run(
        "native-output-initial",
        lambda out: render(out, direct=root / "direct-interfaces"),
        (*inventory_dependencies, "direct-interfaces"),
        accepted_statuses=RUNTIME_NATIVE_OUTPUT_STATUSES,
    )
    initial_receipt = root / "native-output-initial" / (
        "alpha-native-output-receipt.private.json")

    report("metadata-enum-constants")
    enum_result = run(
        "enum-constants",
        lambda out: capture_runtime_enum_constants(
            native_output_receipt=initial_receipt,
            runtime_materializer_model=render_inputs["materializer_model"],
            output_dir=out, wine=live["wine"], wineprefix=live["wineprefix"],
            compiler=live["compiler"], timeout=live["timeout"],
        ),
        ("native-output-initial", "materializer-live"),
        accepted_statuses=("runtime-validated",),
    )
    enum_model = root / "enum-constants/runtime-enum-constants.private.json"

    report("metadata-parameter-defaults")
    run(
        "parameter-defaults",
        lambda out: capture_runtime_parameter_defaults(
            native_output_receipt=initial_receipt,
            runtime_materializer_model=render_inputs["materializer_model"],
            runtime_inventory_dispatch=None,
            output_dir=out, wine=live["wine"], wineprefix=live["wineprefix"],
            compiler=live["compiler"], timeout=live["timeout"],
        ),
        ("native-output-initial", "materializer-live"),
        accepted_statuses=("runtime-validated",),
    )
    parameter_model = root / "parameter-defaults/runtime-parameter-defaults.private.json"


    report("metadata-native-output-enum-constants")
    run(
        "native-output-enum-constants",
        lambda out: render(out, enum=enum_model, parameters=parameter_model,
                           direct=root / "direct-interfaces"),
        (*inventory_dependencies, "direct-interfaces", "enum-constants",
         "parameter-defaults"),
        accepted_statuses=RUNTIME_NATIVE_OUTPUT_STATUSES,
    )
    enum_receipt = root / "native-output-enum-constants" / (
        "alpha-native-output-receipt.private.json")

    report("metadata-assembly-identities")
    run(
        "assembly-identities",
        lambda out: capture_runtime_assembly_identities(
            native_output_receipt=enum_receipt,
            runtime_materializer_model=render_inputs["materializer_model"],
            runtime_inventory_dispatch=None,
            output_dir=out, wine=live["wine"], wineprefix=live["wineprefix"],
            compiler=live["compiler"], timeout=live["timeout"],
        ),
        ("native-output-enum-constants", "materializer-live"),
        accepted_statuses=("runtime-validated",),
    )
    assembly_model = root / "assembly-identities/runtime-assembly-identities.private.json"

    report("metadata-native-output-final")
    final = run(
        "native-output-final",
        lambda out: render(out, enum=enum_model, parameters=parameter_model,
                           assembly=assembly_model, direct=root / "direct-interfaces"),
        (*inventory_dependencies, "native-output-enum-constants",
         "assembly-identities"),
        accepted_statuses=(RUNTIME_NATIVE_OUTPUT_COMPLETE_STATUS,),
    )
    final_receipt = root / "native-output-final" / (
        "alpha-native-output-receipt.private.json")

    report("metadata-dummy-dll")
    dummy = run(
        "dummy-dll",
        lambda out: build_runtime_dummy_output(
            native_output_receipt=final_receipt, output_dir=out,
        ),
        ("native-output-final",),
    )

    reconstruction = None
    if reconstruct:
        report("metadata-structural-reconstruction")

        def build_metadata(out: Path):
            from alpha.p57 import evaluate_metadata_domains
            from alpha.p57 import load_domain_observations
            observations = load_domain_observations(
                domain_observations,
                executable_sha256=session.journal["identity"]["executable_sha256"],
            )
            evidence = evaluate_metadata_domains(
                identity_inventory=render_inputs["type_identity_inventory"],
                native_member_inventory=render_inputs[
                    "native_member_detail_inventory"],
                assembly_identity_model=root / "assembly-identities" /
                    "runtime-assembly-identities.private.json",
                event_model_path=root / "events/runtime-event-module.private.json",
                event_accessor_path=root / "events/runtime-event-accessors.private.json",
                native_output_receipt=final_receipt,
                module_getter_observation_path=root /
                    "events/runtime-module-name-getter-io.private.json",
                executable_sha256=session.journal["identity"]["executable_sha256"],
                observations=observations,
            )
            return reconstruct_runtime_global_metadata(
                native_output_receipt=final_receipt,
                type_descriptor_value_model=render_inputs["descriptor_value_model"],
                type_descriptor_value_inventory=render_inputs["descriptor_value_inventory"],
                type_reference_model=render_inputs["type_reference_model"],
                type_reference_inventory=render_inputs["type_reference_inventory"],
                full_generic_parameter_detail_model=render_inputs[
                    "generic_parameter_detail_model"],
                full_generic_parameter_detail_inventory=render_inputs[
                    "generic_parameter_detail_inventory"],
                output_dir=out,
                allow_incomplete=True,
                domain_evidence=evidence,
            )

        reconstruction = run(
            "metadata-structural-reconstruction", build_metadata,
            ("native-output-final", binding["stages"]["descriptor_values"],
             binding["stages"]["references"]),
            accepted_statuses=("structural-reconstruction-incomplete",),
        )

    report("metadata-publish")

    def publish(_stage_dir: Path) -> dict[str, Any]:
        output_dir.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
        staging = Path(tempfile.mkdtemp(prefix=".metadata-publish-",
                                        dir=output_dir.parent))
        artifacts: dict[str, Any] = {}
        try:
            for name in ("dump.cs", "script.json", "il2cpp.h", "stringliteral.json"):
                source = root / "native-output-final" / name
                if not source.is_file():
                    raise AcquisitionError(f"final native output is incomplete: {name}")
                target = staging / name
                target.write_bytes(source.read_bytes())
                target.chmod(0o600)
                artifacts[name] = {"bytes": target.stat().st_size}
            dummy_bundle = root / "dummy-dll/runtime-dummy-bundle.private"
            if not dummy_bundle.is_dir():
                raise AcquisitionError("runtime DummyDll bundle is missing")
            shutil.copytree(dummy_bundle, staging / "runtime-dummy-bundle.private")
            dummy_dll = root / "dummy-dll/DummyDll"
            if not dummy_dll.is_dir():
                raise AcquisitionError("runtime DummyDll output is missing")
            shutil.copytree(dummy_dll, staging / "DummyDll")
            if reconstruction is not None:
                metadata = root / "metadata-structural-reconstruction/global-metadata.dat"
                if not metadata.is_file():
                    raise AcquisitionError("structural global metadata output is missing")
                shutil.copy2(metadata, staging / "global-metadata.dat")
            payload = {
            "schema": RUNTIME_METADATA_OUTPUT_SCHEMA,
            "status": "metadata-artifacts-complete",
            "metadata_complete": False,
            "target": {"executable_sha256": session.journal["identity"][
                "executable_sha256"]},
            "native_output": {"status": final.get("status"),
                              "counts": final.get("counts")},
            "dummy_dll": {"status": dummy.get("status")},
            "structural_reconstruction": (
                None if reconstruction is None else {
                    "status": reconstruction.get("status"),
                    "pending_domains": reconstruction.get("pending_domains"),
                }
            ),
            "remaining_domains": (
                [] if reconstruction is None
                else list(reconstruction.get("pending_domains") or [])
            ),
            "artifacts": artifacts,
            "checks": {
                "final_native_output_complete": (
                    final.get("status")
                    == "target-bound-standard-metadata-artifacts-complete"
                ),
                "dummy_dll_complete": dummy.get("status") == "complete",
                "structural_reconstruction_present": reconstruction is not None,
                "metadata_complete_not_claimed": True,
            },
            }
            if not all(value is True for value in payload["checks"].values()):
                raise AcquisitionError("runtime metadata output checks did not all pass")
            write_new_json(staging / "alpha-metadata-output-receipt.json", payload)
            publish_new_directory(staging, output_dir)
            write_new_json(Path(_stage_dir) / "publish.private.json", payload)
        finally:
            if staging.exists():
                shutil.rmtree(staging, ignore_errors=True)
        return payload

    published = run("metadata-publish", publish,
                    ("native-output-final", "dummy-dll") + (
                        ("metadata-structural-reconstruction",)
                        if reconstruction is not None else ()
                    ),
                    accepted_statuses=("metadata-artifacts-complete",))
    return published
