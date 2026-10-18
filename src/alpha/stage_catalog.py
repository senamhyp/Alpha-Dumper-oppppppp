
BOOTSTRAP_STAGES = (
    "memory",
    "classes",
    "helpers",
    "helpers-live",
    "materializer",
    "materializer-live",
    "semantics",
    "semantics-live",
    "semantics-complete",
)

PROTO_INVENTORY_STAGES = (
    "native-semantics",
    "ancestry",
    "string-layout",
    "identity",
    "method-names",
    "methods",
    "members",
    "events",
    "type-graph",
    "base-references",
    "strings",
    "method-generics",
    "generic-parameters",
    "references",
)

FULL_INVENTORY_STAGES = (
    *PROTO_INVENTORY_STAGES,
    "field-type-aliases",
    "generic-parameters-full",
    "class-extents",
    "vtables",
    "constructed-vtables",
    "constructed-methods",
    "encoded-vtables",
    "vtable-declarations",
    "interface-method-maps",
)


METADATA_ARTIFACT_STAGES = (
    "native-output-initial",
    "enum-constants",
    "parameter-defaults",
    "native-output-enum-constants",
    "assembly-identities",
    "native-output-final",
    "dummy-dll",
    "metadata-structural-reconstruction",
    "metadata-publish",
)


def acquisition_stage_plan(
    *,
    include_inventory: bool,
    proto_only: bool,
    include_metadata: bool = False,
) -> tuple[str, ...]:
    stages = list(BOOTSTRAP_STAGES)
    if proto_only:
        stages.extend(PROTO_INVENTORY_STAGES)
    elif include_inventory:
        stages.extend(FULL_INVENTORY_STAGES)
    if include_metadata:


        if not include_inventory and not proto_only:
            stages.extend(FULL_INVENTORY_STAGES)
        stages.append("direct-interfaces")
        stages.extend(METADATA_ARTIFACT_STAGES)
    return tuple(stages)


SALVAGE_POLICY: dict[str, tuple[str, str]] = {


    "memory": (
        "recapture",
        "",
    ),


    "methods": (
        "recapture",
        "",
    ),
    "members": (
        "recapture",
        "",
    ),
    "identity": (
        "recapture",
        "",
    ),
    "base-references": (
        "recapture",
        "",
    ),
    "descriptor-values": (
        "recapture",
        "",
    ),
    "method-generics": (
        "recapture",
        "",
    ),
    "generic-parameters": (
        "recapture",
        "",
    ),
    "references": (
        "recapture",
        "",
    ),
    "constructed-layout": (
        "recapture",
        "",
    ),


    "strings": (
        "recapture",
        "",
    ),
    "method-names": (
        "recapture",
        "",
    ),
    "field-type-store": (
        "recapture",
        "",
    ),
}


def salvage_eligible_stages() -> frozenset:
    return frozenset(
        name
        for name, (verdict, _reason) in SALVAGE_POLICY.items()
        if verdict == "carry"
    )


def salvage_recapture_reason(name: str) -> str:
    policy = SALVAGE_POLICY.get(name)
    if policy is not None:
        return policy[1]
    return ""
