from collections import deque
import re

from alpha.h01 import AcquisitionError
from alpha.c01 import decode_x64


REG = re.compile(r"r(?:ax|bx|cx|dx|si|di|bp|sp|[89]|1[0-5])$")
VOLATILE = ("rax", "rcx", "rdx", "r8", "r9", "r10", "r11")
MASK = (1 << 64) - 1


def instructions(code):
    return [(offset, *text.split(None, 1)) if len(text.split(None, 1)) == 2 else (offset, text, "")
            for offset, text in decode_x64(code)]


def number(text):
    try: return int(text, 0)
    except ValueError: return None


def plus(left, right):
    if left is None or right is None: return None
    if left[0] == "constant" and right[0] != "constant": left, right = right, left
    if right[0] != "constant": return None
    if left[0] in ("constant", "stack"):
        return (left[0], left[1] + right[1])
    if left[0] == "field": return ("field_address", right[1])
    if left[0] == "field_address": return ("field_address", left[1] + right[1])
    if left[0] == "field_word": return ("decoded", left[1], "add", right[1] & MASK)
    if left[0] == "decoded" and left[2] == "add":
        return ("decoded", left[1], "add", (left[3] + right[1]) & MASK)
    if left[0] == "decoded": return ("decoded_address", left, right[1])
    if left[0] == "decoded_address": return ("decoded_address", left[1], left[2] + right[1])
    if left[0] == "call": return ("object_address", left, right[1])
    if left[0] == "object_address": return ("object_address", left[1], left[2] + right[1])
    return None


def address(operand, state):
    match = re.fullmatch(r"(?:[A-Z0-9]+ PTR )?\[([^\]]+)\]", operand)
    if not match: return None
    expression = match[1].replace("*1", "")
    terms = re.findall(r"[+-]?[^+-]+", expression)
    value = ("constant", 0)
    for term in terms:
        sign = -1 if term.startswith("-") else 1
        atom = term.lstrip("+-")
        immediate = number(atom)
        part = ("constant", sign * immediate) if immediate is not None else state.get(atom) if sign == 1 else None
        value = plus(value, part)
    return value


def value(operand, state):
    if REG.fullmatch(operand): return state.get(operand)
    register = full_register(operand)
    partial = state.get(register) if register else None
    if operand.startswith("e") and partial and partial[0] == "descriptor_load" and partial[2] <= 4:
        return partial
    immediate = number(operand)
    if immediate is not None: return ("constant", immediate)
    where = address(operand, state)
    width = {"BYTE": 1, "WORD": 2, "DWORD": 4, "QWORD": 8}.get(operand.split()[0] if operand else "")
    if where and where[0] in ("decoded", "decoded_address") and width:
        return ("descriptor_load", where, width)
    if not operand.startswith("QWORD PTR "): return None
    if where == ("field",): return ("field_word", 0)
    if where and where[0] == "field_address": return ("field_word", where[1])
    if where and where[0] == "stack": return state.get(where)
    return None


def full_register(operand):
    if REG.fullmatch(operand): return operand
    aliases = {"eax": "rax", "ebx": "rbx", "ecx": "rcx", "edx": "rdx", "esi": "rsi", "edi": "rdi", "ebp": "rbp", "esp": "rsp",
               "al": "rax", "ah": "rax", "bl": "rbx", "bh": "rbx", "cl": "rcx", "ch": "rcx", "dl": "rdx", "dh": "rdx", "ax": "rax", "bx": "rbx", "cx": "rcx", "dx": "rdx", "sil": "rsi", "dil": "rdi"}
    if operand in aliases: return aliases[operand]
    match = re.fullmatch(r"(r(?:[89]|1[0-5]))[dwb]", operand)
    return match[1] if match else None


def assign(destination, result, state):
    register = full_register(destination)
    if register:
        state.pop(register, None)
        if result is not None and REG.fullmatch(destination): state[register] = result
        return
    where = address(destination, state)
    if where and where[0] == "stack":
        widths = {"BYTE": 1, "WORD": 2, "DWORD": 4, "QWORD": 8, "XMMWORD": 16, "YMMWORD": 32}
        width = widths.get(destination.split()[0], 64)
        for key in list(state):
            if isinstance(key, tuple) and key[0] == "stack" and key[1] < where[1] + width and where[1] < key[1] + 8:
                del state[key]
        if result is not None and destination.startswith("QWORD PTR "): state[where] = result


def signed_target(operand, pointer):
    target = number(operand)
    if target is None: return None
    return pointer + (target - (1 << 64) if target >= 1 << 63 else target)


def trace(code, pointer, *, field_argument):

    rows = instructions(code); table = {row[0]: row for row in rows}
    nexts = {row[0]: rows[i + 1][0] if i + 1 < len(rows) else None for i, row in enumerate(rows)}
    if not rows or rows[0][0] != 0: raise AcquisitionError("field store code lacks entry")
    states = {0: {field_argument: ("field",), "rsp": ("stack", 0)}}
    pending = deque([0]); iterations = 0

    def step(offset, before):
        _, op, operand = table[offset]; state = dict(before)
        args = operand.split(",")
        successors = [nexts[offset]]; call = store = None
        if op in ("ret", "int3", "ud2"): successors = []
        elif op == "call":
            target = signed_target(operand, pointer)
            call = dict(instruction_offset=offset, target_pointer=target, rcx=state.get("rcx"), rdx=state.get("rdx"))
            for register in VOLATILE: state.pop(register, None)
            state["rax"] = ("call", offset, target)
        elif op.startswith("j"):
            target = signed_target(operand, 0)
            if op == "jmp": successors = [target]
            else: successors.append(target)
            for target in successors:
                if target is not None and 0 <= target < len(code) and target not in table:
                    raise AcquisitionError("field store branch enters undecoded instruction")
        elif op in ("mov", "movabs", "movzx") and len(args) == 2:
            destination, source = args; result = value(source, state)
            where = address(destination, state)
            width = {"QWORD": 8, "DWORD": 4}.get(destination.split()[0])
            if width and where and where[0] == "object_address":
                store = dict(instruction_offset=offset, object_call=where[1], object_offset=where[2], value=result, width=width)
            assign(destination, result, state)
            if op == "movzx" and result and result[0] == "descriptor_load" and result[2] in (1, 2) and destination.startswith("e"):
                register = full_register(destination)
                if register: state[register] = result
        elif op == "lea" and len(args) == 2: assign(args[0], address(args[1], state), state)
        elif op in ("add", "sub", "xor") and len(args) == 2:
            left, right = value(args[0], state), value(args[1], state)
            if op == "sub" and right and right[0] == "constant": right = ("constant", -right[1])
            result = plus(left, right) if op in ("add", "sub") else None
            if op == "xor" and left and right:
                if left[0] == "constant": left, right = right, left
                if left[0] == "field_word" and right[0] == "constant": result = ("decoded", left[1], "xor", right[1] & MASK)
            assign(args[0], result, state)
        elif op == "push":
            saved = value(operand, state); stack = plus(state.get("rsp"), ("constant", -8))
            state.pop("rsp", None)
            if stack:
                state["rsp"] = stack
                if saved: state[stack] = saved
        elif op == "pop":
            stack = state.get("rsp"); saved = state.get(stack) if stack else None
            assign(operand, saved, state)
            if stack: state["rsp"] = plus(stack, ("constant", 8))
        elif op in ("test", "cmp", "bt", "nop", "data16", "cs"): pass
        elif op == "xchg" and len(args) == 2:
            left, right = value(args[0], state), value(args[1], state)
            assign(args[0], right, state); assign(args[1], left, state)
        else:

            if args: assign(args[0], None, state)
            if op in ("mul", "imul", "div", "idiv") and len(args) == 1:
                state.pop("rax", None); state.pop("rdx", None)
        return state, [target for target in successors if target in table], call, store

    while pending:
        offset = pending.popleft(); iterations += 1
        if iterations > 100000: raise AcquisitionError("field store dataflow does not converge")
        state, successors, _, _ = step(offset, states[offset])
        for successor in successors:
            old = states.get(successor)
            merged = state if old is None else {key: val for key, val in old.items() if state.get(key) == val}
            if old is None or merged != old:
                states[successor] = dict(merged); pending.append(successor)
    calls, stores = [], []
    for offset, before in sorted(states.items()):
        _, _, call, store = step(offset, before)
        if call: calls.append(call)
        if store: stores.append(store)
    return dict(calls=calls, stores=stores, reached_instructions=len(states))


def getter_offset(code, *, width=8):
    rows = instructions(code)
    if len(rows) < 2 or rows[0][1] != "mov" or rows[1][1] != "ret":
        raise AcquisitionError("field type getter is not a direct object load")
    args = rows[0][2].split(",")
    where = address(args[1], {"rcx": ("call", 0, None)}) if len(args) == 2 else None
    destination, memory = ("rax", "QWORD PTR ") if width == 8 else ("eax", "DWORD PTR ") if width == 4 else (None, "!")
    if len(args) != 2 or args[0] != destination or not args[1].startswith(memory) or not where or where[0] != "object_address":
        raise AcquisitionError("field type getter has an unsupported ABI")
    return where[2]


def derive_store_decoder(code, pointer, cached_offset):
    result = trace(code, pointer, field_argument="rdx")
    calls = {row["instruction_offset"]: row for row in result["calls"]}
    candidates = []
    for row in result["stores"]:
        returned = row["value"]
        if row["width"] != 8 or row["object_offset"] != cached_offset or not returned or returned[0] != "call": continue
        call = calls.get(returned[1]); argument = call.get("rcx") if call else None
        if not argument or argument[0] != "decoded" or call["target_pointer"] is None: continue
        if argument[1] < 0 or argument[1] % 8: continue
        candidates.append(dict(raw_qword_offset=argument[1], operation=argument[2], key=argument[3],
            type_object_helper=call["target_pointer"], call_instruction_offset=call["instruction_offset"],
            store_instruction_offset=row["instruction_offset"], object_field_offset=cached_offset,
            object_allocation_call=row["object_call"]))
    if len(candidates) != 1: raise AcquisitionError("field type store decoder is not unique")
    return dict(candidate=candidates[0], candidate_count=1, reached_instructions=result["reached_instructions"],
                native_field_type_role_proven=False, all_factory_paths_proven=False, metadata_complete=False)


def derive_attribute_load(code, pointer, *, candidate, attribute_object_offset):
    stores = trace(code, pointer, field_argument="rdx")["stores"]
    result = []
    for row in stores:
        observed = row["value"]
        if (row["width"] != 4 or row["object_offset"] != attribute_object_offset
                or row["object_call"] != tuple(candidate["object_allocation_call"])
                or not observed or observed[0] != "descriptor_load"): continue
        address_value, width = observed[1:]
        delta = 0
        if address_value[0] == "decoded_address":
            _, address_value, delta = address_value
        if address_value[0] != "decoded" or address_value[1:3] != (candidate["raw_qword_offset"], candidate["operation"]): continue
        if candidate["operation"] == "add": delta += (address_value[3] - candidate["key"]) & MASK
        elif address_value[3] != candidate["key"]: continue
        if not 0 <= delta <= 64 or width not in (1, 2): continue
        result.append(dict(descriptor_attribute_offset=delta, descriptor_attribute_bytes=width,
            object_attribute_offset=attribute_object_offset, store_instruction_offset=row["instruction_offset"]))
    if len(result) != 1: raise AcquisitionError("field descriptor attribute load is not unique")
    return result[0]


def derive_current_store(*, binary, semantics, types, snapshot):

    import bisect

    from alpha.c04 import MappedPE
    from alpha.p04 import bounded_current_body
    selected = {}
    for key in ("field.from_handle", "field.type", "field.attributes"):
        matches = [row for row in semantics.get("operations", []) if row.get("key") == key]
        if len(matches) != 1 or matches[0].get("semantic_identity_resolved") is not True:
            raise AcquisitionError("native field store semantic operation is not uniquely resolved")
        selected[key] = matches[0]["method_pointer"]
    lower, upper = snapshot.image_range
    pointers = sorted({p for row in types for p in row.method_pointers if lower <= p < upper})


    codes = {}; offsets = {}

    def _following(pointer: int) -> int | None:
        position = bisect.bisect_right(pointers, pointer)
        if position == 0 or position >= len(pointers) or pointers[position - 1] != pointer:
            return None
        return pointers[position]
    with MappedPE(binary) as image:
        for key, width in (("field.type", 8), ("field.attributes", 4)):
            pointer = selected[key]; end = _following(pointer)
            if end is None or not 0 < end - pointer <= 65536 or not image.executable_rva(pointer - lower):
                raise AcquisitionError("native field store getter lacks a current code bound")
            bounds = image.bounded_code(pointer - lower, end - lower)
            if bounds is None or bounds[1] - bounds[0] != end - pointer:
                raise AcquisitionError("native field store getter mapping differs")
            codes[pointer] = bytes(image._mapping[bounds[0]:bounds[1]])
            offsets[key] = getter_offset(codes[pointer], width=width)
        entry, body, thunks = bounded_current_body(image, selected["field.from_handle"], image_base=lower)
        codes[entry] = body
        for thunk in thunks: codes[thunk["pointer"]] = bytes.fromhex(thunk["code_hex"])
        targets = {row["target_pointer"] for row in trace(body, entry, field_argument="rcx")["calls"]
                   if row["rdx"] == ("field",) and row["target_pointer"] is not None}
        if len(targets) != 1: raise AcquisitionError("native field store factory helper is not unique")
        helper, body, thunks = bounded_current_body(image, targets.pop(), image_base=lower)
        codes[helper] = body
        for thunk in thunks: codes[thunk["pointer"]] = bytes.fromhex(thunk["code_hex"])
        result = derive_store_decoder(body, helper, offsets["field.type"])
        result["attributes"] = derive_attribute_load(body, helper, candidate=result["candidate"], attribute_object_offset=offsets["field.attributes"])
        pointer, body, thunks = bounded_current_body(image, result["candidate"]["type_object_helper"], image_base=lower)
        codes[pointer] = body
        for thunk in thunks: codes[thunk["pointer"]] = bytes.fromhex(thunk["code_hex"])
    if any(snapshot.read(pointer, len(raw)) != raw for pointer, raw in codes.items()):
        raise AcquisitionError("native field store current executable and snapshot code differ")
    result.update(source_operations=selected, factory_helper=helper,
        snapshot_code_bytes_verified=sum(map(len, codes.values())),
        current_code_observations=[dict(pointer=p, code_hex=raw.hex()) for p, raw in sorted(codes.items())])
    return result


from dataclasses import asdict, dataclass
from typing import Any

from alpha.h01 import ContractViolation
from alpha.h02 import generation_id


RUNTIME_INVENTORY_SCHEMA = "alpha.runtime-inventory-contract/v1"
DECLARED_MEMBER_BINDING_FLAGS = 0x3E
DECLARED_MEMBER_BINDING_FLAG_NAMES = (
    "DeclaredOnly",
    "Instance",
    "Static",
    "Public",
    "NonPublic",
)


@dataclass(frozen=True)
class RuntimeInventoryOperation:
    key: str
    runtime_owners: tuple[str, ...]
    runtime_name: str
    parameter_count: int
    stage: str
    semantic_role: str


OPERATIONS = (
    RuntimeInventoryOperation(
        "thread.current",
        ("System.Threading.Thread",),
        "get_CurrentThread",
        0,
        "execution",
        "managed-thread-observation-gate",
    ),
    RuntimeInventoryOperation(
        "domain.current",
        ("System.AppDomain",),
        "get_CurrentDomain",
        0,
        "root",
        "current-managed-domain",
    ),
    RuntimeInventoryOperation(
        "domain.assemblies",
        ("System.AppDomain",),
        "GetAssemblies",
        0,
        "root",
        "all-loaded-assemblies",
    ),
    RuntimeInventoryOperation(
        "assembly.types",
        ("System.Reflection.MonoAssembly", "System.Reflection.Assembly"),
        "GetTypes",
        0,
        "assembly",
        "all-assembly-types",
    ),
    RuntimeInventoryOperation(
        "assembly.name",
        ("System.Reflection.MonoAssembly", "System.Reflection.Assembly"),
        "GetName",
        0,
        "assembly",
        "assembly-identity-object",
    ),
    RuntimeInventoryOperation(
        "assembly.full_name",
        ("System.Reflection.MonoAssembly", "System.Reflection.Assembly"),
        "get_FullName",
        0,
        "assembly",
        "assembly-full-name",
    ),
    RuntimeInventoryOperation(
        "assembly_name.name", ("System.Reflection.AssemblyName",),
        "get_Name", 0, "assembly", "assembly-simple-name",
    ),
    RuntimeInventoryOperation(
        "assembly_name.version", ("System.Reflection.AssemblyName",),
        "get_Version", 0, "assembly", "assembly-version-object",
    ),
    RuntimeInventoryOperation(
        "assembly_name.culture_name", ("System.Reflection.AssemblyName",),
        "get_CultureName", 0, "assembly", "assembly-culture-name",
    ),
    RuntimeInventoryOperation(
        "assembly_name.flags", ("System.Reflection.AssemblyName",),
        "get_Flags", 0, "assembly", "assembly-name-flags",
    ),
    RuntimeInventoryOperation(
        "assembly_name.hash_algorithm", ("System.Reflection.AssemblyName",),
        "get_HashAlgorithm", 0, "assembly", "assembly-hash-algorithm",
    ),
    RuntimeInventoryOperation(
        "assembly_name.version_compatibility",
        ("System.Reflection.AssemblyName",), "get_VersionCompatibility", 0,
        "assembly", "assembly-version-compatibility",
    ),
    RuntimeInventoryOperation(
        "assembly_name.public_key_token", ("System.Reflection.AssemblyName",),
        "GetPublicKeyToken", 0, "assembly", "assembly-public-key-token",
    ),
    RuntimeInventoryOperation(
        "assembly_name.public_key", ("System.Reflection.AssemblyName",),
        "GetPublicKey", 0, "assembly", "assembly-public-key",
    ),
    RuntimeInventoryOperation(
        "version.major", ("System.Version",), "get_Major", 0,
        "assembly", "assembly-version-major",
    ),
    RuntimeInventoryOperation(
        "version.minor", ("System.Version",), "get_Minor", 0,
        "assembly", "assembly-version-minor",
    ),
    RuntimeInventoryOperation(
        "version.build", ("System.Version",), "get_Build", 0,
        "assembly", "assembly-version-build",
    ),
    RuntimeInventoryOperation(
        "version.revision", ("System.Version",), "get_Revision", 0,
        "assembly", "assembly-version-revision",
    ),
    RuntimeInventoryOperation(
        "type.fields",
        ("System.RuntimeType",),
        "GetFields",
        1,
        "type",
        "declared-fields-with-binding-flags",
    ),
    RuntimeInventoryOperation(
        "type.methods",
        ("System.RuntimeType",),
        "GetMethods",
        1,
        "type",
        "declared-methods-with-binding-flags",
    ),
    RuntimeInventoryOperation(
        "type.constructors",
        ("System.RuntimeType",),
        "GetConstructors",
        1,
        "type",
        "declared-constructors-with-binding-flags",
    ),
    RuntimeInventoryOperation(
        "type.properties",
        ("System.RuntimeType",),
        "GetProperties",
        1,
        "type",
        "declared-properties-with-binding-flags",
    ),
    RuntimeInventoryOperation(
        "property.attributes",
        ("System.Reflection.MonoProperty",),
        "get_Attributes",
        0,
        "type",
        "property-attributes-with-concrete-owner",
    ),
    RuntimeInventoryOperation(
        "type.events",
        ("System.RuntimeType",),
        "GetEvents",
        1,
        "type",
        "declared-events-with-binding-flags",
    ),
    RuntimeInventoryOperation(
        "event.attributes",
        ("System.Reflection.MonoEvent",),
        "get_Attributes",
        0,
        "type",
        "event-attributes-with-concrete-owner",
    ),
    RuntimeInventoryOperation(
        "type.nested_types",
        ("System.RuntimeType",),
        "GetNestedTypes",
        1,
        "type",
        "declared-nested-types-with-binding-flags",
    ),
    RuntimeInventoryOperation(
        "constructor.name",
        ("System.Reflection.MonoCMethod",),
        "get_Name",
        0,
        "type",
        "constructor-name-with-concrete-owner",
    ),
    RuntimeInventoryOperation(
        "constructor.parameters",
        ("System.Reflection.MonoCMethod",),
        "GetParameters",
        0,
        "type",
        "constructor-parameters-with-concrete-owner",
    ),
    RuntimeInventoryOperation(
        "constructor.attributes",
        ("System.Reflection.MonoCMethod",),
        "get_Attributes",
        0,
        "type",
        "constructor-attributes-with-concrete-owner",
    ),
    RuntimeInventoryOperation(
        "constructor.impl_attributes",
        ("System.Reflection.MonoCMethod",),
        "GetMethodImplementationFlags",
        0,
        "type",
        "constructor-implementation-flags-with-concrete-owner",
    ),
    RuntimeInventoryOperation(
        "type.generic_parameter_constraints",
        ("System.RuntimeType",),
        "GetGenericParameterConstraints",
        0,
        "generic",
        "generic-parameter-constraints",
    ),
    RuntimeInventoryOperation(
        "type.is_generic_parameter",
        ("System.RuntimeType",),
        "get_IsGenericParameter",
        0,
        "generic",
        "generic-parameter-shape",
    ),
    RuntimeInventoryOperation(
        "type.generic_parameter_position",
        ("System.RuntimeType",),
        "get_GenericParameterPosition",
        0,
        "generic",
        "generic-parameter-position",
    ),
    RuntimeInventoryOperation(
        "type.generic_parameter_attributes",
        ("System.RuntimeType",),
        "get_GenericParameterAttributes",
        0,
        "generic",
        "generic-parameter-attributes",
    ),
    RuntimeInventoryOperation(
        "type.is_array",
        ("System.RuntimeType",),
        "get_IsArray",
        0,
        "generic",
        "array-shape",
    ),
    RuntimeInventoryOperation(
        "type.is_pointer",
        ("System.RuntimeType",),
        "get_IsPointer",
        0,
        "generic",
        "pointer-shape",
    ),
    RuntimeInventoryOperation(
        "type.array_rank",
        ("System.RuntimeType",),
        "GetArrayRank",
        0,
        "generic",
        "array-rank",
    ),
    RuntimeInventoryOperation(
        "method.generic_arguments",
        ("System.Reflection.MonoMethod",),
        "GetGenericArguments",
        0,
        "generic",
        "method-generic-arguments",
    ),
    RuntimeInventoryOperation(
        "method.impl_attributes",
        ("System.Reflection.MonoMethod",),
        "GetMethodImplementationFlags",
        0,
        "type",
        "method-implementation-flags-with-concrete-owner",
    ),
    RuntimeInventoryOperation(
        "method.is_generic",
        ("System.Reflection.MonoMethod",),
        "get_IsGenericMethod",
        0,
        "generic",
        "method-generic-shape",
    ),
    RuntimeInventoryOperation(
        "method.is_generic_definition",
        ("System.Reflection.MonoMethod",),
        "get_IsGenericMethodDefinition",
        0,
        "generic",
        "method-generic-definition-shape",
    ),
    RuntimeInventoryOperation(
        "method.generic_definition",
        ("System.Reflection.MonoMethod",),
        "GetGenericMethodDefinition",
        0,
        "generic",
        "method-generic-definition",
    ),
)

ADDITIONAL_REQUIRED_RUNTIME_OWNERS = (
    "System.Reflection.MonoCMethod",
)


def runtime_inventory_contract() -> dict[str, Any]:
    operations = [asdict(operation) for operation in OPERATIONS]
    payload: dict[str, Any] = {
        "schema": RUNTIME_INVENTORY_SCHEMA,
        "operation_count": len(operations),
        "operations": operations,
        "additional_required_runtime_owners": list(
            ADDITIONAL_REQUIRED_RUNTIME_OWNERS
        ),
        "declared_member_binding_flags": {
            "names": list(DECLARED_MEMBER_BINDING_FLAG_NAMES),
            "value": DECLARED_MEMBER_BINDING_FLAGS,
        },
        "required_stages": ["execution", "root", "assembly", "type", "generic"],
        "resolution_policy": {
            "exact_current_target_required": True,
            "fresh_runtime_required": True,
            "all_operations_required": True,
            "one_current_implementation_across_owner_candidates_required": True,
            "declared_member_binding_flags_required": True,
            "managed_thread_observation_required_before_invocation": True,
            "all_member_object_concrete_owners_required": True,
            "native_address_in_contract": False,
            "native_offset_in_contract": False,
            "saved_dispatch_value_in_contract": False,
            "external_component_required": False,
        },
    }
    payload["contract_id"] = generation_id("runtime-inventory-contract", payload)
    validate_runtime_inventory_contract(payload)
    return payload


def validate_runtime_inventory_contract(payload: dict[str, Any]) -> None:
    if payload.get("schema") != RUNTIME_INVENTORY_SCHEMA:
        raise ContractViolation("runtime inventory contract schema is invalid")
    operations = payload.get("operations")
    if not isinstance(operations, list) or len(operations) != len(OPERATIONS):
        raise ContractViolation("runtime inventory contract is incomplete")
    keys = [item.get("key") for item in operations if isinstance(item, dict)]
    if len(keys) != len(operations) or len(set(keys)) != len(keys):
        raise ContractViolation("runtime inventory operation identities are not unique")
    observed_stages: set[str] = set()
    for operation in operations:
        owners = operation.get("runtime_owners")
        if (
            not isinstance(owners, (list, tuple))
            or not owners
            or len(set(owners)) != len(owners)
            or not all(isinstance(owner, str) and owner.startswith("System.") for owner in owners)
            or not isinstance(operation.get("runtime_name"), str)
            or not operation["runtime_name"]
            or type(operation.get("parameter_count")) is not int
            or operation["parameter_count"] < 0
            or operation.get("stage")
            not in {"execution", "root", "assembly", "type", "generic"}
        ):
            raise ContractViolation("runtime inventory operation shape is invalid")
        observed_stages.add(operation["stage"])
    if observed_stages != {"execution", "root", "assembly", "type", "generic"}:
        raise ContractViolation("runtime inventory stages are incomplete")
    if payload.get("additional_required_runtime_owners") != list(
        ADDITIONAL_REQUIRED_RUNTIME_OWNERS
    ):
        raise ContractViolation(
            "runtime inventory additional concrete owners are incomplete"
        )
    if payload.get("declared_member_binding_flags") != {
        "names": list(DECLARED_MEMBER_BINDING_FLAG_NAMES),
        "value": DECLARED_MEMBER_BINDING_FLAGS,
    }:
        raise ContractViolation(
            "runtime inventory declared-member binding flags are invalid"
        )
    policy = payload.get("resolution_policy")
    expected = {
        "exact_current_target_required": True,
        "fresh_runtime_required": True,
        "all_operations_required": True,
        "one_current_implementation_across_owner_candidates_required": True,
        "declared_member_binding_flags_required": True,
        "managed_thread_observation_required_before_invocation": True,
        "all_member_object_concrete_owners_required": True,
        "native_address_in_contract": False,
        "native_offset_in_contract": False,
        "saved_dispatch_value_in_contract": False,
        "external_component_required": False,
    }
    if not isinstance(policy, dict) or not all(
        policy.get(key) is value for key, value in expected.items()
    ):
        raise ContractViolation("runtime inventory resolution policy is unsafe")


from pathlib import Path
import re

from alpha.h01 import AcquisitionError, same_executable_path
from alpha.p01 import NATIVE_GLOBALS, NATIVE_WINDOW_PROC, NATIVE_SEND_ACTION, NATIVE_DISPATCH
from alpha.c01 import current_runtime_process_binding


def bound_creation(identity_plan, reference_model, method_model, binary):
    target = identity_plan.get("target", {})
    pid, creation = target.get("process_id"), target.get("creation_filetime")
    if (type(pid) is not int or not 0 < pid <= 0xFFFFFFFF or type(creation) is not int or not 0 < creation < 1 << 64
            or not same_executable_path(
                target.get("executable_path"), Path(binary).resolve()
            )):
        raise AcquisitionError("method generic source lacks a complete process lifetime")
    for model in (reference_model, method_model):
        other = model.get("target", {})
        if any(type(other.get(k)) is not int or other[k] != target[k] for k in ("process_id", "creation_filetime")):
            raise AcquisitionError("method generic sources belong to different process lifetimes")
    current = current_runtime_process_binding()
    if current is None:
        return pid, creation
    if not same_executable_path(current[2], target["executable_path"]):
        raise AcquisitionError("method generic source process lifetime is stale")


    return current[0], current[1]


def protect_source(source, *, creation_filetime):
    if type(creation_filetime) is not int or not 0 < creation_filetime < 1 << 64:
        raise AcquisitionError("method generic native lifetime is missing")
    def once(old, new):
        nonlocal source
        if source.count(old) != 1: raise AcquisitionError("method generic source protection seam differs")
        source = source.replace(old, new, 1)
    guard = r'''
#include <io.h>
#include <fcntl.h>
#include <sys/stat.h>
static int generic_instance_current(void) {
    FILETIME created,exited,kernel,user;
    if(GetCurrentProcessId()!=expected_pid || !GetProcessTimes(GetCurrentProcess(),&created,&exited,&kernel,&user))return 0;
    return (((uint64_t)created.dwHighDateTime<<32)|created.dwLowDateTime)==CREATIONull;
}
static FILE *method_generic_private_output(const wchar_t *path) {
    int descriptor=_wopen(path,_O_WRONLY|_O_CREAT|_O_EXCL|_O_BINARY,_S_IREAD|_S_IWRITE);
    if(descriptor<0)return NULL;
    FILE *output=_fdopen(descriptor,"wb");
    if(!output){_close(descriptor);_wremove(path);}
    return output;
}
'''.replace("CREATION", str(creation_filetime))
    once("static int readable(", guard + NATIVE_GLOBALS + "\nstatic int readable(")
    replacements = {
        "static LRESULT CALLBACK window_proc(": NATIVE_WINDOW_PROC.replace("probe_candidates()", "derive_layout()"),
        "static int send_action(": NATIVE_SEND_ACTION,
        "static int dispatch(": NATIVE_DISPATCH.replace("expected_argument_count", "expected_method_count").replace(
            "current runtime generic parameter detail inventory", "current runtime method generic inventory"),
    }
    for prefix, replacement in replacements.items():
        matches = re.findall(r"^" + re.escape(prefix) + r"[^\n]*", source, flags=re.MULTILINE)
        if len(matches) != 1: raise AcquisitionError("method generic dispatch source seam differs")
        once(matches[0], replacement)
    once("_wremove(output_path);_wremove(status_path);", "")
    once("if(GetCurrentProcessId()!=expected_pid||", "if(!generic_instance_current()||GetCurrentProcessId()!=expected_pid||")
    once('FILE*out=_wfopen(output_path,L"wb");', "FILE*out=method_generic_private_output(output_path);")
    once('FILE*out=_wfopen(status_path,L"wb");', "FILE*out=method_generic_private_output(status_path);")
    once("int ok=write_output();", "int ok=generic_instance_current()&&!InterlockedCompareExchange(&callback_active,0,0)&&write_output();")
    once(r'\"process_id\": %lu,\n', r'\"creation_filetime\": ' + str(creation_filetime) + r',\n  \"process_id\": %lu,\n')
    once(r'\"output_written\": %s,\n', r'\"callback_quiescent\": %s,\n  \"request_generation_bound\": true,\n  \"output_written\": %s,\n')
    once('failure_kind,written?"true":"false"', 'failure_kind,InterlockedCompareExchange(&callback_active,0,0)?"false":"true",written?"true":"false"')
    return source


import copy
import hashlib
import json
from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity, read_json, read_private_model


MAX_CAPTURE_JOURNAL_BYTES = 64 * 1024 * 1024


def _read_capture_journal(path: Path) -> dict:

    from alpha.p13 import _file_record, _safe_path

    path = _safe_path(path)
    before = _file_record(path)
    if before["bytes"] > MAX_CAPTURE_JOURNAL_BYTES:
        raise AcquisitionError(f"capture journal exceeds resource limit: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AcquisitionError(f"invalid capture journal: {path}") from error
    if _file_record(path) != before or not isinstance(value, dict):
        raise AcquisitionError("capture journal changed while reading")
    return value

SCHEMA = "alpha.proto-four-file-evidence/v1"


def is_proto_evidence(content):
    schema = content.get("schema", "") if isinstance(content, dict) else ""


    return (isinstance(schema, str) and schema.startswith("alpha.runtime-proto-")
            and schema != "alpha.runtime-proto-input/v1")


def model_digest(model):
    return hashlib.sha256(json.dumps(model, ensure_ascii=False, sort_keys=True,
                                    separators=(",", ":")).encode()).hexdigest()


def build_evidence(model, related_models=None):
    return {"schema": SCHEMA, "owner_only": True,
            "scope": "proto-models-observations-and-associated-metadata",
            "binary_payloads_embedded": False,
            "whole_metadata_dump_embedded": False,
            "model_sha256": model_digest(model),
            "related_models_sha256": model_digest(related_models or {}),
            "model": copy.deepcopy(model),
            "related_models": copy.deepcopy(related_models or {})}


def attach_evidence(classes, evidence):
    if not classes:
        raise AcquisitionError("cannot embed capture evidence without a message entry")
    result = copy.deepcopy(classes)
    if "_alpha_capture" in result[0]:
        raise AcquisitionError("capture evidence key already exists")
    result[0]["_alpha_capture"] = copy.deepcopy(evidence)
    return result


def validate_evidence(classes, model):
    evidence = classes[0].get("_alpha_capture") if classes else None
    if (not isinstance(evidence, dict) or evidence.get("schema") != SCHEMA
            or evidence.get("model") != model
            or evidence.get("model_sha256") != model_digest(model)
            or evidence.get("related_models_sha256") != model_digest(evidence.get("related_models"))):
        raise AcquisitionError("exported capture model is incomplete or changed")
    return evidence


def decode_proto_field_metadata(record):

    from alpha.p38 import RUNTIME_PROTO_FIELD_TYPE_HEADER as header, RUNTIME_PROTO_FIELD_TYPE_RECORD as row, RUNTIME_PROTO_FIELD_TYPE_MAGIC as magic, RUNTIME_PROTO_FIELD_TYPE_VERSION as version
    path = Path(record["path"])
    if path.is_symlink() or file_identity(path) != record:
        raise AcquisitionError("Proto field metadata inventory changed")
    raw = path.read_bytes()
    if len(raw) < header.size:
        raise AcquisitionError("Proto field metadata inventory is truncated")
    values = header.unpack_from(raw)
    if (values[0] != magic or values[1] != version or values[2] != header.size
            or values[3] != row.size or len(raw) != header.size + values[5] * row.size):
        raise AcquisitionError("Proto field metadata inventory format differs")
    records = [list(row.unpack_from(raw, header.size + i * row.size)) for i in range(values[5])]
    if len({entry[1] for entry in records}) != len(records):
        raise AcquisitionError("Proto field metadata repeats a field")
    if file_identity(path) != record:
        raise AcquisitionError("Proto field metadata changed while reading")
    return {"schema": "alpha.runtime-proto-field-metadata-table/v1",
            "columns": ["owner_type_index", "field_index", "field_metadata_pointer", "type_descriptor"],
            "records": records, "record_count": len(records),
            "source_header": [value.hex() if isinstance(value, bytes) else value for value in values]}


def decode_proto_observation(record):

    from alpha import p45 as enum
    from alpha import p41 as mutation
    from alpha import p42 as serializer
    from alpha import p38 as inventory
    from alpha import p43 as signed_parse
    import struct
    path = Path(record["path"])
    if path.is_symlink() or file_identity(path) != record:
        raise AcquisitionError("Proto observation changed")
    raw = path.read_bytes()
    formats = {
        enum.RUNTIME_PROTO_ENUM_MAGIC: (enum.RUNTIME_PROTO_ENUM_HEADER, enum.RUNTIME_PROTO_ENUM_RECORD,
            enum.RUNTIME_PROTO_ENUM_VERSION,
            ["field_index", "attribute_complete", "value_bits", "value_kind", "attribute_start", "attribute_count", "reserved"]),
        mutation.OUTPUT_MAGIC: (mutation.OUTPUT_HEADER, mutation.OUTPUT_RECORD, mutation.OUTPUT_VERSION,
            ["message_index", "type_index", "field_index", "number", "wire", "type_enum", "flags", "reserved",
             "before_root", "after_root", "before_class", "after_class", "before_storage_hash", "after_storage_hash",
             "before_reference_hash", "after_reference_hash"]),
        serializer.MAGIC: (serializer.HEADER, serializer.RECORD, serializer.VERSION,
            ["field_index", "type_enum", "number", "wire", "failure", "signed_encoding_code", "serialized_size", "signed_positive_wire_value", "signed_negative_wire_value"]),
        signed_parse.MAGIC: (signed_parse.HEADER, signed_parse.RECORD, signed_parse.VERSION,
            ["row_index", "field_index", "role_kind", "failure_kind", "positive_observed", "negative_observed", "positive_input_hash", "negative_input_hash"]),
        b"ALPHAPS2": (serializer.HEADER, struct.Struct("<IIIIIIQ"), 2,
            ["field_index", "type_enum", "number", "wire", "failure", "signed_encoding_code", "serialized_size"]),
        b"ALPHAPS1": (serializer.HEADER, struct.Struct("<IIIIIIQ"), 1,
            ["field_index", "type_enum", "number", "wire", "failure", "reserved", "serialized_size"]),
    }
    if raw[:8] == inventory.RUNTIME_PROTO_FIELD_TYPE_MAGIC:
        return decode_proto_field_metadata(record)
    if raw[:8] not in formats:
        raise AcquisitionError(f"unclassified Proto binary evidence: {path.name}")
    header, row, version, columns = formats[raw[:8]]
    if len(raw) < header.size:
        raise AcquisitionError("Proto observation header is truncated")
    values = header.unpack_from(raw)
    enum_observation = raw[:8] == enum.RUNTIME_PROTO_ENUM_MAGIC
    count = values[4] if enum_observation else values[5]
    trailer_bytes = int(values[6]) * 4 if enum_observation else 0
    if (values[1] != version or values[2] != header.size or values[3] != row.size
            or len(raw) != header.size + count * row.size + trailer_bytes):
        raise AcquisitionError("Proto observation envelope differs")
    records = [list(row.unpack_from(raw, header.size + i * row.size)) for i in range(count)]
    if file_identity(path) != record:
        raise AcquisitionError("Proto observation changed while reading")
    result = {"schema": "alpha.runtime-proto-structured-observation/v1", "columns": columns,
              "records": records, "record_count": len(records),
              "source_header": [v.hex() if isinstance(v, bytes) else v for v in values]}
    if enum_observation:
        trailer = header.size + count * row.size
        result["custom_attribute_type_indexes_owner_only"] = (
            list(struct.unpack_from(f"<{values[6]}I", raw, trailer))
            if values[6]
            else []
        )
    return result


def collect_direct_json_evidence(model_path, model):

    result = {}
    for name, values in model.get("inputs", {}).items():
        if name in {"runtime_materializer_model", "native_output_receipt", "snapshot"}:
            continue
        records = values if isinstance(values, list) else [values]
        for index, record in enumerate(records):
            if not isinstance(record, dict) or not isinstance(record.get("path"), str):
                continue
            path = Path(record["path"])
            if path.suffix.lower() != ".json":
                continue
            if path.is_symlink() or file_identity(path) != record:
                raise AcquisitionError(f"capture JSON evidence changed: {name}")
            content = read_private_model(path)
            if file_identity(path) != record:
                raise AcquisitionError(f"capture JSON evidence changed while reading: {name}")
            if not is_proto_evidence(content):
                continue
            result[f"{name}[{index}]"] = {"identity": record, "content": content}


    root = model_path.parent.parent
    journal_path = root / "session.private.json"
    if model_path.parent.name.startswith("proto-") and journal_path.is_file():
        from alpha.p13 import _safe_path
        journal = _read_capture_journal(journal_path)
        stages = journal.get("stages", {})
        source_stage = model_path.parent.name
        if source_stage not in stages:
            raise AcquisitionError("source Proto model stage is absent from journal")
        ancestors: set[str] = set()
        pending = [source_stage]
        while pending:
            stage = pending.pop()
            if stage in ancestors:
                continue
            entry = stages.get(stage)
            if not isinstance(entry, dict):
                raise AcquisitionError("Proto evidence dependency stage is absent")
            dependencies = entry.get("dependencies")
            if not isinstance(dependencies, list) or any(
                not isinstance(dependency, str) or dependency not in stages
                for dependency in dependencies
            ):
                raise AcquisitionError("Proto evidence dependency graph is invalid")
            ancestors.add(stage)
            pending.extend(dependencies)
        coverage = {}
        for stage in sorted(ancestors):
            entry = stages[stage]
            if not stage.startswith("proto-") or stage == "proto-input":
                continue
            if entry.get("status") != "complete":
                raise AcquisitionError("Proto evidence ancestor stage is incomplete")
            for relative, sealed in entry.get("artifacts", {}).items():
                path = root / stage / relative
                path = _safe_path(path)
                if not path.is_relative_to(root.resolve()):
                    raise AcquisitionError("capture JSON evidence escapes acquisition root")
                expected = {"path": str(path), **sealed}
                if file_identity(path) != expected:
                    raise AcquisitionError("sealed Proto evidence changed")
                key = f"stage:{stage}/{relative}"
                if any(
                    part.startswith("build-runtime-proto-")
                    for part in Path(relative).parts[:-1]
                ):
                    coverage[key] = {"identity": expected, "disposition": "excluded",
                                     "reason": "collector implementation/build product, not acquired data"}
                    continue
                if path.suffix.lower() == ".json":
                    content = read_private_model(path)
                    if not is_proto_evidence(content):
                        raise AcquisitionError(f"unclassified sealed Proto JSON: {relative}")
                elif path.suffix.lower() == ".bin":
                    content = decode_proto_observation(expected)
                elif path.suffix.lower() in {".log", ".txt"}:
                    content = {"schema": "alpha.runtime-proto-diagnostic-text/v1",
                               "text": path.read_text(encoding="utf-8", errors="strict")}
                else:
                    raise AcquisitionError(f"unclassified sealed Proto evidence: {relative}")
                if file_identity(path) != expected:
                    raise AcquisitionError("sealed Proto evidence changed while reading")
                result[key] = {"identity": expected, "content": content}
                coverage[key] = {"identity": expected, "disposition": "embedded", "evidence_key": key}
        result["artifact-coverage"] = {"content": {
            "schema": "alpha.runtime-proto-artifact-coverage/v1", "artifacts": coverage,
            "source_stage": source_stage,
            "dependency_ancestor_stages": sorted(ancestors),
            "downstream_stage_count": len(set(stages) - ancestors),
            "excluded_scope": [
                "raw process memory", "whole-game metadata inputs",
                "stages outside the source model dependency ancestry",
            ],
            "unsealed_ancestor_stages": {}}}
    inventories = {}
    for entry in result.values():
        content = entry["content"]
        if content.get("schema") == "alpha.runtime-proto-field-type-inventory/v1":
            record = content.get("inventory")
            if not isinstance(record, dict):
                raise AcquisitionError("Proto field metadata inventory identity is absent")
            inventories[record["sha256"]] = record
    for digest, record in inventories.items():
        result[f"structured-field-metadata:{digest}"] = {
            "identity": record, "content": decode_proto_field_metadata(record)}
    return result


import json
import os
import re
import tempfile
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity, read_json, read_private_model


RUNTIME_PROTO_OUTPUT_SCHEMA = "alpha.runtime-proto-output/v4"
DISCORD_URL = "https://discord.gg/VewSHpM2xM"
_CLIENT_VERSION = re.compile(r"^[0-9]+(?:\.[0-9]+){2,3}$")
_IDENTIFIER = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_URL = re.compile(r"https?://", re.IGNORECASE)
_SCALARS = frozenset(
    {
        "double",
        "float",
        "int32",
        "int64",
        "uint32",
        "uint64",
        "sint32",
        "sint64",
        "fixed32",
        "fixed64",
        "sfixed32",
        "sfixed64",
        "bool",
        "string",
        "bytes",
    }
)


def _version_label(version: Any) -> str:
    if not isinstance(version, str) or not _CLIENT_VERSION.fullmatch(version):
        raise AcquisitionError("runtime proto client version is invalid")
    return "OSCB" + version


def dump_artifact_context(target: Mapping[str, Any]) -> dict[str, str]:
    if not isinstance(target, Mapping):
        raise AcquisitionError("runtime proto target is absent")
    version = target.get("client_version")
    build = target.get("client_build")
    executable = target.get("executable_sha256")
    label = _version_label(version)
    if (
        not isinstance(build, str)
        or not (build == version or build.startswith(version + "_"))
        or not isinstance(executable, str)
        or len(executable) != 64
        or any(character not in "0123456789abcdef" for character in executable)
    ):
        raise AcquisitionError("runtime proto target version binding is invalid")
    banner = f"// Dumped by sena with alpha ver{label}"
    discord_line = f"// Discord :  {DISCORD_URL}"
    return {
        "producer": "sena with alpha",
        "client_version": version,
        "client_build": build,
        "version_label": label,
        "banner": banner,
        "discord": DISCORD_URL,
        "discord_line": discord_line,
        "executable_sha256": executable,
    }


def proto_artifact_names(target: Mapping[str, Any]) -> dict[str, str]:
    label = dump_artifact_context(target)["version_label"]
    return {
        "proto": f"Genshin_{label}.proto",
        "sorted_proto": f"Genshin_sorted_{label}.proto",
        "class_list": f"classList_{label}.json",
        "packet_ids": f"packetIds_{label}.json",
        "enum_inventory": f"unreferenced-enums_{label}.json",
        "enum_proto": f"Genshin_enums_{label}.proto",
        "nameproto": f"nameproto_{label}",
        "nameeproto": f"nameeproto_{label}",
        "semantic_names": f"semantic-name-manifest_{label}.json",
        "field_encrypt": f"field-encrypt_{label}.json",
        "receipt": f"runtime-proto-output-receipt_{label}.json",
    }


def _identifier(value: Any, *, label: str) -> str:
    if not isinstance(value, str) or not _IDENTIFIER.fullmatch(value):
        raise AcquisitionError(f"runtime proto {label} is invalid")
    return value


def _field_number(value: Any) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or not 0 < value <= 0x1FFFFFFF:
        raise AcquisitionError("runtime proto field number is invalid")
    if 19000 <= value <= 19999:
        raise AcquisitionError("runtime proto field number is reserved")
    return value


def _rva(value: Any, *, label: str) -> int | None:
    if value is None:
        return None
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise AcquisitionError(f"runtime proto {label} RVA is invalid")
    return value


def _type_name(value: Any, *, label: str) -> str:
    name = _identifier(value, label=label)
    return name


def _declaring_path(value: Any) -> str | None:

    if value is None:
        return None
    if not isinstance(value, str) or not value:
        raise AcquisitionError("runtime proto declaring path is invalid")
    if any(not _IDENTIFIER.fullmatch(part) for part in value.split(".")):
        raise AcquisitionError("runtime proto declaring path is invalid")
    return value


def _normal_field(value: Any) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise AcquisitionError("runtime proto field record is invalid")
    name = _identifier(value.get("name"), label="field name")
    number = _field_number(value.get("number"))
    offset = value.get("offset")
    if not isinstance(offset, int) or isinstance(offset, bool) or offset < 0:
        raise AcquisitionError("runtime proto field offset is invalid")
    cardinality = value.get("cardinality", "singular")
    if cardinality == "map":
        if "packed" in value:
            raise AcquisitionError("packed option is invalid for maps")
        key_type = _type_name(value.get("key_type"), label="map key type")
        if key_type not in _SCALARS - {"double", "float", "bytes"}:
            raise AcquisitionError("runtime proto map key type is invalid")
        value_type = _type_name(value.get("value_type"), label="map value type")
        return {
            "name": name,
            "number": number,
            "offset": offset,
            "cardinality": "map",
            "key_type": key_type,
            "value_type": value_type,
        }
    if cardinality not in ("singular", "repeated"):
        raise AcquisitionError("runtime proto field cardinality is invalid")
    field_type = _type_name(value.get("type"), label="field type")
    result = {
        "name": name,
        "number": number,
        "offset": offset,
        "cardinality": cardinality,
        "type": field_type,
    }
    if value.get("optional") is True:
        if cardinality != "singular":
            raise AcquisitionError("runtime proto optional field is invalid")
        result["optional"] = True
    if "packed" in value:
        if type(value["packed"]) is not bool or cardinality != "repeated" or field_type in {"string", "bytes"}:
            raise AcquisitionError("invalid repeated packed option")
        result["packed"] = value["packed"]
    return result


def _oneof(value: Any) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise AcquisitionError("runtime proto oneof record is invalid")
    name = _identifier(value.get("name"), label="oneof name")
    cases = value.get("cases")
    if not isinstance(cases, Sequence) or isinstance(cases, (str, bytes)) or not cases:
        raise AcquisitionError("runtime proto oneof cases are invalid")
    normalized: list[dict[str, Any]] = []
    for case in cases:
        if not isinstance(case, Mapping):
            raise AcquisitionError("runtime proto oneof case is invalid")
        normalized.append(
            {
                "name": _identifier(case.get("name"), label="oneof case name"),
                "number": _field_number(case.get("number")),
                "type": _type_name(case.get("type"), label="oneof case type"),
            }
        )
    return {"name": name, "cases": normalized}


def _message(value: Any) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise AcquisitionError("runtime proto message record is invalid")
    fields = value.get("fields", [])
    oneofs = value.get("oneofs", [])
    if (
        not isinstance(fields, Sequence)
        or isinstance(fields, (str, bytes))
        or not isinstance(oneofs, Sequence)
        or isinstance(oneofs, (str, bytes))
    ):
        raise AcquisitionError("runtime proto message members are invalid")
    normalized_fields = [_normal_field(field) for field in fields]
    normalized_oneofs = [_oneof(oneof) for oneof in oneofs]
    all_names = [field["name"] for field in normalized_fields]
    all_numbers = [field["number"] for field in normalized_fields]
    for oneof in normalized_oneofs:
        all_names.extend(case["name"] for case in oneof["cases"])
        all_numbers.extend(case["number"] for case in oneof["cases"])
    if len(all_names) != len(set(all_names)):
        raise AcquisitionError("runtime proto message has duplicate field names")
    if len(all_numbers) != len(set(all_numbers)):
        raise AcquisitionError("runtime proto message has duplicate field numbers")
    cmd_id = value.get("cmd_id")
    if cmd_id is not None and (
        not isinstance(cmd_id, int)
        or isinstance(cmd_id, bool)
        or not 0 <= cmd_id <= 0xFFFF
    ):
        raise AcquisitionError("runtime proto command id is invalid")
    return {
        "kind": "message",
        "name": _identifier(value.get("name"), label="message name"),
        "cmd_id": cmd_id,
        "merge_from_rva": _rva(value.get("merge_from_rva"), label="MergeFrom"),
        "write_to_rva": _rva(value.get("write_to_rva"), label="WriteTo"),
        "declaring_path": _declaring_path(value.get("declaring_path")),
        "fields": normalized_fields,
        "oneofs": normalized_oneofs,
    }


def _enum(value: Any) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise AcquisitionError("runtime proto enum record is invalid")
    values = value.get("values")
    if not isinstance(values, Sequence) or isinstance(values, (str, bytes)) or not values:
        raise AcquisitionError("runtime proto enum values are invalid")
    normalized: list[dict[str, Any]] = []
    for item in values:
        if (
            not isinstance(item, Mapping)
            or not isinstance(item.get("number"), int)
            or isinstance(item.get("number"), bool)
            or not -(1 << 31) <= item["number"] < (1 << 31)
        ):
            raise AcquisitionError("runtime proto enum value is invalid")
        normalized.append(
            {
                "name": _identifier(item.get("name"), label="enum value name"),
                "number": item["number"],
                **({"original_name": _identifier(item["original_name"], label="original enum value name")}
                   if "original_name" in item else {}),
            }
        )
    names = [item["name"] for item in normalized]
    if len(names) != len(set(names)):
        raise AcquisitionError("runtime proto enum has duplicate value names")
    if normalized[0]["number"] != 0:
        raise AcquisitionError("runtime proto3 enum must begin with zero")
    return {
        "kind": "enum",
        "name": _identifier(value.get("name"), label="enum name"),
        "declaring_path": _declaring_path(value.get("declaring_path")),
        "values": normalized,
    }


def normalize_proto_items(items: Iterable[Mapping[str, Any]]) -> list[dict[str, Any]]:
    normalized: list[dict[str, Any]] = []
    names: set[str] = set()
    for item in items:
        if not isinstance(item, Mapping):
            raise AcquisitionError("runtime proto top-level item is invalid")
        kind = item.get("kind")
        value = _message(item) if kind == "message" else _enum(item) if kind == "enum" else None
        if value is None:
            raise AcquisitionError("runtime proto top-level kind is invalid")
        if value["name"] in names:
            raise AcquisitionError("runtime proto has duplicate top-level names")
        names.add(value["name"])
        normalized.append(value)
    if not normalized or not any(item["kind"] == "message" for item in normalized):
        raise AcquisitionError("runtime proto output model is empty")


    from collections import Counter
    value_names = Counter(value["name"] for item in normalized if item["kind"] == "enum" for value in item["values"])
    reserved = names | set(value_names)
    for item in sorted((x for x in normalized if x["kind"] == "enum"),key=lambda x:x["name"]):
        for value in sorted(item["values"],key=lambda x:x["name"]):
            original = value["name"]
            if value_names[original] == 1 and original not in names:
                continue
            candidate = item["name"] + "_" + original
            suffix = 1
            while candidate in reserved:
                candidate = item["name"] + "_" + original + "_" + str(suffix)
                suffix += 1
            reserved.add(candidate)
            value["original_name"] = original
            value["name"] = candidate
    for item in normalized:
        if item["kind"] == "enum":
            continue
        fields = list(item["fields"])
        for oneof in item["oneofs"]:
            fields.extend(oneof["cases"])
        for field in fields:
            reference = field.get("value_type") if field.get("cardinality") == "map" else field["type"]
            if reference not in _SCALARS and reference not in names:
                raise AcquisitionError(f"runtime proto type reference is unresolved: {reference}")
    return normalized


def _format_rva(value: int | None) -> str:
    return "-" if value is None else f"0x{value:X}"


PROTO_INDENT = "    "


def _message_relationships(
    normalized: Sequence[Mapping[str, Any]],
) -> tuple[dict[str, str | None], dict[str, list[Mapping[str, Any]]], dict[str, str]]:

    messages = [item for item in normalized if item["kind"] == "message"]
    names = {str(item["name"]) for item in messages}
    by_name = {str(item["name"]): item for item in messages}
    owner_of: dict[str, str | None] = {}
    for item in messages:
        name = str(item["name"])
        path = str(item.get("declaring_path") or name)
        parts = path.split(".")
        owner: str | None = None
        for cut in range(len(parts) - 1, 0, -1):
            candidate = parts[cut - 1]
            if candidate == name or candidate not in names:
                continue
            candidate_path = str(by_name[candidate].get("declaring_path") or candidate)
            if path.startswith(candidate_path + "."):
                owner = candidate
                break
        owner_of[name] = owner
    for item in normalized:
        if item["kind"] != "enum":
            continue
        name = str(item["name"])
        path = str(item.get("declaring_path") or name)
        owner = None
        parts = path.split(".")
        for cut in range(len(parts) - 1, 0, -1):
            candidate = parts[cut - 1]
            if candidate not in names:
                continue
            candidate_path = str(
                by_name[candidate].get("declaring_path") or candidate
            )
            if path.startswith(candidate_path + "."):
                owner = candidate
                break
        owner_of[name] = owner
    for item in messages:
        seen: set[str] = set()
        cursor: str | None = str(item["name"])
        while cursor is not None:
            if cursor in seen:
                raise AcquisitionError("runtime proto declaring path is cyclic")
            seen.add(cursor)
            cursor = owner_of[cursor]
    emitted: dict[str, str] = {}
    for item in messages:
        name = str(item["name"])
        chain: list[str] = []
        cursor: str | None = name
        while cursor is not None and cursor not in emitted:
            chain.append(cursor)
            cursor = owner_of[cursor]
        prefix = emitted[cursor] if cursor is not None else ""
        for step in reversed(chain):
            prefix = step if not prefix else prefix + "." + step
            emitted[step] = prefix
    for item in normalized:
        if item["kind"] != "enum":
            continue
        name = str(item["name"])
        owner = owner_of[name]
        emitted[name] = name if owner is None else emitted[owner] + "." + name
    children: dict[str, list[Mapping[str, Any]]] = {name: [] for name in names}
    for item in normalized:
        owner = owner_of[str(item["name"])]
        if owner is not None:
            children[owner].append(item)
    for bucket in children.values():
        bucket.sort(key=lambda item: (str(item["kind"]), str(item["name"])))
    return owner_of, children, emitted


def _qualified_type(
    name: str, *, scope_path: str, emitted: Mapping[str, str]
) -> str:
    if name not in emitted:
        return name
    target = emitted[name]
    if target.startswith(scope_path + "."):
        return target[len(scope_path) + 1:]
    return target


def _format_field(
    field: Mapping[str, Any],
    *,
    indent: str = "  ",
    scope_path: str = "",
    emitted: Mapping[str, str] | None = None,
) -> str:
    emitted = emitted or {}
    if field.get("cardinality") == "map":
        value_type = _qualified_type(str(field["value_type"]), scope_path=scope_path, emitted=emitted)
        rendered_type = f"map<{field['key_type']}, {value_type}>"
    else:
        prefix = (
            "optional " if field.get("optional")
            else "repeated " if field.get("cardinality") == "repeated"
            else ""
        )
        rendered_type = prefix + _qualified_type(str(field["type"]), scope_path=scope_path, emitted=emitted)
    option = (" [packed=" + str(field["packed"]).lower() + "]") if "packed" in field else ""
    return f"{indent}{rendered_type} {field['name']} = {field['number']}{option};"


def _render_enum(item: Mapping[str, Any], *, indent: str) -> list[str]:
    lines = [f"{indent}enum {item['name']} {{"]
    values = [value["number"] for value in item["values"]]
    if len(values) != len(set(values)):
        lines.append(f"{indent}{PROTO_INDENT}option allow_alias = true;")
    lines.extend(
        f"{indent}{PROTO_INDENT}{value['name']} = {value['number']};"
        for value in item["values"]
    )
    lines.append(f"{indent}}}")
    return lines


def _render_message(
    item: Mapping[str, Any],
    *,
    indent: str,
    children: Mapping[str, list[Mapping[str, Any]]],
    emitted: Mapping[str, str],
    sort_fields: bool,
) -> list[str]:
    name = str(item["name"])
    scope_path = emitted[name]
    body = indent + PROTO_INDENT
    cmd_id = item.get("cmd_id")
    lines = [
        f"{indent}// CmdId: "
        + (str(cmd_id) if isinstance(cmd_id, int) else "-")
        + f" | MergeFrom: {_format_rva(item.get('merge_from_rva'))}"
        + f" | WriteTo: {_format_rva(item.get('write_to_rva'))}",
        f"{indent}message {name} {{",
    ]
    nested = children.get(name, [])
    if nested:
        for child in nested:
            if child["kind"] == "message":
                lines.extend(
                    _render_message(
                        child,
                        indent=body,
                        children=children,
                        emitted=emitted,
                        sort_fields=sort_fields,
                    )
                )
            else:
                lines.extend(_render_enum(child, indent=body))
        lines.append("")
    fields = list(item["fields"])
    if sort_fields:
        fields.sort(key=lambda field: field["number"])
    oneofs = list(item["oneofs"])
    if fields or oneofs:
        lines.extend(
            _format_field(
                field, indent=body, scope_path=scope_path, emitted=emitted
            )
            for field in fields
        )
        for oneof in oneofs:
            lines.append(f"{body}oneof {oneof['name']} {{")
            lines.extend(
                _format_field(
                    case,
                    indent=body + PROTO_INDENT,
                    scope_path=scope_path,
                    emitted=emitted,
                )
                for case in oneof["cases"]
            )
            lines.append(f"{body}}}")
    lines.append(f"{indent}}}")
    return lines


def render_proto(
    items: Iterable[Mapping[str, Any]],
    *,
    client_version: str,
    sort_fields: bool = False,
) -> str:
    normalized = normalize_proto_items(items)
    _owner_of, children, emitted = _message_relationships(normalized)
    lines = [
        f"// Dumped by sena with alpha ver{_version_label(client_version)}",
        f"// Discord :  {DISCORD_URL}",
        "// Runtime-derived wire schema; original source syntax/options are not reconstructed.",
        'syntax = "proto3";',
        "",
    ]
    for item in normalized:
        if _owner_of[str(item["name"])] is not None:
            continue
        if item["kind"] == "message":
            lines.extend(
                _render_message(
                    item,
                    indent="",
                    children=children,
                    emitted=emitted,
                    sort_fields=sort_fields,
                )
            )
        else:
            lines.extend(_render_enum(item, indent=""))
        lines.append("")
    return "\n".join(lines)


def build_class_list(items: Iterable[Mapping[str, Any]]) -> list[dict[str, Any]]:
    normalized = normalize_proto_items(items)
    output: list[dict[str, Any]] = []
    for item in normalized:
        if item["kind"] != "message":
            continue
        row: dict[str, Any] = {"name": item["name"]}
        if item["cmd_id"] is not None:
            row["cmd_id"] = item["cmd_id"]


        row["fields"] = [dict(field) for field in item["fields"]]
        row["oneofs"] = [
            {
                "name": oneof["name"],
                "cases": [dict(case) for case in oneof["cases"]],
            }
            for oneof in item["oneofs"]
        ]
        output.append(row)
    return output


def build_packet_ids(
    items: Iterable[Mapping[str, Any]],
) -> tuple[dict[str, int], list[dict[str, Any]]]:
    normalized = normalize_proto_items(items)
    output: dict[str, int] = {}
    owners_by_id: dict[int, list[str]] = {}
    for item in normalized:
        if item["kind"] != "message" or item["cmd_id"] is None:
            continue
        cmd_id = item["cmd_id"]
        previous = owners_by_id.setdefault(cmd_id, [])
        previous.append(item["name"])
        output[item["name"]] = cmd_id
    duplicates = [
        {
            "cmd_id": cmd_id,
            "names": names,
            "all_names_retained": True,
        }
        for cmd_id, names in owners_by_id.items()
        if len(names) > 1
    ]
    return output, duplicates


def _json_text(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, indent=2) + "\n"


def validate_public_proto_text(value: str, target: Mapping[str, Any]) -> None:
    context = dump_artifact_context(target)
    nonempty = [line.strip() for line in value.splitlines() if line.strip()]
    if nonempty[:2] != [context["banner"], context["discord_line"]]:
        raise AcquisitionError("runtime proto public banner is invalid")
    url_lines = [line.strip() for line in value.splitlines() if _URL.search(line)]
    if url_lines != [context["discord_line"]]:
        raise AcquisitionError("runtime proto public output link domain differs")


def _atomic_write_text(path: Path, value: str) -> None:
    path = path.expanduser().resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as output:
            output.write(value)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary_path, path)
    finally:
        temporary_path.unlink(missing_ok=True)


def write_runtime_proto_outputs(
    *,
    items: Iterable[Mapping[str, Any]],
    output_dir: Path,
    target: Mapping[str, Any],
    capture_evidence=None,
) -> dict[str, Any]:
    normalized = normalize_proto_items(items)
    context = dump_artifact_context(target)
    names = proto_artifact_names(target)
    proto = render_proto(normalized, client_version=context["client_version"])
    sorted_proto = render_proto(
        normalized,
        client_version=context["client_version"],
        sort_fields=True,
    )
    validate_public_proto_text(proto, target)
    validate_public_proto_text(sorted_proto, target)
    classes = build_class_list(normalized)
    if capture_evidence is not None:
        from alpha.p02 import attach_evidence
        classes = attach_evidence(classes, capture_evidence)
    packets, duplicates = build_packet_ids(normalized)
    root = output_dir.expanduser().resolve()
    metadata = {
        key: context[key]
        for key in (
            "producer",
            "client_version",
            "client_build",
            "version_label",
            "banner",
            "discord",
            "executable_sha256",
        )
    }
    files = {
        names["proto"]: proto,
        names["sorted_proto"]: sorted_proto,
        names["class_list"]: _json_text(
            {"dump_metadata": metadata, "classes": classes}
        ),
        names["packet_ids"]: _json_text(
            {"dump_metadata": metadata, "packet_ids": packets}
        ),
    }
    for name, value in files.items():
        _atomic_write_text(root / name, value)
    identities = {name: file_identity(root / name) for name in files}
    message_count = sum(item["kind"] == "message" for item in normalized)
    enum_count = sum(item["kind"] == "enum" for item in normalized)
    field_count = sum(
        len(item["fields"])
        + sum(len(oneof["cases"]) for oneof in item["oneofs"])
        for item in normalized
        if item["kind"] == "message"
    )
    return {
        "schema": RUNTIME_PROTO_OUTPUT_SCHEMA,
        "status": "written",
        "output_dir": str(root),
        "dump_metadata": metadata,
        "artifact_names": names,
        "files": identities,
        "counts": {
            "message_count": message_count,
            "enum_count": enum_count,
            "proto_field_count": field_count,
            "class_field_count": sum(len(item["fields"]) for item in classes),
            "class_oneof_case_count": sum(
                len(oneof["cases"])
                for item in classes
                for oneof in item["oneofs"]
            ),
            "class_with_cmd_id_count": sum("cmd_id" in item for item in classes),
            "packet_id_count": len(packets),
            "duplicate_cmd_id_count": len(duplicates),
        },
        "duplicate_cmd_ids_owner_only": duplicates,
        "policy": {
            "metadata_order_preserved": True,
            "sorted_output_sorts_fields_only": True,
            "duplicate_cmd_id_all_names_retained": True,
            "reference_generation_used_as_seed": False,
            "external_runtime_component_used": False,
            "required_banner": context["banner"],
            "required_discord_line": context["discord_line"],
        },
    }


def _validate_embedded_dump_metadata(
    embedded: Any, target: Mapping[str, Any]
) -> None:
    expected = dump_artifact_context(target)
    required = {
        key: expected[key]
        for key in (
            "producer",
            "client_version",
            "client_build",
            "version_label",
            "banner",
            "discord",
            "executable_sha256",
        )
    }
    if embedded != required:
        raise AcquisitionError("runtime proto embedded dump metadata differs")


def read_proto_class_list(
    path: Path, *, target: Mapping[str, Any] | None = None
):


    value = read_json(path, maximum_bytes=None)
    if not isinstance(value, Mapping) or set(value) != {
        "dump_metadata",
        "classes",
    }:
        raise AcquisitionError("runtime proto classList envelope is invalid")
    if target is not None:
        _validate_embedded_dump_metadata(value["dump_metadata"], target)
    if not isinstance(value["classes"], list):
        raise AcquisitionError("runtime proto classList data is invalid")
    return value["classes"]


def read_proto_packet_ids(
    path: Path, *, target: Mapping[str, Any] | None = None
) -> dict[str, int]:
    value = read_json(path, maximum_bytes=512 * 1024 * 1024)
    if not isinstance(value, Mapping) or set(value) != {
        "dump_metadata",
        "packet_ids",
    }:
        raise AcquisitionError("runtime proto packetIds envelope is invalid")
    if target is not None:
        _validate_embedded_dump_metadata(value["dump_metadata"], target)
    packet_ids = value["packet_ids"]
    if not isinstance(packet_ids, dict) or any(
        not isinstance(name, str)
        or type(number) is not int
        or not 0 <= number <= 0xFFFFFFFF
        for name, number in packet_ids.items()
    ):
        raise AcquisitionError("runtime proto packetIds data is invalid")
    return packet_ids


def validate_runtime_proto_static_model_for_publication(
    model: Mapping[str, Any],
    *, allow_partial_wire_contract: bool = False,
) -> dict[str, int]:
    from alpha.p42 import RUNTIME_PROTO_STATIC_MODEL_SCHEMA

    if not isinstance(model, Mapping):
        raise AcquisitionError("runtime proto static model is not an object")
    checks = model.get("checks")
    messages = model.get("messages_owner_only")
    enums = model.get("enums_owner_only")
    unreferenced = model.get("unreferenced_enums_owner_only")
    unresolved = model.get("unresolved_owner_only")
    counts = model.get("counts")
    if (
        model.get("schema") != RUNTIME_PROTO_STATIC_MODEL_SCHEMA
        or model.get("status") != "complete"
        or not isinstance(checks, Mapping)
        or not checks
        or any(value is not True for value in checks.values())
        or not isinstance(messages, list)
        or not isinstance(enums, list)
        or not isinstance(unreferenced, list)
        or unresolved != []
        or not isinstance(counts, Mapping)
        or model.get("full_semantic_verification_complete") is not True
        or model.get("message_domain_audit_owner_only", {}).get("complete")
        is not True
        or model.get("signed_encoding_coverage_owner_only", {}).get("complete")
        is not True
    ):
        raise AcquisitionError("runtime proto static model is not complete")
    dump_artifact_context(model.get("target", {}))


    normalized = normalize_proto_items([*messages, *enums])
    normalized_messages = [item for item in normalized if item["kind"] == "message"]
    normalized_enums = [item for item in normalized if item["kind"] == "enum"]
    raw_message_type_indexes = [
        item.get("type_index_owner_only")
        for item in messages
        if isinstance(item, Mapping)
    ]
    if (
        len(raw_message_type_indexes) != len(messages)
        or any(type(index) is not int or index < 0 for index in raw_message_type_indexes)
        or len(set(raw_message_type_indexes)) != len(raw_message_type_indexes)
    ):
        raise AcquisitionError("runtime proto message type index domain is invalid")
    normal_field_count = sum(len(item["fields"]) for item in normalized_messages)
    oneof_case_count = sum(
        len(oneof["cases"])
        for item in normalized_messages
        for oneof in item["oneofs"]
    )
    proto_field_count = normal_field_count + oneof_case_count
    optional_field_count = sum(
        field.get("optional") is True
        for item in normalized_messages
        for field in item["fields"]
    )
    expected_counts = {
        "message_count": len(normalized_messages),
        "enum_count": len(normalized_enums),
        "normal_field_count": normal_field_count,
        "oneof_count": sum(len(item["oneofs"]) for item in normalized_messages),
        "proto_field_count": proto_field_count,
        "expected_candidate_tag_count": proto_field_count,
        "optional_field_count": optional_field_count,
        "unresolved_count": 0,
        "unreferenced_enum_count": len(unreferenced),
        "uncaptured_runtime_enum_literal_count": 0,
        "incomplete_enum_attribute_capture_count": 0,
    }
    for name, expected in expected_counts.items():
        if (
            type(counts.get(name)) is not int
            or counts.get(name) < 0
            or counts.get(name) != expected
        ):
            raise AcquisitionError(
                f"runtime proto static model count differs: {name}"
            )

    runtime_enum_count = counts.get("runtime_enum_count")
    if (
        type(runtime_enum_count) is not int
        or runtime_enum_count != len(normalized_enums) + len(unreferenced)
    ):
        raise AcquisitionError("runtime proto enum type domain does not close")
    captured_enum_literals = counts.get("captured_runtime_enum_literal_count")
    runtime_enum_literals = counts.get("runtime_enum_literal_count")
    if (
        type(captured_enum_literals) is not int
        or captured_enum_literals < 0
        or type(runtime_enum_literals) is not int
        or runtime_enum_literals < 0
        or captured_enum_literals != runtime_enum_literals
    ):
        raise AcquisitionError("runtime proto enum literal domain is incomplete")

    features = model.get("protobuf_feature_classification")
    presence = features.get("field_presence_counts") if isinstance(features, Mapping) else None
    repeated_encoding = (
        features.get("repeated_field_encoding_counts")
        if isinstance(features, Mapping) else None
    )
    source_only = features.get("source_only_declarations") if isinstance(features, Mapping) else None
    source_schema_fidelity = (
        features.get("source_schema_fidelity")
        if isinstance(features, Mapping) else None
    )
    group_wire_audit = (
        features.get("group_wire_audit")
        if isinstance(features, Mapping) else None
    )
    parserless_type_indexes = (
        group_wire_audit.get("parserless_message_type_indexes_owner_only")
        if isinstance(group_wire_audit, Mapping) else None
    )
    parserless_model_type_indexes = sorted(
        int(item["type_index_owner_only"])
        for item in messages
        if isinstance(item, Mapping)
        and type(item.get("type_index_owner_only")) is int
        and item.get("merge_from_rva") is None
    )
    serializable_message_count = 0
    parserless_field_message_indexes: list[int] = []
    expected_field_numbers_by_type: dict[int, list[int]] = {}
    expected_field_accesses_by_type: dict[int, dict[int, set[int]]] = {}
    expected_message_names_by_type: dict[int, str] = {}
    for item in messages:
        if not isinstance(item, Mapping):
            continue
        field_count = len(item.get("fields") or []) + sum(
            len(oneof.get("cases") or [])
            for oneof in item.get("oneofs") or []
            if isinstance(oneof, Mapping)
        )
        if field_count:
            serializable_message_count += 1
            if (
                type(item.get("type_index_owner_only")) is int
                and item.get("merge_from_rva") is None
            ):
                parserless_field_message_indexes.append(
                    int(item["type_index_owner_only"])
                )
        type_index = item["type_index_owner_only"]
        field_numbers = sorted(
            [int(field["number"]) for field in item.get("fields") or []]
            + [
                int(case["number"])
                for oneof in item.get("oneofs") or []
                for case in oneof.get("cases") or []
            ]
        )
        expected_field_numbers_by_type[type_index] = field_numbers
        expected_message_names_by_type[type_index] = str(item["name"])
        expected_accesses: dict[int, set[int]] = {}
        for field in item.get("fields") or []:
            number = int(field["number"])
            field_index = field.get("field_index_owner_only")
            if type(field_index) is not int or field_index < 0:
                raise AcquisitionError(
                    "runtime proto output field has no runtime identity"
                )
            expected_accesses.setdefault(number, set()).add(field_index)
        for oneof in item.get("oneofs") or []:
            storage_index = oneof.get("storage_field_index_owner_only")
            if type(storage_index) is not int or storage_index < 0:
                raise AcquisitionError(
                    "runtime proto oneof has no runtime storage identity"
                )
            for case in oneof.get("cases") or []:
                expected_accesses.setdefault(int(case["number"]), set()).add(
                    storage_index
                )
        expected_field_accesses_by_type[type_index] = expected_accesses
    parser_tag_case_coverage = (
        group_wire_audit.get("parser_tag_case_coverage_owner_only")
        if isinstance(group_wire_audit, Mapping) else None
    )
    parser_tag_coverage_valid = isinstance(parser_tag_case_coverage, list)
    parser_tag_coverage_type_indexes: list[int] = []
    uncovered_parser_message_count = 0
    if parser_tag_coverage_valid:
        for row in parser_tag_case_coverage:
            if not isinstance(row, Mapping):
                parser_tag_coverage_valid = False
                break
            type_index = row.get("type_index_owner_only")
            output_numbers = row.get("output_field_numbers")
            parser_numbers = row.get("parser_candidate_field_numbers")
            writer_numbers = row.get("writer_tag_field_numbers")
            formatter_numbers = row.get("formatter_tag_field_numbers")
            oneof_size_numbers = row.get("bounded_oneof_size_case_numbers")
            mapped_numbers = row.get("bounded_field_access_mapped_numbers")
            legacy_mapped_numbers = row.get("parser_field_access_mapped_numbers")
            if mapped_numbers is None:
                mapped_numbers = legacy_mapped_numbers
            elif legacy_mapped_numbers is not None and legacy_mapped_numbers != mapped_numbers:
                parser_tag_coverage_valid = False
                break
            access_rows = row.get(
                "parser_field_access_indexes_by_number_owner_only"
            )
            uncovered_case_numbers = row.get("uncovered_parser_case_numbers")
            uncovered_mapping_numbers = row.get(
                "uncovered_parser_field_access_numbers"
            )
            uncovered_access_pairs = row.get(
                "uncovered_parser_field_access_pairs_owner_only"
            )
            uncovered_numbers = row.get("uncovered_output_field_numbers")

            def valid_number_list(value: Any) -> bool:
                return (
                    isinstance(value, list)
                    and all(type(number) is int and 0 < number <= 0x1FFFFFFF for number in value)
                    and value == sorted(set(value))
                )

            def valid_access_rows(value: Any) -> bool:
                if not isinstance(value, list):
                    return False
                numbers: list[int] = []
                for access_row in value:
                    if not isinstance(access_row, Mapping):
                        return False
                    number = access_row.get("field_number")
                    indexes = access_row.get("field_indexes_owner_only")
                    if (
                        type(number) is not int
                        or not 0 < number <= 0x1FFFFFFF
                        or not isinstance(indexes, list)
                        or not indexes
                        or any(type(index) is not int or index < 0 for index in indexes)
                        or indexes != sorted(set(indexes))
                    ):
                        return False
                    numbers.append(number)
                return numbers == sorted(set(numbers))

            def valid_uncovered_pairs(value: Any) -> bool:
                if not isinstance(value, list):
                    return False
                keys: list[tuple[int, tuple[int, ...]]] = []
                for pair in value:
                    if not isinstance(pair, Mapping):
                        return False
                    number = pair.get("field_number")
                    indexes = pair.get("field_indexes_owner_only")
                    if (
                        type(number) is not int
                        or not 0 < number <= 0x1FFFFFFF
                        or not isinstance(indexes, list)
                        or not indexes
                        or any(type(index) is not int or index < 0 for index in indexes)
                        or indexes != sorted(set(indexes))
                    ):
                        return False
                    keys.append((number, tuple(indexes)))
                return keys == sorted(set(keys))

            if (
                type(type_index) is not int
                or type_index < 0
                or type_index not in expected_field_numbers_by_type
                or not valid_number_list(output_numbers)
                or not valid_number_list(parser_numbers)
                or not valid_number_list(writer_numbers)
                or not valid_number_list(formatter_numbers)
                or not valid_number_list(oneof_size_numbers)
                or not valid_number_list(mapped_numbers)
                or not valid_access_rows(access_rows)
                or not valid_number_list(uncovered_case_numbers)
                or not valid_number_list(uncovered_mapping_numbers)
                or not valid_uncovered_pairs(uncovered_access_pairs)
                or not valid_number_list(uncovered_numbers)
            ):
                parser_tag_coverage_valid = False
                break
            access_indexes_by_number = {
                int(access_row["field_number"]): set(
                    int(index)
                    for index in access_row["field_indexes_owner_only"]
                )
                for access_row in access_rows
            }
            expected_accesses = expected_field_accesses_by_type[type_index]
            expected_uncovered_access_pairs = [
                {
                    "field_number": number,
                    "field_indexes_owner_only": sorted(
                        indexes - access_indexes_by_number.get(number, set())
                    ),
                }
                for number, indexes in sorted(expected_accesses.items())
                if not indexes <= access_indexes_by_number.get(number, set())
            ]
            if (
                output_numbers != expected_field_numbers_by_type[type_index]
                or row.get("message") != expected_message_names_by_type[type_index]
                or not set(parser_numbers) <= set(output_numbers)
                or not set(writer_numbers) <= set(output_numbers)
                or not set(formatter_numbers) <= set(output_numbers)
                or not set(oneof_size_numbers) <= set(output_numbers)
                or not set(mapped_numbers) <= set(output_numbers)
                or not set(access_indexes_by_number) <= set(mapped_numbers)
                or not set(access_indexes_by_number) <= set(parser_numbers)
                or uncovered_case_numbers
                != sorted(set(output_numbers) - set(parser_numbers)
                          - set(writer_numbers) - set(formatter_numbers)
                          - set(oneof_size_numbers))
                or uncovered_mapping_numbers
                != sorted(set(output_numbers) - set(mapped_numbers))
                or (not writer_numbers and not formatter_numbers
                    and not oneof_size_numbers
                    and uncovered_access_pairs != expected_uncovered_access_pairs)
                or uncovered_numbers
                != sorted(
                    set(uncovered_case_numbers)
                    | set(uncovered_mapping_numbers)
                    | {
                        int(access_row["field_number"])
                        for access_row in uncovered_access_pairs
                    }
                )
            ):
                parser_tag_coverage_valid = False
                break
            parser_tag_coverage_type_indexes.append(type_index)
            uncovered_parser_message_count += bool(uncovered_numbers)
        parser_tag_coverage_valid = (
            parser_tag_coverage_valid
            and len(parser_tag_coverage_type_indexes) == len(messages)
            and len(set(parser_tag_coverage_type_indexes)) == len(messages)
            and set(parser_tag_coverage_type_indexes)
            == set(expected_field_numbers_by_type)
        )
    runtime_semantics_outside_wire_schema = (
        features.get("runtime_semantics_outside_wire_schema")
        if isinstance(features, Mapping) else None
    )
    expected_presence: dict[str, int] = {}
    expected_repeated_encoding: dict[str, int] = {}
    message_names = {message["name"] for message in normalized_messages}
    enum_names = {enum["name"] for enum in normalized_enums}
    packable_types = {
        "double", "float", "int32", "int64", "uint32", "uint64",
        "sint32", "sint64", "fixed32", "fixed64", "sfixed32",
        "sfixed64", "bool",
    }

    def count_feature(target: dict[str, int], name: str) -> None:
        target[name] = target.get(name, 0) + 1

    for message in normalized_messages:
        for field in message["fields"]:
            cardinality = field["cardinality"]
            field_type = str(field.get("type") or "")
            if cardinality == "map":
                count_feature(expected_presence, "map_no_presence")
                count_feature(expected_repeated_encoding, "map_entry_length_prefixed")
            elif cardinality == "repeated":
                count_feature(expected_presence, "repeated_no_presence")
                count_feature(
                    expected_repeated_encoding,
                    ("packed" if field.get("packed", True) else "expanded")
                    if field_type in packable_types | enum_names
                    else "not_packable",
                )
            elif field.get("optional") is True:
                count_feature(expected_presence, "explicit_proto3_optional")
            elif field_type in message_names:
                count_feature(expected_presence, "explicit_message_presence")
            else:
                count_feature(expected_presence, "implicit_scalar_or_enum_presence")
        for oneof in message["oneofs"]:
            for _case in oneof["cases"]:
                count_feature(expected_presence, "explicit_oneof_presence")
    if (
        not isinstance(presence, Mapping)
        or any(type(value) is not int or value < 0 for value in presence.values())
        or dict(presence) != expected_presence
        or not isinstance(repeated_encoding, Mapping)
        or any(
            type(value) is not int or value < 0
            for value in repeated_encoding.values()
        )
        or dict(repeated_encoding) != expected_repeated_encoding
        or features.get("rendered_syntax") != "proto3"
        or any(
            type(features.get(name)) is not int or features.get(name) < 0
            for name in (
                "map_field_count",
                "real_oneof_count",
                "proto3_optional_count",
                "unclassified_feature_count",
                "rendered_group_or_delimited_field_count",
                "rendered_required_field_count",
            )
        )
        or features.get("map_field_count") != sum(
            field["cardinality"] == "map"
            for message in normalized_messages for field in message["fields"]
        )
        or features.get("real_oneof_count") != sum(
            len(message["oneofs"]) for message in normalized_messages
        )
        or features.get("proto3_optional_count") != optional_field_count
        or features.get("all_wire_schema_features_classified") is not True
        or features.get("unclassified_feature_count") != 0
        or features.get("rendered_group_or_delimited_field_count") != 0
        or features.get("rendered_required_field_count") != 0
        or not isinstance(source_schema_fidelity, Mapping)
        or dict(source_schema_fidelity) != {
            "claim_scope": "runtime-wire-contract",
            "original_source_equivalence": "not-established",
            "original_syntax_or_edition": "not-recoverable-from-wire-contract",
            "original_required_labels": "not-recoverable-from-wire-contract",
            "original_group_declarations": "not-claimed-from-bounded-parser-evidence",
        }
        or not isinstance(runtime_semantics_outside_wire_schema, Mapping)
        or dict(runtime_semantics_outside_wire_schema) != {
            "enum_open_or_closed": "not-reconstructed-from-wire-contract",
            "utf8_validation": "not-reconstructed-from-wire-contract",
            "json_format": "not-reconstructed-from-wire-contract",
        }
        or not isinstance(group_wire_audit, Mapping)
        or group_wire_audit.get("wire_types_checked") != [3, 4, 6, 7]
        or group_wire_audit.get("observed_group_wire_tag_count") != 0
        or type(group_wire_audit.get("observed_group_wire_tag_count")) is not int
        or group_wire_audit.get("disposition")
        != "fail-closed-if-observed-or-uncovered-serialized-message"
        or group_wire_audit.get("scope")
        != "all-output-messages-with-serialized-fields"
        or group_wire_audit.get("selected_message_count")
        != len(normalized_messages)
        or any(
            type(group_wire_audit.get(name)) is not int
            or group_wire_audit.get(name) < 0
            for name in (
                "selected_message_count",
                "selected_bounded_parser_count",
            )
        )
        or group_wire_audit.get("selected_bounded_parser_count", 0)
        > group_wire_audit.get("selected_message_count", 0)
        or not isinstance(parserless_type_indexes, list)
        or any(type(index) is not int or index < 0 for index in parserless_type_indexes)
        or parserless_type_indexes != sorted(set(parserless_type_indexes))
        or parserless_type_indexes != parserless_model_type_indexes
        or group_wire_audit.get("parserless_message_count")
        != len(parserless_type_indexes)
        or type(group_wire_audit.get("parserless_message_count")) is not int
        or group_wire_audit.get("selected_bounded_parser_count")
        + len(parserless_type_indexes)
        != group_wire_audit.get("selected_message_count")
        or group_wire_audit.get("serializable_message_count")
        != serializable_message_count
        or type(group_wire_audit.get("serializable_message_count")) is not int
        or not parser_tag_coverage_valid
        or group_wire_audit.get("uncovered_serializable_message_count")
        != uncovered_parser_message_count
        or type(group_wire_audit.get("uncovered_serializable_message_count")) is not int
        or uncovered_parser_message_count != 0
        or not allow_partial_wire_contract and parserless_field_message_indexes
        or group_wire_audit.get("bounded_parser_coverage")
        != "all-field-bearing-message-types"
        or not isinstance(source_only, Mapping)
        or not source_only
        or set(source_only) != {
            "reserved_names_and_ranges",
            "extension_ranges",
            "services_and_rpc_methods",
            "imports",
            "source_code_info",
            "comments",
            "custom_json_names",
            "custom_source_options",
            "custom_default_values",
            "legacy_required_labels",
            "original_proto_syntax_or_edition",
            "original_group_declarations",
            "explicit_optional_keyword_on_message_fields",
        }
        or any(
            value != "not_in_recoverable_wire_contract"
            for value in source_only.values()
        )
    ):
        raise AcquisitionError("protobuf feature classification is incomplete")

    enum_indexes: set[int] = set()
    discriminator_count = 0
    known_fragment_exclusion_reasons = {
        "generated-oneof-discriminator",
        "nested-type",
        "nonempty-namespace",
        "no-enum-members",
        "enum-values-incomplete",
        "first-runtime-member-is-not-zero",
        "value-outside-proto-enum-int32-range",
    }
    for row in unreferenced:
        if not isinstance(row, Mapping):
            raise AcquisitionError("unreferenced enum inventory row is invalid")
        type_index = row.get("type_index_owner_only")
        values = row.get("values")
        classification = row.get("classification")
        exclusion_reasons = row.get("fragment_exclusion_reasons")
        if (
            type(type_index) is not int
            or type_index < 0
            or type_index in enum_indexes
            or classification
            not in {"oneof-discriminator", "unreferenced-runtime-enum"}
            or not isinstance(values, list)
            or type(row.get("member_count")) is not int
            or row.get("member_count") != len(values)
            or type(row.get("captured_value_count")) is not int
            or row.get("captured_value_count") != len(values)
            or not isinstance(exclusion_reasons, list)
            or len(exclusion_reasons) != len(set(exclusion_reasons))
            or any(
                not isinstance(reason, str)
                or reason not in known_fragment_exclusion_reasons
                for reason in exclusion_reasons
            )
        ):
            raise AcquisitionError("unreferenced enum inventory does not close")
        enum_indexes.add(type_index)
        discriminator_count += classification == "oneof-discriminator"
        names: set[str] = set()
        for value in values:
            if (
                not isinstance(value, Mapping)
                or not isinstance(value.get("name"), str)
                or not value["name"]
                or value["name"] in names
                or value.get("captured") is not True
                or type(value.get("value")) is not int
            ):
                raise AcquisitionError(
                    "unreferenced enum inventory contains an uncaptured value"
                )
            names.add(value["name"])
    if (
        type(counts.get("unreferenced_oneof_discriminator_count")) is not int
        or counts.get("unreferenced_oneof_discriminator_count") < 0
        or counts.get("unreferenced_oneof_discriminator_count") != discriminator_count
    ):
        raise AcquisitionError("unreferenced oneof discriminator count differs")

    return {
        "message_count": len(normalized_messages),
        "enum_count": len(normalized_enums),
        "normal_field_count": normal_field_count,
        "oneof_case_count": oneof_case_count,
        "proto_field_count": proto_field_count,
        "runtime_enum_count": runtime_enum_count,
        "unreferenced_enum_count": len(unreferenced),
    }


def write_runtime_proto_outputs_from_model(
    *, static_model: Path, output_dir: Path,
    field_encryption_observation_model: Path | None = None,
    allow_partial_wire_contract: bool = False,
    allow_partial_field_encryption: bool = False,
) -> dict[str, Any]:
    model_path = static_model.expanduser().resolve()
    model = read_private_model(model_path)
    publication_counts = validate_runtime_proto_static_model_for_publication(
        model, allow_partial_wire_contract=allow_partial_wire_contract,
    )
    messages = model["messages_owner_only"]
    enums = model["enums_owner_only"]
    from alpha.p02 import build_evidence, collect_direct_json_evidence, validate_evidence
    evidence = build_evidence(model, collect_direct_json_evidence(model_path, model))
    receipt = write_runtime_proto_outputs(
        items=[*messages, *enums],
        output_dir=output_dir,
        target=model["target"],
        capture_evidence=evidence,
    )
    names = proto_artifact_names(model["target"])
    exported = read_proto_class_list(
        output_dir / names["class_list"], target=model["target"]
    )
    if validate_evidence(exported, model) != evidence:
        raise AcquisitionError("exported capture evidence differs from source")
    field_encryption_output = None
    field_encryption_input = None
    if field_encryption_observation_model is not None:
        from alpha.p50 import write_field_encrypt_artifact

        observation_path = field_encryption_observation_model.expanduser().resolve()
        observation_model = read_private_model(observation_path)
        field_encryption_output = write_field_encrypt_artifact(
            proto_model=model,
            runtime_observation_model=observation_model,
            output_path=output_dir.expanduser().resolve() / names["field_encrypt"],
            allow_partial=allow_partial_field_encryption,
        )
        field_encryption_input = file_identity(observation_path)
    receipt["status"] = "complete"


    receipt["completion_scope"] = "modeled-domain-artifact-generation"
    receipt["full_semantic_verification_complete"] = model.get(
        "full_semantic_verification_complete") is True
    receipt["semantic_verification"] = {
        "signed_encoding_complete": model.get("signed_encoding_coverage_owner_only", {}).get("complete") is True,
        "message_domain_complete": model.get("message_domain_audit_owner_only", {}).get("complete") is True,
    }
    receipt["target"] = model.get("target")
    receipt["input"] = file_identity(model_path)
    receipt["checks"] = {
        "static_model_complete": True,
        "static_model_checks_closed": True,
        "unresolved_records_absent": True,
        "all_runtime_enum_constants_available": True,
        "all_runtime_enum_attribute_evidence_available": True,
        "runtime_enum_domain_closed": True,
        "rendered_counts_match_static_model": (
            receipt["counts"]["message_count"]
            == model["counts"]["message_count"]
            and receipt["counts"]["enum_count"]
            == model["counts"]["enum_count"]
            and receipt["counts"]["proto_field_count"]
            == model["counts"]["proto_field_count"]
        ),
        "four_primary_outputs_written": len(receipt["files"]) == 4,
        "complete_source_model_preserved_in_primary_outputs": True,
        "direct_json_evidence_preserved_in_primary_outputs": True,
    }
    if field_encryption_output is not None:
        receipt["field_encryption_output"] = field_encryption_output
        receipt["field_encryption_input"] = field_encryption_input
        receipt["checks"]["field_encryption_runtime_domain_classified"] = True
        receipt["checks"]["field_encryption_artifact_written"] = True
        receipt["checks"]["field_encryption_deferred_roles_recorded"] = True
    if not all(receipt["checks"].values()):
        raise AcquisitionError("runtime proto rendered output counts differ")
    if receipt["counts"]["proto_field_count"] != publication_counts["proto_field_count"]:
        raise AcquisitionError("runtime proto published field count differs")
    receipt_path = output_dir.expanduser().resolve() / names["receipt"]
    _atomic_write_text(receipt_path, _json_text(receipt))
    receipt["receipt"] = file_identity(receipt_path)
    return receipt
