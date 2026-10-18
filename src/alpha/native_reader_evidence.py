from collections import Counter, deque
from hashlib import sha256
from pathlib import Path
from typing import Any, Mapping

from alpha.c04 import MappedPE
from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity
from alpha.p29 import _bounded_code, _shared_detail_decoder


SCHEMA = "alpha.native-reader-dependencies/v1"


def reader_roots(model: Mapping[str, Any]) -> list[int]:
    roots: set[int] = set()
    pending: list[Any] = [model.get("messages_owner_only", [])]
    while pending:
        value = pending.pop()
        if isinstance(value, Mapping):
            for key, child in value.items():
                if key in {"reader_method_owner_only", "reader_methods_owner_only"}:
                    readers = child if isinstance(child, list) else [child]
                    for reader in readers:
                        if not isinstance(reader, Mapping):
                            raise AcquisitionError("native reader binding is invalid")
                        pointer = reader.get("code_pointer_owner_only")
                        if (type(pointer) is not int or pointer <= 0
                                or type(reader.get("call_target_owner_only")) is not int
                                or reader.get("call_target_owner_only") != pointer):
                            raise AcquisitionError("native reader call target binding differs")
                        roots.add(pointer)
                elif isinstance(child, (Mapping, list)):
                    pending.append(child)
        elif isinstance(value, list):
            pending.extend(value)
    return sorted(roots)


def inspect_body(image: Any, pointer: int, code: bytes, *, entry_offset: int = 0) -> dict[str, Any]:
    from capstone import CS_GRP_CALL, CS_GRP_JUMP, CS_GRP_RET
    from capstone.x86_const import X86_OP_IMM, X86_OP_MEM, X86_REG_RIP

    decoder = _shared_detail_decoder()
    pending = [entry_offset]
    reached: dict[int, Any] = {}
    edges: list[dict[str, Any]] = []
    references: list[dict[str, Any]] = []
    obligations: list[dict[str, Any]] = []
    terminals: list[dict[str, Any]] = []
    while pending:
        offset = pending.pop()
        if offset in reached:
            continue
        if not 0 <= offset < len(code):
            obligations.append({"reason": "control-flow-leaves-body", "offset": offset})
            continue
        instruction = next(decoder.disasm(code[offset:offset + 15], offset, count=1), None)
        if instruction is None:
            obligations.append({"reason": "instruction-decode-failed", "offset": offset})
            continue
        reached[offset] = instruction
        next_offset = offset + instruction.size
        for operand in instruction.operands:
            if operand.type != X86_OP_MEM or operand.mem.base != X86_REG_RIP:
                continue
            address = pointer + next_offset + operand.mem.disp
            section = image.section_for_rva(address - image.image_base)
            end_section = image.section_for_rva(address + max(operand.size, 1) - 1 - image.image_base)
            writable = section is not None and bool(section.characteristics & 0x80000000)
            reference = {"offset": offset, "address_owner_only": address,
                         "bytes": operand.size, "instruction": instruction.mnemonic,
                         "section": section.name if section else None,
                         "writable": writable}
            references.append(reference)


            if instruction.mnemonic == "lea":
                continue
            if section is None or section is not end_section:
                obligations.append({"reason": "image-reference-unbounded", **reference})
            elif writable:
                obligations.append({"reason": "writable-image-state", **reference})
        if instruction.group(CS_GRP_RET):
            terminals.append({"offset": offset, "kind": "return"})
            continue
        if instruction.mnemonic in {"int3", "ud2", "hlt", "sysret", "iret", "iretq", "retf"}:
            terminals.append({"offset": offset, "kind": instruction.mnemonic})
            obligations.append({"reason": "exception-or-privileged-terminal", "offset": offset})
            continue
        is_call = instruction.group(CS_GRP_CALL)
        is_jump = instruction.group(CS_GRP_JUMP)
        if is_call or is_jump:
            direct = bool(instruction.operands and instruction.operands[0].type == X86_OP_IMM)
            target = int(instruction.operands[0].imm) if direct else None
            kind = "call" if is_call else "branch"
            if not direct:
                obligations.append({"reason": "indirect-control-transfer", "offset": offset,
                                    "kind": kind, "operand": instruction.op_str})
            elif is_call or not 0 <= target < len(code):
                edges.append({"offset": offset, "kind": kind,
                              "target_owner_only": pointer + target})
            else:
                pending.append(target)
            if is_call or instruction.mnemonic not in {"jmp", "ljmp"}:
                pending.append(next_offset)
            continue
        pending.append(next_offset)
    if not terminals and not edges:
        obligations.append({"reason": "no-resolved-terminal"})
    return {"code_pointer_owner_only": pointer + entry_offset,
            "code_span_start_owner_only": pointer, "entry_offset": entry_offset,
            "code_bytes": len(code),
            "code_sha256": sha256(code).hexdigest(),
            "reachable_instruction_count": len(reached),
            "edges": sorted(edges, key=lambda row: (row["offset"], row["target_owner_only"])),
            "image_references": sorted(references, key=lambda row: row["offset"]),
            "terminals": sorted(terminals, key=lambda row: row["offset"]),
            "obligations": sorted(obligations, key=lambda row: (row.get("offset", -1), row["reason"])),
            "scalar_semantics_proven": False}


def _native_body(image: Any, pointer: int) -> tuple[int, int, bytes] | None:
    body = _bounded_code(image, pointer)
    if body is not None:
        return pointer, 0, body


    rva = pointer - image.image_base
    if not image.executable_rva(rva):
        return None
    function = image.containing_function(rva)
    if function is None:
        return None
    bounds = image.bounded_code(function.begin_rva, function.end_rva)
    if bounds is None:
        return None
    start, end = bounds
    return (image.image_base + function.begin_rva, rva - function.begin_rva,
            bytes(image._mapping[start:end]))


def inspect_dependencies(image: Any, roots: list[int], *, max_methods: int = 2048) -> dict[str, Any]:
    if type(max_methods) is not int or max_methods <= 0:
        raise ValueError("native reader method budget must be positive")
    if any(type(pointer) is not int or pointer <= 0 for pointer in roots):
        raise ValueError("native reader roots must be positive integer addresses")
    roots = sorted(set(roots))

    pending = deque(roots)
    nodes: dict[int, dict[str, Any]] = {}
    while pending and len(nodes) < max_methods:
        pointer = pending.popleft()
        if pointer in nodes:
            continue
        span = _native_body(image, pointer)
        if span is None:
            node = {"code_pointer_owner_only": pointer, "edges": [],
                    "obligations": [{"reason": "callee-body-unavailable"}],
                    "scalar_semantics_proven": False}
        else:
            span_pointer, entry_offset, body = span
            node = inspect_body(image, span_pointer, body, entry_offset=entry_offset)
        nodes[pointer] = node
        pending.extend(sorted({edge["target_owner_only"] for edge in node["edges"]}
                              - nodes.keys()))
    omitted = sorted(set(pending) - nodes.keys())
    root_rows = []
    for root in roots:
        visited: set[int] = set()
        todo = [root]
        reasons: Counter[str] = Counter()
        while todo:
            pointer = todo.pop()
            if pointer in visited:
                continue
            visited.add(pointer)
            node = nodes.get(pointer)
            if node is None:
                reasons["method-budget-exhausted"] += 1
                continue
            reasons.update(item["reason"] for item in node["obligations"])
            todo.extend(edge["target_owner_only"] for edge in node["edges"])
        root_rows.append({"code_pointer_owner_only": root,
                          "dependency_count": len(visited),
                          "obligation_counts": dict(sorted(reasons.items())),
                          "scalar_semantics_proven": False})
    return {"schema": SCHEMA, "status": "diagnostic-only",
            "image_base_owner_only": image.image_base,
            "roots": root_rows, "methods": [nodes[key] for key in sorted(nodes)],
            "unvisited_targets_owner_only": omitted,
            "policy": {"branches_pruned_by_observation": False,
                       "names_used_as_semantic_proof": False,
                       "end_to_end_function_proven": False,
                       "max_methods": max_methods}}


def build_reader_dependency_inventory(*, binary: Path, proto_model: Mapping[str, Any],
                                      max_methods: int = 2048) -> dict[str, Any]:
    identity = file_identity(binary)
    if identity["sha256"] != proto_model.get("target", {}).get("executable_sha256"):
        raise AcquisitionError("native reader binary differs from the proto target")
    with MappedPE(binary) as image:
        result = inspect_dependencies(image, reader_roots(proto_model), max_methods=max_methods)
    if file_identity(binary) != identity:
        raise AcquisitionError("native reader binary changed during dependency analysis")
    result["binary"] = identity
    return result
