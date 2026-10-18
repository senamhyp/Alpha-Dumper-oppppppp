import re
from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.c01 import decode_x64, decode_x64_many
from alpha.c02 import _ALIASES, _REGS
from alpha.c03 import _bytes, _integer, _nop


def prove(code, decoded=None):
    rows = decode_x64(code) if decoded is None else decoded
    returns = [off for off, text in rows if text == "ret"]
    if not returns:
        raise AcquisitionError("descriptor flag proof has no bounded return")
    finish = returns[0]; boundaries = dict(rows)
    token = lambda name: tuple((name, i) for i in range(8))
    receiver, descriptor = token("receiver"), token("descriptor")
    origin = 0xFFFF000000000008
    regs = {r: token("entry-" + r) for r in _REGS}
    regs.update(rcx=receiver, rsp=_bytes(origin))
    preserved = {r: regs[r] for r in ("rbx", "rbp", "rsi", "rdi", "r12", "r13", "r14", "r15", "rsp")}
    stack, reads, branches, visited = {}, [], [], []
    zf = None
    def reg(name):
        if name not in _ALIASES: raise AcquisitionError("descriptor flag proof register is unsupported")
        full, width = _ALIASES[name]; return regs[full][:width]
    def assign(name, value):
        if name not in _ALIASES: raise AcquisitionError("descriptor flag proof destination is unsupported")
        full, width = _ALIASES[name]
        if len(value) != width: raise AcquisitionError("descriptor flag proof assignment width differs")
        regs[full] = tuple(value) + ((0,) * 4 if width == 4 else regs[full][width:])
    def integer(value):
        if any(type(b) is not int for b in value): raise AcquisitionError("descriptor flag proof uses unknown arithmetic")
        return _integer(value)
    def load(text):
        if text in _ALIASES: return reg(text)
        match = re.fullmatch(r"(QWORD|BYTE) PTR \[(r\w+)(?:\+(0x[0-9a-f]+))?\]", text)
        if not match: raise AcquisitionError("descriptor flag proof memory expression differs")
        width, base, displacement = match.groups(); offset = int(displacement, 16) if displacement else 0
        value = reg(base)
        if width == "QWORD" and value == receiver and not reads:
            reads.append(dict(kind="receiver-descriptor", offset=offset, width=8)); return descriptor
        if width == "BYTE" and value == descriptor and len(reads) == 1:
            reads.append(dict(kind="descriptor-byte", offset=offset, width=1))
            return (("byte-domain", tuple(range(256))),)
        raise AcquisitionError("descriptor flag proof reaches an unmodeled native load")
    for off, text in rows:
        if off > finish: break
        visited.append(off); parts = text.split(None, 1); op = parts[0]
        args = tuple(s.strip() for s in parts[1].split(",")) if len(parts) > 1 else ()
        if _nop(text): continue
        if op in ("push", "pop") and len(args) == 1:
            if args[0] not in preserved or args[0] == "rsp": raise AcquisitionError("descriptor flag proof stack operand differs")
            sp = integer(reg("rsp"))
            if op == "push":
                sp -= 8
                if sp < origin - 4096 or sp in stack: raise AcquisitionError("descriptor flag proof stack bound differs")
                stack[sp] = reg(args[0]); assign("rsp", _bytes(sp))
            else:
                if sp not in stack: raise AcquisitionError("descriptor flag proof stack save is absent")
                assign(args[0], stack.pop(sp)); assign("rsp", _bytes(sp + 8))
        elif op in ("sub", "add") and len(args) == 2 and args[0] == "rsp":
            delta = int(args[1], 0); sp = integer(reg("rsp")) + (delta if op == "add" else -delta)
            if delta <= 0 or delta & 7 or not origin - 4096 <= sp <= origin: raise AcquisitionError("descriptor flag proof stack adjustment differs")
            assign("rsp", _bytes(sp)); zf = None
        elif op == "test" and len(args) == 2 and reg(args[0]) == reg(args[1]) and reg(args[0]) in (receiver, descriptor):
            zf = False
        elif op == "je" and len(args) == 1:
            target = int(args[0], 0)
            if zf is not False or target <= finish or target not in boundaries:
                raise AcquisitionError("descriptor flag proof null branch is not excluded")
            branches.append(dict(instruction_offset=off, excluded_target_offset=target))
        elif op in ("mov", "movzx") and len(args) == 2:
            if args[0] not in _ALIASES: raise AcquisitionError("descriptor flag proof refuses native writes")
            value = load(args[1]); width = _ALIASES[args[0]][1]
            if op == "movzx": value += (0,) * (width - len(value))
            assign(args[0], value[:width])
        elif op in ("and", "shr") and len(args) == 2:
            value = reg(args[0])
            if len(value) != 1 or not isinstance(value[0], tuple) or value[0][0] != "byte-domain":
                raise AcquisitionError("descriptor flag proof bit operation is not on the input byte")
            amount = int(args[1], 0)
            if not 0 <= amount <= 255: raise AcquisitionError("descriptor flag proof bit immediate differs")
            domain = tuple(v & amount if op == "and" else v >> (amount & 31) for v in value[0][1])
            assign(args[0], (("byte-domain", domain),)); zf = None
        elif op == "ret" and not args:
            value = reg("al")
            if (len(reads) != 2 or stack or any(regs[r] != v for r, v in preserved.items())
                    or not isinstance(value[0], tuple) or value[0][0] != "byte-domain"):
                raise AcquisitionError("descriptor flag proof return, read domain, or ABI differs")
            bits = [bit for bit in range(8) if value[0][1] == tuple((v >> bit) & 1 for v in range(256))]
            if len(bits) != 1: raise AcquisitionError("descriptor flag proof does not return one exact bit")
            return dict(receiver_descriptor_offset=reads[0]["offset"], descriptor_flag_byte_offset=reads[1]["offset"],
                descriptor_flag_mask=1 << bits[0], input_byte_cases=256, output_width=1,
                required_receiver_nonnull=True, required_descriptor_nonnull=True,
                required_receiver_descriptor_readable=True, required_descriptor_flag_byte_readable=True,
                arbitrary_other_entry_registers_allowed=True, preserved_win64_registers_proven=True,
                native_memory_writes=False, visited_instruction_offsets=visited, reads=reads, excluded_branches=branches,
                flag_semantic_identity_proven=False, null_paths_proven=False, metadata_complete=False)
        else:
            raise AcquisitionError("descriptor flag proof instruction is unsupported: " + text)
    raise AcquisitionError("descriptor flag proof did not reach its bounded return")


def rewrite_reference_byref(source, *, code, handle_qword):

    proof = prove(code)
    if (type(handle_qword) is not int or not 0 <= handle_qword < 4096
            or handle_qword * 8 != proof["receiver_descriptor_offset"]):
        raise AcquisitionError("reference ByRef descriptor field differs from proved getter")
    old = ("uint64_t source_bits=0;memcpy(&source_bits,(const void*)(target->descriptor+8u),8u);"
        "uint8_t source_byref=!!(source_bits&(1ull<<30));")
    if not isinstance(source, str) or source.count(old) != 1:
        raise AcquisitionError("reference ByRef source seam is absent or repeated")
    offset, mask = proof["descriptor_flag_byte_offset"], proof["descriptor_flag_mask"]
    new = (f"uint8_t source_flag_byte=0;"
        f"if(target->descriptor>UINTPTR_MAX-{offset}u||!readable(target->descriptor+{offset}u,1u))"
        "{failure_index=capture_index+1u;failure_kind=16001u;return 0;}"
        f"memcpy(&source_flag_byte,(const void*)(target->descriptor+{offset}u),1u);"
        f"uint8_t source_byref=!!(source_flag_byte&{mask}u);")
    return source.replace(old, new, 1)


import hashlib
from dataclasses import dataclass

from alpha.h01 import AcquisitionError
from alpha.c03 import EncodedWordDispatch, derive_encoded_word_dispatch
from alpha.c02 import _ALIASES
from alpha.c03 import ReadExpression, trace_indexed_reads, variables
from alpha.c01 import decode_x64


@dataclass(frozen=True)
class EncodedVtableCodeContract:
    class_input: str
    slot_input: str
    read: ReadExpression
    dispatch: EncodedWordDispatch
    helper_code_sha256: str
    candidate_count: int
    alternative_pointer_read: ReadExpression | None = None
    alternative_count_expression: tuple | None = None


def _loads(expr):
    if expr[0] == "load":
        yield expr
    for child in expr[1:]:
        if isinstance(child, tuple):
            yield from _loads(child)


def derive_encoded_vtable_contract(code: bytes, *, current_code_va: int) -> EncodedVtableCodeContract:
    registers = {full for full, _ in _ALIASES.values()}
    candidates = []
    reads = trace_indexed_reads(code, current_code_va=current_code_va)
    for read in reads:
        inputs = variables(read.expression)
        if (read.expression[2] != 4 or len(inputs) != 2 or not inputs <= registers
            or read.guard is None or read.guard_zero_required is None):
            continue
        guard_inputs = variables(read.guard)
        guard_loads = list(_loads(read.guard))
        if len(guard_inputs) != 1 or not guard_inputs <= inputs or len(guard_loads) != 1:
            continue


        if not any(isinstance(child, tuple) and child[0] == "constant" and child[1] != 0 for child in read.guard[1:]):
            continue
        class_input = next(iter(guard_inputs))
        slot_input = next(iter(inputs - guard_inputs))
        dependent_loads = [node for node in _loads(read.expression) if class_input in variables(node)]
        if len(dependent_loads) < 3:
            continue
        try:
            dispatch = derive_encoded_word_dispatch(code, load_instruction_offset=read.instruction_offset)
        except AcquisitionError:
            continue
        candidates.append((class_input, slot_input, read, dispatch))
    if len(candidates) != 1:
        raise AcquisitionError(f"guarded encoded-vtable code contract is not unique (candidates={len(candidates)})")
    class_input, slot_input, read, dispatch = candidates[0]
    entry = read.guard_alternative_entry_offset
    alternative = []
    if entry is not None:


        instructions = decode_x64(code)
        end = next((offset for offset, text in instructions if offset >= entry and text.split(None, 1)[0].startswith(("j", "call", "ret"))), len(code))
        for pointer in reads:
            if not entry <= pointer.instruction_offset < end or pointer.expression[2] != 8:
                continue
            if variables(pointer.expression) != {class_input, slot_input}:
                continue
            counts = [node for node in _loads(pointer.expression) if variables(node) == {class_input}]
            if len(counts) == 1:
                alternative.append((pointer, counts[0]))
        if len(alternative) > 1:
            raise AcquisitionError("native vtable alternative pointer branch is ambiguous")
    pointer, count = alternative[0] if alternative else (None, None)
    return EncodedVtableCodeContract(class_input, slot_input, read, dispatch,
        hashlib.sha256(code).hexdigest(), len(candidates), pointer, count)


from dataclasses import asdict
import hashlib

from alpha.h01 import AcquisitionError
from alpha.c02 import discover_extent_copy_candidates
from alpha.c01 import decode_x64
from alpha.c03 import verify_current_small_copy, copy_boundary_cases


def root_self_return_methods(*, identity_rows, method_rows, ancestry_rows):
    identities, classes, descriptors = {}, {}, set()
    for row in identity_rows:
        if len(row) != 13 or row[0] in identities or not row[2] or row[2] in descriptors or not row[3] or row[3] in classes:
            raise AcquisitionError("root extent TypeDef identity domain is invalid")
        identities[row[0]] = row; classes[row[3]] = row[0]; descriptors.add(row[2])
    relations, roots = {}, {}
    for row in ancestry_rows:
        if (len(row) != 5 or row[0] not in identities or row[0] in relations or row[2] != identities[row[0]][3]
                or row[1] not in (1, 2) or (row[1] == 1) != (row[3] == 0) or bool(row[3]) != bool(row[4])):
            raise AcquisitionError("root extent ancestry domain is inconsistent")
        if row[3] in classes and identities[classes[row[3]]][2] != row[4]:
            raise AcquisitionError("root extent parent class and descriptor differ")
        relations[row[0]] = row
        if row[1] == 1 and not identities[row[0]][7] & 0x20 and not identities[row[0]][1] & (32 | 64):
            roots[row[0]] = identities[row[0]][2]
    if set(relations) != set(identities):
        raise AcquisitionError("root extent ancestry domain is incomplete")


    checked = set()
    external_parents = set()
    for origin in relations:
        chain = set()
        current = origin
        while current not in checked:
            if current in chain:
                raise AcquisitionError("root extent ancestry domain is cyclic")
            chain.add(current)
            parent = relations[current][3]
            if not parent:
                break
            if parent not in classes:
                external_parents.add(parent)
                break
            current = classes[parent]
        checked.update(chain)
    methods, seen = [], set()
    for index, row in enumerate(method_rows):
        if len(row) != 13 or row[0] not in identities or not row[2] or row[2] in seen:
            raise AcquisitionError("root extent MethodDef owner/identity differs")
        seen.add(row[2])
        if (row[0] in roots and row[4] == roots[row[0]] and not row[5] & (0x10 | 0x400)
                and not row[9] & 1 and row[10] == 0 and row[3]):
            methods.append({"type_index": row[0], "method_index": index, "metadata_pointer": row[2],
                            "method_pointer": row[3], "class_pointer": identities[row[0]][3]})
    return {"root_count": len(roots), "methods": methods,
            "external_parent_class_count": len(external_parents),
            "ancestry_closed": not external_parents}


def bounded_current_body(image, pointer, *, image_base, max_hops=8):

    trace, seen = [], set()
    rva = pointer - image_base
    for _ in range(max_hops):
        if rva in seen or not image.executable_rva(rva):
            raise AcquisitionError("root extent thunk is cyclic or outside executable code")
        seen.add(rva)
        offset = image.rva_to_offset(rva)
        if offset is None:
            raise AcquisitionError("root extent code has no current file mapping")
        section = next((s for s in image.executable_sections if s.raw_offset <= offset < s.raw_end), None)
        if section is None:
            raise AcquisitionError("root extent mapped code is not executable")
        prefix = bytes(image._mapping[offset:min(offset + 5, section.raw_end)])
        width = 5 if prefix[:1] == b"\xe9" else 2 if prefix[:1] == b"\xeb" else 0
        if width:
            if len(prefix) < width:
                raise AcquisitionError("root extent direct thunk is truncated")
            target = rva + width + int.from_bytes(prefix[1:width], "little", signed=True)
            trace.append({"pointer": image_base + rva, "code_hex": prefix[:width].hex(), "target_pointer": image_base + target})
            rva = target
            continue
        function = image.containing_function(rva)
        if function is None or not 0 < function.end_rva - rva <= 1 << 20:
            raise AcquisitionError("root extent operation has no bounded current function extent")
        bounds = image.bounded_code(rva, function.end_rva)
        if bounds is None or bounds[0] != offset or bounds[1] > section.raw_end:
            raise AcquisitionError("root extent current function bounds differ")
        code = bytes(image._mapping[bounds[0]:bounds[1]])
        return image_base + rva, code, trace
    raise AcquisitionError("root extent direct thunk chain exceeds bounded analysis")


def control_flow_obligations(code, pointer):

    external, indirect = [], []
    for offset, text in decode_x64(code):
        parts = text.split(None, 1)
        operation = parts[0]
        if operation != "call" and not operation.startswith("j"):
            continue
        operand = parts[1] if len(parts) == 2 else ""
        try:
            target = int(operand, 0)
            if target >= 1 << 63:
                target -= 1 << 64
        except ValueError:
            indirect.append({"instruction_offset": offset, "operation": operation, "operand": operand})
            continue
        if not 0 <= target < len(code):
            external.append({"instruction_offset": offset, "operation": operation, "target_pointer": pointer + target})
    return {"external_edges": external, "indirect_edges": indirect, "all_paths_proven": False}


def bounded_copy_tails(image, code, pointer, image_base):
    bodies, rejected = [], []
    for target in sorted({edge["target_pointer"] for edge in control_flow_obligations(code, pointer)["external_edges"]}):
        try:
            try:
                entry, body, thunks = bounded_current_body(image, target, image_base=image_base)
            except AcquisitionError:


                if not target < pointer or pointer - target > 1 << 20:
                    raise
                begin, end = target - image_base, pointer - image_base
                bounds = image.bounded_code(begin, end)
                if not image.executable_rva(begin) or bounds is None or bounds[1] - bounds[0] != end - begin:
                    raise AcquisitionError("copy tail has no complete current code interval")
                entry, body, thunks = target, bytes(image._mapping[bounds[0]:bounds[1]]), []
            bodies.append({"body_pointer": entry, "body_code_hex": body.hex(),
                "body_code_sha256": hashlib.sha256(body).hexdigest(), "thunks": thunks,
                "control_flow": control_flow_obligations(body, entry), "role_proven": False})
        except AcquisitionError as error:
            rejected.append({"pointer": target, "reason": str(error)})
    return bodies, rejected


def derive_extent_candidates(*, identity_rows, method_rows, ancestry_rows, image, image_base):
    selected = root_self_return_methods(identity_rows=identity_rows, method_rows=method_rows, ancestry_rows=ancestry_rows)
    resolved, rejected = [], []
    for method in selected["methods"]:
        try:
            pointer, code, trace = bounded_current_body(image, method["method_pointer"], image_base=image_base)
            candidates = discover_extent_copy_candidates(code)
        except AcquisitionError as error:
            rejected.append(dict(method, reason=str(error)))
            continue
        helpers, unresolved_helpers = {}, []
        for candidate in candidates:
            for role, offset in (("allocation", candidate.allocation_callee_offset), ("copy", candidate.copy_callee_offset)):
                entry = pointer + offset
                if (role, entry) in helpers:
                    continue
                try:
                    helper_pointer, helper_code, helper_trace = bounded_current_body(image, entry, image_base=image_base)
                except AcquisitionError as error:
                    unresolved_helpers.append({"role_candidate": role, "entry_pointer": entry, "reason": str(error)})
                    continue
                helpers[role, entry] = {"role_candidate": role, "entry_pointer": entry, "body_pointer": helper_pointer,
                    "body_code_hex": helper_code.hex(), "body_code_sha256": hashlib.sha256(helper_code).hexdigest(),
                    "thunks": helper_trace, "control_flow": control_flow_obligations(helper_code, helper_pointer), "role_proven": False}
                if role == "copy":
                    tails, tail_rejections = bounded_copy_tails(image, helper_code, helper_pointer, image_base)
                    helpers[role, entry]["external_tail_bodies"] = tails
                    helpers[role, entry]["unresolved_external_tails"] = tail_rejections
                    try:
                        helpers[role, entry]["small_copy_replay"] = verify_current_small_copy(image, helper_code, helper_pointer, image_base)
                    except AcquisitionError as error:
                        helpers[role, entry]["small_copy_unresolved"] = str(error)
                    try:
                        limits = sorted({(1 << (item.class_extent_width * 8)) - 1 - item.payload_offset
                            for item in candidates if pointer + item.copy_callee_offset == entry})
                        cases = sorted({case for limit in limits for case in copy_boundary_cases(helper_code, limit)})
                        helpers[role, entry]["copy_boundary_case_domain"] = {"payload_limits_from_candidate_widths": limits,
                            "cases": [list(case) for case in cases]}
                        external = {tail["body_pointer"]: bytes.fromhex(tail["body_code_hex"]) for tail in tails}
                        external.update({thunk["pointer"]: bytes.fromhex(thunk["code_hex"]) for tail in tails for thunk in tail["thunks"]})
                        replay = verify_current_small_copy(image, helper_code, helper_pointer, image_base, cases=cases, external_bodies=external)
                        replay.update(payload_limits_from_candidate_widths=limits,
                            data_source="current-executable-initial-bytes-not-live-CPU-state")
                        helpers[role, entry]["copy_boundary_replay"] = replay
                    except AcquisitionError as error:
                        helpers[role, entry]["copy_boundary_unresolved"] = str(error)
        resolved.append(dict(method, body_pointer=pointer, body_code_hex=code.hex(),
            body_code_sha256=hashlib.sha256(code).hexdigest(), thunks=trace,
            control_flow=control_flow_obligations(code, pointer), helpers=list(helpers.values()), unresolved_helpers=unresolved_helpers,
            extent_copy_candidates=[dict(asdict(candidate), allocation_callee_pointer=pointer + candidate.allocation_callee_offset,
                copy_callee_pointer=pointer + candidate.copy_callee_offset) for candidate in candidates]))
    return {"schema": "alpha.root-extent-candidates/v1", "root_count": selected["root_count"],
        "external_parent_class_count": selected["external_parent_class_count"],
        "ancestry_closed": selected["ancestry_closed"],
        "method_candidate_count": len(selected["methods"]), "resolved": resolved, "rejected": rejected,
        "name_seed_used": False, "fixed_offset_used": False, "fixed_ordinal_used": False,
        "method_invoked": False, "allocator_role_proven": False, "copy_role_proven": False,
        "object_payload_origin_proven": False, "native_type_sizes_proven": False, "metadata_complete": False}


from collections import Counter

from alpha.h01 import AcquisitionError
prove_flag = prove
from alpha.p05 import prove as prove_qword


def derive(*, qword_methods, flag_methods, object_references, read, object_class):

    if type(object_class) is not int or not 0 < object_class < 1 << 64:
        raise AcquisitionError("descriptor relation object class is invalid")
    candidates, rejected = {}, []
    for domain, methods, prover in (("qword", qword_methods, prove_qword), ("flag", flag_methods, prove_flag)):
        found, seen = [], set()


        decoded_rows = decode_x64_many([
            method["code"] for method in methods
            if isinstance(method.get("code"), bytes)
            and 0 < len(method["code"]) <= 1_048_576
        ])
        for method in methods:
            identity = method.get("metadata_pointer")
            pointer = method.get("method_pointer")
            if (type(identity) is not int or not 0 < identity < 1 << 64 or identity in seen
                    or type(pointer) is not int or not 0 < pointer < 1 << 64):
                raise AcquisitionError("descriptor relation method identity is invalid or repeated")
            if not isinstance(method.get("code"), bytes) or not 0 < len(method["code"]) <= 1_048_576:
                raise AcquisitionError("descriptor relation method code is invalid or unbounded")
            seen.add(identity)
            decoded = decoded_rows[method["code"]]
            try:
                if isinstance(decoded, AcquisitionError):
                    raise decoded
                proof = prover(method["code"], decoded)
            except AcquisitionError as error:
                rejected.append(dict(domain=domain, metadata_pointer=identity, reason=str(error)[:512]))
                continue
            found.append(dict(metadata_pointer=identity, method_pointer=pointer, proof=proof))
        candidates[domain] = found
    pairs = [(q, f) for q in candidates["qword"] for f in candidates["flag"]
             if q["proof"]["receiver_qword_offset"] == f["proof"]["receiver_descriptor_offset"]]
    if len(pairs) != 1:
        raise AcquisitionError(f"descriptor getter data-flow pair is not unique (candidates={len(pairs)})")
    qword, flag = pairs[0]
    offset = qword["proof"]["receiver_qword_offset"]
    byte_offset = flag["proof"]["descriptor_flag_byte_offset"]
    mask = flag["proof"]["descriptor_flag_mask"]
    if offset % 8:
        raise AcquisitionError("descriptor relation receiver field is not qword aligned")
    references, values, set_descriptors, clear_descriptors = set(), Counter(), set(), set()
    sample_rows, rejected_objects = [], Counter()

    def bounded_read(pointer, displacement, width):
        if pointer + displacement > (1 << 64) - width:
            return None
        raw = read(pointer + displacement, width)
        if raw is not None and (not isinstance(raw, bytes) or len(raw) != width):
            raise AcquisitionError("descriptor relation read has an invalid exact width")
        return raw

    for receiver in object_references:
        if type(receiver) is not int or not 0 < receiver < 1 << 64 or receiver in references:
            raise AcquisitionError("descriptor relation object reference is invalid or repeated")
        references.add(receiver)
        owner = bounded_read(receiver, 0, 8)
        if owner is None or int.from_bytes(owner, "little") != object_class:
            rejected_objects["not_class_header"] += 1; continue
        raw = bounded_read(receiver, offset, 8)
        if raw is None:
            rejected_objects["receiver_field_unreadable"] += 1; continue
        descriptor = int.from_bytes(raw, "little")
        byte = bounded_read(descriptor, byte_offset, 1) if descriptor else None
        if byte is None:
            rejected_objects["descriptor_byte_unreadable"] += 1; continue
        value = byte[0]; values[value] += 1
        (set_descriptors if value & mask else clear_descriptors).add(descriptor)
        sample_rows.append(dict(receiver=receiver, descriptor=descriptor, byte_value=value))
    if set_descriptors & clear_descriptors:
        raise AcquisitionError("descriptor relation source changed within an observation")

    if len(set_descriptors) < 2 or len(clear_descriptors) < 8:
        raise AcquisitionError("descriptor relation distinct set/clear support is insufficient")
    return dict(selected_field_qword=offset // 8, qword_getter=qword, flag_getter=flag,
        qword_candidate_count=len(candidates["qword"]), flag_candidate_count=len(candidates["flag"]),
        pair_candidate_count=1, rejected_methods=rejected,
        object_reference_count=len(references), readable_object_count=len(sample_rows),
        distinct_set_descriptor_count=len(set_descriptors), distinct_clear_descriptor_count=len(clear_descriptors),
        set_count=sum(n for value, n in values.items() if value & mask),
        clear_count=sum(n for value, n in values.items() if not value & mask),
        byte_value_counts=dict(sorted(values.items())), samples=sample_rows,
        rejected_object_counts=dict(rejected_objects), native_type_enum_convention_used=False,
        fixed_descriptor_length_used=False, fixed_descriptor_offset_used=False,
        descriptor_field_data_flow_proven=True, descriptor_semantic_identity_proven=False,
        all_native_layouts_current_derived=False, metadata_complete=False)


import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError
from alpha.p01 import reflection_contract
from alpha.p02 import runtime_inventory_contract
from alpha.c03 import MEMBER_CATEGORIES, load_runtime_member_observation
from alpha.c03 import load_runtime_type_identity_observation
from alpha.h02 import file_identity, sha256_file


RUNTIME_MEMBER_DETAIL_SCHEMA = "alpha.runtime-member-detail-observation/v2"
RUNTIME_MEMBER_DETAIL_MAGIC = b"ALPHAMD2"
RUNTIME_MEMBER_DETAIL_VERSION = 2
RUNTIME_MEMBER_DETAIL_HEADER = struct.Struct(
    "<8sIIII64s64s64s64s64s64sQ5Q"
)
RUNTIME_MEMBER_DETAIL_TYPE = struct.Struct("<5I")
RUNTIME_MEMBER_DETAIL_FIELD = struct.Struct("<QIIIIQ")
RUNTIME_MEMBER_DETAIL_METHOD = struct.Struct("<QIIIIIQQII")
RUNTIME_MEMBER_DETAIL_PARAMETER = struct.Struct("<QIIIIQ")
RUNTIME_MEMBER_DETAIL_PROPERTY = struct.Struct("<QIIIQQ")
RUNTIME_MEMBER_DETAIL_EVENT = struct.Struct("<QIIIQQQQ")
DETAIL_CATEGORIES = MEMBER_CATEGORIES[:5]
METHOD_DETAIL_CONSTRUCTOR = 1 << 0
METHOD_DETAIL_GENERIC = 1 << 1
METHOD_DETAIL_GENERIC_DEFINITION = 1 << 2
METHOD_DETAIL_MASK = (1 << 3) - 1
PARAMETER_DETAIL_IN = 1 << 0
PARAMETER_DETAIL_OUT = 1 << 1
PARAMETER_DETAIL_OPTIONAL = 1 << 2
PARAMETER_DETAIL_MASK = (1 << 3) - 1
MAXIMUM_DETAIL_STRING_BYTES = 16_384
MAXIMUM_PARAMETERS_PER_METHOD = 65_536
MAXIMUM_GENERIC_ARGUMENTS_PER_METHOD = 65_536
_SHA256 = re.compile(r"^[0-9a-f]{64}$")
_TOKEN_TABLES = {
    "fields": 0x04,
    "methods": 0x06,
    "constructors": 0x06,
    "properties": 0x17,
    "events": 0x14,
}


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime member detail {label} is invalid"
        ) from error
    if not _SHA256.fullmatch(value):
        raise AcquisitionError(f"runtime member detail {label} is invalid")
    return value


def _text(data: bytes, position: int, length: int, *, label: str) -> tuple[str, int]:
    if not 0 < length <= MAXIMUM_DETAIL_STRING_BYTES:
        raise AcquisitionError(f"runtime member detail {label} length is invalid")
    end = position + length
    if end > len(data):
        raise AcquisitionError(f"runtime member detail {label} is truncated")
    try:
        value = data[position:end].decode("utf-8")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime member detail {label} is invalid"
        ) from error
    if not value or any(ord(character) < 0x20 for character in value):
        raise AcquisitionError(f"runtime member detail {label} is invalid")
    return value, end


def _unpack(
    layout: struct.Struct, data: bytes, position: int, *, label: str
) -> tuple[tuple[Any, ...], int]:
    end = position + layout.size
    if end > len(data):
        raise AcquisitionError(f"runtime member detail {label} is truncated")
    return layout.unpack_from(data, position), end


def _pointer(value: int, *, label: str, required: bool = True) -> int | None:
    if (required and not value) or (value and value & 7):
        raise AcquisitionError(f"runtime member detail {label} is invalid")
    return value or None


def _token(value: int, *, category: str) -> int:
    if not value or value >> 24 != _TOKEN_TABLES[category]:
        raise AcquisitionError("runtime member detail metadata token is invalid")
    return value


def load_runtime_member_detail_observation(
    path: Path,
    *,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    type_observation_path = type_observation_path.expanduser().resolve()
    member_observation_path = member_observation_path.expanduser().resolve()
    type_identity_observation_path = type_identity_observation_path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime member detail observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError("runtime member detail observation is not owner-only")
    members = load_runtime_member_observation(
        member_observation_path,
        type_observation_path=type_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    identities = load_runtime_type_identity_observation(
        type_identity_observation_path,
        type_observation_path=type_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    try:
        data = path.read_bytes()
    except OSError as error:
        raise AcquisitionError(
            "runtime member detail observation is unreadable"
        ) from error
    if len(data) < RUNTIME_MEMBER_DETAIL_HEADER.size:
        raise AcquisitionError("runtime member detail observation is truncated")
    (
        magic,
        version,
        header_bytes,
        pointer_bytes,
        reserved,
        executable_raw,
        reflection_raw,
        inventory_raw,
        roots_raw,
        members_raw,
        identities_raw,
        type_count,
        *declared_totals,
    ) = RUNTIME_MEMBER_DETAIL_HEADER.unpack_from(data)
    executable_sha256 = _digest(executable_raw, label="target digest")
    reflection_sha256 = _digest(reflection_raw, label="reflection digest")
    inventory_sha256 = _digest(inventory_raw, label="inventory digest")
    roots_sha256 = _digest(roots_raw, label="type-root digest")
    members_sha256 = _digest(members_raw, label="member-root digest")
    identities_sha256 = _digest(identities_raw, label="type-identity digest")
    reflection = reflection_contract()
    inventory = runtime_inventory_contract()
    expected_totals = [members["counts"][category] for category in DETAIL_CATEGORIES]
    if (
        magic != RUNTIME_MEMBER_DETAIL_MAGIC
        or version != RUNTIME_MEMBER_DETAIL_VERSION
        or header_bytes != RUNTIME_MEMBER_DETAIL_HEADER.size
        or pointer_bytes != 8
        or reserved != 0
        or executable_sha256 != members["target"]["executable_sha256"]
        or executable_sha256 != identities["target"]["executable_sha256"]
        or reflection_sha256
        != reflection["contract_id"].rsplit(":", 1)[-1]
        or inventory_sha256 != inventory["contract_id"].rsplit(":", 1)[-1]
        or roots_sha256 != sha256_file(type_observation_path)
        or members_sha256 != sha256_file(member_observation_path)
        or identities_sha256 != sha256_file(type_identity_observation_path)
        or type_count != members["type_count"]
        or type_count != identities["type_count"]
        or declared_totals != expected_totals
    ):
        raise AcquisitionError("runtime member detail header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime member detail target binding is stale")

    all_method_objects = {
        pointer
        for type_record in members["types"]
        for category in ("methods", "constructors")
        for pointer in type_record[category]
    }
    position = header_bytes
    records: list[dict[str, Any]] = []
    observed_totals = [0] * len(DETAIL_CATEGORIES)
    parameter_objects: set[int] = set()
    reference_count = 0
    parameter_count = 0
    method_generic_argument_count = 0
    for type_index, member_roots in enumerate(members["types"]):
        raw_counts, position = _unpack(
            RUNTIME_MEMBER_DETAIL_TYPE,
            data,
            position,
            label="type counts",
        )
        expected_counts = tuple(
            len(member_roots[category]) for category in DETAIL_CATEGORIES
        )
        if raw_counts != expected_counts:
            raise AcquisitionError(
                "runtime member detail type counts do not match member roots"
            )
        type_record: dict[str, Any] = {"type_index": type_index}
        type_tokens: set[int] = set()

        fields: list[dict[str, Any]] = []
        for expected_object in member_roots["fields"]:
            raw, position = _unpack(
                RUNTIME_MEMBER_DETAIL_FIELD,
                data,
                position,
                label="field",
            )
            member_object, name_bytes, attributes, token, reserved_field, type_object = raw
            if member_object != expected_object or reserved_field != 0:
                raise AcquisitionError("runtime field detail identity is invalid")
            token = _token(token, category="fields")
            if token in type_tokens:
                raise AcquisitionError("runtime member detail tokens are not unique")
            type_tokens.add(token)
            type_object = _pointer(type_object, label="field type")
            name, position = _text(data, position, name_bytes, label="field name")
            fields.append(
                {
                    "member_object": member_object,
                    "name": name,
                    "attributes": attributes,
                    "metadata_token": token,
                    "type_object": type_object,
                }
            )
            reference_count += 1
        type_record["fields"] = fields

        for category, constructor in (("methods", False), ("constructors", True)):
            method_records: list[dict[str, Any]] = []
            for expected_object in member_roots[category]:
                raw, position = _unpack(
                    RUNTIME_MEMBER_DETAIL_METHOD,
                    data,
                    position,
                    label="method",
                )
                (
                    member_object,
                    name_bytes,
                    attributes,
                    impl_attributes,
                    token,
                    detail_flags,
                    return_type,
                    generic_definition,
                    raw_parameter_count,
                    generic_argument_count,
                ) = raw
                if (
                    member_object != expected_object
                    or detail_flags & ~METHOD_DETAIL_MASK
                    or impl_attributes > 0xFFFF
                    or bool(detail_flags & METHOD_DETAIL_CONSTRUCTOR) != constructor
                    or raw_parameter_count > MAXIMUM_PARAMETERS_PER_METHOD
                    or generic_argument_count > MAXIMUM_GENERIC_ARGUMENTS_PER_METHOD
                    or constructor
                    and (
                        return_type
                        or generic_definition
                        or generic_argument_count
                        or detail_flags
                        != METHOD_DETAIL_CONSTRUCTOR
                    )
                    or not constructor and not return_type
                    or bool(detail_flags & METHOD_DETAIL_GENERIC_DEFINITION)
                    and not detail_flags & METHOD_DETAIL_GENERIC
                    or bool(generic_argument_count)
                    != bool(detail_flags & METHOD_DETAIL_GENERIC)
                ):
                    raise AcquisitionError("runtime method detail shape is invalid")
                token = _token(token, category=category)
                if token in type_tokens:
                    raise AcquisitionError(
                        "runtime member detail tokens are not unique"
                    )
                type_tokens.add(token)
                return_reference = _pointer(
                    return_type,
                    label="method return type",
                    required=not constructor,
                )
                definition_reference = _pointer(
                    generic_definition,
                    label="method generic definition",
                    required=bool(detail_flags & METHOD_DETAIL_GENERIC),
                )
                if definition_reference is not None and definition_reference not in all_method_objects:
                    raise AcquisitionError(
                        "runtime method generic definition is absent from roots"
                    )
                name, position = _text(
                    data, position, name_bytes, label="method name"
                )
                parameters: list[dict[str, Any]] = []
                for _ in range(raw_parameter_count):
                    parameter_raw, position = _unpack(
                        RUNTIME_MEMBER_DETAIL_PARAMETER,
                        data,
                        position,
                        label="parameter",
                    )
                    (
                        parameter_object,
                        parameter_name_bytes,
                        parameter_flags,
                        reserved_parameter,
                        reserved_parameter_two,
                        parameter_type,
                    ) = parameter_raw
                    if (
                        not parameter_object
                        or parameter_object & 7
                        or parameter_object in parameter_objects
                        or parameter_flags & ~PARAMETER_DETAIL_MASK
                        or reserved_parameter
                        or reserved_parameter_two
                    ):
                        raise AcquisitionError(
                            "runtime method parameter detail is invalid"
                        )
                    parameter_objects.add(parameter_object)
                    parameter_type = _pointer(
                        parameter_type, label="parameter type"
                    )
                    parameter_name, position = _text(
                        data,
                        position,
                        parameter_name_bytes,
                        label="parameter name",
                    )
                    parameters.append(
                        {
                            "parameter_object": parameter_object,
                            "name": parameter_name,
                            "shape_flags": parameter_flags,
                            "type_object": parameter_type,
                        }
                    )
                    parameter_count += 1
                    reference_count += 1
                argument_bytes = generic_argument_count * pointer_bytes
                end = position + argument_bytes
                if end > len(data):
                    raise AcquisitionError(
                        "runtime method generic arguments are truncated"
                    )
                generic_arguments = (
                    list(
                        struct.unpack_from(
                            f"<{generic_argument_count}Q", data, position
                        )
                    )
                    if generic_argument_count
                    else []
                )
                if any(not value or value & 7 for value in generic_arguments):
                    raise AcquisitionError(
                        "runtime method generic argument is invalid"
                    )
                position = end
                method_generic_argument_count += len(generic_arguments)
                reference_count += len(generic_arguments)
                if return_reference is not None:
                    reference_count += 1
                if definition_reference is not None:
                    reference_count += 1
                method_records.append(
                    {
                        "member_object": member_object,
                        "name": name,
                        "attributes": attributes,
                        "impl_attributes": impl_attributes,
                        "metadata_token": token,
                        "detail_flags": detail_flags,
                        "return_type": return_reference,
                        "generic_definition": definition_reference,
                        "parameters": parameters,
                        "generic_arguments": generic_arguments,
                    }
                )
            type_record[category] = method_records

        properties: list[dict[str, Any]] = []
        type_method_set = set(member_roots["methods"])
        for expected_object in member_roots["properties"]:
            raw, position = _unpack(
                RUNTIME_MEMBER_DETAIL_PROPERTY,
                data,
                position,
                label="property",
            )
            member_object, name_bytes, token, reserved_property, getter, setter = raw
            if member_object != expected_object or reserved_property:
                raise AcquisitionError("runtime property detail identity is invalid")
            token = _token(token, category="properties")
            if token in type_tokens or (
                getter and getter not in type_method_set
            ) or (setter and setter not in type_method_set) or not (getter or setter):
                raise AcquisitionError("runtime property detail references are invalid")
            type_tokens.add(token)
            name, position = _text(
                data, position, name_bytes, label="property name"
            )
            properties.append(
                {
                    "member_object": member_object,
                    "name": name,
                    "metadata_token": token,
                    "getter": getter or None,
                    "setter": setter or None,
                }
            )
        type_record["properties"] = properties

        events: list[dict[str, Any]] = []
        for expected_object in member_roots["events"]:
            raw, position = _unpack(
                RUNTIME_MEMBER_DETAIL_EVENT,
                data,
                position,
                label="event",
            )
            (
                member_object,
                name_bytes,
                token,
                reserved_event,
                handler_type,
                add_method,
                remove_method,
                raise_method,
            ) = raw
            accessors = (add_method, remove_method, raise_method)
            if (
                member_object != expected_object
                or reserved_event
                or any(value and value not in type_method_set for value in accessors)
                or not (add_method or remove_method)
            ):
                raise AcquisitionError("runtime event detail references are invalid")
            token = _token(token, category="events")
            if token in type_tokens:
                raise AcquisitionError("runtime member detail tokens are not unique")
            type_tokens.add(token)
            handler_type = _pointer(handler_type, label="event handler type")
            name, position = _text(data, position, name_bytes, label="event name")
            events.append(
                {
                    "member_object": member_object,
                    "name": name,
                    "metadata_token": token,
                    "handler_type": handler_type,
                    "add_method": add_method or None,
                    "remove_method": remove_method or None,
                    "raise_method": raise_method or None,
                }
            )
            reference_count += 1
        type_record["events"] = events
        records.append(type_record)
        for category_index, count in enumerate(raw_counts):
            observed_totals[category_index] += count

    if position != len(data) or observed_totals != declared_totals:
        raise AcquisitionError(
            "runtime member detail totals or trailer are invalid"
        )
    return {
        "schema": RUNTIME_MEMBER_DETAIL_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contracts": {
            "reflection_contract_id": reflection["contract_id"],
            "inventory_contract_id": inventory["contract_id"],
            "type_observation_sha256": roots_sha256,
            "member_observation_sha256": members_sha256,
            "type_identity_observation_sha256": identities_sha256,
        },
        "type_count": type_count,
        "counts": dict(zip(DETAIL_CATEGORIES, observed_totals, strict=True)),
        "parameter_count": parameter_count,
        "method_generic_argument_count": method_generic_argument_count,
        "type_reference_count": reference_count,
        "types": records,
        "identity": file_identity(path),
        "raw_runtime_member_and_type_objects_owner_only": True,
        "all_type_references_require_graph_resolution": True,
    }


def inspect_runtime_member_detail_observation(
    path: Path,
    *,
    type_observation_path: Path,
    member_observation_path: Path,
    type_identity_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_member_detail_observation(
        path,
        type_observation_path=type_observation_path,
        member_observation_path=member_observation_path,
        type_identity_observation_path=type_identity_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_MEMBER_DETAIL_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contracts": model["contracts"],
        "type_count": model["type_count"],
        "counts": model["counts"],
        "parameter_count": model["parameter_count"],
        "method_generic_argument_count": model[
            "method_generic_argument_count"
        ],
        "type_reference_count": model["type_reference_count"],
        "identity": model["identity"],
        "raw_runtime_objects_exposed": False,
    }
