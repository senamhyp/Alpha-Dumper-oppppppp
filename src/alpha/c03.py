from dataclasses import dataclass

from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.c02 import _ALIASES
from alpha.c01 import decode_x64


@dataclass(frozen=True)
class EncodedWordDispatch:
    index_mask: int
    tag_mask: int
    compared_tag: int
    comparison_instruction_offset: int
    branch_instruction_offset: int
    equal_target_offset: int
    different_target_offset: int


def derive_encoded_word_dispatch(code: bytes, *, load_instruction_offset: int) -> EncodedWordDispatch:
    instructions = decode_x64(code)
    indexes = {offset: index for index, (offset, _) in enumerate(instructions)}
    if load_instruction_offset not in indexes:
        raise AcquisitionError("encoded-word load is not an instruction boundary")
    start = indexes[load_instruction_offset]
    instruction = instructions[start][1].split(None, 1)
    operands = [part.strip() for part in instruction[1].split(",")] if len(instruction) == 2 else []
    if (instruction[0] not in ("mov", "movsxd") or len(operands) != 2
        or operands[0] not in _ALIASES or not operands[1].startswith("DWORD PTR [")
        or _ALIASES[operands[0]][1] < 4):
        raise AcquisitionError("encoded-word source is not a current DWORD load")
    registers = {_ALIASES[operands[0]][0]: ("word",)}
    comparison = None

    def value(operand):
        if operand in _ALIASES:
            full, width = _ALIASES[operand]
            return registers.get(full) if width >= 4 else None
        try:
            return ("constant", int(operand, 0) & 0xFFFFFFFF)
        except ValueError:
            return None

    for index in range(start + 1, len(instructions)):
        offset, text = instructions[index]
        parts = text.split(None, 1)
        operation = parts[0]
        operands = [part.strip() for part in parts[1].split(",")] if len(parts) == 2 else []
        if operation in ("je", "jz", "jne", "jnz"):
            if comparison is None or index + 1 >= len(instructions):
                break
            masked, constant, comparison_offset = comparison
            if not masked or masked[0] != "mask" or not constant or constant[0] != "constant":
                break
            high, tag = masked[1], constant[1]
            low = high ^ 0xFFFFFFFF
            if (not 0 < low < 0xFFFFFFFF or low & (low + 1) or tag & low
                or ("mask", low) not in registers.values()):
                break
            try:
                jump_target = int(operands[0], 0)
            except (ValueError, IndexError):
                break
            if jump_target not in indexes:
                break
            fallthrough = instructions[index + 1][0]
            equal, different = (jump_target, fallthrough) if operation in ("je", "jz") else (fallthrough, jump_target)
            return EncodedWordDispatch(low, high, tag, comparison_offset, offset, equal, different)
        if operation.startswith(("j", "call", "ret")):
            break
        if operation in ("nop", "nopl", "nopw"):
            continue
        if operation == "cmp" and len(operands) == 2:
            comparison = value(operands[0]), value(operands[1]), offset
            continue
        if operation in ("mov", "movabs") and len(operands) == 2 and operands[0] in _ALIASES:
            full, width = _ALIASES[operands[0]]
            registers[full] = value(operands[1]) if width >= 4 else None
            continue
        comparison = None
        if not operands or operands[0] not in _ALIASES:

            break
        full, width = _ALIASES[operands[0]]
        if operation == "and" and len(operands) == 2 and width == 4:
            left, right = registers.get(full), value(operands[1])
            if left and left[0] in ("word", "mask") and right and right[0] == "constant":
                mask = right[1] & (left[1] if left[0] == "mask" else 0xFFFFFFFF)
                registers[full] = ("mask", mask)
                continue
        registers[full] = None
    raise AcquisitionError("encoded-word index/tag dispatch is not uniquely proven")


from dataclasses import asdict
import hashlib

from alpha.h01 import AcquisitionError
from alpha.c02 import discover_extent_copy_candidates


def derive_extent_load(model):
    if model.get("schema") != "alpha.root-extent-candidates/v1":
        raise AcquisitionError("extent layout requires a current root operation model")
    found = []
    for root in model.get("resolved", []):
        try:
            code = bytes.fromhex(root["body_code_hex"])
            pointer = root["body_pointer"]
            if (not code or type(pointer) is not int or pointer <= 0
                    or hashlib.sha256(code).hexdigest() != root["body_code_sha256"]):
                raise AcquisitionError("extent layout code identity differs")
            candidates = discover_extent_copy_candidates(code)
            expected = [dict(asdict(candidate),
                allocation_callee_pointer=pointer + candidate.allocation_callee_offset,
                copy_callee_pointer=pointer + candidate.copy_callee_offset)
                for candidate in candidates]
            if root["extent_copy_candidates"] != expected:
                raise AcquisitionError("extent layout candidate does not replay from code")
            found.extend((pointer, candidate, root["body_code_sha256"]) for candidate in candidates)
        except (KeyError, TypeError, ValueError) as error:
            raise AcquisitionError("extent layout operation is malformed") from error

    if len(found) != 1:
        raise AcquisitionError("extent layout needs exactly one rederived candidate")
    pointer, candidate, digest = found[0]
    return {"schema": "alpha.code-derived-extent-load/v1",
        "operation_pointer": pointer, "operation_code_sha256": digest,
        "candidate": asdict(candidate), "operation_candidate_count": len(found),
        "code_rederived": True, "allocator_role_proven": False,
        "object_payload_origin_proven": False, "native_type_sizes_proven": False}


def observe_candidate_extents(model, class_headers, *, include_rows=True):

    load = derive_extent_load(model)
    candidate = load["candidate"]
    offset, width = candidate["class_extent_offset"], candidate["class_extent_width"]
    if not isinstance(class_headers, dict) or not class_headers:
        raise AcquisitionError("extent layout class observation is empty")
    words = {}
    for index, header in class_headers.items():
        if (type(index) is not int or index < 0 or not isinstance(header, bytes)
                or offset + width > len(header)):
            raise AcquisitionError("extent layout class observation is invalid or truncated")
        words[index] = header[offset:offset + width]
    if not include_rows:
        return _observe_extent_words_core(model, words, load, include_rows=False)
    return _observe_extent_words_core(model, words, load, include_rows=True)


def observe_extent_words(model, words):

    return _observe_extent_words_core(model, words, derive_extent_load(model), include_rows=True)


def _observe_extent_words_core(model, words, load, *, include_rows):

    candidate = load["candidate"]
    width, payload = candidate["class_extent_width"], candidate["payload_offset"]
    if not isinstance(words, dict) or not words:
        raise AcquisitionError("extent layout class observation is empty")
    if not include_rows:


        values = [int.from_bytes(raw, "little") for raw in words.values()]
        return {"schema": "alpha.code-derived-class-extent-observation/v1",
            "load": load, "class_count": len(values),
            "distinct_extent_count": len(set(values)),
            "zero_extent_count": values.count(0),
            "negative_copy_count": sum(value < payload for value in values),
            "all_class_rows_covered": True, "fixed_header_window_used": False,
            "fixed_payload_offset_used": False, "fixed_extent_width_used": False,
            "process_identity_verified": False, "two_observations_verified": False,
            "allocator_role_proven": False, "object_payload_origin_proven": False,
            "native_type_sizes_proven": False, "packing_proven": False,
            "alignment_proven": False, "metadata_complete": False}
    rows = []
    for index, raw in words.items():
        if type(index) is not int or index < 0 or not isinstance(raw, bytes) or len(raw) != width:
            raise AcquisitionError("extent layout word identity or width differs")
        extent = int.from_bytes(raw, "little")
        rows.append({"class_index": index, "encoded_extent_hex": raw.hex(),
            "extent_value": extent,
            "candidate_payload_bytes": extent - payload if extent >= payload else None,
            "copy_arithmetic_nonnegative": extent >= payload})
    rows.sort(key=lambda row: row["class_index"])
    return {"schema": "alpha.code-derived-class-extent-observation/v1",
        "load": load, "rows": rows, "class_count": len(rows),
        "distinct_extent_count": len({row["extent_value"] for row in rows}),
        "zero_extent_count": sum(row["extent_value"] == 0 for row in rows),
        "negative_copy_count": sum(not row["copy_arithmetic_nonnegative"] for row in rows),
        "all_class_rows_covered": True, "fixed_header_window_used": False,
        "fixed_payload_offset_used": False, "fixed_extent_width_used": False,
        "process_identity_verified": False, "two_observations_verified": False,
        "allocator_role_proven": False, "object_payload_origin_proven": False,
        "native_type_sizes_proven": False, "packing_proven": False,
        "alignment_proven": False, "metadata_complete": False}


import re
from dataclasses import dataclass

from alpha.h01 import AcquisitionError
from alpha.c02 import _ALIASES
from alpha.c01 import decode_x64


def variables(expr: tuple) -> frozenset[str]:
    if expr[0] == "variable":
        return frozenset({expr[1]})
    return frozenset().union(*(variables(child) for child in expr[1:] if isinstance(child, tuple)))


def evaluate(expr: tuple, values: dict[str, int], reader) -> int:

    op = expr[0]
    if op == "constant":
        return expr[1]
    if op == "variable":
        if expr[1] not in values:
            raise AcquisitionError("native expression input is unbound")
        return values[expr[1]]
    if op == "load":
        address = evaluate(expr[1], values, reader) & ((1 << 64) - 1)
        width = expr[2]
        if width not in (1, 2, 4, 8) or address + width > 1 << 64:
            raise AcquisitionError("native expression read bounds are invalid")
        raw = reader.read(address, width)
        if raw is None or len(raw) != width:
            raise AcquisitionError("native expression read is unavailable")
        return int.from_bytes(raw, "little")
    if op in ("bits", "signed"):
        width = expr[2]
        if width not in (8, 16, 32, 64):
            raise AcquisitionError("native expression integer width is invalid")
        value = evaluate(expr[1], values, reader) & ((1 << width) - 1)
        if op == "signed" and value & (1 << (width - 1)):
            value -= 1 << width
        return value
    if op not in ("add", "sub", "xor", "and", "mul", "shl"):
        raise AcquisitionError("unsupported native expression operation")
    left, right = (evaluate(child, values, reader) for child in expr[1:])
    if op == "add":
        return left + right
    if op == "sub":
        return left - right
    if op == "xor":
        return left ^ right
    if op == "and":
        return left & right
    if op == "mul":
        return left * right
    if not 0 <= right < 64:
        raise AcquisitionError("unsupported native expression shift")
    return left << right


@dataclass(frozen=True)
class ReadExpression:
    instruction_offset: int
    expression: tuple


    guard: tuple | None
    guard_zero_required: bool | None
    guard_branch_instruction_offset: int | None = None
    guard_alternative_entry_offset: int | None = None


def trace_indexed_reads(code: bytes, *, current_code_va: int) -> tuple[ReadExpression, ...]:

    instructions = decode_x64(code)
    by_offset = {offset: index for index, (offset, _) in enumerate(instructions)}
    branch_targets = set()
    successors = {}
    for index, (offset, text) in enumerate(instructions):
        parts = text.split(None, 1)
        operation = parts[0]
        following = [index + 1] if index + 1 < len(instructions) else []
        if operation.startswith("ret"):
            following = []
        elif operation.startswith("j"):
            if operation == "jmp":
                following = []
            try:
                target = int(parts[1], 0)
            except (ValueError, IndexError):
                target = None
            if target in by_offset:
                branch_targets.add(target)
                following.append(by_offset[target])
        successors[index] = following
    reachable, pending = set(), [0] if instructions else []
    while pending:
        index = pending.pop()
        if index in reachable:
            continue
        reachable.add(index)
        pending.extend(successors[index])
    registers: dict[str, tuple] = {}
    guard, zero_required, last_test = None, None, None
    guard_branch, guard_alternative = None, None
    found = []

    def value(operand, next_va):
        if operand in _ALIASES:
            full, width = _ALIASES[operand]
            return ("bits", registers.get(full, ("variable", full)), width * 8)
        match = re.fullmatch(r"(BYTE|WORD|DWORD|QWORD) PTR (\[.*\])", operand)
        if match:
            return ("load", memory(match[2], next_va), {"BYTE": 1, "WORD": 2, "DWORD": 4, "QWORD": 8}[match[1]])
        return ("constant", int(operand, 0))

    def memory(operand, next_va):
        if not operand.startswith("[") or not operand.endswith("]"):
            raise ValueError("unsupported memory operand")
        total = ("constant", 0)
        for term in re.findall(r"[+-]?[^+-]+", operand[1:-1]):
            negative = term.startswith("-")
            factors = term.lstrip("+-").split("*")
            if len(factors) > 2:
                raise ValueError("unsupported indexed address")
            item = ("constant", next_va) if factors[0] == "rip" else value(factors[0], next_va)
            if len(factors) == 2:
                scale = int(factors[1], 0)
                if scale not in (1, 2, 4, 8):
                    raise ValueError("unsupported address scale")
                item = ("mul", item, ("constant", scale))
            total = ("sub" if negative else "add", total, item)
        return total

    for index, (offset, text) in enumerate(instructions):
        if offset in branch_targets:

            registers = {}
            guard, zero_required, last_test = None, None, None
            guard_branch, guard_alternative = None, None
        if index not in reachable:
            continue
        next_va = current_code_va + (instructions[index + 1][0] if index + 1 < len(instructions) else len(code))
        pieces = text.split(None, 1)
        operation = pieces[0]
        operands = [part.strip() for part in pieces[1].split(",")] if len(pieces) == 2 else []
        if operation.startswith(("j", "call", "ret")):
            guard = last_test if operation in ("je", "jz", "jne", "jnz") else None
            zero_required = operation in ("jne", "jnz") if guard is not None else None
            guard_branch = offset if guard is not None else None
            try:
                guard_alternative = int(operands[0], 0) if guard is not None else None
            except (ValueError, IndexError):
                guard, zero_required, guard_branch, guard_alternative = None, None, None, None
            registers = {}
            last_test = None
            continue
        last_test = None
        if operation == "test" and len(operands) == 2:
            try:
                last_test = ("and", value(operands[0], next_va), value(operands[1], next_va))
            except (ValueError, KeyError):
                pass
            continue
        if operation in ("cmp", "nop", "nopl", "nopw"):
            continue
        if not operands or operands[0] not in _ALIASES:
            registers = {}
            guard, zero_required = None, None
            guard_branch, guard_alternative = None, None
            continue
        full, width = _ALIASES[operands[0]]
        if width < 4:
            registers[full] = ("variable", f"partial-write-{offset}-{full}")
            continue
        try:
            if operation in ("mov", "movabs", "movsxd", "movzx", "lea"):
                result = memory(operands[1], next_va) if operation == "lea" else value(operands[1], next_va)
                if result[0] == "load" and "*" in operands[1]:
                    found.append(ReadExpression(offset, result, guard, zero_required, guard_branch, guard_alternative))
                if operation == "movsxd":
                    result = ("signed", result, 32)
            elif operation in ("add", "sub", "xor", "and", "shl"):
                left, right = value(operands[0], next_va), value(operands[1], next_va)
                if operation == "shl":
                    right = ("and", right, ("constant", width * 8 - 1))
                if operation in ("xor", "sub") and operands[0] == operands[1]:
                    result = ("constant", 0)
                else:
                    result = (operation, left, right)
            else:
                raise ValueError("unsupported operation")
            registers[full] = ("bits", result, width * 8)
        except (ValueError, KeyError, IndexError):
            registers[full] = ("variable", f"unsupported-write-{offset}-{full}")
    return tuple(found)


import hashlib
import re

from alpha.h01 import AcquisitionError
from alpha.c02 import _ALIASES, _REGS
from alpha.c01 import decode_x64

_MASK = (1 << 64) - 1
_MEMORY = re.compile(r"(?:(BYTE|WORD|DWORD|QWORD|XMMWORD|YMMWORD) PTR )?\[([^]]+)\]")
_WIDTHS = {"BYTE": 1, "WORD": 2, "DWORD": 4, "QWORD": 8, "XMMWORD": 16, "YMMWORD": 32}
_PRESERVED = ("rbx", "rbp", "rsi", "rdi", "rsp", "r12", "r13", "r14", "r15")
_VECTOR_ALIASES = {f"{prefix}{i}": (f"ymm{i}", width) for i in range(16) for prefix, width in (("xmm", 16), ("ymm", 32))}


def _integer(value):
    if not all(type(byte) is int for byte in value):
        raise AcquisitionError("small copy uses symbolic bytes as an address or condition")
    return int.from_bytes(bytes(value), "little")


def _bytes(value, width=8):
    return tuple((value & ((1 << (width * 8)) - 1)).to_bytes(width, "little"))


def _nop(text):
    return bool(re.fullmatch(r"(?:(?:data16|cs) )*nop(?: .*)?", text))


def _guard(instructions):
    for index, (offset, text) in enumerate(instructions):
        if _nop(text):
            continue
        match = re.fullmatch(r"cmp\s+r8,(0x[0-9a-f]+|[0-9]+)", text)
        if match:
            maximum = int(match[1], 0)
            if maximum > 256 or index + 1 >= len(instructions):
                break
            branch = re.fullmatch(r"ja\s+(0x[0-9a-f]+|[0-9]+)", instructions[index + 1][1])
            if branch and int(branch[1], 0) in dict(instructions) and int(branch[1], 0) > instructions[index + 1][0]:
                return offset, instructions[index + 1][0], maximum
            break
        if not (re.fullmatch(r"mov\s+\w+,\w+", text) or re.fullmatch(r"lea\s+\w+,\[rip[+-]0x[0-9a-f]+\]", text)):
            break
    raise AcquisitionError("small copy has no supported entry size guard")


def verify_small_copy(code, pointer, read_image, *, cases=None, external_bodies=None):

    instructions = decode_x64(code)
    guard_offset, branch_offset, maximum = _guard(instructions)
    extended = cases is not None
    ends = {offset: instructions[i + 1][0] if i + 1 < len(instructions) else len(code)
            for i, (offset, _) in enumerate(instructions)}
    if external_bodies:
        if not extended or not isinstance(external_bodies, dict) or len(external_bodies) > 64:
            raise AcquisitionError("copy replay external body domain is invalid")
        parts = list(instructions)
        occupied = [(pointer, pointer + len(code))]
        for entry, body in external_bodies.items():
            if type(entry) is not int or entry <= 0 or not isinstance(body, bytes) or not 0 < len(body) <= 1 << 20:
                raise AcquisitionError("copy replay external body bounds are invalid")
            if any(entry < end and entry + len(body) > begin for begin, end in occupied):
                raise AcquisitionError("copy replay external code bodies overlap")
            occupied.append((entry, entry + len(body)))
            decoded = decode_x64(body)
            for i, (offset, text) in enumerate(decoded):

                op = text.split(None, 1)
                if op[0].startswith("j") and len(op) == 2:
                    try:
                        target = int(op[1], 0)
                        if target >= 1 << 63: target -= 1 << 64
                        text = op[0] + " " + hex(target + entry - pointer)
                    except ValueError:
                        pass
                parts.append((entry - pointer + offset, text))
                ends[entry - pointer + offset] = entry - pointer + (decoded[i + 1][0] if i + 1 < len(decoded) else len(body))
        instructions = sorted(parts)
    if extended:
        if not isinstance(cases, (list, tuple)) or not cases or len(cases) > 20000:
            raise AcquisitionError("copy replay case domain is invalid")
        if any(not isinstance(case, (list, tuple)) or len(case) != 2 or any(type(v) is not int for v in case)
               or not 0 <= case[0] <= 1 << 20 or abs(case[1]) > case[0] + 4096 for case in cases):
            raise AcquisitionError("copy replay length or distance is invalid")
        if len(set(tuple(case) for case in cases)) != len(cases):
            raise AcquisitionError("copy replay case domain repeats")
    else:
        cases = [(count, distance) for count in range(maximum + 1) for distance in range(-count - 1, count + 2)]
    aliases = dict(_ALIASES, **(_VECTOR_ALIASES if extended else {}))
    positions = {offset: index for index, (offset, _) in enumerate(instructions)}
    tables, visited, case_count = {}, set(), 0
    for count, distance in cases:

        for arena in (0x100000000000, 0x200000000007):
            for _ in (None,):
                source, destination = arena, arena + distance
                memory = {address: ("input", address - arena) for address in
                          range(min(source, destination), max(source, destination) + count)}
                expected = tuple(memory[source + i] for i in range(count))
                registers = {name: tuple(("unknown", name, i) for i in range(8)) for name in _REGS}
                registers.update(rcx=_bytes(destination), rdx=_bytes(source), r8=_bytes(count))


                stack_origin = 0x300000000008
                stack = {}
                if extended:
                    registers["rsp"] = _bytes(stack_origin)
                    registers.update({f"ymm{i}": tuple(("vector", i, byte) for byte in range(32)) for i in range(16)})
                preserved = {name: registers[name] for name in _PRESERVED}
                vector_preserved = {f"ymm{i}": registers[f"ymm{i}"][:16] for i in range(6, 16)} if extended else {}
                index, steps, compared = positions[0], 0, None
                carry = zero = None

                def register(name):
                    if name not in aliases:
                        raise AcquisitionError("small copy register is unsupported")
                    full, width = aliases[name]
                    return registers[full][:width]

                def assign(name, value):
                    if name not in aliases:
                        raise AcquisitionError("small copy destination register is unsupported")
                    full, width = aliases[name]
                    if len(value) != width:
                        raise AcquisitionError("small copy register width differs")
                    registers[full] = tuple(value) + ((0,) * 4 if width == 4 else registers[full][width:])
                    if name in _VECTOR_ALIASES and operation.startswith("v") and width == 16:
                        registers[full] = tuple(value) + (0,) * 16

                def address(operand, next_offset):
                    match = _MEMORY.fullmatch(operand)
                    if not match:
                        raise AcquisitionError("small copy memory operand is unsupported")
                    total = 0
                    for term in re.findall(r"[+-]?[^+-]+", match[2]):
                        sign = -1 if term.startswith("-") else 1
                        term = term.lstrip("+-")
                        if term == "rip":
                            value = pointer + next_offset
                        elif "*" in term:
                            name, scale = term.split("*")
                            if scale not in ("1", "2", "4", "8"):
                                raise AcquisitionError("small copy memory scale is unsupported")
                            value = _integer(register(name)) * int(scale)
                        elif term in _ALIASES:
                            value = _integer(register(term))
                        else:
                            try:
                                value = int(term, 0)
                            except ValueError as error:
                                raise AcquisitionError("small copy memory displacement is unsupported") from error
                        total += sign * value
                    return total & _MASK, _WIDTHS.get(match[1])

                def load(operand, next_offset):
                    if operand in aliases:
                        return register(operand)
                    if not _MEMORY.fullmatch(operand):
                        try:
                            return _bytes(int(operand, 0))
                        except ValueError as error:
                            raise AcquisitionError("copy replay operand is unsupported") from error
                    location, width = address(operand, next_offset)
                    if width is None:
                        raise AcquisitionError("small copy load width is absent")
                    if operation in ("movdqa", "movaps", "vmovdqa", "vmovntdq") and location % width:
                        raise AcquisitionError("copy replay aligned load is misaligned")
                    if source <= location and location + width <= source + count:
                        return tuple(memory[location + i] for i in range(width))
                    if width not in ((1, 4) if extended else (4,)) or min(source, destination) - 4096 <= location <= max(source, destination) + count + 4096:
                        raise AcquisitionError("small copy reads outside its source interval")
                    raw = read_image(location, width)
                    if not isinstance(raw, bytes) or len(raw) != width:
                        raise AcquisitionError("small copy dispatch data is truncated")
                    if location in tables and tables[location] != raw:
                        raise AcquisitionError("small copy dispatch data changed")
                    tables[location] = raw
                    return tuple(raw)

                while True:
                    if not 0 <= index < len(instructions) or steps >= (max(1024, count * 8 + 1024) if extended else 1024):
                        raise AcquisitionError("small copy execution left bounded instructions")
                    steps += 1
                    offset, text = instructions[index]
                    next_offset = ends[offset]
                    next_index = positions.get(next_offset, len(instructions))
                    visited.add(offset)
                    parts = text.split(None, 1)
                    operation = parts[0]
                    operands = parts[1].split(",") if len(parts) == 2 else []
                    if _nop(text):
                        pass
                    elif operation == "ret" and not operands:
                        if stack:
                            raise AcquisitionError("copy replay returns with unbalanced stack saves")
                        if any(registers[name] != value for name, value in preserved.items()):
                            raise AcquisitionError("small copy corrupts a preserved ABI register")
                        if any(registers[name][:16] != value for name, value in vector_preserved.items()):
                            raise AcquisitionError("copy replay corrupts a preserved vector register")
                        if _integer(register("rax")) != destination or tuple(memory[destination + i] for i in range(count)) != expected:
                            raise AcquisitionError("small copy return value or copied bytes differ")
                        case_count += 1
                        break
                    elif extended and operation in ("push", "pop") and len(operands) == 1:
                        target = operands[0]
                        if target not in _ALIASES or _ALIASES[target][1] != 8 or target == "rsp":
                            raise AcquisitionError("copy replay stack operation is unsupported")
                        sp = _integer(register("rsp"))
                        if operation == "push":
                            if not stack_origin - 256 <= sp - 8 < stack_origin or sp - 8 in stack:
                                raise AcquisitionError("copy replay exceeds bounded stack saves")
                            stack[sp - 8] = register(target)
                            assign("rsp", _bytes(sp - 8))
                        else:
                            if sp not in stack:
                                raise AcquisitionError("copy replay pops an unobserved stack slot")
                            assign(target, stack.pop(sp))
                            assign("rsp", _bytes(sp + 8))
                    elif extended and re.fullmatch(r"rep\s+movs\s+BYTE PTR \[rdi\],BYTE PTR \[rsi\]", text):


                        amount = _integer(register("rcx"))
                        src, dst = _integer(register("rsi")), _integer(register("rdi"))
                        if (amount > count or not source <= src <= src + amount <= source + count
                                or not destination <= dst <= dst + amount <= destination + count):
                            raise AcquisitionError("copy replay REP access leaves source or destination")


                        for byte in range(amount):
                            memory[dst + byte] = memory[src + byte]
                        assign("rcx", _bytes(0)); assign("rsi", _bytes(src + amount)); assign("rdi", _bytes(dst + amount))
                    elif operation in ("cmp", "test") and extended and len(operands) == 2:
                        left = load(operands[0], next_offset)
                        bits = len(left) * 8
                        lhs, rhs = _integer(left), _integer(load(operands[1], next_offset)) & ((1 << bits) - 1)
                        carry, zero = ((lhs < rhs, lhs == rhs) if operation == "cmp" else (False, lhs & rhs == 0))
                    elif operation in ("ja", "jae", "jb", "jbe", "je", "jne") and extended and len(operands) == 1:
                        if zero is None or (operation not in ("je", "jne") and carry is None):
                            raise AcquisitionError("copy replay branch flags are unknown")
                        take = {"ja": not carry and not zero, "jae": not carry, "jb": carry,
                                "jbe": carry or zero, "je": zero, "jne": not zero}[operation]
                        if take:
                            target = int(operands[0], 0)
                            if target >= 1 << 63: target -= 1 << 64
                            if target not in positions:
                                raise AcquisitionError("copy replay branch leaves the current bounded body")
                            index = positions[target]
                            continue
                    elif operation == "cmp" and offset == guard_offset:
                        compared = (_integer(register("r8")), maximum)
                    elif operation == "ja" and offset == branch_offset and compared is not None:
                        if compared[0] > compared[1]:
                            raise AcquisitionError("small copy replay escaped its declared length domain")
                    elif operation == "jmp" and len(operands) == 1:
                        try:
                            target = (_integer(register(operands[0])) - pointer) if operands[0] in _ALIASES else int(operands[0], 0)
                            if target >= 1 << 63: target -= 1 << 64
                        except ValueError as error:
                            raise AcquisitionError("small copy jump is unsupported") from error
                        if target not in positions:
                            raise AcquisitionError("small copy jump is not an in-body instruction boundary")
                        index = positions[target]
                        continue
                    elif operation == "lea" and len(operands) == 2:
                        target, _ = address(operands[1], next_offset)
                        assign(operands[0], _bytes(target, _ALIASES.get(operands[0], (None, 0))[1]))
                    elif operation in (("mov", "movzx", "movdqu", "movdqa", "movups", "movaps", "vmovdqu", "vmovdqa", "vmovntdq") if extended else ("mov", "movzx")) and len(operands) == 2:
                        target, operand = operands
                        value = load(operand, next_offset)
                        if target in aliases:
                            width = aliases[target][1]
                            if operation == "movzx":
                                if len(value) >= width:
                                    raise AcquisitionError("small copy zero extension width differs")
                                value += (0,) * (width - len(value))
                            assign(target, value)
                        else:
                            if operation == "movzx":
                                raise AcquisitionError("small copy memory operation is unsupported")
                            location, width = address(target, next_offset)
                            if operation in ("movdqa", "movaps", "vmovdqa", "vmovntdq") and width and location % width:
                                raise AcquisitionError("copy replay aligned store is misaligned")
                            if width != len(value) or not destination <= location or location + width > destination + count:
                                raise AcquisitionError("small copy writes outside its destination interval")
                            memory.update((location + i, byte) for i, byte in enumerate(value))
                    elif extended and operation in ("add", "sub", "and", "shr", "dec") and operands and operands[0] in _ALIASES and len(operands) == (1 if operation == "dec" else 2):
                        width = _ALIASES[operands[0]][1]; bits = width * 8; mask = (1 << bits) - 1
                        lhs = _integer(register(operands[0])); rhs = 1 if operation == "dec" else _integer(load(operands[1], next_offset)) & mask
                        if operation == "add": result, carry = (lhs + rhs) & mask, lhs + rhs > mask
                        elif operation == "sub": result, carry = (lhs - rhs) & mask, lhs < rhs
                        elif operation == "dec": result = (lhs - 1) & mask
                        elif operation == "and": result, carry = lhs & rhs, False
                        else:
                            rhs &= 63 if bits == 64 else 31
                            if not rhs:
                                index = next_index
                                continue
                            result, carry = lhs >> rhs, bool((lhs >> (rhs - 1)) & 1)
                        zero = result == 0
                        assign(operands[0], _bytes(result, width))
                    elif extended and operation in ("sfence", "vzeroupper") and not operands:
                        if operation == "vzeroupper":
                            for i in range(16):
                                registers[f"ymm{i}"] = registers[f"ymm{i}"][:16] + (0,) * 16
                    elif operation == "add" and len(operands) == 2 and all(name in _ALIASES for name in operands):
                        width = _ALIASES[operands[0]][1]
                        assign(operands[0], _bytes(_integer(register(operands[0])) + _integer(register(operands[1])), width))
                        compared = None
                    else:
                        raise AcquisitionError("small copy instruction is unsupported: " + text)
                    index = next_index
    report = {"schema": "alpha.small-copy-symbolic-replay/v1", "maximum_length": maximum,
        "length_count": maximum + 1, "symbolic_case_count": case_count,
        "body_code_sha256": hashlib.sha256(code).hexdigest(), "visited_instruction_offsets": sorted(visited),
        "dispatch_words": [{"pointer": location, "code_hex": raw.hex()} for location, raw in sorted(tables.items())],
        "bounded_cases_verified": True, "symbolic_input_bytes": True, "overlap_distances_enumerated": True,
        "preserved_abi_registers_verified": True, "synthetic_address_placements": 2,
        "live_code_and_data_verified": False, "all_helper_paths_proven": False, "copy_role_proven": False}
    if extended:
        report.update(schema="alpha.copy-case-symbolic-replay/v1", requested_cases=[list(case) for case in cases],
            maximum_length=max(count for count, _ in cases), length_count=len({count for count, _ in cases}),
            overlap_distances_enumerated=False, preserved_vector_registers_verified=True,
            direction_flag_clear_abi_precondition=True, balanced_stack_saves_verified=True)
        if external_bodies:
            report["external_bodies"] = [{"pointer": entry, "code_sha256": hashlib.sha256(body).hexdigest()}
                for entry, body in sorted(external_bodies.items())]
    return report


def copy_boundary_cases(code, maximum_length):

    if type(maximum_length) is not int or not 0 <= maximum_length <= 1 << 20:
        raise AcquisitionError("copy boundary payload limit exceeds bounded replay")
    instructions = decode_x64(code)
    _, _, prefix = _guard(instructions)
    thresholds = {maximum_length}
    for _, text in instructions:
        match = re.fullmatch(r"cmp\s+r8,(0x[0-9a-f]+|[0-9]+)", text)
        if match:
            thresholds.add(int(match[1], 0))
    lengths = set(range(min(prefix, maximum_length) + 1))
    lengths.update(value + delta for value in thresholds for delta in (-1, 0, 1) if 0 <= value + delta <= maximum_length)
    return [(count, distance) for count in sorted(lengths) for distance in
            sorted({0, -1, 1, -count - 1, -count, -count + 1, count - 1, count, count + 1})]


def verify_current_small_copy(image, code, pointer, image_base, *, cases=None, external_bodies=None):
    def read_image(location, width):
        rva = location - image_base
        section = image.section_for_rva(rva)
        offset = image.rva_to_offset(rva)
        if section is None or offset is None or offset + width > section.raw_end:
            raise AcquisitionError("small copy dispatch word is outside current file-backed image")
        return bytes(image._mapping[offset:offset + width])
    return verify_small_copy(code, pointer, read_image, cases=cases, external_bodies=external_bodies)


import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError
from alpha.p02 import DECLARED_MEMBER_BINDING_FLAGS, runtime_inventory_contract
from alpha.p03 import MAXIMUM_TYPE_COUNT, load_runtime_inventory_observation
from alpha.h02 import file_identity, sha256_file


RUNTIME_MEMBER_OBSERVATION_SCHEMA = "alpha.runtime-member-observation/v1"
RUNTIME_MEMBER_OBSERVATION_MAGIC = b"ALPHAMO1"
RUNTIME_MEMBER_OBSERVATION_VERSION = 1
RUNTIME_MEMBER_OBSERVATION_HEADER = struct.Struct(
    "<8sIIII64s64s64s7Q"
)
RUNTIME_MEMBER_OBSERVATION_ENTRY = struct.Struct("<6I")
MEMBER_CATEGORIES = (
    "fields",
    "methods",
    "constructors",
    "properties",
    "events",
    "nested_types",
)
MAXIMUM_MEMBERS_PER_TYPE = 200_000
MAXIMUM_TOTAL_MEMBER_OBJECTS = 8_000_000
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _decode_digest(value: bytes, *, label: str) -> str:
    try:
        digest = value.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime member observation {label} is invalid"
        ) from error
    if not _SHA256.fullmatch(digest):
        raise AcquisitionError(
            f"runtime member observation {label} is invalid"
        )
    return digest


def load_runtime_member_observation(
    path: Path,
    *,
    type_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    type_observation_path = type_observation_path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime member observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError("runtime member observation is not owner-only")
    type_observation = load_runtime_inventory_observation(
        type_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    try:
        data = path.read_bytes()
    except OSError as error:
        raise AcquisitionError("runtime member observation is unreadable") from error
    if len(data) < RUNTIME_MEMBER_OBSERVATION_HEADER.size:
        raise AcquisitionError("runtime member observation is truncated")
    unpacked = RUNTIME_MEMBER_OBSERVATION_HEADER.unpack_from(data)
    (
        magic,
        version,
        header_bytes,
        pointer_bytes,
        binding_flags,
        executable_raw,
        contract_raw,
        type_observation_raw,
        type_count,
        *declared_totals,
    ) = unpacked
    executable_sha256 = _decode_digest(executable_raw, label="target digest")
    contract_sha256 = _decode_digest(contract_raw, label="contract digest")
    type_observation_sha256 = _decode_digest(
        type_observation_raw, label="type observation digest"
    )
    contract = runtime_inventory_contract()
    if (
        magic != RUNTIME_MEMBER_OBSERVATION_MAGIC
        or version != RUNTIME_MEMBER_OBSERVATION_VERSION
        or header_bytes != RUNTIME_MEMBER_OBSERVATION_HEADER.size
        or pointer_bytes != 8
        or binding_flags != DECLARED_MEMBER_BINDING_FLAGS
        or contract_sha256 != contract["contract_id"].rsplit(":", 1)[-1]
        or type_observation_sha256 != sha256_file(type_observation_path)
        or executable_sha256
        != type_observation["target"]["executable_sha256"]
        or type_count != type_observation["type_count"]
        or not 0 < type_count <= MAXIMUM_TYPE_COUNT
        or len(declared_totals) != len(MEMBER_CATEGORIES)
        or sum(declared_totals) > MAXIMUM_TOTAL_MEMBER_OBJECTS
    ):
        raise AcquisitionError("runtime member observation header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime member observation target binding is stale")

    position = header_bytes
    observed_totals = [0] * len(MEMBER_CATEGORIES)
    globally_unique: dict[str, set[int]] = {
        category: set() for category in MEMBER_CATEGORIES
    }
    all_type_objects = {
        pointer
        for assembly in type_observation["assemblies"]
        for pointer in assembly["type_objects"]
    }
    records: list[dict[str, Any]] = []
    for type_index in range(type_count):
        end = position + RUNTIME_MEMBER_OBSERVATION_ENTRY.size
        if end > len(data):
            raise AcquisitionError("runtime member observation is truncated")
        counts = RUNTIME_MEMBER_OBSERVATION_ENTRY.unpack_from(data, position)
        position = end
        record: dict[str, Any] = {"type_index": type_index}
        for category_index, (category, count) in enumerate(
            zip(MEMBER_CATEGORIES, counts, strict=True)
        ):
            if count > MAXIMUM_MEMBERS_PER_TYPE:
                raise AcquisitionError(
                    "runtime member observation per-type count is invalid"
                )
            byte_count = count * pointer_bytes
            end = position + byte_count
            if end > len(data):
                raise AcquisitionError("runtime member observation is truncated")
            pointers = (
                struct.unpack_from(f"<{count}Q", data, position)
                if count
                else ()
            )
            if any(
                not pointer or pointer & (pointer_bytes - 1)
                for pointer in pointers
            ):
                raise AcquisitionError(
                    "runtime member observation contains an invalid pointer"
                )
            if category == "nested_types":
                if any(pointer not in all_type_objects for pointer in pointers):
                    raise AcquisitionError(
                        "runtime nested type is absent from the type inventory"
                    )
            selected = globally_unique[category]
            if len(set(pointers)) != len(pointers) or selected.intersection(
                pointers
            ):
                raise AcquisitionError(
                    f"runtime {category} are not globally unique"
                )
            selected.update(pointers)
            record[category] = list(pointers)
            observed_totals[category_index] += count
            position = end
        records.append(record)
    if (
        position != len(data)
        or observed_totals != declared_totals
        or globally_unique["methods"].intersection(
            globally_unique["constructors"]
        )
    ):
        raise AcquisitionError(
            "runtime member observation totals, method identity, or trailer are invalid"
        )
    return {
        "schema": RUNTIME_MEMBER_OBSERVATION_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contract": {
            "contract_id": contract["contract_id"],
            "declared_member_binding_flags": binding_flags,
            "type_observation_sha256": type_observation_sha256,
        },
        "type_count": type_count,
        "counts": dict(zip(MEMBER_CATEGORIES, observed_totals, strict=True)),
        "types": records,
        "identity": file_identity(path),
        "raw_runtime_member_objects_owner_only": True,
    }


def inspect_runtime_member_observation(
    path: Path,
    *,
    type_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_member_observation(
        path,
        type_observation_path=type_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_MEMBER_OBSERVATION_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contract": model["contract"],
        "type_count": model["type_count"],
        "counts": model["counts"],
        "identity": model["identity"],
        "raw_runtime_member_objects_exposed": False,
    }


import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError
from alpha.p02 import runtime_inventory_contract
from alpha.p03 import load_runtime_inventory_observation
from alpha.h02 import file_identity, sha256_file


RUNTIME_TYPE_IDENTITY_SCHEMA = "alpha.runtime-type-identity-observation/v1"
RUNTIME_TYPE_IDENTITY_MAGIC = b"ALPHATI1"
RUNTIME_TYPE_IDENTITY_VERSION = 1
RUNTIME_TYPE_IDENTITY_HEADER = struct.Struct("<8sIIII64s64s64sQQ")
RUNTIME_TYPE_IDENTITY_ASSEMBLY = struct.Struct("<I")
RUNTIME_TYPE_IDENTITY_ENTRY = struct.Struct("<IIIIQQQQII")
TYPE_SHAPE_ENUM = 1 << 0
TYPE_SHAPE_VALUE_TYPE = 1 << 1
TYPE_SHAPE_GENERIC = 1 << 2
TYPE_SHAPE_GENERIC_DEFINITION = 1 << 3
TYPE_SHAPE_BYREF = 1 << 4
TYPE_SHAPE_INTERFACE = 1 << 5
TYPE_SHAPE_MASK = (1 << 6) - 1
MAXIMUM_IDENTITY_STRING_BYTES = 16_384
MAXIMUM_TYPE_RELATIONS = 65_536
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _digest(value: bytes, *, label: str) -> str:
    try:
        result = value.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(f"runtime type identity {label} is invalid") from error
    if not _SHA256.fullmatch(result):
        raise AcquisitionError(f"runtime type identity {label} is invalid")
    return result


def _text(data: bytes, *, label: str, allow_empty: bool = False) -> str:
    try:
        value = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise AcquisitionError(f"runtime type identity {label} is invalid") from error
    if (
        (not value and not allow_empty)
        or any(ord(character) < 0x20 for character in value)
    ):
        raise AcquisitionError(f"runtime type identity {label} is invalid")
    return value


def load_runtime_type_identity_observation(
    path: Path,
    *,
    type_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    type_observation_path = type_observation_path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime type identity observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError(
            "runtime type identity observation is not owner-only"
        )
    roots = load_runtime_inventory_observation(
        type_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    try:
        data = path.read_bytes()
    except OSError as error:
        raise AcquisitionError(
            "runtime type identity observation is unreadable"
        ) from error
    if len(data) < RUNTIME_TYPE_IDENTITY_HEADER.size:
        raise AcquisitionError("runtime type identity observation is truncated")
    (
        magic,
        version,
        header_bytes,
        pointer_bytes,
        reserved,
        executable_raw,
        contract_raw,
        roots_raw,
        assembly_count,
        type_count,
    ) = RUNTIME_TYPE_IDENTITY_HEADER.unpack_from(data)
    executable_sha256 = _digest(executable_raw, label="target digest")
    contract_sha256 = _digest(contract_raw, label="contract digest")
    roots_sha256 = _digest(roots_raw, label="type-root digest")
    contract = runtime_inventory_contract()
    if (
        magic != RUNTIME_TYPE_IDENTITY_MAGIC
        or version != RUNTIME_TYPE_IDENTITY_VERSION
        or header_bytes != RUNTIME_TYPE_IDENTITY_HEADER.size
        or pointer_bytes != 8
        or reserved != 0
        or contract_sha256 != contract["contract_id"].rsplit(":", 1)[-1]
        or roots_sha256 != sha256_file(type_observation_path)
        or executable_sha256 != roots["target"]["executable_sha256"]
        or assembly_count != roots["assembly_count"]
        or type_count != roots["type_count"]
    ):
        raise AcquisitionError("runtime type identity header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime type identity target binding is stale")

    position = header_bytes
    assemblies: list[dict[str, Any]] = []
    for assembly_index in range(assembly_count):
        end = position + RUNTIME_TYPE_IDENTITY_ASSEMBLY.size
        if end > len(data):
            raise AcquisitionError("runtime type identity is truncated")
        (length,) = RUNTIME_TYPE_IDENTITY_ASSEMBLY.unpack_from(data, position)
        position = end
        if not 0 < length <= MAXIMUM_IDENTITY_STRING_BYTES:
            raise AcquisitionError("runtime assembly identity length is invalid")
        end = position + length
        if end > len(data):
            raise AcquisitionError("runtime assembly identity is truncated")
        assemblies.append(
            {
                "assembly_index": assembly_index,
                "full_name": _text(
                    data[position:end], label="assembly full name"
                ),
            }
        )
        position = end
    if len({record["full_name"] for record in assemblies}) != assembly_count:
        raise AcquisitionError("runtime assembly identities are not unique")

    root_objects = [
        pointer
        for assembly in roots["assemblies"]
        for pointer in assembly["type_objects"]
    ]
    root_set = set(root_objects)
    records: list[dict[str, Any]] = []
    qualified_names: set[tuple[int, str, str, int]] = set()
    assembly_index = 0
    next_assembly_boundary = roots["assemblies"][0]["type_count"]
    for type_index in range(type_count):
        while type_index >= next_assembly_boundary and assembly_index + 1 < assembly_count:
            assembly_index += 1
            next_assembly_boundary += roots["assemblies"][assembly_index][
                "type_count"
            ]
        end = position + RUNTIME_TYPE_IDENTITY_ENTRY.size
        if end > len(data):
            raise AcquisitionError("runtime type identity is truncated")
        (
            name_bytes,
            namespace_bytes,
            attributes,
            shape,
            base_type,
            declaring_type,
            element_type,
            generic_definition,
            interface_count,
            generic_argument_count,
        ) = RUNTIME_TYPE_IDENTITY_ENTRY.unpack_from(data, position)
        position = end
        if (
            not 0 < name_bytes <= MAXIMUM_IDENTITY_STRING_BYTES
            or namespace_bytes > MAXIMUM_IDENTITY_STRING_BYTES
            or shape & ~TYPE_SHAPE_MASK
            or (shape & TYPE_SHAPE_GENERIC_DEFINITION and not shape & TYPE_SHAPE_GENERIC)
            or interface_count > MAXIMUM_TYPE_RELATIONS
            or generic_argument_count > MAXIMUM_TYPE_RELATIONS
        ):
            raise AcquisitionError("runtime type identity record is invalid")
        string_end = position + name_bytes + namespace_bytes
        relation_count = interface_count + generic_argument_count
        relation_end = string_end + relation_count * pointer_bytes
        if relation_end > len(data):
            raise AcquisitionError("runtime type identity record is truncated")
        name = _text(data[position : position + name_bytes], label="type name")
        position += name_bytes
        namespace = _text(
            data[position : position + namespace_bytes],
            label="type namespace",
            allow_empty=True,
        )
        position += namespace_bytes
        relations = (
            struct.unpack_from(f"<{relation_count}Q", data, position)
            if relation_count
            else ()
        )
        position = relation_end
        references = (
            base_type,
            declaring_type,
            element_type,
            generic_definition,
            *relations,
        )
        if any(reference and reference & 7 for reference in references):
            raise AcquisitionError("runtime type reference pointer is invalid")
        if declaring_type and declaring_type not in root_set:
            raise AcquisitionError("runtime declaring type is absent from roots")
        identity = (assembly_index, namespace, name, declaring_type)
        if identity in qualified_names:
            raise AcquisitionError("runtime root type identities are not unique")
        qualified_names.add(identity)
        records.append(
            {
                "type_index": type_index,
                "assembly_index": assembly_index,
                "type_object": root_objects[type_index],
                "name": name,
                "namespace": namespace,
                "attributes": attributes,
                "shape": shape,
                "base_type": base_type or None,
                "declaring_type": declaring_type or None,
                "element_type": element_type or None,
                "generic_definition": generic_definition or None,
                "interfaces": list(relations[:interface_count]),
                "generic_arguments": list(relations[interface_count:]),
            }
        )
    if position != len(data):
        raise AcquisitionError("runtime type identity has a trailer")
    return {
        "schema": RUNTIME_TYPE_IDENTITY_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contract": {
            "contract_id": contract["contract_id"],
            "type_observation_sha256": roots_sha256,
        },
        "assembly_count": assembly_count,
        "type_count": type_count,
        "relation_count": sum(
            len(record["interfaces"]) + len(record["generic_arguments"])
            for record in records
        ),
        "assemblies": assemblies,
        "types": records,
        "identity": file_identity(path),
        "raw_runtime_type_references_owner_only": True,
    }


def inspect_runtime_type_identity_observation(
    path: Path,
    *,
    type_observation_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_type_identity_observation(
        path,
        type_observation_path=type_observation_path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_TYPE_IDENTITY_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contract": model["contract"],
        "assembly_count": model["assembly_count"],
        "type_count": model["type_count"],
        "relation_count": model["relation_count"],
        "assembly_full_names": [
            assembly["full_name"] for assembly in model["assemblies"]
        ],
        "identity": model["identity"],
        "raw_runtime_type_references_exposed": False,
    }
