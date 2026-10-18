import re

from alpha.h01 import AcquisitionError
from alpha.c01 import decode_x64
from alpha.c02 import _ALIASES, _REGS
from alpha.c03 import _nop


def prove(code, decoded=None):
    if not isinstance(code, bytes) or not 0 < len(code) <= 1_048_576:
        raise AcquisitionError("receiver qword code resource bound differs")
    rows = decode_x64(code) if decoded is None else decoded; instructions = dict(rows)
    following = {rows[i][0]: rows[i+1][0] for i in range(len(rows)-1)}
    token = lambda name: tuple((name, i) for i in range(8))
    receiver, field = token("receiver"), token("field")
    regs = {r: token("entry-" + r) for r in _REGS}; regs["rcx"] = receiver
    nonvolatile = ("rbx", "rbp", "rsi", "rdi", "r12", "r13", "r14", "r15", "rsp")
    preserved = {r: regs[r] for r in nonvolatile}
    stack, sp, visited, offsets = {}, 0, [], set()
    zf, pc = None, 0

    def fail(reason):
        raise AcquisitionError("receiver qword " + reason)

    def reg(name):
        if name not in _ALIASES: fail("register is unsupported")
        full, width = _ALIASES[name]
        return regs[full][:width]

    def assign(name, value):
        if name not in _ALIASES or _ALIASES[name][0] == "rsp": fail("destination is unsupported or native memory")
        full, width = _ALIASES[name]
        if len(value) != width: fail("assignment width differs")
        regs[full] = value + ((0,) * 4 if width == 4 else regs[full][width:])

    while True:
        if pc not in instructions or pc in visited: fail("control flow is not bounded and loop-free")
        visited.append(pc); text = instructions[pc]; parts = text.split(None, 1)
        op = parts[0]; args = tuple(a.strip() for a in parts[1].split(",")) if len(parts) == 2 else ()
        next_pc = following.get(pc)
        if _nop(text): pass
        elif op in ("push", "pop") and len(args) == 1:
            if args[0] not in nonvolatile or args[0] == "rsp": fail("stack save operand differs")
            if op == "push":
                sp -= 8
                if sp < -4096 or sp in stack: fail("stack save bound differs")
                stack[sp] = reg(args[0])
            else:
                if sp not in stack: fail("stack restore is absent")
                assign(args[0], stack.pop(sp)); sp += 8
        elif op in ("sub", "add") and len(args) == 2 and args[0] == "rsp":
            if not re.fullmatch(r"(?:0x[0-9a-f]+|[0-9]+)", args[1]): fail("stack adjustment is not immediate")
            delta = int(args[1], 0); updated = sp + (delta if op == "add" else -delta)
            if delta <= 0 or delta & 7 or not -4096 <= updated <= 0: fail("stack adjustment bound differs")
            if updated > sp and any(sp <= address < updated for address in stack): fail("stack adjustment discards a save")
            sp = updated; zf = None
        elif op == "mov" and len(args) == 2:
            if args[1] in _ALIASES:
                value = reg(args[1])
            else:
                match = re.fullmatch(r"QWORD PTR \[(r\w+)(?:\+(0x[0-9a-f]+))?\]", args[1])
                if match is None or reg(match[1]) != receiver: fail("native load is not receiver-relative qword")
                offset = int(match[2], 16) if match[2] else 0
                offsets.add(offset)
                if len(offsets) != 1: fail("reads multiple receiver fields")
                value = field
            assign(args[0], value)
        elif op == "test" and len(args) == 2 and reg(args[0]) == reg(args[1]) == receiver:
            zf = False
        elif op in ("je", "jne", "jmp") and len(args) == 1:
            if not re.fullmatch(r"0x[0-9a-f]+", args[0]): fail("branch is not direct")
            if op != "jmp" and zf is None: fail("branch depends on unknown flags")
            if op == "jmp" or (zf if op == "je" else not zf): next_pc = int(args[0], 0)
        elif op == "ret" and not args:
            if (regs["rax"] != field or len(offsets) != 1 or stack or sp
                    or any(regs[r] != v for r, v in preserved.items())):
                fail("returned qword or Win64 ABI differs")
            return dict(receiver_qword_offset=next(iter(offsets)), output_width=8,
                visited_instruction_offsets=visited, arbitrary_field_value_allowed=True,
                required_receiver_nonnull=True, required_receiver_qword_readable=True,
                arbitrary_other_entry_registers_allowed=True, native_pointer_values_opaque=True,
                preserved_win64_registers_proven=True, native_memory_writes=False,
                computation_proven=True, semantic_identity_proven=False, null_paths_proven=False,
                metadata_complete=False)
        else:
            fail("instruction is unsupported: " + text)
        regs["rsp"] = preserved["rsp"] if sp == 0 else token(("private-stack", sp))
        pc = next_pc
