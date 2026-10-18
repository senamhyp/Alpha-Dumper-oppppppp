from dataclasses import dataclass
from typing import Iterable, Mapping

from capstone import CS_ARCH_X86, CS_MODE_64, Cs
from capstone.x86 import X86_OP_IMM, X86_OP_MEM, X86_REG_RIP


@dataclass(frozen=True)
class FunctionReferences:
    calls: frozenset[int]
    slots: frozenset[int]
    instruction_count: int
    indirect_transfer_count: int


def scan_function_references(
    sections: Iterable[tuple[int, bytes]], ranges: Iterable[tuple[int, int]],
) -> dict[int, FunctionReferences]:
    sections = sorted(sections)
    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    decoder.detail = True
    result = {}
    for begin, end in ranges:
        data = next((raw[begin - base:end - base] for base, raw in sections
                     if base <= begin < end <= base + len(raw)), b"")
        if len(data) != end - begin or not data:
            continue
        pending = [begin]
        decoded = {}
        occupied = set()
        calls, slots = set(), set()
        indirect_transfers = 0
        valid = True
        while pending and valid:
            address = pending.pop()
            if address in decoded:
                continue
            if address in occupied or not begin <= address < end:
                valid = False
                break
            for instruction in decoder.disasm(data[address - begin:], address):
                address = instruction.address
                if address in decoded:
                    break
                byte_range = range(address, address + instruction.size)
                if any(byte in occupied for byte in byte_range):
                    valid = False
                    break
                decoded[address] = instruction.size
                occupied.update(byte_range)
                operands = instruction.operands
                for operand in operands:
                    if operand.type == X86_OP_MEM and operand.mem.base == X86_REG_RIP:
                        slots.add(address + instruction.size + operand.mem.disp)
                mnemonic = instruction.mnemonic
                direct = bool(operands and operands[0].type == X86_OP_IMM)
                target = operands[0].imm if direct else None
                if mnemonic == "call" and direct:
                    calls.add(target)
                if mnemonic in {"call", "jmp"} and not direct:
                    indirect_transfers += 1
                if mnemonic.startswith("ret") or mnemonic in {"int3", "ud2", "hlt"}:
                    break
                if mnemonic.startswith("j") or mnemonic.startswith("loop"):
                    if direct and begin <= target < end:
                        pending.append(target)
                    elif mnemonic == "jmp" and direct:
                        calls.add(target)
                    elif mnemonic != "jmp":

                        valid = False
                    if mnemonic == "jmp":
                        break
                address += instruction.size
            else:

                if address != end:
                    valid = False
        if valid:
            result[begin] = FunctionReferences(
                frozenset(calls), frozenset(slots), len(decoded), indirect_transfers,
            )
    return result


def directed_packet_candidates(
    graph: Mapping[int, set[int]], seeds: Mapping[int, set[int]],
    *, boundaries: Iterable[int] = (),
) -> dict[int, set[int]]:
    from collections import defaultdict, deque

    reverse = defaultdict(set)
    for caller, callees in graph.items():
        for callee in callees:
            reverse[callee].add(caller)
    result = {node: set(values) for node, values in seeds.items() if values}
    boundaries = set(boundaries)
    queue = deque(result)
    queued = set(result)
    while queue:
        node = queue.popleft()
        queued.remove(node)
        for caller in reverse.get(node, ()):
            if caller in boundaries:
                continue
            values = result.setdefault(caller, set())
            extra = result[node] - values
            if extra:
                values.update(extra)
                if caller not in queued:
                    queue.append(caller)
                    queued.add(caller)
    return result
