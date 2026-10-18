import re
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_path_bits
from alpha.p02 import runtime_inventory_contract
from alpha.h02 import file_identity


RUNTIME_INVENTORY_OBSERVATION_SCHEMA = (
    "alpha.runtime-inventory-observation/v1"
)
RUNTIME_INVENTORY_OBSERVATION_MAGIC = b"ALPHAIO1"
RUNTIME_INVENTORY_OBSERVATION_VERSION = 1
RUNTIME_INVENTORY_OBSERVATION_HEADER = struct.Struct(
    "<8sIIII64s64sQQ"
)
RUNTIME_INVENTORY_OBSERVATION_ENTRY = struct.Struct("<II")
MAXIMUM_ASSEMBLY_COUNT = 4096
MAXIMUM_TYPE_COUNT = 2_000_000
_SHA256 = re.compile(r"^[0-9a-f]{64}$")


def _contract_digest() -> str:
    contract_id = runtime_inventory_contract()["contract_id"]
    prefix = "runtime-inventory-contract:sha256:"
    if not contract_id.startswith(prefix):
        raise AcquisitionError("runtime inventory contract id is invalid")
    digest = contract_id.removeprefix(prefix)
    if not _SHA256.fullmatch(digest):
        raise AcquisitionError("runtime inventory contract digest is invalid")
    return digest


def _decode_digest(value: bytes, *, label: str) -> str:
    try:
        digest = value.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime inventory observation {label} is invalid"
        ) from error
    if not _SHA256.fullmatch(digest):
        raise AcquisitionError(
            f"runtime inventory observation {label} is invalid"
        )
    return digest


def load_runtime_inventory_observation(
    path: Path,
    *,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime inventory observation is unavailable")
    if owner_only_path_bits(path):
        raise AcquisitionError("runtime inventory observation is not owner-only")
    try:
        data = path.read_bytes()
    except OSError as error:
        raise AcquisitionError(
            "runtime inventory observation is unreadable"
        ) from error
    if len(data) < RUNTIME_INVENTORY_OBSERVATION_HEADER.size:
        raise AcquisitionError("runtime inventory observation is truncated")
    (
        magic,
        version,
        header_bytes,
        pointer_bytes,
        reserved,
        executable_raw,
        contract_raw,
        assembly_count,
        type_count,
    ) = RUNTIME_INVENTORY_OBSERVATION_HEADER.unpack_from(data)
    executable_sha256 = _decode_digest(executable_raw, label="target digest")
    contract_sha256 = _decode_digest(contract_raw, label="contract digest")
    if (
        magic != RUNTIME_INVENTORY_OBSERVATION_MAGIC
        or version != RUNTIME_INVENTORY_OBSERVATION_VERSION
        or header_bytes != RUNTIME_INVENTORY_OBSERVATION_HEADER.size
        or pointer_bytes != 8
        or reserved != 0
        or contract_sha256 != _contract_digest()
        or not 0 < assembly_count <= MAXIMUM_ASSEMBLY_COUNT
        or not 0 < type_count <= MAXIMUM_TYPE_COUNT
    ):
        raise AcquisitionError("runtime inventory observation header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime inventory observation target binding is stale")

    position = header_bytes
    assemblies: list[dict[str, Any]] = []
    observed_type_count = 0
    observed_type_objects: set[int] = set()
    for expected_index in range(assembly_count):
        end = position + RUNTIME_INVENTORY_OBSERVATION_ENTRY.size
        if end > len(data):
            raise AcquisitionError("runtime inventory observation is truncated")
        assembly_index, assembly_type_count = (
            RUNTIME_INVENTORY_OBSERVATION_ENTRY.unpack_from(data, position)
        )
        position = end
        if assembly_index != expected_index:
            raise AcquisitionError(
                "runtime inventory assembly indexes are not contiguous"
            )
        if assembly_type_count > MAXIMUM_TYPE_COUNT - observed_type_count:
            raise AcquisitionError("runtime inventory type count is invalid")
        byte_count = assembly_type_count * pointer_bytes
        end = position + byte_count
        if end > len(data):
            raise AcquisitionError("runtime inventory observation is truncated")
        type_objects = (
            struct.unpack_from(f"<{assembly_type_count}Q", data, position)
            if assembly_type_count
            else ()
        )
        if any(
            not pointer or pointer & (pointer_bytes - 1)
            for pointer in type_objects
        ):
            raise AcquisitionError(
                "runtime inventory type object pointer is invalid"
            )
        if (
            len(set(type_objects)) != len(type_objects)
            or observed_type_objects.intersection(type_objects)
        ):
            raise AcquisitionError(
                "runtime inventory type objects are not globally unique"
            )
        observed_type_objects.update(type_objects)
        observed_type_count += assembly_type_count
        assemblies.append(
            {
                "assembly_index": assembly_index,
                "type_count": assembly_type_count,
                "type_objects": list(type_objects),
            }
        )
        position = end
    if position != len(data) or observed_type_count != type_count:
        raise AcquisitionError(
            "runtime inventory observation totals or trailer are invalid"
        )
    return {
        "schema": RUNTIME_INVENTORY_OBSERVATION_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "contract": {
            "contract_id": runtime_inventory_contract()["contract_id"],
            "all_inventory_roots_observed_on_managed_thread": True,
        },
        "assembly_count": assembly_count,
        "type_count": type_count,
        "assemblies": assemblies,
        "identity": file_identity(path),
        "raw_runtime_type_objects_owner_only": True,
    }


def inspect_runtime_inventory_observation(
    path: Path,
    *,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_inventory_observation(
        path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_INVENTORY_OBSERVATION_SCHEMA,
        "status": model["status"],
        "target": model["target"],
        "contract": model["contract"],
        "assembly_count": model["assembly_count"],
        "type_count": model["type_count"],
        "assembly_type_counts": [
            record["type_count"] for record in model["assemblies"]
        ],
        "identity": model["identity"],
        "raw_runtime_type_objects_exposed": False,
    }


from dataclasses import dataclass
import re

from alpha.h01 import AcquisitionError
from alpha.c01 import decode_x64
from alpha.c02 import _ALIASES, _REGS


SELF = ("affine", 1, 0, 0)
INDEX = ("affine", 0, 1, 0)
_NONVOLATILE = ("rbx", "rsi", "rdi", "rbp", "r12", "r13", "r14", "r15")
_MEMORY = re.compile(r"(?:(BYTE|WORD|DWORD|QWORD) PTR )?\[([^\]]+)\]")
_WIDTHS = {"BYTE": 1, "WORD": 2, "DWORD": 4, "QWORD": 8}


def _register(operand, registers):
    alias = _ALIASES.get(operand)
    if alias is None:
        return None
    full, width = alias
    value = registers.get(full)
    if value == ("index32",):
        return INDEX if width == 4 else None
    if width == 8:
        return value
    if width == 4 and (value == INDEX or value and value[0] == "load" and value[2] <= 4):
        return value
    return None


def _address(operand, registers):
    match = _MEMORY.fullmatch(operand)
    if match is None:
        return None, None
    result = [0, 0, 0]

    text = match[2].replace("-", "+-")
    for term in text.split("+"):
        if not term:
            continue
        pieces = term.split("*")
        value = _register(pieces[0], registers)
        if value is not None and value[0] == "affine":
            if len(pieces) > 2:
                return None, None
            try:
                scale = int(pieces[1], 0) if len(pieces) == 2 else 1
            except ValueError:
                return None, None
            for index in range(3):
                result[index] += value[index + 1] * scale
        elif len(pieces) == 1:
            try:
                result[2] += int(term, 0)
            except ValueError:
                return None, None
        else:
            return None, None
    return ("affine", *result), _WIDTHS.get(match[1])


def _operand(operand, registers, instruction):
    if operand in _ALIASES:
        return _register(operand, registers)
    address, width = _address(operand, registers)
    return ("load", address, width, instruction) if address is not None and width else None


def _length(value):
    return bool(value and value[0] == "load" and value[1][:3] == ("affine", 1, 0)
                and value[1][3] >= 0 and value[2] == 4)


@dataclass(frozen=True, order=True)
class LengthCandidate:
    length_offset: int
    length_width: int
    load_instruction: int
    return_instruction: int


@dataclass(frozen=True, order=True)
class IndexerCandidate:
    length_offset: int
    length_width: int
    data_offset: int
    element_width: int
    index_scale: int
    bound_instruction: int
    load_instruction: int
    return_instruction: int


def analyze_string_layout_candidates(instructions):
    by_offset = {offset: index for index, (offset, _) in enumerate(instructions)}
    registers = dict.fromkeys(_REGS)
    registers.update({reg: ("preserved", reg) for reg in _NONVOLATILE})
    registers.update(rcx=SELF, rdx=("index32",), rsp=("stack", 0))
    registers["$saved_stack"] = ()
    pending = [(0, registers, None, (), False)]
    seen, lengths, indexers = set(), set(), set()
    while pending:
        index, registers, comparison, bounds, nonnegative = pending.pop()
        if not 0 <= index < len(instructions):
            continue
        key = (index, tuple(registers.items()), comparison, bounds, nonnegative)
        if key in seen:
            continue
        seen.add(key)
        if len(seen) > max(1024, len(instructions) * 256):
            raise AcquisitionError("string layout candidate analysis exceeded control-flow bound")
        offset, instruction = instructions[index]
        parts = instruction.split(None, 1)
        operation = parts[0]
        operands = tuple(item.strip() for item in parts[1].split(",")) if len(parts) == 2 else ()
        if operation.startswith("ret"):
            if (operation != "ret" or operands or registers["rsp"] != ("stack", 0) or
                any(registers[reg] != ("preserved", reg) for reg in _NONVOLATILE)):
                continue
            value = registers["rax"]
            if _length(value):
                lengths.add(LengthCandidate(value[1][3], value[2], value[3], offset))
            if (value and value[0] == "load" and value[1][:3] == ("affine", 1, 2)
                and value[1][3] >= 0 and value[2] == 2):
                for length, branch in bounds:
                    if value[1][3] >= length[1][3] + length[2]:
                        indexers.add(IndexerCandidate(length[1][3], length[2], value[1][3],
                                                      value[2], 2, branch, value[3], offset))
            continue
        if operation.startswith("j"):
            try:
                target = by_offset.get(int(operands[0], 0))
            except (ValueError, IndexError):
                target = None
            fallthrough, taken = bounds, bounds
            fall_nonnegative, taken_nonnegative = nonnegative, nonnegative
            if comparison is not None:
                left, right = comparison
                if comparison == ("index-sign", INDEX):
                    if operation == "js":
                        fall_nonnegative = True
                    elif operation == "jns":
                        taken_nonnegative = True
                if left == INDEX and _length(right):
                    if operation in ("jae", "jnb", "jnc") or nonnegative and operation in ("jge", "jnl"):
                        fallthrough = (*bounds, (right, offset))
                    elif operation in ("jb", "jc", "jnae") or nonnegative and operation in ("jl", "jnge"):
                        taken = (*bounds, (right, offset))
                if right == INDEX and _length(left):
                    if operation in ("jbe", "jna") or nonnegative and operation in ("jle", "jng"):
                        fallthrough = (*bounds, (left, offset))
                    elif operation in ("ja", "jnbe") or nonnegative and operation in ("jg", "jnle"):
                        taken = (*bounds, (left, offset))
            if operation != "jmp":
                pending.append((index + 1, dict(registers), comparison, fallthrough, fall_nonnegative))
            if target is not None:
                pending.append((target, dict(registers), comparison, taken, taken_nonnegative))
            continue
        if operation == "cmp" and len(operands) == 2:
            comparison = tuple(_operand(operand, registers, offset) for operand in operands)
        elif operation in ("mov", "movzx", "movsxd", "lea") and len(operands) == 2:
            destination, source = operands
            if destination not in _ALIASES:

                continue
            full, width = _ALIASES[destination]
            if full == "rsp":
                continue
            value = None
            if operation == "lea" and width == 8:
                value, _ = _address(source, registers)
            elif operation == "movsxd" and width == 8 and source in _ALIASES and _ALIASES[source][1] == 4:
                candidate = _register(source, registers)
                if candidate == INDEX:
                    value = INDEX
            else:
                candidate = _operand(source, registers, offset)
                if source in _ALIASES and operation == "mov" and _ALIASES[source][1] == width and width >= 4:
                    value = candidate
                elif candidate and candidate[0] == "load":
                    if (operation == "mov" and width == candidate[2] and width >= 4 or
                        operation == "movzx" and width >= 4 and candidate[2] < width):
                        value = candidate
            registers[full] = value
        elif operation in ("nop", "nopl", "nopw", "endbr64"):
            pass
        elif operation == "push" and len(operands) == 1 and operands[0] in _REGS:
            stack = registers["rsp"]
            if operands[0] == "rsp" or not stack or stack[0] != "stack" or stack[1] < -4088:
                continue
            saved = dict(registers["$saved_stack"])
            saved[stack[1] - 8] = registers[operands[0]]
            registers["$saved_stack"] = tuple(sorted(saved.items()))
            registers["rsp"] = ("stack", stack[1] - 8)
        elif operation == "pop" and len(operands) == 1 and operands[0] in _REGS:
            stack = registers["rsp"]
            if operands[0] == "rsp" or not stack or stack[0] != "stack" or stack[1] >= 0:
                continue
            saved = dict(registers["$saved_stack"])
            registers[operands[0]] = saved.pop(stack[1], None)
            registers["$saved_stack"] = tuple(sorted(saved.items()))
            registers["rsp"] = ("stack", stack[1] + 8)
        elif operation in ("add", "sub") and len(operands) == 2 and operands[0] == "rsp":
            try:
                displacement = int(operands[1], 0) * (1 if operation == "add" else -1)
            except ValueError:
                continue
            stack = registers["rsp"]
            if not stack or stack[0] != "stack" or not -4096 <= stack[1] + displacement <= 0:
                continue


            position = stack[1] + displacement
            registers["$saved_stack"] = tuple((where, value) for where, value in registers["$saved_stack"]
                                             if where >= position)
            registers["rsp"] = ("stack", position)
            comparison = None
        elif operation == "test":
            comparison = (("index-sign", INDEX) if len(operands) == 2 and
                          operands[0] == operands[1] and _register(operands[0], registers) == INDEX
                          else None)
        else:


            continue
        pending.append((index + 1, dict(registers), comparison, bounds, nonnegative))
    return tuple(sorted(lengths)), tuple(sorted(indexers))


def discover_string_layout_candidates(code):
    return analyze_string_layout_candidates(decode_x64(code))
