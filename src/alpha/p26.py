from alpha.h02 import windows_run as _host_run

import json
import os
import re
import stat
import struct
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import (
    AcquisitionError,
    owner_only_path_bits,
    owner_uid,
    same_executable_path,
)
from alpha.p14 import current_capture_scope, assert_current_capture_alive
from alpha.p13 import _safe_path
from alpha.p02 import bound_creation, protect_source
from alpha.c04 import _verify_files
from alpha.p16 import REFLECTION_SEMANTICS_SCHEMA
from alpha.p22 import METHOD_DETAIL_CONSTRUCTOR, RUNTIME_METHOD_DETAIL_HEADER, RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_METHOD, RUNTIME_METHOD_DETAIL_SCHEMA, RUNTIME_METHOD_DETAIL_VERSION
from alpha.c04 import MappedPE
from alpha.p20 import load_runtime_metadata_usage_member_inventory
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA, _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_RECORD, RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION, TYPE_REFERENCE_ARRAY
from alpha.h02 import file_identity, read_json


RUNTIME_METHOD_GENERIC_PLAN_SCHEMA = (
    "alpha.runtime-method-generic-inventory-plan/v1"
)
RUNTIME_METHOD_GENERIC_STATUS_SCHEMA = (
    "alpha.runtime-method-generic-inventory-status/v1"
)
RUNTIME_METHOD_GENERIC_SCHEMA = "alpha.runtime-method-generic-inventory/v1"
RUNTIME_METHOD_GENERIC_MAGIC = b"ALPHAMG1"
RUNTIME_METHOD_GENERIC_VERSION = 1
RUNTIME_METHOD_GENERIC_HEADER = struct.Struct(
    "<8sIIIIQQQQQQ64s64s64s64s64s64s"
)
RUNTIME_METHOD_GENERIC_RECORD = struct.Struct("<IIQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime method generic {label} is not owner-only"
        )
    return path


def _digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime method generic {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime method generic {label} digest is invalid"
        )
    return value


def _text(raw: bytes, offset: int, length: int, *, label: str) -> str:
    if not length or offset < 0 or offset + length > len(raw):
        raise AcquisitionError(
            f"runtime method generic {label} is out of range"
        )
    chunk = raw[offset : offset + length]
    try:
        value = chunk.decode("utf-8")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime method generic {label} is invalid"
        ) from error


    if not value or min(chunk) < 0x20:
        raise AcquisitionError(
            f"runtime method generic {label} is invalid"
        )
    return value


def _validated_model(
    *, model_path: Path, inventory_path: Path, schema: str,
    inventory_key: str, executable_sha256: str | None, label: str,
) -> tuple[Path, Path, dict[str, Any], str]:
    model_path = _owner_file(model_path, label=f"{label} model")
    inventory_path = _owner_file(
        inventory_path, label=f"{label} inventory"
    )
    model = read_json(model_path)
    target = model.get("target", {}).get("executable_sha256")
    if (
        not isinstance(model, dict)
        or model.get("schema") != schema
        or model.get("status") != "runtime-validated"
        or not isinstance(target, str)
        or (executable_sha256 is not None and target != executable_sha256)
        or not model.get("checks")
        or not all(model["checks"].values())
        or model.get(inventory_key, {}).get("sha256")
        != file_identity(inventory_path)["sha256"]
    ):
        raise AcquisitionError(
            f"runtime method generic {label} binding is stale"
        )
    return model_path, inventory_path, model, target


def _identity_names(raw: bytes) -> tuple[list[str], dict[int, int]]:
    header = _IDENTITY_HEADER.unpack_from(raw)
    count = header[5]
    rows_start = _IDENTITY_HEADER.size
    rows_end = rows_start + count * _IDENTITY_RECORD.size
    if rows_end <= len(raw):
        rows = list(
            _IDENTITY_RECORD.iter_unpack(memoryview(raw)[rows_start:rows_end])
        )
    else:
        rows = [
            _IDENTITY_RECORD.unpack_from(
                raw, rows_start + index * _IDENTITY_RECORD.size
            )
            for index in range(count)
        ]
    by_descriptor = {row[2]: index for index, row in enumerate(rows)}
    if len(by_descriptor) != count:
        raise AcquisitionError(
            "runtime method generic identity descriptors repeat"
        )
    cache: dict[int, str] = {}

    def name(index: int) -> str:
        cached = cache.get(index)
        if cached is not None:
            return cached
        row = rows[index]
        simple = _text(raw, row[11], row[8], label="type name")
        namespace = (
            _text(raw, row[12], row[9], label="type namespace")
            if row[9]
            else ""
        )
        if row[5]:
            owner = by_descriptor.get(row[5])
            if owner is None:
                raise AcquisitionError(
                    "runtime method generic nested owner is absent"
                )
            prefix = name(owner)
        else:
            prefix = namespace
        value = f"{prefix}.{simple}" if prefix else simple
        cache[index] = value
        return value

    return [name(index) for index in range(count)], by_descriptor


def _select_generic_arguments_candidate(
    *, identity: bytes, methods: bytes, references: bytes,
) -> dict[str, int]:
    names, root_by_descriptor = _identity_names(identity)
    try:
        method_owner = names.index("System.Reflection.MonoMethod")
        runtime_type = names.index("System.RuntimeType")
        type_root = names.index("System.Type")
    except ValueError as error:
        raise AcquisitionError(
            "runtime method generic required owners are absent"
        ) from error
    method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(methods)
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(references)
    reference_count = reference_header[5]
    reference_start = RUNTIME_TYPE_REFERENCE_HEADER.size
    reference_end = (
        reference_start
        + reference_count * RUNTIME_TYPE_REFERENCE_RECORD.size
    )
    if reference_end <= len(references):
        reference_rows = RUNTIME_TYPE_REFERENCE_RECORD.iter_unpack(
            memoryview(references)[reference_start:reference_end]
        )
    else:
        reference_rows = (
            RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
                references,
                reference_start + index * RUNTIME_TYPE_REFERENCE_RECORD.size,
            )
            for index in range(reference_count)
        )
    node_by_descriptor: dict[int, tuple[int, ...]] = {}
    for row in reference_rows:
        if row[0] in node_by_descriptor:
            raise AcquisitionError(
                "runtime method generic reference descriptors repeat"
            )
        node_by_descriptor[row[0]] = row

    def node(pointer: int) -> tuple[int, ...] | None:
        return node_by_descriptor.get(pointer)

    def is_type_root(pointer: int) -> bool:
        row = node(pointer)
        aliases = (pointer, row[1] if row is not None else 0)
        return any(root_by_descriptor.get(alias) == type_root for alias in aliases)

    def returns_type_array(pointer: int) -> bool:
        row = node(pointer)
        return bool(
            row is not None
            and row[4] & TYPE_REFERENCE_ARRAY
            and row[9] == 1
            and row[13]
            and is_type_root(row[13])
        )

    candidates: list[tuple[int, tuple[int, ...]]] = []
    method_start = RUNTIME_METHOD_DETAIL_HEADER.size
    method_count = method_header[5]
    method_end = method_start + method_count * RUNTIME_METHOD_DETAIL_METHOD.size
    if method_end <= len(methods):
        method_rows = enumerate(
            RUNTIME_METHOD_DETAIL_METHOD.iter_unpack(
                memoryview(methods)[method_start:method_end]
            )
        )
    else:
        method_rows = (
            (
                index,
                RUNTIME_METHOD_DETAIL_METHOD.unpack_from(
                    methods,
                    method_start + index * RUNTIME_METHOD_DETAIL_METHOD.size,
                ),
            )
            for index in range(method_count)
        )
    for index, row in method_rows:
        if (
            row[0] == method_owner
            and row[10] == 0
            and not row[9] & METHOD_DETAIL_CONSTRUCTOR
            and row[2]
            and row[3]
            and returns_type_array(row[4])
        ):
            candidates.append((index, row))
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime method generic arguments operation is not unique"
        )
    index, row = candidates[0]


    identity_row_base = _IDENTITY_HEADER.size
    return {
        "method_index": index,
        "pointer": row[3],
        "metadata": row[2],
        "method_class": _IDENTITY_RECORD.unpack_from(
            identity, identity_row_base + method_owner * _IDENTITY_RECORD.size
        )[3],
        "runtime_type_class": _IDENTITY_RECORD.unpack_from(
            identity,
            identity_row_base + runtime_type * _IDENTITY_RECORD.size,
        )[3],
    }


def _derive_method_generic_decoder_v2(
    *, binary: Path, method_pointer: int,
) -> dict[str, int]:
    with MappedPE(binary, require_runtime_functions=False) as image:
        def read(address: int, size: int) -> bytes:
            if not image.image_base <= address < image.image_base + image.size_of_image:
                raise AcquisitionError(
                    "runtime method generic decoder target is outside the image"
                )
            offset = image.rva_to_offset(address - image.image_base)
            if offset is None or offset + size > len(image._mapping):
                raise AcquisitionError(
                    "runtime method generic decoder bytes are unavailable"
                )
            return bytes(image._mapping[offset : offset + size])

        target = method_pointer
        for _ in range(4):
            thunk = read(target, 16)
            if thunk[0] != 0xE9:
                break
            target = target + 5 + struct.unpack_from("<i", thunk, 1)[0]
        code = read(target, 640)
        prefix_match = list(
            re.finditer(
                rb"\x48\x8b\x41(.)\xf6\x40(.)(.)\x74."
                rb"\x48\x8b\x48(.)\x48\x8b\x59(.)\x48\x85\xdb\x74."
                rb"\x8b\x3b",
                code,
                re.DOTALL,
            )
        )
        if len(prefix_match) != 1:
            raise AcquisitionError(
                "runtime method generic structural prefix is not unique"
            )
        prefix = prefix_match[0]
        plain_arguments = list(
            re.finditer(
                rb"\x48\x8b\x43(.)\x48\x8b\x0c\xe8",
                code[prefix.end():],
                re.DOTALL,
            )
        )
        plain_offsets = {found.group(1)[0] for found in plain_arguments}
        if not plain_arguments or len(plain_offsets) != 1:
            raise AcquisitionError(
                "runtime method generic structural plain arguments conflict"
            )
        resolvers = list(
            re.finditer(
                rb"\x8b\x48(.)\xe8(.{4})\x8b\x40(.)"
                rb"\xb9\xff\xff\xff\xff\x48\x39\xc8",
                code,
                re.DOTALL,
            )
        )
        if len(resolvers) != 1:
            raise AcquisitionError(
                "runtime method generic structural definition resolver is not unique"
            )
        resolver = resolvers[0]
        resolver_call = resolver.group(2)
        definition_resolver = (
            target
            + resolver.start(2)
            + len(resolver_call)
            + struct.unpack("<i", resolver_call)[0]
        )
        prefix_fields = {
            "metadata_object_offset": prefix.group(1)[0],
            "flags_offset": prefix.group(2)[0],
            "inflated_mask": prefix.group(3)[0],
            "inflated_context_offset": prefix.group(4)[0],
            "generic_instance_offset": prefix.group(5)[0],
        }
        return _derive_protected_decoder_roles(
            image=image,
            target=target,
            code=code,
            definition_resolver=definition_resolver,
            definition_handle_offset=resolver.group(1)[0],
            protected_index_offset=resolver.group(3)[0],
            prefix_fields=prefix_fields,
            plain_arguments_offset=next(iter(plain_offsets)),
        )


def _derive_protected_decoder_roles(
    *,
    image: Any,
    target: int,
    code: bytes,
    definition_resolver: int,
    definition_handle_offset: int,
    protected_index_offset: int,
    prefix_fields: dict[str, int],
    plain_arguments_offset: int,
) -> dict[str, int]:
    from alpha.p57 import _instruction_stream

    image_base = image.image_base
    instructions = _instruction_stream(
        image, target - image_base, target - image_base + len(code)
    )

    def reg_name(instruction: Any, operand: Any) -> str | None:
        if operand.type != 1:
            return None
        return instruction.reg_name(operand.reg)

    def rip_global(instruction: Any) -> int | None:
        operands = instruction.operands
        if (
            instruction.mnemonic not in ("mov", "movabs")
            or len(operands) != 2
            or operands[0].type != 1
            or operands[1].type != 3
            or operands[1].mem.base != 41
        ):
            return None
        return (
            image_base + instruction.address + instruction.size
            + operands[1].mem.disp
        )

    def imm32(operand: Any) -> int:
        return int(operand.imm) & 0xFFFFFFFF

    def imm64(operand: Any) -> int:
        return int(operand.imm) & 0xFFFFFFFFFFFFFFFF

    def follow_base_name(instruction: Any, operand: Any) -> str | None:
        if operand.type != 3 or operand.mem.base == 0:
            return None
        return instruction.reg_name(operand.mem.base)

    index_register = None
    for instruction in instructions:
        operands = instruction.operands
        if (
            instruction.mnemonic == "mov"
            and len(operands) == 2
            and operands[0].type == 1
            and operands[1].type == 3
            and operands[1].size == 4
            and operands[1].mem.base != 0
            and operands[1].mem.disp == protected_index_offset
        ):
            candidate = reg_name(instruction, operands[0])
            if index_register is None:
                index_register = candidate
            elif index_register != candidate:
                raise AcquisitionError(
                    "runtime method generic protected index register conflicts"
                )
    if index_register is None:
        raise AcquisitionError(
            "runtime method generic protected index register is unavailable"
        )

    chains: list[dict[str, Any]] = []
    for position, instruction in enumerate(instructions):
        operands = instruction.operands

        if (
            instruction.mnemonic != "movsxd"
            or len(operands) != 2
            or operands[0].type != 1
            or operands[1].type != 3
            or operands[1].size != 4
            or operands[1].mem.base == 0
            or operands[1].mem.index != 0
        ):
            continue
        state_register = reg_name(instruction, operands[0])
        if state_register is None:
            continue
        if instruction.reg_name(operands[1].mem.base) != state_register:
            continue
        if position + 2 >= len(instructions):
            continue
        combine = instructions[position + 1]
        if (
            combine.mnemonic not in ("xor", "add")
            or len(combine.operands) != 2
            or combine.operands[0].type != 1
            or combine.operands[1].type != 2
            or reg_name(combine, combine.operands[0]) != state_register
        ):
            continue
        add = instructions[position + 2]
        if (
            add.mnemonic != "add"
            or len(add.operands) != 2
            or add.operands[0].type != 1
            or add.operands[1].type != 1
            or reg_name(add, add.operands[1]) != state_register
        ):
            continue
        base_register = reg_name(add, add.operands[0])
        base_global = state_global = None
        for candidate in reversed(instructions[max(0, position - 12):position]):
            address = rip_global(candidate)
            if address is None:
                continue
            name = reg_name(candidate, candidate.operands[0])
            if name == base_register and base_global is None:
                base_global = address
            if name == state_register and state_global is None:
                state_global = address
        if base_global is None or state_global is None:
            continue
        chains.append(
            {
                "position": position,
                "state_offset": int(operands[1].mem.disp) & 0xFFFFFFFF,
                "disp_xor": (
                    imm32(combine.operands[1])
                    if combine.mnemonic == "xor"
                    else 0
                ),
                "disp_add": (
                    imm32(combine.operands[1])
                    if combine.mnemonic == "add"
                    else 0
                ),
                "base_register": base_register,
                "state_register": state_register,
                "base_global": base_global,
                "state_global": state_global,
            }
        )
    if len(chains) != 1:
        raise AcquisitionError(
            "runtime method generic protected count table is not unique"
        )
    chain = chains[0]
    record_register = None
    record_shift = None
    key_position = None
    for position in range(chain["position"] + 3, len(instructions)):
        instruction = instructions[position]
        operands = instruction.operands
        if (
            instruction.mnemonic != "shl"
            or len(operands) != 2
            or operands[0].type != 1
            or operands[1].type != 2
        ):
            continue
        candidate = reg_name(instruction, operands[0])
        for follow in instructions[position + 1:position + 3]:
            if (
                follow.mnemonic == "add"
                and len(follow.operands) == 2
                and follow.operands[0].type == 1
                and follow.operands[1].type == 1
                and reg_name(follow, follow.operands[0]) == candidate
                and reg_name(follow, follow.operands[1]) == chain["base_register"]
            ):
                record_register = candidate
                record_shift = int(operands[1].imm)
                key_position = position
                break
        if record_register is not None:
            break
    if record_register is None or record_shift is None or key_position is None:
        raise AcquisitionError(
            "runtime method generic protected record stride is unavailable"
        )

    record_key_multiplier = count_key_xor = count_key_multiplier = None
    count_key_add = 0
    count_key_shift = 0
    key_register = None
    key_add_applied = False
    for position in range(key_position + 1, len(instructions)):
        instruction = instructions[position]
        operands = instruction.operands
        if (
            instruction.mnemonic == "imul"
            and len(operands) == 3
            and operands[0].type == 1
            and operands[1].type == 1
            and operands[2].type == 2
        ):
            destination = reg_name(instruction, operands[0])
            source_value = reg_name(instruction, operands[1])
            if record_key_multiplier is None:
                if source_value != index_register or destination != index_register:
                    continue
                record_key_multiplier = imm32(operands[2])
                continue
            if count_key_multiplier is None and count_key_xor is not None:
                if source_value != index_register or destination == index_register:
                    continue
                count_key_multiplier = imm32(operands[2])
                key_register = destination
                continue
        if (
            instruction.mnemonic in ("xor", "add")
            and len(operands) == 2
            and operands[0].type == 1
            and operands[1].type == 2
            and reg_name(instruction, operands[0]) == index_register
            and count_key_xor is None
            and record_key_multiplier is not None
        ):
            count_key_xor = imm32(operands[1])
            continue
        if (
            instruction.mnemonic in ("add", "shr")
            and len(operands) == 2
            and operands[0].type == 1
            and operands[1].type == 2
            and key_register is not None
            and reg_name(instruction, operands[0]) == key_register
            and count_key_multiplier is not None
        ):
            if instruction.mnemonic == "add":
                count_key_add = imm32(operands[1])
                key_add_applied = True
            else:
                count_key_shift = int(operands[1].imm)
            break
    if (
        record_key_multiplier is None
        or count_key_xor is None
        or count_key_multiplier is None
        or key_register is None
    ):
        raise AcquisitionError(
            "runtime method generic protected count key is unavailable"
        )

    count_value_add = None
    count_value_offset = None
    for position in range(key_position, len(instructions)):
        instruction = instructions[position]
        operands = instruction.operands
        if (
            instruction.mnemonic != "mov"
            or len(operands) != 2
            or operands[0].type != 1
            or operands[1].type != 2
        ):
            continue
        value_register = reg_name(instruction, operands[0])
        for follow in instructions[position + 1:position + 3]:
            if (
                follow.mnemonic == "add"
                and len(follow.operands) == 2
                and follow.operands[0].type == 1
                and follow.operands[1].type == 3
                and reg_name(follow, follow.operands[0]) == value_register
                and follow.reg_name(follow.operands[1].mem.base)
                == record_register
            ):
                count_value_add = imm32(operands[1])
                count_value_offset = int(follow.operands[1].mem.disp) & 0xFFFFFFFF
                break
        if count_value_add is not None:
            break
    if count_value_add is None or count_value_offset is None:
        raise AcquisitionError(
            "runtime method generic protected count value is unavailable"
        )

    parameter_state_offset = parameter_table_xor = None
    parameter_table_add = 0
    parameter_table_global = None
    parameter_state_global = None
    rip_registers: dict[str, int] = {}
    for position, instruction in enumerate(instructions):
        operands = instruction.operands
        address = rip_global(instruction)
        if address is not None:
            name = reg_name(instruction, operands[0])
            if name is not None:
                rip_registers[name] = address
        if (
            instruction.mnemonic != "mov"
            or len(operands) != 2
            or operands[0].type != 1
            or operands[1].type != 3
            or operands[1].size != 4
            or operands[1].mem.index != 0
        ):
            continue
        state_base = instruction.reg_name(operands[1].mem.base)
        if state_base not in rip_registers:
            continue
        table_register = reg_name(instruction, operands[0])
        if position + 4 >= len(instructions):
            continue
        mix = instructions[position + 1]
        if (
            mix.mnemonic != "mov"
            or len(mix.operands) != 2
            or mix.operands[0].type != 1
            or mix.operands[1].type != 2
            or reg_name(mix, mix.operands[0]) == table_register
        ):
            continue
        constant_register = reg_name(mix, mix.operands[0])
        combine = instructions[position + 2]
        if (
            combine.mnemonic not in ("add", "xor")
            or len(combine.operands) != 2
            or combine.operands[0].type != 1
            or combine.operands[1].type != 1
            or reg_name(combine, combine.operands[0]) != table_register
            or reg_name(combine, combine.operands[1]) != constant_register
        ):
            continue
        extend = instructions[position + 3]
        if (
            extend.mnemonic != "movsxd"
            or len(extend.operands) != 2
            or extend.operands[0].type != 1
            or extend.operands[1].type != 1
            or reg_name(extend, extend.operands[1]) != table_register
        ):
            continue
        add = instructions[position + 4]
        if (
            add.mnemonic != "add"
            or len(add.operands) != 2
            or add.operands[0].type != 1
            or add.operands[1].type != 3
            or reg_name(add, add.operands[0])
            != reg_name(extend, extend.operands[0])
            or add.operands[1].mem.base != 41
        ):
            continue
        parameter_state_offset = int(operands[1].mem.disp) & 0xFFFFFFFF
        constant = imm32(mix.operands[1])
        if combine.mnemonic == "xor":
            parameter_table_xor = constant
            parameter_table_add = 0
        else:
            parameter_table_xor = 0
            parameter_table_add = constant
        parameter_table_global = (
            image_base + add.address + add.size + add.operands[1].mem.disp
        )
        parameter_state_global = rip_registers[state_base]
        break
    if parameter_state_offset is None or parameter_table_global is None:
        raise AcquisitionError(
            "runtime method generic protected parameter table is unavailable"
        )
    if (
        parameter_state_global != chain["state_global"]
        or parameter_table_global != chain["base_global"]
    ):
        raise AcquisitionError(
            "runtime method generic protected decoder globals conflict"
        )

    parameter_stride = None
    for position, instruction in enumerate(instructions):
        operands = instruction.operands
        if (
            instruction.mnemonic != "shl"
            or len(operands) != 2
            or operands[0].type != 1
            or operands[1].type != 2
        ):
            continue
        candidate = reg_name(instruction, operands[0])
        subs = instructions[position + 1:position + 3]
        if len(subs) != 2:
            continue
        first, second = subs
        if (
            first.mnemonic == "sub"
            and second.mnemonic == "sub"
            and len(first.operands) == 2
            and len(second.operands) == 2
            and first.operands[0].type == 1
            and second.operands[0].type == 1
            and first.operands[1].type == 1
            and second.operands[1].type == 1
            and reg_name(first, first.operands[0]) == candidate
            and reg_name(second, second.operands[0]) == candidate
            and reg_name(first, first.operands[1])
            == reg_name(second, second.operands[1])
        ):
            parameter_stride = (1 << int(operands[1].imm)) - 2
            break
    if not parameter_stride or not 8 <= parameter_stride <= 64:
        raise AcquisitionError(
            "runtime method generic protected parameter stride is unavailable"
        )

    parameter_key_multiplier = parameter_key_add = parameter_key_xor = None
    for position, instruction in enumerate(instructions):
        operands = instruction.operands
        if (
            instruction.mnemonic != "movabs"
            or len(operands) != 2
            or operands[0].type != 1
            or operands[1].type != 2
        ):
            continue
        multiplier_register = reg_name(instruction, operands[0])
        if position + 3 >= len(instructions):
            continue
        multiply = instructions[position + 1]
        if (
            multiply.mnemonic != "imul"
            or len(multiply.operands) != 2
            or multiply.operands[0].type != 1
            or multiply.operands[1].type != 1
            or reg_name(multiply, multiply.operands[1]) != multiplier_register
        ):
            continue
        add = instructions[position + 2]
        if (
            add.mnemonic != "add"
            or len(add.operands) != 2
            or add.operands[0].type != 1
            or add.operands[1].type != 1
            or reg_name(add, add.operands[0])
            != reg_name(multiply, multiply.operands[0])
        ):
            continue
        addend_register = reg_name(add, add.operands[1])
        addend = None
        for candidate in reversed(instructions[max(0, position - 24):position]):
            if (
                candidate.mnemonic == "movabs"
                and len(candidate.operands) == 2
                and candidate.operands[0].type == 1
                and reg_name(candidate, candidate.operands[0])
                == addend_register
            ):
                addend = imm64(candidate.operands[1])
                break
        if addend is None:
            continue
        combine = instructions[position + 3]
        if (
            combine.mnemonic != "xor"
            or len(combine.operands) != 2
            or combine.operands[0].type != 1
            or combine.operands[1].type != 2
            or reg_name(combine, combine.operands[0])
            != reg_name(add, add.operands[0])
        ):
            continue
        parameter_key_multiplier = imm64(operands[1])
        parameter_key_add = addend
        parameter_key_xor = imm32(combine.operands[1])
        break
    if (
        parameter_key_multiplier is None
        or parameter_key_add is None
        or parameter_key_xor is None
    ):
        raise AcquisitionError(
            "runtime method generic protected parameter key is unavailable"
        )

    parameter_source_offset = parameter_source_xor = None
    for position, instruction in enumerate(instructions):
        operands = instruction.operands
        if (
            instruction.mnemonic != "mov"
            or len(operands) != 2
            or operands[0].type != 1
            or operands[1].type != 3
            or operands[1].size != 4
            or follow_base_name(instruction, operands[1]) != record_register
        ):
            continue
        if (int(operands[1].mem.disp) & 0xFFFFFFFF) == count_value_offset:
            continue
        source_register = reg_name(instruction, operands[0])
        if position + 2 >= len(instructions):
            continue
        key_xor = instructions[position + 1]
        constant_xor = instructions[position + 2]
        if (
            key_xor.mnemonic == "xor"
            and len(key_xor.operands) == 2
            and key_xor.operands[0].type == 1
            and key_xor.operands[1].type == 1
            and reg_name(key_xor, key_xor.operands[0]) == source_register
            and reg_name(key_xor, key_xor.operands[1]) == key_register
            and constant_xor.mnemonic == "xor"
            and len(constant_xor.operands) == 2
            and constant_xor.operands[0].type == 1
            and constant_xor.operands[1].type == 2
            and reg_name(constant_xor, constant_xor.operands[0])
            == source_register
        ):
            parameter_source_offset = int(operands[1].mem.disp) & 0xFFFFFFFF
            parameter_source_xor = imm32(constant_xor.operands[1])
            break
    if parameter_source_offset is None or parameter_source_xor is None:
        raise AcquisitionError(
            "runtime method generic protected parameter source is unavailable"
        )

    parameter_helper = descriptor_offset = None
    for position, instruction in enumerate(instructions):
        operands = instruction.operands
        if (
            instruction.mnemonic != "call"
            or len(operands) != 1
            or operands[0].type != 2
        ):
            continue
        if position == 0 or position + 1 >= len(instructions):
            continue
        setup = instructions[position - 1]
        if (
            setup.mnemonic != "mov"
            or len(setup.operands) != 2
            or setup.operands[0].type != 1
            or setup.operands[1].type != 1
            or setup.reg_name(setup.operands[0].reg) != "rcx"
        ):
            continue
        pair_register = reg_name(setup, setup.operands[1])
        pair_ready = False
        for candidate in instructions[max(0, position - 24):position]:
            if (
                candidate.mnemonic == "lea"
                and len(candidate.operands) == 2
                and candidate.operands[0].type == 1
                and candidate.operands[1].type == 3
                and candidate.operands[1].mem.base != 0
                and candidate.reg_name(candidate.operands[1].mem.base) == "rsp"
                and reg_name(candidate, candidate.operands[0]) == pair_register
            ):
                pair_ready = True
                break
        if not pair_ready:
            continue
        follow = instructions[position + 1]
        if (
            follow.mnemonic != "lea"
            or len(follow.operands) != 2
            or follow.operands[0].type != 1
            or follow.operands[1].type != 3
            or follow.reg_name(follow.operands[1].mem.base) != "rax"
        ):
            continue
        parameter_helper = image_base + operands[0].imm
        descriptor_offset = int(follow.operands[1].mem.disp) & 0xFFFFFFFF
        break
    if parameter_helper is None or descriptor_offset is None:
        raise AcquisitionError(
            "runtime method generic protected parameter helper is unavailable"
        )

    if not key_add_applied:
        raise AcquisitionError(
            "runtime method generic protected count key shape is unsupported"
        )
    codec = 4
    return {
        "decoder_codec": codec,
        "function": target,
        "metadata_object_offset": prefix_fields["metadata_object_offset"],
        "flags_offset": prefix_fields["flags_offset"],
        "inflated_mask": prefix_fields["inflated_mask"],
        "inflated_context_offset": prefix_fields["inflated_context_offset"],
        "generic_instance_offset": prefix_fields["generic_instance_offset"],
        "plain_count_offset": 0,
        "plain_arguments_offset": plain_arguments_offset,
        "definition_handle_offset": definition_handle_offset,
        "definition_resolver": definition_resolver,
        "protected_index_offset": protected_index_offset,
        "metadata_base_global": chain["base_global"],
        "metadata_state_global": chain["state_global"],
        "count_base_add": chain["disp_add"],
        "count_table_xor": chain["disp_xor"],
        "count_state_offset": chain["state_offset"],
        "record_key_multiplier": record_key_multiplier,
        "record_shift": record_shift,
        "count_key_xor": count_key_xor,
        "count_key_multiplier": count_key_multiplier,
        "count_key_add": count_key_add,
        "count_key_shift": count_key_shift,
        "count_final_xor": 0,
        "count_value_offset": count_value_offset,
        "count_value_add": count_value_add,
        "parameter_state_offset": parameter_state_offset,
        "parameter_table_xor": parameter_table_xor,
        "parameter_table_add": parameter_table_add,
        "parameter_source_offset": parameter_source_offset,
        "parameter_source_xor": parameter_source_xor,
        "parameter_source_add": 0,
        "parameter_stride": parameter_stride,
        "parameter_key_multiplier": parameter_key_multiplier,
        "parameter_key_add": parameter_key_add,
        "parameter_key_xor": parameter_key_xor,
        "parameter_mix_multiplier": 1,
        "parameter_mix_xor": 0,
        "parameter_final_multiplier": 1,
        "parameter_key_shift": 0,
        "parameter_helper": parameter_helper,
        "descriptor_offset": descriptor_offset,
    }


def _derive_scalar_affine_method_generic(*, target, code, prefix, plain_offset, resolver):
    def unique(pattern):
        matches = list(re.finditer(pattern, code, re.DOTALL))
        if len(matches) != 1:
            raise AcquisitionError("scalar method generic decoder is not unique")
        return matches[0]
    count_table = unique(rb"\x48\x8b\x0d(.{4})\x48\x85\xc9.{0,16}\x48\x8b\x15(.{4})\x48\x63\x52(.)\x48\x81\xf2(.{4})\x48\x01\xd1\x49\x89\xc7\x49\xc1\xe7(.)\x49\x01\xcf")
    count_key = unique(rb"\x44\x69\xe0(.{4})\x41\x81\xc4(.{4})\x41\x8b\x7f(.)\x44\x31\xe7\x81\xf7(.{4})")
    parameter_table = unique(rb"\x48\x8b\x0d(.{4})\x48\x63\x91(.{4})\x48\x81\xf2(.{4})\x48\x03\x15(.{4})")
    parameter_multiplier = unique(rb"\x49\xbd(.{8})")
    parameter_mix = unique(rb"\x48\x89\xc8\x48\xc1\xe0(.)\x48\x29\xc8\x48\x29\xc8\x49\x0f\xaf\xcd\x48\xc1\xe9(.)\x48\x69\xc9(.{4})\x48\xc1\xe9(.)\x48\x81\xc1(.{4})")
    parameter_source = unique(rb"\x41\x8b\x4f(.)\x44\x31\xe1\x81\xf1(.{4})")
    parameter_helper = unique(rb"\x4c\x89\xf1\xe8(.{4})\x48\x8d\x98(.{4})")
    def byte(match, index): return match.group(index)[0]
    def u32(match, index): return struct.unpack('<I', match.group(index))[0]
    def u64(match, index): return struct.unpack('<Q', match.group(index))[0]
    def rip(match, index): return target + match.end(index) + struct.unpack('<i', match.group(index))[0]
    if rip(count_table,1) != rip(parameter_table,4) or rip(count_table,2) != rip(parameter_table,1):
        raise AcquisitionError("scalar method generic globals conflict")
    shift = byte(parameter_mix,1)
    if (not 4 <= shift <= 6 or not 4 <= byte(count_table,5) <= 6
            or byte(parameter_mix,2) >= 64 or byte(parameter_mix,4) >= 64
            or u32(parameter_helper,2) > 4096 or not u32(count_key,1)
            or not u64(parameter_multiplier,1) or not u32(parameter_mix,3)):
        raise AcquisitionError("scalar method generic decoder shape is invalid")
    stride = (1 << shift) - 2
    return {
        "decoder_codec": 5,
        "parameter_table_add": 0,
        "function": target,
        "metadata_object_offset": byte(prefix,1),
        "flags_offset": byte(prefix,2),
        "inflated_mask": byte(prefix,3),
        "inflated_context_offset": byte(prefix,4),
        "generic_instance_offset": byte(prefix,5),
        "plain_count_offset": 0,
        "plain_arguments_offset": plain_offset,
        "definition_handle_offset": byte(resolver,1),
        "definition_resolver": rip(resolver,2),
        "protected_index_offset": byte(resolver,3),
        "metadata_base_global": rip(count_table,1),
        "metadata_state_global": rip(count_table,2),
        "count_base_add": 0,
        "count_table_xor": u32(count_table,4),
        "count_state_offset": byte(count_table,3),
        "record_key_multiplier": u32(count_key,1),
        "record_shift": byte(count_table,5),
        "count_key_xor": 0,
        "count_key_multiplier": 1,
        "count_key_add": u32(count_key,2),
        "count_key_shift": 0,
        "count_final_xor": u32(count_key,4),
        "count_value_offset": byte(count_key,3),
        "count_value_add": 0,
        "parameter_state_offset": u32(parameter_table,2),
        "parameter_table_xor": u32(parameter_table,3),
        "parameter_source_offset": byte(parameter_source,1),
        "parameter_source_xor": u32(parameter_source,2),
        "parameter_source_add": 0,
        "parameter_stride": stride,
        "parameter_key_multiplier": u64(parameter_multiplier,1),
        "parameter_key_add": u32(parameter_mix,5),
        "parameter_key_xor": 0,
        "parameter_mix_multiplier": u32(parameter_mix,3),
        "parameter_mix_xor": byte(parameter_mix,4),
        "parameter_final_multiplier": 1,
        "parameter_key_shift": byte(parameter_mix,2),
        "parameter_helper": rip(parameter_helper,1),
        "descriptor_offset": u32(parameter_helper,2),
    }

def _derive_method_generic_decoder(
    *, binary: Path, method_pointer: int,
) -> dict[str, int]:
    try:
        return _derive_method_generic_decoder_legacy(
            binary=binary, method_pointer=method_pointer
        )
    except AcquisitionError as legacy_error:
        try:
            return _derive_method_generic_decoder_v2(
                binary=binary, method_pointer=method_pointer
            )
        except AcquisitionError:
            raise legacy_error


def _derive_method_generic_decoder_legacy(
    *, binary: Path, method_pointer: int,
) -> dict[str, int]:

    with MappedPE(binary, require_runtime_functions=False) as image:
        def read(address: int, size: int) -> bytes:
            if not image.image_base <= address < image.image_base + image.size_of_image:
                raise AcquisitionError(
                    "runtime method generic decoder target is outside the image"
                )
            offset = image.rva_to_offset(address - image.image_base)
            if offset is None or offset + size > len(image._mapping):
                raise AcquisitionError(
                    "runtime method generic decoder bytes are unavailable"
                )
            return bytes(image._mapping[offset : offset + size])

        target = method_pointer
        for _ in range(4):
            thunk = read(target, 16)
            if thunk[0] != 0xE9:
                break
            target = target + 5 + struct.unpack_from("<i", thunk, 1)[0]
        code = read(target, 640)

    def match(pattern: bytes, *, label: str, start: int = 0) -> re.Match[bytes]:
        matches = list(re.finditer(pattern, code[start:], re.DOTALL))
        if len(matches) != 1:
            raise AcquisitionError(
                f"runtime method generic {label} decoder is not unique"
            )
        found = matches[0]

        return found

    prefix = match(
        rb"\x48\x8b\x41(.)\xf6\x40(.)(.)\x74."
        rb"\x48\x8b\x48(.)\x48\x8b\x59(.)\x48\x85\xdb\x74."
        rb"\x8b\x3b",
        label="plain prefix",
    )
    plain_start = prefix.end()
    plain_argument_matches = list(
        re.finditer(
            rb"\x48\x8b\x43(.)\x48\x8b\x0c\xe8",
            code[plain_start:],
            re.DOTALL,
        )
    )
    plain_argument_offsets = {
        found.group(1)[0] for found in plain_argument_matches
    }
    if not plain_argument_matches or len(plain_argument_offsets) != 1:
        raise AcquisitionError(
            "runtime method generic plain argument decoder conflicts"
        )
    protected_resolvers = list(
        re.finditer(
            rb"\x8b\x48(.)\xe8(.{4})\x8b\x40(.)"
            rb"\xb9\xff\xff\xff\xff\x48\x39\xc8",
            code,
            re.DOTALL,
        )
    )
    if len(protected_resolvers) > 1:
        raise AcquisitionError(
            "runtime method generic definition resolver decoder is ambiguous"
        )
    if protected_resolvers:
        def unique(pattern: bytes, *, label: str) -> re.Match[bytes]:
            found = list(re.finditer(pattern, code, re.DOTALL))
            if len(found) != 1:
                raise AcquisitionError(
                    f"runtime method generic {label} decoder is not unique"
                )
            return found[0]

        def rip(found: re.Match[bytes], group: int) -> int:
            raw = found.group(group)
            return (
                target
                + found.start(group)
                + len(raw)
                + struct.unpack("<i", raw)[0]
            )

        resolver = protected_resolvers[0]
        resolver_call = resolver.group(2)
        definition_resolver = (
            target
            + resolver.start(2)
            + len(resolver_call)
            + struct.unpack("<i", resolver_call)[0]
        )
        if re.search(rb"\x44\x69\xe0(.{4})\x41\x81\xc4(.{4})\x41\x8b\x7f(.)\x44\x31\xe7\x81\xf7(.{4})", code, re.DOTALL):
            return _derive_scalar_affine_method_generic(target=target, code=code,
                prefix=prefix, plain_offset=next(iter(plain_argument_offsets)), resolver=resolver)
        count_table = unique(
            rb"\x48\x8b\x0d(.{4})\x48\x85\xc9.{0,16}"
            rb"\x48\x8b\x15(.{4})\x48\x63\x92(.{4})"
            rb"\x48\x81\xf2(.{4})\x48\x01\xd1"
            rb"\x49\x89\xc7\x49\xc1\xe7(.)\x49\x01\xcf",
            label="protected count table",
        )
        affine_count_keys = list(re.finditer(
            rb"\x48\xb9(.{8})\x48\x0f\xaf\xc8"
            rb"\x49\xbd(.{8})\x49\x01\xcd",
            code,
            re.DOTALL,
        ))
        if affine_count_keys:
            if len(affine_count_keys) != 1:
                raise AcquisitionError(
                    "runtime method generic affine count key decoder is not unique"
                )
            count_key = affine_count_keys[0]
            count_value = unique(
                rb"\xbf(.{4})\x41\x03\x7f(.)\x49\xc1\xed(.)"
                rb"\x41\x89\xfc\x45\x29\xec",
                label="affine count value",
            )
            parameter_table = unique(
                rb"\x48\x8b\x0d(.{4})\x48\x63\x91(.{4})"
                rb"\x48\x81\xf2(.{4})\x48\x03\x15(.{4})",
                label="affine parameter table",
            )
            parameter_source_xor = unique(
                rb"\x31\xff\xbd(.{4})\x4c\x8d\x74\x24.",
                label="affine parameter source constant",
            )
            parameter_source = unique(
                rb"\x41\x8b\x0f\x31\xe9\x44\x29\xe9"
                rb"\x0f\xb7\xc7\x01\xc8",
                label="affine parameter source",
            )
            parameter_key = unique(
                rb"\x48\xbb(.{8})\x48\x0f\xaf\xcb"
                rb"\x48\xbb(.{8})\x48\x01\xd9"
                rb"\x48\x81\xf1(.{4})\x48\x69\xc9(.{4})",
                label="affine parameter key",
            )
            parameter_stride = unique(
                rb"\x48\x89\xc8\x48\xc1\xe0(.)"
                rb"\x48\x29\xc8\x48\x29\xc8",
                label="affine parameter stride",
            )
            parameter_helper = unique(
                rb"\x4c\x89\xf1\xe8(.{4})\x48\x8d\x58(.)",
                label="affine parameter helper",
            )
            if (
                rip(count_table, 1) != rip(parameter_table, 4)
                or rip(count_table, 2) != rip(parameter_table, 1)
                or count_table.group(5)[0] < 3
                or count_table.group(5)[0] > 6
                or count_value.group(3)[0] >= 64
                or parameter_stride.group(1)[0] != 4
            ):
                raise AcquisitionError(
                    "runtime method generic affine decoder globals conflict"
                )
            return {
                "decoder_codec": 3,
                "parameter_table_add": 0,
                "function": target,
                "metadata_object_offset": prefix.group(1)[0],
                "flags_offset": prefix.group(2)[0],
                "inflated_mask": prefix.group(3)[0],
                "inflated_context_offset": prefix.group(4)[0],
                "generic_instance_offset": prefix.group(5)[0],
                "plain_count_offset": 0,
                "plain_arguments_offset": next(iter(plain_argument_offsets)),
                "definition_handle_offset": resolver.group(1)[0],
                "definition_resolver": definition_resolver,
                "protected_index_offset": resolver.group(3)[0],
                "metadata_base_global": rip(count_table, 1),
                "metadata_state_global": rip(count_table, 2),
                "count_base_add": 0,
                "count_table_xor": struct.unpack("<I", count_table.group(4))[0],
                "count_state_offset": struct.unpack("<I", count_table.group(3))[0],
                "record_key_multiplier": struct.unpack("<Q", count_key.group(1))[0],
                "record_shift": count_table.group(5)[0],
                "count_key_xor": 0,
                "count_key_multiplier": 1,
                "count_key_add": struct.unpack("<Q", count_key.group(2))[0],
                "count_key_shift": count_value.group(3)[0],
                "count_final_xor": 0,
                "count_value_offset": count_value.group(2)[0],
                "count_value_add": struct.unpack("<I", count_value.group(1))[0],
                "parameter_state_offset": struct.unpack("<I", parameter_table.group(2))[0],
                "parameter_table_xor": struct.unpack("<I", parameter_table.group(3))[0],
                "parameter_source_offset": 0,
                "parameter_source_xor": struct.unpack("<I", parameter_source_xor.group(1))[0],
                "parameter_source_add": 0,
                "parameter_stride": (1 << parameter_stride.group(1)[0]) - 2,
                "parameter_key_multiplier": struct.unpack("<Q", parameter_key.group(1))[0],
                "parameter_key_add": struct.unpack("<Q", parameter_key.group(2))[0],
                "parameter_key_xor": struct.unpack("<I", parameter_key.group(3))[0],
                "parameter_mix_multiplier": struct.unpack("<I", parameter_key.group(4))[0],
                "parameter_mix_xor": 0,
                "parameter_final_multiplier": 1,
                "parameter_key_shift": 0,
                "parameter_helper": rip(parameter_helper, 1),
                "descriptor_offset": parameter_helper.group(2)[0],
            }
        count_key = unique(
            rb"\x48\xb9(.{8})\x48\x0f\xaf\xc8"
            rb"\x48\x81\xf1(.{4})\x4c\x69\xe1(.{4})"
            rb"\x49\xc1\xec(.)",
            label="protected count key",
        )
        count_value = unique(
            rb"\x41\xbd(.{4})\x45\x03\x6f(.)\x45\x31\xe5",
            label="protected count value",
        )
        parameter_table = unique(
            rb"\x48\x8b\x0d(.{4})\x48\x63\x91(.{4})"
            rb"\x48\x81\xf2(.{4})\x48\x03\x15(.{4})",
            label="protected parameter table",
        )
        parameter_key = unique(
            rb"\x48\x69\xc3(.{4})\x48\x35(.{4})"
            rb"\x48\x69\xc0(.{4})\x48\x05(.{4})"
            rb"\x48\x35(.{4})\x48\x69\xc0(.{4})"
            rb"\x48\xc1\xe8(.)",
            label="protected parameter key",
        )
        parameter_source_add = unique(
            rb"\x31\xff\xbd(.{4})\x4c\x8d\x74\x24.",
            label="protected parameter source add",
        )
        parameter_source = unique(
            rb"\x41\x8b\x4f(.)\x01\xe9\x44\x31\xe1",
            label="protected parameter source",
        )
        parameter_helper = unique(
            rb"\x4c\x89\xf1\xe8(.{4})\x48\x8d\x58(.)",
            label="protected parameter helper",
        )
        if (
            rip(count_table, 1) != rip(parameter_table, 4)
            or rip(count_table, 2) != rip(parameter_table, 1)
        ):
            raise AcquisitionError(
                "runtime method generic protected decoder globals conflict"
            )
        parameter_shift = 4
        parameter_stride = (1 << parameter_shift) - 2
        return {
            "decoder_codec": 2,
            "parameter_table_add": 0,
            "function": target,
            "metadata_object_offset": prefix.group(1)[0],
            "flags_offset": prefix.group(2)[0],
            "inflated_mask": prefix.group(3)[0],
            "inflated_context_offset": prefix.group(4)[0],
            "generic_instance_offset": prefix.group(5)[0],
            "plain_count_offset": 0,
            "plain_arguments_offset": next(iter(plain_argument_offsets)),
            "definition_handle_offset": resolver.group(1)[0],
            "definition_resolver": definition_resolver,
            "protected_index_offset": resolver.group(3)[0],
            "metadata_base_global": rip(count_table, 1),
            "metadata_state_global": rip(count_table, 2),
            "count_base_add": 0,
            "count_table_xor": struct.unpack("<I", count_table.group(4))[0],
            "count_state_offset": struct.unpack("<I", count_table.group(3))[0],
            "record_key_multiplier": struct.unpack("<Q", count_key.group(1))[0],
            "record_shift": count_table.group(5)[0],
            "count_key_xor": struct.unpack("<I", count_key.group(2))[0],
            "count_key_multiplier": struct.unpack("<I", count_key.group(3))[0],
            "count_key_add": 0,
            "count_key_shift": count_key.group(4)[0],
            "count_final_xor": 0,
            "count_value_offset": count_value.group(2)[0],
            "count_value_add": struct.unpack("<I", count_value.group(1))[0],
            "parameter_state_offset": struct.unpack("<I", parameter_table.group(2))[0],
            "parameter_table_xor": struct.unpack("<I", parameter_table.group(3))[0],
            "parameter_source_offset": parameter_source.group(1)[0],
            "parameter_source_xor": 0,
            "parameter_source_add": struct.unpack("<I", parameter_source_add.group(1))[0],
            "parameter_stride": parameter_stride,
            "parameter_key_multiplier": struct.unpack("<I", parameter_key.group(1))[0],
            "parameter_key_add": struct.unpack("<I", parameter_key.group(4))[0],
            "parameter_key_xor": struct.unpack("<I", parameter_key.group(2))[0],
            "parameter_mix_multiplier": struct.unpack("<I", parameter_key.group(3))[0],
            "parameter_mix_xor": struct.unpack("<I", parameter_key.group(5))[0],
            "parameter_final_multiplier": struct.unpack("<I", parameter_key.group(6))[0],
            "parameter_key_shift": parameter_key.group(7)[0],
            "parameter_helper": rip(parameter_helper, 1),
            "descriptor_offset": parameter_helper.group(2)[0],
        }
    resolver = match(
        rb"\x8b\x48(.)\xe8(.{4})\x44\x8b\x78(.)\xb8\xff\xff\xff\xff",
        label="definition resolver",
    )
    resolver_call_disp = resolver.group(2)
    resolver_call_end = target + resolver.start(2) + len(resolver_call_disp)
    definition_resolver = resolver_call_end + struct.unpack(
        "<i", resolver_call_disp
    )[0]
    protected_start = resolver.end()
    base_global = match(
        rb"\x48\x8b\x05(.{4})\x48\x85\xc0",
        label="protected metadata base",
        start=protected_start,
    )
    base_disp = base_global.group(1)
    base_address = (
        target
        + protected_start
        + base_global.start(1)
        + 4
        + struct.unpack("<i", base_disp)[0]
    )
    count_state = match(
        rb"\x48\x8b\x0d(.{4})\xba(.{4})\x03\x51(.)",
        label="protected count state",
        start=protected_start,
    )
    state_disp = count_state.group(1)
    state_address = (
        target
        + protected_start
        + count_state.start(1)
        + 4
        + struct.unpack("<i", state_disp)[0]
    )
    count_index = match(
        rb"\x49\x69\xcf(.{4})\x49\xc1\xe7(.)",
        label="protected count index",
        start=protected_start,
    )
    count_mix = match(
        rb"\x48\x81\xf1(.{4})\x48\xb8(.{8})\x48\x0f\xaf\xc1"
        rb"\x49\xbc(.{8})\x49\x01\xc4\x49\xc1\xec(.)"
        rb"\x45\x8b\x2f\x45\x31\xe5\x41\x81\xf5(.{4})",
        label="protected count mix",
        start=protected_start,
    )
    parameter_state = match(
        rb"\x48\x8b\x0d(.{4})\x48\x63\x91(.{4})\x48\x81\xf2(.{4})"
        rb"\x48\x03\x15(.{4})",
        label="protected parameter state",
        start=protected_start,
    )
    parameter_state_disp = parameter_state.group(1)
    parameter_state_address = (
        target
        + protected_start
        + parameter_state.start(1)
        + 4
        + struct.unpack("<i", parameter_state_disp)[0]
    )
    parameter_base_disp = parameter_state.group(4)
    parameter_base_address = (
        target
        + protected_start
        + parameter_state.start(4)
        + 4
        + struct.unpack("<i", parameter_base_disp)[0]
    )
    parameter_source = match(
        rb"\x41\x8b\x4f(.)\x44\x31\xe1\x81\xf1(.{4})",
        label="protected parameter source",
        start=protected_start,
    )
    parameter_multiplier = match(
        rb"\x48\xbd(.{8})",
        label="protected parameter multiplier",
        start=protected_start,
    )
    parameter_mix = match(
        rb"\x48\x89\xc8\x48\xc1\xe0(.)\x48\x29\xc8\x48\x29\xc8"
        rb"\x48\x0f\xaf\xcd\x48\x81\xc1(.{4})\x48\x81\xf1(.{4})",
        label="protected parameter mix",
        start=protected_start,
    )
    parameter_helper = match(
        rb"\x4c\x89\xf1\xe8(.{4})\x48\x8d\x58(.)",
        label="protected parameter helper",
        start=protected_start,
    )
    helper_disp = parameter_helper.group(1)
    helper_address = (
        target
        + protected_start
        + parameter_helper.start(1)
        + 4
        + struct.unpack("<i", helper_disp)[0]
    )
    if (
        base_address != parameter_base_address
        or state_address != parameter_state_address
        or prefix.group(3)[0] == 0
    ):
        raise AcquisitionError(
            "runtime method generic protected decoder globals conflict"
        )
    parameter_shift = parameter_mix.group(1)[0]
    parameter_stride = (1 << parameter_shift) - 2
    if not 1 <= parameter_stride <= 64:
        raise AcquisitionError(
            "runtime method generic parameter stride is invalid"
        )
    return {
        "decoder_codec": 1,
        "parameter_table_add": 0,
        "function": target,
        "metadata_object_offset": prefix.group(1)[0],
        "flags_offset": prefix.group(2)[0],
        "inflated_mask": prefix.group(3)[0],
        "inflated_context_offset": prefix.group(4)[0],
        "generic_instance_offset": prefix.group(5)[0],
        "plain_count_offset": 0,
        "plain_arguments_offset": next(iter(plain_argument_offsets)),
        "definition_handle_offset": resolver.group(1)[0],
        "definition_resolver": definition_resolver,
        "protected_index_offset": resolver.group(3)[0],
        "metadata_base_global": base_address,
        "metadata_state_global": state_address,
        "count_base_add": struct.unpack("<I", count_state.group(2))[0],
        "count_table_xor": 0,
        "count_state_offset": count_state.group(3)[0],
        "record_key_multiplier": struct.unpack("<I", count_index.group(1))[0],
        "record_shift": count_index.group(2)[0],
        "count_key_xor": struct.unpack("<I", count_mix.group(1))[0],
        "count_key_multiplier": struct.unpack("<Q", count_mix.group(2))[0],
        "count_key_add": struct.unpack("<Q", count_mix.group(3))[0],
        "count_key_shift": count_mix.group(4)[0],
        "count_final_xor": struct.unpack("<I", count_mix.group(5))[0],
        "count_value_offset": 0,
        "count_value_add": 0,
        "parameter_state_offset": struct.unpack(
            "<I", parameter_state.group(2)
        )[0],
        "parameter_table_xor": struct.unpack(
            "<I", parameter_state.group(3)
        )[0],
        "parameter_source_offset": parameter_source.group(1)[0],
        "parameter_source_xor": struct.unpack(
            "<I", parameter_source.group(2)
        )[0],
        "parameter_source_add": 0,
        "parameter_stride": parameter_stride,
        "parameter_key_multiplier": struct.unpack(
            "<Q", parameter_multiplier.group(1)
        )[0],
        "parameter_key_add": struct.unpack("<I", parameter_mix.group(2))[0],
        "parameter_key_xor": struct.unpack("<I", parameter_mix.group(3))[0],
        "parameter_mix_multiplier": 1,
        "parameter_mix_xor": 0,
        "parameter_final_multiplier": 1,
        "parameter_key_shift": 0,
        "parameter_helper": helper_address,
        "descriptor_offset": parameter_helper.group(2)[0],
    }


def _binding(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
    metadata_usage_member_model: Path,
    metadata_usage_member_inventory: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    binary_identity = file_identity(binary)
    executable_sha256 = binary_identity["sha256"]
    identity_model_path, identity_path, identity_model, target = (
        _validated_model(
            model_path=type_identity_model,
            inventory_path=type_identity_inventory,
            schema=RUNTIME_TYPE_IDENTITY_SCHEMA,
            inventory_key="identity_inventory",
            executable_sha256=executable_sha256,
            label="type identity",
        )
    )
    reference_model_path, reference_path, _reference_model, _ = (
        _validated_model(
            model_path=type_reference_model,
            inventory_path=type_reference_inventory,
            schema=RUNTIME_TYPE_REFERENCE_SCHEMA,
            inventory_key="inventory",
            executable_sha256=target,
            label="type reference",
        )
    )
    method_model_path, method_path, _method_model, _ = _validated_model(
        model_path=method_detail_model,
        inventory_path=method_detail_inventory,
        schema=RUNTIME_METHOD_DETAIL_SCHEMA,
        inventory_key="inventory",
        executable_sha256=target,
        label="method detail",
    )
    semantics_path = _owner_file(
        reflection_semantics_model, label="reflection semantics"
    )
    semantics = read_json(semantics_path)
    operations = {
        row.get("key"): row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
    }
    from_handle = operations.get("method.from_handle", {})
    if (
        semantics.get("schema") != REFLECTION_SEMANTICS_SCHEMA
        or semantics.get("status") != "resolved"
        or semantics.get("binary", {}).get("sha256") != target
        or semantics.get("checks", {}).get("all_operations_resolved")
        is not True
        or from_handle.get("semantic_identity_resolved") is not True
        or not isinstance(from_handle.get("method_pointer"), int)
        or not isinstance(from_handle.get("metadata_pointer"), int)
        or from_handle["method_pointer"] <= 0
        or from_handle["metadata_pointer"] <= 0
    ):
        raise AcquisitionError(
            "runtime method generic reflection binding is stale"
        )
    identity_plan_path = _owner_file(
        identity_model_path.parent / "runtime-type-identity-plan.private.json",
        label="type identity plan",
    )
    identity_status_path = _owner_file(
        identity_model_path.parent
        / "runtime-type-identity-status.private.json",
        label="type identity status",
    )
    identity_plan = read_json(identity_plan_path)
    identity_status = read_json(identity_status_path)
    plan_process_id = identity_plan.get("target", {}).get("process_id")
    process_id, creation_filetime = bound_creation(
        identity_plan, _reference_model, _method_model, binary
    )
    if (
        identity_plan.get("status") != "prepared"
        or identity_plan.get("target", {}).get("executable_sha256") != target
        or identity_status.get("status") != "complete"
        or identity_status.get("process_id") != plan_process_id
        or not isinstance(plan_process_id, int)
        or plan_process_id <= 0
    ):
        raise AcquisitionError(
            "runtime method generic process binding is stale"
        )
    identity = identity_path.read_bytes()
    methods = method_path.read_bytes()
    references = reference_path.read_bytes()
    identity_header = _IDENTITY_HEADER.unpack_from(identity)
    method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(methods)
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(references)
    type_count = identity_header[5]
    image_base, image_bytes = identity_header[6:8]
    if (
        identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or method_header[0] != RUNTIME_METHOD_DETAIL_MAGIC
        or method_header[1] != RUNTIME_METHOD_DETAIL_VERSION
        or reference_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or reference_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or method_header[5] <= 0
        or method_header[8] != image_base
        or method_header[9] != image_bytes
        or reference_header[10] != image_base
        or reference_header[11] != image_bytes
        or _digest(identity_header[9], label="identity executable") != target
        or _digest(method_header[12], label="method executable") != target
        or _digest(reference_header[12], label="reference executable")
        != target
    ):
        raise AcquisitionError(
            "runtime method generic inventory headers are inconsistent"
        )
    candidate = _select_generic_arguments_candidate(
        identity=identity, methods=methods, references=references
    )
    decoder = _derive_method_generic_decoder(
        binary=binary, method_pointer=candidate["pointer"]
    )
    member_model_path = _owner_file(
        metadata_usage_member_model, label="metadata usage member model"
    )
    member_path = _owner_file(
        metadata_usage_member_inventory,
        label="metadata usage member inventory",
    )
    members = load_runtime_metadata_usage_member_inventory(
        model_path=member_model_path,
        inventory_path=member_path,
        expected_executable_sha256=target,
    )
    if not members["method_specs"]:
        raise AcquisitionError(
            "runtime method generic method-spec proof domain is empty"
        )
    return {
        "binary": binary_identity,
        "semantics": file_identity(semantics_path),
        "type_identity_model": file_identity(identity_model_path),
        "type_identity_inventory": file_identity(identity_path),
        "type_identity_plan": file_identity(identity_plan_path),
        "type_identity_status": file_identity(identity_status_path),
        "type_reference_model": file_identity(reference_model_path),
        "type_reference_inventory": file_identity(reference_path),
        "method_detail_model": file_identity(method_model_path),
        "method_detail_inventory": file_identity(method_path),
        "metadata_usage_member_model": file_identity(member_model_path),
        "metadata_usage_member_inventory": file_identity(member_path),
        "process_id": process_id,
        "creation_filetime": creation_filetime,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "type_count": type_count,
        "method_count": method_header[5],
        "handle_qword": method_header[10],
        "candidate": candidate,
        "decoder": decoder,
        "from_handle": {
            "pointer": from_handle["method_pointer"],
            "metadata": from_handle["metadata_pointer"],
        },
    }


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define ALPHA_BATCH_METHODS 512u
#define ALPHA_MAX_GENERIC_ARGUMENTS 64u
typedef struct{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t type_count,image_base,image_bytes,string_bytes;char executable[64],native[64],semantics[64];}identity_header;
typedef struct{uint32_t definition_index,flags;uint64_t descriptor,class_pointer,module_pointer,declaring_descriptor,type_object;uint32_t attributes,name_bytes,namespace_bytes,reserved;uint64_t name_offset,namespace_offset;}identity_record;
typedef struct{char magic[8];uint32_t version,header_bytes,method_bytes,parameter_bytes;uint64_t method_count,parameter_count,string_bytes,image_base,image_bytes,handle_qword,reserved;char executable[64],native[64],identity[64],names[64];}method_header;
typedef struct{uint32_t definition_index,method_index;uint64_t metadata,function,return_descriptor;uint32_t attributes,impl_attributes,token,slot,flags,parameter_count;uint64_t parameter_start,name_offset;}method_record;
typedef struct{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t usage_count,field_count,method_spec_count,image_base,image_bytes,type_base,type_stride,generic_base,generic_stride;char executable[64],identity[64],pair[64],content[64];}member_header;
typedef struct{uint32_t first,destination,kind,source;uint64_t slot;int32_t value0,value1,value2;uint32_t reserved;}member_record;
typedef struct{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t method_count,generic_method_count,generic_argument_count,image_base,image_bytes,candidate_method_index;char executable[64],identity[64],methods[64],references[64],semantics[64],members[64];}output_header;
typedef struct{uint32_t method_index,argument_count;uint64_t argument_start;}output_record;
_Static_assert(sizeof(identity_header)==$identity_header_bytes,"identity header");
_Static_assert(sizeof(identity_record)==$identity_record_bytes,"identity record");
_Static_assert(sizeof(method_header)==$method_header_bytes,"method header");
_Static_assert(sizeof(method_record)==$method_record_bytes,"method record");
_Static_assert(sizeof(output_header)==$output_header_bytes,"output header");
_Static_assert(sizeof(output_record)==$output_record_bytes,"output record");
static const char executable_sha256[]="$executable_sha256",identity_sha256[]="$identity_sha256",method_sha256[]="$method_sha256",reference_sha256[]="$reference_sha256",semantics_sha256[]="$semantics_sha256",member_sha256[]="$member_sha256";
static const DWORD expected_pid=${process_id}u;static const uint64_t expected_type_count=${type_count}ull,expected_method_count=${method_count}ull,expected_image_base=${image_base}ull,expected_image_bytes=${image_bytes}ull,expected_candidate_method=${candidate_method}ull;
static const uint32_t handle_qword=${handle_qword}u;
static const uint32_t decoder_codec=${decoder_decoder_codec}u,decoder_metadata_object_offset=${decoder_metadata_object_offset}u,decoder_flags_offset=${decoder_flags_offset}u,decoder_inflated_mask=${decoder_inflated_mask}u,decoder_inflated_context_offset=${decoder_inflated_context_offset}u,decoder_generic_instance_offset=${decoder_generic_instance_offset}u,decoder_plain_count_offset=${decoder_plain_count_offset}u,decoder_plain_arguments_offset=${decoder_plain_arguments_offset}u,decoder_definition_handle_offset=${decoder_definition_handle_offset}u,decoder_protected_index_offset=${decoder_protected_index_offset}u,decoder_count_state_offset=${decoder_count_state_offset}u,decoder_count_table_xor=${decoder_count_table_xor}u,decoder_record_shift=${decoder_record_shift}u,decoder_count_key_xor=${decoder_count_key_xor}u,decoder_count_key_shift=${decoder_count_key_shift}u,decoder_count_final_xor=${decoder_count_final_xor}u,decoder_count_value_offset=${decoder_count_value_offset}u,decoder_count_value_add=${decoder_count_value_add}u,decoder_parameter_state_offset=${decoder_parameter_state_offset}u,decoder_parameter_table_xor=${decoder_parameter_table_xor}u,decoder_parameter_table_add=${decoder_parameter_table_add}u,decoder_parameter_source_offset=${decoder_parameter_source_offset}u,decoder_parameter_source_xor=${decoder_parameter_source_xor}u,decoder_parameter_source_add=${decoder_parameter_source_add}u,decoder_parameter_stride=${decoder_parameter_stride}u,decoder_parameter_key_xor=${decoder_parameter_key_xor}u,decoder_parameter_mix_multiplier=${decoder_parameter_mix_multiplier}u,decoder_parameter_mix_xor=${decoder_parameter_mix_xor}u,decoder_parameter_final_multiplier=${decoder_parameter_final_multiplier}u,decoder_parameter_key_shift=${decoder_parameter_key_shift}u,decoder_descriptor_offset=${decoder_descriptor_offset}u;
static const uint64_t decoder_record_key_multiplier=${decoder_record_key_multiplier}ull,decoder_count_key_multiplier=${decoder_count_key_multiplier}ull,decoder_count_key_add=${decoder_count_key_add}ull,decoder_parameter_key_multiplier=${decoder_parameter_key_multiplier}ull,decoder_parameter_key_add=${decoder_parameter_key_add}ull;static const uintptr_t decoder_definition_resolver=${decoder_definition_resolver}ull,decoder_metadata_base_global=${decoder_metadata_base_global}ull,decoder_metadata_state_global=${decoder_metadata_state_global}ull,decoder_parameter_helper=${decoder_parameter_helper}ull;static const uint32_t decoder_count_base_add=${decoder_count_base_add}u;
static const wchar_t identity_path[]=$identity_path,method_path[]=$method_path,reference_path[]=$reference_path,semantics_path[]=$semantics_path,member_path[]=$member_path,output_path[]=$output_path,status_path[]=$status_path;
static unsigned char *identity_data,*method_data,*member_data;static method_record*methods;static output_record*records;static uint64_t*arguments;static unsigned char*known_generic,*known_arity;static uint32_t*known_instance;static uint64_t argument_count,argument_capacity,generic_count,capture_index,verify_index,completed_count,verified_count,failure_index,known_generic_count;static uint32_t failure_kind,generic_marker_offset,generic_marker_mode,generic_marker_mask;static UINT message_id;static WNDPROC original_proc;static volatile LONG action,complete;
static int readable(uintptr_t value,SIZE_T bytes){MEMORY_BASIC_INFORMATION r;if(!value||!bytes||value+bytes<value||!VirtualQuery((const void*)value,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t end=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&end>=value&&value+bytes<=end;}
static int valid_generic_descriptor(uintptr_t descriptor){uint64_t bits=0;if(!readable(descriptor,16u))return 0;memcpy(&bits,(const void*)(descriptor+8u),8u);return ((bits>>16)&0xffu)==0x1eu;}
static uintptr_t member_generic_base;static uint32_t member_generic_stride;
static int native_generic_arguments_from(uintptr_t metadata,uintptr_t output[ALPHA_MAX_GENERIC_ARGUMENTS],uint32_t*output_count){
    *output_count=0;if(!readable(metadata,64u))return 0;
    uint8_t flags=0;memcpy(&flags,(const void*)(metadata+decoder_flags_offset),1u);
    if(flags&decoder_inflated_mask){
        uintptr_t context=0,instance=0;memcpy(&context,(const void*)(metadata+decoder_inflated_context_offset),8u);
        if(!readable(context+decoder_generic_instance_offset,8u))return 0;memcpy(&instance,(const void*)(context+decoder_generic_instance_offset),8u);
        if(instance){
            uint32_t count=0;uintptr_t arguments_pointer=0;if(!readable(instance+decoder_plain_arguments_offset,8u))return 0;
            memcpy(&count,(const void*)(instance+decoder_plain_count_offset),4u);memcpy(&arguments_pointer,(const void*)(instance+decoder_plain_arguments_offset),8u);
            if(!count||count>ALPHA_MAX_GENERIC_ARGUMENTS||!readable(arguments_pointer,(SIZE_T)count*8u))return 0;
            for(uint32_t i=0;i<count;i++){memcpy(&output[i],(const void*)(arguments_pointer+(uintptr_t)i*8u),8u);if(!valid_generic_descriptor(output[i]))return 0;}
            *output_count=count;return 1;
        }
        uint32_t definition_handle=0;memcpy(&definition_handle,(const void*)(metadata+decoder_definition_handle_offset),4u);
        typedef uintptr_t(*definition_resolver)(uint32_t);metadata=((definition_resolver)decoder_definition_resolver)(definition_handle);if(!readable(metadata,64u))return 0;
    }
    uint32_t protected_index=0;memcpy(&protected_index,(const void*)(metadata+decoder_protected_index_offset),4u);if(protected_index==0xffffffffu)return 0;
    uintptr_t metadata_base=0,metadata_state=0;if(!readable(decoder_metadata_base_global,8u)||!readable(decoder_metadata_state_global,8u))return 0;
    memcpy(&metadata_base,(const void*)decoder_metadata_base_global,8u);memcpy(&metadata_state,(const void*)decoder_metadata_state_global,8u);
    if(!metadata_base||!metadata_state||!readable(metadata_state+decoder_count_state_offset,4u)||!readable(metadata_state+decoder_parameter_state_offset,4u))return 0;
    int32_t raw_count_displacement=0;memcpy(&raw_count_displacement,(const void*)(metadata_state+decoder_count_state_offset),4u);
    int64_t count_displacement=(decoder_codec==2u||decoder_codec==3u||decoder_codec==4u||decoder_codec==5u)?(int64_t)(((uint64_t)(int64_t)raw_count_displacement)^((uint64_t)(int64_t)(int32_t)decoder_count_table_xor)):(int64_t)(int32_t)(decoder_count_base_add+(uint32_t)raw_count_displacement);
    uintptr_t record=metadata_base+(intptr_t)count_displacement+((uintptr_t)protected_index<<decoder_record_shift);if(!readable(record,16u))return 0;
    uint64_t count_key=(uint64_t)protected_index*decoder_record_key_multiplier;count_key^=decoder_count_key_xor;count_key*=decoder_count_key_multiplier;
    if(decoder_codec==1u||decoder_codec==3u||decoder_codec==4u)count_key+=decoder_count_key_add;count_key>>=decoder_count_key_shift;
    if(decoder_codec==5u)count_key=(uint32_t)((uint32_t)protected_index*(uint32_t)decoder_record_key_multiplier+(uint32_t)decoder_count_key_add);
    uint32_t encrypted_count=0;memcpy(&encrypted_count,(const void*)(record+decoder_count_value_offset),4u);
    uint32_t count=decoder_codec==3u?(encrypted_count+decoder_count_value_add)-(uint32_t)count_key:(decoder_codec==2u||decoder_codec==4u)?(encrypted_count+decoder_count_value_add)^(uint32_t)count_key:encrypted_count^(uint32_t)count_key^decoder_count_final_xor;
    if(!count||count>ALPHA_MAX_GENERIC_ARGUMENTS)return 0;
    int32_t raw_parameter_displacement=0;memcpy(&raw_parameter_displacement,(const void*)(metadata_state+decoder_parameter_state_offset),4u);
    int64_t parameter_displacement=decoder_codec==4u?(int64_t)(int32_t)(decoder_parameter_table_add+(uint32_t)raw_parameter_displacement):(int64_t)(((uint64_t)(int64_t)raw_parameter_displacement)^((uint64_t)(int64_t)(int32_t)decoder_parameter_table_xor));
    uintptr_t parameter_table=metadata_base+(intptr_t)parameter_displacement;if(!readable(parameter_table,1u))return 0;
    uint32_t encrypted_source=0;memcpy(&encrypted_source,(const void*)(record+decoder_parameter_source_offset),4u);
    uint32_t source=decoder_codec==3u?(encrypted_source^decoder_parameter_source_xor)-(uint32_t)count_key:decoder_codec==2u?(encrypted_source+decoder_parameter_source_add)^(uint32_t)count_key:encrypted_source^(uint32_t)count_key^decoder_parameter_source_xor;
    typedef uintptr_t(*parameter_helper)(const uint64_t*);
    for(uint32_t i=0;i<count;i++){
        uint32_t parameter_index=source+(uint16_t)i;uint64_t pair[2]={0,0};
        if(parameter_index!=0xffffffffu){
            uint64_t parameter_key=(uint64_t)parameter_index*decoder_parameter_key_multiplier;
            if(decoder_codec==3u){parameter_key+=decoder_parameter_key_add;parameter_key^=decoder_parameter_key_xor;parameter_key*=decoder_parameter_mix_multiplier;}
            else if(decoder_codec==2u){parameter_key^=decoder_parameter_key_xor;parameter_key*=decoder_parameter_mix_multiplier;parameter_key+=decoder_parameter_key_add;parameter_key^=decoder_parameter_mix_xor;parameter_key*=decoder_parameter_final_multiplier;parameter_key>>=decoder_parameter_key_shift;}
            else if(decoder_codec==5u){parameter_key>>=decoder_parameter_key_shift;parameter_key*=decoder_parameter_mix_multiplier;parameter_key>>=decoder_parameter_mix_xor;parameter_key+=decoder_parameter_key_add;}
            else parameter_key=(parameter_key+decoder_parameter_key_add)^decoder_parameter_key_xor;
            pair[0]=parameter_key;pair[1]=parameter_table+(uintptr_t)parameter_index*decoder_parameter_stride;
        }
        uintptr_t parameter=((parameter_helper)decoder_parameter_helper)(pair);if(!parameter||parameter+decoder_descriptor_offset<parameter)return 0;
        output[i]=parameter+decoder_descriptor_offset;if(!valid_generic_descriptor(output[i]))return 0;
    }
    *output_count=count;return 1;
}
static int native_generic_arguments(uint64_t method_index,uintptr_t output[ALPHA_MAX_GENERIC_ARGUMENTS],uint32_t*output_count){
    uintptr_t metadata=methods[method_index].metadata;if(!readable(metadata,16u))return 0;
    /* The metadata usage member inventory already validated the generic
       instance record of every method spec live, so a known generic method
       yields its argument list straight from that instance. */
    if(decoder_codec==4u&&known_generic[method_index]&&known_instance[method_index]&&member_generic_base&&member_generic_stride){
        uintptr_t instance=member_generic_base+(uintptr_t)known_instance[method_index]*(uintptr_t)member_generic_stride;
        if(readable(instance,16u)){uint64_t count=0,list=0;memcpy(&count,(const void*)instance,8u);memcpy(&list,(const void*)(instance+8u),8u);
            if(count&&count<=ALPHA_MAX_GENERIC_ARGUMENTS&&readable(list,(SIZE_T)count*8u)){int ok=1;for(uint32_t i=0;i<(uint32_t)count;i++){uintptr_t argument=0;memcpy(&argument,(const void*)(list+(uintptr_t)i*8u),8u);if(!valid_generic_descriptor(argument)){ok=0;break;}output[i]=argument;}if(ok){*output_count=(uint32_t)count;return 1;}}}
    }
    if(native_generic_arguments_from(metadata,output,output_count))return 1;
    /* A protected client keeps the inflated definition one indirection deeper;
       the derived contract names that displacement, so the same expressions
       are evaluated against whichever object describes the method. */
    uint8_t direct_flags=0;
    if(decoder_codec==4u&&readable(metadata+decoder_flags_offset,1u)){
        memcpy(&direct_flags,(const void*)(metadata+decoder_flags_offset),1u);
    }
    if(decoder_codec==4u&&(direct_flags&decoder_inflated_mask)&&readable(metadata+decoder_metadata_object_offset,8u)){
        uintptr_t definition=0;memcpy(&definition,(const void*)(metadata+decoder_metadata_object_offset),8u);
        if(definition&&definition!=metadata&&native_generic_arguments_from(definition,output,output_count))return 1;
    }
    *output_count=0;return 0;
}
static int append_argument(uint64_t value){if(!value||argument_count>=expected_method_count*ALPHA_MAX_GENERIC_ARGUMENTS)return 0;if(argument_count==argument_capacity){uint64_t next=argument_capacity?argument_capacity*2u:4096u;if(next>expected_method_count*ALPHA_MAX_GENERIC_ARGUMENTS)next=expected_method_count*ALPHA_MAX_GENERIC_ARGUMENTS;uint64_t*grown=realloc(arguments,(SIZE_T)next*8u);if(!grown)return 0;arguments=grown;argument_capacity=next;}arguments[argument_count++]=value;return 1;}
static int read_file(const wchar_t*path,unsigned char**data,SIZE_T*bytes){*data=NULL;*bytes=0;FILE*f=_wfopen(path,L"rb");if(!f||_fseeki64(f,0,SEEK_END))return 0;__int64 size=_ftelli64(f);if(size<0||_fseeki64(f,0,SEEK_SET)){fclose(f);return 0;}*bytes=(SIZE_T)size;*data=malloc(*bytes?*bytes:1u);int ok=*data&&fread(*data,1,*bytes,f)==*bytes;fclose(f);if(!ok){free(*data);*data=NULL;}return ok;}
static void digest_hex(const unsigned char d[32],char o[65]){static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}o[64]=0;}
static int sha256_file(const wchar_t*path,char output[65]){HANDLE input=CreateFileW(path,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,FILE_ATTRIBUTE_NORMAL,NULL);if(input==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE algorithm=NULL;BCRYPT_HASH_HANDLE hash=NULL;DWORD object_size=0,received=0;unsigned char*object=NULL,*buffer=NULL,digest[32];int ok=BCryptOpenAlgorithmProvider(&algorithm,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(algorithm,BCRYPT_OBJECT_LENGTH,(PUCHAR)&object_size,sizeof(object_size),&received,0)>=0;if(ok)object=HeapAlloc(GetProcessHeap(),0,object_size);if(ok)buffer=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!object||!buffer))ok=0;if(ok&&BCryptCreateHash(algorithm,&hash,object,object_size,NULL,0,0)<0)ok=0;while(ok){DWORD count=0;if(!ReadFile(input,buffer,1048576u,&count,NULL)){ok=0;break;}if(!count)break;if(BCryptHashData(hash,buffer,count,0)<0)ok=0;}if(ok&&BCryptFinishHash(hash,digest,sizeof(digest),0)<0)ok=0;if(ok)digest_hex(digest,output);if(hash)BCryptDestroyHash(hash);if(algorithm)BCryptCloseAlgorithmProvider(algorithm,0);if(object)HeapFree(GetProcessHeap(),0,object);if(buffer)HeapFree(GetProcessHeap(),0,buffer);CloseHandle(input);return ok;}
static int executable_identity(char output[65]){wchar_t path[32768];DWORD n=GetModuleFileNameW(NULL,path,32768);return n&&n<32768&&sha256_file(path,output);}
static int method_has_generic_marker(uint64_t index){
    if(generic_marker_mode==5u){
        if(!readable(methods[index].metadata,16u))return -1;
        if(known_generic[index])return 1;
        /* Constructors inherit generic arguments from their declaring type in
           this decoder family, so only the member-evidenced ones are generic. */
        if(methods[index].flags&1u)return 0;
        uintptr_t scratch[ALPHA_MAX_GENERIC_ARGUMENTS]={0};uint32_t count=0;
        return native_generic_arguments(index,scratch,&count)?1:0;
    }
    uintptr_t metadata=methods[index].metadata;if(!readable(metadata,64u))return -1;
    if(generic_marker_mode==4u){
        uint8_t flags=0;memcpy(&flags,(const void*)(metadata+decoder_flags_offset),1u);
        if(flags&decoder_inflated_mask){
            uintptr_t context=0,instance=0;memcpy(&context,(const void*)(metadata+decoder_inflated_context_offset),8u);
            if(!readable(context+decoder_generic_instance_offset,8u))return -1;memcpy(&instance,(const void*)(context+decoder_generic_instance_offset),8u);if(instance)return 1;
            uint32_t definition_handle=0;memcpy(&definition_handle,(const void*)(metadata+decoder_definition_handle_offset),4u);
            typedef uintptr_t(*definition_resolver)(uint32_t);metadata=((definition_resolver)decoder_definition_resolver)(definition_handle);if(!readable(metadata,64u))return -1;
        }
        uint32_t protected_index=0;memcpy(&protected_index,(const void*)(metadata+decoder_protected_index_offset),4u);return protected_index!=0xffffffffu;
    }
    uintptr_t address=metadata+generic_marker_offset;
    if(generic_marker_mode==1u){uintptr_t value=0;if(!readable(address,8u))return -1;memcpy(&value,(const void*)address,8u);return value!=0;}
    if(generic_marker_mode==2u){uint32_t value=0;if(!readable(address,4u))return -1;memcpy(&value,(const void*)address,4u);return value!=0xffffffffu;}
    if(generic_marker_mode==3u){uint8_t value=0;if(!readable(address,1u))return -1;memcpy(&value,(const void*)address,1u);return !!(value&generic_marker_mask);}
    return -1;
}
static int derive_generic_marker(void){
    if(decoder_codec==4u){
        /*
         * The protected family hides the inflate step behind a layout that
         * changes between builds.  A method is therefore marked by behaviour:
         * only a method whose protected record really decodes into a valid
         * generic argument list is generic, which is the same evidence the
         * capture step publishes.
         */
        generic_marker_offset=0u;generic_marker_mode=5u;generic_marker_mask=0u;uint64_t observed=0;
        for(uint64_t i=0;i<expected_method_count;i++){int marked=method_has_generic_marker(i);if(marked<0||(known_generic[i]&&!marked)){failure_kind=10u;failure_index=i+1u;return 0;}observed+=(uint64_t)marked;}
        if(observed<known_generic_count||observed>100000u){failure_kind=11u;failure_index=observed;return 0;}return 1;
    }
    if(decoder_codec==2u||decoder_codec==3u||decoder_codec==5u){
        generic_marker_offset=decoder_protected_index_offset;generic_marker_mode=4u;generic_marker_mask=0u;uint64_t observed=0;
        for(uint64_t i=0;i<expected_method_count;i++){int marked=method_has_generic_marker(i);if(marked<0||(known_generic[i]&&!marked)){failure_kind=10u;failure_index=i+1u;return 0;}observed+=(uint64_t)marked;}
        if(observed<known_generic_count||observed>100000u){failure_kind=11u;failure_index=observed;return 0;}return 1;
    }
    uint32_t matches=0,selected_offset=0,selected_mode=0,selected_mask=0;
    for(uint32_t mode=1;mode<=2;mode++){uint32_t step=mode==1u?8u:4u;for(uint32_t offset=0;offset<64u;offset+=step){int valid=1;for(uint64_t i=0;i<expected_method_count&&valid;i++){if(!known_generic[i]&&!(methods[i].flags&1u))continue;uintptr_t address=methods[i].metadata+offset;if(mode==1u){uintptr_t value=0;if(!readable(address,8u)){valid=0;break;}memcpy(&value,(const void*)address,8u);if(known_generic[i])valid=value&&!(value&7u)&&readable(value,16u);else valid=value==0;}else{uint32_t value=0;if(!readable(address,4u)){valid=0;break;}memcpy(&value,(const void*)address,4u);if(known_generic[i])valid=value!=0xffffffffu&&value<expected_method_count;else valid=value==0xffffffffu;}}if(valid){selected_offset=offset;selected_mode=mode;selected_mask=0;matches++;}}}
    for(uint32_t offset=0;offset<64u;offset++){for(uint32_t mask=1u;mask<=0x80u;mask<<=1u){int valid=1;for(uint64_t i=0;i<expected_method_count&&valid;i++){if(!known_generic[i]&&!(methods[i].flags&1u))continue;uint8_t value=0;if(!readable(methods[i].metadata+offset,1u)){valid=0;break;}memcpy(&value,(const void*)(methods[i].metadata+offset),1u);if(known_generic[i])valid=!!(value&mask);else valid=!(value&mask);}if(valid){selected_offset=offset;selected_mode=3u;selected_mask=mask;matches++;}}}
    if(matches!=1u){failure_kind=9u;failure_index=matches;return 0;}generic_marker_offset=selected_offset;generic_marker_mode=selected_mode;generic_marker_mask=selected_mask;uint64_t observed=0;
    for(uint64_t i=0;i<expected_method_count;i++){int marked=method_has_generic_marker(i);if(marked<0||(known_generic[i]&&!marked)||(methods[i].flags&1u&&marked)){failure_kind=10u;failure_index=i+1u;return 0;}observed+=(uint64_t)marked;}
    if(observed<known_generic_count||observed>100000u){failure_kind=11u;failure_index=observed;return 0;}return 1;
}
static int derive_layout(void){for(uint64_t i=0;i<expected_method_count;i++){if(!known_generic[i])continue;uintptr_t values[ALPHA_MAX_GENERIC_ARGUMENTS]={0};uint32_t count=0;if(!native_generic_arguments(i,values,&count)||count!=known_arity[i]){failure_index=i+1u;failure_kind=12u;return 0;}}return 1;}
static int capture_batch(void){uint64_t end=capture_index+ALPHA_BATCH_METHODS;if(end>expected_method_count)end=expected_method_count;for(;capture_index<end;capture_index++){output_record*out=&records[capture_index];out->method_index=(uint32_t)capture_index;out->argument_start=argument_count;int marked=method_has_generic_marker(capture_index);if(marked<0){failure_index=capture_index+1u;failure_kind=19u;return 0;}if(!marked){completed_count++;continue;}uintptr_t values[ALPHA_MAX_GENERIC_ARGUMENTS]={0};uint32_t count=0;if(!native_generic_arguments(capture_index,values,&count)){failure_index=capture_index+1u;failure_kind=21u;return 0;}out->argument_count=count;for(uint32_t i=0;i<count;i++){for(uint32_t j=0;j<i;j++)if(values[j]==values[i]){failure_index=capture_index+1u;failure_kind=23u;return 0;}if(!append_argument(values[i])){failure_index=capture_index+1u;failure_kind=24u;return 0;}}generic_count++;completed_count++;}return 1;}
static int verify_batch(void){uint64_t end=verify_index+ALPHA_BATCH_METHODS;if(end>expected_method_count)end=expected_method_count;for(;verify_index<end;verify_index++){output_record*out=&records[verify_index];if(!out->argument_count)continue;uintptr_t values[ALPHA_MAX_GENERIC_ARGUMENTS]={0};uint32_t count=0;if(!native_generic_arguments(verify_index,values,&count)||count!=out->argument_count){failure_index=verify_index+1u;failure_kind=30u;return 0;}for(uint32_t i=0;i<count;i++)if(values[i]!=arguments[out->argument_start+i]){failure_index=verify_index+1u;failure_kind=31u;return 0;}verified_count++;}return 1;}
static LRESULT CALLBACK window_proc(HWND window,UINT message,WPARAM wparam,LPARAM lparam){if(message!=message_id)return CallWindowProcW(original_proc,window,message,wparam,lparam);LONG selected=InterlockedCompareExchange(&action,0,0);int ok=selected==1?derive_layout():selected==2?capture_batch():selected==3?verify_batch():0;InterlockedExchange(&complete,ok?1:-1);return ok;}
typedef struct{DWORD pid;HWND window;uint32_t count;}selection;static BOOL CALLBACK select_window(HWND window,LPARAM value){selection*s=(selection*)(uintptr_t)value;DWORD pid=0;RECT b;if(!IsWindowVisible(window)||GetWindow(window,GW_OWNER)||!GetWindowRect(window,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(window,&pid);if(pid==s->pid){s->window=window;s->count++;}return TRUE;}
static int send_action(HWND window,LONG selected){DWORD_PTR result=0;InterlockedExchange(&action,selected);InterlockedExchange(&complete,0);return SendMessageTimeoutW(window,message_id,0,0,SMTO_BLOCK,60000,&result)&&InterlockedCompareExchange(&complete,0,0)==1;}
static int dispatch(void){selection s={0};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window){failure_kind=100u;failure_index=s.count;return 0;}message_id=RegisterWindowMessageW(L"ALPHA v2 current runtime method generic inventory");SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);DWORD error=GetLastError();int ok=message_id&&(original_proc||error==ERROR_SUCCESS);if(ok)ok=send_action(s.window,1);while(ok&&capture_index<expected_method_count)ok=send_action(s.window,2);while(ok&&verify_index<expected_method_count)ok=send_action(s.window,3);if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);original_proc=NULL;if(!ok&&!failure_kind)failure_kind=101u;return ok;}
static void write_status(const char*status,int written){FILE*out=_wfopen(status_path,L"wb");if(!out)return;fprintf(out,"{\n  \"schema\": \"$status_schema\",\n  \"status\": \"%s\",\n  \"process_id\": %lu,\n  \"completed_method_count\": %llu,\n  \"generic_method_count\": %llu,\n  \"generic_argument_count\": %llu,\n  \"verified_generic_method_count\": %llu,\n  \"known_method_spec_definition_count\": %llu,\n  \"generic_marker_offset_owner_only\": %u,\n  \"generic_marker_mode_owner_only\": %u,\n  \"generic_marker_mask_owner_only\": %u,\n  \"failure_index_owner_only\": %llu,\n  \"failure_kind_owner_only\": %u,\n  \"output_written\": %s,\n  \"fresh_runtime_observation\": true,\n  \"second_generic_observation\": true,\n  \"protected_generic_decoder_current_code_derived\": true,\n  \"generic_marker_live_derived\": true,\n  \"saved_method_generic_used\": false,\n  \"fixed_address_used\": false,\n  \"fixed_offset_used\": false,\n  \"external_runtime_component_used\": false\n}\n",status,(unsigned long)GetCurrentProcessId(),(unsigned long long)completed_count,(unsigned long long)generic_count,(unsigned long long)argument_count,(unsigned long long)verified_count,(unsigned long long)known_generic_count,generic_marker_offset,generic_marker_mode,generic_marker_mask,(unsigned long long)failure_index,failure_kind,written?"true":"false");fclose(out);}
static int write_output(void){output_header header;memset(&header,0,sizeof(header));memcpy(header.magic,"ALPHAMG1",8);header.version=$output_version;header.header_bytes=sizeof(header);header.record_bytes=sizeof(output_record);header.method_count=expected_method_count;header.generic_method_count=generic_count;header.generic_argument_count=argument_count;header.image_base=expected_image_base;header.image_bytes=expected_image_bytes;header.candidate_method_index=expected_candidate_method;memcpy(header.executable,executable_sha256,64);memcpy(header.identity,identity_sha256,64);memcpy(header.methods,method_sha256,64);memcpy(header.references,reference_sha256,64);memcpy(header.semantics,semantics_sha256,64);memcpy(header.members,member_sha256,64);FILE*out=_wfopen(output_path,L"wb");if(!out)return 0;int ok=fwrite(&header,1,sizeof(header),out)==sizeof(header)&&fwrite(records,sizeof(*records),expected_method_count,out)==expected_method_count&&fwrite(arguments,8u,argument_count,out)==argument_count;if(fclose(out))ok=0;if(!ok)_wremove(output_path);return ok;}
static DWORD WINAPI worker(LPVOID unused){(void)unused;_wremove(output_path);_wremove(status_path);char executable[65],identity[65],method[65],reference[65],semantics[65],member[65];if(GetCurrentProcessId()!=expected_pid||!executable_identity(executable)||strcmp(executable,executable_sha256)||!sha256_file(identity_path,identity)||strcmp(identity,identity_sha256)||!sha256_file(method_path,method)||strcmp(method,method_sha256)||!sha256_file(reference_path,reference)||strcmp(reference,reference_sha256)||!sha256_file(semantics_path,semantics)||strcmp(semantics,semantics_sha256)||!sha256_file(member_path,member)||strcmp(member,member_sha256)){failure_kind=200u;write_status("identity_mismatch",0);return 0;}SIZE_T identity_bytes=0,method_bytes=0,member_bytes=0;if(!read_file(identity_path,&identity_data,&identity_bytes)||!read_file(method_path,&method_data,&method_bytes)||!read_file(member_path,&member_data,&member_bytes)||identity_bytes<sizeof(identity_header)+expected_type_count*sizeof(identity_record)||method_bytes<sizeof(method_header)+expected_method_count*sizeof(method_record)||member_bytes<sizeof(member_header)){failure_kind=201u;write_status("input_unavailable",0);return 0;}identity_header*ih=(identity_header*)identity_data;method_header*mh=(method_header*)method_data;member_header*uh=(member_header*)member_data;uint64_t member_count=uh->field_count+uh->method_spec_count;if(memcmp(ih->magic,"ALPHATI1",8)||ih->version!=1u||ih->type_count!=expected_type_count||ih->image_base!=expected_image_base||ih->image_bytes!=expected_image_bytes||memcmp(mh->magic,"ALPHADM1",8)||mh->version!=1u||mh->method_count!=expected_method_count||mh->image_base!=expected_image_base||mh->image_bytes!=expected_image_bytes||mh->handle_qword!=handle_qword||memcmp(uh->magic,"ALPHAUM1",8)||uh->version!=1u||uh->header_bytes!=sizeof(member_header)||uh->record_bytes!=sizeof(member_record)||uh->image_base!=expected_image_base||uh->image_bytes!=expected_image_bytes||member_count>(member_bytes-sizeof(member_header))/sizeof(member_record)){failure_kind=202u;write_status("input_invalid",0);return 0;}methods=(method_record*)(method_data+sizeof(*mh));member_generic_base=uh->generic_base;member_generic_stride=(uint32_t)uh->generic_stride;records=calloc((SIZE_T)expected_method_count,sizeof(*records));known_generic=calloc((SIZE_T)expected_method_count,1u);known_arity=calloc((SIZE_T)expected_method_count,1u);known_instance=calloc((SIZE_T)expected_method_count,sizeof(uint32_t));if(!records||!known_generic||!known_arity||!known_instance){failure_kind=203u;write_status("allocation_failed",0);return 0;}member_record*member_rows=(member_record*)(member_data+sizeof(*uh));for(uint64_t i=0;i<member_count;i++){member_record*row=&member_rows[i];if(row->kind!=6u||row->value0<0)continue;if(row->value2<0||(uint32_t)row->value2>=expected_method_count||!uh->generic_stride){failure_kind=205u;failure_index=i+1u;write_status("member_invalid",0);return 0;}uint64_t arity=0;uintptr_t instance=uh->generic_base+(uintptr_t)(uint32_t)row->value0*uh->generic_stride;if(!readable(instance,8u)){failure_kind=207u;failure_index=i+1u;write_status("arity_unreadable",0);return 0;}memcpy(&arity,(const void*)instance,8u);if(!arity||arity>ALPHA_MAX_GENERIC_ARGUMENTS||(known_arity[row->value2]&&known_arity[row->value2]!=arity)){failure_kind=208u;failure_index=i+1u;write_status("arity_invalid",0);return 0;}known_arity[row->value2]=(uint8_t)arity;if(!known_instance[row->value2])known_instance[row->value2]=(uint32_t)row->value0;if(!known_generic[row->value2]){known_generic[row->value2]=1u;known_generic_count++;}}if(!known_generic_count||!derive_generic_marker()){if(!failure_kind)failure_kind=206u;write_status("marker_failed",0);return 0;}if(!dispatch()||completed_count!=expected_method_count||generic_count<known_generic_count||verified_count!=generic_count){if(!failure_kind)failure_kind=204u;write_status("capture_failed",0);return 0;}int ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}
BOOL WINAPI DllMain(HINSTANCE module,DWORD reason,LPVOID reserved){(void)reserved;if(reason==DLL_PROCESS_ATTACH){DisableThreadLibraryCalls(module);HANDLE thread=CreateThread(NULL,0,worker,NULL,0,NULL);if(thread)CloseHandle(thread);}return TRUE;}
''')


def runtime_method_generic_inventory_source(
    *, binding: dict[str, Any], output_path: Path, status_path: Path,
) -> str:
    candidate = binding["candidate"]
    values = {
            "identity_header_bytes": _IDENTITY_HEADER.size,
            "identity_record_bytes": _IDENTITY_RECORD.size,
            "method_header_bytes": RUNTIME_METHOD_DETAIL_HEADER.size,
            "method_record_bytes": RUNTIME_METHOD_DETAIL_METHOD.size,
            "output_header_bytes": RUNTIME_METHOD_GENERIC_HEADER.size,
            "output_record_bytes": RUNTIME_METHOD_GENERIC_RECORD.size,
            "output_version": RUNTIME_METHOD_GENERIC_VERSION,
            "status_schema": RUNTIME_METHOD_GENERIC_STATUS_SCHEMA,
            "executable_sha256": binding["binary"]["sha256"],
            "identity_sha256": binding["type_identity_inventory"]["sha256"],
            "method_sha256": binding["method_detail_inventory"]["sha256"],
            "reference_sha256": binding["type_reference_inventory"]["sha256"],
            "semantics_sha256": binding["semantics"]["sha256"],
            "member_sha256": binding[
                "metadata_usage_member_inventory"
            ]["sha256"],
            "process_id": binding["process_id"],
            "type_count": binding["type_count"],
            "method_count": binding["method_count"],
            "image_base": binding["image_base"],
            "image_bytes": binding["image_bytes"],
            "candidate_method": candidate["method_index"],
            "handle_qword": binding["handle_qword"],
            "runtime_type_class": candidate["runtime_type_class"],
            "method_class": candidate["method_class"],
            "from_handle_pointer": binding["from_handle"]["pointer"],
            "from_handle_metadata": binding["from_handle"]["metadata"],
            "generic_arguments_pointer": candidate["pointer"],
            "generic_arguments_metadata": candidate["metadata"],
            "identity_path": _wide_literal(
                _windows_z_path(Path(binding["type_identity_inventory"]["path"]))
            ),
            "method_path": _wide_literal(
                _windows_z_path(Path(binding["method_detail_inventory"]["path"]))
            ),
            "reference_path": _wide_literal(
                _windows_z_path(Path(binding["type_reference_inventory"]["path"]))
            ),
            "semantics_path": _wide_literal(
                _windows_z_path(Path(binding["semantics"]["path"]))
            ),
            "member_path": _wide_literal(
                _windows_z_path(
                    Path(binding["metadata_usage_member_inventory"]["path"])
                )
            ),
            "output_path": _wide_literal(_windows_z_path(output_path)),
            "status_path": _wide_literal(_windows_z_path(status_path)),
        }
    for key, value in binding["decoder"].items():
        values[f"decoder_{key}"] = value
    return protect_source(_COLLECTOR.substitute(values), creation_filetime=binding.get("creation_filetime"))


def prepare_runtime_method_generic_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
    metadata_usage_member_model: Path,
    metadata_usage_member_inventory: Path, output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(_safe_path(output_dir))
    if any(output_dir.iterdir()):
        raise AcquisitionError("method generic capture requires a new empty output directory")
    binding = _binding(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        metadata_usage_member_model=metadata_usage_member_model,
        metadata_usage_member_inventory=metadata_usage_member_inventory,
    )
    output_path = output_dir / "runtime-method-generics.private.bin"
    status_path = output_dir / "runtime-method-generics-status.private.json"
    model_path = output_dir / "runtime-method-generics.private.json"
    plan_path = output_dir / "runtime-method-generics-plan.private.json"
    build_dir = _owner_directory(output_dir / "build-method-generics")
    source_path = build_dir / "runtime-method-generics.c"
    injector_source = build_dir / "runtime-method-generics-injector.c"
    injector_path = build_dir / "alpha-runtime-method-generics-injector.exe"
    _private_text(
        source_path,
        runtime_method_generic_inventory_source(
            binding=binding, output_path=output_path, status_path=status_path
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    collector_path = build_dir / (
        "alpha-runtime-method-generics-"
        + file_identity(source_path)["sha256"][:12]
        + ".dll"
    )
    selected_compiler = _compiler(compiler)


    with ThreadPoolExecutor(max_workers=2) as executor:
        collector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler), "-O2", "-s", "-shared", "-Wall",
                "-Wextra", "-Wformat=2", "-Werror=format", str(source_path),
                "-o", str(collector_path), "-lbcrypt",
            ],
            label="runtime method generic collector",
            source_path=source_path,
            output_path=collector_path,
        )
        injector_build = executor.submit(
            cached_windows_build,
            [
                str(selected_compiler), "-O2", "-s", "-municode", "-Wall",
                "-Wextra", "-Wformat=2", "-Werror=format",
                str(injector_source), "-o", str(injector_path),
            ],
            label="runtime method generic injector",
            source_path=injector_source,
            output_path=injector_path,
        )
        collector_build.result()
        injector_build.result()
    for artifact in (collector_path, injector_path):
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_METHOD_GENERIC_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(Path(binary).expanduser().resolve()),
            "executable_sha256": binding["binary"]["sha256"],
            "process_id": binding["process_id"],
            "creation_filetime": binding["creation_filetime"],
            "image_base_owner_only": binding["image_base"],
            "image_bytes": binding["image_bytes"],
        },
        "inputs": {
            key: binding[key]
            for key in (
                "semantics", "type_identity_model",
                "type_identity_inventory", "type_identity_plan",
                "type_identity_status", "type_reference_model",
                "type_reference_inventory", "method_detail_model",
                "method_detail_inventory", "metadata_usage_member_model",
                "metadata_usage_member_inventory",
            )
        },
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "output_path": str(output_path),
        "status_path": str(status_path),
        "model_path": str(model_path),
        "contract": {
            "type_count": binding["type_count"],
            "method_count": binding["method_count"],
            "record_bytes": RUNTIME_METHOD_GENERIC_RECORD.size,
            "candidate_method_index_owner_only": binding["candidate"][
                "method_index"
            ],
            "candidate_method_pointer_owner_only": binding["candidate"][
                "pointer"
            ],
            "protected_generic_decoder_owner_only": binding["decoder"],
            "candidate_unique_current_signature": True,
            "all_methods_required": True,
            "second_generic_observation_required": True,
            "generation_bound_dispatch_required": True,
            "callback_quiescence_required": True,
            "metadata_usage_method_spec_arity_agreement_required": True,
        },
        "policy": {
            "same_process_required": True,
            "current_executable_sha256_embedded": True,
            "current_runtime_semantics_embedded": True,
            "protected_generic_decoder_current_code_derived": True,
            "generic_method_marker_live_derived": True,
            "raw_pointers_owner_only": True,
            "saved_method_generic_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(plan_path, plan)
    return {
        "schema": RUNTIME_METHOD_GENERIC_PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "method_count": binding["method_count"],
        "candidate_count": 1,
        "policy": plan["policy"],
    }


def _qword(image: MappedPE, pointer: int) -> int:
    if (
        pointer < image.image_base
        or pointer + 8 > image.image_base + image.size_of_image
    ):
        raise AcquisitionError(
            "runtime method generic proof pointer is outside the exact image"
        )
    offset = image.rva_to_offset(pointer - image.image_base)
    if offset is None or offset + 8 > len(image._mapping):
        raise AcquisitionError(
            "runtime method generic proof pointer has no immutable PE bytes"
        )
    return struct.unpack_from("<Q", image._mapping, offset)[0]


def _record_rows(
    record: struct.Struct, raw: bytes, start: int, count: int,
):
    if count <= 0:
        return iter(())
    end = start + count * record.size
    if start >= 0 and end <= len(raw):
        return record.iter_unpack(memoryview(raw)[start:end])
    return (
        record.unpack_from(raw, start + index * record.size)
        for index in range(count)
    )


def _validate_capture(
    *, plan: dict[str, Any], status: dict[str, Any],
) -> tuple[dict[str, int], dict[str, bool]]:
    output_path = Path(plan["output_path"])
    raw = output_path.read_bytes()
    if len(raw) < RUNTIME_METHOD_GENERIC_HEADER.size:
        raise AcquisitionError("runtime method generic output is truncated")
    header = RUNTIME_METHOD_GENERIC_HEADER.unpack_from(raw)
    method_count = plan["contract"]["method_count"]
    generic_count, argument_count = header[6:8]
    records_start = RUNTIME_METHOD_GENERIC_HEADER.size
    arguments_start = (
        records_start + method_count * RUNTIME_METHOD_GENERIC_RECORD.size
    )
    header_valid = (
        header[0] == RUNTIME_METHOD_GENERIC_MAGIC
        and header[1] == RUNTIME_METHOD_GENERIC_VERSION
        and header[2] == RUNTIME_METHOD_GENERIC_HEADER.size
        and header[3] == RUNTIME_METHOD_GENERIC_RECORD.size
        and header[4] == 0
        and header[5] == method_count
        and header[8] == plan["target"]["image_base_owner_only"]
        and header[9] == plan["target"]["image_bytes"]
        and header[10]
        == plan["contract"]["candidate_method_index_owner_only"]
        and _digest(header[11], label="output executable")
        == plan["target"]["executable_sha256"]
        and _digest(header[12], label="output identity")
        == plan["inputs"]["type_identity_inventory"]["sha256"]
        and _digest(header[13], label="output methods")
        == plan["inputs"]["method_detail_inventory"]["sha256"]
        and _digest(header[14], label="output references")
        == plan["inputs"]["type_reference_inventory"]["sha256"]
        and _digest(header[15], label="output semantics")
        == plan["inputs"]["semantics"]["sha256"]
        and _digest(header[16], label="output members")
        == plan["inputs"]["metadata_usage_member_inventory"]["sha256"]
        and arguments_start + argument_count * 8 == len(raw)
    )
    method_raw = Path(
        plan["inputs"]["method_detail_inventory"]["path"]
    ).read_bytes()
    arguments = (
        struct.unpack_from(f"<{argument_count}Q", raw, arguments_start)
        if argument_count
        else ()
    )
    rows_valid = header_valid
    generic_methods: dict[int, int] = {}
    marker_mode = status.get("generic_marker_mode_owner_only")
    members = load_runtime_metadata_usage_member_inventory(
        model_path=Path(
            plan["inputs"]["metadata_usage_member_model"]["path"]
        ),
        inventory_path=Path(
            plan["inputs"]["metadata_usage_member_inventory"]["path"]
        ),
        expected_executable_sha256=plan["target"]["executable_sha256"],
    )
    spec_definitions = {
        spec["method_definition_index"]
        for spec in members["method_specs"]
        if spec["method_inst_index"] >= 0
    }
    cursor = 0
    for index, (record_row, method) in enumerate(
        zip(
            _record_rows(
                RUNTIME_METHOD_GENERIC_RECORD, raw, records_start, method_count
            ),
            _record_rows(
                RUNTIME_METHOD_DETAIL_METHOD,
                method_raw,
                RUNTIME_METHOD_DETAIL_HEADER.size,
                method_count,
            ),
        )
    ):
        method_index, count, start = record_row
        if count:
            values = arguments[start : start + count]
            invalid = (
                method_index != index
                or start != cursor
                or count > 64
                or start + count > argument_count
                or (
                    method[9] & METHOD_DETAIL_CONSTRUCTOR
                    and not (marker_mode == 5 and index in spec_definitions)
                )
                or any(not value or value & 7 for value in values)
                or len(set(values)) != count
            )
        else:


            invalid = (
                method_index != index
                or start != cursor
                or start > argument_count
            )
        if invalid:
            rows_valid = False
            break
        if count:
            generic_methods[index] = count
        cursor += count
    rows_valid = (
        rows_valid
        and cursor == argument_count
        and len(generic_methods) == generic_count
    )
    spec_count = 0
    spec_methods: set[int] = set()
    spec_arity_agreement = rows_valid
    with MappedPE(
        Path(plan["target"]["executable_path"]),
        require_runtime_functions=False,
    ) as image:
        generic_base = image.image_base + members["generic_inst_base_rva"]
        for spec in members["method_specs"]:
            instance = spec["method_inst_index"]
            if instance < 0:
                continue
            definition = spec["method_definition_index"]
            arity = _qword(
                image,
                generic_base + instance * members["generic_inst_stride"],
            )
            spec_count += 1
            spec_methods.add(definition)
            if not 1 <= arity <= 64 or generic_methods.get(definition) != arity:
                spec_arity_agreement = False
                break
    counts = {
        "method_count": method_count,
        "generic_method_count": generic_count,
        "generic_argument_count": argument_count,
        "metadata_usage_method_spec_count": spec_count,
        "metadata_usage_unique_method_count": len(spec_methods),
    }
    decoder_code_derived = False
    decoder = plan.get("contract", {}).get(
        "protected_generic_decoder_owner_only"
    )
    candidate_pointer = plan.get("contract", {}).get(
        "candidate_method_pointer_owner_only"
    )
    if (
        isinstance(decoder, dict)
        and decoder
        and all(type(value) is int for value in decoder.values())
        and type(candidate_pointer) is int
        and candidate_pointer > 0
    ):
        try:
            current_decoder = _derive_method_generic_decoder(
                binary=Path(plan["target"]["executable_path"]),
                method_pointer=candidate_pointer,
            )
        except AcquisitionError:
            current_decoder = None
        decoder_code_derived = current_decoder == decoder
    checks = {
        "process_creation_matches": type(status.get("creation_filetime")) is int
            and status["creation_filetime"] == plan["target"].get("creation_filetime"),
        "dispatch_generation_bound": status.get("request_generation_bound") is True
            and plan["contract"].get("generation_bound_dispatch_required") is True,
        "callback_quiescent": status.get("callback_quiescent") is True
            and plan["contract"].get("callback_quiescence_required") is True,
        "status_schema": status.get("schema")
        == RUNTIME_METHOD_GENERIC_STATUS_SCHEMA,
        "status_complete": status.get("status") == "complete",
        "same_process": status.get("process_id")
        == plan["target"]["process_id"],
        "header_bound": header_valid,
        "all_methods_captured": status.get("completed_method_count")
        == method_count,
        "generic_rows_valid": rows_valid,
        "generic_count_matches": status.get("generic_method_count")
        == generic_count,
        "argument_count_matches": status.get("generic_argument_count")
        == argument_count,
        "second_generic_observation_complete": status.get(
            "second_generic_observation"
        )
        is True
        and status.get("verified_generic_method_count") == generic_count,
        "protected_generic_decoder_current_code_derived": status.get(
            "protected_generic_decoder_current_code_derived"
        )
        is True
        and plan.get("policy", {}).get(
            "protected_generic_decoder_current_code_derived"
        )
        is True
        and decoder_code_derived,
        "generic_method_marker_live_derived": status.get(
            "generic_marker_live_derived"
        )
        is True
        and isinstance(status.get("generic_marker_offset_owner_only"), int)
        and 0 <= status["generic_marker_offset_owner_only"] < 64
        and status.get("generic_marker_mode_owner_only") in (1, 2, 3, 4, 5)
        and isinstance(status.get("generic_marker_mask_owner_only"), int)
        and (
            status["generic_marker_mode_owner_only"] in (1, 2)
            and status["generic_marker_mask_owner_only"] == 0
            or status["generic_marker_mode_owner_only"] == 3
            and status["generic_marker_mask_owner_only"]
            in (1, 2, 4, 8, 16, 32, 64, 128)
            or status["generic_marker_mode_owner_only"] == 4
            and status["generic_marker_mask_owner_only"] == 0
            and decoder.get("decoder_codec") in (2, 3, 5)
            and status["generic_marker_offset_owner_only"]
            == decoder.get("protected_index_offset")
            or status["generic_marker_mode_owner_only"] == 5
            and status["generic_marker_mask_owner_only"] == 0
            and status["generic_marker_offset_owner_only"] == 0
            and decoder.get("decoder_codec") == 4
        )
        and status.get("known_method_spec_definition_count")
        == len(spec_methods),
        "metadata_usage_method_spec_arity_exact": spec_arity_agreement,
        "metadata_usage_method_spec_domain_complete": spec_count
        == len(
            [
                spec
                for spec in members["method_specs"]
                if spec["method_inst_index"] >= 0
            ]
        ),
        "fresh_runtime_observation": status.get(
            "fresh_runtime_observation"
        )
        is True,
        "saved_method_generic_absent": status.get(
            "saved_method_generic_used"
        )
        is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_component_used"
        )
        is False,
    }
    return counts, checks


@current_capture_scope
def capture_runtime_method_generic_inventory(
    *, binary: Path, reflection_semantics_model: Path,
    type_identity_model: Path, type_identity_inventory: Path,
    type_reference_model: Path, type_reference_inventory: Path,
    method_detail_model: Path, method_detail_inventory: Path,
    metadata_usage_member_model: Path,
    metadata_usage_member_inventory: Path, output_dir: Path,
    wine: Path, wineprefix: Path, compiler: Path | None = None,
    timeout: float = 1800.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_method_generic_inventory(
        binary=binary,
        reflection_semantics_model=reflection_semantics_model,
        type_identity_model=type_identity_model,
        type_identity_inventory=type_identity_inventory,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        method_detail_model=method_detail_model,
        method_detail_inventory=method_detail_inventory,
        metadata_usage_member_model=metadata_usage_member_model,
        metadata_usage_member_inventory=metadata_usage_member_inventory,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan_path = output_dir / "runtime-method-generics-plan.private.json"
    plan = read_json(plan_path)
    capture_sources = dict(plan["inputs"], collector=plan["collector"], injector=plan["injector"])
    _verify_files(capture_sources)
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError("runtime method generic Wine is unavailable")
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "runtime method generic injector could not run"
        ) from error
    _private_text(
        output_dir / "runtime-method-generics-injector.private.log",
        json.dumps(
            {
                "returncode": injected.returncode,
                "stdout": injected.stdout,
                "stderr": injected.stderr,
            },
            ensure_ascii=False,
            indent=2,
        )
        + "\n",
    )
    if injected.returncode:
        raise AcquisitionError("runtime method generic injection failed")
    deadline = time.monotonic() + timeout
    status_path = Path(plan["status_path"])
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        assert_current_capture_alive()
        if status_path.is_file():
            try:
                candidate = read_json(status_path)
            except (OSError, ValueError):
                candidate = None
            if (isinstance(candidate, dict) and candidate.get("status")
                    and candidate["status"] not in ("capturing", "verifying", "running")):
                status = candidate
                break
        time.sleep(0.2)
    if status is None:
        raise AcquisitionError("runtime method generic capture timed out")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "runtime method generic capture failed "
            f"(status={status.get('status')}, "
            f"index={status.get('failure_index_owner_only')}, "
            f"kind={status.get('failure_kind_owner_only')})"
        )
    output_path = Path(plan["output_path"])
    _seal_runtime_output(output_path)
    _seal_runtime_output(status_path)
    _verify_files(capture_sources)
    counts, checks = _validate_capture(plan=plan, status=status)
    if not all(checks.values()):
        failed = sorted(key for key, value in checks.items() if not value)
        raise AcquisitionError(
            "runtime method generic validation failed: " + ", ".join(failed)
        )
    model = {
        "schema": RUNTIME_METHOD_GENERIC_SCHEMA,
        "status": "runtime-validated",
        "target": {
            "executable_sha256": plan["target"]["executable_sha256"],
            "process_id": plan["target"]["process_id"],
            "creation_filetime": plan["target"]["creation_filetime"],
        },
        "inputs": plan["inputs"],
        "inventory": file_identity(output_path),
        "status_receipt": file_identity(status_path),
        "counts": counts,
        "checks": checks,
        "owner_only": True,
    }
    _private_json(Path(plan["model_path"]), model)
    return {
        "schema": RUNTIME_METHOD_GENERIC_SCHEMA,
        "status": "runtime-validated",
        "target": model["target"],
        "counts": counts,
        "checks": checks,
        "inventory": model["inventory"],
    }


def load_runtime_method_generic_inventory(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
    expected_method_detail_inventory_sha256: str | None = None,
    include_methods: bool = True,
) -> dict[str, Any]:


    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    plan_path = _owner_file(
        model_path.parent / "runtime-method-generics-plan.private.json",
        label="plan",
    )
    status_path = _owner_file(
        model_path.parent / "runtime-method-generics-status.private.json",
        label="status",
    )
    model = read_json(model_path)
    plan = read_json(plan_path)
    status = read_json(status_path)
    target = model.get("target", {}).get("executable_sha256")
    if (
        model.get("schema") != RUNTIME_METHOD_GENERIC_SCHEMA
        or model.get("status") != "runtime-validated"
        or not model.get("checks")
        or not all(model["checks"].values())
        or model.get("inventory", {}).get("sha256")
        != file_identity(inventory_path)["sha256"]
        or model.get("status_receipt", {}).get("sha256")
        != file_identity(status_path)["sha256"]
        or plan.get("schema") not in (
            RUNTIME_METHOD_GENERIC_PLAN_SCHEMA,
            "alpha.runtime-reflection-method-generic-plan/v1",
        )
        or plan.get("status") != "prepared"
        or Path(plan.get("output_path", "")).expanduser().resolve()
        != inventory_path
        or Path(plan.get("model_path", "")).expanduser().resolve()
        != model_path
        or Path(plan.get("status_path", "")).expanduser().resolve()
        != status_path
        or plan.get("target", {}).get("executable_sha256") != target
        or (
            expected_executable_sha256 is not None
            and target != expected_executable_sha256.lower()
        )
        or (
            expected_method_detail_inventory_sha256 is not None
            and plan.get("inputs", {})
            .get("method_detail_inventory", {})
            .get("sha256")
            != expected_method_detail_inventory_sha256.lower()
        )
    ):
        raise AcquisitionError("runtime method generic binding is stale")
    if plan.get("schema") == RUNTIME_METHOD_GENERIC_PLAN_SCHEMA:
        counts, checks = _validate_capture(plan=plan, status=status)
    else:


        from alpha.p29 import _validate as _validate_reflection_capture
        counts, checks = _validate_reflection_capture(
            plan=plan, status=status
        )
    if counts != model.get("counts") or checks != model.get("checks"):
        raise AcquisitionError("runtime method generic validation is stale")
    raw = inventory_path.read_bytes()
    header = RUNTIME_METHOD_GENERIC_HEADER.unpack_from(raw)
    method_count, argument_count = header[5], header[7]
    records_start = RUNTIME_METHOD_GENERIC_HEADER.size
    arguments_start = (
        records_start + method_count * RUNTIME_METHOD_GENERIC_RECORD.size
    )
    arguments = (
        struct.unpack_from(f"<{argument_count}Q", raw, arguments_start)
        if argument_count
        else ()
    )
    methods: list[dict[str, Any]] = []


    if include_methods:
        for method_index, count, start in _record_rows(
            RUNTIME_METHOD_GENERIC_RECORD, raw, records_start, method_count
        ):
            if count:
                methods.append(
                    {
                        "method_index": method_index,
                        "generic_argument_descriptors_owner_only": list(
                            arguments[start : start + count]
                        ),
                    }
                )
    return {
        "schema": RUNTIME_METHOD_GENERIC_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": target},
        "counts": counts,
        "methods": methods,
        "identity": file_identity(inventory_path),
        "read_only_snapshot": True,
        "raw_native_addresses_owner_only": True,
    }


from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.p13 import RuntimeProcessProbe, _safe_path
from alpha.p19 import _implementation_digest
from alpha.c08 import load_bound_method_ancestry
from alpha.c09 import canonical
from alpha.c04 import _verify_files
from alpha.c01 import bind_runtime_process
from alpha.c04 import MappedPE
from alpha.p04 import derive_extent_candidates
from alpha.p16 import root_extent_memory_requests, replay_root_extent_observation
from alpha.c03 import derive_extent_load, observe_extent_words
from alpha.p14 import read_current_runtime_ranges, load_runtime_range_observation
from alpha.p15 import merged_ranges
from alpha.h02 import write_new_json
from alpha.p27 import RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER as GH, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD as GR, RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD as GF
from alpha.h02 import read_json, file_identity


def constructed_extent_sources(*, model_path, inventory_path, expected_target, identity_inventory, method_inventory):
    selected = {"constructed_model": file_identity(model_path), "constructed_inventory": file_identity(inventory_path)}
    model = read_json(model_path)
    if (model.get("schema") != "alpha.runtime-constructed-generic-layout/v1" or model.get("status") != "runtime-validated"
            or model.get("inventory") != selected["constructed_inventory"]
            or any(type(model.get("target", {}).get(key)) is not type(expected_target[key])
                   or model["target"][key] != expected_target[key] for key in ("process_id", "executable_sha256"))
            or any(model.get("checks", {}).get(key) is not True for key in (
                "all_constructed_generic_rows_valid", "generic_indexes_unique", "materialized_classes_unique",
                "all_constructed_fields_valid", "field_count_exact", "two_observations_match", "header_bound"))):
        raise AcquisitionError("class extent constructed domain is not a validated current capture")
    inputs = model.get("inputs", {})
    selected.update({"constructed_" + key: value for key, value in inputs.items()})
    selected["constructed_status"] = model["status_receipt"]
    if model.get("extent_operation") is not None:
        selected["constructed_extent_operation"] = model["extent_operation"]
    _verify_files(selected)
    reference = read_json(Path(inputs["type_reference_model"]["path"]))
    if (reference.get("schema") != "alpha.runtime-type-reference-inventory/v1"
            or reference.get("status") != "runtime-validated" or not reference.get("checks")
            or any(value is not True for value in reference["checks"].values())
            or canonical(reference.get("target", {})) != canonical(expected_target)
            or reference.get("inventory") != inputs["type_reference_inventory"]
            or any(reference.get("inputs", {}).get("type_identity_inventory", {}).get(key) != identity_inventory.get(key) for key in ("path", "bytes", "sha256"))
            or any(reference.get("inputs", {}).get("method_detail_inventory", {}).get(key) != method_inventory.get(key) for key in ("path", "bytes", "sha256"))):
        raise AcquisitionError("class extent constructed source belongs to another process or TypeDef domain")
    raw = Path(inventory_path).read_bytes()
    if len(raw) < GH.size:
        raise AcquisitionError("class extent constructed source header is truncated")
    header = GH.unpack_from(raw); count, fields = header[5:7]
    if (header[:5] != (b"ALPHACG1", 1, GH.size, GR.size, GF.size)
            or GH.size + count * GR.size + fields * GF.size != len(raw)
            or header[7:10] != tuple(expected_target[key] for key in ("process_id", "image_base_owner_only", "image_bytes"))
            or header[12] != expected_target["executable_sha256"].encode()
            or header[14:16] != tuple(inputs[key]["sha256"].encode() for key in ("native_helper_model", "native_semantics_model"))
            or count != model.get("counts", {}).get("constructed_generic_class_count")
            or fields != model.get("counts", {}).get("constructed_generic_field_count")):
        raise AcquisitionError("class extent constructed header/extent differs")
    classes, descriptors, indexes = set(), set(), set(); bindings = []; field_total = 0
    for row in GR.iter_unpack(raw[GH.size:GH.size + count * GR.size]):
        descriptor, current, index, definition, inst, _, klass, aliases, field_count, _ = row
        if (not descriptor or descriptor & 7 or descriptor in descriptors or not current or current & 7
                or index in indexes or definition >> 32 or not inst or not klass or klass & 7 or klass in classes or not aliases):
            raise AcquisitionError("class extent constructed class identity is invalid")
        classes.add(klass); descriptors.add(descriptor); indexes.add(index); field_total += field_count
        bindings.append(dict(domain="constructed", descriptor=descriptor, current_descriptor=current,
            generic_index=index, definition_index=definition, class_pointer=klass))
    if not classes or field_total != fields:
        raise AcquisitionError("class extent constructed class coverage is incomplete")
    _verify_files(selected)
    return bindings, selected


def capture_runtime_class_extents(*, binary, event_capture_plan, constructed_generic_model, constructed_generic_inventory,
                                  output_dir, wine, wineprefix, compiler=None, timeout=900.0):
    binary, event_capture_plan, output_dir = (_safe_path(Path(p)) for p in (binary, event_capture_plan, output_dir))
    selected = {"event_capture_plan": file_identity(event_capture_plan), "binary": file_identity(binary)}
    plan = read_json(event_capture_plan); selected.update(plan["inputs"])
    _verify_files(selected)
    target = plan["target"]
    if (not same_executable_path(target.get("executable_path"), binary)
            or target.get("executable_sha256") != selected["binary"]["sha256"]):
        raise AcquisitionError("class extent target executable differs")
    identity_plan = read_json(Path(selected["type_identity_plan"]["path"]))
    if canonical(identity_plan["target"]) != canonical(target):
        raise AcquisitionError("class extent nominal source process differs")
    constructed, extras = constructed_extent_sources(model_path=constructed_generic_model,
        inventory_path=constructed_generic_inventory, expected_target=target,
        identity_inventory=selected["type_identity_inventory"], method_inventory=selected["method_detail_inventory"])
    selected.update(extras)
    if any(output_dir.is_relative_to(Path(record["path"]).parent) for record in selected.values()):
        raise AcquisitionError("class extent output must not modify source directories")
    output_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
    if any(output_dir.iterdir()):
        raise AcquisitionError("class extent requires an empty output directory; existing evidence preserved")
    implementation = _implementation_digest()
    probe = RuntimeProcessProbe(binary=binary, wine=wine, wineprefix=wineprefix, build_dir=output_dir / "probe", compiler=compiler)
    current = probe()
    for key, value in target.items():
        actual = current.get("image_base" if key == "image_base_owner_only" else key)
        if type(actual) is not type(value) or actual != value:
            raise AcquisitionError("class extent source is not the current process instance")
    native = dict(selected, type_count=plan["contract"]["type_count"], image_base=current["image_base"], image_bytes=current["image_bytes"])
    (identities, methods, ancestry), source_inputs = load_bound_method_ancestry(native=native, binary=binary,
        process_identity=target, **{key: Path(selected[key]["path"]) for key in
            ("method_detail_model", "method_detail_inventory", "ancestry_inventory")})
    selected.update(source_inputs)
    with MappedPE(binary) as image:
        if image.size_of_image != current["image_bytes"]:
            raise AcquisitionError("class extent executable image size differs")
        operation = derive_extent_candidates(identity_rows=identities, method_rows=methods, ancestry_rows=ancestry,
            image=image, image_base=current["image_base"])
    load = derive_extent_load(operation); offset, width = (load["candidate"][key] for key in ("class_extent_offset", "class_extent_width"))
    nominal = [dict(domain="nominal", type_index=row[0], descriptor=row[2], class_pointer=row[3]) for row in identities]
    bindings = nominal + constructed
    classes = {row["class_pointer"] for row in bindings}
    if len({row["class_pointer"] for row in nominal}) != len(nominal) or any(not p or p & 7 for p in classes):
        raise AcquisitionError("class extent nominal class domain is not unique")
    requests = merged_ranges(root_extent_memory_requests(operation) + [(pointer + offset, width) for pointer in classes])
    def unchanged():
        _verify_files(selected)
        if _implementation_digest() != implementation:
            raise AcquisitionError("class extent implementation changed during capture")
    unchanged()
    with bind_runtime_process(current):
        observed = read_current_runtime_ranges(binary=binary, ranges=requests, output_dir=output_dir / "ranges",
            wine=wine, wineprefix=wineprefix, compiler=compiler)
    receipt = output_dir / "ranges" / "runtime-ranges.private.json"
    view = load_runtime_range_observation(receipt, expected_identity=current)
    if any(view.read(address, size) != observed[address] for address, size in requests):
        raise AcquisitionError("class extent sealed observations differ")
    code_replay = replay_root_extent_observation(operation, observed)
    evidence = observe_extent_words(operation, {pointer: view.read(pointer + offset, width) for pointer in classes})
    for row in evidence["rows"]: row["class_pointer"] = row.pop("class_index")
    evidence.update(process_identity_verified=True, two_observations_verified=True)
    unchanged()
    if probe() != current: raise AcquisitionError("class extent process changed during observation")
    unchanged()
    result = dict(schema="alpha.runtime-class-extent-inventory/v1", status="runtime-observed", target=target,
        identity=current, implementation=implementation, inputs=selected, operation=operation, observation=file_identity(receipt),
        evidence=evidence, class_bindings=bindings, code_replay=code_replay,
        counts=dict(nominal_class_count=len(nominal), constructed_class_count=len(constructed),
            unique_class_count=len(classes), shared_class_count=len(bindings) - len(classes),
            distinct_extent_count=evidence["distinct_extent_count"], zero_extent_count=evidence["zero_extent_count"],
            negative_copy_count=evidence["negative_copy_count"]),
        checks=dict(source_identities_unchanged=True, current_process_lifetime_verified=True, current_code_rederived=True,
            current_code_and_data_reobserved=True, exact_code_derived_word_width=True, all_class_bindings_observed=True,
            all_observations_two_passes=True, no_header_search_window=True, no_saved_extent_values=True),
        target_method_invoked=False, target_code_injection_used=False, native_type_sizes_proven=False,
        allocator_role_proven=False, object_payload_origin_proven=False, packing_proven=False, alignment_proven=False,
        metadata_complete=False, published=False)
    write_new_json(output_dir / "runtime-class-extents.private.json", result)
    return {key: result[key] for key in ("schema", "status", "target", "counts", "checks", "metadata_complete", "published")}
