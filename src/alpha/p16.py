import struct
from bisect import bisect_right
from collections import Counter
from pathlib import Path
from typing import Any

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError
from alpha.h04 import MemorySnapshot
from alpha.p01 import reflection_contract
from alpha.p14 import REFLECTION_BOOTSTRAP_SCHEMA
from alpha.p15 import RUNTIME_CLASS_SCHEMA
from alpha.c04 import MappedPE
from alpha.h02 import file_identity, read_json


REFLECTION_SEMANTICS_SCHEMA = "alpha.runtime-reflection-semantics/v1"
METHOD_NAME_DECODE_OPERATION_CODES = {"xor": 1, "add": 2}
METHOD_NAME_OWNER = "System.Reflection.MonoMethod"
NAME_OPERATION_DESCRIPTORS = (
    (
        "method.name",
        METHOD_NAME_OWNER,
        METHOD_NAME_OWNER,
        "cached-branch",
    ),
    (
        "field.name",
        "System.Reflection.MonoField",
        "System.Reflection.MonoField",
        "direct-return",
    ),
    (
        "property.name",
        "System.Reflection.MonoProperty",
        "System.Reflection.MonoProperty",
        "rsi-alias-return",
    ),
    (
        "parameter.name",
        "System.Reflection.MonoParameterInfo",
        "System.Reflection.ParameterInfo",
        "direct-return",
    ),
)
DIRECT_OBJECT_OPERATION_DESCRIPTORS = (
    (
        "field.type",
        "System.Reflection.MonoField",
        "System.Reflection.MonoField",
        "System.RuntimeType",
    ),
    (
        "parameter.type",
        "System.Reflection.MonoParameterInfo",
        "System.Reflection.ParameterInfo",
        "System.RuntimeType",
    ),
)
SENTINEL_FIELD_OPERATION_DESCRIPTORS = (
    (
        "parameter.default_value",
        "System.Reflection.MonoParameterInfo",
        "System.Reflection.MonoParameterInfo",
        ("System", "DBNull"),
        "sentinel-field-return",
    ),
)
DIRECT_DWORD_OPERATION_OWNERS = (
    ("field.attributes", "System.Reflection.MonoField"),
)
NESTED_WORD_OPERATION_OWNERS = (
    ("method.attributes", "System.Reflection.MonoMethod"),
)
NATIVE_TYPE_DESCRIPTOR_OPERATION_OWNERS = (
    ("type.handle", "System.RuntimeType"),
)
NATIVE_TYPE_FLAG_OPERATION_DESCRIPTORS = (
    (
        "type.is_byref",
        "System.RuntimeType",
        "System.Type",
    ),
)
TYPE_FROM_HANDLE_OPERATION_OWNERS = (
    ("type.from_handle", "System.Type"),
)
PROPERTY_ACCESSOR_OPERATIONS = (
    ("property.getter", "get_"),
    ("property.setter", "set_"),
)
MIN_PROPERTY_ACCESSOR_NAME_SUPPORT = 2
PARAMETER_FLAG_OPERATION_MASKS = (
    ("parameter.is_in", 0x01),
    ("parameter.is_out", 0x02),
    ("parameter.is_optional", 0x10),
)


def _managed_string(
    snapshot: MemorySnapshot,
    pointer: int,
    *,
    string_class: int,
    maximum: int = 512,
) -> str | None:
    if not pointer or maximum < 1:
        return None
    header = snapshot.qwords(pointer, 1)
    raw_length = snapshot.read(pointer + 16, 4) if header else None
    if not header or header[0] != string_class or raw_length is None:
        return None
    length = int.from_bytes(raw_length, "little", signed=True)
    if not 0 < length <= maximum:
        return None
    raw = snapshot.read(pointer + 20, length * 2)
    if raw is None:
        return None
    try:
        value = raw.decode("utf-16-le")
    except UnicodeDecodeError:
        return None


    if any(character < "\x20" for character in value):
        return None
    return value


def _dominant_cached_string_field(
    *,
    snapshot: MemorySnapshot,
    class_pointer: int,
    string_class: int,
    scan_qwords: int = 10,
    getter_fields: set[int] | None = None,
) -> dict[str, Any]:
    support: Counter[int] = Counter()
    object_count = 0
    representative: dict[str, Any] | None = None
    for reference in snapshot.references(class_pointer):
        values = snapshot.qwords(reference, scan_qwords)
        if not values or values[0] != class_pointer:
            continue
        object_count += 1
        for field, value in enumerate(values):
            name = _managed_string(
                snapshot, value, string_class=string_class
            )
            if name is None:
                continue
            support[field] += 1
            if representative is None or support[field] > support.get(
                representative["field_qword"], 0
            ):
                representative = {
                    "object_pointer": reference,
                    "field_qword": field,
                    "string_pointer": value,
                    "string_length": len(name),
                }
    if not support:
        raise AcquisitionError("runtime reflection cached name field is unavailable")
    strongest = max(support.values())
    selected = (
        [field for field, count in support.items() if field in getter_fields and count >= 8]
        if getter_fields is not None
        else [field for field, count in support.items() if count == strongest]
    )
    if len(selected) != 1 or strongest < 8:
        raise AcquisitionError(
            "runtime reflection cached name field is not unique "
            f"(candidates={len(selected)}, support={strongest})"
        )
    field = selected[0]
    strongest = support[field]
    for reference in snapshot.references(class_pointer):
        values = snapshot.qwords(reference, scan_qwords)
        if not values or values[0] != class_pointer:
            continue
        name = _managed_string(
            snapshot, values[field], string_class=string_class
        )
        if name is not None:
            representative = {
                "object_pointer": reference,
                "field_qword": field,
                "string_pointer": values[field],
                "string_length": len(name),
            }
            break
    if representative is None:
        raise AcquisitionError("runtime reflection name representative is unavailable")
    return {
        "object_reference_count": object_count,
        "candidate_field_count": len(support),
        "support_by_field": dict(sorted(support.items())),
        "getter_candidate_fields": sorted(getter_fields) if getter_fields is not None else None,
        "selected_field_qword": field,
        "selected_field_support": strongest,
        "representative": representative,
    }


def _dominant_object_field(
    *,
    snapshot: MemorySnapshot,
    class_pointer: int,
    target_class_pointer: int,
    scan_qwords: int = 10,
) -> dict[str, Any]:
    support: Counter[int] = Counter()
    object_count = 0
    for reference in snapshot.references(class_pointer):
        values = snapshot.qwords(reference, scan_qwords)
        if not values or values[0] != class_pointer:
            continue
        object_count += 1
        for field, value in enumerate(values):
            target = snapshot.qwords(value, 1) if value else None
            if target and target[0] == target_class_pointer:
                support[field] += 1
    if not support:
        raise AcquisitionError("runtime reflection object field is unavailable")
    strongest = max(support.values())
    selected = [field for field, count in support.items() if count == strongest]
    if len(selected) != 1 or strongest < 8:
        raise AcquisitionError(
            "runtime reflection object field is not unique "
            f"(candidates={len(selected)}, support={strongest})"
        )
    return {
        "object_reference_count": object_count,
        "candidate_field_count": len(support),
        "support_by_field": dict(sorted(support.items())),
        "selected_field_qword": selected[0],
        "selected_field_support": strongest,
    }


def _derive_native_descriptor_operations(*, snapshot, image, classes, class_addresses):

    from alpha.p04 import derive
    descriptor_evidence, flag_evidence, operations = [], [], []
    method_pointers = _method_pointer_boundaries(classes)

    def domain(owner):
        owners = [row for row in classes.get("classes", []) if row.get("runtime_owner") == owner]
        if (len(owners) != 1 or type(owners[0].get("class_pointer")) is not int
                or owners[0]["class_pointer"] <= 0
                or owners[0]["class_pointer"] != class_addresses.get(owner)):
            raise AcquisitionError("descriptor getter bootstrap owner is absent or ambiguous")
        rows = [row for row in classes.get("methods", []) if row.get("runtime_owner") == owner]
        if (type(owners[0].get("method_count")) is not int or not rows
                or owners[0]["method_count"] != len(rows)
                or any(type(row.get("class_pointer")) is not int
                       or row["class_pointer"] != owners[0]["class_pointer"] for row in rows)):
            raise AcquisitionError("descriptor getter complete method owner domain differs")
        metadata = [row.get("metadata_pointer") for row in rows]
        if (any(type(value) is not int or not 0 < value < 1 << 64 for value in metadata)
                or len(set(metadata)) != len(metadata)):
            raise AcquisitionError("descriptor getter method identity is invalid or duplicated")
        methods, unavailable = [], []
        for row in rows:
            pointer = row.get("method_pointer")
            if type(pointer) is not int or not 0 <= pointer < 1 << 64:
                raise AcquisitionError("descriptor getter method pointer is invalid")
            if pointer == 0:
                unavailable.append(dict(metadata_pointer=row["metadata_pointer"], method_pointer=pointer,
                                        reason="no-current-native-entry"))
                continue
            code = _method_code(
                snapshot=snapshot, image=image, method_pointer=pointer,
                method_pointers=method_pointers,
            )
            if code is None:
                raise AcquisitionError("descriptor getter nonnull method code is unavailable")
            methods.append(dict(metadata_pointer=row["metadata_pointer"], method_pointer=pointer, code=code))
        return methods, {row["metadata_pointer"]: row for row in rows}, unavailable

    for operation_key, object_owner in NATIVE_TYPE_DESCRIPTOR_OPERATION_OWNERS:
        flags = [row for row in NATIVE_TYPE_FLAG_OPERATION_DESCRIPTORS if row[1] == object_owner]
        if len(flags) != 1:
            raise AcquisitionError("descriptor getter owner/flag relation is ambiguous")
        flag_key, _, flag_owner = flags[0]
        qwords, qword_rows, unavailable_qwords = domain(object_owner)
        flag_methods, flag_rows, unavailable_flags = domain(flag_owner)
        relation = derive(qword_methods=qwords, flag_methods=flag_methods,
            object_references=snapshot.references(class_addresses[object_owner]),
            read=snapshot.read, object_class=class_addresses[object_owner])
        selected_field = relation["selected_field_qword"]


        import hashlib
        import json
        samples = relation["samples"]
        proof = {key: value for key, value in relation.items() if key != "samples"}
        proof["sample_rows_sha256"] = hashlib.sha256(
            json.dumps(samples, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        proof["unavailable_qword_method_code"] = unavailable_qwords
        proof["unavailable_flag_method_code"] = unavailable_flags
        proof["qword_owner_method_count"] = len(qword_rows)
        proof["flag_owner_method_count"] = len(flag_rows)
        proof["all_nonnull_owner_method_code_observed"] = True
        qword = relation["qword_getter"]
        flag = relation["flag_getter"]
        descriptor_evidence.append(dict(operation_key=operation_key, runtime_owner=object_owner,
            class_pointer=class_addresses[object_owner], selected_field_qword=selected_field,
            selected_field_support=relation["readable_object_count"],
            object_reference_count=relation["object_reference_count"],
            candidate_field_count=relation["pair_candidate_count"],
            support_by_field={selected_field: relation["readable_object_count"]},
            field_selection="unique-independent-getter-data-flow-pair",
            descriptor_field_data_flow_proven=True, native_type_enum_convention_used=False,
            fixed_descriptor_length_used=False, getter_relation=proof))
        flag_proof = flag["proof"]
        flag_evidence.append(dict(operation_key=flag_key, object_runtime_owner=object_owner,
            method_runtime_owner=flag_owner, derived_descriptor_field_qword=selected_field,
            derived_flag_byte_offset=flag_proof["descriptor_flag_byte_offset"],
            derived_flag_mask=flag_proof["descriptor_flag_mask"],
            readable_object_count=relation["readable_object_count"],
            set_count=relation["set_count"], clear_count=relation["clear_count"],
            distinct_set_descriptor_count=relation["distinct_set_descriptor_count"],
            distinct_clear_descriptor_count=relation["distinct_clear_descriptor_count"],
            descriptor_field_data_flow_proven=True, native_type_enum_convention_used=False,
            flag_computation_proof=flag_proof))
        for key, owner, selected, rows, label in (
                (operation_key, object_owner, qword, qword_rows, "get_TypeHandle"),
                (flag_key, flag_owner, flag, flag_rows, "get_IsByRef")):
            method = rows[selected["metadata_pointer"]]
            operations.append(dict(key=key, runtime_owner=owner, runtime_name=label,
                method_index=method["method_index"], metadata_pointer=method["metadata_pointer"],
                method_pointer=method["method_pointer"], semantic_identity_resolved=True,
                resolution="derived-current-getter-data-flow-and-distinct-flag-domain"))
    return descriptor_evidence, flag_evidence, operations


def _loads_rax_from_rcx_field(code: bytes, byte_offset: int) -> bool:
    return _returns_object_field(code, byte_offset, cached=True)


def _returns_derived_string_field(code: bytes, byte_offset: int) -> bool:
    return _returns_object_field(code, byte_offset, cached=True) or _returns_object_field(
        code, byte_offset, cached=False
    )


def _directly_returns_rcx_field(code: bytes, byte_offset: int) -> bool:
    return _returns_object_field(code, byte_offset, cached=False)


def _guarded_qword_getter_shape(code: bytes) -> int | None:
    if len(code) < 18 or not code.startswith(b"\x48\x83\xec"):
        return None
    stack_bytes = code[3]
    if code[4:7] != b"\x48\x85\xc9":
        return None
    cursor = 7
    if code[cursor] == 0x74:
        cursor += 2
    elif code[cursor : cursor + 2] == b"\x0f\x84":
        cursor += 6
    else:
        return None
    if code[cursor : cursor + 3] == b"\x48\x8b\x41":
        byte_offset = code[cursor + 3]
        cursor += 4
    elif code[cursor : cursor + 3] == b"\x48\x8b\x81":
        byte_offset = struct.unpack_from("<i", code, cursor + 3)[0]
        cursor += 7
    else:
        return None
    if byte_offset < 0 or code[cursor : cursor + 4] != bytes(
        (0x48, 0x83, 0xC4, stack_bytes)
    ):
        return None
    cursor += 4
    return byte_offset if code[cursor : cursor + 1] == b"\xc3" else None


def _returns_rsi_alias_field(code: bytes, byte_offset: int) -> bool:
    return _returns_object_field(code, byte_offset, cached=False)


def _returns_sentinel_field(code: bytes, byte_offset: int) -> bool:
    return _returns_object_field(
        code, byte_offset, cached=False, allow_call_result=True
    )


def _parameter_flag_getter_shape(code: bytes) -> tuple[int, int] | None:
    if code.startswith(b"\x0f\xb6\x41") and len(code) >= 7:
        byte_offset = code[3]
        cursor = 4
    elif code.startswith(b"\x0f\xb6\x81") and len(code) >= 10:
        byte_offset = struct.unpack_from("<i", code, 3)[0]
        cursor = 7
    else:
        return None
    if byte_offset < 0 or code[cursor : cursor + 1] != b"\x24":
        return None
    mask = code[cursor + 1]
    if not mask or mask & (mask - 1):
        return None
    cursor += 2
    shift = mask.bit_length() - 1
    if shift:
        if shift == 1 and code[cursor : cursor + 2] == b"\xd0\xe8":
            cursor += 2
        elif code[cursor : cursor + 3] == b"\xc0\xe8" + bytes((shift,)):
            cursor += 3
        else:
            return None
    return (byte_offset, mask) if code[cursor : cursor + 1] == b"\xc3" else None


def _direct_dword_getter_shape(code: bytes) -> int | None:
    if code.startswith(b"\x8b\x41") and len(code) >= 4 and code[3] == 0xC3:
        return code[2]
    if code.startswith(b"\x8b\x81") and len(code) >= 7 and code[6] == 0xC3:
        byte_offset = struct.unpack_from("<i", code, 2)[0]
        return byte_offset if byte_offset >= 0 else None
    return None


def _nested_word_getter_shape(code: bytes) -> tuple[int, int] | None:
    if (
        len(code) >= 9
        and code.startswith(b"\x48\x8b\x41")
        and code[4:7] == b"\x0f\xb7\x40"
        and code[8] == 0xC3
    ):
        return code[3], code[7]
    if (
        len(code) >= 15
        and code.startswith(b"\x48\x8b\x81")
        and code[7:10] == b"\x0f\xb7\x80"
        and code[14] == 0xC3
    ):
        object_offset = struct.unpack_from("<i", code, 3)[0]
        nested_offset = struct.unpack_from("<i", code, 10)[0]
        if object_offset >= 0 and nested_offset >= 0:
            return object_offset, nested_offset
    return None


def _nested_byte_mask_getter_shape(
    code: bytes,
) -> tuple[int, int, int] | None:
    for position in range(min(32, len(code))):
        if code[position : position + 3] != b"\x48\x8b\x41":
            continue
        if position + 12 > len(code):
            continue
        object_offset = code[position + 3]
        cursor = position + 4
        if code[cursor : cursor + 3] != b"\x0f\xb6\x40":
            continue
        nested_offset = code[cursor + 3]
        cursor += 4
        if code[cursor : cursor + 1] != b"\x24":
            continue
        mask = code[cursor + 1]
        if not mask or mask & (mask - 1):
            continue
        cursor += 2
        shift = mask.bit_length() - 1
        if shift:
            if shift == 1 and code[cursor : cursor + 2] == b"\xd0\xe8":
                cursor += 2
            elif code[cursor : cursor + 3] == b"\xc0\xe8" + bytes((shift,)):
                cursor += 3
            else:
                continue
        epilogue = code[cursor : cursor + 5]
        if epilogue == b"\x48\x83\xc4" + code[3:4] + b"\xc3":
            return object_offset, nested_offset, mask
    return None


def _type_from_handle_shape(code: bytes) -> dict[str, int] | None:
    if (
        len(code) < 36
        or code[:9] != b"\x48\x83\xec\x28\x48\x85\xc9\x74\x14"
        or code[9:11] != b"\xb2\x01"
        or code[11] != 0xE8
        or code[16:19] != b"\x48\x8d\x48"
        or code[20:25] != b"\x48\x83\xc4\x28\xe9"
        or code[29:36] != b"\x31\xc0\x48\x83\xc4\x28\xc3"
    ):
        return None
    object_adjust = code[19]
    if not object_adjust or object_adjust % 8:
        return None
    return {
        "native_handle_call_offset": 11,
        "managed_type_tail_offset": 24,
        "native_object_adjust": object_adjust,
    }


def _property_accessor_getter_shape(code: bytes, byte_offset: int) -> bool:
    if not 0 <= byte_offset <= 0x7F:
        return False
    field_load = b"\x48\x8b\x46" + bytes((byte_offset,))
    common = all(
        pattern in code
        for pattern in (
            b"\x89\xd3",
            b"\x48\x89\xce",
            field_load,
            b"\x48\x85\xc0",
            b"\x84\xdb",
            b"\x83\xe1\x07",
            b"\x83\xf9\x06",
            b"\xc3",
        )
    )
    return common


def _relative_call_target(
    code: bytes,
    *,
    method_pointer: int,
    call_offset: int,
) -> int | None:
    if (
        call_offset < 0
        or call_offset + 5 > len(code)
        or code[call_offset] != 0xE8
    ):
        return None
    displacement = struct.unpack_from("<i", code, call_offset + 1)[0]
    return method_pointer + call_offset + 5 + displacement


def _x64_instruction_stream(
    code: bytes, *, method_pointer: int
) -> list[dict[str, Any]]:
    try:
        from capstone import CS_AC_WRITE, Cs, CS_ARCH_X86, CS_GRP_JUMP, CS_MODE_64
        from capstone.x86 import X86_OP_IMM, X86_OP_MEM, X86_OP_REG
    except ImportError as error:
        raise AcquisitionError(
            "runtime semantic decoding requires the declared capstone dependency"
        ) from error

    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    decoder.detail = True
    register_indices = {
        "rax": 0,
        "rcx": 1,
        "rdx": 2,
        "rbx": 3,
        "rsp": 4,
        "rbp": 5,
        "rsi": 6,
        "rdi": 7,
        "r8": 8,
        "r9": 9,
        "r10": 10,
        "r11": 11,
        "r12": 12,
        "r13": 13,
        "r14": 14,
        "r15": 15,
    }
    aliases = {
        alias: base
        for base, names in {
            "rax": ("eax", "ax", "al", "ah"),
            "rcx": ("ecx", "cx", "cl", "ch"),
            "rdx": ("edx", "dx", "dl", "dh"),
            "rbx": ("ebx", "bx", "bl", "bh"),
            "rsp": ("esp", "sp", "spl"),
            "rbp": ("ebp", "bp", "bpl"),
            "rsi": ("esi", "si", "sil"),
            "rdi": ("edi", "di", "dil"),
        }.items()
        for alias in names
    }

    def register_index(register: int) -> int | None:
        name = decoder.reg_name(register)
        if not isinstance(name, str):
            return None
        name = aliases.get(name, name)
        if name not in register_indices and name.endswith(("d", "w", "b")):
            candidate = name[:-1]
            name = candidate if candidate in register_indices else name
        return register_indices.get(name)

    output: list[dict[str, Any]] = []
    try:
        decoded_instructions = list(decoder.disasm(code, method_pointer))
    except Exception as error:
        raise AcquisitionError(
            "runtime method x64 instructions could not be decoded"
        ) from error
    for instruction in decoded_instructions:
        offset = instruction.address - method_pointer
        operands = instruction.operands
        try:
            written_registers = instruction.regs_access()[1]
        except Exception as error:
            raise AcquisitionError(
                "runtime method register effects could not be decoded"
            ) from error
        record: dict[str, Any] = {
            "offset": offset,
            "size": instruction.size,
            "kind": "other",
            "writes": tuple(
                index
                for index in (
                    register_index(register)
                    for register in written_registers
                )
                if index is not None
            ),
            "memory_writes": tuple(
                (
                    register_index(operand.mem.base),
                    bool(operand.mem.index),
                    operand.mem.disp,
                    operand.size,
                )
                for operand in operands
                if operand.type == X86_OP_MEM and operand.access & CS_AC_WRITE
            ),
        }
        if instruction.mnemonic.startswith("ret"):
            record["kind"] = "return"
        elif instruction.mnemonic in ("int3", "ud2"):
            record["kind"] = "trap"
        elif instruction.mnemonic == "call":
            record["kind"] = "call"
            record["target"] = (
                operands[0].imm
                if operands and operands[0].type == X86_OP_IMM
                else None
            )
        elif instruction.mnemonic == "jmp":
            record["kind"] = "jump"
            record["target"] = (
                operands[0].imm - method_pointer
                if operands and operands[0].type == X86_OP_IMM
                else None
            )
        elif instruction.group(CS_GRP_JUMP):
            record["kind"] = "branch"
            record["target"] = (
                operands[0].imm - method_pointer
                if operands and operands[0].type == X86_OP_IMM
                else None
            )
        elif instruction.mnemonic in ("mov", "movabs") and len(operands) == 2:
            destination, source = operands
            if destination.type == X86_OP_REG:
                destination_index = register_index(destination.reg)
                if destination_index is not None:
                    if source.type == X86_OP_IMM and destination.size == 8:
                        record.update(
                            kind="immediate",
                            destination=destination_index,
                            value=source.imm & 0xFFFFFFFFFFFFFFFF,
                        )
                    elif source.type == X86_OP_REG:
                        record.update(
                            kind="move-register",
                            destination=destination_index,
                            source=register_index(source.reg),
                            full_width=destination.size == 8 and source.size == 8,
                            destination_size=destination.size,
                            source_size=source.size,
                        )
                    elif source.type == X86_OP_MEM:
                        record.update(
                            kind="load",
                            destination=destination_index,
                            base=register_index(source.mem.base),
                            displacement=source.mem.disp,
                            indexed=bool(source.mem.index),
                            full_width=destination.size == 8,
                        )
            elif destination.type == X86_OP_MEM and source.type == X86_OP_REG:
                record.update(
                    kind="store",
                    destination=register_index(source.reg),
                    base=register_index(destination.mem.base),
                    displacement=destination.mem.disp,
                    indexed=bool(destination.mem.index),
                    full_width=destination.size == 8 and source.size == 8,
                )
        elif instruction.mnemonic == "lea" and len(operands) == 2:
            destination, source = operands
            if destination.type == X86_OP_REG and source.type == X86_OP_MEM:
                record.update(
                    kind="lea",
                    destination=register_index(destination.reg),
                    base=register_index(source.mem.base),
                    displacement=source.mem.disp,
                    indexed=bool(source.mem.index),
                    full_width=destination.size == 8,
                )
        elif instruction.mnemonic == "xor" and len(operands) == 2:
            destination, source = operands
            if destination.type == X86_OP_REG and source.type == X86_OP_REG:
                record.update(
                    kind="xor-register",
                    destination=register_index(destination.reg),
                    source=register_index(source.reg),
                    full_width=destination.size == 8 and source.size == 8,
                )
            elif destination.type == X86_OP_REG and source.type == X86_OP_MEM:
                record.update(
                    kind="xor-memory-right",
                    destination=register_index(destination.reg),
                    base=register_index(source.mem.base),
                    displacement=source.mem.disp,
                    indexed=bool(source.mem.index),
                    full_width=destination.size == 8 and source.size == 8,
                )
        elif instruction.mnemonic == "add" and len(operands) == 2:
            destination, source = operands
            if destination.type == X86_OP_REG and source.type == X86_OP_REG:
                record.update(
                    kind="add-register",
                    destination=register_index(destination.reg),
                    source=register_index(source.reg),
                    full_width=destination.size == 8 and source.size == 8,
                )
            elif destination.type == X86_OP_REG and source.type == X86_OP_MEM:
                record.update(
                    kind="add-memory-right",
                    destination=register_index(destination.reg),
                    base=register_index(source.mem.base),
                    displacement=source.mem.disp,
                    indexed=bool(source.mem.index),
                    full_width=destination.size == 8 and source.size == 8,
                )
        output.append(record)
    return output


def _method_name_dataflow(
    code: bytes,
    *,
    method_pointer: int,
    input_state: tuple[Any, ...],
    cached_name_byte_offset: int | None,
) -> dict[str, Any]:
    instructions = _x64_instruction_stream(code, method_pointer=method_pointer)
    by_offset = {
        int(instruction["offset"]): instruction for instruction in instructions
    }
    offsets = tuple(sorted(by_offset))
    next_offsets = {
        offset: offsets[index + 1] if index + 1 < len(offsets) else None
        for index, offset in enumerate(offsets)
    }
    calls: list[dict[str, Any]] = []
    cached_load_seen = False
    cached_stores: list[dict[str, Any]] = []
    node_accesses: list[dict[str, Any]] = []
    memory_writes_observed: list[dict[str, Any]] = []
    decoded_values: set[tuple[Any, ...]] = set()
    return_values: set[tuple[Any, ...]] = set()
    control_flow_complete = True
    memory_effects_complete = True
    return_count = 0
    unresolved_return_count = 0
    worklist: list[tuple[int, dict[int, tuple[Any, ...]]]] = (
        [(offsets[0], {1: input_state})] if offsets else []
    )
    visited: set[tuple[int, tuple[tuple[int, tuple[Any, ...]], ...]]] = set()

    def schedule(instruction: dict[str, Any], states: dict[int, tuple[Any, ...]]) -> None:
        nonlocal control_flow_complete
        offset = int(instruction["offset"])
        kind = instruction["kind"]
        fallthrough = next_offsets[offset]
        target = instruction.get("target")
        successors: tuple[int | None, ...]
        if kind in ("return", "trap"):
            successors = ()
        elif kind == "jump":
            successors = (int(target),) if isinstance(target, int) else ()
            if not isinstance(target, int) or int(target) not in by_offset:
                control_flow_complete = False
        elif kind == "branch":
            successors = (
                fallthrough,
                int(target) if isinstance(target, int) else None,
            )
            if (
                fallthrough is None
                or not isinstance(target, int)
                or int(target) not in by_offset
            ):
                control_flow_complete = False
        else:
            successors = (fallthrough,)
            if fallthrough is None:
                control_flow_complete = False
        for successor in successors:
            if successor is not None and successor in by_offset:
                worklist.append((successor, dict(states)))

    while worklist:
        offset, states = worklist.pop()
        identity = (offset, tuple(sorted(states.items())))
        if identity in visited:
            continue
        visited.add(identity)
        if len(visited) > 4096:
            raise AcquisitionError("runtime method name control flow is excessive")
        instruction = by_offset[offset]
        kind = instruction["kind"]
        if kind == "immediate":
            states[int(instruction["destination"])] = (
                "constant", int(instruction["value"])
            )
            schedule(instruction, states)
            continue
        if kind in ("push", "other"):
            for base, indexed, displacement, width in instruction["memory_writes"]:
                base_state = states.get(base) if isinstance(base, int) else None
                if base_state is not None and base_state[:1] in (
                    ("object",), ("metadata",), ("node",)
                ):
                    memory_writes_observed.append({
                        "base": base_state,
                        "indexed": indexed,
                        "displacement": displacement,
                        "width": width,
                        "source": None,
                    })
                    memory_effects_complete = False
            for register in instruction.get("writes", ()):
                states.pop(int(register), None)
            schedule(instruction, states)
            continue
        if kind == "pop":
            register = instruction.get("register")
            if isinstance(register, int):
                states.pop(register, None)
            schedule(instruction, states)
            continue
        if kind == "call":
            target = instruction.get("target")
            calls.append({
                "offset": offset,
                "target": target,
                "rcx": states.get(1),
                "rdx": states.get(2),
            })
            for register in (1, 2, 8, 9, 10, 11):
                states.pop(register, None)
            states[0] = (
                ("call-result", target, offset)
                if isinstance(target, int)
                else ("unknown",)
            )
            schedule(instruction, states)
            continue
        if kind == "return":
            return_count += 1
            value = states.get(0)
            if value is not None and value[:1] != ("unknown",):
                return_values.add(value)
            else:
                unresolved_return_count += 1
            schedule(instruction, states)
            continue
        if kind in ("jump", "branch"):
            schedule(instruction, states)
            continue
        if kind == "lea":
            destination = instruction.get("destination")
            base = instruction["base"]
            if (
                isinstance(destination, int)
                and not instruction["indexed"]
                and instruction["full_width"]
                and isinstance(base, int)
                and int(instruction["displacement"]) == 0
                and base in states
            ):
                states[int(destination)] = states[base]
            else:
                if isinstance(destination, int):
                    states.pop(destination, None)
            schedule(instruction, states)
            continue
        destination_value = instruction.get("destination")
        destination = (
            int(destination_value)
            if isinstance(destination_value, int)
            else None
        )
        if kind == "load":
            if destination is None:
                schedule(instruction, states)
                continue
            base = instruction["base"]
            displacement = int(instruction["displacement"])
            base_state = states.get(base) if isinstance(base, int) else None
            if (
                instruction["indexed"]
                or displacement < 0
                or displacement % 8
                or base_state is None
                or not instruction["full_width"]
            ):
                states.pop(destination, None)
                schedule(instruction, states)
                continue
            if (
                cached_name_byte_offset is not None
                and base_state == ("object",)
                and displacement == cached_name_byte_offset
            ):
                cached_load_seen = True
                states[destination] = ("cached-name", displacement)
            elif base_state == ("object",):
                states[destination] = ("metadata", displacement)
            elif base_state[:1] == ("metadata",):
                states[destination] = (
                    "node", base_state[1], displacement
                )
            elif base_state[:1] == ("node",):
                states[destination] = (
                    "encoded", base_state[1], base_state[2], displacement
                )
            else:
                states.pop(destination, None)
            schedule(instruction, states)
            continue
        if kind == "move-register":
            source = instruction.get("source")
            if destination is not None:
                source_state = states.get(source) if isinstance(source, int) else None
                if instruction["full_width"] and source_state is not None:
                    states[destination] = source_state
                elif (
                    instruction["destination_size"] == 4
                    and instruction["source_size"] == 4
                    and source_state is not None
                    and source_state[:1] == ("call-result",)
                ):
                    states[destination] = source_state
                else:
                    states.pop(destination, None)
            schedule(instruction, states)
            continue
        if kind == "store":
            base = instruction["base"]
            displacement = int(instruction["displacement"])
            base_state = states.get(base) if isinstance(base, int) else None
            source_state = states.get(destination) if destination is not None else None
            if base_state is not None and base_state[:1] in (
                ("object",), ("metadata",), ("node",)
            ):
                memory_writes_observed.append({
                    "base": base_state,
                    "indexed": instruction["indexed"],
                    "displacement": displacement,
                    "width": 8 if instruction["full_width"] else 0,
                    "source": source_state,
                })
            if (
                (not instruction["full_width"] or instruction["indexed"])
                and base_state is not None
                and base_state[:1] in (("object",), ("metadata",), ("node",))
            ):
                memory_effects_complete = False
            if (
                instruction["full_width"]
                and not instruction["indexed"]
                and base_state is not None
                and displacement >= 0
                and displacement % 8 == 0
            ):
                record = {
                    "offset": int(instruction["offset"]),
                    "base": base_state,
                    "displacement": displacement,
                    "source": source_state,
                }
                if (
                    cached_name_byte_offset is not None
                    and base_state == ("object",)
                    and displacement == cached_name_byte_offset
                ):
                    cached_stores.append(record)
                if base_state[:1] in (("metadata",), ("node",)):
                    node_accesses.append(record)
            schedule(instruction, states)
            continue
        if kind in (
            "xor-register", "xor-memory-right", "add-register", "add-memory-right"
        ):
            if destination is None or not instruction["full_width"]:
                if destination is not None:
                    states.pop(destination, None)
                schedule(instruction, states)
                continue
            left = states.get(destination)
            operation = kind.split("-", 1)[0]
            if kind.endswith("-register"):
                source = instruction.get("source")
                right = states.get(source) if isinstance(source, int) else None
            else:
                base = instruction["base"]
                displacement = int(instruction["displacement"])
                base_state = states.get(base) if isinstance(base, int) else None
                right = (
                    ("encoded", base_state[1], base_state[2], displacement)
                    if (
                        not instruction["indexed"]
                        and base_state is not None
                        and base_state[:1] == ("node",)
                        and displacement >= 0
                        and displacement % 8 == 0
                    )
                    else None
                )
            if left is not None or right is not None:
                pair = (left, right)
                encoded = next(
                    (value for value in pair if value and value[:1] == ("encoded",)),
                    None,
                )
                constant = next(
                    (value for value in pair if value and value[:1] == ("constant",)),
                    None,
                )
                if encoded is not None and constant is not None and constant[1]:
                    decoded = (
                        "decoded", operation, encoded[1], encoded[2],
                        encoded[3], constant[1]
                    )
                    states[destination] = decoded
                    decoded_values.add(decoded)
                elif (
                    constant is not None
                    and any(value and value[:1] == ("call-result",) for value in pair)
                ):
                    call_result = next(
                        value for value in pair
                        if value and value[:1] == ("call-result",)
                    )
                    states[destination] = (
                        "transformed-call-result", operation,
                        call_result, constant[1]
                    )
                elif (
                    left is not None
                    and right is not None
                    and left[:1] == ("constant",)
                    and right[:1] == ("constant",)
                ):
                    states[destination] = (
                        "constant",
                        (left[1] ^ right[1]) if operation == "xor"
                        else (left[1] + right[1]) & 0xFFFFFFFFFFFFFFFF,
                    )
                else:
                    states.pop(destination, None)
            schedule(instruction, states)
            continue
        for register in instruction.get("writes", ()):
            states.pop(int(register), None)
        schedule(instruction, states)
    return {
        "calls": calls,
        "cached_load_seen": cached_load_seen,
        "cached_stores": cached_stores,
        "node_accesses": node_accesses,
        "memory_writes_observed": memory_writes_observed,
        "decoded_values": decoded_values,
        "return_values": return_values,
        "return_count": return_count,
        "unresolved_return_count": unresolved_return_count,
        "control_flow_complete": control_flow_complete,
        "memory_effects_complete": memory_effects_complete,
    }


def _returns_object_field(
    code: bytes,
    byte_offset: int,
    *,
    cached: bool,
    allow_call_result: bool = False,
) -> bool:
    if not code or byte_offset < 0 or byte_offset % 8:
        return False
    try:
        analysis = _method_name_dataflow(
            code,
            method_pointer=0,
            input_state=("object",),
            cached_name_byte_offset=byte_offset if cached else None,
        )
    except AcquisitionError:
        return False
    expected = (
        ("cached-name", byte_offset)
        if cached
        else ("metadata", byte_offset)
    )
    protected_field_overwritten = any(
        write["base"] == ("object",)
        and (
            write["indexed"]
            or write["width"] == 0
            or (
                write["displacement"] < byte_offset + 8
                and write["displacement"] + write["width"] > byte_offset
            )
        )
        and not (
            cached
            and write["displacement"] == byte_offset
            and write["width"] == 8
            and write["source"] is not None
            and write["source"][:1] == ("call-result",)
        )
        for write in analysis["memory_writes_observed"]
    )
    return (
        analysis["control_flow_complete"]
        and not protected_field_overwritten
        and analysis["return_count"] > 0
        and analysis["unresolved_return_count"] == 0
        and expected in analysis["return_values"]
        and all(
            value == expected
            or ((cached or allow_call_result) and value[:1] == ("call-result",))
            for value in analysis["return_values"]
        )
    )


def _derive_method_name_decoder(
    code: bytes,
    *,
    method_pointer: int,
    cached_name_byte_offset: int,
) -> dict[str, Any]:
    if (
        not code
        or method_pointer <= 0
        or cached_name_byte_offset < 0
        or cached_name_byte_offset % 8
    ):
        raise AcquisitionError("runtime method name decoder input is invalid")
    analysis = _method_name_dataflow(
        code,
        method_pointer=method_pointer,
        input_state=("object",),
        cached_name_byte_offset=cached_name_byte_offset,
    )
    if not analysis["cached_load_seen"]:
        raise AcquisitionError("runtime method name cached path is unavailable")
    if not analysis["control_flow_complete"]:
        raise AcquisitionError(
            "runtime method name control flow is not fully bounded"
        )
    if not analysis["memory_effects_complete"]:
        raise AcquisitionError(
            "runtime method name memory writes are not fully classified"
        )
    if analysis["return_count"] < 2 or analysis["unresolved_return_count"]:
        raise AcquisitionError(
            "runtime method name return paths are not fully classified"
        )
    calls = analysis["calls"]
    candidates: set[tuple[str, int, int, int, int, int, int, int, int]] = set()
    for decoded in analysis["decoded_values"]:
        _kind, operation, metadata_offset, node_offset, encoded_offset, key = decoded
        length_calls = [
            call for call in calls if call["rcx"] == decoded
        ]
        for length_call in length_calls:
            string_calls = [
                call
                for call in calls
                if call["rcx"] == decoded
                and call["rdx"] == (
                    "call-result", length_call["target"], length_call["offset"]
                )
            ]
            for string_call in string_calls:
                lazy_calls = [
                    call
                    for call in calls
                    if call["rcx"] == ("metadata", metadata_offset)
                ]
                for lazy_call in lazy_calls:
                    lazy_result_reaches_length_helper = any(
                        call["target"] == length_call["target"]
                        and call["rcx"] == (
                            "call-result", lazy_call["target"], lazy_call["offset"]
                        )
                        for call in calls
                    )
                    managed_string_cached = any(
                        store["source"] == (
                            "call-result", string_call["target"], string_call["offset"]
                        )
                        for store in analysis["cached_stores"]
                    )
                    if lazy_result_reaches_length_helper and managed_string_cached:
                        candidates.add((
                            operation,
                            metadata_offset,
                            node_offset,
                            encoded_offset,
                            key,
                            length_call["target"],
                            string_call["target"],
                            lazy_call["target"],
                            string_call["offset"],
                        ))
    if len(candidates) != 1:
        decoded_values = analysis["decoded_values"]
        decoded_tuple = tuple(decoded_values)
        length_call_count = sum(
            call["rcx"] in decoded_values for call in calls
        )
        string_call_count = sum(
            call["rcx"] in decoded_values
            and any(
                length_call["target"] is not None
                and call["rdx"] == (
                    "call-result", length_call["target"], length_call["offset"]
                )
                for length_call in calls
                if length_call["rcx"] in decoded_values
            )
            for call in calls
        )
        lazy_call_count = sum(
            call["rcx"] == ("metadata", decoded[1])
            for decoded in decoded_tuple
            for call in calls
        )
        cache_write_count = sum(
            store["base"] == ("object",)
            and store["displacement"] == cached_name_byte_offset
            for store in analysis["cached_stores"]
        )
        raise AcquisitionError(
            "runtime method name decoder evidence does not close "
            f"(candidates={len(candidates)}, decoded_paths={len(decoded_values)}, "
            f"length_calls={length_call_count}, managed_string_calls={string_call_count}, "
            f"lazy_initializer_calls={lazy_call_count}, cache_writes={cache_write_count}, "
            f"control_flow_complete={analysis['control_flow_complete']})"
        )
    (
        operation,
        metadata_offset,
        node_offset,
        encoded_offset,
        key,
        length_helper,
        managed_string_helper,
        lazy_initializer,
        string_call_offset,
    ) = next(iter(candidates))
    if analysis["return_values"] != {
        ("cached-name", cached_name_byte_offset),
        ("call-result", managed_string_helper, string_call_offset),
    }:
        raise AcquisitionError(
            "runtime method name return paths disagree with decoded helper"
        )
    return {
        "decode_operation": operation,
        "decode_key": key,
        "cached_name_field_qword": cached_name_byte_offset // 8,
        "metadata_field_qword": metadata_offset // 8,
        "name_node_field_qword": node_offset // 8,
        "encoded_name_field_qword": encoded_offset // 8,
        "xor_key": key if operation == "xor" else 0,
        "length_helper": length_helper,
        "managed_string_helper": managed_string_helper,
        "lazy_initializer": lazy_initializer,
    }


def _method_return_type_shape(
    code: bytes,
    *,
    method_pointer: int,
    metadata_byte_offset: int,
) -> dict[str, int] | None:
    if (
        not code
        or method_pointer <= 0
        or not 0 <= metadata_byte_offset <= 0x7F
        or not code.startswith(
            b"\x56\x48\x83\xec\x20\x48\x8b\x71"
            + bytes((metadata_byte_offset,))
        )
    ):
        return None
    owner_load = code.find(b"\x48\x8b\x4e", 9)
    owner_offset = code[owner_load + 3] if owner_load >= 0 else 0
    owner_instruction_bytes = 4
    if owner_load < 0:
        owner_load = code.find(b"\x48\x8b\x0e", 9)
        owner_instruction_bytes = 3
    embedded_add = code.find(
        b"\x48\x83\xc1", owner_load + owner_instruction_bytes
    )
    first_call = code.find(b"\xe8")
    cache_load = code.find(b"\x48\x8b\x46", first_call + 5)
    key_load = code.find(b"\x48\xb9", cache_load + 4)
    encoded_load = -1
    encoded_instruction_bytes = 0
    encoded_offset = -1
    decode_operation = None
    if key_load >= 0:
        try:
            from capstone import Cs, CS_ARCH_X86, CS_MODE_64
            from capstone.x86 import X86_OP_MEM, X86_OP_REG
        except ImportError as error:
            raise AcquisitionError(
                "runtime method return decoding requires capstone"
            ) from error
        decoder = Cs(CS_ARCH_X86, CS_MODE_64)
        decoder.detail = True
        for instruction in decoder.disasm(code, 0):
            operands = instruction.operands
            if (
                instruction.address >= key_load + 10
                and instruction.mnemonic in ("xor", "add")
                and len(operands) == 2
                and operands[0].type == X86_OP_REG
                and decoder.reg_name(operands[0].reg) == "rcx"
                and operands[0].size == 8
                and operands[1].type == X86_OP_MEM
                and operands[1].size == 8
                and decoder.reg_name(operands[1].mem.base) == "rax"
                and not operands[1].mem.index
                and 0 <= operands[1].mem.disp <= 0x78
                and operands[1].mem.disp % 8 == 0
            ):
                encoded_load = instruction.address
                encoded_instruction_bytes = instruction.size
                encoded_offset = operands[1].mem.disp
                decode_operation = instruction.mnemonic
                break
    tail_jump = code.find(
        b"\xe9", encoded_load + encoded_instruction_bytes
    )
    lazy_prefix = code.find(b"\x48\x89\xf1\xe8", tail_jump + 5)
    if min(
        first_call,
        owner_load,
        embedded_add,
        cache_load,
        key_load,
        encoded_load,
        tail_jump,
        lazy_prefix,
    ) < 0:
        return None
    cache_offset = code[cache_load + 3]
    embedded_offset = code[embedded_add + 3]
    key = struct.unpack_from("<Q", code, key_load + 2)[0]
    first_target = _relative_call_target(
        code,
        method_pointer=method_pointer,
        call_offset=first_call,
    )
    lazy_node_helper = _relative_call_target(
        code,
        method_pointer=method_pointer,
        call_offset=lazy_prefix + 3,
    )
    tail_displacement = struct.unpack_from("<i", code, tail_jump + 1)[0]
    tail_target = method_pointer + tail_jump + 5 + tail_displacement
    if (
        not key
        or owner_offset % 8
        or owner_offset > 0x78
        or embedded_offset > 0x78
        or cache_offset % 8
        or encoded_offset % 8
        or cache_offset > 0x78
        or encoded_offset > 0x78
        or not first_target
        or not lazy_node_helper
        or tail_target != first_target
    ):
        return None
    return {
        "metadata_byte_offset": metadata_byte_offset,
        "return_type_owner_byte_offset": owner_offset,
        "embedded_type_byte_offset": embedded_offset,
        "cache_node_byte_offset": cache_offset,
        "encoded_type_byte_offset": encoded_offset,
        "decode_operation": decode_operation,
        "decode_key": key,
        "xor_key": key if decode_operation == "xor" else 0,
        "managed_type_helper": first_target,
        "lazy_node_helper": lazy_node_helper,
    }


def _method_parameters_shape(
    code: bytes,
    *,
    metadata_byte_offset: int,
) -> dict[str, int] | None:
    prefix = (
        b"\x56\x57\x48\x83\xec\x28\x48\x8b\x71"
        + bytes((metadata_byte_offset,))
    )
    if len(code) < 96 or not code.startswith(prefix):
        return None
    cached_load = code.find(b"\x48\x8b\x41", len(prefix))
    bool_argument = code.find(b"\xb2\x01", cached_load + 4)
    length_loads = (
        code.find(b"\x48\x8b\x40\x18", bool_argument + 2),
        code.find(b"\x8b\x40\x18", bool_argument + 2),
    )
    result_type_load = code.find(b"\x48\x8b\x0d", bool_argument + 2)
    if (
        min(cached_load, bool_argument, *length_loads, result_type_load) < 0
        or code.count(b"\xe8") < 5
        or b"\xcc" not in code[-8:]
    ):
        return None
    cached_offset = code[cached_load + 3]
    if cached_offset % 8 or cached_offset > 0x78:
        return None
    return {
        "metadata_byte_offset": metadata_byte_offset,
        "cached_parameters_byte_offset": cached_offset,
        "result_type_load_offset": result_type_load,
    }


def _lazy_name_initializer_matches(
    code: bytes,
    *,
    decoder: dict[str, Any],
) -> bool:
    node_offset = decoder["name_node_field_qword"] * 8
    encoded_offset = decoder["encoded_name_field_qword"] * 8
    metadata_offset = decoder["metadata_field_qword"] * 8
    operation = decoder["decode_operation"]
    key = decoder["decode_key"]
    if (
        min(node_offset, encoded_offset, metadata_offset) < 0
        or operation not in METHOD_NAME_DECODE_OPERATION_CODES
        or not key
    ):
        return False
    analysis = _method_name_dataflow(
        code,
        method_pointer=0,
        input_state=("metadata", metadata_offset),
        cached_name_byte_offset=None,
    )
    expected = (
        "decoded", operation, metadata_offset, node_offset, encoded_offset, key
    )
    node_load_seen = any(
        decoded[:5] == expected[:5]
        for decoded in analysis["decoded_values"]
    )
    node_store_seen = any(
        store["base"] == ("metadata", metadata_offset)
        and store["displacement"] == node_offset
        for store in analysis["node_accesses"]
    )
    if operation == "add":
        inverse_key = (-key) & 0xFFFFFFFFFFFFFFFF
        encoded_store_seen = any(
            store["base"] == ("node", metadata_offset, node_offset)
            and store["displacement"] == encoded_offset
            and store["source"] is not None
            and store["source"][:2] == ("transformed-call-result", "add")
            and store["source"][3] == inverse_key
            and store["source"][2][:1] == ("call-result",)
            for store in analysis["node_accesses"]
        )
        return (
            analysis["control_flow_complete"]
            and analysis["memory_effects_complete"]
            and analysis["return_count"] > 0
            and node_store_seen
            and encoded_store_seen
        )
    return (
        analysis["control_flow_complete"]
        and analysis["memory_effects_complete"]
        and analysis["return_count"] > 0
        and node_load_seen
        and expected in analysis["decoded_values"]
        and node_store_seen
    )


def _derive_method_parameter_count_field(
    *,
    snapshot: MemorySnapshot,
    resolved_operations: list[dict[str, Any]],
    method_records: list[dict[str, Any]],
    scan_bytes: int = 256,
    maximum_parameter_count: int = 64,
) -> dict[str, Any]:
    contract = reflection_contract()
    expected_counts = {
        operation["key"]: operation["parameter_count"]
        for operation in contract["operations"]
    }
    semantic_samples = [
        (
            operation.get("metadata_pointer", 0),
            expected_counts.get(operation.get("key", "")),
        )
        for operation in resolved_operations
    ]
    if (
        scan_bytes < 1
        or maximum_parameter_count < 1
        or len(semantic_samples) < 8
        or any(
            not pointer or not isinstance(expected, int)
            for pointer, expected in semantic_samples
        )
        or not method_records
    ):
        raise AcquisitionError(
            "runtime method parameter count semantic samples are incomplete"
        )
    candidates: list[tuple[int, int]] = []
    for byte_offset in range(scan_bytes):
        if any(
            (raw := snapshot.read(pointer + byte_offset, 1)) is None
            or raw[0] != expected
            for pointer, expected in semantic_samples
        ):
            continue
        observed: list[int] = []
        for method in method_records:
            pointer = method.get("metadata_pointer", 0)
            raw = snapshot.read(pointer + byte_offset, 1) if pointer else None
            if raw is None or raw[0] > maximum_parameter_count:
                break
            observed.append(raw[0])
        if len(observed) == len(method_records):
            candidates.append((byte_offset, len(set(observed))))
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime method parameter count field is not unique "
            f"(candidates={len(candidates)})"
        )
    byte_offset, distinct_count = candidates[0]
    return {
        "scan_byte_count": scan_bytes,
        "maximum_observed_parameter_count": maximum_parameter_count,
        "semantic_sample_count": len(semantic_samples),
        "method_record_count": len(method_records),
        "candidate_field_count": 1,
        "selected_byte_offset": byte_offset,
        "distinct_parameter_count": distinct_count,
    }


def _method_pointer_boundaries(classes: dict[str, Any]) -> tuple[int, ...]:
    return tuple(sorted({
        pointer
        for method in classes.get("methods", [])
        if type(pointer := method.get("method_pointer")) is int and pointer > 0
    }))


def _method_code(
    *,
    snapshot: MemorySnapshot,
    image: MappedPE,
    method_pointer: int,
    method_pointers: tuple[int, ...] = (),
) -> bytes | None:
    if not method_pointer or method_pointer < snapshot.image_base:
        return None
    rva = method_pointer - snapshot.image_base
    if rva >= image.size_of_image or not image.executable_rva(rva):
        return None
    function = image.containing_function(rva)
    if function is not None and function.end_rva > rva:
        byte_count = function.end_rva - rva
        if byte_count > 1_048_576:
            raise AcquisitionError(
                "runtime reflection method exceeds the supported analysis size"
            )
    else:
        byte_count = 512
        next_index = bisect_right(method_pointers, method_pointer)
        if next_index < len(method_pointers):
            byte_count = min(
                byte_count, method_pointers[next_index] - method_pointer
            )
    return snapshot.read(method_pointer, byte_count)


def discover_reflection_semantics(
    *,
    binary: Path,
    snapshot_path: Path,
    bootstrap_model: Path,
    class_model: Path,
) -> dict[str, Any]:
    bootstrap = read_json(bootstrap_model)
    classes = read_json(class_model)
    if (
        not isinstance(bootstrap, dict)
        or bootstrap.get("schema") != REFLECTION_BOOTSTRAP_SCHEMA
    ):
        raise AcquisitionError("runtime reflection semantic bootstrap is invalid")
    if (
        not isinstance(classes, dict)
        or classes.get("schema") != RUNTIME_CLASS_SCHEMA
    ):
        raise AcquisitionError("runtime reflection semantic class model is invalid")
    binary_identity = file_identity(binary)
    snapshot_identity = file_identity(snapshot_path)
    if (
        bootstrap.get("binary", {}).get("sha256") != binary_identity["sha256"]
        or bootstrap.get("binary", {}).get("bytes") != binary_identity["bytes"]
    ):
        raise AcquisitionError("runtime reflection semantic target binding is stale")
    if classes.get("snapshot", {}).get("sha256") != snapshot_identity["sha256"]:
        raise AcquisitionError("runtime reflection semantic snapshot binding is stale")
    if classes.get("bootstrap_model_sha256") != file_identity(bootstrap_model)[
        "sha256"
    ]:
        raise AcquisitionError("runtime reflection semantic bootstrap binding is stale")

    method_pointers = _method_pointer_boundaries(classes)

    class_addresses = {
        item["runtime_owner"]: item["class_pointer"]
        for item in classes.get("classes", [])
    }
    required_name_owners = {
        owner
        for _key, object_owner, method_owner, _shape in NAME_OPERATION_DESCRIPTORS
        for owner in (object_owner, method_owner)
    }
    required_object_owners = {
        owner
        for (
            _key,
            object_owner,
            method_owner,
            target_owner,
        ) in DIRECT_OBJECT_OPERATION_DESCRIPTORS
        for owner in (object_owner, method_owner, target_owner)
    }
    required_sentinel_owners = {
        owner
        for (
            _key,
            object_owner,
            method_owner,
            _target_cache,
            _shape,
        ) in SENTINEL_FIELD_OPERATION_DESCRIPTORS
        for owner in (object_owner, method_owner)
    }
    missing_name_owners = sorted(
        (
            required_name_owners
            | required_object_owners
            | required_sentinel_owners
        )
        - class_addresses.keys()
    )
    if missing_name_owners:
        raise AcquisitionError(
            "runtime reflection name owner classes are unavailable: "
            + ", ".join(missing_name_owners)
        )
    string_cache = [
        cache
        for cache in bootstrap.get("type_caches", [])
        if cache.get("namespace") == "System" and cache.get("type_name") == "String"
    ]
    if len(string_cache) != 1:
        raise AcquisitionError("runtime reflection String cache is not unique")
    required_sentinel_caches = {
        target_cache
        for (
            _key,
            _object_owner,
            _method_owner,
            target_cache,
            _shape,
        ) in SENTINEL_FIELD_OPERATION_DESCRIPTORS
    }
    sentinel_cache_records: dict[tuple[str, str], dict[str, Any]] = {}
    for namespace, type_name in required_sentinel_caches:
        matches = [
            cache
            for cache in bootstrap.get("type_caches", [])
            if cache.get("namespace") == namespace
            and cache.get("type_name") == type_name
        ]
        if len(matches) != 1:
            raise AcquisitionError(
                "runtime reflection sentinel type cache is not unique"
            )
        sentinel_cache_records[(namespace, type_name)] = matches[0]

    with MemorySnapshot(snapshot_path) as snapshot, MappedPE(binary) as image:
        if (
            snapshot.image_bytes != image.size_of_image
            or snapshot.image_bytes != bootstrap["binary"]["size_of_image"]
        ):
            raise AcquisitionError("runtime reflection semantic image binding is stale")
        string_values = snapshot.qwords(
            snapshot.image_base + string_cache[0]["result_slot_rva"], 1
        )
        string_class = string_values[0] if string_values else 0
        if not string_class:
            raise AcquisitionError("runtime reflection String class is unavailable")
        sentinel_classes: dict[tuple[str, str], int] = {}
        for pair, cache in sentinel_cache_records.items():
            values = snapshot.qwords(
                snapshot.image_base + cache["result_slot_rva"], 1
            )
            if not values or not values[0]:
                raise AcquisitionError(
                    "runtime reflection sentinel class is unavailable"
                )
            sentinel_classes[pair] = values[0]


        snapshot.capture_reference_hits(
            set(class_addresses.values()) | set(sentinel_classes.values())
        )
        evidence_records: list[dict[str, Any]] = []
        resolved_operations: list[dict[str, Any]] = []
        for (
            operation_key,
            object_runtime_owner,
            method_runtime_owner,
            matcher_name,
        ) in NAME_OPERATION_DESCRIPTORS:
            class_pointer = class_addresses[object_runtime_owner]
            candidates: list[dict[str, Any]] = []
            matcher = {
                "cached-branch": _loads_rax_from_rcx_field,
                "direct-return": _directly_returns_rcx_field,
                "rsi-alias-return": _returns_rsi_alias_field,
            }[matcher_name]


            owner_code = [
                (method, _method_code(snapshot=snapshot, image=image,
                                      method_pointer=method.get("method_pointer", 0),
                                      method_pointers=method_pointers))
                for method in classes.get("methods", [])
                if method.get("runtime_owner") == method_runtime_owner
            ]
            getter_fields = {
                field for field in range(2, 10)
                if any(code is not None and matcher(code, field * 8)
                       for _, code in owner_code)
            }
            evidence = _dominant_cached_string_field(
                snapshot=snapshot, class_pointer=class_pointer,
                string_class=string_class, getter_fields=getter_fields,
            )
            byte_offset = evidence["selected_field_qword"] * 8
            for method, code in owner_code:
                if code is None or not matcher(code, byte_offset):
                    continue
                candidates.append(method)
            if len(candidates) != 1:
                raise AcquisitionError(
                    "runtime reflection name getter is not unique "
                    f"(owner={method_runtime_owner}, candidates={len(candidates)})"
                )
            selected = candidates[0]
            evidence_records.append(
                {
                    "runtime_owner": object_runtime_owner,
                    "method_runtime_owner": method_runtime_owner,
                    "class_pointer": class_pointer,
                    **evidence,
                }
            )
            resolved_operations.append(
                {
                    "key": operation_key,
                    "runtime_owner": method_runtime_owner,
                    "runtime_name": "get_Name",
                    "method_index": selected["method_index"],
                    "metadata_pointer": selected["metadata_pointer"],
                    "method_pointer": selected["method_pointer"],
                    "semantic_identity_resolved": True,
                    "resolution": "derived-managed-string-field-return",
                }
            )

        direct_dword_evidence: list[dict[str, Any]] = []
        name_evidence_by_owner = {
            evidence["runtime_owner"]: evidence for evidence in evidence_records
        }
        for operation_key, runtime_owner in DIRECT_DWORD_OPERATION_OWNERS:
            candidates: list[tuple[dict[str, Any], int]] = []
            for method in classes.get("methods", []):
                if method.get("runtime_owner") != runtime_owner:
                    continue
                code = _method_code(
                    snapshot=snapshot,
                    image=image,
                    method_pointer=method.get("method_pointer", 0),
                    method_pointers=method_pointers,
                )
                byte_offset = _direct_dword_getter_shape(code or b"")
                if byte_offset is not None:
                    candidates.append((method, byte_offset))
            if len(candidates) != 1 or runtime_owner not in name_evidence_by_owner:
                raise AcquisitionError(
                    "runtime reflection direct dword getter is not unique "
                    f"(owner={runtime_owner}, candidates={len(candidates)})"
                )
            selected, byte_offset = candidates[0]
            class_pointer = class_addresses[runtime_owner]
            name_field = name_evidence_by_owner[runtime_owner][
                "selected_field_qword"
            ]
            object_count = 0
            values: Counter[int] = Counter()
            for reference in snapshot.references(class_pointer):
                fields = snapshot.qwords(reference, max(10, name_field + 1))
                raw = snapshot.read(reference + byte_offset, 4)
                if (
                    not fields
                    or fields[0] != class_pointer
                    or raw is None
                    or _managed_string(
                        snapshot,
                        fields[name_field],
                        string_class=string_class,
                    )
                    is None
                ):
                    continue
                object_count += 1
                values[struct.unpack("<I", raw)[0]] += 1
            if (
                object_count < 8
                or len(values) < 2
                or not values
                or max(values) > 0xFFFF
            ):
                raise AcquisitionError(
                    "runtime reflection dword getter observations are incomplete"
                )
            direct_dword_evidence.append(
                {
                    "operation_key": operation_key,
                    "runtime_owner": runtime_owner,
                    "class_pointer": class_pointer,
                    "attribute_byte_offset": byte_offset,
                    "object_reference_count": object_count,
                    "distinct_value_count": len(values),
                    "maximum_value": max(values),
                }
            )
            resolved_operations.append(
                {
                    "key": operation_key,
                    "runtime_owner": runtime_owner,
                    "runtime_name": "get_Attributes",
                    "method_index": selected["method_index"],
                    "metadata_pointer": selected["metadata_pointer"],
                    "method_pointer": selected["method_pointer"],
                    "semantic_identity_resolved": True,
                    "resolution": "derived-direct-dword-field-and-object-domain",
                }
            )

        property_class = class_addresses["System.Reflection.MonoProperty"]
        method_class = class_addresses["System.Reflection.MonoMethod"]
        property_name_field = name_evidence_by_owner[
            "System.Reflection.MonoProperty"
        ]["selected_field_qword"]
        method_name_field = name_evidence_by_owner[
            "System.Reflection.MonoMethod"
        ]["selected_field_qword"]
        property_accessor_field_support = {
            key: Counter() for key, _prefix in PROPERTY_ACCESSOR_OPERATIONS
        }
        property_object_count = 0
        for reference in snapshot.references(property_class):
            fields = snapshot.qwords(reference, 10)
            if not fields or fields[0] != property_class:
                continue
            property_name = _managed_string(
                snapshot,
                fields[property_name_field],
                string_class=string_class,
            )
            if property_name is None:
                continue
            property_object_count += 1
            for field, candidate in enumerate(fields):
                method_fields = snapshot.qwords(candidate, 10) if candidate else None
                if not method_fields or method_fields[0] != method_class:
                    continue
                method_name = _managed_string(
                    snapshot,
                    method_fields[method_name_field],
                    string_class=string_class,
                )
                for operation_key, prefix in PROPERTY_ACCESSOR_OPERATIONS:
                    if method_name == prefix + property_name:
                        property_accessor_field_support[operation_key][field] += 1
        property_accessor_evidence: list[dict[str, Any]] = []
        for operation_key, prefix in PROPERTY_ACCESSOR_OPERATIONS:
            support = property_accessor_field_support[operation_key]
            if not support:
                raise AcquisitionError(
                    "runtime property accessor field is unavailable"
                )
            strongest = max(support.values())
            selected_fields = [
                field for field, count in support.items() if count == strongest
            ]
            if (
                len(selected_fields) != 1
                or strongest < MIN_PROPERTY_ACCESSOR_NAME_SUPPORT
            ):
                raise AcquisitionError(
                    "runtime property accessor field is not unique "
                    f"(operation={operation_key}, candidates="
                    f"{len(selected_fields)}, support={strongest})"
                )
            selected_field = selected_fields[0]
            byte_offset = selected_field * 8
            candidates: list[dict[str, Any]] = []
            for method in classes.get("methods", []):
                if method.get("runtime_owner") != "System.Reflection.MonoProperty":
                    continue
                code = _method_code(
                    snapshot=snapshot,
                    image=image,
                    method_pointer=method.get("method_pointer", 0),
                    method_pointers=method_pointers,
                )
                if code is not None and _property_accessor_getter_shape(
                    code, byte_offset
                ):
                    candidates.append(method)
            if len(candidates) != 1:
                raise AcquisitionError(
                    "runtime property accessor getter is not unique "
                    f"(operation={operation_key}, candidates={len(candidates)})"
                )
            selected = candidates[0]
            property_accessor_evidence.append(
                {
                    "operation_key": operation_key,
                    "runtime_owner": "System.Reflection.MonoProperty",
                    "class_pointer": property_class,
                    "selected_field_qword": selected_field,
                    "selected_field_support": strongest,
                    "property_object_reference_count": property_object_count,
                    "semantic_name_prefix": prefix,
                }
            )
            resolved_operations.append(
                {
                    "key": operation_key,
                    "runtime_owner": "System.Reflection.MonoProperty",
                    "runtime_name": {
                        "property.getter": "GetGetMethod",
                        "property.setter": "GetSetMethod",
                    }[operation_key],
                    "method_index": selected["method_index"],
                    "metadata_pointer": selected["metadata_pointer"],
                    "method_pointer": selected["method_pointer"],
                    "semantic_identity_resolved": True,
                    "resolution": "derived-accessor-name-and-visibility-filter",
                }
            )
        if len(
            {
                evidence["selected_field_qword"]
                for evidence in property_accessor_evidence
            }
        ) != len(PROPERTY_ACCESSOR_OPERATIONS):
            raise AcquisitionError(
                "runtime property accessor fields are not structurally distinct"
            )

        parameter_flag_candidates: dict[int, list[dict[str, Any]]] = {
            mask: [] for _key, mask in PARAMETER_FLAG_OPERATION_MASKS
        }
        parameter_flag_offsets: set[int] = set()
        for method in classes.get("methods", []):
            if method.get("runtime_owner") != "System.Reflection.ParameterInfo":
                continue
            code = _method_code(
                snapshot=snapshot,
                image=image,
                method_pointer=method.get("method_pointer", 0),
                method_pointers=method_pointers,
            )
            shape = _parameter_flag_getter_shape(code or b"")
            if shape is None or shape[1] not in parameter_flag_candidates:
                continue
            byte_offset, mask = shape
            parameter_flag_offsets.add(byte_offset)
            parameter_flag_candidates[mask].append(method)
        if len(parameter_flag_offsets) != 1 or any(
            len(candidates) != 1
            for candidates in parameter_flag_candidates.values()
        ):
            raise AcquisitionError(
                "runtime reflection parameter flag getters are not unique"
            )
        parameter_flag_offset = next(iter(parameter_flag_offsets))
        parameter_objects = 0
        parameter_flag_set_counts = {
            mask: 0 for _key, mask in PARAMETER_FLAG_OPERATION_MASKS
        }
        parameter_flag_clear_counts = {
            mask: 0 for _key, mask in PARAMETER_FLAG_OPERATION_MASKS
        }
        parameter_object_class = class_addresses[
            "System.Reflection.MonoParameterInfo"
        ]
        for reference in snapshot.references(parameter_object_class):
            values = snapshot.qwords(reference, 1)
            raw = snapshot.read(reference + parameter_flag_offset, 1)
            if not values or values[0] != parameter_object_class or raw is None:
                continue
            parameter_objects += 1
            attributes = raw[0]
            for _operation_key, mask in PARAMETER_FLAG_OPERATION_MASKS:
                target = (
                    parameter_flag_set_counts
                    if attributes & mask
                    else parameter_flag_clear_counts
                )
                target[mask] += 1
        if parameter_objects < 8:
            raise AcquisitionError(
                "runtime reflection parameter flag observations are incomplete"
            )
        for operation_key, mask in PARAMETER_FLAG_OPERATION_MASKS:
            selected = parameter_flag_candidates[mask][0]
            resolved_operations.append(
                {
                    "key": operation_key,
                    "runtime_owner": "System.Reflection.ParameterInfo",
                    "runtime_name": {
                        "parameter.is_in": "get_IsIn",
                        "parameter.is_out": "get_IsOut",
                        "parameter.is_optional": "get_IsOptional",
                    }[operation_key],
                    "method_index": selected["method_index"],
                    "metadata_pointer": selected["metadata_pointer"],
                    "method_pointer": selected["method_pointer"],
                    "semantic_identity_resolved": True,
                    "resolution": (
                        "derived-shared-attribute-byte-and-framework-semantic-bit"
                    ),
                }
            )
        parameter_flag_evidence = {
            "runtime_owner": "System.Reflection.MonoParameterInfo",
            "method_runtime_owner": "System.Reflection.ParameterInfo",
            "object_reference_count": parameter_objects,
            "attribute_byte_offset": parameter_flag_offset,
            "semantic_masks": {
                operation_key: mask
                for operation_key, mask in PARAMETER_FLAG_OPERATION_MASKS
            },
            "set_counts": {
                operation_key: parameter_flag_set_counts[mask]
                for operation_key, mask in PARAMETER_FLAG_OPERATION_MASKS
            },
            "clear_counts": {
                operation_key: parameter_flag_clear_counts[mask]
                for operation_key, mask in PARAMETER_FLAG_OPERATION_MASKS
            },
        }

        sentinel_field_evidence: list[dict[str, Any]] = []
        for (
            operation_key,
            object_runtime_owner,
            method_runtime_owner,
            target_cache,
            matcher_name,
        ) in SENTINEL_FIELD_OPERATION_DESCRIPTORS:
            evidence = _dominant_object_field(
                snapshot=snapshot,
                class_pointer=class_addresses[object_runtime_owner],
                target_class_pointer=sentinel_classes[target_cache],
            )
            byte_offset = evidence["selected_field_qword"] * 8
            matcher = {
                "sentinel-field-return": _returns_sentinel_field,
            }[matcher_name]
            candidates: list[dict[str, Any]] = []
            for method in classes.get("methods", []):
                if method.get("runtime_owner") != method_runtime_owner:
                    continue
                code = _method_code(
                    snapshot=snapshot,
                    image=image,
                    method_pointer=method.get("method_pointer", 0),
                    method_pointers=method_pointers,
                )
                if code is not None and matcher(code, byte_offset):
                    candidates.append(method)
            if len(candidates) != 1:
                raise AcquisitionError(
                    "runtime reflection sentinel field getter is not unique "
                    f"(owner={method_runtime_owner}, candidates={len(candidates)})"
                )
            selected = candidates[0]
            sentinel_field_evidence.append(
                {
                    "operation_key": operation_key,
                    "runtime_owner": object_runtime_owner,
                    "method_runtime_owner": method_runtime_owner,
                    "target_cache": {
                        "namespace": target_cache[0],
                        "type_name": target_cache[1],
                    },
                    "class_pointer": class_addresses[object_runtime_owner],
                    "target_class_pointer": sentinel_classes[target_cache],
                    **evidence,
                }
            )
            resolved_operations.append(
                {
                    "key": operation_key,
                    "runtime_owner": method_runtime_owner,
                    "runtime_name": "get_DefaultValue",
                    "method_index": selected["method_index"],
                    "metadata_pointer": selected["metadata_pointer"],
                    "method_pointer": selected["method_pointer"],
                    "semantic_identity_resolved": True,
                    "resolution": "derived-current-runtime-sentinel-field-return",
                }
            )

        method_name_operation = next(
            operation
            for operation in resolved_operations
            if operation["key"] == "method.name"
        )
        method_name_evidence = name_evidence_by_owner[METHOD_NAME_OWNER]
        method_name_code = _method_code(
            snapshot=snapshot,
            image=image,
            method_pointer=method_name_operation["method_pointer"],
            method_pointers=method_pointers,
        )
        if method_name_code is None:
            raise AcquisitionError("runtime method name getter code is unavailable")
        method_name_decoder = _derive_method_name_decoder(
            method_name_code,
            method_pointer=method_name_operation["method_pointer"],
            cached_name_byte_offset=(
                method_name_evidence["selected_field_qword"] * 8
            ),
        )
        for helper_key in (
            "length_helper",
            "managed_string_helper",
            "lazy_initializer",
        ):
            helper = method_name_decoder[helper_key]
            helper_rva = helper - snapshot.image_base
            if not 0 <= helper_rva < image.size_of_image or not image.executable_rva(
                helper_rva
            ):
                raise AcquisitionError(
                    "runtime method name decoder helper is outside current image"
                )
        lazy_code = snapshot.read(method_name_decoder["lazy_initializer"], 256)
        if lazy_code is None or not _lazy_name_initializer_matches(
            lazy_code,
            decoder=method_name_decoder,
        ):
            raise AcquisitionError(
                "runtime method name lazy initializer is not semantically bound"
            )
        initialized_method_name_nodes = 0
        lazy_method_name_nodes = 0
        metadata_field_qword = method_name_decoder["metadata_field_qword"]
        node_field_qword = method_name_decoder["name_node_field_qword"]
        for method in classes.get("methods", []):
            metadata = method.get("metadata_pointer", 0)
            values = snapshot.qwords(metadata, node_field_qword + 1)
            if not values:
                raise AcquisitionError(
                    "runtime method name decoder metadata is unreadable"
                )
            if values[node_field_qword]:
                initialized_method_name_nodes += 1
            else:
                lazy_method_name_nodes += 1
        method_name_decoder_evidence = {
            "method_record_count": len(classes.get("methods", [])),
            "initialized_name_node_count": initialized_method_name_nodes,
            "lazy_name_node_count": lazy_method_name_nodes,
            "metadata_field_qword": metadata_field_qword,
            **method_name_decoder,
        }

        nested_word_evidence: list[dict[str, Any]] = []
        for operation_key, runtime_owner in NESTED_WORD_OPERATION_OWNERS:
            candidates: list[tuple[dict[str, Any], int, int]] = []
            for method in classes.get("methods", []):
                if method.get("runtime_owner") != runtime_owner:
                    continue
                code = _method_code(
                    snapshot=snapshot,
                    image=image,
                    method_pointer=method.get("method_pointer", 0),
                    method_pointers=method_pointers,
                )
                shape = _nested_word_getter_shape(code or b"")
                if shape is not None:
                    candidates.append((method, *shape))
            if len(candidates) != 1:
                raise AcquisitionError(
                    "runtime reflection nested word getter is not unique "
                    f"(owner={runtime_owner}, candidates={len(candidates)})"
                )
            selected, object_offset, nested_offset = candidates[0]
            expected_object_offset = (
                method_name_decoder["metadata_field_qword"] * 8
            )
            if object_offset != expected_object_offset:
                raise AcquisitionError(
                    "runtime reflection nested word getter does not use the "
                    "derived MethodInfo field"
                )
            values: Counter[int] = Counter()
            readable_count = 0
            for method in classes.get("methods", []):
                metadata_pointer = method.get("metadata_pointer")
                if not isinstance(metadata_pointer, int) or not metadata_pointer:
                    continue
                raw = snapshot.read(metadata_pointer + nested_offset, 2)
                if raw is None:
                    continue
                readable_count += 1
                values[struct.unpack("<H", raw)[0]] += 1
            if (
                readable_count != len(classes.get("methods", []))
                or len(values) < 4
            ):
                raise AcquisitionError(
                    "runtime reflection nested word domain is incomplete"
                )
            nested_word_evidence.append(
                {
                    "operation_key": operation_key,
                    "runtime_owner": runtime_owner,
                    "derived_object_field_qword": object_offset // 8,
                    "derived_nested_word_offset": nested_offset,
                    "method_record_count": readable_count,
                    "distinct_value_count": len(values),
                    "zero_value_count": values[0],
                    "maximum_value": max(values),
                }
            )
            resolved_operations.append(
                {
                    "key": operation_key,
                    "runtime_owner": runtime_owner,
                    "runtime_name": "get_Attributes",
                    "method_index": selected["method_index"],
                    "metadata_pointer": selected["metadata_pointer"],
                    "method_pointer": selected["method_pointer"],
                    "semantic_identity_resolved": True,
                    "resolution": (
                        "derived-methodinfo-nested-word-and-complete-domain"
                    ),
                }
            )

        object_field_evidence: list[dict[str, Any]] = []
        for (
            operation_key,
            object_runtime_owner,
            method_runtime_owner,
            target_runtime_owner,
        ) in DIRECT_OBJECT_OPERATION_DESCRIPTORS:
            evidence = _dominant_object_field(
                snapshot=snapshot,
                class_pointer=class_addresses[object_runtime_owner],
                target_class_pointer=class_addresses[target_runtime_owner],
            )
            byte_offset = evidence["selected_field_qword"] * 8
            candidates: list[dict[str, Any]] = []
            for method in classes.get("methods", []):
                if method.get("runtime_owner") != method_runtime_owner:
                    continue
                code = _method_code(
                    snapshot=snapshot,
                    image=image,
                    method_pointer=method.get("method_pointer", 0),
                    method_pointers=method_pointers,
                )
                if code is None or not _directly_returns_rcx_field(
                    code, byte_offset
                ):
                    continue
                candidates.append(method)
            if len(candidates) != 1:
                raise AcquisitionError(
                    "runtime reflection direct object getter is not unique "
                    f"(owner={method_runtime_owner}, candidates={len(candidates)})"
                )
            selected = candidates[0]
            object_field_evidence.append(
                {
                    "operation_key": operation_key,
                    "runtime_owner": object_runtime_owner,
                    "method_runtime_owner": method_runtime_owner,
                    "target_runtime_owner": target_runtime_owner,
                    "class_pointer": class_addresses[object_runtime_owner],
                    "target_class_pointer": class_addresses[target_runtime_owner],
                    **evidence,
                }
            )
            resolved_operations.append(
                {
                    "key": operation_key,
                    "runtime_owner": method_runtime_owner,
                    "runtime_name": "get_ParameterType",
                    "method_index": selected["method_index"],
                    "metadata_pointer": selected["metadata_pointer"],
                    "method_pointer": selected["method_pointer"],
                    "semantic_identity_resolved": True,
                    "resolution": "derived-runtime-object-field-return",
                }
            )

        (native_type_descriptor_evidence, native_type_flag_evidence,
         descriptor_operations) = _derive_native_descriptor_operations(
            snapshot=snapshot, image=image, classes=classes, class_addresses=class_addresses)
        resolved_operations.extend(descriptor_operations)

        method_parameter_count_evidence = _derive_method_parameter_count_field(
            snapshot=snapshot,
            resolved_operations=resolved_operations,
            method_records=classes.get("methods", []),
        )
        parameter_count_offset = method_parameter_count_evidence[
            "selected_byte_offset"
        ]
        type_from_handle_evidence: list[dict[str, Any]] = []
        for operation_key, runtime_owner in TYPE_FROM_HANDLE_OPERATION_OWNERS:
            candidates: list[tuple[dict[str, Any], dict[str, int]]] = []
            for method in classes.get("methods", []):
                if method.get("runtime_owner") != runtime_owner:
                    continue
                metadata_pointer = method.get("metadata_pointer", 0)
                arity = snapshot.read(
                    metadata_pointer + parameter_count_offset, 1
                ) if metadata_pointer else None
                code = _method_code(
                    snapshot=snapshot,
                    image=image,
                    method_pointer=method.get("method_pointer", 0),
                    method_pointers=method_pointers,
                )
                shape = _type_from_handle_shape(code or b"")
                if arity and arity[0] == 1 and shape is not None:
                    candidates.append((method, shape))
            if len(candidates) != 1:
                raise AcquisitionError(
                    "runtime type-from-handle wrapper is not unique "
                    f"(owner={runtime_owner}, candidates={len(candidates)})"
                )
            selected, shape = candidates[0]
            code = _method_code(
                snapshot=snapshot,
                image=image,
                method_pointer=selected["method_pointer"],
                method_pointers=method_pointers,
            )
            if code is None:
                raise AcquisitionError(
                    "runtime type-from-handle wrapper code is unavailable"
                )
            native_target = _relative_call_target(
                code,
                method_pointer=selected["method_pointer"],
                call_offset=shape["native_handle_call_offset"],
            )
            tail_offset = shape["managed_type_tail_offset"]
            tail_displacement = struct.unpack_from(
                "<i", code, tail_offset + 1
            )[0]
            managed_target = (
                selected["method_pointer"] + tail_offset + 5
                + tail_displacement
            )
            if any(
                target is None
                or not 0 <= target - snapshot.image_base < image.size_of_image
                or not image.executable_rva(target - snapshot.image_base)
                for target in (native_target, managed_target)
            ):
                raise AcquisitionError(
                    "runtime type-from-handle helper is outside current image"
                )
            type_from_handle_evidence.append(
                {
                    "operation_key": operation_key,
                    "runtime_owner": runtime_owner,
                    "parameter_count": 1,
                    "null_handle_guarded": True,
                    "native_handle_helper_owner_only": native_target,
                    "managed_type_helper_owner_only": managed_target,
                    "native_object_adjust_owner_only": shape[
                        "native_object_adjust"
                    ],
                }
            )
            resolved_operations.append(
                {
                    "key": operation_key,
                    "runtime_owner": runtime_owner,
                    "runtime_name": "GetTypeFromHandle",
                    "method_index": selected["method_index"],
                    "metadata_pointer": selected["metadata_pointer"],
                    "method_pointer": selected["method_pointer"],
                    "semantic_identity_resolved": True,
                    "resolution": (
                        "derived-null-guarded-native-handle-to-managed-type-wrapper"
                    ),
                }
            )

    contract = reflection_contract()
    resolved_keys = [operation["key"] for operation in resolved_operations]
    unresolved = [
        operation["key"]
        for operation in contract["operations"]
        if operation["key"] not in resolved_keys
    ]
    return {
        "schema": REFLECTION_SEMANTICS_SCHEMA,
        "status": "partially-resolved",
        "binary": binary_identity,
        "snapshot": snapshot_identity,
        "bootstrap_model_sha256": file_identity(bootstrap_model)["sha256"],
        "class_model_sha256": file_identity(class_model)["sha256"],
        "object_evidence": evidence_records,
        "object_field_evidence": object_field_evidence,
        "native_type_descriptor_evidence": native_type_descriptor_evidence,
        "native_type_flag_evidence": native_type_flag_evidence,
        "parameter_flag_evidence": parameter_flag_evidence,
        "sentinel_field_evidence": sentinel_field_evidence,
        "direct_dword_evidence": direct_dword_evidence,
        "nested_word_evidence": nested_word_evidence,
        "property_accessor_evidence": property_accessor_evidence,
        "method_name_decoder": method_name_decoder_evidence,
        "method_parameter_count": method_parameter_count_evidence,
        "type_from_handle_evidence": type_from_handle_evidence,
        "operations": resolved_operations,
        "contract": {
            "contract_id": contract["contract_id"],
            "operation_count": contract["operation_count"],
            "resolved_operation_keys": resolved_keys,
            "unresolved_operation_keys": unresolved,
            "semantic_operation_resolution_complete": False,
        },
        "checks": {
            "target_identity_bound": True,
            "snapshot_identity_bound": True,
            "bootstrap_identity_bound": True,
            "managed_string_class_derived": True,
            "cached_name_fields_semantically_unique": True,
            "name_getter_operation_count": len(evidence_records),
            "name_getters_semantically_unique": len(evidence_records)
            == len(NAME_OPERATION_DESCRIPTORS),
            "direct_object_getter_operation_count": len(object_field_evidence),
            "direct_object_getters_semantically_unique": len(
                object_field_evidence
            )
            == len(DIRECT_OBJECT_OPERATION_DESCRIPTORS),
            "parameter_flag_getter_operation_count": len(
                PARAMETER_FLAG_OPERATION_MASKS
            ),
            "parameter_flag_getters_semantically_unique": True,
            "parameter_flag_observations_complete": True,
            "sentinel_field_getter_operation_count": len(
                sentinel_field_evidence
            ),
            "sentinel_field_getters_semantically_unique": len(
                sentinel_field_evidence
            )
            == len(SENTINEL_FIELD_OPERATION_DESCRIPTORS),
            "direct_dword_getter_operation_count": len(direct_dword_evidence),
            "direct_dword_getters_semantically_unique": len(
                direct_dword_evidence
            )
            == len(DIRECT_DWORD_OPERATION_OWNERS),
            "property_accessor_operation_count": len(
                property_accessor_evidence
            ),
            "property_accessors_semantically_unique": len(
                property_accessor_evidence
            )
            == len(PROPERTY_ACCESSOR_OPERATIONS),
            "method_name_decoder_derived": True,
            "method_name_decoder_helpers_current_image_bound": True,
            "method_name_lazy_initializer_semantically_bound": True,
            "method_parameter_count_field_semantically_unique": True,
            "method_parameter_count_observations_complete": True,
            "method_attributes_nested_word_semantically_unique": True,
            "method_attributes_methodinfo_domain_complete": True,
            "native_type_descriptor_getter_operation_count": len(
                native_type_descriptor_evidence
            ),
            "native_type_descriptor_getters_semantically_unique": len(
                native_type_descriptor_evidence
            )
            == len(NATIVE_TYPE_DESCRIPTOR_OPERATION_OWNERS),
            "native_type_descriptor_fields_current_code_derived": all(
                evidence["descriptor_field_data_flow_proven"]
                and evidence["native_type_enum_convention_used"] is False
                and evidence["fixed_descriptor_length_used"] is False
                for evidence in native_type_descriptor_evidence
            ),
            "native_type_flag_getter_operation_count": len(
                native_type_flag_evidence
            ),
            "native_type_flag_getters_semantically_unique": len(
                native_type_flag_evidence
            )
            == len(NATIVE_TYPE_FLAG_OPERATION_DESCRIPTORS),
            "native_type_flag_object_domains_complete": all(
                evidence["set_count"] and evidence["clear_count"]
                for evidence in native_type_flag_evidence
            ),
            "type_from_handle_operation_count": len(
                type_from_handle_evidence
            ),
            "type_from_handle_wrapper_semantically_unique": len(
                type_from_handle_evidence
            )
            == len(TYPE_FROM_HANDLE_OPERATION_OWNERS),
            "all_operations_resolved": False,
            "official_runtime_attested": False,
            "acceptance_eligible": False,
            "fixed_address_used": False,
            "fixed_rva_used": False,
            "fixed_offset_used": False,
            "fixed_ordinal_used": False,
            "saved_reference_values_used": False,
            "external_runtime_component_used": False,
        },
    }


def inspect_reflection_semantics(
    *,
    binary: Path,
    snapshot: Path,
    bootstrap_model: Path,
    class_model: Path,
    output: Path,
) -> dict[str, Any]:
    model = discover_reflection_semantics(
        binary=binary,
        snapshot_path=snapshot,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
    )
    output = output.expanduser().resolve()
    _private_json(output, model)
    return {
        "schema": REFLECTION_SEMANTICS_SCHEMA,
        "status": model["status"],
        "resolved_operation_count": len(model["operations"]),
        "unresolved_operation_count": len(
            model["contract"]["unresolved_operation_keys"]
        ),
        "semantic_operation_resolution_complete": model["contract"][
            "semantic_operation_resolution_complete"
        ],
        "object_evidence": [
            {
                "runtime_owner": evidence["runtime_owner"],
                "object_reference_count": evidence["object_reference_count"],
                "selected_field_support": evidence["selected_field_support"],
            }
            for evidence in model["object_evidence"]
        ],
        "object_field_evidence": [
            {
                "operation_key": evidence["operation_key"],
                "object_reference_count": evidence["object_reference_count"],
                "selected_field_support": evidence["selected_field_support"],
            }
            for evidence in model["object_field_evidence"]
        ],
        "parameter_flag_evidence": {
            "object_reference_count": model["parameter_flag_evidence"][
                "object_reference_count"
            ],
            "set_counts": model["parameter_flag_evidence"]["set_counts"],
            "clear_counts": model["parameter_flag_evidence"]["clear_counts"],
        },
        "sentinel_field_evidence": [
            {
                "operation_key": evidence["operation_key"],
                "object_reference_count": evidence["object_reference_count"],
                "selected_field_support": evidence["selected_field_support"],
                "target_cache": evidence["target_cache"],
            }
            for evidence in model["sentinel_field_evidence"]
        ],
        "direct_dword_evidence": [
            {
                "operation_key": evidence["operation_key"],
                "object_reference_count": evidence["object_reference_count"],
                "distinct_value_count": evidence["distinct_value_count"],
            }
            for evidence in model["direct_dword_evidence"]
        ],
        "property_accessor_evidence": [
            {
                "operation_key": evidence["operation_key"],
                "property_object_reference_count": evidence[
                    "property_object_reference_count"
                ],
                "selected_field_support": evidence["selected_field_support"],
            }
            for evidence in model["property_accessor_evidence"]
        ],
        "method_name_decoder": {
            "method_record_count": model["method_name_decoder"][
                "method_record_count"
            ],
            "initialized_name_node_count": model["method_name_decoder"][
                "initialized_name_node_count"
            ],
            "lazy_name_node_count": model["method_name_decoder"][
                "lazy_name_node_count"
            ],
            "lazy_initializer_semantically_bound": model["checks"][
                "method_name_lazy_initializer_semantically_bound"
            ],
        },
        "method_parameter_count": {
            "semantic_sample_count": model["method_parameter_count"][
                "semantic_sample_count"
            ],
            "method_record_count": model["method_parameter_count"][
                "method_record_count"
            ],
            "candidate_field_count": model["method_parameter_count"][
                "candidate_field_count"
            ],
            "distinct_parameter_count": model["method_parameter_count"][
                "distinct_parameter_count"
            ],
            "field_semantically_unique": model["checks"][
                "method_parameter_count_field_semantically_unique"
            ],
        },
        "checks": model["checks"],
        "raw_addresses_offsets_and_method_identity_owner_only": True,
        "output": str(output),
    }


import struct
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError
from alpha.h04 import MemorySnapshot
from alpha.p14 import REFLECTION_BOOTSTRAP_SCHEMA
from alpha.p15 import RUNTIME_CLASS_SCHEMA
from alpha.c04 import MappedPE, PESection, RuntimeFunction
from alpha.h02 import file_identity, read_json


RUNTIME_TYPE_MATERIALIZER_SCHEMA = "alpha.runtime-type-materializer-model/v1"
_POINTER_BYTES = 8
_MAXIMUM_TYPE_KIND = 63
_MINIMUM_DEFINITION_DOMAIN_DENSITY = 0.99


def _positive_integer(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def _external_tail_jumps(
    image: MappedPE, function: RuntimeFunction
) -> list[dict[str, int]]:
    bounds = image.bounded_code(function.begin_rva, function.end_rva)
    if bounds is None:
        raise AcquisitionError("runtime type resolver function bytes are unavailable")
    begin, end = bounds
    output: list[dict[str, int]] = []
    for offset in range(begin, max(begin, end - 4)):
        if image._mapping[offset] != 0xE9:
            continue
        site_rva = function.begin_rva + offset - begin
        displacement = struct.unpack_from("<i", image._mapping, offset + 1)[0]
        target_rva = site_rva + 5 + displacement
        if (
            not image.executable_rva(target_rva)
            or function.begin_rva <= target_rva < function.end_rva
        ):
            continue
        output.append(
            {
                "site_rva": site_rva,
                "target_rva": target_rva,
                "site_offset_in_resolver": site_rva - function.begin_rva,
            }
        )
    return output


def _select_unique_external_tail_jump(
    candidates: list[dict[str, int]],
) -> dict[str, int]:
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime type materializer tail target is not unique "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def _aligned_pair_index(
    image: MappedPE,
) -> tuple[
    dict[tuple[int, int], list[int]],
    defaultdict[int, list[tuple[int, int, int]]],
    Counter[int],
    defaultdict[int, dict[int, list[tuple[int, int]]]],
    tuple[PESection, ...],
]:


    sections = tuple(image.readonly_sections)
    occurrences: dict[tuple[int, int], list[int]] = {}
    families: defaultdict[int, list[tuple[int, int, int]]] = defaultdict(list)
    family_support: Counter[int] = Counter()
    family_overflow: defaultdict[int, dict[int, list[tuple[int, int]]]] = defaultdict(
        dict
    )
    mapping = memoryview(image._mapping)
    occurrence_setdefault = occurrences.setdefault
    unpack_pairs = struct.Struct("<QQ").iter_unpack
    for section_index, section in enumerate(sections):
        beginning = section.raw_offset + (-section.raw_offset % 16)
        window = (section.raw_end - beginning) // 16
        if window <= 0:
            continue
        offset = beginning
        for data, flags in unpack_pairs(
            mapping[beginning : beginning + window * 16]
        ):


            fresh = [1, offset, section_index]
            entry = occurrence_setdefault((data, flags), fresh)
            if entry is not fresh:
                entry[0] += 1
            if flags and not flags & 0xFFFF and not flags >> 32:
                kind = flags >> 16
                if kind <= _MAXIMUM_TYPE_KIND:
                    family_support[kind] += 1
                    if data < 0x100000000:
                        families[kind].append((data, offset, section_index))
                    else:
                        overflow = family_overflow[kind]
                        sites = overflow.get(data)
                        if sites is None:
                            overflow[data] = [(offset, section_index)]
                        else:
                            sites.append((offset, section_index))
            offset += 16
    return occurrences, families, family_support, family_overflow, sections


def _descriptor_field_candidates_from_index(
    *,
    snapshot: MemorySnapshot,
    classes: list[dict[str, Any]],
    header_qwords: int,
    occurrences: dict[tuple[int, int], list[int]],
    sections: tuple[PESection, ...],
) -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    for field in range(header_qwords - 1):
        observations: list[dict[str, Any]] = []
        valid = True
        for item in classes:
            values = snapshot.qwords(item["class_pointer"] + field * 8, 2)
            entry = None if values is None else occurrences.get(values)
            if entry is None or entry[0] != 1:
                valid = False
                break
            section = sections[entry[2]]
            observations.append(
                {
                    "runtime_owner": item["runtime_owner"],
                    "class_pointer": item["class_pointer"],
                    "definition_index": values[0],
                    "type_flags": values[1],
                    "static_descriptor_rva": section.virtual_address
                    + entry[1]
                    - section.raw_offset,
                }
            )
        indexes = {item["definition_index"] for item in observations}
        flags = {item["type_flags"] for item in observations}
        if (
            valid
            and len(observations) == len(classes)
            and len(indexes) == len(classes)
            and len(flags) == 1
            and _well_formed_type_flags(next(iter(flags)))
        ):
            candidates.append(
                {
                    "descriptor_qword": field,
                    "definition_flag": next(iter(flags)),
                    "observations": observations,
                }
            )
    return candidates


def _select_descriptor_field(candidates: list[dict[str, Any]]) -> dict[str, Any]:
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime embedded type descriptor field is not semantically unique "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def _class_name_field_candidates(
    *,
    snapshot: MemorySnapshot,
    classes: list[dict[str, Any]],
    header_qwords: int,
) -> list[int]:
    candidates: list[int] = []
    for field in range(header_qwords):
        complete = True
        for item in classes:
            values = snapshot.qwords(item["class_pointer"] + field * 8, 1)
            owner = item.get("runtime_owner")
            if (
                not values
                or not isinstance(owner, str)
                or "." not in owner
                or snapshot.c_string(values[0], maximum=512)
                != owner.rsplit(".", 1)[1]
            ):
                complete = False
                break
        if complete:
            candidates.append(field)
    return candidates


def _select_class_name_field(candidates: list[int]) -> int:
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime class name field is not semantically unique "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def _well_formed_type_flags(value: int) -> bool:
    return (
        value > 0
        and value >> 32 == 0
        and value & 0xFFFF == 0
        and 1 <= value >> 16 <= _MAXIMUM_TYPE_KIND
    )


def _select_definition_flag_kinds(
    families: dict[int, list[tuple[int, int, int]]],
    *,
    known_kind: int,
    minimum_family_size: int,
) -> set[int]:


    known_records = families.get(known_kind, ())
    known_values = [record[0] for record in known_records]
    if (
        len(known_values) < minimum_family_size
        or len(set(known_values)) != len(known_values)
    ):
        raise AcquisitionError("runtime definition descriptor family is incomplete")
    selected = {known_kind}
    selected_values = set(known_values)

    candidate_families: list[tuple[int, int, set[int]]] = []
    for kind, records in families.items():
        if kind == known_kind or len(records) < minimum_family_size:
            continue
        values = [record[0] for record in records]
        value_set = set(values)
        if (
            len(value_set) != len(values)
            or not value_set
        ):
            continue
        candidate_families.append((len(value_set), kind, value_set))
    for _size, kind, value_set in sorted(candidate_families, reverse=True):
        if selected_values.isdisjoint(value_set):
            selected.add(kind)
            selected_values.update(value_set)

            if len(selected_values) / (max(selected_values) + 1) >= (
                _MINIMUM_DEFINITION_DOMAIN_DENSITY
            ):
                break
    if len(selected) < 2:
        raise AcquisitionError(
            "runtime value/reference definition descriptor families are incomplete"
        )
    return selected


def _complete_descriptor_domain_from_index(
    *,
    families: dict[int, list[tuple[int, int, int]]],
    family_support: Counter[int],
    family_overflow: dict[int, dict[int, list[tuple[int, int]]]],
    sections: tuple[PESection, ...],
    selected_kinds: set[int],
) -> tuple[list[tuple[int, int, int]], dict[str, Any]]:


    definitions: dict[int, tuple[int, int, int]] = {}
    for kind in sorted(selected_kinds):
        for data, offset, section_index in families[kind]:
            if data in definitions:
                raise AcquisitionError(
                    "runtime definition descriptor index is duplicated"
                )
            definitions[data] = (kind, offset, section_index)
        for data, sites in family_overflow.get(kind, {}).items():
            if data in definitions or len(sites) > 1:
                raise AcquisitionError(
                    "runtime definition descriptor index is duplicated"
                )
            offset, section_index = sites[0]
            definitions[data] = (kind, offset, section_index)
    if not definitions:
        raise AcquisitionError("runtime definition descriptor domain is empty")
    maximum = max(definitions)
    if maximum <= 0:
        raise AcquisitionError("runtime definition descriptor bound is invalid")
    density = len(definitions) / (maximum + 1)
    if density < _MINIMUM_DEFINITION_DOMAIN_DENSITY:
        raise AcquisitionError(
            "runtime definition descriptor domain is not a dense current prefix"
        )
    missing = sorted(set(range(maximum + 1)) - set(definitions))
    candidates_by_index: defaultdict[int, list[tuple[int, int, int]]] = (
        defaultdict(list)
    )
    missing_set = set(missing)
    for kind, records in families.items():
        if kind in selected_kinds:
            continue
        for data, offset, section_index in records:
            if data in missing_set:
                candidates_by_index[data].append((kind, offset, section_index))
    for kind, sites_by_data in family_overflow.items():
        if kind in selected_kinds:
            continue
        for data, sites in sites_by_data.items():
            if data in missing_set:
                for offset, section_index in sites:
                    candidates_by_index[data].append((kind, offset, section_index))
    primitive_records: list[tuple[int, int, int]] = []
    for index in missing:
        candidates = candidates_by_index[index]
        if len(candidates) > 1:
            minimum_support = min(
                family_support[candidate[0]]
                for candidate in candidates
            )
            candidates = [
                candidate
                for candidate in candidates
                if family_support[candidate[0]] == minimum_support
            ]
        if len(candidates) != 1:
            raise AcquisitionError(
                "runtime primitive definition descriptor is not unique "
                f"(index={index}, candidates={len(candidates)})"
            )
        definitions[index] = candidates[0]
        primitive_records.append(candidates[0])
    if sorted(definitions) != list(range(maximum + 1)):
        raise AcquisitionError(
            "runtime definition descriptor domain is not contiguous"
        )
    ordered = [definitions[index] for index in range(maximum + 1)]
    return ordered, {
        "definition_count": maximum + 1,
        "dominant_definition_count": maximum + 1 - len(missing),
        "primitive_definition_count": len(missing),
        "dominant_domain_density": density,
        "primitive_type_flag_count": len(
            {record[0] << 16 for record in primitive_records}
        ),
    }


def _load_and_bind(
    *,
    binary: Path,
    snapshot: Path,
    bootstrap_model: Path,
    class_model: Path,
) -> tuple[
    dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]
]:
    binary_identity = file_identity(binary)
    snapshot_identity = file_identity(snapshot)
    bootstrap_identity = file_identity(bootstrap_model)
    bootstrap = read_json(bootstrap_model)
    classes = read_json(class_model)
    if (
        not isinstance(bootstrap, dict)
        or bootstrap.get("schema") != REFLECTION_BOOTSTRAP_SCHEMA
    ):
        raise AcquisitionError("runtime type materializer bootstrap is invalid")
    if not isinstance(classes, dict) or classes.get("schema") != RUNTIME_CLASS_SCHEMA:
        raise AcquisitionError("runtime type materializer class model is invalid")
    if (
        bootstrap.get("binary", {}).get("sha256") != binary_identity["sha256"]
        or classes.get("snapshot", {}).get("sha256")
        != snapshot_identity["sha256"]
        or classes.get("snapshot", {}).get("bytes") != snapshot_identity["bytes"]
        or classes.get("bootstrap_model_sha256") != bootstrap_identity["sha256"]
    ):
        raise AcquisitionError("runtime type materializer input binding is stale")
    required_bootstrap = ("state_slot_rva", "type_resolver_helper_rva")
    if any(not _positive_integer(bootstrap.get(key)) for key in required_bootstrap):
        raise AcquisitionError("runtime type materializer resolver binding is absent")
    class_checks = classes.get("checks")
    if (
        not isinstance(class_checks, dict)
        or class_checks.get("owner_root_contract_exact") is not True
        or class_checks.get("all_contract_owner_classes_present") is not True
        or class_checks.get("vtable_boundary_derived") is not True
    ):
        raise AcquisitionError("runtime type materializer class evidence is incomplete")
    return binary_identity, snapshot_identity, bootstrap, classes


def discover_runtime_type_materializer(
    *,
    binary: Path,
    snapshot: Path,
    bootstrap_model: Path,
    class_model: Path,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    snapshot = snapshot.expanduser().resolve()
    bootstrap_model = bootstrap_model.expanduser().resolve()
    class_model = class_model.expanduser().resolve()
    binary_identity, snapshot_identity, bootstrap, class_data = _load_and_bind(
        binary=binary,
        snapshot=snapshot,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
    )
    raw_classes = class_data.get("classes")
    layout = class_data.get("layout")
    if not isinstance(raw_classes, list) or not isinstance(layout, dict):
        raise AcquisitionError("runtime type materializer class evidence is invalid")
    classes = [dict(item) for item in raw_classes if isinstance(item, dict)]
    header_qwords = layout.get("vtable_start_qword")
    if len(classes) != len(raw_classes) or not _positive_integer(header_qwords):
        raise AcquisitionError("runtime type materializer class layout is invalid")

    with MemorySnapshot(snapshot) as memory, MappedPE(binary) as image:
        if memory.image_bytes != image.size_of_image:
            raise AcquisitionError("runtime type materializer image binding is stale")
        resolver = image.containing_function(bootstrap["type_resolver_helper_rva"])
        if resolver is None or resolver.begin_rva != bootstrap["type_resolver_helper_rva"]:
            raise AcquisitionError(
                "runtime type resolver function boundary is inconsistent"
            )
        tail_candidates = _external_tail_jumps(image, resolver)
        tail = _select_unique_external_tail_jump(tail_candidates)
        occurrences, families, family_support, family_overflow, sections = (
            _aligned_pair_index(image)
        )
        descriptor_candidates = _descriptor_field_candidates_from_index(
            snapshot=memory,
            classes=classes,
            header_qwords=header_qwords,
            occurrences=occurrences,
            sections=sections,
        )
        descriptor_field = _select_descriptor_field(descriptor_candidates)
        class_name_field = _select_class_name_field(
            _class_name_field_candidates(
                snapshot=memory,
                classes=classes,
                header_qwords=header_qwords,
            )
        )
        selected_kinds = _select_definition_flag_kinds(
            families,
            known_kind=descriptor_field["definition_flag"] >> 16,
            minimum_family_size=len(classes),
        )
        descriptors, domain = _complete_descriptor_domain_from_index(
            families=families,
            family_support=family_support,
            family_overflow=family_overflow,
            sections=sections,
            selected_kinds=selected_kinds,
        )

    serialized_descriptors = [
        {
            "type_definition_index": index,
            "type_flags": kind << 16,
            "descriptor_rva": sections[section_index].virtual_address
            + offset
            - sections[section_index].raw_offset,
            "section_name": sections[section_index].name,
        }
        for index, (kind, offset, section_index) in enumerate(descriptors)
    ]
    return {
        "schema": RUNTIME_TYPE_MATERIALIZER_SCHEMA,
        "status": "static-definition-domain-discovered",
        "binary": {
            "bytes": binary_identity["bytes"],
            "sha256": binary_identity["sha256"],
            "size_of_image": class_data["snapshot"]["image_bytes"],
        },
        "snapshot": {
            "bytes": snapshot_identity["bytes"],
            "sha256": snapshot_identity["sha256"],
        },
        "inputs": {
            "bootstrap_model_sha256": file_identity(bootstrap_model)["sha256"],
            "class_model_sha256": file_identity(class_model)["sha256"],
        },
        "resolver": {
            "state_slot_rva": bootstrap["state_slot_rva"],
            "type_resolver_helper_rva": bootstrap["type_resolver_helper_rva"],
            "resolver_function_begin_rva": resolver.begin_rva,
            "resolver_function_end_rva": resolver.end_rva,
            "external_tail_jump_candidates": tail_candidates,
            "type_info_materializer_rva": tail["target_rva"],
        },
        "layout": {
            "embedded_descriptor_qword": descriptor_field["descriptor_qword"],
            "embedded_descriptor_byte_offset": descriptor_field[
                "descriptor_qword"
            ]
            * _POINTER_BYTES,
            "definition_type_flags": sorted(
                kind << 16 for kind in selected_kinds
            ),
            "class_name_pointer_qword": class_name_field,
        },
        "inventory_layout": {
            "class_name_pointer_qword": class_name_field,
            "parent_class_qword": layout["parent_class_qword"],
            "parent_class_byte_offset": layout.get(
                "parent_class_byte_offset",
                layout["parent_class_qword"] * _POINTER_BYTES,
            ),
            "parent_class_pointer_encoding": layout.get(
                "parent_class_pointer_encoding", "native-pointer"
            ),
            "class_declaring_qword": 0,
            "method_array_pointer_qword": layout[
                "method_array_pointer_qword"
            ],
            "method_count_byte_offset": layout["method_count_byte_offset"],
            "method_declaring_class_qword": layout["declaring_class_qword"],
            "method_pointer_qword": layout["method_pointer_qword"],
        },
        "owner_validation_contract": descriptor_field["observations"],
        "definition_domain": domain,
        "type_definitions": serialized_descriptors,
        "checks": {
            "binary_identity_bound": True,
            "snapshot_identity_bound": True,
            "bootstrap_identity_bound": True,
            "class_model_identity_bound": True,
            "type_resolver_function_bound": True,
            "unique_external_tail_materializer_derived": True,
            "embedded_descriptor_field_semantically_unique": True,
            "class_name_field_semantically_unique": True,
            "owner_static_descriptors_exact": True,
            "definition_flag_families_derived": True,
            "type_definition_indexes_contiguous": len(serialized_descriptors)
            == domain["definition_count"],
            "primitive_descriptor_holes_uniquely_completed": True,
            "materializer_runtime_validated": False,
            "all_type_definitions_materialized": False,
            "fixed_address_used": False,
            "fixed_rva_used": False,
            "fixed_offset_used": False,
            "fixed_version_used": False,
            "saved_type_count_used": False,
            "saved_type_index_used": False,
            "saved_descriptor_used": False,
            "external_runtime_component_used": False,
        },
    }


def inspect_runtime_type_materializer(
    *,
    binary: Path,
    snapshot: Path,
    bootstrap_model: Path,
    class_model: Path,
    output: Path,
) -> dict[str, Any]:
    model = discover_runtime_type_materializer(
        binary=binary,
        snapshot=snapshot,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
    )
    output = output.expanduser().resolve()
    _private_json(output, model)
    domain = model["definition_domain"]
    return {
        "schema": RUNTIME_TYPE_MATERIALIZER_SCHEMA,
        "status": "discovered",
        "phase": model["status"],
        "binary": model["binary"],
        "snapshot": model["snapshot"],
        "type_definition_count": domain["definition_count"],
        "dominant_definition_count": domain["dominant_definition_count"],
        "primitive_definition_count": domain["primitive_definition_count"],
        "dominant_domain_density": domain["dominant_domain_density"],
        "owner_validation_count": len(model["owner_validation_contract"]),
        "checks": model["checks"],
        "raw_rvas_offsets_descriptors_and_owner_pointers_owner_only": True,
        "output": str(output),
    }


import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError
from alpha.h04 import MemorySnapshot
from alpha.p14 import REFLECTION_BOOTSTRAP_SCHEMA
from alpha.p15 import _is_executable_pointer, _is_metadata_pointer
from alpha.h02 import file_identity, read_json


def _unique_identity_bound_json(
    directory: Path, *, sha256: str, schema: str, label: str
) -> tuple[Path, dict[str, Any]]:
    matches: list[tuple[Path, dict[str, Any]]] = []
    for path in directory.glob("*.json"):
        try:
            if file_identity(path)["sha256"] != sha256:
                continue
            model = read_json(path)
        except (OSError, ValueError):
            continue
        if isinstance(model, dict) and model.get("schema") == schema:
            matches.append((path.resolve(), model))
    if len(matches) != 1:
        raise AcquisitionError(
            f"runtime member attribute {label} is not uniquely identity-bound"
        )
    return matches[0]


def _select_fill_operation(
    rows: list[dict[str, int]], *, arity: int, label: str
) -> dict[str, int]:
    candidates = [
        row
        for row in rows
        if row["arity"] == arity
        and row["attributes"] & 0x10
        and row["method_pointer"] > 0
    ]
    if len(candidates) != 1:
        raise AcquisitionError(
            f"runtime member attribute {label} fill operation is ambiguous "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def _follow_relative_jumps(snapshot: MemorySnapshot, pointer: int) -> int:
    current = pointer
    visited: set[int] = set()
    while True:
        if current in visited:
            raise AcquisitionError(
                "runtime member attribute operation contains a jump cycle"
            )
        visited.add(current)
        raw = snapshot.read(current, 8)
        if raw is None:
            raise AcquisitionError(
                "runtime member attribute operation body is unavailable"
            )
        if raw[0] == 0xE9:
            current += 5 + struct.unpack_from("<i", raw, 1)[0]
            continue
        if raw[0] == 0xEB:
            current += 2 + struct.unpack_from("<b", raw, 1)[0]
            continue
        return current


def _derive_request_mask(
    snapshot: MemorySnapshot, *, method_pointer: int
) -> tuple[int, dict[str, int]]:


    implementation = _follow_relative_jumps(snapshot, method_pointer)
    raw = snapshot.read(implementation, 160)
    if raw is None:
        raise AcquisitionError(
            "runtime member attribute request-mask body is unavailable"
        )
    bits: set[int] = set()
    for index in range(len(raw) - 2):


        if raw[index] != 0xF6 or raw[index + 1] & 0xF8 != 0xC0:
            continue
        immediate = raw[index + 2]
        if immediate and immediate & (immediate - 1) == 0:
            bits.add(immediate)
    if len(bits) < 2:
        raise AcquisitionError(
            "runtime member attribute request-mask shape is ambiguous"
        )
    mask = 0
    for bit in bits:
        mask |= bit
    return mask, {
        "implementation_pointer_owner_only": implementation,
        "implementation_body_bytes": len(raw),
        "request_mask_bit_count": len(bits),
        "request_mask_candidate_count": 1,
    }


def derive_member_attribute_fill_operations(
    *,
    semantics: dict[str, Any],
    class_model: dict[str, Any],
    snapshot_path: Path,
    expected_executable_sha256: str,
) -> dict[str, Any]:


    class_checks = class_model.get("checks", {})
    required_checks = (
        "all_contract_owner_classes_present",
        "declaring_class_field_unique",
        "method_layout_semantically_unique",
        "method_pointer_field_unique",
        "snapshot_image_binding_matches",
        "vtable_boundary_derived",
    )
    snapshot_path = snapshot_path.expanduser().resolve()
    if (
        class_model.get("status") != "discovered"
        or any(class_checks.get(key) is not True for key in required_checks)
        or class_model.get("snapshot", {}).get("sha256")
        != file_identity(snapshot_path)["sha256"]
        or semantics.get("snapshot", {}).get("sha256")
        != file_identity(snapshot_path)["sha256"]
        or semantics.get("binary", {}).get("sha256")
        != expected_executable_sha256
    ):
        raise AcquisitionError("runtime member attribute structural inputs are stale")

    arity_offset = semantics.get("method_parameter_count", {}).get(
        "selected_byte_offset"
    )
    layout = class_model.get("layout", {})
    method_array_qword = layout.get("method_array_pointer_qword")
    method_count_offset = layout.get("method_count_byte_offset")
    declaring_qword = layout.get("declaring_class_qword")
    method_pointer_qword = layout.get("method_pointer_qword")
    if (
        not isinstance(arity_offset, int)
        or arity_offset < 6
        or not isinstance(method_array_qword, int)
        or method_array_qword < 0
        or not isinstance(method_count_offset, int)
        or method_count_offset < 0
        or not isinstance(declaring_qword, int)
        or declaring_qword < 0
        or not isinstance(method_pointer_qword, int)
        or method_pointer_qword < 0
    ):
        raise AcquisitionError("runtime member attribute method layout is unavailable")

    bootstrap_sha = semantics.get("bootstrap_model_sha256")
    if not isinstance(bootstrap_sha, str) or len(bootstrap_sha) != 64:
        raise AcquisitionError("runtime member attribute bootstrap identity is absent")
    bootstrap_path, bootstrap = _unique_identity_bound_json(
        snapshot_path.parent,
        sha256=bootstrap_sha,
        schema=REFLECTION_BOOTSTRAP_SCHEMA,
        label="bootstrap",
    )
    if bootstrap.get("binary", {}).get("sha256") != expected_executable_sha256:
        raise AcquisitionError("runtime member attribute bootstrap target differs")
    cache_by_owner = {
        f"{row.get('namespace')}.{row.get('type_name')}": row
        for row in bootstrap.get("type_caches", [])
        if isinstance(row, dict)
    }
    required_owners = (
        "System.Reflection.MonoPropertyInfo",
        "System.Reflection.MonoEventInfo",
    )
    if any(owner not in cache_by_owner for owner in required_owners):
        raise AcquisitionError("runtime member attribute info type caches are absent")

    method_rows: dict[str, list[dict[str, int]]] = {}
    class_pointers: dict[str, int] = {}
    property_request_mask = 0
    property_request_evidence: dict[str, int] = {}
    with MemorySnapshot(snapshot_path) as snapshot:
        if snapshot.image_bytes != bootstrap.get("binary", {}).get("size_of_image"):
            raise AcquisitionError("runtime member attribute snapshot image differs")
        for owner in required_owners:
            cache = cache_by_owner[owner]
            result_slot_rva = cache.get("result_slot_rva")
            if (
                not isinstance(result_slot_rva, int)
                or not 0 <= result_slot_rva < snapshot.image_bytes
            ):
                raise AcquisitionError(
                    "runtime member attribute type cache slot is invalid"
                )
            cached = snapshot.qwords(snapshot.image_base + result_slot_rva, 1)
            class_pointer = cached[0] if cached else 0
            if not _is_metadata_pointer(snapshot, class_pointer):
                raise AcquisitionError(
                    f"runtime member attribute class is unavailable: {owner}"
                )
            class_pointers[owner] = class_pointer
            header_bytes = max(
                (method_array_qword + 1) * 8,
                method_count_offset + 2,
            )
            header = snapshot.read(class_pointer, header_bytes)
            if header is None:
                raise AcquisitionError(
                    "runtime member attribute class header is unavailable"
                )
            method_array = struct.unpack_from(
                "<Q", header, method_array_qword * 8
            )[0]
            method_count = struct.unpack_from(
                "<H", header, method_count_offset
            )[0]
            methods = snapshot.qwords(method_array, method_count)
            if not methods or len(methods) != method_count:
                raise AcquisitionError(
                    "runtime member attribute method array is unavailable"
                )
            rows: list[dict[str, int]] = []
            for metadata_pointer in methods:
                required_bytes = max(
                    arity_offset + 1,
                    (declaring_qword + 1) * 8,
                    (method_pointer_qword + 1) * 8,
                )
                raw = snapshot.read(metadata_pointer, required_bytes)
                if raw is None:
                    raise AcquisitionError(
                        "runtime member attribute method record is unavailable"
                    )
                declaring = struct.unpack_from(
                    "<Q", raw, declaring_qword * 8
                )[0]
                method_pointer = struct.unpack_from(
                    "<Q", raw, method_pointer_qword * 8
                )[0]


                slot, impl_attributes, attributes, arity = struct.unpack_from(
                    "<HHHB", raw, arity_offset - 6
                )
                if declaring != class_pointer:
                    raise AcquisitionError(
                        "runtime member attribute declaring class differs"
                    )
                if method_pointer and not _is_executable_pointer(
                    snapshot, method_pointer
                ):
                    raise AcquisitionError(
                        "runtime member attribute method pointer is not executable"
                    )
                rows.append(
                    {
                        "metadata_pointer": metadata_pointer,
                        "method_pointer": method_pointer,
                        "attributes": attributes,
                        "impl_attributes": impl_attributes,
                        "slot": slot,
                        "arity": arity,
                    }
                )
            method_rows[owner] = rows

        selected_for_mask = _select_fill_operation(
            method_rows["System.Reflection.MonoPropertyInfo"],
            arity=3,
            label="property",
        )
        property_request_mask, property_request_evidence = (
            _derive_request_mask(
                snapshot, method_pointer=selected_for_mask["method_pointer"]
            )
        )

    property_fill = _select_fill_operation(
        method_rows["System.Reflection.MonoPropertyInfo"],
        arity=3,
        label="property",
    )
    event_fill = _select_fill_operation(
        method_rows["System.Reflection.MonoEventInfo"],
        arity=2,
        label="event",
    )

    def operation(
        row: dict[str, int], *, owner: str, arity: int
    ) -> dict[str, Any]:
        return {
            "runtime_owner": owner,
            "class_pointer": class_pointers[owner],
            "metadata_pointer": row["metadata_pointer"],
            "method_pointer": row["method_pointer"],
            "parameter_count": arity,
            "semantic_identity_resolved": True,
            "derivation": (
                "current-runtime-owner-static-shape-arity-and-live-info-layout"
            ),
        }

    return {
        "status": "resolved",
        "bootstrap": file_identity(bootstrap_path),
        "operations": {
            "property.info_fill": operation(
                property_fill,
                owner="System.Reflection.MonoPropertyInfo",
                arity=3,
            ) | {"request_mask": property_request_mask},
            "event.info_fill": operation(
                event_fill,
                owner="System.Reflection.MonoEventInfo",
                arity=2,
            ),
        },
        "evidence": {
            "property_info_method_count": len(
                method_rows["System.Reflection.MonoPropertyInfo"]
            ),
            "property_fill_candidate_count": 1,
            "property_request_mask": property_request_mask,
            **{
                f"property_{key}": value
                for key, value in property_request_evidence.items()
            },
            "event_info_method_count": len(
                method_rows["System.Reflection.MonoEventInfo"]
            ),
            "event_fill_candidate_count": 1,
            "method_arity_offset_owner_only": arity_offset,
            "class_and_method_layout_current_snapshot_derived": True,
            "live_info_field_layout_validation_required": True,
            "saved_method_name_used": False,
            "saved_method_ordinal_used": False,
            "saved_dispatch_used": False,
            "fixed_rva_used": False,
            "fixed_offset_used": False,
            "prior_version_input_used": False,
        },
    }


from alpha.h02 import windows_run as _host_run

import copy
import json
import math
import os
import struct
import subprocess
import time
from pathlib import Path
from typing import Any, Callable, Iterable

from alpha.p12 import _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build, runtime_injector_source
from alpha.h01 import AcquisitionError
from alpha.p14 import REFLECTION_BOOTSTRAP_SCHEMA
from alpha.p15 import RUNTIME_CLASS_SCHEMA
from alpha.c04 import MappedPE, PESection, RuntimeFunction
from alpha.h02 import file_identity, read_json


RUNTIME_NATIVE_HELPER_SCHEMA = "alpha.runtime-native-helper-model/v1"
RUNTIME_NATIVE_HELPER_PLAN_SCHEMA = "alpha.runtime-native-helper-plan/v1"
RUNTIME_NATIVE_HELPER_VALIDATION_SCHEMA = (
    "alpha.runtime-native-helper-validation/v1"
)
MAXIMUM_ITERATOR_FUNCTION_BYTES = 4096


def _memory_operand(
    code: bytes | memoryview,
    modrm_offset: int,
    rex: int,
) -> tuple[int | None, int, int] | None:

    if modrm_offset >= len(code):
        return None
    modrm = code[modrm_offset]
    mode = modrm >> 6
    rm = modrm & 7
    if mode == 3:
        return None
    cursor = modrm_offset + 1
    base = rm | (8 if rex & 1 else 0)
    if rm == 4:
        if cursor >= len(code):
            return None
        sib = code[cursor]
        cursor += 1
        sib_base = sib & 7
        base = sib_base | (8 if rex & 1 else 0)
        if mode == 0 and sib_base == 5:
            base = None
    elif mode == 0 and rm == 5:
        base = None
    displacement = 0
    if mode == 1:
        if cursor >= len(code):
            return None
        displacement = struct.unpack_from("<b", code, cursor)[0]
        cursor += 1
    elif mode == 2 or (mode == 0 and base is None):
        if cursor + 4 > len(code):
            return None
        displacement = struct.unpack_from("<i", code, cursor)[0]
        cursor += 4
    return base, displacement, cursor


def _iter_instruction_prefixes(code: bytes | memoryview) -> Iterable[tuple[int, int, int]]:

    for start in range(len(code)):
        first = code[start]
        if 0x40 <= first <= 0x4F:
            if start + 1 < len(code):
                yield start, start + 1, first
        else:
            yield start, start, 0


_WORD_LOAD_PREFIX = b"\x0f\xb7"


def _code_bytes(code: bytes | memoryview) -> bytes:

    return code if isinstance(code, bytes) else bytes(code)


def _rex_opcode_positions(data: bytes, opcodes: tuple[int, ...]) -> list[int]:

    positions: list[int] = []
    for opcode in opcodes:
        needle = bytes((opcode,))
        position = data.find(needle)
        while position >= 0:
            prefix = data[position - 1] if position else 0
            if 0x48 <= prefix <= 0x4F:
                positions.append(position)
            position = data.find(needle, position + 1)
    positions.sort()
    return positions


def _member_access_bases_word_load(
    code: bytes | memoryview,
    *,
    displacement: int,
) -> list[tuple[int, int]]:

    data = _code_bytes(code)
    return _scan_word_load_accesses(
        data,
        displacement=displacement,
        find=data.find,
        origin=0,
        limit=len(data),
    )


def _member_access_bases_word_load_section(
    image: MappedPE,
    section: PESection,
    *,
    displacement: int,
) -> list[tuple[int, int]]:

    mapping = image._mapping
    view = memoryview(mapping)[section.raw_offset : section.raw_end]
    try:
        return _scan_word_load_accesses(
            view,
            displacement=displacement,
            find=mapping.find,
            origin=section.raw_offset,
            limit=section.raw_end,
        )
    finally:
        view.release()


def _scan_word_load_accesses(
    view: bytes | memoryview,
    *,
    displacement: int,
    find: Callable[[bytes, int, int], int],
    origin: int,
    limit: int,
) -> list[tuple[int, int]]:

    length = len(view)
    accesses: list[tuple[int, int]] = []
    position = find(_WORD_LOAD_PREFIX, origin, limit)
    while position >= 0:
        index = position - origin

        if index + 2 < length:
            bare = _memory_operand(view, index + 2, 0)
            bare_hit: tuple[int, int] | None = None
            if bare is not None:
                base, observed, _end = bare
                if base is not None and observed == displacement:
                    bare_hit = (index, base)

            if index > 0 and 0x40 <= view[index - 1] <= 0x4F:
                rex = view[index - 1]
                rex_operand = _memory_operand(view, index + 2, rex)
                if rex_operand is not None:
                    rex_base, rex_observed, _end = rex_operand
                    if rex_base is not None and rex_observed == displacement:
                        accesses.append((index - 1, rex_base))
            if bare_hit is not None:
                accesses.append(bare_hit)
        position = find(_WORD_LOAD_PREFIX, position + 1, limit)
    return accesses


def _member_access_bases(
    code: bytes | memoryview,
    *,
    displacement: int,
    word_load: bool,
) -> list[tuple[int, int]]:
    data = _code_bytes(code)
    if word_load:
        return _member_access_bases_word_load(data, displacement=displacement)


    total = len(data)
    accesses: list[tuple[int, int]] = []
    for position in _rex_opcode_positions(data, (0x03, 0x8B, 0x8D)):
        if position + 2 > total:
            continue
        operand = _memory_operand(data, position + 1, data[position - 1])
        if operand is None:
            continue
        base, observed_displacement, _end = operand
        if base is not None and observed_displacement == displacement:
            accesses.append((position - 1, base))
    return accesses


def _register_moves(code: bytes | memoryview) -> list[tuple[int, int, int]]:
    data = _code_bytes(code)
    total = len(data)
    moves: list[tuple[int, int, int]] = []
    for position in _rex_opcode_positions(data, (0x89, 0x8B)):
        if position + 2 > total:
            continue
        rex = data[position - 1]
        modrm = data[position + 1]
        if modrm >> 6 != 3:
            continue
        reg = ((modrm >> 3) & 7) | (8 if rex & 4 else 0)
        rm = (modrm & 7) | (8 if rex & 1 else 0)
        destination, source = (rm, reg) if data[position] == 0x89 else (reg, rm)
        moves.append((position - 1, destination, source))
    return moves


def _argument_aliases(code: bytes | memoryview, argument_register: int) -> set[int]:
    aliases = {argument_register}
    moves = _register_moves(code)
    changed = True
    while changed:
        changed = False
        for _offset, destination, source in moves:
            if source in aliases and destination not in aliases:
                aliases.add(destination)
                changed = True
    return aliases


def _qword_loads(code: bytes | memoryview) -> list[tuple[int, int, int]]:
    data = _code_bytes(code)
    total = len(data)
    loads: list[tuple[int, int, int]] = []
    for position in _rex_opcode_positions(data, (0x8B,)):
        if position + 2 > total:
            continue
        rex = data[position - 1]
        modrm = data[position + 1]
        if modrm >> 6 == 3:
            continue
        operand = _memory_operand(data, position + 1, rex)
        if operand is None:
            continue
        base, displacement, _end = operand
        if base is None or displacement:
            continue
        destination = ((modrm >> 3) & 7) | (8 if rex & 4 else 0)
        loads.append((position - 1, destination, base))
    return loads


def _qword_member_loads(
    code: bytes | memoryview,
) -> list[tuple[int, int, int, int]]:
    data = _code_bytes(code)
    total = len(data)
    loads: list[tuple[int, int, int, int]] = []
    for position in _rex_opcode_positions(data, (0x8B,)):
        if position + 2 > total:
            continue
        rex = data[position - 1]
        modrm = data[position + 1]
        if modrm >> 6 == 3:
            continue
        operand = _memory_operand(data, position + 1, rex)
        if operand is None:
            continue
        base, displacement, _end = operand
        if base is None:
            continue
        destination = ((modrm >> 3) & 7) | (8 if rex & 4 else 0)
        loads.append((position - 1, destination, base, displacement))
    return loads


def _qword_stores(code: bytes | memoryview) -> list[tuple[int, int, int]]:
    data = _code_bytes(code)
    total = len(data)
    stores: list[tuple[int, int, int]] = []
    for position in _rex_opcode_positions(data, (0x89,)):
        if position + 2 > total:
            continue
        rex = data[position - 1]
        modrm = data[position + 1]
        if modrm >> 6 == 3:
            continue
        operand = _memory_operand(data, position + 1, rex)
        if operand is None:
            continue
        base, displacement, _end = operand
        if base is None or displacement:
            continue
        source = ((modrm >> 3) & 7) | (8 if rex & 4 else 0)
        stores.append((position - 1, base, source))
    return stores


def _pointer_increments(
    code: bytes | memoryview, pointer_bytes: int
) -> list[tuple[int, int]]:
    data = _code_bytes(code)
    total = len(data)
    increments: list[tuple[int, int]] = []
    for position in _rex_opcode_positions(data, (0x83,)):
        if (
            position + 3 > total
            or data[position + 1] >> 6 != 3
            or ((data[position + 1] >> 3) & 7) != 0
            or data[position + 2] != pointer_bytes
        ):
            continue
        rex = data[position - 1]
        register = (data[position + 1] & 7) | (8 if rex & 1 else 0)
        increments.append((position - 1, register))
    return increments


def _bounded_register_increments(
    code: bytes | memoryview,
    *,
    minimum: int = 1,
    maximum: int = 128,
) -> list[tuple[int, int, int]]:
    data = _code_bytes(code)
    total = len(data)
    increments: list[tuple[int, int, int]] = []
    for position in _rex_opcode_positions(data, (0x83,)):
        if (
            position + 3 > total
            or data[position + 1] >> 6 != 3
            or ((data[position + 1] >> 3) & 7) != 0
        ):
            continue
        step = data[position + 2]
        if not minimum <= step <= maximum:
            continue
        rex = data[position - 1]
        register = (data[position + 1] & 7) | (8 if rex & 1 else 0)
        increments.append((position - 1, register, step))
    return increments


def _pointer_scale_shifts(
    code: bytes | memoryview, pointer_bytes: int
) -> list[tuple[int, int]]:
    shift = int(math.log2(pointer_bytes))
    if 1 << shift != pointer_bytes:
        raise AcquisitionError("runtime helper pointer size is not a power of two")
    data = _code_bytes(code)
    total = len(data)
    matches: list[tuple[int, int]] = []
    for position in _rex_opcode_positions(data, (0xC1,)):
        if (
            position + 3 > total
            or data[position + 1] >> 6 != 3
            or ((data[position + 1] >> 3) & 7) != 4
            or data[position + 2] != shift
        ):
            continue
        rex = data[position - 1]
        register = (data[position + 1] & 7) | (8 if rex & 1 else 0)
        matches.append((position - 1, register))
    return matches


def _iterator_sequence_count(
    code: bytes | memoryview, *, pointer_bytes: int
) -> tuple[int, int]:
    iterator_aliases = _argument_aliases(code, 2)
    loads = [event for event in _qword_loads(code) if event[2] in iterator_aliases]
    increments = _pointer_increments(code, pointer_bytes)
    stores = [event for event in _qword_stores(code) if event[1] in iterator_aliases]
    dereferences = _qword_loads(code)
    sequences: set[tuple[int, int, int, int]] = set()
    for load_offset, value_register, _iterator_register in loads:
        for increment_offset, increment_register in increments:
            if increment_offset <= load_offset or increment_register != value_register:
                continue
            for store_offset, _store_base, source_register in stores:
                if store_offset <= increment_offset or source_register != value_register:
                    continue
                if any(
                    dereference_offset > store_offset
                    and destination_register == 0
                    and source_register == value_register
                    for (
                        dereference_offset,
                        destination_register,
                        source_register,
                    ) in dereferences
                ):
                    sequences.add(
                        (load_offset, increment_offset, store_offset, value_register)
                    )
    return len(sequences), len(iterator_aliases)


def _direct_member_iterator_candidate(
    *,
    image: MappedPE,
    function: RuntimeFunction,
    class_header_bytes: int,
    minimum_class_member_byte_offset: int,
    excluded_array_byte_offsets: set[int],
) -> dict[str, Any] | None:
    bounded = image.bounded_code(function.begin_rva, function.end_rva)
    if bounded is None:
        return None
    begin, end = bounded
    code = bytes(image._mapping[begin:end])
    if not 48 <= len(code) <= 512 or not _zero_return_present(code):
        return None
    iterator_aliases = _argument_aliases(code, 2)
    class_aliases = _argument_aliases(code, 1)
    loads = _qword_member_loads(code)
    iterator_loads = [
        event
        for event in loads
        if event[2] in iterator_aliases and event[3] == 0
    ]
    stores = [
        event for event in _qword_stores(code) if event[1] in iterator_aliases
    ]
    increments = _bounded_register_increments(code, minimum=8, maximum=128)
    update_sequences: set[tuple[int, int, int, int, int]] = set()
    for load_offset, value_register, _base, _displacement in iterator_loads:
        for increment_offset, increment_register, step in increments:
            if increment_offset <= load_offset or increment_register != value_register:
                continue
            for store_offset, _store_base, source_register in stores:
                if store_offset > increment_offset and source_register == value_register:
                    update_sequences.add(
                        (
                            load_offset,
                            increment_offset,
                            store_offset,
                            value_register,
                            step,
                        )
                    )
    if not update_sequences:
        return None
    step_values = {sequence[4] for sequence in update_sequences}
    if len(step_values) != 1:
        return None
    record_stride = next(iter(step_values))
    if record_stride % 8:
        return None
    array_fields: dict[int, int] = {}
    for load_offset, destination, base, displacement in loads:
        if (
            base not in class_aliases
            or displacement in excluded_array_byte_offsets
            or displacement < minimum_class_member_byte_offset
            or displacement >= class_header_bytes
            or displacement % 8
        ):
            continue
        if any(
            store_offset > load_offset
            and store_offset - load_offset <= 16
            and store_source == destination
            for store_offset, _store_base, store_source in stores
        ):
            array_fields[displacement] = array_fields.get(displacement, 0) + 1
    if len(array_fields) != 1:
        return None
    array_byte_offset = next(iter(array_fields))
    return {
        "function_rva": function.begin_rva,
        "function_bytes": function.end_rva - function.begin_rva,
        "member_array_byte_offset": array_byte_offset,
        "record_stride": record_stride,
        "iterator_update_sequence_count": len(update_sequences),
        "iterator_argument_alias_count": len(iterator_aliases),
        "class_argument_alias_count": len(class_aliases),
        "initial_array_store_evidence_count": array_fields[array_byte_offset],
        "direct_call_targets": _direct_call_targets(
            code, function_rva=function.begin_rva, image=image
        ),
        "zero_return_present": True,
    }


def _discover_direct_member_iterators(
    *,
    image: MappedPE,
    class_header_bytes: int,
    minimum_class_member_byte_offset: int,
    excluded_array_byte_offsets: set[int],
) -> list[dict[str, Any]]:
    functions: dict[tuple[int, int], RuntimeFunction] = {}
    seed = b"\x48\x8b\x02"
    for section in image.executable_sections:
        cursor = section.raw_offset
        while cursor + len(seed) <= section.raw_end:
            found = image._mapping.find(seed, cursor, section.raw_end)
            if found < 0:
                break
            rva = image.offset_to_rva(section, found)
            function = image.containing_function(rva)
            if (
                function is not None
                and function.end_rva - function.begin_rva <= 512
            ):
                functions[(function.begin_rva, function.end_rva)] = function
            cursor = found + 1
    candidates: list[dict[str, Any]] = []
    for function in functions.values():
        candidate = _direct_member_iterator_candidate(
            image=image,
            function=function,
            class_header_bytes=class_header_bytes,
            minimum_class_member_byte_offset=minimum_class_member_byte_offset,
            excluded_array_byte_offsets=excluded_array_byte_offsets,
        )
        if candidate is not None:
            candidates.append(candidate)
    candidates.sort(key=lambda value: value["function_rva"])
    return candidates


def _select_direct_member_iterators(
    candidates: list[dict[str, Any]], *, minimum_kinds: int = 3
) -> list[dict[str, Any]]:
    layout_pairs = {
        (candidate["member_array_byte_offset"], candidate["record_stride"])
        for candidate in candidates
    }
    if len(candidates) < minimum_kinds or len(layout_pairs) != len(candidates):
        raise AcquisitionError(
            "runtime direct member iterator set is not structurally distinct "
            f"(candidates={len(candidates)}, layouts={len(layout_pairs)})"
        )
    return candidates


def _direct_call_targets(
    code: bytes | memoryview, *, function_rva: int, image: MappedPE
) -> list[int]:


    targets: set[int] = set()
    data = _code_bytes(code)
    limit = len(data) - 4
    if limit <= 0:
        return []
    position = data.find(b"\xe8")
    while 0 <= position < limit:
        displacement = struct.unpack_from("<i", data, position + 1)[0]
        target = function_rva + position + 5 + displacement
        if image.executable_rva(target):
            targets.add(target)
        position = data.find(b"\xe8", position + 1)
    return sorted(targets)


def _zero_return_present(code: bytes | memoryview) -> bool:


    zero_accumulator = any(
        pattern in code
        for pattern in (
            b"\x31\xc0", b"\x33\xc0",
            b"\x29\xc0", b"\x2b\xc0",
            b"\x48\x31\xc0", b"\x48\x33\xc0",
            b"\x48\x29\xc0", b"\x48\x2b\xc0",
            b"\xb8\x00\x00\x00\x00",
        )
    )
    return zero_accumulator and b"\xc3" in code


def _iterator_candidate(
    *,
    image: MappedPE,
    function: RuntimeFunction,
    method_array_byte_offset: int,
    method_count_byte_offset: int,
    pointer_bytes: int,
) -> dict[str, Any] | None:
    bounded = image.bounded_code(function.begin_rva, function.end_rva)
    if bounded is None:
        return None
    begin, end = bounded
    code = bytes(image._mapping[begin:end])
    if not 0 < len(code) <= MAXIMUM_ITERATOR_FUNCTION_BYTES:
        return None
    count_accesses = _member_access_bases(
        code,
        displacement=method_count_byte_offset,
        word_load=True,
    )
    array_accesses = _member_access_bases(
        code,
        displacement=method_array_byte_offset,
        word_load=False,
    )
    shared_bases = sorted(
        {base for _offset, base in count_accesses}
        & {base for _offset, base in array_accesses}
    )
    iterator_sequences, iterator_alias_count = _iterator_sequence_count(
        code, pointer_bytes=pointer_bytes
    )
    scale_shifts = _pointer_scale_shifts(code, pointer_bytes)
    eligible = bool(
        shared_bases
        and iterator_sequences
        and scale_shifts
        and _zero_return_present(code)
    )
    if not eligible:
        return None
    return {
        "function_rva": function.begin_rva,
        "function_bytes": function.end_rva - function.begin_rva,
        "method_count_access_count": len(count_accesses),
        "method_array_access_count": len(array_accesses),
        "shared_class_base_register_count": len(shared_bases),
        "iterator_argument_alias_count": iterator_alias_count,
        "iterator_sequence_count": iterator_sequences,
        "pointer_scale_shift_count": len(scale_shifts),
        "direct_call_targets": _direct_call_targets(
            code, function_rva=function.begin_rva, image=image
        ),
        "zero_return_present": True,
    }


def _select_class_method_iterator(
    candidates: list[dict[str, Any]],
) -> dict[str, Any]:
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime class method iterator is not structurally unique "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def _bound_models(
    *, binary: Path, bootstrap_model: Path, class_model: Path
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    bootstrap = read_json(bootstrap_model)
    classes = read_json(class_model)
    if (
        not isinstance(bootstrap, dict)
        or bootstrap.get("schema") != REFLECTION_BOOTSTRAP_SCHEMA
    ):
        raise AcquisitionError("runtime native helper bootstrap model is invalid")
    if not isinstance(classes, dict) or classes.get("schema") != RUNTIME_CLASS_SCHEMA:
        raise AcquisitionError("runtime native helper class model is invalid")
    binary_identity = file_identity(binary)
    expected_binary = bootstrap.get("binary")
    if (
        not isinstance(expected_binary, dict)
        or binary_identity["sha256"] != expected_binary.get("sha256")
        or binary_identity["bytes"] != expected_binary.get("bytes")
    ):
        raise AcquisitionError("runtime native helper binary binding is stale")
    if classes.get("bootstrap_model_sha256") != file_identity(bootstrap_model)["sha256"]:
        raise AcquisitionError("runtime native helper class/bootstrap binding is stale")
    if classes.get("snapshot", {}).get("image_bytes") != expected_binary.get(
        "size_of_image"
    ):
        raise AcquisitionError("runtime native helper image binding is stale")
    return binary_identity, bootstrap, classes


def discover_runtime_native_helpers(
    *, binary: Path, bootstrap_model: Path, class_model: Path
) -> dict[str, Any]:
    binary_identity, bootstrap, classes = _bound_models(
        binary=binary,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
    )
    layout = classes.get("layout")
    if not isinstance(layout, dict):
        raise AcquisitionError("runtime native helper class layout is unavailable")
    pointer_qword = layout.get("method_array_pointer_qword")
    count_offset = layout.get("method_count_byte_offset")
    parent_qword = layout.get("parent_class_qword")
    parent_byte_offset = layout.get("parent_class_byte_offset")
    parent_encoding = layout.get("parent_class_pointer_encoding")
    if parent_byte_offset is None and isinstance(parent_qword, int):
        parent_byte_offset = parent_qword * 8
    if parent_encoding is None:
        parent_encoding = "native-pointer"
    if (
        not isinstance(pointer_qword, int)
        or pointer_qword < 0
        or not isinstance(count_offset, int)
        or count_offset < 0
        or not isinstance(parent_qword, int)
        or parent_qword < 0
        or not isinstance(parent_byte_offset, int)
        or parent_byte_offset < 0
        or parent_encoding not in {
            "hierarchy-pointer",
            "native-pointer",
            "same-region-low32",
        }
    ):
        raise AcquisitionError("runtime native helper class layout is invalid")
    pointer_bytes = 8
    array_offset = pointer_qword * pointer_bytes
    candidates: dict[tuple[int, int], dict[str, Any]] = {}
    count_hit_count = 0
    with MappedPE(binary) as image:
        if image.size_of_image != bootstrap["binary"]["size_of_image"]:
            raise AcquisitionError("runtime native helper PE image binding is stale")
        for section in image.executable_sections:


            for offset, _base in _member_access_bases_word_load_section(
                image, section, displacement=count_offset
            ):
                count_hit_count += 1
                hit_rva = image.offset_to_rva(
                    section, section.raw_offset + offset
                )
                function = image.containing_function(hit_rva)
                if function is None:
                    continue
                key = (function.begin_rva, function.end_rva)
                if key in candidates:
                    continue
                candidate = _iterator_candidate(
                    image=image,
                    function=function,
                    method_array_byte_offset=array_offset,
                    method_count_byte_offset=count_offset,
                    pointer_bytes=pointer_bytes,
                )
                if candidate is not None:
                    candidates[key] = candidate
        direct_member_candidates = _discover_direct_member_iterators(
            image=image,
            class_header_bytes=layout["vtable_start_qword"] * pointer_bytes,


            minimum_class_member_byte_offset=pointer_bytes,
            excluded_array_byte_offsets={array_offset},
        )
    selected = _select_class_method_iterator(list(candidates.values()))
    selected_direct_members = _select_direct_member_iterators(
        direct_member_candidates
    )
    return {
        "schema": RUNTIME_NATIVE_HELPER_SCHEMA,
        "status": "class-method-iterator-discovered",
        "scope": "bootstrap-owner-native-helper-discovery",
        "all_runtime_helpers_claimed": False,
        "binary": {
            "bytes": binary_identity["bytes"],
            "sha256": binary_identity["sha256"],
            "size_of_image": bootstrap["binary"]["size_of_image"],
        },
        "bootstrap_model_sha256": file_identity(bootstrap_model)["sha256"],
        "class_model_sha256": file_identity(class_model)["sha256"],
        "layout_evidence": {
            "method_array_pointer_qword": pointer_qword,
            "method_count_byte_offset": count_offset,
            "pointer_bytes": pointer_bytes,
        },
        "scan": {
            "method_count_access_hit_count": count_hit_count,
            "class_method_iterator_candidate_count": len(candidates),
            "direct_member_iterator_candidate_count": len(
                direct_member_candidates
            ),
            "candidates": sorted(
                candidates.values(), key=lambda value: value["function_rva"]
            ),
        },
        "helpers": {
            "class_get_methods": selected,
            "direct_member_iterators": selected_direct_members,
        },
        "checks": {
            "target_identity_bound": True,
            "bootstrap_identity_bound": True,
            "class_model_identity_bound": True,
            "class_layout_derived_from_fresh_snapshot": True,
            "class_method_iterator_structurally_unique": True,
            "class_method_iterator_runtime_validated": False,
            "direct_member_iterator_set_structurally_distinct": True,
            "direct_member_iterators_runtime_validated": False,
            "direct_member_iterators_runtime_classified": False,
            "native_metadata_walk_complete": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "fixed_rva_used": False,
            "fixed_version_used": False,
            "saved_reference_values_used": False,
            "external_runtime_component_used": False,
            "acceptance_eligible": False,
        },
    }


def inspect_runtime_native_helpers(
    *, binary: Path, bootstrap_model: Path, class_model: Path, output: Path
) -> dict[str, Any]:
    model = discover_runtime_native_helpers(
        binary=binary,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
    )
    output = output.expanduser().resolve()
    _private_json(output, model)
    return {
        "schema": RUNTIME_NATIVE_HELPER_SCHEMA,
        "status": "discovered",
        "artifact_quality": "provisional",
        "quality_reason": "live iterator behavior and member semantics remain unverified",
        "phase": model["status"],
        "binary": model["binary"],
        "class_method_iterator_candidate_count": model["scan"][
            "class_method_iterator_candidate_count"
        ],
        "direct_member_iterator_candidate_count": model["scan"][
            "direct_member_iterator_candidate_count"
        ],
        "checks": model["checks"],
        "raw_helper_addresses_owner_only": True,
        "output": str(output),
    }


def _c_string_literal(value: str) -> str:
    escaped = (
        value.replace("\\", "\\\\")
        .replace('"', '\\"')
        .replace("\n", "\\n")
        .replace("\r", "\\r")
    )
    return f'"{escaped}"'


def _validation_owner_rows(classes: dict[str, Any]) -> tuple[str, int, int]:
    rows: list[str] = []
    total_methods = 0
    observed: set[tuple[str, str]] = set()
    raw_classes = classes.get("classes")
    if not isinstance(raw_classes, list) or not raw_classes:
        raise AcquisitionError("runtime native helper validation owner set is empty")
    for entry in raw_classes:
        if not isinstance(entry, dict):
            raise AcquisitionError("runtime native helper validation owner is invalid")
        owner = entry.get("runtime_owner")
        method_count = entry.get("method_count")
        if (
            not isinstance(owner, str)
            or "." not in owner
            or not isinstance(method_count, int)
            or not 0 <= method_count <= 65535
        ):
            raise AcquisitionError("runtime native helper validation owner is invalid")
        namespace_name, type_name = owner.rsplit(".", 1)
        pair = (namespace_name, type_name)
        if pair in observed:
            raise AcquisitionError("runtime native helper validation owner is duplicated")
        observed.add(pair)
        total_methods += method_count
        rows.append(
            "    {"
            + _c_string_literal(namespace_name)
            + ", "
            + _c_string_literal(type_name)
            + f", {method_count}u}}"
        )
    if total_methods != len(classes.get("methods", [])):
        raise AcquisitionError(
            "runtime native helper validation method total is inconsistent"
        )
    return ",\n".join(rows), len(rows), total_methods


def _validation_member_candidate_rows(
    helpers: dict[str, Any], *, maximum_candidates: int = 16
) -> tuple[str, int]:
    candidates = helpers.get("helpers", {}).get("direct_member_iterators")
    if (
        not isinstance(candidates, list)
        or not candidates
        or len(candidates) > maximum_candidates
    ):
        raise AcquisitionError(
            "runtime native helper member iterator candidate set is invalid"
        )
    rows: list[str] = []
    layouts: set[tuple[int, int]] = set()
    for candidate in candidates:
        if not isinstance(candidate, dict):
            raise AcquisitionError(
                "runtime native helper member iterator candidate is invalid"
            )
        function_rva = candidate.get("function_rva")
        array_offset = candidate.get("member_array_byte_offset")
        stride = candidate.get("record_stride")
        values = (function_rva, array_offset, stride)
        if any(not isinstance(value, int) or value <= 0 for value in values):
            raise AcquisitionError(
                "runtime native helper member iterator candidate is invalid"
            )
        if array_offset % 8 or stride % 8 or stride > 128:
            raise AcquisitionError(
                "runtime native helper member iterator layout is invalid"
            )
        layout = (array_offset, stride)
        if layout in layouts:
            raise AcquisitionError(
                "runtime native helper member iterator layout is duplicated"
            )
        layouts.add(layout)
        rows.append(
            f"    {{{function_rva}ull, {array_offset}u, {stride}u}}"
        )
    return ",\n".join(rows), len(rows)


def runtime_native_helper_validator_source(
    *,
    expected_executable_sha256: str,
    status_path: Path,
    state_slot_rva: int,
    resolver_helper_rva: int,
    class_get_methods_rva: int,
    method_array_byte_offset: int,
    method_count_byte_offset: int,
    owner_rows: str,
    owner_count: int,
    expected_method_count: int,
    member_candidate_rows: str = "",
    member_candidate_count: int = 0,
) -> str:
    if len(expected_executable_sha256) != 64 or any(
        character not in "0123456789abcdefABCDEF"
        for character in expected_executable_sha256
    ):
        raise AcquisitionError(
            "runtime native helper validation requires an executable SHA-256"
        )
    numeric_values = (
        state_slot_rva,
        resolver_helper_rva,
        class_get_methods_rva,
        method_array_byte_offset,
        method_count_byte_offset,
        owner_count,
        expected_method_count,
        member_candidate_count,
    )
    if any(not isinstance(value, int) or value < 0 for value in numeric_values):
        raise AcquisitionError("runtime native helper validation binding is invalid")
    if not state_slot_rva or not resolver_helper_rva or not class_get_methods_rva:
        raise AcquisitionError("runtime native helper validation helper is unavailable")
    if (
        not owner_rows
        or not owner_count
        or not expected_method_count
        or not member_candidate_rows
        or not member_candidate_count
    ):
        raise AcquisitionError("runtime native helper validation contract is empty")
    status_literal = _wide_literal(_windows_z_path(status_path))
    return rf'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

#define ALPHA_HASH_CHUNK (1024u * 1024u)
#define ALPHA_MEMBER_OBSERVER_REVISION 3u
#define ALPHA_MAX_MEMBER_SLOTS 16u
#define ALPHA_MAX_MEMBER_RECORDS 65535u
static const char expected_executable_sha256[] =
    "{expected_executable_sha256.lower()}";
static const wchar_t status_output[] = {status_literal};
static const uint64_t derived_state_slot_rva = {state_slot_rva}ull;
static const uint64_t derived_resolver_helper_rva = {resolver_helper_rva}ull;
static const uint64_t derived_class_get_methods_rva =
    {class_get_methods_rva}ull;
static const uint32_t derived_method_array_byte_offset =
    {method_array_byte_offset}u;
static const uint32_t derived_method_count_byte_offset =
    {method_count_byte_offset}u;

typedef struct {{
    const char *namespace_name;
    const char *type_name;
    uint32_t expected_method_count;
}} alpha_required_owner;

static const alpha_required_owner required_owners[] = {{
{owner_rows}
}};
static const uint32_t required_owner_count = {owner_count}u;
static const uint32_t required_method_count = {expected_method_count}u;

typedef struct {{
    uint64_t function_rva;
    uint32_t member_array_byte_offset;
    uint32_t record_stride;
}} alpha_member_candidate;

typedef struct {{
    uint32_t owner_count;
    uint32_t record_count;
    uint32_t direct_result_count;
    uint32_t indirect_result_count;
    uint32_t parent_support[ALPHA_MAX_MEMBER_SLOTS];
    uint32_t method_support[ALPHA_MAX_MEMBER_SLOTS];
    int iterator_end_null;
    int layout_complete;
}} alpha_member_result;

static const alpha_member_candidate member_candidates[] = {{
{member_candidate_rows}
}};
static const uint32_t member_candidate_count = {member_candidate_count}u;

typedef uintptr_t (*alpha_type_resolver)(
    uintptr_t state,
    const char *namespace_name,
    const char *type_name
);
typedef uintptr_t (*alpha_class_get_methods)(
    uintptr_t class_object,
    uintptr_t *iterator
);
typedef uintptr_t (*alpha_class_get_member)(
    uintptr_t class_object,
    uintptr_t *iterator
);

static void digest_hex(const unsigned char digest[32], char output[65]) {{
    static const char alphabet[] = "0123456789abcdef";
    for (int index = 0; index < 32; index++) {{
        output[index * 2] = alphabet[digest[index] >> 4];
        output[index * 2 + 1] = alphabet[digest[index] & 15];
    }}
    output[64] = 0;
}}

static int sha256_file(const wchar_t *path, char output[65]) {{
    HANDLE input = CreateFileW(
        path, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (input == INVALID_HANDLE_VALUE) return 0;
    BCRYPT_ALG_HANDLE algorithm = NULL;
    BCRYPT_HASH_HANDLE hash = NULL;
    DWORD object_size = 0, received = 0;
    unsigned char *object = NULL, *buffer = NULL;
    unsigned char digest[32];
    int ok = BCryptOpenAlgorithmProvider(
        &algorithm, BCRYPT_SHA256_ALGORITHM, NULL, 0
    ) >= 0;
    if (ok) ok = BCryptGetProperty(
        algorithm, BCRYPT_OBJECT_LENGTH,
        (PUCHAR)&object_size, sizeof(object_size), &received, 0
    ) >= 0 && object_size;
    if (ok) object = (unsigned char *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, object_size
    );
    if (!object || BCryptCreateHash(
            algorithm, &hash, object, object_size, NULL, 0, 0
        ) < 0) ok = 0;
    if (ok) buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, ALPHA_HASH_CHUNK
    );
    if (!buffer) ok = 0;
    while (ok) {{
        DWORD bytes = 0;
        if (!ReadFile(input, buffer, ALPHA_HASH_CHUNK, &bytes, NULL)) {{
            ok = 0;
            break;
        }}
        if (!bytes) break;
        if (BCryptHashData(hash, buffer, bytes, 0) < 0) ok = 0;
    }}
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) >= 0)
        digest_hex(digest, output);
    else
        ok = 0;
    if (hash) BCryptDestroyHash(hash);
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    if (object) HeapFree(GetProcessHeap(), 0, object);
    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);
    CloseHandle(input);
    return ok;
}}

static int executable_identity(char output[65]) {{
    wchar_t executable[MAX_PATH * 8];
    DWORD length = GetModuleFileNameW(
        NULL, executable,
        (DWORD)(sizeof(executable) / sizeof(executable[0]))
    );
    return length && length < sizeof(executable) / sizeof(executable[0]) &&
        sha256_file(executable, output);
}}

static int main_image(uintptr_t *base, uint64_t *bytes) {{
    HMODULE module = GetModuleHandleW(NULL);
    if (!module) return 0;
    const unsigned char *image = (const unsigned char *)module;
    if (image[0] != 'M' || image[1] != 'Z') return 0;
    uint32_t pe_offset = 0;
    memcpy(&pe_offset, image + 0x3c, sizeof(pe_offset));
    if (pe_offset > 0x100000u || memcmp(image + pe_offset, "PE\0\0", 4))
        return 0;
    const unsigned char *optional = image + pe_offset + 24;
    uint16_t magic = 0;
    uint32_t image_size = 0;
    memcpy(&magic, optional, sizeof(magic));
    memcpy(&image_size, optional + 56, sizeof(image_size));
    if (magic != 0x20bu || !image_size || image_size > 0x80000000u)
        return 0;
    *base = (uintptr_t)module;
    *bytes = image_size;
    return 1;
}}

static int readable_pointer(uintptr_t value, SIZE_T bytes) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !bytes || value + bytes <= value || !VirtualQuery(
            (const void *)value, &region, sizeof(region)
        ) || region.State != MEM_COMMIT || region.Protect & PAGE_GUARD)
        return 0;
    DWORD protect = region.Protect & 0xffu;
    if (protect == PAGE_NOACCESS || !protect) return 0;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    return end > value && bytes <= end - value;
}}

static int executable_pointer(uintptr_t value) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !VirtualQuery(
            (const void *)value, &region, sizeof(region)
        ) || region.State != MEM_COMMIT) return 0;
    DWORD protect = region.Protect & 0xffu;
    return protect == PAGE_EXECUTE || protect == PAGE_EXECUTE_READ ||
        protect == PAGE_EXECUTE_READWRITE ||
        protect == PAGE_EXECUTE_WRITECOPY;
}}

static int class_method_pointer(
    uintptr_t class_object,
    uintptr_t value
) {{
    uint16_t method_count = 0;
    uintptr_t method_array = 0;
    uintptr_t count_address = class_object +
        derived_method_count_byte_offset;
    uintptr_t array_address = class_object +
        derived_method_array_byte_offset;
    if (!value || count_address < class_object || array_address < class_object ||
        !readable_pointer(count_address, sizeof(method_count)) ||
        !readable_pointer(array_address, sizeof(method_array))) return 0;
    memcpy(&method_count, (const void *)count_address, sizeof(method_count));
    memcpy(&method_array, (const void *)array_address, sizeof(method_array));
    if (!method_count || !method_array || !readable_pointer(
            method_array, (SIZE_T)method_count * sizeof(uintptr_t)
        )) return 0;
    for (uint32_t index = 0; index < method_count; index++) {{
        uintptr_t method = 0;
        memcpy(
            &method,
            (const void *)(method_array +
                (uintptr_t)index * sizeof(uintptr_t)),
            sizeof(method)
        );
        if (method == value) return 1;
    }}
    return 0;
}}

static int observe_member_candidate(
    const alpha_member_candidate *candidate,
    uintptr_t image_base,
    uint64_t image_bytes,
    uintptr_t state,
    alpha_type_resolver resolve,
    alpha_member_result *result
) {{
    if (!candidate || !result || !candidate->function_rva ||
        candidate->function_rva >= image_bytes ||
        !candidate->member_array_byte_offset ||
        !candidate->record_stride ||
        candidate->record_stride % sizeof(uintptr_t) ||
        candidate->record_stride / sizeof(uintptr_t) >
            ALPHA_MAX_MEMBER_SLOTS) return 0;
    uintptr_t helper_address = image_base +
        (uintptr_t)candidate->function_rva;
    if (!executable_pointer(helper_address)) return 0;
    alpha_class_get_member get_member =
        (alpha_class_get_member)helper_address;
    memset(result, 0, sizeof(*result));
    result->layout_complete = 1;
    result->iterator_end_null = 1;
    for (uint32_t owner_index = 0;
         owner_index < required_owner_count; owner_index++) {{
        const alpha_required_owner *owner = &required_owners[owner_index];
        uintptr_t class_object = resolve(
            state, owner->namespace_name, owner->type_name
        );
        uintptr_t array_address = class_object +
            candidate->member_array_byte_offset;
        uintptr_t member_array = 0;
        if (!class_object || array_address < class_object ||
            !readable_pointer(array_address, sizeof(member_array))) {{
            result->layout_complete = 0;
            return 0;
        }}
        memcpy(&member_array, (const void *)array_address, sizeof(member_array));
        uintptr_t iterator = 0;
        for (uint32_t record_index = 0;
             record_index < ALPHA_MAX_MEMBER_RECORDS; record_index++) {{
            uintptr_t observed = get_member(class_object, &iterator);
            if (!observed) break;
            if (!member_array) {{
                memcpy(
                    &member_array,
                    (const void *)array_address,
                    sizeof(member_array)
                );
            }}
            if (!member_array || iterator != member_array +
                    (uintptr_t)record_index * candidate->record_stride ||
                !readable_pointer(
                    iterator, candidate->record_stride
                )) {{
                result->layout_complete = 0;
                return 0;
            }}
            if (observed == iterator) result->direct_result_count++;
            uintptr_t indirect = 0;
            memcpy(&indirect, (const void *)iterator, sizeof(indirect));
            if (observed == indirect) result->indirect_result_count++;
            uint32_t slot_count = candidate->record_stride /
                (uint32_t)sizeof(uintptr_t);
            for (uint32_t slot = 0; slot < slot_count; slot++) {{
                uintptr_t value = 0;
                memcpy(
                    &value,
                    (const void *)(iterator +
                        (uintptr_t)slot * sizeof(uintptr_t)),
                    sizeof(value)
                );
                if (value == class_object) result->parent_support[slot]++;
                if (class_method_pointer(class_object, value))
                    result->method_support[slot]++;
            }}
            result->record_count++;
        }}
        if (get_member(class_object, &iterator)) {{
            result->iterator_end_null = 0;
            return 0;
        }}
        result->owner_count++;
    }}
    return result->layout_complete && result->iterator_end_null &&
        result->owner_count == required_owner_count && result->record_count &&
        (result->direct_result_count == result->record_count ||
         result->indirect_result_count == result->record_count);
}}

static void write_status(
    const char *status,
    const char *observed_hash,
    uint32_t owner_count,
    uint32_t direct_method_count,
    uint32_t iterator_method_count,
    int direct_layout_complete,
    int iterator_order_complete,
    int iterator_end_null,
    const alpha_member_result *member_results,
    int member_iterators_complete
) {{
    FILE *output = _wfopen(status_output, L"wb");
    if (!output) return;
    fprintf(
        output,
        "{{\n"
        "  \"schema\": \"{RUNTIME_NATIVE_HELPER_VALIDATION_SCHEMA}\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"executable_hash_matches\": %s,\n"
        "  \"required_owner_count\": %u,\n"
        "  \"required_method_count\": %u,\n"
        "  \"observed_owner_count\": %u,\n"
        "  \"direct_method_count\": %u,\n"
        "  \"iterator_method_count\": %u,\n"
        "  \"direct_layout_complete\": %s,\n"
        "  \"iterator_order_complete\": %s,\n"
        "  \"iterator_end_null\": %s,\n"
        "  \"member_candidate_count\": %u,\n"
        "  \"member_iterators_complete\": %s,\n"
        "  \"member_iterators\": [\n",
        status,
        (unsigned long)GetCurrentProcessId(),
        expected_executable_sha256,
        observed_hash ? observed_hash : "",
        observed_hash && !strcmp(
            observed_hash, expected_executable_sha256
        ) ? "true" : "false",
        required_owner_count,
        required_method_count,
        owner_count,
        direct_method_count,
        iterator_method_count,
        direct_layout_complete ? "true" : "false",
        iterator_order_complete ? "true" : "false",
        iterator_end_null ? "true" : "false",
        member_candidate_count,
        member_iterators_complete ? "true" : "false"
    );
    for (uint32_t candidate_index = 0;
         candidate_index < member_candidate_count; candidate_index++) {{
        const alpha_member_result *result = member_results
            ? &member_results[candidate_index] : NULL;
        fprintf(
            output,
            "    {{\"candidate_index\": %u, \"owner_count\": %u, "
            "\"record_count\": %u, \"direct_result_count\": %u, "
            "\"indirect_result_count\": %u, "
            "\"iterator_end_null\": %s, "
            "\"layout_complete\": %s, \"parent_support\": [",
            candidate_index,
            result ? result->owner_count : 0,
            result ? result->record_count : 0,
            result ? result->direct_result_count : 0,
            result ? result->indirect_result_count : 0,
            result && result->iterator_end_null ? "true" : "false",
            result && result->layout_complete ? "true" : "false"
        );
        for (uint32_t slot = 0; slot < ALPHA_MAX_MEMBER_SLOTS; slot++)
            fprintf(
                output, "%s%u", slot ? ", " : "",
                result ? result->parent_support[slot] : 0
            );
        fprintf(output, "], \"method_support\": [");
        for (uint32_t slot = 0; slot < ALPHA_MAX_MEMBER_SLOTS; slot++)
            fprintf(
                output, "%s%u", slot ? ", " : "",
                result ? result->method_support[slot] : 0
            );
        fprintf(
            output, "]}}%s\n",
            candidate_index + 1u == member_candidate_count ? "" : ","
        );
    }}
    fprintf(
        output,
        "  ],\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"raw_runtime_pointers_exposed\": false,\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_offset_used\": false,\n"
        "  \"network_used\": false,\n"
        "  \"external_runtime_plugin_used\": false\n"
        "}}\n"
    );
    fflush(output);
    fclose(output);
    _wchmod(status_output, 0600);
}}

static DWORD WINAPI worker(void *unused) {{
    (void)unused;
    char observed_hash[65] = {{0}};
    if (!executable_identity(observed_hash) || strcmp(
            observed_hash, expected_executable_sha256
        )) {{
        write_status("executable-identity-mismatch", observed_hash,
            0, 0, 0, 0, 0, 0, NULL, 0);
        return 1;
    }}
    uintptr_t image_base = 0;
    uint64_t image_bytes = 0;
    if (!main_image(&image_base, &image_bytes) ||
        derived_state_slot_rva + sizeof(uintptr_t) > image_bytes ||
        derived_resolver_helper_rva >= image_bytes ||
        derived_class_get_methods_rva >= image_bytes) {{
        write_status("image-binding-invalid", observed_hash,
            0, 0, 0, 0, 0, 0, NULL, 0);
        return 2;
    }}
    uintptr_t state_slot = image_base + (uintptr_t)derived_state_slot_rva;
    uintptr_t resolver_address = image_base +
        (uintptr_t)derived_resolver_helper_rva;
    uintptr_t iterator_address = image_base +
        (uintptr_t)derived_class_get_methods_rva;
    uintptr_t state = 0;
    if (!readable_pointer(state_slot, sizeof(state)) ||
        !executable_pointer(resolver_address) ||
        !executable_pointer(iterator_address)) {{
        write_status("helper-binding-invalid", observed_hash,
            0, 0, 0, 0, 0, 0, NULL, 0);
        return 3;
    }}
    memcpy(&state, (const void *)state_slot, sizeof(state));
    if (!state) {{
        write_status("resolver-state-unavailable", observed_hash,
            0, 0, 0, 0, 0, 0, NULL, 0);
        return 4;
    }}
    alpha_type_resolver resolve = (alpha_type_resolver)resolver_address;
    alpha_class_get_methods get_methods =
        (alpha_class_get_methods)iterator_address;
    uint32_t owners = 0, direct_methods = 0, iterator_methods = 0;
    int direct_complete = 1, order_complete = 1, end_null = 1;
    for (uint32_t owner_index = 0;
         owner_index < required_owner_count; owner_index++) {{
        const alpha_required_owner *owner = &required_owners[owner_index];
        uintptr_t class_object = resolve(
            state, owner->namespace_name, owner->type_name
        );
        uintptr_t count_address = class_object +
            derived_method_count_byte_offset;
        uintptr_t array_address = class_object +
            derived_method_array_byte_offset;
        uint16_t direct_count = 0;
        uintptr_t direct_array = 0;
        if (!class_object || count_address < class_object ||
            array_address < class_object ||
            !readable_pointer(count_address, sizeof(direct_count)) ||
            !readable_pointer(array_address, sizeof(direct_array))) {{
            direct_complete = 0;
            break;
        }}
        memcpy(&direct_count, (const void *)count_address, sizeof(direct_count));
        memcpy(&direct_array, (const void *)array_address, sizeof(direct_array));
        if (direct_count != owner->expected_method_count ||
            (direct_count && (!direct_array || !readable_pointer(
                direct_array, (SIZE_T)direct_count * sizeof(uintptr_t)
            )))) {{
            direct_complete = 0;
            break;
        }}
        uintptr_t iterator = 0;
        for (uint32_t method_index = 0;
             method_index < direct_count; method_index++) {{
            uintptr_t expected_method = 0;
            memcpy(
                &expected_method,
                (const void *)(direct_array +
                    (uintptr_t)method_index * sizeof(uintptr_t)),
                sizeof(expected_method)
            );
            uintptr_t observed_method = get_methods(class_object, &iterator);
            if (!expected_method || observed_method != expected_method) {{
                order_complete = 0;
                break;
            }}
            iterator_methods++;
        }}
        if (!order_complete) break;
        if (get_methods(class_object, &iterator)) {{
            end_null = 0;
            break;
        }}
        direct_methods += direct_count;
        owners++;
    }}
    int method_complete = direct_complete && order_complete && end_null &&
        owners == required_owner_count &&
        direct_methods == required_method_count &&
        iterator_methods == required_method_count;
    alpha_member_result member_results[16];
    memset(member_results, 0, sizeof(member_results));
    int member_complete = method_complete && member_candidate_count <= 16u;
    for (uint32_t candidate_index = 0;
         candidate_index < member_candidate_count;
         candidate_index++) {{
        int candidate_complete = method_complete && observe_member_candidate(
            &member_candidates[candidate_index],
            image_base, image_bytes, state, resolve,
            &member_results[candidate_index]
        );
        if (!candidate_complete) member_complete = 0;
    }}
    int complete = method_complete && member_complete;
    write_status(
        complete ? "complete" : "validation-mismatch",
        observed_hash, owners, direct_methods, iterator_methods,
        direct_complete, order_complete, end_null,
        member_results, member_complete
    );
    return complete ? 0 : 5;
}}

BOOL WINAPI DllMain(HINSTANCE instance, DWORD reason, LPVOID reserved) {{
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {{
        DisableThreadLibraryCalls(instance);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }}
    return TRUE;
}}
'''


def _load_native_helper_model(
    *,
    binary: Path,
    bootstrap_model: Path,
    class_model: Path,
    native_helper_model: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    binary_identity, bootstrap, classes = _bound_models(
        binary=binary,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
    )
    helpers = read_json(native_helper_model)
    if (
        not isinstance(helpers, dict)
        or helpers.get("schema") != RUNTIME_NATIVE_HELPER_SCHEMA
        or helpers.get("binary", {}).get("sha256") != binary_identity["sha256"]
        or helpers.get("binary", {}).get("bytes") != binary_identity["bytes"]
        or helpers.get("bootstrap_model_sha256")
        != file_identity(bootstrap_model)["sha256"]
        or helpers.get("class_model_sha256")
        != file_identity(class_model)["sha256"]
        or helpers.get("scan", {}).get(
            "class_method_iterator_candidate_count"
        )
        != 1
        or helpers.get("checks", {}).get(
            "class_method_iterator_structurally_unique"
        )
        is not True
    ):
        raise AcquisitionError("runtime native helper model binding is stale")
    return binary_identity, bootstrap, classes, helpers


def prepare_runtime_native_helper_validation(
    *,
    binary: Path,
    bootstrap_model: Path,
    class_model: Path,
    native_helper_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    output_dir = _owner_directory(output_dir)
    binary_identity, bootstrap, classes, helpers = _load_native_helper_model(
        binary=binary,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
        native_helper_model=native_helper_model,
    )
    owner_rows, owner_count, method_count = _validation_owner_rows(classes)
    member_candidate_rows, member_candidate_count = (
        _validation_member_candidate_rows(helpers)
    )
    layout = helpers["layout_evidence"]
    helper = helpers["helpers"]["class_get_methods"]
    status_path = output_dir / "native-helper-status.private.json"
    validated_model_path = output_dir / "runtime-native-helpers.validated.private.json"
    build_dir = _owner_directory(output_dir / "build-native-helper")
    source_path = build_dir / "runtime-native-helper-validator.c"
    injector_source_path = build_dir / "runtime-native-helper-injector.c"
    injector_path = build_dir / "alpha-runtime-native-helper-injector.exe"
    for stale in (status_path, validated_model_path):
        stale.unlink(missing_ok=True)
    _private_text(
        source_path,
        runtime_native_helper_validator_source(
            expected_executable_sha256=binary_identity["sha256"],
            status_path=status_path,
            state_slot_rva=bootstrap["state_slot_rva"],
            resolver_helper_rva=bootstrap["type_resolver_helper_rva"],
            class_get_methods_rva=helper["function_rva"],
            method_array_byte_offset=(
                layout["method_array_pointer_qword"] * layout["pointer_bytes"]
            ),
            method_count_byte_offset=layout["method_count_byte_offset"],
            owner_rows=owner_rows,
            owner_count=owner_count,
            expected_method_count=method_count,
            member_candidate_rows=member_candidate_rows,
            member_candidate_count=member_candidate_count,
        ),
    )
    validator_path = build_dir / (
        "alpha-runtime-native-helper-"
        + file_identity(source_path)["sha256"][:12]
        + ".dll"
    )
    _private_text(injector_source_path, runtime_injector_source())
    selected_compiler = _compiler(compiler)
    cached_windows_build(
        [
            str(selected_compiler),
            "-O2",
            "-s",
            "-shared",
            "-Wall",
            "-Wextra",
            "-Wformat=2",
            "-Werror=format",
            str(source_path),
            "-o",
            str(validator_path),
            "-lbcrypt",
        ],
        label="runtime native helper validator",
        source_path=source_path,
        output_path=validator_path,
    )
    cached_windows_build(
        [
            str(selected_compiler),
            "-O2",
            "-s",
            "-municode",
            "-Wall",
            "-Wextra",
            "-Wformat=2",
            "-Werror=format",
            str(injector_source_path),
            "-o",
            str(injector_path),
        ],
        label="runtime native helper injector",
        source_path=injector_source_path,
        output_path=injector_path,
    )
    for artifact in (validator_path, injector_path):
        if not artifact.is_file() or not artifact.stat().st_size:
            raise AcquisitionError(
                f"runtime native helper build did not produce {artifact.name}"
            )
        artifact.chmod(0o600)
    plan = {
        "schema": RUNTIME_NATIVE_HELPER_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_path": str(binary),
            "executable_sha256": binary_identity["sha256"],
            "executable_bytes": binary_identity["bytes"],
            "process_name": binary.name,
        },
        "inputs": {
            "bootstrap_model_sha256": file_identity(bootstrap_model)["sha256"],
            "class_model_sha256": file_identity(class_model)["sha256"],
            "native_helper_model_sha256": file_identity(native_helper_model)[
                "sha256"
            ],
        },
        "validator": file_identity(validator_path),
        "injector": file_identity(injector_path),
        "outputs": {
            "status": str(status_path),
            "validated_model": str(validated_model_path),
        },
        "contract": {
            "owner_count": owner_count,
            "method_count": method_count,
            "member_candidate_count": member_candidate_count,
        },
        "policy": {
            "current_executable_sha256_embedded": True,
            "fresh_runtime_observation_required": True,
            "direct_layout_cross_check_required": True,
            "iterator_order_cross_check_required": True,
            "iterator_end_null_required": True,
            "raw_runtime_pointers_owner_only": True,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "fixed_rva_used": False,
            "fixed_version_used": False,
            "external_runtime_component_used": False,
        },
    }
    _private_json(output_dir / "native-helper-plan.private.json", plan)
    return {
        "schema": RUNTIME_NATIVE_HELPER_PLAN_SCHEMA,
        "status": "prepared",
        "target": {
            "executable_sha256": binary_identity["sha256"],
            "executable_bytes": binary_identity["bytes"],
        },
        "contract": plan["contract"],
        "policy": plan["policy"],
    }


def _member_iterator_validation_checks(
    status: dict[str, Any], plan: dict[str, Any]
) -> dict[str, bool]:
    candidate_count = plan.get("contract", {}).get("member_candidate_count")
    owner_count = plan.get("contract", {}).get("owner_count")
    observations = status.get("member_iterators")
    shape_valid = (
        isinstance(candidate_count, int)
        and candidate_count > 0
        and status.get("member_candidate_count") == candidate_count
        and isinstance(observations, list)
        and len(observations) == candidate_count
    )
    indices_exact = bool(
        shape_valid
        and all(isinstance(entry, dict) for entry in observations)
        and [entry.get("candidate_index") for entry in observations]
        == list(range(candidate_count))
    )
    owner_coverage = bool(
        indices_exact
        and isinstance(owner_count, int)
        and all(entry.get("owner_count") == owner_count for entry in observations)
    )
    record_coverage = bool(
        indices_exact
        and all(
            isinstance(entry.get("record_count"), int)
            and entry["record_count"] > 0
            for entry in observations
        )
    )
    modes_unique = bool(
        record_coverage
        and all(
            (
                entry.get("direct_result_count") == entry["record_count"]
                and entry.get("indirect_result_count") == 0
            )
            or (
                entry.get("indirect_result_count") == entry["record_count"]
                and entry.get("direct_result_count") == 0
            )
            for entry in observations
        )
    )
    support_vectors_valid = bool(
        record_coverage
        and all(
            isinstance(entry.get(key), list)
            and len(entry[key]) == 16
            and all(
                isinstance(value, int)
                and 0 <= value <= entry["record_count"]
                for value in entry[key]
            )
            for entry in observations
            for key in ("parent_support", "method_support")
        )
    )
    return {
        "member_candidate_count_matches": shape_valid,
        "member_candidate_indices_exact": indices_exact,
        "member_owner_coverage_complete": owner_coverage,
        "member_record_coverage_nonzero": record_coverage,
        "member_iterator_modes_unique": modes_unique,
        "member_support_vectors_valid": support_vectors_valid,
        "member_layouts_complete": bool(
            indices_exact
            and status.get("member_iterators_complete") is True
            and all(
                entry.get("layout_complete") is True
                and entry.get("iterator_end_null") is True
                for entry in observations
            )
        ),
    }


def _classify_runtime_member_iterators(
    helper_model: dict[str, Any], status: dict[str, Any]
) -> dict[str, Any]:
    candidates = helper_model.get("helpers", {}).get("direct_member_iterators")
    observations = status.get("member_iterators")
    if (
        not isinstance(candidates, list)
        or not isinstance(observations, list)
        or len(candidates) != len(observations)
    ):
        raise AcquisitionError(
            "runtime member iterator classification evidence is incomplete"
        )
    paired: list[tuple[dict[str, Any], dict[str, Any]]] = []
    for index, (candidate, observation) in enumerate(
        zip(candidates, observations, strict=True)
    ):
        if (
            not isinstance(candidate, dict)
            or not isinstance(observation, dict)
            or observation.get("candidate_index") != index
            or not isinstance(observation.get("record_count"), int)
            or observation["record_count"] <= 0
        ):
            raise AcquisitionError(
                "runtime member iterator classification binding is stale"
            )
        paired.append((candidate, observation))
    direct = [
        pair
        for pair in paired
        if pair[1].get("direct_result_count") == pair[1]["record_count"]
        and pair[1].get("indirect_result_count") == 0
    ]
    indirect = [
        pair
        for pair in paired
        if pair[1].get("indirect_result_count") == pair[1]["record_count"]
        and pair[1].get("direct_result_count") == 0
    ]
    if len(direct) != 3 or len(indirect) != 1:
        raise AcquisitionError(
            "runtime member iterator topology is not uniquely classifiable "
            f"(direct={len(direct)}, indirect={len(indirect)})"
        )
    direct.sort(key=lambda pair: pair[0]["record_stride"])
    strides = [pair[0]["record_stride"] for pair in direct]
    if len(set(strides)) != len(strides) or strides != sorted(strides):
        raise AcquisitionError("runtime member iterator stride topology is ambiguous")

    def classified(
        semantic_kind: str,
        pair: tuple[dict[str, Any], dict[str, Any]],
        topology_rank: int | None,
    ) -> dict[str, Any]:
        candidate, observation = pair
        return {
            **candidate,
            "semantic_kind": semantic_kind,
            "runtime_record_count": observation["record_count"],
            "runtime_owner_count": observation["owner_count"],
            "iterator_mode": (
                "direct-record" if topology_rank is not None else "pointer-array"
            ),
            "record_topology_rank": topology_rank,
            "semantic_label_from_saved_stride": False,
            "runtime_validated": True,
        }

    return {
        "class_get_fields": classified("field", direct[0], 0),
        "class_get_properties": classified("property", direct[1], 1),
        "class_get_events": classified("event", direct[2], 2),
        "class_get_indirect_members_unclassified": classified(
            "unclassified", indirect[0], None
        ),
        "checks": {
            "three_direct_record_topologies_present": True,
            "one_pointer_array_topology_present": True,
            "direct_record_strides_fresh_and_distinct": True,
            "field_property_event_topology_rank_unique": True,
            "saved_stride_values_used": False,
            "member_semantics_independently_proven": False,
        },
        "unclassified_helper_count": len(indirect),
        "semantic_evidence": "record-stride-topology-rank-only",
    }


def capture_runtime_native_helper_validation(
    *,
    binary: Path,
    bootstrap_model: Path,
    class_model: Path,
    native_helper_model: Path,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 120.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    prepare_runtime_native_helper_validation(
        binary=binary,
        bootstrap_model=bootstrap_model,
        class_model=class_model,
        native_helper_model=native_helper_model,
        output_dir=output_dir,
        compiler=compiler,
    )
    plan = read_json(output_dir / "native-helper-plan.private.json")
    binary = binary.expanduser().resolve()
    if file_identity(binary)["sha256"] != plan["target"]["executable_sha256"]:
        raise AcquisitionError(
            "target executable changed after native helper preparation"
        )
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError("selected Wine binary or prefix is unavailable")
    build_dir = output_dir / "build-native-helper"
    validator = Path(plan["validator"]["path"])
    injector = Path(plan["injector"]["path"])
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine), injector, validator, binary.name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "ALPHA v2 runtime native helper injector could not run"
        ) from error
    _private_text(
        output_dir / "native-helper-injector.private.log",
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
        raise AcquisitionError(
            f"ALPHA v2 runtime native helper injection failed ({injected.returncode})"
        )
    status_path = Path(plan["outputs"]["status"])
    deadline = time.monotonic() + max(1.0, timeout)
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        if status_path.is_file():
            try:
                value = json.loads(status_path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                value = None
            if isinstance(value, dict):
                status = value
                break
        time.sleep(0.25)
    if status is None:
        raise AcquisitionError("ALPHA v2 runtime native helper validation timed out")
    _seal_runtime_output(status_path)
    checks = {
        "schema": status.get("schema")
        == RUNTIME_NATIVE_HELPER_VALIDATION_SCHEMA,
        "complete": status.get("status") == "complete",
        "executable_hash_matches": status.get("executable_hash_matches") is True,
        "expected_hash_matches_plan": status.get("expected_executable_sha256")
        == plan["target"]["executable_sha256"],
        "observed_hash_matches_plan": status.get("observed_executable_sha256")
        == plan["target"]["executable_sha256"],
        "owner_count_matches": status.get("required_owner_count")
        == plan["contract"]["owner_count"]
        and status.get("observed_owner_count")
        == plan["contract"]["owner_count"],
        "direct_method_count_matches": status.get("required_method_count")
        == plan["contract"]["method_count"]
        and status.get("direct_method_count")
        == plan["contract"]["method_count"],
        "iterator_method_count_matches": status.get("iterator_method_count")
        == plan["contract"]["method_count"],
        "direct_layout_complete": status.get("direct_layout_complete") is True,
        "iterator_order_complete": status.get("iterator_order_complete") is True,
        "iterator_end_null": status.get("iterator_end_null") is True,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "raw_runtime_pointers_absent": status.get("raw_runtime_pointers_exposed")
        is False,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_offset_absent": status.get("fixed_offset_used") is False,
        "network_absent": status.get("network_used") is False,
        "external_runtime_component_absent": status.get(
            "external_runtime_plugin_used"
        )
        is False,
    }
    checks.update(_member_iterator_validation_checks(status, plan))
    validated = all(checks.values())
    if validated:
        helper_model = copy.deepcopy(read_json(native_helper_model))
        classification = _classify_runtime_member_iterators(helper_model, status)
        helper_model["status"] = "native-member-iterators-runtime-classified"
        helper_model["artifact_quality"] = "provisional"
        helper_model["quality_reason"] = (
            "member identity uses record stride rank and one helper is unclassified"
        )
        helper_model["checks"]["class_method_iterator_runtime_validated"] = True
        helper_model["checks"]["direct_member_iterators_runtime_validated"] = True
        helper_model["checks"]["direct_member_iterators_runtime_classified"] = False
        helper_model["checks"]["direct_member_iterators_topology_classified"] = True
        helper_model["checks"]["member_semantics_independently_proven"] = False
        for key in (
            "class_get_fields",
            "class_get_properties",
            "class_get_events",
            "class_get_indirect_members_unclassified",
        ):
            helper_model["helpers"][key] = classification[key]
        helper_model["member_classification_checks"] = classification["checks"]
        helper_model["unclassified_helper_count"] = classification[
            "unclassified_helper_count"
        ]
        helper_model["semantic_evidence"] = classification["semantic_evidence"]
        helper_model["runtime_validation"] = {
            "status_sha256": file_identity(status_path)["sha256"],
            "process_id": status["process_id"],
            "owner_count": status["observed_owner_count"],
            "method_count": status["iterator_method_count"],
            "member_iterators": status["member_iterators"],
            "checks": checks,
        }
        _private_json(Path(plan["outputs"]["validated_model"]), helper_model)
    return {
        "schema": RUNTIME_NATIVE_HELPER_VALIDATION_SCHEMA,
        "status": "validated" if validated else "rejected",
        "artifact_quality": "provisional" if validated else "rejected",
        "quality_reason": (
            "member identity uses record stride rank and one helper is unclassified"
            if validated else "runtime iterator validation failed"
        ),
        "owner_count": status.get("observed_owner_count", 0),
        "method_count": status.get("iterator_method_count", 0),
        "classified_member_helper_count": 3 if validated else 0,
        "unclassified_member_helper_count": 1 if validated else 0,
        "checks": checks,
        "raw_helper_addresses_and_runtime_pointers_owner_only": True,
        "validated_model": plan["outputs"]["validated_model"]
        if validated
        else None,
    }


import hashlib
import re

from alpha.h01 import AcquisitionError
from alpha.p15 import merged_ranges
from alpha.p14 import RuntimeRangeView
from alpha.c03 import verify_small_copy, copy_boundary_cases
from alpha.c01 import decode_x64


def _pieces(model):
    if model.get("schema") != "alpha.root-extent-candidates/v1" or not model.get("resolved"):
        raise AcquisitionError("root extent observation has no derived operations")
    for root in model["resolved"]:
        helpers = root.get("helpers", [])
        for operation in [root] + helpers + [tail for helper in helpers for tail in helper.get("external_tail_bodies", [])]:
            try:
                pointer, code = operation["body_pointer"], bytes.fromhex(operation["body_code_hex"])
                if type(pointer) is not int or pointer <= 0 or not code or hashlib.sha256(code).hexdigest() != operation["body_code_sha256"]:
                    raise AcquisitionError("root extent operation code identity differs")
                yield pointer, code
                for thunk in operation["thunks"]:
                    raw = bytes.fromhex(thunk["code_hex"])
                    width = 5 if raw[:1] == b"\xe9" else 2 if raw[:1] == b"\xeb" else 0
                    if not width or len(raw) != width or thunk["pointer"] + width + int.from_bytes(raw[1:], "little", signed=True) != thunk["target_pointer"]:
                        raise AcquisitionError("root extent thunk target differs")
                    yield thunk["pointer"], raw
                for word in operation.get("small_copy_replay", {}).get("dispatch_words", []):
                    raw = bytes.fromhex(word["code_hex"])
                    if len(raw) != 4:
                        raise AcquisitionError("root extent dispatch word width differs")
                    yield word["pointer"], raw
            except (KeyError, ValueError, TypeError) as error:
                raise AcquisitionError("root extent operation evidence is malformed") from error


def root_extent_memory_requests(model):
    return merged_ranges([(pointer, len(code)) for pointer, code in _pieces(model)])


def copy_runtime_input_requests(model):

    requests = root_extent_memory_requests(model)
    widths = {"BYTE": 1, "WORD": 2, "DWORD": 4, "QWORD": 8}
    for root in model["resolved"]:
        for helper in root.get("helpers", []):
            if "copy_boundary_case_domain" not in helper:
                continue
            for body in [helper] + helper.get("external_tail_bodies", []):
                code = bytes.fromhex(body["body_code_hex"])
                instructions = decode_x64(code)
                for i, (offset, text) in enumerate(instructions):
                    if text.split(None, 1)[0] == "lea":
                        continue
                    match = re.search(r"(BYTE|WORD|DWORD|QWORD) PTR \[rip([+-])(0x[0-9a-f]+)\]", text)
                    if match:
                        delta = int(match[3], 0) * (-1 if match[2] == "-" else 1)
                        end = instructions[i + 1][0] if i + 1 < len(instructions) else len(code)
                        address = (body["body_pointer"] + end + delta) & ((1 << 64) - 1)
                        requests.append((address, widths[match[1]]))
    return merged_ranges(requests)


def replay_boundary_copy_observation(model, observation, *, fallback=None):

    view = RuntimeRangeView(observation)
    for pointer, raw in _pieces(model):
        if view.read(pointer, len(raw)) != raw:
            raise AcquisitionError("copy boundary live code or known table word changed")
    missing, reports = {}, []
    def read(address, width):
        value = view.read(address, width)
        if value is not None:
            return value


        if width != 4 or fallback is None:
            raise AcquisitionError("copy boundary runtime input is missing")
        raw = fallback(address, width)
        if not isinstance(raw, bytes) or len(raw) != width:
            raise AcquisitionError("copy boundary provisional dispatch word is absent")
        missing[address] = raw
        return raw
    for address, width in copy_runtime_input_requests(model):
        if view.read(address, width) is None:
            raise AcquisitionError("copy boundary initial runtime inputs are incomplete")
    for root in model["resolved"]:
        for helper in root.get("helpers", []):
            domain = helper.get("copy_boundary_case_domain")
            if domain is None:
                continue
            code = bytes.fromhex(helper["body_code_hex"])
            limits = sorted({(1 << (item["class_extent_width"] * 8)) - 1 - item["payload_offset"]
                for item in root["extent_copy_candidates"] if item["copy_callee_pointer"] == helper["entry_pointer"]})
            cases = sorted({case for limit in limits for case in copy_boundary_cases(code, limit)})
            if domain != {"payload_limits_from_candidate_widths": limits, "cases": [list(case) for case in cases]}:
                raise AcquisitionError("copy boundary case domain differs from current extent candidates")
            bodies = {tail["body_pointer"]: bytes.fromhex(tail["body_code_hex"]) for tail in helper.get("external_tail_bodies", [])}
            bodies.update({thunk["pointer"]: bytes.fromhex(thunk["code_hex"])
                for tail in helper.get("external_tail_bodies", []) for thunk in tail["thunks"]})
            replay = verify_small_copy(code, helper["body_pointer"], read, cases=cases, external_bodies=bodies)
            replay["live_code_and_data_verified"] = not missing
            reports.append({"body_pointer": helper["body_pointer"], "replay": replay})
    if not reports:
        raise AcquisitionError("copy boundary replay has no current candidate domains")
    return {"boundary_copy_replays": reports, "provisional_dispatch_words": [
        {"pointer": pointer, "code_hex": raw.hex()} for pointer, raw in sorted(missing.items())],
        "all_runtime_inputs_observed": not missing, "copy_role_proven": False, "metadata_complete": False}


def replay_root_extent_observation(model, observation):
    requests = root_extent_memory_requests(model)
    view = RuntimeRangeView(observation)
    for pointer, code in _pieces(model):
        if view.read(pointer, len(code)) != code:
            raise AcquisitionError("root extent live code or dispatch data differs from current executable")
    replays = []
    for root in model["resolved"]:
        for helper in root.get("helpers", []):
            if "small_copy_replay" not in helper:
                continue
            result = verify_small_copy(bytes.fromhex(helper["body_code_hex"]), helper["body_pointer"], view.read)
            if result != helper["small_copy_replay"]:
                raise AcquisitionError("root extent live symbolic replay differs from current derivation")
            result["live_code_and_data_verified"] = True
            replays.append({"body_pointer": helper["body_pointer"], "replay": result})
    if not replays:
        raise AcquisitionError("root extent observation has no verified small-copy domain")
    return {"range_count": len(requests), "byte_count": sum(size for _, size in requests),
        "small_copy_replays": replays, "current_code_and_dispatch_bytes_equal": True,
        "copy_role_proven": False, "allocator_role_proven": False,
        "object_payload_origin_proven": False, "metadata_complete": False}
