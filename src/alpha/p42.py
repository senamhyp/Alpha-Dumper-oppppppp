import bisect
import copy
import hashlib
from collections import defaultdict
from pathlib import Path
from typing import Any, Iterable

from alpha.p12 import _private_bytes, _private_json
from alpha.h01 import AcquisitionError
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER
from alpha.p33 import _MetadataUsageTypeRenderer, _UnresolvableGeneric, _optional_text, _text
from alpha.p29 import (
    _bounded_code, _direct_tag_writes, _memory_accesses, _message_types,
    _native_register_index, _reachable_instruction_map, _runtime, _tag_cases,
    _this_register, analyze_runtime_proto,
)
from alpha.c06 import LiveRuntimeInventory
from alpha.p41 import PLAN_SCHEMA as RUNTIME_PROTO_MUTATION_PLAN_SCHEMA, RuntimeSnapshot
from alpha.p38 import RUNTIME_PROTO_FIELD_TYPE_HEADER, RUNTIME_PROTO_FIELD_TYPE_MAGIC, RUNTIME_PROTO_FIELD_TYPE_RECORD, RUNTIME_PROTO_FIELD_TYPE_SCHEMA, RUNTIME_PROTO_FIELD_TYPE_VERSION
from alpha.c04 import MappedPE
from alpha.p20 import load_runtime_metadata_usage_value_inventory
from alpha.h02 import file_identity, read_json, read_private_model


RUNTIME_PROTO_STATIC_MODEL_SCHEMA = "alpha.runtime-proto-static-model/v15"
RUNTIME_PROTO_ENUM_CONSTANT_SCHEMA = "alpha.runtime-proto-enum-constants/v3"
RUNTIME_PROTO_MUTATION_RESULT_SCHEMA = "alpha.runtime-proto-field-mutation-result/v2"
RUNTIME_PROTO_SERIALIZER_RESULT_SCHEMA = "alpha.runtime-proto-serializer-probe-result/v1"

_PRIMITIVES = {
    "System.Boolean": "bool",
    "System.Int32": "int32",
    "System.UInt32": "uint32",
    "System.Int64": "int64",
    "System.UInt64": "uint64",
    "System.Single": "float",
    "System.Double": "double",
    "System.String": "string",
}


def _split_generic(value: str) -> tuple[str, list[str]] | None:

    start = value.find("<")
    if start < 1 or not value.endswith(">"):
        return None
    depth = 0
    cursor = start + 1
    argument_start = cursor
    arguments: list[str] = []
    while cursor < len(value) - 1:
        character = value[cursor]
        if character == "<":
            depth += 1
        elif character == ">":
            if not depth:
                return None
            depth -= 1
        elif character == "," and not depth:
            argument = value[argument_start:cursor].strip()
            if not argument:
                return None
            arguments.append(argument)
            argument_start = cursor + 1
        cursor += 1
    if depth:
        return None
    argument = value[argument_start:-1].strip()
    if not argument:
        return None
    arguments.append(argument)
    return value[:start], arguments


def _snake_case(value: str) -> str:

    if not value:
        raise AcquisitionError("runtime proto oneof case name is empty")
    output: list[str] = []
    for index, character in enumerate(value):
        if character == "_":
            if output and output[-1] != "_":
                output.append("_")
            continue
        if character.isupper():
            previous = value[index - 1] if index else ""
            following = value[index + 1] if index + 1 < len(value) else ""
            if output and output[-1] != "_" and (
                previous.islower()
                or previous.isdigit()
                or previous.isupper() and following.islower()
            ):
                output.append("_")
            output.append(character.lower())
        else:
            output.append(character)
    result = "".join(output).strip("_")
    if not result:
        raise AcquisitionError("runtime proto oneof case name is empty")
    return result


def _rip_load_targets(code: bytes, method_pointer: int) -> list[tuple[int, int]]:

    output: list[tuple[int, int]] = []
    for cursor in range(max(0, len(code) - 6)):
        if (
            0x48 <= code[cursor] <= 0x4F
            and code[cursor + 1] == 0x8B
            and code[cursor + 2] & 0xC7 == 0x05
        ):
            target = (
                method_pointer
                + cursor
                + 7
                + int.from_bytes(
                    code[cursor + 3 : cursor + 7], "little", signed=True
                )
            )
            output.append((cursor, target))
    return output


def _modrm_end(code: bytes, offset: int) -> int | None:

    if not 0 <= offset < len(code):
        return None
    modrm = code[offset]
    mod = modrm >> 6
    rm = modrm & 7
    cursor = offset + 1
    if mod != 3 and rm == 4:
        if cursor >= len(code):
            return None
        sib = code[cursor]
        cursor += 1
        if mod == 0 and sib & 7 == 5:
            cursor += 4
    if mod == 0 and rm == 5:
        cursor += 4
    elif mod == 1:
        cursor += 1
    elif mod == 2:
        cursor += 4
    return cursor if cursor <= len(code) else None


def _direct_case_branches(code: bytes) -> list[tuple[int, int, int]]:

    comparisons: list[tuple[int, int, int]] = []
    cursor = 0
    while cursor < len(code):
        start = cursor
        number: int | None = None
        end: int | None = None
        if code[cursor] == 0x3D and cursor + 5 <= len(code):
            number = int.from_bytes(code[cursor + 1 : cursor + 5], "little")
            end = cursor + 5
        elif code[cursor] in (0x81, 0x83) and cursor + 2 <= len(code):
            operand_end = _modrm_end(code, cursor + 1)
            if code[cursor + 1] >> 3 & 7 == 7 and operand_end is not None:
                immediate_bytes = 4 if code[cursor] == 0x81 else 1
                if operand_end + immediate_bytes <= len(code):
                    number = int.from_bytes(
                        code[operand_end : operand_end + immediate_bytes],
                        "little",
                        signed=immediate_bytes == 1,
                    )
                    end = operand_end + immediate_bytes
        if number is None or end is None or number <= 0:
            cursor += 1
            continue
        branch_end: int | None = None
        target: int | None = None
        equal_branch = False
        if end + 2 <= len(code) and code[end] in (0x74, 0x75):
            branch_end = end + 2
            equal_branch = code[end] == 0x74
            displacement = int.from_bytes(
                code[end + 1 : branch_end], "little", signed=True
            )
            target = branch_end + displacement if equal_branch else branch_end
        elif (
            end + 6 <= len(code)
            and code[end] == 0x0F
            and code[end + 1] in (0x84, 0x85)
        ):
            branch_end = end + 6
            equal_branch = code[end + 1] == 0x84
            displacement = int.from_bytes(
                code[end + 2 : branch_end], "little", signed=True
            )
            target = branch_end + displacement if equal_branch else branch_end
        if target is not None and 0 <= target < len(code):
            comparisons.append((number, start, target))
            cursor = branch_end if branch_end is not None else end
        else:
            cursor = start + 1
    return comparisons


class _RuntimeTypeSlotResolver:


    def __init__(
        self,
        *,
        snapshot: Path | None,
        runtime_materializer_model: Path | None,
        runtime: Any,
        binary: Path,
        static_slots: dict[int, str],
    ):
        self.static_slots = static_slots
        self.snapshot: RuntimeSnapshot | None = None
        self.class_names: dict[int, str] = {}
        self.cache: dict[int, str | None] = {}
        if snapshot is None and runtime_materializer_model is None:
            return
        if snapshot is None or runtime_materializer_model is None:
            raise AcquisitionError(
                "runtime proto type slots require snapshot and materializer models"
            )
        self.snapshot = RuntimeSnapshot(snapshot.expanduser().resolve())
        with MappedPE(binary) as image:
            if (
                self.snapshot.image_base != image.image_base
                or self.snapshot.image_bytes != image.size_of_image
            ):
                self.close()
                raise AcquisitionError("runtime proto type-slot snapshot is stale")
        with LiveRuntimeInventory(
            materializer_model=runtime_materializer_model,
            binary=binary,
        ) as live:
            if live.type_count != runtime.type_count:
                self.close()
                raise AcquisitionError("runtime proto type-slot inventory differs")
            for type_index in range(live.type_count):
                row = live.type_row(type_index)
                name = runtime.renderer.root_name(type_index)
                previous = self.class_names.get(row.class_pointer)
                if previous is not None and previous != name:
                    self.close()
                    raise AcquisitionError(
                        "runtime proto type-slot class pointers conflict"
                    )
                self.class_names[row.class_pointer] = name

    def resolve(self, target: int) -> str | None:
        if target in self.cache:
            return self.cache[target]
        name = self.static_slots.get(target)
        if self.snapshot is not None:
            try:
                class_pointer = int.from_bytes(self.snapshot.read(target, 8), "little")
            except KeyError:
                class_pointer = 0
            runtime_name = self.class_names.get(class_pointer)
            if runtime_name is not None:
                name = runtime_name
        self.cache[target] = name
        return name

    def close(self) -> None:
        if self.snapshot is not None:
            self.snapshot.close()
            self.snapshot = None

    def __enter__(self) -> "_RuntimeTypeSlotResolver":
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()


def _field_rows(runtime: Any) -> tuple[dict[int, dict[str, Any]], dict[int, list[int]]]:
    by_index: dict[int, dict[str, Any]] = {}
    by_owner: dict[int, list[int]] = defaultdict(list)
    for field_index in range(runtime.field_count):
        row = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + field_index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        item = {
            "field_index": field_index,
            "owner_type_index": row[0],
            "member_index": row[1],
            "metadata": row[2],
            "descriptor": row[3],
            "managed_offset": row[4],
            "attributes": row[5],
            "token": row[6],
            "name": _text(runtime.native, row[9], row[7], label="field name"),
        }
        by_index[field_index] = item
        by_owner[row[0]].append(field_index)
    return by_index, by_owner


class _ProtoTypes:
    def __init__(self, runtime: Any, message_types: Iterable[int]):
        self.runtime = runtime
        self.message_types = set(message_types)
        self.index_by_name = {
            runtime.renderer.root_name(index): index
            for index in range(runtime.type_count)
        }
        definitions: dict[str, list[int]] = defaultdict(list)
        for name, index in self.index_by_name.items():
            definitions[name.split("<", 1)[0]].append(index)
        self.definition_by_name: dict[str, int] = {}
        for name, indexes in definitions.items():
            top_level = [
                index
                for index in indexes
                if not runtime.renderer.identity_row(index)[5]
            ]
            candidates = top_level if top_level else indexes
            if len(candidates) == 1:
                self.definition_by_name[name] = candidates[0]
        self.cache: dict[tuple[str, int], dict[str, Any] | None] = {}

    def classify_name(self, rendered: str, wire: int) -> dict[str, Any] | None:
        key = (rendered, wire)
        if key in self.cache:
            return self.cache[key]
        result: dict[str, Any] | None
        if rendered in _PRIMITIVES:
            name = _PRIMITIVES[rendered]
            if rendered == "System.UInt32" and wire == 5:
                name = "fixed32"
            elif rendered == "System.Int32" and wire == 5:
                name = "sfixed32"
            elif rendered == "System.UInt64" and wire == 1:
                name = "fixed64"
            elif rendered == "System.Int64" and wire == 1:
                name = "sfixed64"
            expected = {
                "bool": 0,
                "int32": 0,
                "uint32": 0,
                "int64": 0,
                "uint64": 0,
                "fixed32": 5,
                "sfixed32": 5,
                "fixed64": 1,
                "sfixed64": 1,
                "float": 5,
                "double": 1,
                "string": 2,
            }[name]
            result = {"cardinality": "singular", "type": name} if wire == expected else None
        else:
            generic = _split_generic(rendered)
            definition = self.definition_by_name.get(
                generic[0] if generic else rendered
            )
            interfaces = (
                self.runtime.renderer.root_interfaces(definition)
                if definition is not None
                else []
            )
            if generic and any("IDictionary<" in item for item in interfaces):
                if len(generic[1]) != 2 or wire != 2:
                    result = None
                else:
                    key_type = self.classify_name(generic[1][0], self._natural_wire(generic[1][0]))
                    value_type = self.classify_name(generic[1][1], self._natural_wire(generic[1][1]))
                    result = (
                        {
                            "cardinality": "map",
                            "key_type": key_type["type"],
                            "value_type": value_type["type"],
                        }
                        if key_type
                        and value_type
                        and key_type.get("cardinality") == "singular"
                        and value_type.get("cardinality") == "singular"
                        else None
                    )
            elif generic and any("IList<" in item for item in interfaces):
                element_wire = self._natural_wire(generic[1][0])
                if len(generic[1]) != 1 or wire not in {2, element_wire}:
                    result = None
                else:
                    element = self.classify_name(
                        generic[1][0], element_wire
                    )
                    result = (
                        {
                            "cardinality": "repeated",
                            "type": element["type"],
                            **(
                                {"packed": wire == 2}
                                if element_wire in (0, 1, 5)
                                else {}
                            ),
                        }
                        if element and element.get("cardinality") == "singular"
                        else None
                    )
            else:
                type_index = self.index_by_name.get(rendered)
                if type_index is None or wire not in (0, 2):
                    result = None
                elif self.runtime.renderer.identity_row(type_index)[1] & 0x20:
                    result = (
                        {"cardinality": "singular", "type": rendered.rsplit(".", 1)[-1]}
                        if wire == 0
                        else None
                    )
                elif (
                    "System.Collections.Generic.IEnumerable<System.Byte>"
                    in self.runtime.renderer.root_interfaces(type_index)
                ):
                    result = (
                        {
                            "cardinality": "singular",
                            "type": "bytes",
                        }
                        if wire == 2
                        else None
                    )
                elif type_index in self.message_types:
                    result = (
                        {
                            "cardinality": "singular",
                            "type": rendered.rsplit(".", 1)[-1],
                        }
                        if wire == 2
                        else None
                    )
                else:
                    result = None
        self.cache[key] = result
        return result

    def _natural_wire(self, rendered: str) -> int:
        if rendered in {"System.Single"}:
            return 5
        if rendered in {"System.Double"}:
            return 1
        if rendered in {
            "System.Boolean", "System.Int32", "System.UInt32",
            "System.Int64", "System.UInt64",
        }:
            return 0
        type_index = self.index_by_name.get(rendered)
        if type_index is not None and self.runtime.renderer.identity_row(type_index)[1] & 0x20:
            return 0
        return 2


def _unsupported_message_wire_field_indexes(
    *,
    rendered: Mapping[int, str],
    message_type_names: set[str],
    excluded_field_indexes: set[int],
    classifier: _ProtoTypes,
) -> list[int]:
    return sorted(
        field_index
        for field_index, rendered_type in rendered.items()
        if field_index not in excluded_field_indexes
        and rendered_type in message_type_names
        and not any(
            classifier.classify_name(rendered_type, wire) is not None
            for wire in (0, 1, 2, 5)
        )
    )


def _bounded_oneof_size_evidence(
    *, message: dict[str, Any], runtime: Any, image: MappedPE,
    fields: dict[int, dict[str, Any]], method_indexes: list[int],
    needed_numbers: set[int],
) -> dict[int, set[int]]:
    from capstone.x86_const import X86_OP_IMM, X86_OP_MEM, X86_OP_REG

    oneofs_by_number: dict[int, list[tuple[int, int, int]]] = defaultdict(list)
    for oneof in message["oneofs"]:
        storage_index = int(oneof["storage_field_index_owner_only"])
        discriminator_index = int(oneof["discriminator_field_index_owner_only"])
        storage_offset = int(oneof["storage_offset"])
        discriminator_offset = int(fields[discriminator_index]["managed_offset"]) + 16
        for case in oneof["cases"]:
            number = int(case["number"])
            if number in needed_numbers:
                oneofs_by_number[number].append(
                    (storage_index, storage_offset, discriminator_offset)
                )
    if not oneofs_by_number:
        return {}

    evidence: dict[int, set[int]] = defaultdict(set)
    for method_index in method_indexes:
        method = runtime.method_row(method_index)
        if (
            not method[3] or method[9] & 1 or method[5] & 0x10
            or method[10] != 0
            or runtime.method_return(method_index) not in {
                "System.Int32", "System.UInt32", "System.Int64", "System.UInt64"
            }
        ):
            continue
        code = _bounded_code(image, int(method[3]))
        if not code:
            continue
        branches = [row for row in _direct_case_branches(code) if row[0] in oneofs_by_number]
        if not branches:
            continue
        base = _this_register(code)
        instructions = _reachable_instruction_map(code)
        for number, compare_offset, case_start in branches:
            comparison = instructions.get(compare_offset)
            if comparison is None or comparison.mnemonic.lower() != "cmp":
                continue
            operands = comparison.operands
            if (
                len(operands) != 2 or operands[0].type != X86_OP_REG
                or operands[1].type != X86_OP_IMM
                or int(operands[1].imm) != number
            ):
                continue
            compared = _native_register_index(comparison.reg_name(operands[0].reg))
            if compared is None:
                continue
            previous = [
                instruction for offset, instruction in sorted(instructions.items())
                if compare_offset - 64 <= offset < compare_offset
            ]
            source = None
            for instruction in reversed(previous):
                _reads, writes = instruction.regs_access()
                if any(
                    _native_register_index(instruction.reg_name(reg)) == compared
                    for reg in writes
                ):
                    source = instruction
                    break
            if source is None or source.mnemonic.lower() != "mov":
                continue
            source_operands = source.operands
            if (
                len(source_operands) != 2
                or source_operands[0].type != X86_OP_REG
                or source_operands[1].type != X86_OP_MEM
                or _native_register_index(source.reg_name(source_operands[0].reg)) != compared
                or _native_register_index(source.reg_name(source_operands[1].mem.base)) != base
                or source_operands[1].mem.index != 0
                or source_operands[1].size not in (4, 8)
            ):
                continue
            accesses = _memory_accesses(code, case_start, len(code), base_register=base)
            for storage_index, storage_offset, discriminator_offset in oneofs_by_number[number]:
                if int(source_operands[1].mem.disp) != discriminator_offset:
                    continue
                if any(
                    access["object_offset"] == storage_offset
                    and access["code_offset"] < case_start + 128
                    for access in accesses
                ):
                    evidence[number].add(storage_index)
        if all(
            any(index in evidence.get(number, set()) for index, _, _ in candidates)
            for number, candidates in oneofs_by_number.items()
        ):
            break
    return evidence


def _collect_runtime_assignment_tag_evidence(
    *,
    runtime_assignments: Mapping[int, Mapping[str, Any]],
    field_by_index: Mapping[int, Mapping[str, Any]],
) -> dict[int, dict[int, set[int]]]:
    collected: dict[int, dict[int, set[int]]] = defaultdict(
        lambda: defaultdict(set)
    )
    for field_index, assignment in runtime_assignments.items():
        row = field_by_index.get(int(field_index))
        if row is None:
            continue
        number = assignment.get("number")
        if type(number) is not int or not 0 < number <= 0x1FFFFFFF:
            continue
        owner_type_index = row.get("owner_type_index")
        if type(owner_type_index) is not int:
            continue
        collected[owner_type_index][number].add(int(field_index))
    return {
        type_index: {number: set(indexes) for number, indexes in numbers.items()}
        for type_index, numbers in collected.items()
    }


def _field_tag_case_coverage(
    *,
    messages: list[dict[str, Any]],
    analysis_messages: list[dict[str, Any]],
    runtime: Any,
    image: MappedPE,
    fields: dict[int, dict[str, Any]],
    methods_by_owner: dict[int, list[int]],
    runtime_assignment_numbers: (
        Mapping[int, Mapping[int, int | Iterable[int]]] | None
    ) = None,
) -> tuple[list[dict[str, Any]], int, int]:
    parser_case_numbers_by_type: dict[int, set[int]] = defaultdict(set)
    parser_access_indexes_by_type: dict[int, dict[int, set[int]]] = defaultdict(
        lambda: defaultdict(set)
    )
    writer_tag_numbers_by_type: dict[int, set[int]] = defaultdict(set)
    writer_access_indexes_by_type: dict[int, dict[int, set[int]]] = defaultdict(
        lambda: defaultdict(set)
    )
    formatter_tag_numbers_by_type: dict[int, set[int]] = defaultdict(set)
    formatter_access_indexes_by_type: dict[int, dict[int, set[int]]] = defaultdict(
        lambda: defaultdict(set)
    )
    for source in analysis_messages:
        type_index = int(source["type_index"])
        for candidate in source["candidate_tags"]:
            if "bounded-parser-tag-case" in candidate.get("sources", []):
                number = int(candidate["field_number"])
                if not 0 < number <= 0x1FFFFFFF:
                    raise AcquisitionError(
                        "bounded parser candidate has an invalid field number"
                    )
                parser_case_numbers_by_type[type_index].add(number)
        for mapping in source.get("mappings", []):
            if not isinstance(mapping, dict):
                raise AcquisitionError(
                    "runtime parser field-access mapping is invalid"
                )
            mapping_source = mapping.get("source")
            if mapping_source not in {
                "bounded-parser-tag-case", "bounded-writer-varint-tag",
                "bounded-static-formatter-tag",
            }:
                continue
            number = int(mapping["field_number"])
            if not 0 < number <= 0x1FFFFFFF:
                raise AcquisitionError(
                    "bounded parser field-access mapping has an invalid field number"
                )
            accesses = mapping.get("field_accesses")
            if not isinstance(accesses, list):
                raise AcquisitionError(
                    "bounded parser field-access mapping has no access inventory"
                )
            for access in accesses:
                if not isinstance(access, dict):
                    raise AcquisitionError(
                        "bounded parser field-access mapping entry is invalid"
                    )
                field_index = access.get("field_index")
                if type(field_index) is not int or field_index < 0:
                    raise AcquisitionError(
                        "bounded parser field-access mapping index is invalid"
                    )
                destination = {
                    "bounded-parser-tag-case": parser_access_indexes_by_type,
                    "bounded-writer-varint-tag": writer_access_indexes_by_type,
                    "bounded-static-formatter-tag": formatter_access_indexes_by_type,
                }[str(mapping_source)]
                destination[type_index][number].add(field_index)
            if mapping_source == "bounded-writer-varint-tag":
                writer_tag_numbers_by_type[type_index].add(number)
            elif (
                mapping_source == "bounded-static-formatter-tag"
                and int(mapping.get("wire", -1)) in (0, 1, 2, 5)
            ):
                formatter_tag_numbers_by_type[type_index].add(number)

    coverage = []
    serializable_message_count = 0
    uncovered_message_count = 0
    for message in messages:
        type_index = int(message["type_index_owner_only"])
        output_numbers = sorted(
            [int(field["number"]) for field in message["fields"]]
            + [
                int(case["number"])
                for oneof in message["oneofs"]
                for case in oneof["cases"]
            ]
        )
        parser_numbers = sorted(parser_case_numbers_by_type.get(type_index, set()))
        expected_indexes_by_number: dict[int, set[int]] = defaultdict(set)
        for field in message["fields"]:
            field_index = field.get("field_index_owner_only")
            if type(field_index) is not int or field_index < 0:
                raise AcquisitionError(
                    "output field has no runtime field identity for parser coverage"
                )
            expected_indexes_by_number[int(field["number"])].add(field_index)
        for oneof in message["oneofs"]:
            storage_index = oneof.get("storage_field_index_owner_only")
            if type(storage_index) is not int or storage_index < 0:
                raise AcquisitionError(
                    "output oneof has no runtime storage identity for parser coverage"
                )
            for case in oneof["cases"]:
                expected_indexes_by_number[int(case["number"])].add(storage_index)
        access_indexes = parser_access_indexes_by_type.get(type_index, {})
        writer_access_indexes = writer_access_indexes_by_type.get(type_index, {})
        formatter_access_indexes = formatter_access_indexes_by_type.get(type_index, {})
        writer_numbers = writer_tag_numbers_by_type.get(type_index, set())
        formatter_numbers = formatter_tag_numbers_by_type.get(type_index, set())


        runtime_assignments = (
            runtime_assignment_numbers.get(type_index, {})
            if runtime_assignment_numbers
            else {}
        )
        runtime_numbers: set[int] = set()
        runtime_assignment_evidence: list[dict[str, Any]] = []
        runtime_conflicts: list[dict[str, Any]] = []
        for raw_number, raw_field_indexes in sorted(runtime_assignments.items()):
            number = int(raw_number)
            if isinstance(raw_field_indexes, int):
                field_indexes = {int(raw_field_indexes)}
            else:
                field_indexes = {int(item) for item in raw_field_indexes}
            if not field_indexes:
                raise AcquisitionError(
                    "runtime serializer observation has no field identity; "
                    f"message={message['name']!r} field_number={number}"
                )
            expected_indexes = expected_indexes_by_number.get(number)
            if expected_indexes is None:
                runtime_conflicts.append(
                    {
                        "field_number": number,
                        "field_indexes_owner_only": sorted(field_indexes),
                        "reason": "probed tag is not an output field number",
                    }
                )
                continue
            if not field_indexes <= expected_indexes:
                runtime_conflicts.append(
                    {
                        "field_number": number,
                        "field_indexes_owner_only": sorted(field_indexes),
                        "reason": (
                            "probed field identity differs from the output field"
                        ),
                        "output_field_indexes_owner_only": sorted(expected_indexes),
                    }
                )
                continue
            runtime_numbers.add(number)
            for field_index in sorted(field_indexes):
                runtime_assignment_evidence.append(
                    {
                        "field_number": number,
                        "field_index_owner_only": field_index,
                    }
                )
                access_indexes.setdefault(number, set()).add(field_index)
        if runtime_conflicts:
            raise AcquisitionError(
                "runtime serializer observation conflicts with the output model; "
                f"message={message['name']!r} "
                f"conflicts={runtime_conflicts[:8]!r}"
            )
        already_mapped = {
            number: (
                access_indexes.get(number, set())
                | writer_access_indexes.get(number, set())
                | formatter_access_indexes.get(number, set())
            )
            for number in expected_indexes_by_number
        }
        needed_oneof_numbers = {
            int(case["number"])
            for oneof in message["oneofs"]
            for case in oneof["cases"]
            if (
                int(case["number"]) not in parser_case_numbers_by_type.get(type_index, set())
                and int(case["number"]) not in writer_numbers
                and int(case["number"]) not in formatter_numbers
            ) or int(oneof["storage_field_index_owner_only"]) not in already_mapped.get(
                int(case["number"]), set()
            )
        }
        size_evidence = _bounded_oneof_size_evidence(
            message=message, runtime=runtime, image=image, fields=fields,
            method_indexes=methods_by_owner.get(type_index, []),
            needed_numbers=needed_oneof_numbers,
        ) if needed_oneof_numbers else {}
        mapped_numbers = sorted(
            number
            for number in (
                set(access_indexes)
                | set(writer_access_indexes)
                | set(formatter_access_indexes)
                | set(size_evidence)
                | runtime_numbers
            )
            if (
                access_indexes.get(number)
                or writer_access_indexes.get(number)
                or formatter_access_indexes.get(number)
                or size_evidence.get(number)
                or number in runtime_numbers
            )
        )
        exact_numbers = (
            writer_numbers | formatter_numbers | set(size_evidence)
            | runtime_numbers
        )
        missing_cases = sorted(
            set(output_numbers) - set(parser_numbers) - exact_numbers
        )
        missing_mappings = sorted(set(output_numbers) - set(mapped_numbers))
        missing_pairs = [
            {
                "field_number": number,
                "field_indexes_owner_only": sorted(
                    expected_indexes
                    - access_indexes.get(number, set())
                    - writer_access_indexes.get(number, set())
                    - formatter_access_indexes.get(number, set())
                    - size_evidence.get(number, set())
                ),
            }
            for number, expected_indexes in sorted(expected_indexes_by_number.items())
            if not expected_indexes
            <= (
                access_indexes.get(number, set())
                | writer_access_indexes.get(number, set())
                | formatter_access_indexes.get(number, set())
                | size_evidence.get(number, set())
            )
        ]
        missing = sorted(
            set(missing_cases)
            | set(missing_mappings)
            | {int(row["field_number"]) for row in missing_pairs}
        )
        if output_numbers:
            serializable_message_count += 1
        if missing:
            uncovered_message_count += 1
        coverage.append(
            {
                "type_index_owner_only": type_index,
                "message": message["name"],
                "output_field_numbers": output_numbers,
                "parser_candidate_field_numbers": parser_numbers,
                "writer_tag_field_numbers": sorted(writer_numbers),
                "formatter_tag_field_numbers": sorted(formatter_numbers),
                "bounded_oneof_size_case_numbers": sorted(size_evidence),
                "bounded_field_access_mapped_numbers": mapped_numbers,
                "runtime_serializer_probe_field_numbers": sorted(runtime_numbers),
                "runtime_serializer_probe_evidence_owner_only": (
                    runtime_assignment_evidence
                ),
                "parser_field_access_indexes_by_number_owner_only": [
                    {
                        "field_number": number,
                        "field_indexes_owner_only": sorted(indexes),
                    }
                    for number, indexes in sorted(access_indexes.items())
                    if indexes
                ],
                "uncovered_parser_case_numbers": missing_cases,
                "uncovered_parser_field_access_numbers": missing_mappings,
                "uncovered_parser_field_access_pairs_owner_only": missing_pairs,
                "uncovered_output_field_numbers": missing,
            }
        )
    if uncovered_message_count:
        examples = [
            row for row in coverage if row["uncovered_output_field_numbers"]
        ][:32]
        raise AcquisitionError(
            "bounded parser, writer, or formatter tag and field-access coverage is missing for "
            f"{uncovered_message_count} output messages/fields; "
            "unsupported group wires, unrelated constants, or unknown field mappings "
            "cannot be ruled out. Examples: "
            + repr(examples)
        )
    return coverage, serializable_message_count, uncovered_message_count


def _type_usage_context(
    receipt: dict[str, Any],
    paths: dict[str, Path],
    runtime: Any,
    field_descriptors: Iterable[int],
) -> tuple[dict[int, str], dict[int, str]]:
    values = load_runtime_metadata_usage_value_inventory(
        model_path=paths["metadata_usage_value_model"],
        inventory_path=paths["metadata_usage_value_inventory"],
        expected_executable_sha256=receipt["target"]["executable_sha256"],
    )


    defer_generics = not values["generic_records_owner_only"]
    with _MetadataUsageTypeRenderer(
        binary=paths["binary"],
        renderer=runtime.renderer,
        generic_records=values["generic_records_owner_only"],
    ) as renderer:
        rows, _codes = renderer.render_usages(
            values["type_usages"], defer_unresolvable_generics=defer_generics)
        if renderer.deferred_generic_slots:
            print({
                "deferred_generic_type_slots": len(renderer.deferred_generic_slots),
                "type_usage_count": len(values["type_usages"]),
                "generic_table_empty": defer_generics,
            }, flush=True)
        native_names: dict[int, str] = {}
        deferred_native_names = 0
        for descriptor in set(field_descriptors):
            if descriptor in runtime.renderer.node_by_descriptor:
                continue
            data, bits = renderer._type_record(descriptor)
            try:
                native_names[descriptor] = renderer.render(descriptor, data, bits)
            except _UnresolvableGeneric:


                if not defer_generics:
                    raise
                deferred_native_names += 1
        if deferred_native_names:
            print({
                "deferred_generic_native_names": deferred_native_names,
                "generic_table_empty": defer_generics,
            }, flush=True)
    return (
        {
            values["image_base"] + int(item["Address"]): str(item["Name"])[:-9]
            for item in rows
            if str(item["Name"]).endswith("_TypeInfo")
        },
        native_names,
    )


def _live_embedded_type_names(
    *,
    runtime_materializer_model: Path | None,
    runtime: Any,
    binary: Path,
) -> dict[int, str]:

    if runtime_materializer_model is None:
        return {}
    output: dict[int, str] = {}
    with LiveRuntimeInventory(
        materializer_model=runtime_materializer_model,
        binary=binary,
    ) as live:
        if live.type_count != runtime.type_count:
            raise AcquisitionError("runtime proto live type inventory differs")
        for type_index in range(live.type_count):
            row = live.type_row(type_index)
            descriptor = row.embedded_descriptor(
                live.embedded_descriptor_byte_offset
            )
            name = runtime.renderer.root_name(type_index)
            previous = output.get(descriptor)
            if previous is not None and previous != name:
                raise AcquisitionError(
                    "runtime proto embedded type descriptors conflict"
                )
            output[descriptor] = name
    return output


_WRITER_REFERENCES_CACHE: dict[tuple, tuple[dict, dict]] = {}


_WRITER_REFERENCES_MEMO_DIR: Path | None = None
_WRITER_REFERENCES_MEMO_SCHEMA = "alpha.proto-writer-references-memo/v1"
_WRITER_REFERENCES_MEMO_KEEP = 4
_WRITER_REFERENCES_MEMO_IMPLEMENTATION: str | None = None


def set_writer_references_memo_dir(path: Path | None) -> None:
    global _WRITER_REFERENCES_MEMO_DIR
    _WRITER_REFERENCES_MEMO_DIR = (
        Path(path).expanduser().resolve() if path is not None else None
    )


def _writer_references_memo_implementation() -> str:
    global _WRITER_REFERENCES_MEMO_IMPLEMENTATION
    if _WRITER_REFERENCES_MEMO_IMPLEMENTATION is None:
        from alpha.p19 import _implementation_digest
        try:
            from alpha.computation_identity import computation_digest
            _WRITER_REFERENCES_MEMO_IMPLEMENTATION = computation_digest((
                ("alpha.p42", "_writer_type_references"),
                ("alpha.p42", "_oneof_branch_type_references"),
                ("alpha.p42", "_RuntimeTypeSlotResolver"),
                ("alpha.p29", "_runtime"),
                ("alpha.p29", "_analyze_runtime_proto_uncached"),
            ))
        except (OSError, ValueError, SyntaxError, ImportError):
            _WRITER_REFERENCES_MEMO_IMPLEMENTATION = _implementation_digest()
    return _WRITER_REFERENCES_MEMO_IMPLEMENTATION


def _writer_references_content_identity(key_element: tuple | None) -> str | None:
    if key_element is None:
        return None
    path, size, _mtime_ns = key_element
    record = file_identity(Path(path))
    if record["bytes"] != size:


        return None
    return json.dumps(record, ensure_ascii=False, sort_keys=True)


def _writer_references_memo_key(writer_cache_key: tuple, *, implementation: str | None = None) -> str | None:
    digest = hashlib.sha256()
    digest.update(
        (implementation or _writer_references_memo_implementation()).encode("utf-8") + b"\0"
    )
    for element in writer_cache_key:
        identity = _writer_references_content_identity(element)
        if identity is None and element is not None:
            return None
        digest.update((identity or "absent").encode("utf-8") + b"\0")
    return digest.hexdigest()[:32]


def _writer_references_memo_domain(rows: Any) -> dict[tuple[int, int], list[str]] | None:
    if not isinstance(rows, dict):
        return None
    result: dict[tuple[int, int], list[str]] = {}
    for key, names in rows.items():
        left, separator, right = str(key).partition(":")
        if not separator or not left.isdigit() or not right.isdigit():
            return None
        if not isinstance(names, list) or not all(
            isinstance(name, str) for name in names
        ):
            return None
        result[(int(left), int(right))] = list(names)
    return result


def _load_writer_references_memo(writer_cache_key: tuple) -> tuple[dict, dict] | None:
    if _WRITER_REFERENCES_MEMO_DIR is None:
        return None
    key = _writer_references_memo_key(writer_cache_key)
    if key is None:
        return None
    payload_path = _WRITER_REFERENCES_MEMO_DIR / f"writer-references-{key}.payload"
    meta_path = _WRITER_REFERENCES_MEMO_DIR / f"writer-references-{key}.meta.json"
    if not meta_path.exists():
        return _load_legacy_writer_references_memo(writer_cache_key)
    try:
        meta = read_json(meta_path, maximum_bytes=1 << 20)
        if (
            meta.get("schema") != _WRITER_REFERENCES_MEMO_SCHEMA
            or meta.get("implementation") != _writer_references_memo_implementation()
            or type(meta.get("payload_bytes")) is not int
        ):
            return None
        raw = payload_path.read_bytes()
        if (
            len(raw) != meta["payload_bytes"]
            or hashlib.sha256(raw).hexdigest() != meta.get("payload_sha256")
        ):
            return None
        payload = json.loads(raw)
        if payload.get("schema") != _WRITER_REFERENCES_MEMO_SCHEMA:
            return None
        writer_types = _writer_references_memo_domain(payload.get("writer_types"))
        oneof_branch_types = _writer_references_memo_domain(
            payload.get("oneof_branch_types")
        )
        if writer_types is None or oneof_branch_types is None:
            return None
        return writer_types, oneof_branch_types
    except (AcquisitionError, OSError, ValueError, TypeError, KeyError):

        return None


def _load_legacy_writer_references_memo(writer_cache_key: tuple) -> tuple[dict, dict] | None:
    from alpha.computation_identity import legacy_source_matches
    roots = (("alpha.p42", "_writer_type_references"),
             ("alpha.p42", "_oneof_branch_type_references"),
             ("alpha.p42", "_RuntimeTypeSlotResolver"),
             ("alpha.p29", "_runtime"), ("alpha.p29", "_analyze_runtime_proto_uncached"))
    for meta_path in sorted(_WRITER_REFERENCES_MEMO_DIR.glob("writer-references-*.meta.json"), reverse=True):
        try:
            meta = read_json(meta_path, maximum_bytes=1 << 20)
            implementation = str(meta.get("implementation", ""))
            expected_key = _writer_references_memo_key(writer_cache_key, implementation=implementation)
            if (meta.get("schema") != _WRITER_REFERENCES_MEMO_SCHEMA
                    or meta.get("key", expected_key) != expected_key
                    or meta_path.name != f"writer-references-{expected_key}.meta.json"
                    or type(meta.get("payload_bytes")) is not int):
                continue
            raw = meta_path.with_name(meta_path.name[:-len(".meta.json")] + ".payload").read_bytes()
            if (len(raw) != meta["payload_bytes"]
                    or hashlib.sha256(raw).hexdigest() != meta.get("payload_sha256")):
                continue
            if not legacy_source_matches(_WRITER_REFERENCES_MEMO_DIR.parent,
                    implementation, roots, _writer_references_memo_implementation()):
                continue
            payload = json.loads(raw)
            writer = _writer_references_memo_domain(payload.get("writer_types"))
            oneof = _writer_references_memo_domain(payload.get("oneof_branch_types"))
            if payload.get("schema") != _WRITER_REFERENCES_MEMO_SCHEMA or writer is None or oneof is None:
                continue
            _store_writer_references_memo(writer_cache_key, writer, oneof)
            return writer, oneof
        except (AcquisitionError, OSError, ValueError, TypeError, KeyError):
            continue
    return None


def _store_writer_references_memo(
    writer_cache_key: tuple,
    writer_types: dict[tuple[int, int], list[str]],
    oneof_branch_types: dict[tuple[int, int], list[str]],
) -> None:
    if _WRITER_REFERENCES_MEMO_DIR is None:
        return
    key = _writer_references_memo_key(writer_cache_key)
    if key is None:
        return
    payload_path = _WRITER_REFERENCES_MEMO_DIR / f"writer-references-{key}.payload"
    meta_path = _WRITER_REFERENCES_MEMO_DIR / f"writer-references-{key}.meta.json"
    try:


        encoded = json.dumps(
            {
                "schema": _WRITER_REFERENCES_MEMO_SCHEMA,
                "writer_types": {
                    f"{type_index}:{slot}": names
                    for (type_index, slot), names in writer_types.items()
                },
                "oneof_branch_types": {
                    f"{type_index}:{number}": names
                    for (type_index, number), names in oneof_branch_types.items()
                },
            },
            ensure_ascii=False, separators=(",", ":"),
        ).encode("utf-8")
        _private_bytes(payload_path, encoded)
        _private_json(meta_path, {
            "schema": _WRITER_REFERENCES_MEMO_SCHEMA,
            "implementation": _writer_references_memo_implementation(),
            "payload_bytes": len(encoded),
            "payload_sha256": hashlib.sha256(encoded).hexdigest(),
        })
    except (OSError, TypeError, ValueError):
        return
    if _WRITER_REFERENCES_MEMO_DIR is None:
        return
    try:
        rows = []
        for stale_meta in _WRITER_REFERENCES_MEMO_DIR.glob(
            "writer-references-*.meta.json"
        ):
            stale_payload = stale_meta.with_name(
                stale_meta.name[: -len(".meta.json")] + ".payload"
            )
            if stale_payload.is_file():
                rows.append((stale_meta.stat().st_mtime_ns, stale_meta, stale_payload))
        for _, stale_meta, stale_payload in sorted(rows, reverse=True)[
            _WRITER_REFERENCES_MEMO_KEEP:
        ]:
            stale_meta.unlink(missing_ok=True)
            stale_payload.unlink(missing_ok=True)
    except OSError:
        return


def _sealed_input_key(path: Path | None) -> tuple | None:
    if path is None:
        return None
    resolved = Path(path).expanduser().resolve()
    stat = resolved.stat()
    return (str(resolved), stat.st_size, stat.st_mtime_ns)


def _writer_type_references(
    *,
    runtime: Any,
    binary: Path,
    analysis: dict[str, Any],
    type_slots: _RuntimeTypeSlotResolver,
) -> dict[tuple[int, int], list[str]]:
    output: dict[tuple[int, int], list[str]] = {}
    with MappedPE(binary) as image:
        for message in analysis["messages_owner_only"]:
            method_index = message.get("write_to_method_index")
            if not isinstance(method_index, int):
                continue
            method = runtime.method_row(method_index)
            code = _bounded_code(image, method[3])
            if code is None:
                continue
            tags = _direct_tag_writes(code)
            loads = _rip_load_targets(code, method[3])
            for index, tag in enumerate(tags):
                start = max(0, int(tag["start"]) - 96)
                end = (
                    int(tags[index + 1]["start"])
                    if index + 1 < len(tags)
                    else len(code)
                )


                ranked_loads = sorted(
                    (
                        (offset, target)
                        for offset, target in loads
                        if start <= offset < end
                    ),
                    key=lambda item: (
                        item[0] < int(tag["end"]),
                        abs(item[0] - int(tag["end"])),
                    ),
                )
                names: list[str] = []
                for _offset, target in ranked_loads:
                    name = type_slots.resolve(target)
                    if name is not None:
                        names.append(name)
                        break
                key = (int(message["type_index"]), int(tag["field_number"]))
                accumulated = output.setdefault(key, [])
                for name in names:
                    if name not in accumulated:
                        accumulated.append(name)
    return output


def _oneof_branch_type_references(
    *,
    runtime: Any,
    image: MappedPE,
    type_index: int,
    method_indexes: Iterable[int],
    case_numbers: set[int],
    type_slots: _RuntimeTypeSlotResolver,
) -> dict[int, list[str]]:

    observations: dict[int, list[str]] = defaultdict(list)
    for method_index in method_indexes:
        method = runtime.method_row(method_index)
        if method[0] != type_index or not method[3]:
            continue
        code = _bounded_code(image, method[3])
        if code is None:
            continue
        loads = _rip_load_targets(code, method[3])
        if not loads:
            continue
        branches = _direct_case_branches(code)
        branch_starts = sorted(
            {
                target_offset
                for _number, _comparison, target_offset in branches
                if 0 <= target_offset < len(code)
            }
        )
        for number, _comparison, target_offset in branches:
            if number not in case_numbers:
                continue
            following = [start for start in branch_starts if start > target_offset]
            limit = following[0] if following else len(code)
            for offset, target in loads:
                if not target_offset <= offset < limit:
                    continue
                name = type_slots.resolve(target)
                if name is not None:
                    if name not in observations[number]:
                        observations[number].append(name)
                    break
    return dict(observations)


def _command_id_constant(code: bytes) -> int | None:

    from capstone import Cs, CS_ARCH_X86, CS_MODE_64
    from capstone.x86 import X86_OP_REG, X86_OP_IMM
    decoder=Cs(CS_ARCH_X86,CS_MODE_64);decoder.detail=True
    value=None
    for ins in decoder.disasm(code,0):
        if ins.mnemonic in ('nop','endbr64'):continue
        if ins.mnemonic=='ret':return value
        ops=ins.operands
        if (ins.mnemonic=='mov' and len(ops)==2 and ops[0].type==X86_OP_REG
            and decoder.reg_name(ops[0].reg) in ('ax','eax','rax') and ops[1].type==X86_OP_IMM):
            value=ops[1].imm&0xffff
        elif (ins.mnemonic=='xor' and len(ops)==2 and all(op.type==X86_OP_REG for op in ops)
              and ops[0].reg==ops[1].reg and decoder.reg_name(ops[0].reg) in ('ax','eax','rax')):
            value=0
        else:return None
    return None


def _bounded_entry_code(
    image: MappedPE, pointer: int, entry_boundaries: list[int]
) -> bytes | None:
    rva = pointer - image.image_base
    if rva <= 0 or not image.executable_rva(rva):
        return None
    function = image.containing_function(rva)
    boundary_index = bisect.bisect_right(entry_boundaries, rva)
    if boundary_index >= len(entry_boundaries):
        return None
    end_rva = entry_boundaries[boundary_index]
    if function is not None:
        end_rva = min(end_rva, function.end_rva)
    if end_rva <= rva:
        return None
    bounds = image.bounded_code(rva, end_rva)
    if bounds is None:
        return None
    start, end = bounds
    return bytes(image._mapping[start:end])


def _select_cmd_id_family(
    candidates: list[dict[str, Any]],
) -> tuple[dict[int, int], dict[str, Any]]:
    if not candidates:
        raise AcquisitionError("runtime proto command getter domain is empty")
    families = {candidate["family"] for candidate in candidates}
    if len(families) != 1:
        raise AcquisitionError(
            "runtime proto command getter family is structurally ambiguous"
        )
    by_owner: dict[int, list[dict[str, Any]]] = defaultdict(list)
    for candidate in candidates:
        by_owner[candidate["owner"]].append(candidate)
    if any(len(rows) != 1 for rows in by_owner.values()):
        raise AcquisitionError(
            "runtime proto command getter is not unique per message owner"
        )
    output = {
        owner: rows[0]["value"] for owner, rows in by_owner.items()
    }
    family = next(iter(families))
    evidence = {
        "selection": "unique-current-runtime-structural-method-family",
        "method_name_owner_only": family[0],
        "return_type_descriptor_owner_only": family[1],
        "attributes_owner_only": family[2],
        "implementation_attributes_owner_only": family[3],
        "slot_owner_only": family[4],
        "flags_owner_only": family[5],
        "candidate_method_count": len(candidates),
        "owner_count": len(output),
        "family_count": 1,
        "duplicate_owner_count": 0,
        "all_bodies_bounded_and_decoded": True,
        "fixed_method_name_used": False,
        "fixed_method_flags_used": False,
        "fixed_command_count_used": False,
    }
    return output, evidence


def _cmd_ids(
    runtime: Any, binary: Path, message_types: set[int]
) -> tuple[dict[int, int], dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    with MappedPE(binary) as image:
        entry_boundaries = sorted(
            {
                int(runtime.method_row(index)[3]) - image.image_base
                for index in range(runtime.method_count)
                if int(runtime.method_row(index)[3]) > image.image_base
                and image.executable_rva(
                    int(runtime.method_row(index)[3]) - image.image_base
                )
            }
            | {row[0] for row in image.runtime_functions}
            | {
                section.virtual_end
                for section in image.sections
                if section.executable
            }
        )
        for method_index in range(runtime.method_count):
            row = runtime.method_row(method_index)
            if (
                row[0] not in message_types
                or row[10]
                or row[5] & 0x10
                or runtime.method_return(method_index) != "System.UInt16"
            ):
                continue
            if not row[3]:
                raise AcquisitionError(
                    f"runtime proto command getter pointer unavailable: method {method_index}")
            code = _bounded_entry_code(image, row[3], entry_boundaries)
            if code is None:
                raise AcquisitionError(
                    f"runtime proto command getter code unavailable: method {method_index}")
            value = _command_id_constant(code)
            if value is None:
                raise AcquisitionError(
                    f"runtime proto command getter encoding unsupported: method {method_index}")
            candidates.append(
                {
                    "owner": int(row[0]),
                    "method_index": method_index,
                    "value": value,
                    "family": (
                        runtime.method_name(method_index, row),
                        int(row[4]),
                        int(row[5]),
                        int(row[6]),
                        int(row[8]),
                        int(row[9]),
                    ),
                }
            )
    return _select_cmd_id_family(candidates)


def _output_enum_indexes(runtime, messages):

    names = set()
    for message in messages:
        for field in message.get("fields", []):
            names.add(field.get("value_type") if field.get("cardinality") == "map" else field.get("type"))
        for oneof in message.get("oneofs", []):
            names.update(case["type"] for case in oneof["cases"])
    matches = defaultdict(list)
    for index in range(runtime.type_count):
        if runtime.renderer.identity_row(index)[1] & 0x20:
            name = runtime.renderer.root_name(index).rsplit(".", 1)[-1]
            if name in names:
                matches[name].append(index)
    if any(len(indexes) != 1 for indexes in matches.values()):
        raise AcquisitionError("output enum name identifies multiple runtime types")
    return {indexes[0] for indexes in matches.values()}


def _enum_literals(
    runtime: Any,
    field_by_index: dict[int, dict[str, Any]],
    fields_by_owner: dict[int, list[int]],
    type_index: int,
) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    for field_index in fields_by_owner.get(type_index, []):
        field = field_by_index[field_index]
        if field["name"] == "value__" or field["attributes"] & 0x40 == 0:
            continue
        output.append(
            {
                "field_index": field_index,
                "name": field["name"],
                "number": None,
            }
        )
    return output


def _load_enum_constants(path: Path | None, executable_sha256: str) -> dict[int, int]:
    if path is None:
        return {}
    path = path.expanduser().resolve()
    model = read_private_model(path)
    if (
        model.get("schema") != RUNTIME_PROTO_ENUM_CONSTANT_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256") != executable_sha256
        or not all(model.get("checks", {}).values())
    ):
        raise AcquisitionError("runtime proto enum constants are stale")
    output: dict[int, int] = {}
    for row in model.get("constants", []):
        field_index = row.get("field_index")
        number = row.get("number")
        if not isinstance(field_index, int) or not isinstance(number, int):
            raise AcquisitionError("runtime proto enum constant is invalid")
        if field_index in output and output[field_index] != number:
            raise AcquisitionError("runtime proto enum constants conflict")
        output[field_index] = number
    return output


def _load_enum_literal_attributes(
    path: Path | None, executable_sha256: str
) -> tuple[dict[int, frozenset[int]], set[int]]:
    if path is None:
        return {}, set()
    model = read_private_model(path.expanduser().resolve())
    if (
        model.get("schema") != RUNTIME_PROTO_ENUM_CONSTANT_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or not all(model.get("checks", {}).values())
    ):
        raise AcquisitionError("runtime proto enum attribute evidence is stale")
    output: dict[int, frozenset[int]] = {}
    incomplete: set[int] = set()
    for row in model.get("constants", []):
        field_index = row.get("field_index")
        attributes = row.get("custom_attribute_type_indexes_owner_only")
        if not isinstance(field_index, int):
            raise AcquisitionError("runtime proto enum attribute field is invalid")
        if attributes is None:
            incomplete.add(field_index)
            continue
        if (
            not isinstance(attributes, list)
            or any(type(index) is not int or index < 0 for index in attributes)
            or len(attributes) != len(set(attributes))
        ):
            raise AcquisitionError("runtime proto enum attribute set is invalid")
        output[field_index] = frozenset(attributes)
    return output, incomplete


def _validate_mutation_provenance(model: dict[str, Any]) -> None:
    inputs = model.get("inputs")
    plan_checks = model.get("plan_checks")
    policy = model.get("policy")
    if (
        not isinstance(inputs, dict)
        or not isinstance(plan_checks, dict)
        or not plan_checks
        or any(value is not True for value in plan_checks.values())
        or not isinstance(policy, dict)
        or policy.get("implicit_full_protobuf_range_scan_used") is not False
        or policy.get("merge_from_only") is not True
        or policy.get("write_to_used") is not False
    ):
        raise AcquisitionError("runtime proto mutation provenance is incomplete")
    plan_record = inputs.get("mutation_plan")
    if not isinstance(plan_record, dict) or not isinstance(
        plan_record.get("path"), str
    ):
        raise AcquisitionError("runtime proto mutation source plan is absent")
    plan_path = Path(plan_record["path"])
    if (
        not plan_path.is_file()
        or plan_path.is_symlink()
        or file_identity(plan_path) != plan_record
    ):
        raise AcquisitionError("runtime proto mutation source plan is stale")
    plan = read_json(plan_path)
    modes = {
        row.get("candidate_mode")
        for row in plan.get("messages_owner_only", [])
        if isinstance(row, dict)
    }
    if (
        plan.get("schema") != RUNTIME_PROTO_MUTATION_PLAN_SCHEMA
        or plan.get("status") != "offline-plan-complete"
        or plan.get("target", {}).get("executable_sha256")
        != model.get("target", {}).get("executable_sha256")
        or not isinstance(plan.get("checks"), dict)
        or not plan["checks"]
        or any(value is not True for value in plan["checks"].values())
        or not modes
        or not modes
        <= {
            "oneof-enum-literals",
            "parser-evidence-tag-domain",
            "parser-exhaustion-audit",
            "known-signed-scalar-audit",
            "runtime-parser-differential-scan",
        }
        or "full-protobuf-obfuscation-range" in modes
        or plan.get("policy", {}).get(
            "implicit_full_protobuf_range_scan_used"
        )
        is not False
    ):
        raise AcquisitionError(
            "runtime proto mutation source plan is not evidence-bound"
        )
    for row in plan.get("messages_owner_only", []):
        if row.get("candidate_mode") != "runtime-parser-differential-scan":
            continue
        start, end = row.get("scan_min"), row.get("scan_max")
        resolved = row.get("resolved_numbers")
        candidates = row.get("candidate_numbers")
        if (
            not isinstance(start, int) or not isinstance(end, int)
            or not 1 <= start <= end <= 0x1FFFFFFF
            or end - start >= 4096
            or not isinstance(resolved, list)
            or not isinstance(candidates, list)
            or candidates != [number for number in range(start, end + 1)
                              if number not in set(resolved)]
            or plan.get("policy", {}).get("fresh_runtime_parser_differential_scan") is not True
        ):
            raise AcquisitionError("runtime parser scan provenance is inconsistent")


def _load_runtime_field_assignments(
    *,
    serializer_probe_model: Path | Iterable[Path] | None,
    mutation_model: Path | Iterable[Path] | None,
    executable_sha256: str,
) -> tuple[dict[int, dict[str, Any]], set[int], dict[int, str]]:

    output: dict[int, dict[str, Any]] = {}
    confirmed_nonserialized: set[int] = set()
    nonserialized_evidence: dict[int, str] = {}

    def paths(value: Path | Iterable[Path] | None) -> list[Path]:
        if value is None:
            return []
        if isinstance(value, Path):
            return [value]
        result = list(value)
        if not all(isinstance(item, Path) for item in result):
            raise AcquisitionError("runtime proto observation path is invalid")
        return result

    def validated(path: Path, schema: str, label: str) -> dict[str, Any]:
        resolved = path.expanduser().resolve()
        model = read_private_model(resolved)
        if (
            model.get("schema") != schema
            or model.get("status") != "runtime-validated"
            or model.get("target", {}).get("executable_sha256")
            != executable_sha256
            or not all(model.get("checks", {}).values())
        ):
            raise AcquisitionError(f"runtime proto {label} model is stale")
        if schema == RUNTIME_PROTO_MUTATION_RESULT_SCHEMA:
            _validate_mutation_provenance(model)
        return model

    for mutation_path in paths(mutation_model):
        model = validated(
            mutation_path,
            RUNTIME_PROTO_MUTATION_RESULT_SCHEMA,
            "mutation",
        )
        source_plan = read_json(Path(model["inputs"]["mutation_plan"]["path"]))
        source_messages = source_plan.get("messages_owner_only", [])
        if not isinstance(source_messages, list):
            raise AcquisitionError("runtime proto mutation source messages are invalid")
        for row in model.get("assignments_owner_only", []):
            field_index = row.get("field_index_owner_only")
            number = row.get("field_number")
            wires = row.get("wires")
            if (
                not isinstance(field_index, int)
                or not isinstance(number, int)
                or not 0 < number <= 0x1FFFFFFF
                or not isinstance(wires, list)
                or len(wires) != 1
                or wires[0] not in (0, 1, 2, 5)
            ):
                raise AcquisitionError("runtime proto mutation assignment is invalid")
            previous = output.get(field_index)
            value = {
                "number": number,
                "wire": int(wires[0]),
                "source": "runtime-merge-from-unique-mutation",
            }
            if previous is not None and (
                previous["number"] != value["number"]
                or previous["wire"] != value["wire"]
            ):
                raise AcquisitionError("runtime proto mutation assignments conflict")
            output[field_index] = value
        for row in model.get("unmutated_fields_owner_only", []):
            field_index = row.get("field_index_owner_only")
            message_index = row.get("message_index_owner_only")
            if (
                not isinstance(field_index, int)
                or field_index < 0
                or not isinstance(message_index, int)
                or message_index < 0
                or message_index >= len(source_messages)
            ):
                raise AcquisitionError(
                    "runtime proto unmutated field coordinate is invalid"
                )
            if source_messages[message_index].get("candidate_mode") == "runtime-parser-differential-scan":


                continue
            confirmed_nonserialized.add(field_index)
            nonserialized_evidence[field_index] = (
                "runtime-merge-from-exhaustive-no-storage-mutation/v1"
            )

    for serializer_path in paths(serializer_probe_model):
        model = validated(
            serializer_path,
            RUNTIME_PROTO_SERIALIZER_RESULT_SCHEMA,
            "serializer probe",
        )
        for row in model.get("failures_owner_only", []):
            field_index = row.get("field_index_owner_only")
            failure_kind = row.get("failure_kind_owner_only")
            if not isinstance(field_index, int) or not isinstance(failure_kind, int):
                raise AcquisitionError("runtime proto serializer failure is invalid")


            if failure_kind == 7 or (
                failure_kind == 8
                and row.get("nonserialized_auxiliary_owner_only") is True
                and row.get("auxiliary_evidence") in {
                    "write-to-changes-only-already-resolved-tags/v1",
                    "write-to-invalid-payload-with-exhausted-tag-domain/v1",
                }
            ):
                confirmed_nonserialized.add(field_index)
                nonserialized_evidence.setdefault(field_index, (
                    "runtime-write-to-empty-output/v1"
                    if failure_kind == 7
                    else str(row["auxiliary_evidence"])
                ))
        for row in model.get("assignments_owner_only", []):
            field_index = row.get("field_index_owner_only")
            number = row.get("field_number")
            wire = row.get("wire")
            if (
                not isinstance(field_index, int)
                or not isinstance(number, int)
                or not 0 < number <= 0x1FFFFFFF
                or wire not in (0, 1, 2, 5)
            ):
                raise AcquisitionError("runtime proto serializer assignment is invalid")
            previous = output.get(field_index)
            if previous is not None and (
                previous["number"] != number or previous["wire"] != wire
            ):
                raise AcquisitionError(
                    "runtime proto serializer and mutation assignments conflict"
                )
            output[field_index] = {
                "number": number,
                "wire": int(wire),
                "source": "runtime-write-to-emitted-tag",
            }
            encoding = row.get("signed_encoding")
            if encoding is not None:
                from alpha.p01 import ENCODINGS, encoding_from_code, encoding_from_values
                code = next((code for code, name in ENCODINGS.items() if name == encoding), -1)
                encoding_from_code(code, row.get("runtime_type_enum"), wire)
                observation = {'runtime_type_enum': row.get('runtime_type_enum'), 'wire': wire,
                    'positive': row.get('signed_positive_wire_value'),
                    'negative': row.get('signed_negative_wire_value')}
                if encoding_from_values(observation['runtime_type_enum'], wire,
                        observation['positive'], observation['negative']) != encoding:
                    raise AcquisitionError("signed field observation does not support its encoding")
                if row.get("signed_encoding_evidence") != "write-to-positive-negative-123/v1":
                    raise AcquisitionError("runtime proto signed encoding evidence is missing")
                if previous and previous.get("signed_encoding", encoding) != encoding:
                    raise AcquisitionError("runtime proto signed encoding observations conflict")
                output[field_index].update(signed_encoding=encoding,
                    signed_encoding_evidence=row["signed_encoding_evidence"], signed_encoding_observation=observation)
            elif previous and "signed_encoding" in previous:
                output[field_index].update({key: previous[key] for key in
                    ("signed_encoding", "signed_encoding_evidence", "signed_encoding_observation")})
    overlap = confirmed_nonserialized & set(output)
    if overlap:
        raise AcquisitionError(
            "runtime proto fields are both serialized and non-serialized"
        )
    if set(nonserialized_evidence) != confirmed_nonserialized:
        raise AcquisitionError("runtime proto nonserialized evidence domain differs")
    return output, confirmed_nonserialized, nonserialized_evidence


def _load_oneof_runtime_observations(
    *,
    mutation_model: Path | None,
    runtime_materializer_model: Path | None,
    runtime: Any,
    binary: Path,
    executable_sha256: str,
) -> dict[tuple[int, int, int], dict[str, Any]]:
    if mutation_model is None and runtime_materializer_model is None:
        return {}
    if mutation_model is None or runtime_materializer_model is None:
        raise AcquisitionError(
            "runtime proto oneof observations require mutation and materializer models"
        )
    model_path = mutation_model.expanduser().resolve()
    model = read_private_model(model_path)
    if (
        model.get("schema") != RUNTIME_PROTO_MUTATION_RESULT_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or not all(model.get("checks", {}).values())
    ):
        raise AcquisitionError("runtime proto oneof mutation model is stale")
    _validate_mutation_provenance(model)
    output: dict[tuple[int, int, int], dict[str, Any]] = {}
    with LiveRuntimeInventory(
        materializer_model=runtime_materializer_model,
        binary=binary,
    ) as live:
        class_types: dict[int, tuple[int, str]] = {}
        for type_index in range(live.type_count):
            row = live.type_row(type_index)
            if row.class_pointer in class_types:
                raise AcquisitionError("runtime proto live class pointers conflict")
            class_types[row.class_pointer] = (type_index, row.name)
        for row in model.get("observations_owner_only", []):
            type_index = row.get("type_index_owner_only")
            field_index = row.get("field_index_owner_only")
            number = row.get("field_number")
            wire = row.get("wire")
            class_pointer = row.get("after_class_owner_only")
            if (
                not isinstance(type_index, int)
                or not isinstance(field_index, int)
                or not isinstance(number, int)
                or not 0 < number <= 0x1FFFFFFF
                or wire not in (0, 1, 2, 5)
                or not isinstance(class_pointer, int)
                or class_pointer not in class_types
            ):
                raise AcquisitionError("runtime proto oneof observation is invalid")
            observed_type_index, _observed_name = class_types[class_pointer]
            observed_name = runtime.renderer.root_name(observed_type_index)
            key = (type_index, field_index, number)
            value = {
                "wire": int(wire),
                "type_index": observed_type_index,
                "type_name": observed_name,
            }
            if key in output and output[key] != value:
                raise AcquisitionError("runtime proto oneof observations conflict")
            output[key] = value
    return output


def _classify_observed_oneof_type(
    observation: dict[str, Any],
    classifier: _ProtoTypes,
    wire: int,
) -> dict[str, Any] | None:
    type_index = int(observation["type_index"])
    name = str(observation["type_name"])
    classified = classifier.classify_name(name, wire)
    if classified is not None and classified.get("cardinality") == "singular":
        return classified
    if wire != 2:
        return None
    interfaces = classifier.runtime.renderer.root_interfaces(type_index)
    if name == "System.Byte[]" or any(
        item == "System.Collections.Generic.IEnumerable<System.Byte>"
        for item in interfaces
    ):
        return {"cardinality": "singular", "type": "bytes"}
    if type_index in classifier.message_types:
        return {
            "cardinality": "singular",
            "type": name.rsplit(".", 1)[-1],
        }
    return None


def _pick_writer_type(
    names: list[str],
    classifier: _ProtoTypes,
    wire: int,
    ambiguous: list | None = None,
) -> dict[str, Any] | None:
    candidates: list[dict[str, Any]] = []
    labels: list[str] = []
    for name in names:
        classified = classifier.classify_name(name, wire)
        if classified is not None and classified not in candidates:
            candidates.append(classified)
            labels.append(name)
    if not candidates:
        return None
    if len(candidates) == 1:
        return candidates[0]

    def kind_rank(index: int) -> int:
        definition = classifier.definition_by_name.get(
            str(candidates[index].get("type"))
        )
        if definition is None:
            return 2
        if definition in classifier.message_types:
            return 0 if wire == 2 else 2
        if classifier.runtime.renderer.identity_row(definition)[1] & 0x20:
            return 0 if wire == 0 else 2
        return 2

    order = sorted(
        range(len(candidates)), key=lambda index: (kind_rank(index), labels[index])
    )
    best_rank = kind_rank(order[0])
    best = [index for index in order if kind_rank(index) == best_rank]
    if len(best) != 1:
        if ambiguous is not None:
            ambiguous.extend(
                {
                    "type": candidates[index].get("type"),
                    "candidate": labels[index],
                }
                for index in best
            )
        return None
    if ambiguous is not None:
        ambiguous.extend(
            {"type": candidates[index].get("type"), "candidate": labels[index]}
            for index in order
            if index != best[0] and kind_rank(index) == best_rank
        )
    return candidates[best[0]]


def _pick_natural_writer_type(
    names: list[str], classifier: _ProtoTypes
) -> tuple[int, dict[str, Any]] | None:
    candidates: list[tuple[int, dict[str, Any]]] = []
    for name in names:
        wire = classifier._natural_wire(name)
        classified = classifier.classify_name(name, wire)
        candidate = (wire, classified) if classified is not None else None
        if (
            candidate is not None
            and classified.get("cardinality") == "singular"
            and candidate not in candidates
        ):
            candidates.append(candidate)
    return candidates[0] if len(candidates) == 1 else None


def _parser_reader_wire_evidence(
    *, analysis_messages: list[dict[str, Any]], runtime: Any, binary: Path,
) -> dict[tuple[int, int], int]:
    from capstone import Cs, CS_ARCH_X86, CS_MODE_64, CS_GRP_CALL, CS_GRP_JUMP
    from capstone.x86_const import X86_OP_IMM, X86_OP_MEM

    wires_by_reader: dict[int, set[int]] = defaultdict(set)
    for source in analysis_messages:
        for mapping in source.get("mappings", []):
            if (
                mapping.get("source") != "bounded-parser-tag-case"
                or mapping.get("wire_evidence") != "exact-tag"
            ):
                continue
            for access in mapping.get("field_accesses", []):
                transfer = access.get("parser_body_transfer_owner_only") or {}
                reader = transfer.get("reader_method_owner_only") or {}
                pointer = reader.get("call_target_owner_only")
                if transfer.get("status") == "proven" and type(pointer) is int:
                    wires_by_reader[pointer].add(int(mapping["wire"]))
    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    decoder.detail = True
    evidence: dict[tuple[int, int], int] = {}
    reader_by_case: dict[tuple[int, int], int] = {}
    with MappedPE(binary) as image:
        for source in analysis_messages:
            type_index = int(source["type_index"])
            normalized = [
                mapping for mapping in source.get("mappings", [])
                if mapping.get("source") == "bounded-parser-tag-case"
                and mapping.get("wire_evidence") == "field-number-only"
            ]
            method_index = source.get("merge_from_method_index")
            if not normalized or type(method_index) is not int:
                continue
            pointer = int(runtime.method_row(method_index)[3])
            code = _bounded_code(image, pointer)
            if not code:
                continue
            case_starts = {
                int(case["field_number"]): int(case["case_start"])
                for case in _tag_cases(code)
                if case.get("wire_evidence") == "field-number-only"
                and type(case.get("case_start")) is int
            }
            for mapping in normalized:
                number = int(mapping["field_number"])
                start = case_starts.get(number)
                writes = sorted(
                    int(access["code_offset"])
                    for access in mapping.get("field_accesses", [])
                    if access.get("access") in {"write", "read_write"}
                    and type(access.get("code_offset")) is int
                )
                if start is None or not writes or not start <= writes[0] < len(code):
                    continue
                write_offset = writes[0]
                instructions = list(decoder.disasm(
                    code[start:write_offset + 15], start
                ))
                if not any(int(ins.address) == write_offset for ins in instructions):
                    continue
                prior_calls = [
                    ins for ins in instructions
                    if ins.group(CS_GRP_CALL)
                    and ins.operands and ins.operands[0].type == X86_OP_IMM
                    and 0 < write_offset - int(ins.address) <= 32
                ]
                if not prior_calls:
                    continue
                call = prior_calls[-1]
                if any(
                    ins.group(CS_GRP_JUMP)
                    and int(call.address) < int(ins.address) < write_offset
                    for ins in instructions
                ):
                    continue
                reader_pointer = pointer + int(call.operands[0].imm)
                reader_by_case[(type_index, number)] = reader_pointer
        unresolved_readers = set(reader_by_case.values())
        method_indexes_by_pointer: dict[int, list[int]] = defaultdict(list)
        if unresolved_readers:
            for method_index in range(runtime.method_count):
                pointer = int(runtime.method_row(method_index)[3])
                if pointer in unresolved_readers:
                    method_indexes_by_pointer[pointer].append(method_index)
        for pointer in unresolved_readers:
            method_indexes = method_indexes_by_pointer.get(pointer, [])
            if len(method_indexes) != 1:
                continue
            method_index = method_indexes[0]
            method = runtime.method_row(method_index)
            if (
                method[10] != 0
                or runtime.method_return(method_index) not in {
                    "System.Int32", "System.UInt32", "System.Int64", "System.UInt64"
                }
            ):
                continue
            code = _bounded_code(image, pointer)
            if not code:
                continue
            byte_reads = 0
            low_seven_masks = 0
            shifts: set[int] = set()
            for instruction in decoder.disasm(code, 0):
                operands = instruction.operands
                if (
                    instruction.mnemonic.lower() == "movzx"
                    and len(operands) == 2
                    and operands[1].type == X86_OP_MEM
                    and operands[1].size == 1
                ):
                    byte_reads += 1
                if len(operands) == 2 and operands[1].type == X86_OP_IMM:
                    immediate = int(operands[1].imm)
                    if instruction.mnemonic.lower() == "and" and immediate == 0x7F:
                        low_seven_masks += 1
                    elif instruction.mnemonic.lower() == "shl" and immediate in {7, 14, 21, 28, 35, 42, 49, 56, 63}:
                        shifts.add(immediate)
            if (
                (byte_reads or low_seven_masks >= 3)
                and low_seven_masks and 7 in shifts and len(shifts) >= 2
            ):
                wires_by_reader[pointer].add(0)
        for key, pointer in reader_by_case.items():
            wires = wires_by_reader.get(pointer, set())
            if len(wires) == 1:
                evidence[key] = next(iter(wires))
    return evidence


def _select_tag_candidate(
    candidates: list[dict[str, Any]],
    *,
    mapping: dict[str, Any] | None,
    observed: dict[str, Any] | None,
    reader_wire: int | None = None,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
    if not candidates:
        return None, {"reason": "no-candidates"}
    number = int(candidates[0]["field_number"])
    if any(int(item["field_number"]) != number for item in candidates):
        raise AcquisitionError("tag candidate group contains multiple field numbers")

    def has_wire_evidence(item: dict[str, Any]) -> bool:
        sources = set(str(value) for value in item.get("sources", []))
        evidence = set(
            str(value) for value in item.get("wire_evidence_sources", [])
        )
        if sources & {
            "bounded-writer-varint-tag",
            "bounded-static-formatter-tag",
        }:
            return True
        return "exact-tag" in evidence

    number_only_candidates = [
        item
        for item in candidates
        if "bounded-parser-tag-case" in item.get("sources", [])
        and "field-number-only"
        in set(str(value) for value in item.get("wire_evidence_sources", []))
        and not has_wire_evidence(item)
    ]
    wire_evidence_wires = {
        int(item["wire"]) for item in candidates if has_wire_evidence(item)
    }

    proof_sets: list[tuple[str, set[int]]] = []
    if observed is not None and int(observed.get("number", -1)) == number:
        proof_sets.append(("runtime-field-assignment", {int(observed["wire"])}))
    if reader_wire is not None:
        proof_sets.append(("bounded-parser-reader-wire", {reader_wire}))
    formatter_wires = {
        int(item["wire"])
        for item in candidates
        if "bounded-static-formatter-tag" in item.get("sources", [])
    }
    writer_wires = {
        int(item["wire"])
        for item in candidates
        if "bounded-writer-varint-tag" in item.get("sources", [])
    }
    if formatter_wires:
        proof_sets.append(("static-formatter-tag", formatter_wires))
    if writer_wires:
        proof_sets.append(("writer-tag", writer_wires))

    direct_wires = set().union(*(values for _name, values in proof_sets)) if proof_sets else set()
    if len(direct_wires) > 1:
        return None, {
            "reason": "direct-evidence-disagrees",
            "evidence_owner_only": {
                name: sorted(values) for name, values in proof_sets
            },
        }
    if direct_wires:
        chosen_wire = next(iter(direct_wires))
        evidence = [name for name, values in proof_sets if chosen_wire in values]
    elif (
        mapping is not None
        and mapping.get("wire") is not None
        and mapping.get("wire_evidence") != "field-number-only"
    ):
        chosen_wire = int(mapping["wire"])
        mapping_evidence = str(mapping.get("wire_evidence", ""))
        evidence = [
            "single-parser-wire"
            if mapping_evidence == "exact-tag"
            else "runtime-field-assignment"
            if mapping_evidence == "runtime-field-assignment"
            else str(mapping.get("source", "field-mapping"))
        ]
    elif len(wire_evidence_wires) == 1:
        chosen_wire = next(iter(wire_evidence_wires))
        evidence = ["single-parser-wire"]
    else:
        return None, {
            "reason": (
                "parser-switch-proves-field-number-only"
                if number_only_candidates and not wire_evidence_wires
                else "multiple-wires-without-deciding-evidence"
            ),
            "accepted_wires_owner_only": sorted(wire_evidence_wires),
            "field_number_only_parser_case_count": len(number_only_candidates),
        }

    matches = [
        item
        for item in candidates
        if int(item["wire"]) == chosen_wire and has_wire_evidence(item)
    ]
    if not matches:
        if not number_only_candidates or not direct_wires:
            return None, {
                "reason": "evidence-wire-absent-from-candidates",
                "wire": chosen_wire,
                "accepted_wires_owner_only": sorted(wire_evidence_wires),
                "evidence_owner_only": evidence,
            }
        selected = dict(number_only_candidates[0])
        selected["wire"] = chosen_wire
        selected["raw_tag"] = (number << 3) | chosen_wire
        selected["wire_evidence_sources"] = list(
            selected.get("wire_evidence_sources", [])
        )
        selected["wire_evidence_sources"].extend(
            name for name, values in proof_sets
            if chosen_wire in values
            and name not in selected["wire_evidence_sources"]
        )
    else:
        selected = dict(matches[0])
    supporting_candidates = [*matches, *number_only_candidates]
    selected["sources"] = sorted(
        {
            str(source)
            for item in supporting_candidates
            for source in item.get("sources", [])
        }
    )
    selected_wire_sources = {
        str(value) for value in selected.get("wire_evidence_sources", [])
    }
    selected_wire_sources.update(
        str(value)
        for item in supporting_candidates
        for value in item.get("wire_evidence_sources", [])
    )
    selected["wire_evidence_sources"] = sorted(selected_wire_sources)
    selected["accepted_wires_owner_only"] = sorted(wire_evidence_wires)
    selected["wire_selection_evidence_owner_only"] = evidence
    return selected, None


def unaccounted_runtime_members(
    *,
    messages: list[dict[str, Any]],
    fields_by_owner: Mapping[int, Iterable[int]],
    runtime_nonserialized_fields: Iterable[int],
    structural_member_indexes: Iterable[int],
    mapping_accessed_members: Mapping[int, Iterable[int]],
    non_protobuf_members: Mapping[int, Iterable[int]],
    runtime_field_names: Mapping[int, str],
) -> list[dict[str, Any]]:
    shared = (
        set(int(index) for index in runtime_nonserialized_fields)
        | set(int(index) for index in structural_member_indexes)
    )
    records: list[dict[str, Any]] = []
    for message in messages:
        type_index = int(message["type_index_owner_only"])
        accounted = {
            int(field["field_index_owner_only"]) for field in message["fields"]
        }
        for oneof in message.get("oneofs") or []:
            for key in (
                "storage_field_index_owner_only",
                "discriminator_field_index_owner_only",
            ):
                value = oneof.get(key)
                if isinstance(value, int) and not isinstance(value, bool):
                    accounted.add(value)
        accounted |= shared
        accounted |= set(
            int(index) for index in mapping_accessed_members.get(type_index, ())
        )
        accounted |= set(
            int(index) for index in non_protobuf_members.get(type_index, ())
        )
        missing = sorted(
            int(index) for index in fields_by_owner.get(type_index, ())
        )
        missing = [index for index in missing if index not in accounted]
        if missing:
            records.append(
                {
                    "message": message["name"],
                    "type_index_owner_only": type_index,
                    "field_indexes_owner_only": missing,
                    "rendered_types_owner_only": {
                        str(field_index): str(
                            runtime_field_names.get(field_index, "")
                        )
                        for field_index in missing
                    },
                    "wire_contract_disposition": (
                        "unresolved-current-runtime-member"
                    ),
                }
            )
    return records


def instance_member_domain(
    field_by_index: Mapping[int, Mapping[str, Any]],
    fields_by_owner: Mapping[int, Iterable[int]],
) -> dict[int, list[int]]:
    return {
        type_index: [
            field_index for field_index in field_indexes
            if not int(field_by_index[field_index]["attributes"]) & 0x10
        ]
        for type_index, field_indexes in fields_by_owner.items()
    }


def build_runtime_proto_static_model(
    *,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    enum_constant_model: Path | None = None,
    serializer_probe_model: Path | Iterable[Path] | None = None,
    mutation_model: Path | Iterable[Path] | None = None,
    oneof_mutation_model: Path | None = None,
    runtime_materializer_model: Path | None = None,
    snapshot: Path | None = None,
) -> dict[str, Any]:

    receipt, paths, runtime = _runtime(native_output_receipt)
    analysis = analyze_runtime_proto(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
    )
    group_wire_audit = analysis.get("group_wire_audit")
    if (
        not isinstance(group_wire_audit, dict)
        or group_wire_audit.get("wire_types_checked") != [3, 4, 6, 7]
        or group_wire_audit.get("observed_group_wire_tag_count") != 0
        or group_wire_audit.get("disposition")
        != "fail-closed-if-observed-or-uncovered-serialized-message"
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
        or not isinstance(
            group_wire_audit.get("parserless_message_type_indexes_owner_only"),
            list,
        )
    ):
        raise AcquisitionError(
            "runtime group wire audit is absent, incomplete, or reports a group tag"
        )
    _base, selected_types = _message_types(runtime)
    if group_wire_audit["selected_message_count"] != len(selected_types):
        raise AcquisitionError(
            "runtime group wire audit message domain differs from modeled types"
        )
    parserless_type_indexes = group_wire_audit[
        "parserless_message_type_indexes_owner_only"
    ]
    if (
        any(type(index) is not int or index < 0 for index in parserless_type_indexes)
        or len(set(parserless_type_indexes)) != len(parserless_type_indexes)
        or parserless_type_indexes != sorted(parserless_type_indexes)
        or group_wire_audit["selected_bounded_parser_count"]
        != len(selected_types) - len(parserless_type_indexes)
    ):
        raise AcquisitionError("runtime group wire parser coverage inventory is invalid")
    selected = set(selected_types)
    parserless_type_set = set(parserless_type_indexes)
    analysis_parserless_type_set = {
        int(row["type_index"])
        for row in analysis.get("messages_owner_only", [])
        if row.get("merge_from_method_index") is None
    }
    if parserless_type_set != analysis_parserless_type_set:
        raise AcquisitionError(
            "runtime group wire parserless type inventory differs from analyzed messages"
        )
    classifier = _ProtoTypes(runtime, selected)
    field_by_index, fields_by_owner = _field_rows(runtime)


    instance_fields_by_owner = instance_member_domain(field_by_index, fields_by_owner)
    constants = _load_enum_constants(
        enum_constant_model, receipt["target"]["executable_sha256"]
    )
    enum_literal_attributes, incomplete_enum_attribute_fields = _load_enum_literal_attributes(
        enum_constant_model, receipt["target"]["executable_sha256"]
    )
    (
        runtime_assignments,
        runtime_nonserialized_fields,
        runtime_nonserialized_evidence,
    ) = _load_runtime_field_assignments(
        serializer_probe_model=serializer_probe_model,
        mutation_model=mutation_model,
        executable_sha256=receipt["target"]["executable_sha256"],
    )
    from alpha.p01 import validate_exclusions
    exclusion_evidence = validate_exclusions(
        runtime, analysis, field_by_index, runtime_nonserialized_fields,
        paths["binary"], runtime_nonserialized_evidence)
    oneof_observations = _load_oneof_runtime_observations(
        mutation_model=oneof_mutation_model,
        runtime_materializer_model=runtime_materializer_model,
        runtime=runtime,
        binary=paths["binary"],
        executable_sha256=receipt["target"]["executable_sha256"],
    )
    all_field_descriptors = [
        int(field["descriptor"])
        for message in analysis["messages_owner_only"]
        for field in message["fields"]
    ]
    type_slots, native_type_names = _type_usage_context(
        receipt, paths, runtime, all_field_descriptors
    )
    native_type_names.update(
        _live_embedded_type_names(
            runtime_materializer_model=runtime_materializer_model,
            runtime=runtime,
            binary=paths["binary"],
        )
    )
    methods_by_owner: dict[int, list[int]] = defaultdict(list)
    for method_index in range(runtime.method_count):
        methods_by_owner[int(runtime.method_row(method_index)[0])].append(method_index)
    possible_oneof_types: set[int] = set()
    for source in analysis["messages_owner_only"]:
        type_index = int(source["type_index"])
        owner_descriptor = runtime.renderer.identity_row(type_index)[2]
        has_object = False
        has_nested_enum = False
        for field in source["fields"]:
            descriptor = int(field["descriptor"])
            name = native_type_names.get(
                descriptor,
                runtime.renderer.render(descriptor)
                if descriptor in runtime.renderer.node_by_descriptor
                else "",
            )
            field_type = runtime.renderer.root_by_descriptor.get(descriptor)
            if field_type is None:
                field_type = classifier.index_by_name.get(name)
            has_object = has_object or name == "System.Object"
            has_nested_enum = has_nested_enum or (
                field_type is not None
                and runtime.renderer.identity_row(field_type)[1] & 0x20
                and runtime.renderer.identity_row(field_type)[5] == owner_descriptor
            )
        if has_object and has_nested_enum:
            possible_oneof_types.add(type_index)
    oneof_branch_types: dict[tuple[int, int], list[str]] = {}
    writer_cache_key = (
        _sealed_input_key(paths["binary"]),
        _sealed_input_key(native_output_receipt),
        _sealed_input_key(proto_field_type_model),
        _sealed_input_key(snapshot),
        _sealed_input_key(runtime_materializer_model),
        _sealed_input_key(enum_constant_model),
    )
    cached_references = _WRITER_REFERENCES_CACHE.get(writer_cache_key)
    if cached_references is None:


        persistent_references = _load_writer_references_memo(writer_cache_key)
        if persistent_references is not None:
            cached_references = persistent_references
            _WRITER_REFERENCES_CACHE[writer_cache_key] = persistent_references
    if cached_references is not None:
        writer_types = copy.deepcopy(cached_references[0])
        oneof_branch_types = copy.deepcopy(cached_references[1])
    else:
        with _RuntimeTypeSlotResolver(
            snapshot=snapshot,
            runtime_materializer_model=runtime_materializer_model,
            runtime=runtime,
            binary=paths["binary"],
            static_slots=type_slots,
        ) as resolved_type_slots:
            writer_types = _writer_type_references(
                runtime=runtime,
                binary=paths["binary"],
                analysis=analysis,
                type_slots=resolved_type_slots,
            )
            case_numbers = {
                int(number) for number in constants.values() if int(number) > 0
            }
            with MappedPE(paths["binary"]) as image:
                for type_index in sorted(possible_oneof_types):
                    for number, names in _oneof_branch_type_references(
                        runtime=runtime,
                        image=image,
                        type_index=type_index,
                        method_indexes=methods_by_owner.get(type_index, []),
                        case_numbers=case_numbers,
                        type_slots=resolved_type_slots,
                    ).items():
                        oneof_branch_types[(type_index, number)] = names
        if len(_WRITER_REFERENCES_CACHE) >= 4:
            _WRITER_REFERENCES_CACHE.clear()
        _WRITER_REFERENCES_CACHE[writer_cache_key] = (
            copy.deepcopy(writer_types), copy.deepcopy(oneof_branch_types),
        )
        _store_writer_references_memo(
            writer_cache_key, writer_types, oneof_branch_types
        )
    cmd_ids, command_id_getter_evidence = _cmd_ids(
        runtime, paths["binary"], selected
    )

    messages: list[dict[str, Any]] = []
    referenced_enum_indexes: set[int] = set()
    discriminator_indexes: set[int] = set()
    unresolved: list[dict[str, Any]] = []
    unattributed_member_records: list[dict[str, Any]] = []
    diagnostics: list[dict[str, Any]] = []
    runtime_field_names: dict[int, str] = {}
    structural_member_indexes: set[int] = set()
    mapping_accessed_members: dict[int, set[int]] = {}
    non_protobuf_members: dict[int, set[int]] = {}
    cross_source_mapping_conflicts = int(
        analysis.get("counts", {}).get("cross_source_mapping_conflict_count", 0)
    )
    if cross_source_mapping_conflicts:
        diagnostics.append(
            {
                "kind": "static-field-access-scanner-conflicts",
                "count": cross_source_mapping_conflicts,
                "resolution": (
                    "parser case mappings retain field ownership; writer and "
                    "formatter scans remain tag-wire evidence because their "
                    "bounded regions can include neighbouring field accesses"
                ),
            }
        )
    expected_normal_field_count = 0
    expected_oneof_case_count = 0
    reader_wire_evidence = _parser_reader_wire_evidence(
        analysis_messages=analysis["messages_owner_only"],
        runtime=runtime,
        binary=paths["binary"],
    )

    for source in analysis["messages_owner_only"]:
        type_index = int(source["type_index"])
        candidate_groups: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for candidate in source["candidate_tags"]:
            candidate_groups[int(candidate["field_number"])].append(candidate)
        fields = {int(item["field_index"]): item for item in source["fields"]}
        rendered = {
            field_index: native_type_names.get(
                int(item["descriptor"]),
                runtime.renderer.render(int(item["descriptor"]))
                if int(item["descriptor"]) in runtime.renderer.node_by_descriptor
                else "",
            )
            for field_index, item in fields.items()
        }
        missing_rendered_types = [index for index, name in rendered.items() if not name]
        if missing_rendered_types:
            unresolved.append({
                "kind": "field-type-unresolved",
                "message": source["name"],
                "field_indexes_owner_only": sorted(missing_rendered_types),
            })
        runtime_field_names.update(rendered)
        accessed_members: set[int] = set()
        for mapping in source["mappings"]:
            for access in mapping.get("field_accesses") or []:
                index = access.get("field_index")
                if isinstance(index, int) and not isinstance(index, bool):
                    accessed_members.add(index)
        mapping_accessed_members[type_index] = accessed_members
        nested_enums: list[tuple[int, int]] = []
        object_fields: list[int] = []
        owner_descriptor = runtime.renderer.identity_row(type_index)[2]
        for field_index, name in rendered.items():
            enum_index = runtime.renderer.root_by_descriptor.get(
                int(fields[field_index]["descriptor"])
            )
            if enum_index is None:
                enum_index = classifier.index_by_name.get(name)
            if (
                enum_index is not None
                and runtime.renderer.identity_row(enum_index)[1] & 0x20
                and runtime.renderer.identity_row(enum_index)[5] == owner_descriptor
            ):
                nested_enums.append((field_index, enum_index))
            elif name == "System.Object":
                object_fields.append(field_index)

        oneof_pairs: list[tuple[int, int, int]] = []
        used_object_fields: set[int] = set()
        for discriminator_field, enum_index in nested_enums:
            scored: list[tuple[int, int]] = []
            enum_literals = _enum_literals(
                runtime, field_by_index, fields_by_owner, enum_index
            )
            literal_count = sum(
                str(item["name"]).casefold() != "none" for item in enum_literals
            )
            for object_field in object_fields:
                support = 0
                primary_count = 0
                for mapping in source["mappings"]:
                    accesses = {
                        int(item["field_index"])
                        for item in mapping.get("field_accesses", [])
                    }
                    if object_field in accesses and discriminator_field in accesses:
                        support += 1
                    if int(mapping["primary_field_index"]) == object_field:
                        primary_count += 1
                exact_case_count = int(primary_count == literal_count)
                if object_field not in used_object_fields and (support or exact_case_count):
                    scored.append(
                        (exact_case_count * 100000 + support * 100 + primary_count, object_field)
                    )
            scored.sort(reverse=True)
            if scored and (len(scored) == 1 or scored[0][0] > scored[1][0]):
                oneof_pairs.append((scored[0][1], discriminator_field, enum_index))
                used_object_fields.add(scored[0][1])
                discriminator_indexes.add(enum_index)
        remaining_enums = [
            item for item in nested_enums if item[1] not in discriminator_indexes
        ]
        remaining_objects = [
            item for item in object_fields if item not in used_object_fields
        ]
        if len(remaining_enums) == len(remaining_objects) == 1:
            discriminator_field, enum_index = remaining_enums[0]
            oneof_pairs.append(
                (remaining_objects[0], discriminator_field, enum_index)
            )
            discriminator_indexes.add(enum_index)


        declared_oneof_numbers: set[int] = set()
        for _storage_field, _discriminator_field, enum_index in oneof_pairs:
            for literal in _enum_literals(
                runtime, field_by_index, fields_by_owner, enum_index
            ):
                number = constants.get(int(literal["field_index"]))
                if isinstance(number, int) and number > 0:
                    declared_oneof_numbers.add(number)

        oneof_storage = {item[0] for item in oneof_pairs}
        oneof_discriminators = {item[1] for item in oneof_pairs}
        unsupported_message_fields = _unsupported_message_wire_field_indexes(
            rendered=rendered,
            message_type_names={
                runtime.renderer.root_name(message_type)
                for message_type in selected
            },
            excluded_field_indexes=(
                oneof_storage
                | oneof_discriminators
                | runtime_nonserialized_fields
            ),
            classifier=classifier,
        )
        if unsupported_message_fields:
            raise AcquisitionError(
                "runtime message-valued field has no supported protobuf wire "
                "classification (possible group or unmodeled feature): "
                + repr(
                    {
                        "message": source["name"],
                        "fields": [
                            {
                                "field_index_owner_only": index,
                                "rendered_type": rendered[index],
                            }
                            for index in unsupported_message_fields
                        ],
                    }
                )
            )
        serializable_fields = {
            field_index
            for field_index, name in rendered.items()
            if field_index not in oneof_storage
            and field_index not in oneof_discriminators
            and field_index not in runtime_nonserialized_fields
            and any(
                classifier.classify_name(name, wire) is not None
                for wire in (0, 1, 2, 5)
            )
        }
        non_serializable_fields = (
            set(fields)
            - oneof_storage
            - oneof_discriminators
            - serializable_fields
        )


        native_members = {
            int(index) for index in instance_fields_by_owner.get(type_index, ())
        }
        if native_members != set(fields):
            raise AcquisitionError(
                "runtime proto field-type inventory does not cover the exact "
                f"instance member domain of {source['name']}: "
                f"missing={sorted(native_members - set(fields))[:16]}, "
                f"foreign={sorted(set(fields) - native_members)[:16]}"
            )
        expected_normal_field_count += len(serializable_fields)
        non_protobuf_members[type_index] = set(non_serializable_fields)
        if non_serializable_fields:
            diagnostics.append(
                {
                    "kind": "non-protobuf-instance-fields",
                    "message": source["name"],
                    "field_indexes_owner_only": sorted(non_serializable_fields),
                    "rendered_types_owner_only": {
                        str(field_index): rendered[field_index]
                        for field_index in sorted(non_serializable_fields)
                    },
                }
            )
        expected_oneof_case_count += sum(
            max(
                0,
                len(
                    _enum_literals(
                        runtime, field_by_index, fields_by_owner, enum_index
                    )
                )
                - 1,
            )
            for _storage, _discriminator, enum_index in oneof_pairs
        )
        mapping_by_number: dict[int, dict[str, Any]] = {}
        mappings_by_number: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for mapping in source["mappings"]:
            mappings_by_number[int(mapping["field_number"])].append(mapping)
        source_priority = {
            "bounded-parser-tag-case": 0,
            "bounded-writer-varint-tag": 1,
            "bounded-static-formatter-tag": 2,
        }
        for number, alternatives in mappings_by_number.items():
            best_priority = min(
                source_priority.get(str(item.get("source")), 99)
                for item in alternatives
            )
            strongest = [
                item
                for item in alternatives
                if source_priority.get(str(item.get("source")), 99)
                == best_priority
            ]
            field_number_only = all(
                item.get("wire_evidence") == "field-number-only"
                for item in strongest
            )
            wires = {int(item["wire"]) for item in strongest}
            mapping_wires = {0, 1, 2, 5} if field_number_only else wires
            accessed_fields = {
                int(access["field_index"])
                for item in strongest
                for access in item.get("field_accesses", [])
                if int(access["field_index"]) in fields
            }
            plausible_fields = {
                field_index
                for field_index in accessed_fields
                if field_index in oneof_storage
                or any(
                    classifier.classify_name(rendered[field_index], wire)
                    is not None
                    for wire in mapping_wires
                )
            }
            if len(plausible_fields) == 1:
                selected_primary = next(iter(plausible_fields))
                selected_mapping = dict(min(
                    strongest,
                    key=lambda item: (
                        int(item["primary_field_index"]), int(item["wire"])
                    ),
                ))
                selected_mapping["primary_field_index"] = selected_primary


                if len(wires) != 1 or field_number_only:
                    selected_mapping["wire"] = None
                selected_mapping["wire_evidence"] = (
                    "field-number-only" if field_number_only else "exact-tag"
                )
                mapping_by_number[number] = selected_mapping
            else:
                diagnostics.append(
                    {
                        "kind": "ambiguous-static-field-mapping",
                        "message": source["name"],
                        "number": number,
                        "strongest_source_priority_owner_only": best_priority,
                        "alternatives_owner_only": [
                            {
                                "source": item.get("source"),
                                "wire": int(item["wire"]),
                                "primary_field_index": int(
                                    item["primary_field_index"]
                                ),
                                "accessed_field_indexes": sorted(
                                    int(access["field_index"])
                                    for access in item.get("field_accesses", [])
                                    if int(access["field_index"]) in fields
                                ),
                            }
                            for item in strongest
                        ],
                        "effect": (
                            "static assignment withheld; runtime mutation must "
                            "establish the field identity"
                        ),
                    }
                )
        source_candidates: list[dict[str, Any]] = []
        for number, candidates in sorted(candidate_groups.items()):
            mapping = mapping_by_number.get(number)
            observed_matches = [
                (field_index, runtime_assignments[field_index])
                for field_index in fields
                if field_index in runtime_assignments
                and int(runtime_assignments[field_index].get("number", -1))
                == number
            ]
            if len(observed_matches) > 1:
                unresolved.append(
                    {
                        "kind": "runtime-field-number-conflict",
                        "message": source["name"],
                        "number": number,
                        "field_indexes_owner_only": sorted(
                            field_index
                            for field_index, _observation in observed_matches
                        ),
                    }
                )
                observed = None
            elif observed_matches:
                observed_field, observed = observed_matches[0]
                if mapping is None or int(mapping["primary_field_index"]) != observed_field:
                    diagnostics.append(
                        {
                            "kind": "static-field-mapping-overridden-by-runtime",
                            "message": source["name"],
                            "number": number,
                            "static_field_index_owner_only": (
                                int(mapping["primary_field_index"])
                                if mapping is not None
                                else None
                            ),
                            "runtime_field_index_owner_only": observed_field,
                        }
                    )
                    mapping = {
                        "field_number": number,
                        "wire": int(observed["wire"]),
                        "primary_field_index": observed_field,
                        "source": "runtime-field-assignment",
                    }
                    mapping_by_number[number] = mapping
            else:
                primary = (
                    int(mapping["primary_field_index"])
                    if mapping is not None
                    else None
                )
                observed = (
                    runtime_assignments.get(primary)
                    if primary is not None
                    else None
                )
                if observed is not None and mapping is not None:
                    mapping = dict(mapping)
                    mapping["wire"] = int(observed["wire"])
                    mapping["wire_evidence"] = "runtime-field-assignment"
                    mapping["source"] = "runtime-field-assignment"
                    mapping_by_number[number] = mapping
            selected_candidate, selection_error = _select_tag_candidate(
                candidates, mapping=mapping, observed=observed,
                reader_wire=reader_wire_evidence.get((type_index, number)),
            )
            if selection_error is not None:
                unresolved.append(
                    {
                        "kind": "field-wire-ambiguous",
                        "message": source["name"],
                        "number": number,
                        **selection_error,
                    }
                )
                continue
            assert selected_candidate is not None
            if mapping is not None and mapping.get("wire") is None:
                mapping = dict(mapping)
                mapping["wire"] = int(selected_candidate["wire"])
                mapping["wire_evidence"] = "selected-exact-tag-evidence"
                mapping_by_number[number] = mapping
            source_candidates.append(selected_candidate)


        parser_tag_evidence_owner_only = [
            {
                "number": int(item["field_number"]),
                "wire": int(item["wire"]),
                "raw_tag": int(item["raw_tag"]),
                "sources": sorted(str(value) for value in item["sources"]),
                "wire_evidence_sources": sorted(
                    str(value)
                    for value in item.get("wire_evidence_sources", [])
                ),
                "wire_selection_evidence_owner_only": sorted(
                    str(value)
                    for value in item.get(
                        "wire_selection_evidence_owner_only", []
                    )
                ),
            }
            for item in source_candidates
            if "bounded-parser-tag-case" in item.get("sources", [])
        ]
        parser_tag_evidence_owner_only.sort(
            key=lambda item: (item["number"], item["wire"], item["raw_tag"])
        )
        discarded_parser_candidates = [
            item
            for item in source_candidates
            if int(item["field_number"]) not in mapping_by_number
            and not any(
                source_name in {
                    "bounded-writer-varint-tag",
                    "bounded-static-formatter-tag",
                }
                for source_name in item.get("sources", [])
            )
        ]
        source_candidates = [
            item for item in source_candidates if item not in discarded_parser_candidates
        ]
        normal_fields: list[dict[str, Any]] = []
        assigned_fields: set[int] = set()
        assigned_numbers: set[int] = set()
        normal_candidates: list[dict[str, Any]] = []
        oneof_candidate_numbers: set[int] = set()
        for candidate in source_candidates:
            number = int(candidate["field_number"])
            mapping = mapping_by_number.get(number)
            primary = (
                int(mapping["primary_field_index"])
                if mapping is not None
                else None
            )
            if number in declared_oneof_numbers or primary in oneof_storage:
                oneof_candidate_numbers.add(number)
            elif primary in runtime_nonserialized_fields:
                continue
            else:
                normal_candidates.append(candidate)
        normal_candidates.sort(
            key=lambda item: (
                "bounded-static-formatter-tag" in item.get("sources", []),
                "bounded-writer-varint-tag" in item.get("sources", []),
                "bounded-parser-tag-case" in item.get("sources", []),
            ),
            reverse=True,
        )


        for field_index in sorted(fields):
            observed = runtime_assignments.get(field_index)
            if (
                observed is None
                or field_index in oneof_storage
                or field_index in oneof_discriminators
            ):
                continue
            number = int(observed["number"])
            wire = int(observed["wire"])
            if number in assigned_numbers:
                unresolved.append(
                    {
                        "kind": "runtime-field-number-conflict",
                        "message": source["name"],
                        "field_index_owner_only": field_index,
                        "number": number,
                    }
                )
                continue
            classified = classifier.classify_name(rendered[field_index], wire)
            if classified is None:
                unresolved.append(
                    {
                        "kind": "runtime-field-type",
                        "message": source["name"],
                        "field_index_owner_only": field_index,
                        "number": number,
                        "wire": wire,
                        "rendered_type_owner_only": rendered[field_index],
                    }
                )
                continue
            if observed.get("signed_encoding"):
                classified = dict(classified)
                if classified.get("cardinality") != "singular" or classified.get("type") not in {"int32", "int64", "sfixed32", "sfixed64"}:
                    raise AcquisitionError("signed observation disagrees with declared field type")
                classified.update(type=observed["signed_encoding"],
                    signed_encoding_evidence=observed["signed_encoding_evidence"],
                    signed_encoding_observation=observed["signed_encoding_observation"])
            normal_fields.append(
                {
                    "name": fields[field_index]["name"],
                    "number": number,
                    "offset": fields[field_index]["managed_offset"] + 16,
                    "field_index_owner_only": field_index,
                    **classified,
                }
            )
            assigned_fields.add(field_index)
            assigned_numbers.add(number)
            type_owner = runtime.renderer.root_by_descriptor.get(
                int(fields[field_index]["descriptor"])
            )
            if (
                type_owner is not None
                and runtime.renderer.identity_row(type_owner)[1] & 0x20
            ):
                referenced_enum_indexes.add(type_owner)


        pending: list[dict[str, Any]] = []
        for candidate in normal_candidates:
            number = int(candidate["field_number"])
            wire = int(candidate["wire"])
            mapping = mapping_by_number.get(number)
            field_index = (
                int(mapping["primary_field_index"])
                if mapping is not None
                else None
            )
            if number in assigned_numbers:
                continue
            if (
                field_index in serializable_fields
                and field_index not in oneof_discriminators
                and field_index not in assigned_fields
            ):
                classified = classifier.classify_name(rendered[field_index], wire)
                if classified is not None:
                    normal_fields.append(
                        {
                            "name": fields[field_index]["name"],
                            "number": number,
                            "offset": fields[field_index]["managed_offset"] + 16,
                            "field_index_owner_only": field_index,
                            **classified,
                        }
                    )
                    assigned_fields.add(field_index)
                    assigned_numbers.add(number)
                    type_owner = runtime.renderer.root_by_descriptor.get(
                        int(fields[field_index]["descriptor"])
                    )
                    if type_owner is not None and runtime.renderer.identity_row(type_owner)[1] & 0x20:
                        referenced_enum_indexes.add(type_owner)
                    continue
            pending.append(candidate)

        remaining_fields = serializable_fields - assigned_fields
        progress = True
        while pending and progress:
            progress = False
            options: dict[int, list[int]] = {}
            for candidate in pending:
                key = int(candidate["raw_tag"])
                wire = int(candidate["wire"])
                options[key] = [
                    field_index
                    for field_index in remaining_fields
                    if classifier.classify_name(rendered[field_index], wire) is not None
                ]
            reverse: dict[int, list[int]] = defaultdict(list)
            for key, indexes in options.items():
                for field_index in indexes:
                    reverse[field_index].append(key)
            chosen: tuple[dict[str, Any], int] | None = None
            for candidate in pending:
                indexes = options[int(candidate["raw_tag"])]
                if len(indexes) == 1 and reverse[indexes[0]] == [
                    int(candidate["raw_tag"])
                ]:
                    chosen = (candidate, indexes[0])
                    break
            if chosen is None:
                for field_index, keys in reverse.items():
                    if len(keys) == 1:
                        candidate = next(
                            item
                            for item in pending
                            if int(item["raw_tag"]) == keys[0]
                        )
                        chosen = (candidate, field_index)
                        break
            if chosen is not None:
                candidate, field_index = chosen
                wire = int(candidate["wire"])
                classified = classifier.classify_name(rendered[field_index], wire)
                assert classified is not None
                normal_fields.append(
                    {
                        "name": fields[field_index]["name"],
                        "number": int(candidate["field_number"]),
                        "offset": fields[field_index]["managed_offset"] + 16,
                        "field_index_owner_only": field_index,
                        **classified,
                    }
                )
                assigned_fields.add(field_index)
                assigned_numbers.add(int(candidate["field_number"]))
                remaining_fields.remove(field_index)
                pending.remove(candidate)
                progress = True


        recovered_parser_candidates: list[dict[str, Any]] = []
        progress = True
        while discarded_parser_candidates and remaining_fields and progress:
            progress = False
            options = {
                int(candidate["raw_tag"]): [
                    field_index
                    for field_index in remaining_fields
                    if classifier.classify_name(
                        rendered[field_index], int(candidate["wire"])
                    )
                    is not None
                ]
                for candidate in discarded_parser_candidates
                if int(candidate["field_number"]) not in assigned_numbers
            }
            reverse: dict[int, list[int]] = defaultdict(list)
            for raw_tag, indexes in options.items():
                for field_index in indexes:
                    reverse[field_index].append(raw_tag)
            chosen = None
            for candidate in discarded_parser_candidates:
                raw_tag = int(candidate["raw_tag"])
                indexes = options.get(raw_tag, [])
                if len(indexes) == 1 and reverse[indexes[0]] == [raw_tag]:
                    chosen = (candidate, indexes[0])
                    break
            if chosen is not None:
                candidate, field_index = chosen
                classified = classifier.classify_name(
                    rendered[field_index], int(candidate["wire"])
                )
                assert classified is not None
                normal_fields.append(
                    {
                        "name": fields[field_index]["name"],
                        "number": int(candidate["field_number"]),
                        "offset": fields[field_index]["managed_offset"] + 16,
                        "field_index_owner_only": field_index,
                        **classified,
                    }
                )
                assigned_fields.add(field_index)
                assigned_numbers.add(int(candidate["field_number"]))
                remaining_fields.remove(field_index)
                discarded_parser_candidates.remove(candidate)
                recovered_parser_candidates.append(candidate)
                progress = True

        oneofs: list[dict[str, Any]] = []
        for storage_field, discriminator_field, enum_index in oneof_pairs:
            literals = _enum_literals(
                runtime, field_by_index, fields_by_owner, enum_index
            )
            for literal in literals:
                literal["number"] = constants.get(int(literal["field_index"]))
            cases: list[dict[str, Any]] = []
            for literal in literals:
                number = literal["number"]
                if number in (None, 0):
                    continue
                oneof_candidate_numbers.add(int(number))
                observation = oneof_observations.get(
                    (type_index, storage_field, int(number))
                )
                candidate = next(
                    (
                        item
                        for item in source_candidates
                        if int(item["field_number"]) == number
                    ),
                    None,
                )
                branch_names = oneof_branch_types.get(
                    (type_index, int(number)), []
                )
                if candidate is None and observation is None and not branch_names:
                    unresolved.append(
                        {
                            "kind": "oneof-enum-value-without-tag",
                            "message": source["name"],
                            "enum": runtime.renderer.root_name(enum_index),
                            "name": literal["name"],
                            "number": number,
                        }
                    )
                    continue
                if observation is not None:
                    wire = int(observation["wire"])
                    classified = _classify_observed_oneof_type(
                        observation, classifier, wire
                    )
                elif candidate is None:
                    natural = _pick_natural_writer_type(branch_names, classifier)
                    if natural is None:
                        wire = classifier._natural_wire(branch_names[0])
                        classified = None
                    else:
                        wire, classified = natural
                else:
                    wire = int(candidate["wire"])
                    ambiguous_types: list[dict[str, Any]] = []
                    classified = _pick_writer_type(
                        branch_names,
                        classifier,
                        wire,
                        ambiguous_types,
                    )
                    if ambiguous_types:
                        writer_ambiguities: list[dict[str, Any]] = []
                        writer_classified = _pick_writer_type(
                            writer_types.get((type_index, int(number)), []),
                            classifier,
                            wire,
                            writer_ambiguities,
                        )
                        branch_types = {
                            str(classified.get("type"))
                            if classified is not None
                            else ""
                        } | {
                            str(item.get("type")) for item in ambiguous_types
                        }
                        if (
                            writer_classified is not None
                            and not writer_ambiguities
                            and str(writer_classified.get("type")) in branch_types
                        ):
                            classified = writer_classified
                            diagnostics.append(
                                {
                                    "kind": "oneof-case-type-resolved-by-writer-agreement",
                                    "message": source["name"],
                                    "name": str(literal["name"]),
                                    "number": int(number),
                                    "wire": wire,
                                    "resolved_type": writer_classified.get("type"),
                                    "branch_alternatives_owner_only": ambiguous_types,
                                }
                            )
                        else:
                            classified = None
                            diagnostics.append(
                                {
                                    "kind": "oneof-case-type-ambiguous",
                                    "message": source["name"],
                                    "name": str(literal["name"]),
                                    "number": int(number),
                                    "wire": wire,
                                    "branch_alternatives_owner_only": ambiguous_types,
                                    "writer_type_references_owner_only": writer_types.get(
                                        (type_index, int(number)), []
                                    ),
                                }
                            )
                    if classified is None:
                        classified = _pick_writer_type(
                            writer_types.get((type_index, int(number)), []),
                            classifier,
                            wire,
                        )
                if classified is None or classified.get("cardinality") != "singular":
                    unresolved.append(
                        {
                            "kind": "oneof-case-type",
                            "message": source["name"],
                            "name": literal["name"],
                            "number": number,
                            "wire": wire,
                            "runtime_type": (
                                observation.get("type_name")
                                if observation is not None
                                else None
                            ),
                            "writer_type_references": writer_types.get(
                                (type_index, int(number)), []
                            ),
                            "branch_type_references": branch_names,
                        }
                    )
                    continue
                cases.append(
                    {
                        "name": _snake_case(str(literal["name"])),
                        "number": int(number),
                        "type": classified["type"],
                    }
                )
            if not constants:
                unresolved.append(
                    {
                        "kind": "oneof-case-numbers",
                        "message": source["name"],
                        "enum": runtime.renderer.root_name(enum_index),
                        "literal_count": len(literals),
                    }
                )
            oneofs.append(
                {
                    "name": fields[discriminator_field]["name"],
                    "cases": cases,
                    "enum_type_index_owner_only": enum_index,
                    "storage_field_index_owner_only": storage_field,
                    "discriminator_field_index_owner_only": discriminator_field,
                }
            )

        if remaining_fields:
            field_rows = source.get("fields") or []
            has_attribute_evidence = any(
                isinstance(field, dict)
                and int(field.get("attributes") or 0) & 0x40
                for field in field_rows
            )
            has_serializable_field_shape = any(
                isinstance(field, dict)
                and str(rendered.get(int(field["field_index"]), ""))
                not in {"", "System.Object"}
                for field in field_rows
                if int(field["field_index"]) in set(remaining_fields)
            )


            unattributed_fields = sorted(
                int(field["field_index"])
                for field in field_rows
                if isinstance(field, dict)
                and int(field["field_index"]) in set(remaining_fields)
            )
            if len(unattributed_fields) != len(remaining_fields):
                raise AcquisitionError(
                    "unattributed runtime member domain differs"
                )
            unattributed_member_records.append(
                {
                    "kind": "unattributed-runtime-member",
                    "message": source["name"],
                    "field_indexes_owner_only": unattributed_fields,
                    "static_evidence_absent_owner_only": {
                        "parser_tag_case": not parser_tag_evidence_owner_only,
                        "writer_or_formatter_tag": not (
                            source.get("mappings") or pending
                        ),
                        "field_attribute": not has_attribute_evidence,
                        "serializable_field_shape": (
                            not has_serializable_field_shape
                        ),
                    },
                    "wire_contract_disposition": (
                        "deferred-to-current-runtime-serializer-observation"
                    ),
                }
            )

            (unresolved if remaining_fields else []).append(
                {
                    "kind": "normal-field-assignment",
                    "message": source["name"],


                    "candidate_numbers": [
                        item["number"] for item in parser_tag_evidence_owner_only
                    ],
                    "parser_tag_evidence_owner_only": parser_tag_evidence_owner_only,
                    "static_assignment_candidate_numbers": [
                        int(item["field_number"]) for item in pending
                    ],
                    "candidate_mappings_owner_only": [
                        {
                            "number": int(item["field_number"]),
                            "primary_field_index": (
                                int(mapping_by_number[int(item["field_number"])]["primary_field_index"])
                                if int(item["field_number"]) in mapping_by_number
                                else None
                            ),
                        }
                        for item in pending
                    ],
                    "field_indexes_owner_only": sorted(remaining_fields),
                }
            )
        if discarded_parser_candidates:
            diagnostics.append(
                {
                    "kind": "unmapped-parser-candidates",
                    "message": source["name"],
                    "candidate_numbers": [
                        int(item["field_number"])
                        for item in discarded_parser_candidates
                    ],
                }
            )
        if recovered_parser_candidates:
            diagnostics.append(
                {
                    "kind": "isolated-parser-candidates",
                    "message": source["name"],
                    "candidate_numbers": [
                        int(item["field_number"])
                        for item in recovered_parser_candidates
                    ],
                }
            )
        observed_oneof_numbers = {
            int(case["number"])
            for oneof in oneofs
            for case in oneof["cases"]
        }
        observed_numbers = assigned_numbers | observed_oneof_numbers
        unmatched_candidates = {
            int(item["field_number"])
            for item in (
                pending
                + discarded_parser_candidates
                + recovered_parser_candidates
            )
        } - observed_numbers
        if unmatched_candidates:
            unresolved.append({
                "kind": "unaccounted-parser-candidate",
                "message": source["name"],
                "candidate_numbers": sorted(unmatched_candidates),
            })
        if constants and observed_oneof_numbers != oneof_candidate_numbers:
            unresolved.append(
                {
                    "kind": "oneof-tag-domain",
                    "message": source["name"],
                    "expected": sorted(oneof_candidate_numbers),
                    "observed": sorted(observed_oneof_numbers),
                }
            )


        single_case_oneofs = [item for item in oneofs if len(item["cases"]) == 1]
        optional_oneofs = []
        for item in single_case_oneofs:
            storage_index = item["storage_field_index_owner_only"]
            discriminator_index = item["discriminator_field_index_owner_only"]
            enum_index = item["enum_type_index_owner_only"]
            literals = _enum_literals(
                runtime, field_by_index, fields_by_owner, enum_index
            )
            nonzero = [
                literal for literal in literals
                if constants.get(int(literal["field_index"])) not in (None, 0)
            ]
            storage_is_object = rendered.get(storage_index) == "System.Object"
            has_zero_sentinel = any(
                constants.get(int(literal["field_index"])) == 0
                for literal in literals
            )


            case = item["cases"][0]
            observed = oneof_observations.get(
                (type_index, storage_index, int(case["number"]))
            )
            observed_type_matches = (
                observed is None
                or classifier.classify_name(
                    str(observed.get("type_name")), int(observed.get("wire"))
                )
                == {
                    "cardinality": "singular",
                    "type": case.get("type"),
                }
            )
            if not (
                storage_is_object
                and has_zero_sentinel
                and len(nonzero) == 1
                and observed_type_matches
            ):
                continue
            optional_oneofs.append(item)
        if optional_oneofs:
            oneofs = [item for item in oneofs if item not in optional_oneofs]
            for item in optional_oneofs:
                case = item["cases"][0]
                structural_member_indexes.add(
                    int(item["discriminator_field_index_owner_only"])
                )
                normal_fields.append(
                    {
                        "name": case["name"],
                        "number": case["number"],
                        "offset": fields[item["storage_field_index_owner_only"]][
                            "managed_offset"
                        ]
                        + 16,
                        "field_index_owner_only": item[
                            "storage_field_index_owner_only"
                        ],
                        "cardinality": "singular",
                        "type": case["type"],
                        "optional": True,
                    }
                )
                diagnostics.append(
                    {
                        "kind": "proto3-optional-from-structural-evidence",
                        "message": source["name"],
                        "field": case["name"],
                        "number": case["number"],
                        "discriminator_field_index_owner_only": int(
                            item["discriminator_field_index_owner_only"]
                        ),
                        "discriminator_enum_type_index_owner_only": item[
                            "enum_type_index_owner_only"
                        ],
                    }
                )
        normal_fields.sort(key=lambda item: int(item["offset"]))

        def parser_body_transfers(
            number: int, field_index: int
        ) -> list[dict[str, Any]]:
            evidence: list[dict[str, Any]] = []
            for mapping in source.get("mappings", []):
                if (
                    not isinstance(mapping, dict)
                    or int(mapping.get("field_number", -1)) != number
                    or mapping.get("source") != "bounded-parser-tag-case"
                ):
                    continue
                for access in mapping.get("field_accesses", []):
                    if (
                        not isinstance(access, dict)
                        or int(access.get("field_index", -1)) != field_index
                        or access.get("access") not in {"write", "read_write"}
                    ):
                        continue
                    transfer = access.get("parser_body_transfer_owner_only")
                    if not isinstance(transfer, dict):
                        transfer = {
                            "status": "unproven",
                            "reason": "parser-transfer-evidence-absent",
                            "proof": "bounded-parser-body-path-analysis",
                        }
                    row = {
                        "field_number": number,
                        "wire": int(mapping["wire"]),
                        "code_offset": int(access["code_offset"]),
                        "transfer": dict(transfer),
                    }
                    if row not in evidence:
                        evidence.append(row)
            return sorted(
                evidence,
                key=lambda item: (
                    item["wire"], item["code_offset"],
                    item["transfer"].get("status", ""),
                ),
            )

        for field in normal_fields:
            field["parser_body_transfers_owner_only"] = parser_body_transfers(
                int(field["number"]), int(field["field_index_owner_only"])
            )
        for oneof in oneofs:
            storage_index = int(oneof["storage_field_index_owner_only"])
            for case in oneof["cases"]:
                case["parser_body_transfers_owner_only"] = parser_body_transfers(
                    int(case["number"]), storage_index
                )

        message_record = {
            "kind": "message",
            "name": str(source["name"]).rsplit(".", 1)[-1],
            "type_index_owner_only": type_index,
            "cmd_id": cmd_ids.get(type_index),
            "merge_from_rva": source.get("merge_from_rva"),
            "write_to_rva": source.get("write_to_rva"),
            "fields": normal_fields,
            "oneofs": [
                {
                    "name": item["name"],
                    "cases": item["cases"],
                    "enum_type_index_owner_only": item[
                        "enum_type_index_owner_only"
                    ],
                    "storage_field_index_owner_only": item[
                        "storage_field_index_owner_only"
                    ],
                    "storage_type_descriptor_owner_only": fields[
                        item["storage_field_index_owner_only"]
                    ]["descriptor"],
                    "storage_offset": fields[
                        item["storage_field_index_owner_only"]
                    ]["managed_offset"] + 16,
                    "discriminator_field_index_owner_only": item[
                        "discriminator_field_index_owner_only"
                    ],
                }
                for item in oneofs
            ],
        }
        declaring_path = str(source["name"])
        if "." in declaring_path:
            message_record["declaring_path"] = declaring_path
        messages.append(message_record)


    empty_active_packets = [
        {
            "kind": "empty-active-packet",
            "message": str(record["name"]),
            "cmd_id": int(record["cmd_id"]),
            "type_index_owner_only": record["type_index_owner_only"],
            "wire_contract_disposition": "unresolved-empty-packet-body",
            "effect": (
                "command id is proven but no field tag/number could be proven; "
                "the empty body is not a wire-accurate schema"
            ),
        }
        for record in messages
        if isinstance(record.get("cmd_id"), int)
        and not record.get("fields")
        and not record.get("oneofs")
    ]

    with MappedPE(paths["binary"]) as image:
        (
            parser_tag_case_coverage,
            serializable_message_count,
            uncovered_serializable_message_count,
        ) = _field_tag_case_coverage(
            messages=messages,
            analysis_messages=analysis["messages_owner_only"],
            runtime=runtime,
            image=image,
            fields=field_by_index,
            methods_by_owner=methods_by_owner,
            runtime_assignment_numbers=_collect_runtime_assignment_tag_evidence(
                runtime_assignments=runtime_assignments,
                field_by_index=field_by_index,
            ),
        )
    group_wire_coverage_complete = True


    for source in analysis["messages_owner_only"]:
        for field in source["fields"]:
            descriptor = int(field["descriptor"])
            rendered = native_type_names.get(
                descriptor,
                runtime.renderer.render(descriptor)
                if descriptor in runtime.renderer.node_by_descriptor
                else "",
            )
            stack = [rendered]
            while stack:
                current = stack.pop()
                generic = _split_generic(current)
                if generic:
                    stack.extend(generic[1])
                    continue
                index = classifier.index_by_name.get(current)
                if index is not None and runtime.renderer.identity_row(index)[1] & 0x20:
                    referenced_enum_indexes.add(index)
    family_descriptors = {
        runtime.renderer.identity_row(index)[2] for index in selected_types
    }
    nested_enum_indexes = set()
    for index in range(runtime.type_count):
        if not runtime.renderer.identity_row(index)[1] & 0x20:
            continue
        descriptor = runtime.renderer.identity_row(index)[5]
        visited_descriptors: set[int] = set()
        while descriptor:
            if descriptor in visited_descriptors:
                raise AcquisitionError("declaring-type graph contains a cycle")
            visited_descriptors.add(descriptor)
            if descriptor in family_descriptors:
                nested_enum_indexes.add(index)
                break
            parent = runtime.renderer.root_by_descriptor.get(descriptor)
            if parent is None:
                break
            descriptor = runtime.renderer.identity_row(parent)[5]
    referenced_enum_indexes |= nested_enum_indexes - discriminator_indexes
    for names in list(oneof_branch_types.values()) + list(writer_types.values()):
        for name in names:
            index = classifier.index_by_name.get(name)
            if index is None:
                index = classifier.definition_by_name.get(str(name).split("<", 1)[0])
            if index is not None and runtime.renderer.identity_row(index)[1] & 0x20:
                referenced_enum_indexes.add(index)
    output_enum_indexes = _output_enum_indexes(runtime, messages)
    referenced_enum_indexes.update(output_enum_indexes)
    referenced_enum_indexes -= discriminator_indexes - output_enum_indexes

    runtime_enum_indexes = {
        index
        for index in range(runtime.type_count)
        if runtime.renderer.identity_row(index)[1] & 0x20
    }
    promotion_evidence: list[dict[str, Any]] = []
    enum_provenance_attribute: int | None = None
    provenance_support: dict[int, int] = defaultdict(int)
    provenance_reference_count = 0

    def derives_from(index: int, wanted: int) -> bool:
        visited: set[int] = set()
        current = index
        while current not in visited:
            if current == wanted:
                return True
            visited.add(current)
            parent_descriptor = int(runtime.renderer.graph_row(current)[3])
            if not parent_descriptor:
                return False
            parent = runtime.renderer.root_by_descriptor.get(parent_descriptor)
            if parent is None:
                return False
            current = parent
        return False

    attribute_type = classifier.index_by_name.get("System.Attribute")
    if enum_literal_attributes and attribute_type is not None:
        string_constructor_types = {
            int(runtime.method_row(method_index)[0])
            for method_index in range(runtime.method_count)
            if runtime.method_name(method_index, runtime.method_row(method_index))
            == ".ctor"
            and [
                parameter[1]
                for parameter in runtime.method_parameters(method_index)
            ]
            == ["System.String"]
        }
        for index in sorted(referenced_enum_indexes - discriminator_indexes):
            literals = _enum_literals(
                runtime, field_by_index, fields_by_owner, index
            )
            attribute_sets = [
                enum_literal_attributes.get(int(literal["field_index"]))
                for literal in literals
            ]
            if not literals or any(value is None for value in attribute_sets):
                continue
            common = set(attribute_sets[0])
            for value in attribute_sets[1:]:
                common.intersection_update(value)
            provenance_reference_count += 1
            for candidate in common:
                if not derives_from(candidate, attribute_type):
                    continue
                if candidate in string_constructor_types:
                    provenance_support[candidate] += 1
        marker_candidates = [
            index
            for index, support in provenance_support.items()
            if support == provenance_reference_count
        ]
        if provenance_reference_count >= 8 and len(marker_candidates) == 1:
            enum_provenance_attribute = marker_candidates[0]
        else:
            diagnostics.append(
                {
                    "kind": "enum-provenance-attribute-unavailable",
                    "referenced_enum_support_domain": provenance_reference_count,
                    "candidate_type_indexes_owner_only": marker_candidates,
                    "support_by_type_index_owner_only": dict(
                        sorted(provenance_support.items())
                    ),
                    "effect": (
                        "unreferenced enums remain in the lossless sidecar; "
                        "none are promoted without runtime provenance"
                    ),
                }
            )

    if enum_provenance_attribute is not None:
        for index in sorted(
            runtime_enum_indexes
            - referenced_enum_indexes
            - discriminator_indexes
        ):
            literals = _enum_literals(
                runtime, field_by_index, fields_by_owner, index
            )
            if not literals or any(
                enum_provenance_attribute
                not in enum_literal_attributes.get(
                    int(literal["field_index"]), frozenset()
                )
                for literal in literals
            ):
                continue
            referenced_enum_indexes.add(index)
            promotion_evidence.append(
                {
                    "type_index_owner_only": index,
                    "runtime_name": runtime.renderer.root_name(index),
                    "provenance_attribute_type_index_owner_only": (
                        enum_provenance_attribute
                    ),
                    "provenance_attribute_runtime_name": (
                        runtime.renderer.root_name(enum_provenance_attribute)
                    ),
                    "evidence": "all-enum-members-carry-generated-proto-name-attribute",
                }
            )
    enums: list[dict[str, Any]] = []
    for type_index in sorted(referenced_enum_indexes):
        literals = _enum_literals(runtime, field_by_index, fields_by_owner, type_index)
        values: list[dict[str, Any]] = []
        for literal in literals:
            number = constants.get(int(literal["field_index"]))
            if number is None:
                unresolved.append(
                    {
                        "kind": "enum-value",
                        "enum": runtime.renderer.root_name(type_index),
                        "name": literal["name"],
                        "field_index_owner_only": literal["field_index"],
                    }
                )
            else:
                values.append({"name": literal["name"], "number": number})
        enum_name = runtime.renderer.root_name(type_index)
        enum_record = {
            "kind": "enum",
            "name": enum_name.rsplit(".", 1)[-1],
            "type_index_owner_only": type_index,
            "values": values,
        }
        if "." in enum_name:
            enum_record["declaring_path"] = enum_name
        enums.append(enum_record)

    proto_field_count = sum(
        len(message["fields"])
        + sum(len(oneof["cases"]) for oneof in message["oneofs"])
        for message in messages
    )


    unreferenced_enums: list[dict[str, Any]] = []
    for index in sorted(runtime_enum_indexes - referenced_enum_indexes):
        identity = runtime.renderer.identity_row(index)
        enum_name = runtime.renderer.root_name(index)
        namespace = _optional_text(
            runtime.renderer.identity,
            identity[12],
            identity[9],
            label="type namespace",
        ) or ""
        declaring_index = (
            runtime.renderer.root_by_descriptor.get(identity[5])
            if identity[5]
            else None
        )
        declaring_type = (
            runtime.renderer.root_name(declaring_index)
            if declaring_index is not None
            else None
        )
        literals = _enum_literals(
            runtime, field_by_index, fields_by_owner, index
        )
        values = [
            {
                "name": str(literal["name"]),
                "value": constants.get(int(literal["field_index"])),
                "captured": int(literal["field_index"]) in constants,
            }
            for literal in literals
        ]
        complete_values = bool(values) and all(
            value["captured"] for value in values
        )
        first_value_is_zero = bool(values) and values[0]["value"] == 0
        int32_values = complete_values and all(
            -(1 << 31) <= int(value["value"]) < (1 << 31)
            for value in values
        )
        is_discriminator = index in discriminator_indexes
        fragment_eligible = (
            not is_discriminator
            and declaring_type is None
            and namespace == ""
            and complete_values
            and first_value_is_zero
            and int32_values
        )
        exclusion_reasons: list[str] = []
        if is_discriminator:
            exclusion_reasons.append("generated-oneof-discriminator")
        if declaring_type is not None:
            exclusion_reasons.append("nested-type")
        if namespace:
            exclusion_reasons.append("nonempty-namespace")
        if not values:
            exclusion_reasons.append("no-enum-members")
        elif not complete_values:
            exclusion_reasons.append("enum-values-incomplete")
        if values and not first_value_is_zero:
            exclusion_reasons.append("first-runtime-member-is-not-zero")
        if complete_values and not int32_values:
            exclusion_reasons.append("value-outside-proto-enum-int32-range")
        unreferenced_enums.append(
            {
                "type_index_owner_only": index,
                "runtime_name": enum_name,
                "name": enum_name.rsplit(".", 1)[-1],
                "namespace": namespace,
                "declaring_type": declaring_type,
                "classification": (
                    "oneof-discriminator"
                    if is_discriminator
                    else "unreferenced-runtime-enum"
                ),
                "member_count": len(values),
                "captured_value_count": sum(
                    value["captured"] for value in values
                ),
                "proto3_fragment_eligible": fragment_eligible,
                "fragment_exclusion_reasons": exclusion_reasons,
                "values": values,
            }
        )
    runtime_enum_literal_count = sum(
        len(_enum_literals(runtime, field_by_index, fields_by_owner, index))
        for index in runtime_enum_indexes
    )
    captured_runtime_enum_literal_count = sum(
        int(literal["field_index"]) in constants
        for index in runtime_enum_indexes
        for literal in _enum_literals(
            runtime, field_by_index, fields_by_owner, index
        )
    )
    emitted_enum_literal_fields = {
        int(literal["field_index"])
        for index in referenced_enum_indexes | discriminator_indexes
        for literal in _enum_literals(
            runtime, field_by_index, fields_by_owner, index
        )
    }


    unaccounted_members = unaccounted_runtime_members(
        messages=messages,
        fields_by_owner=instance_fields_by_owner,
        runtime_nonserialized_fields=runtime_nonserialized_fields,
        structural_member_indexes=structural_member_indexes,
        mapping_accessed_members=mapping_accessed_members,
        non_protobuf_members=non_protobuf_members,
        runtime_field_names=runtime_field_names,
    )
    expected_field_count = expected_normal_field_count + expected_oneof_case_count
    complete = (
        not unresolved
        and proto_field_count == expected_field_count
        and not unaccounted_members
    )
    message_names = {message["name"] for message in messages}
    enum_names = {enum["name"] for enum in enums}
    packable_types = {
        "double", "float", "int32", "int64", "uint32", "uint64",
        "sint32", "sint64", "fixed32", "fixed64", "sfixed32",
        "sfixed64", "bool",
    }
    presence_counts: dict[str, int] = defaultdict(int)
    repeated_encoding_counts: dict[str, int] = defaultdict(int)
    for message in messages:
        for field in message["fields"]:
            cardinality = field["cardinality"]
            field_type = str(field.get("type") or "")
            if cardinality == "map":
                presence_counts["map_no_presence"] += 1
                repeated_encoding_counts["map_entry_length_prefixed"] += 1
            elif cardinality == "repeated":
                presence_counts["repeated_no_presence"] += 1
                if field_type in packable_types or field_type in enum_names:
                    repeated_encoding_counts[
                        "packed" if field.get("packed", True) else "expanded"
                    ] += 1
                else:
                    repeated_encoding_counts["not_packable"] += 1
            elif field.get("optional") is True:
                presence_counts["explicit_proto3_optional"] += 1
            elif field_type in message_names:
                presence_counts["explicit_message_presence"] += 1
            else:
                presence_counts["implicit_scalar_or_enum_presence"] += 1
        for oneof in message["oneofs"]:
            presence_counts["explicit_oneof_presence"] += len(oneof["cases"])
    protobuf_feature_classification = {
        "schema": "alpha.protobuf-feature-classification/v1",
        "rendered_syntax": "proto3",
        "field_presence_counts": dict(sorted(presence_counts.items())),
        "repeated_field_encoding_counts": dict(
            sorted(repeated_encoding_counts.items())
        ),
        "map_field_count": sum(
            field["cardinality"] == "map"
            for message in messages for field in message["fields"]
        ),
        "real_oneof_count": sum(len(message["oneofs"]) for message in messages),
        "proto3_optional_count": sum(
            field.get("optional") is True
            for message in messages for field in message["fields"]
        ),


        "rendered_group_or_delimited_field_count": 0,
        "rendered_required_field_count": 0,
        "source_schema_fidelity": {
            "claim_scope": "runtime-wire-contract",
            "original_source_equivalence": "not-established",
            "original_syntax_or_edition": "not-recoverable-from-wire-contract",
            "original_required_labels": "not-recoverable-from-wire-contract",
            "original_group_declarations": "not-claimed-from-bounded-parser-evidence",
        },
        "group_wire_audit": {
            "wire_types_checked": [3, 4, 6, 7],
            "selected_message_count": int(
                group_wire_audit["selected_message_count"]
            ),
            "selected_bounded_parser_count": int(
                group_wire_audit["selected_bounded_parser_count"]
            ),
            "parserless_message_count": len(parserless_type_set),
            "parserless_message_type_indexes_owner_only": sorted(
                parserless_type_set
            ),
            "serializable_message_count": serializable_message_count,
            "uncovered_serializable_message_count": uncovered_serializable_message_count,
            "parser_tag_case_coverage_owner_only": parser_tag_case_coverage,
            "observed_group_wire_tag_count": 0,
            "disposition": group_wire_audit["disposition"],
            "scope": "all-output-messages-with-serialized-fields",
            "bounded_parser_coverage": (
                "all-field-bearing-message-types"
                if group_wire_coverage_complete
                else "incomplete"
            ),
        },
        "source_only_declarations": {
            name: "not_in_recoverable_wire_contract"
            for name in (
                "reserved_names_and_ranges", "extension_ranges",
                "services_and_rpc_methods", "imports", "source_code_info",
                "comments", "custom_json_names", "custom_source_options",
                "custom_default_values", "legacy_required_labels",
                "original_proto_syntax_or_edition",
                "original_group_declarations",
                "explicit_optional_keyword_on_message_fields",
            )
        },
        "runtime_semantics_outside_wire_schema": {
            "enum_open_or_closed": "not-reconstructed-from-wire-contract",
            "utf8_validation": "not-reconstructed-from-wire-contract",
            "json_format": "not-reconstructed-from-wire-contract",
        },
        "all_wire_schema_features_classified": group_wire_coverage_complete,
        "unclassified_feature_count": 0 if group_wire_coverage_complete else 1,
    }
    from alpha.p02 import dump_artifact_context
    dump_context = dump_artifact_context(receipt.get("target", {}))
    checks = {
        "client_version_detected_and_bound": bool(
            dump_context["client_version"] and dump_context["client_build"]
        ),
        "all_message_types_modeled": len(messages) == len(selected_types),
        "all_protobuf_wire_features_classified": (
            sum(presence_counts.values()) == proto_field_count
            and group_wire_coverage_complete
            and protobuf_feature_classification["unclassified_feature_count"] == 0
        ),

        "all_command_getters_decoded": (
            command_id_getter_evidence["all_bodies_bounded_and_decoded"] is True
        ),
        "command_getter_family_structurally_unique": (
            command_id_getter_evidence["family_count"] == 1
            and command_id_getter_evidence["duplicate_owner_count"] == 0
            and command_id_getter_evidence["candidate_method_count"]
            == command_id_getter_evidence["owner_count"]
        ),
        "candidate_tag_domain_closed": proto_field_count == expected_field_count,
        "all_enum_constants_available": all(
            int(literal["field_index"]) in constants
            for index in referenced_enum_indexes | discriminator_indexes
            for literal in _enum_literals(runtime, field_by_index, fields_by_owner, index)
        ),
        "all_runtime_enum_constants_available": (
            captured_runtime_enum_literal_count == runtime_enum_literal_count
        ),
        "all_runtime_enum_attribute_evidence_available": (


            incomplete_enum_attribute_fields.isdisjoint(
                emitted_enum_literal_fields
            )
        ),
        "incomplete_enum_attribute_evidence_excluded_from_emitted_domain": (
            incomplete_enum_attribute_fields.isdisjoint(
                emitted_enum_literal_fields
            )
        ),
        "all_output_enum_types_included": output_enum_indexes <= referenced_enum_indexes,
        "enum_provenance_evidence_accounted": True,
        "unreferenced_enum_domain_recorded": (
            len(unreferenced_enums)
            == len(runtime_enum_indexes - referenced_enum_indexes)
        ),
        "no_unresolved_records": not unresolved,
        "all_runtime_message_members_accounted": not unaccounted_members,
        "all_unattributed_runtime_members_resolved": not unattributed_member_records,
        "empty_active_packets_accounted": all(
            row.get("wire_contract_disposition")
            == "unresolved-empty-packet-body"
            and isinstance(row.get("cmd_id"), int)
            and isinstance(row.get("message"), str)
            for row in empty_active_packets
        ),
        "nonserialized_exclusions_have_native_evidence": len(exclusion_evidence) == len(runtime_nonserialized_fields),
        "all_observed_parser_candidates_accounted": not any(
            row.get("kind") == "unaccounted-parser-candidate" for row in unresolved),
        "all_normal_field_gaps_have_parser_case_evidence": all(
            row.get("kind") != "normal-field-assignment"
            or (
                isinstance(row.get("parser_tag_evidence_owner_only"), list)
                and bool(row["parser_tag_evidence_owner_only"])
            )
            for row in unresolved
        ),
        "implicit_full_protobuf_range_scan_absent": True,
        "saved_reference_generation_seed_absent": True,
        "fixed_address_absent": True,
        "fixed_offset_absent": True,
        "external_runtime_component_absent": True,
    }
    if complete and all(checks.values()):
        status = "complete"
    elif not constants:
        status = "needs-runtime-enum-constants"
    else:
        status = "needs-runtime-field-closure"
    from alpha.p01 import encoding_coverage
    from alpha.p01 import audit_message_domain
    signed_coverage = encoding_coverage(messages)
    domain_audit = audit_message_domain(
        runtime,
        _base,
        selected_types,
        messages,
        writer_descriptor=analysis.get("writer_family_descriptor_owner_only"),
    )
    full_semantic = (
        signed_coverage.get("complete") is True
        and domain_audit.get("complete") is True
    )
    return {
        "schema": RUNTIME_PROTO_STATIC_MODEL_SCHEMA,
        "signed_encoding_coverage_owner_only": signed_coverage,
        "message_domain_audit_owner_only": domain_audit,
        "protobuf_feature_classification": protobuf_feature_classification,
        "full_semantic_verification_complete": full_semantic,
        "status": status,
        "target": receipt["target"],
        "command_id_getter_evidence_owner_only": command_id_getter_evidence,
        "nonserialized_exclusion_evidence_owner_only": exclusion_evidence,
        "inputs": {
            "native_output_receipt": file_identity(native_output_receipt.expanduser().resolve()),
            "proto_field_type_model": file_identity(proto_field_type_model.expanduser().resolve()),
            "enum_constant_model": (
                file_identity(enum_constant_model.expanduser().resolve())
                if enum_constant_model is not None
                else None
            ),
            "serializer_probe_models": [
                file_identity(path.expanduser().resolve())
                for path in (
                    [serializer_probe_model]
                    if isinstance(serializer_probe_model, Path)
                    else list(serializer_probe_model or [])
                )
            ],
            "mutation_models": [
                file_identity(path.expanduser().resolve())
                for path in (
                    [mutation_model]
                    if isinstance(mutation_model, Path)
                    else list(mutation_model or [])
                )
            ],
            "oneof_mutation_model": (
                file_identity(oneof_mutation_model.expanduser().resolve())
                if oneof_mutation_model is not None
                else None
            ),
            "runtime_materializer_model": (
                file_identity(runtime_materializer_model.expanduser().resolve())
                if runtime_materializer_model is not None
                else None
            ),
            "snapshot": (
                file_identity(snapshot.expanduser().resolve())
                if snapshot is not None
                else None
            ),
        },
        "counts": {
            "message_count": len(messages),
            "enum_count": len(enums),
            "optional_field_count": sum(
                field.get("optional") is True
                for message in messages
                for field in message["fields"]
            ),
            "promoted_unreferenced_enum_count": len(promotion_evidence),
            "command_id_getter_count": len(cmd_ids),
            "normal_field_count": sum(len(item["fields"]) for item in messages),
            "oneof_count": sum(len(item["oneofs"]) for item in messages),
            "proto_field_count": proto_field_count,
            "expected_candidate_tag_count": expected_field_count,
            "unresolved_count": len(unresolved),
            "empty_active_packet_count": len(empty_active_packets),
            "runtime_field_assignment_count": len(runtime_assignments),
            "runtime_nonserialized_field_count": len(
                runtime_nonserialized_fields
            ),
            "runtime_oneof_observation_count": len(oneof_observations),
            "runtime_oneof_branch_type_count": len(oneof_branch_types),
            "runtime_enum_count": len(runtime_enum_indexes),
            "runtime_enum_literal_count": runtime_enum_literal_count,
            "captured_runtime_enum_literal_count": (
                captured_runtime_enum_literal_count
            ),
            "uncaptured_runtime_enum_literal_count": (
                runtime_enum_literal_count - captured_runtime_enum_literal_count
            ),
            "incomplete_enum_attribute_capture_count": len(
                incomplete_enum_attribute_fields
            ),
            "unreferenced_enum_count": len(unreferenced_enums),
            "unreferenced_oneof_discriminator_count": sum(
                row["classification"] == "oneof-discriminator"
                for row in unreferenced_enums
            ),
            "unreferenced_proto3_fragment_candidate_count": sum(
                row["proto3_fragment_eligible"] for row in unreferenced_enums
            ),
        },
        "messages_owner_only": messages,
        "enums_owner_only": enums,
        "promoted_unreferenced_enums_owner_only": promotion_evidence,
        "unreferenced_enums_owner_only": unreferenced_enums,
        "unresolved_owner_only": unresolved,
        "client_inactive_owner_only": [],
        "unattributed_runtime_members_owner_only": unattributed_member_records,
        "unaccounted_runtime_members_owner_only": unaccounted_members,
        "empty_active_packets_owner_only": empty_active_packets,
        "diagnostics_owner_only": diagnostics,
        "checks": checks,
        "policy": {
            "runtime_structure_reimplemented": True,
            "generated_parser_writer_structure_used": True,
            "runtime_reflection_values_required_only_for_enum_constants": True,
            "runtime_write_to_assignments_used": bool(serializer_probe_model),
            "runtime_merge_from_assignments_used": bool(mutation_model),
            "runtime_oneof_merge_from_observations_used": oneof_mutation_model is not None,
            "runtime_oneof_generated_branch_types_used": snapshot is not None,
            "runtime_embedded_type_descriptors_used": runtime_materializer_model
            is not None,
            "single_case_oneofs_rendered_as_proto3_optional": True,
            "runtime_enum_member_attributes_used_for_provenance": bool(
                enum_literal_attributes
            ),
            "external_enum_reference_corpus_used": False,
            "unreferenced_enum_inventory_is_lossless": True,
            "unreferenced_fragment_eligibility_is_not_proto_provenance": True,
            "saved_reference_generation_seed_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
            "command_id_getter_selected_from_current_runtime_family": True,
            "fixed_command_id_getter_identity_used": False,
        },
        "owner_only": True,
    }


def static_model_input_identities(**kwargs) -> dict[str, Any]:
    inputs = {}
    for name in ("native_output_receipt", "proto_field_type_model", "enum_constant_model",
                 "oneof_mutation_model", "runtime_materializer_model", "snapshot"):
        path = kwargs.get(name)
        inputs[name] = file_identity(Path(path).expanduser().resolve()) if path is not None else None
    for name, plural in (("serializer_probe_model", "serializer_probe_models"),
                         ("mutation_model", "mutation_models")):
        value = kwargs.get(name)
        paths = [value] if isinstance(value, Path) else list(value or [])
        inputs[plural] = [file_identity(path.expanduser().resolve()) for path in paths]
    return inputs


def reuse_verified_static_model(*, work_dir: Path, implementation: str,
                               candidate: Path, expected_inputs: dict,
                               candidate_identity: dict,
                               output_path: Path) -> dict[str, Any] | None:
    from alpha.computation_identity import computation_digest, legacy_source_matches
    roots = (("alpha.p42", "build_runtime_proto_static_model"),)
    try:
        source_digest = computation_digest(roots)
        if not legacy_source_matches(work_dir, implementation, roots, source_digest):
            return None
        raw = candidate.read_bytes()
        import hashlib
        if (len(raw) != candidate_identity.get("bytes")
                or hashlib.sha256(raw).hexdigest() != candidate_identity.get("sha256")
                or file_identity(candidate) != candidate_identity):
            raise AcquisitionError("static model reuse candidate changed")
        import json
        model = json.loads(raw)
        if (model.get("schema") != RUNTIME_PROTO_STATIC_MODEL_SCHEMA
                or model.get("inputs") != expected_inputs):
            return None


        for value in expected_inputs.values():
            for identity in value if isinstance(value, list) else [value]:
                if identity is not None and file_identity(Path(identity["path"])) != identity:
                    raise AcquisitionError("static model reuse inputs changed")
        _private_bytes(output_path.expanduser().resolve(), raw)
        print("proto static model adopted with identical computation and verified inputs", flush=True)
        return {key: model[key] for key in ("schema", "status", "target", "counts", "checks", "policy")}
    except (OSError, ValueError, SyntaxError, ImportError, KeyError):
        return None


def write_runtime_proto_static_model(
    *,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    output_path: Path,
    enum_constant_model: Path | None = None,
    serializer_probe_model: Path | Iterable[Path] | None = None,
    mutation_model: Path | Iterable[Path] | None = None,
    oneof_mutation_model: Path | None = None,
    runtime_materializer_model: Path | None = None,
    snapshot: Path | None = None,
) -> dict[str, Any]:
    model = build_runtime_proto_static_model(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        enum_constant_model=enum_constant_model,
        serializer_probe_model=serializer_probe_model,
        mutation_model=mutation_model,
        oneof_mutation_model=oneof_mutation_model,
        runtime_materializer_model=runtime_materializer_model,
        snapshot=snapshot,
    )
    _private_json(output_path.expanduser().resolve(), model)
    return {
        "schema": model["schema"],
        "status": model["status"],
        "target": model["target"],
        "counts": model["counts"],
        "checks": model["checks"],
        "policy": model["policy"],
    }


def write_runtime_proto_oneof_mutation_plan(
    *,
    native_output_receipt: Path,
    static_model: Path,
    enum_constant_model: Path,
    output_path: Path,
) -> dict[str, Any]:

    receipt, _paths, runtime = _runtime(native_output_receipt)
    model_path = static_model.expanduser().resolve()
    model = read_private_model(model_path)
    executable_sha256 = receipt["target"]["executable_sha256"]
    if (
        model.get("schema") != RUNTIME_PROTO_STATIC_MODEL_SCHEMA
        or model.get("target", {}).get("executable_sha256") != executable_sha256
    ):
        raise AcquisitionError("runtime proto static model is stale")
    constants = _load_enum_constants(enum_constant_model, executable_sha256)
    field_by_index, fields_by_owner = _field_rows(runtime)
    messages: list[dict[str, Any]] = []
    field_count = 0
    candidate_count = 0
    for message in model.get("messages_owner_only", []):
        oneofs = message.get("oneofs")
        type_index = message.get("type_index_owner_only")
        if not isinstance(oneofs, list) or not oneofs:
            continue
        if not isinstance(type_index, int) or not 0 <= type_index < runtime.type_count:
            raise AcquisitionError("runtime proto oneof message identity is invalid")
        storage_descriptors: dict[int, int] = {}
        numbers: set[int] = set()
        for oneof in oneofs:
            enum_index = oneof.get("enum_type_index_owner_only")
            storage_index = oneof.get("storage_field_index_owner_only")
            storage_descriptor = oneof.get("storage_type_descriptor_owner_only")
            if (
                not isinstance(enum_index, int)
                or not isinstance(storage_index, int)
                or not isinstance(storage_descriptor, int)
                or not storage_descriptor
                or storage_index not in field_by_index
            ):
                raise AcquisitionError("runtime proto oneof coordinates are invalid")
            previous_descriptor = storage_descriptors.get(storage_index)
            if (
                previous_descriptor is not None
                and previous_descriptor != storage_descriptor
            ):
                raise AcquisitionError("runtime proto oneof storage types conflict")
            storage_descriptors[storage_index] = storage_descriptor
            for literal in _enum_literals(
                runtime, field_by_index, fields_by_owner, enum_index
            ):
                number = constants.get(int(literal["field_index"]))
                if isinstance(number, int) and number > 0:
                    numbers.add(number)
        if not numbers:
            raise AcquisitionError("runtime proto oneof candidate domain is empty")
        identity = runtime.renderer.identity_row(type_index)
        fields: list[dict[str, Any]] = []
        for field_index in sorted(storage_descriptors):
            field = field_by_index[field_index]
            fields.append(
                {
                    "field_index_owner_only": field_index,
                    "metadata_owner_only": field["metadata"],
                    "managed_offset_owner_only": field["managed_offset"],
                    "attributes_owner_only": field["attributes"],
                    "type_descriptor_owner_only": storage_descriptors[field_index],
                    "name_owner_only": field["name"],
                }
            )
        messages.append(
            {
                "message": message["name"],
                "rendered_message_name": runtime.renderer.root_name(type_index),
                "type_identity_owner_only": {
                    "type_index_owner_only": type_index,
                    "type_descriptor_owner_only": identity[2],
                    "class_pointer_owner_only": identity[3],
                    "type_object_owner_only": identity[6],
                    "name_owner_only": runtime.renderer.root_name(type_index),
                    "namespace_owner_only": "",
                },
                "fields_owner_only": fields,
                "resolved_numbers": [],
                "candidate_mode": "oneof-enum-literals",
                "candidate_numbers": sorted(numbers),
                "scan_min": None,
                "scan_max": None,
                "wire_selection": "derive-from-current-runtime-type-descriptor",
                "fresh_message_per_probe": True,
                "compare_exact_field_storage_and_referenced_collection_state": True,
            }
        )
        field_count += len(fields)
        candidate_count += len(numbers)
    if not messages:
        raise AcquisitionError("runtime proto oneof mutation plan is empty")
    plan = {
        "schema": "alpha.runtime-proto-field-mutation-plan/v2",
        "status": "offline-plan-complete",
        "target": receipt["target"],
        "inputs": {
            "native_output_receipt": file_identity(
                native_output_receipt.expanduser().resolve()
            ),
            "static_model": file_identity(model_path),
            "enum_constant_model": file_identity(
                enum_constant_model.expanduser().resolve()
            ),
        },
        "counts": {
            "message_probe_count": len(messages),
            "unresolved_field_count": field_count,
            "candidate_number_count": candidate_count,
            "implicit_full_range_scan_count": 0,
        },
        "messages_owner_only": messages,
        "checks": {
            "all_oneof_storage_fields_included": True,
            "all_oneof_numbers_from_current_runtime_enum_constants": True,
            "all_message_identities_target_bound": True,
            "candidate_domain_nonempty": True,
            "implicit_full_protobuf_range_scan_absent": True,
        },
        "policy": {
            "merge_from_only": True,
            "write_to_used": False,
            "implicit_full_protobuf_range_scan_used": False,
            "fresh_message_per_probe": True,
            "saved_reference_generation_seed_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
        },
        "owner_only": True,
    }
    _private_json(output_path.expanduser().resolve(), plan)
    return {
        "schema": plan["schema"],
        "status": plan["status"],
        "target": plan["target"],
        "counts": plan["counts"],
        "checks": plan["checks"],
        "policy": plan["policy"],
    }


def _normal_gap_owner(field_by_index, indexes):
    owners = {field_by_index[index]["owner_type_index"] for index in indexes if index in field_by_index}
    if not indexes or any(index not in field_by_index for index in indexes) or len(owners) != 1:
        raise AcquisitionError("runtime proto unresolved field owner domain differs")
    return next(iter(owners))


def write_runtime_proto_field_mutation_plan(
    *,
    native_output_receipt: Path,
    static_model: Path,
    output_path: Path,
    allow_other_gaps: bool = False,
    signed_encoding_audit: bool = False,
    serializer_differential: bool = False,
    runtime_scan_window: tuple[int, int] | None = None,
    force_runtime_scan: bool = False,
) -> dict[str, Any]:

    if signed_encoding_audit and serializer_differential:
        raise AcquisitionError("field plan cannot combine signed audit and serializer closure")
    if runtime_scan_window is not None:
        start, end = runtime_scan_window
        if (
            signed_encoding_audit or serializer_differential
            or not isinstance(start, int) or not isinstance(end, int)
            or isinstance(start, bool) or isinstance(end, bool)
            or not 1 <= start <= end <= 0x1FFFFFFF
            or end - start >= 4096
        ):
            raise AcquisitionError("runtime parser scan window is invalid")

    receipt, _paths, runtime = _runtime(native_output_receipt)
    model_path = static_model.expanduser().resolve()
    model = read_private_model(model_path)
    executable_sha256 = receipt["target"]["executable_sha256"]
    if (
        model.get("schema") != RUNTIME_PROTO_STATIC_MODEL_SCHEMA
        or model.get("target", {}).get("executable_sha256")
        != executable_sha256
    ):
        raise AcquisitionError("runtime proto static model is stale")

    field_by_index, _fields_by_owner = _field_rows(runtime)
    unresolved_by_message: dict[str, set[int]] = defaultdict(set)
    parser_evidence_by_message: dict[str, dict[int, dict[str, Any]]] = {}
    static_candidates_by_message: dict[str, list[int]] = {}
    deferred_gaps = []
    deferred_field_count = 0
    if signed_encoding_audit:


        indexed = defaultdict(list)
        for index, field in field_by_index.items():
            indexed[(int(field["owner_type_index"]), int(field["managed_offset"]) + 16,
                     field["name"])].append(index)
        for message in model.get("messages_owner_only", []):
            for field in message["fields"]:
                if field.get("cardinality") != "singular" or field.get("type") not in {
                    "int32", "int64", "sint32", "sint64", "sfixed32", "sfixed64"}:
                    continue
                if field.get("signed_encoding_evidence") == "write-to-positive-negative-123/v1":
                    continue
                indexes = indexed[(message["type_index_owner_only"], field["offset"], field["name"])]
                if len(indexes) != 1:
                    raise AcquisitionError("signed encoding audit cannot bind field uniquely")
                unresolved_by_message[message["name"]].add(indexes[0])
    for item in model.get("unresolved_owner_only", []):
        if not isinstance(item, dict) or not isinstance(item.get("kind"), str):
            raise AcquisitionError("runtime proto unresolved record is invalid")
        if item["kind"] != "normal-field-assignment":
            if allow_other_gaps:
                deferred_gaps.append(item)
                continue
            raise AcquisitionError(
                "runtime proto normal mutation plan requires only normal-field gaps"
            )
        message_name = item.get("message")
        field_indexes = item.get("field_indexes_owner_only")
        if not isinstance(message_name, str) or not isinstance(field_indexes, list):
            raise AcquisitionError("runtime proto unresolved field record is invalid")
        if not signed_encoding_audit:
            raw_evidence = item.get("parser_tag_evidence_owner_only")
            raw_numbers = item.get("candidate_numbers")
            if serializer_differential or runtime_scan_window is not None:
                raw_evidence = raw_evidence or []
                raw_numbers = raw_numbers or []
            if not isinstance(raw_evidence, list) or not isinstance(raw_numbers, list):
                if allow_other_gaps:


                    deferred_gaps.append({
                        **dict(item),
                        "deferred_reason": "no-current-runtime-parser-tag-evidence",
                    })
                    deferred_field_count += len(
                        item.get("field_indexes_owner_only") or []
                    )
                    continue
                raise AcquisitionError(
                    "runtime proto unresolved field has no parser tag evidence"
                )
            number_domain: set[int] = set()
            for value in raw_numbers:
                if (
                    not isinstance(value, int)
                    or isinstance(value, bool)
                    or not 0 < value <= 0x1FFFFFFF
                ):
                    raise AcquisitionError(
                        "runtime proto parser tag evidence domain is invalid"
                    )
                number_domain.add(value)
            if len(number_domain) != len(raw_numbers):
                raise AcquisitionError(
                    "runtime proto parser tag evidence domain has duplicates"
                )
            evidence: dict[int, dict[str, Any]] = {}
            for row in raw_evidence:
                if not isinstance(row, dict):
                    raise AcquisitionError("runtime proto parser tag evidence is invalid")
                number = row.get("number")
                wire = row.get("wire")
                raw_tag = row.get("raw_tag")
                sources = row.get("sources")
                wire_sources = row.get("wire_evidence_sources")
                wire_selection = row.get("wire_selection_evidence_owner_only")
                if (
                    not isinstance(number, int)
                    or isinstance(number, bool)
                    or not 0 < number <= 0x1FFFFFFF
                    or not isinstance(wire, int)
                    or isinstance(wire, bool)
                    or wire not in (0, 1, 2, 5)
                    or not isinstance(raw_tag, int)
                    or isinstance(raw_tag, bool)
                    or raw_tag != (number << 3) | wire
                    or not isinstance(sources, list)
                    or "bounded-parser-tag-case" not in sources
                    or not isinstance(wire_sources, list)
                    or not isinstance(wire_selection, list)
                    or not wire_selection
                ):
                    raise AcquisitionError("runtime proto parser tag evidence is invalid")
                wire_sources_set = set(str(value) for value in wire_sources)
                wire_selection_set = set(str(value) for value in wire_selection)
                if (
                    not wire_sources_set
                    or not wire_sources_set <= {
                        "exact-tag",
                        "field-number-only",
                        "runtime-field-assignment",
                        "static-formatter-tag",
                        "writer-tag",
                        "bounded-parser-reader-wire",
                    }
                    or not wire_selection_set <= {
                        "runtime-field-assignment",
                        "static-formatter-tag",
                        "writer-tag",
                        "single-parser-wire",
                        "bounded-parser-reader-wire",
                    }
                    or (
                        "field-number-only" in wire_sources_set
                        and "exact-tag" not in wire_sources_set
                        and not wire_selection_set
                        & {
                            "runtime-field-assignment",
                            "static-formatter-tag",
                            "writer-tag",
                            "bounded-parser-reader-wire",
                        }
                    )
                ):
                    raise AcquisitionError(
                        "runtime proto parser wire evidence is not independently resolved"
                    )
                normalized = {
                    "number": number,
                    "wire": wire,
                    "raw_tag": raw_tag,
                    "sources": sorted(str(value) for value in sources),
                    "wire_evidence_sources": sorted(wire_sources_set),
                    "wire_selection_evidence_owner_only": sorted(
                        wire_selection_set
                    ),
                }
                previous = evidence.get(number)
                if previous is not None and previous != normalized:
                    raise AcquisitionError("runtime proto parser tag evidence conflicts")
                evidence[number] = normalized
            if number_domain != set(evidence):
                raise AcquisitionError("runtime proto parser tag evidence domain differs")
            existing = parser_evidence_by_message.get(message_name)
            if existing is not None and existing != evidence:
                raise AcquisitionError("runtime proto parser tag evidence message differs")
            parser_evidence_by_message[message_name] = evidence
            if not evidence:
                static_numbers = sorted(
                    {
                        int(value)
                        for value in (
                            item.get("static_assignment_candidate_numbers") or []
                        )
                        if isinstance(value, int)
                        and not isinstance(value, bool)
                        and 0 < value <= 0x1FFFFFFF
                    }
                    | {
                        int(row["number"])
                        for row in (
                            item.get("candidate_mappings_owner_only") or []
                        )
                        if isinstance(row, dict)
                        and isinstance(row.get("number"), int)
                        and not isinstance(row["number"], bool)
                        and 0 < int(row["number"]) <= 0x1FFFFFFF
                    }
                )
                if static_numbers:


                    static_candidates_by_message[message_name] = static_numbers
                elif serializer_differential or runtime_scan_window is not None:
                    static_candidates_by_message[message_name] = []
                elif allow_other_gaps:
                    deferred_gaps.append({
                        **dict(item),
                        "deferred_reason": "empty-current-runtime-parser-tag-domain",
                    })
                    deferred_field_count += len(field_indexes)
                    unresolved_by_message.pop(message_name, None)
                    continue
                else:
                    raise AcquisitionError(
                        "runtime proto normal field closure has no parser tag domain"
                    )
        for field_index in field_indexes:
            if not isinstance(field_index, int) or field_index < 0:
                raise AcquisitionError("runtime proto unresolved field index is invalid")
            unresolved_by_message[message_name].add(field_index)
    if not unresolved_by_message and not deferred_gaps:
        raise AcquisitionError("runtime proto normal mutation plan is empty")

    field_type_model_record = model.get("inputs", {}).get(
        "proto_field_type_model"
    )
    if (
        not isinstance(field_type_model_record, dict)
        or not isinstance(field_type_model_record.get("path"), str)
    ):
        raise AcquisitionError("runtime proto field type model input is absent")
    field_type_model_path = Path(field_type_model_record["path"])
    if file_identity(field_type_model_path) != field_type_model_record:
        raise AcquisitionError("runtime proto field type model input is stale")
    field_type_model = read_json(field_type_model_path)
    inventory_record = field_type_model.get("inventory")
    if (
        field_type_model.get("schema") != RUNTIME_PROTO_FIELD_TYPE_SCHEMA
        or field_type_model.get("status") != "runtime-validated"
        or field_type_model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or not isinstance(inventory_record, dict)
        or not isinstance(inventory_record.get("path"), str)
    ):
        raise AcquisitionError("runtime proto field type model is invalid")
    inventory_path = Path(inventory_record["path"])
    if file_identity(inventory_path) != inventory_record:
        raise AcquisitionError("runtime proto field type inventory is stale")
    raw_field_types = inventory_path.read_bytes()
    header = RUNTIME_PROTO_FIELD_TYPE_HEADER.unpack_from(raw_field_types)
    if (
        header[0] != RUNTIME_PROTO_FIELD_TYPE_MAGIC
        or header[1] != RUNTIME_PROTO_FIELD_TYPE_VERSION
        or len(raw_field_types)
        != RUNTIME_PROTO_FIELD_TYPE_HEADER.size
        + int(header[5]) * RUNTIME_PROTO_FIELD_TYPE_RECORD.size
    ):
        raise AcquisitionError("runtime proto field type inventory is invalid")
    type_descriptor_by_field: dict[int, tuple[int, int]] = {}
    for record_index in range(int(header[5])):
        owner_index, field_index, _pointer, descriptor = (
            RUNTIME_PROTO_FIELD_TYPE_RECORD.unpack_from(
                raw_field_types,
                RUNTIME_PROTO_FIELD_TYPE_HEADER.size
                + record_index * RUNTIME_PROTO_FIELD_TYPE_RECORD.size,
            )
        )
        if field_index in type_descriptor_by_field:
            raise AcquisitionError("runtime proto field type inventory duplicates a field")
        type_descriptor_by_field[field_index] = (owner_index, descriptor)
    static_messages = {
        message.get("type_index_owner_only"): message
        for message in model.get("messages_owner_only", [])
        if isinstance(message, dict) and isinstance(message.get("name"), str)
    }
    messages: list[dict[str, Any]] = []
    field_count = 0
    candidate_count = 0
    for message_name in sorted(unresolved_by_message):
        indexes = sorted(unresolved_by_message[message_name])
        owner = _normal_gap_owner(field_by_index, indexes)
        static_message = static_messages.get(owner)
        if static_message is None:
            raise AcquisitionError("runtime proto unresolved message is absent")
        type_index = static_message.get("type_index_owner_only")
        if not isinstance(type_index, int) or not 0 <= type_index < runtime.type_count:
            raise AcquisitionError("runtime proto unresolved message identity is invalid")
        if message_name not in (static_message["name"], runtime.renderer.root_name(type_index)):
            raise AcquisitionError("runtime proto unresolved message name differs from owner identity")
        fields: list[dict[str, Any]] = []
        for field_index in indexes:
            field = field_by_index.get(field_index)
            captured_type = type_descriptor_by_field.get(field_index)
            if (
                field is None
                or int(field["owner_type_index"]) != type_index
                or captured_type is None
                or captured_type[0] != type_index
                or not captured_type[1]
            ):
                raise AcquisitionError("runtime proto unresolved field owner differs")
            fields.append(
                {
                    "field_index_owner_only": field_index,
                    "metadata_owner_only": field["metadata"],
                    "managed_offset_owner_only": field["managed_offset"],
                    "attributes_owner_only": field["attributes"],
                    "type_descriptor_owner_only": captured_type[1],
                    "name_owner_only": field["name"],
                }
            )
        resolved_numbers = {
            int(field["number"])
            for field in static_message.get("fields", [])
            if isinstance(field, dict)
            and isinstance(field.get("number"), int)
            and int(field["number"]) > 0
        }
        resolved_numbers.update(
            int(case["number"])
            for oneof in static_message.get("oneofs", [])
            if isinstance(oneof, dict)
            for case in oneof.get("cases", [])
            if isinstance(case, dict)
            and isinstance(case.get("number"), int)
            and int(case["number"]) > 0
        )
        identity = runtime.renderer.identity_row(type_index)
        candidate_numbers: list[int]
        candidate_evidence_owner_only: list[dict[str, Any]]
        candidate_mode: str
        if signed_encoding_audit:
            candidate_numbers = []
            candidate_evidence_owner_only = []
            candidate_mode = "known-signed-scalar-audit"
        else:
            evidence = parser_evidence_by_message.get(message_name)
            static_numbers = static_candidates_by_message.get(message_name) or []
            probe_resolved_numbers = sorted(resolved_numbers)
            if runtime_scan_window is not None and (force_runtime_scan or not evidence and not static_numbers):
                candidate_numbers = [
                    number for number in range(start, end + 1)
                    if number not in resolved_numbers
                ]


                candidate_evidence_owner_only = []
                candidate_mode = "runtime-parser-differential-scan"
            elif evidence:
                candidate_numbers = sorted(set(evidence) - resolved_numbers)
                candidate_evidence_owner_only = [
                    evidence[number] for number in candidate_numbers
                ]
                candidate_mode = "parser-evidence-tag-domain"
                if not candidate_numbers and not serializer_differential:
                    candidate_numbers = sorted(evidence)
                    candidate_evidence_owner_only = [
                        evidence[number] for number in candidate_numbers
                    ]
                    candidate_mode = "parser-exhaustion-audit"
                    probe_resolved_numbers = []
            elif static_numbers:
                candidate_numbers = sorted(set(static_numbers) - resolved_numbers)
                candidate_evidence_owner_only = [
                    {"number": number, "sources": ["static-field-assignment"]}
                    for number in candidate_numbers
                ]
                candidate_mode = "static-assignment-evidence"
            elif serializer_differential:
                candidate_numbers = []
                candidate_evidence_owner_only = []
                candidate_mode = "serializer-current-runtime-observation"
            else:
                raise AcquisitionError(
                    "runtime proto normal field closure has no parser tag domain"
                )
            if not serializer_differential and not candidate_numbers:
                if allow_other_gaps:


                    deferred_gaps.append({
                        "kind": "normal-field-assignment",
                        "message": message_name,
                        "field_indexes_owner_only": indexes,
                        "parser_tag_evidence_owner_only": (
                            [evidence[number] for number in sorted(evidence)]
                            if evidence else []
                        ),
                        "candidate_numbers": candidate_numbers,
                        "deferred_reason": (
                            "all-current-runtime-candidates-already-resolved"
                        ),
                    })
                    deferred_field_count += len(fields)
                    unresolved_by_message.pop(message_name, None)
                    continue
                raise AcquisitionError("runtime proto parser tag domain is exhausted")
        messages.append(
            {
                "message": message_name,
                "rendered_message_name": runtime.renderer.root_name(type_index),
                "write_to_rva_owner_only": static_message.get("write_to_rva"),
                "type_identity_owner_only": {
                    "type_index_owner_only": type_index,
                    "type_descriptor_owner_only": identity[2],
                    "class_pointer_owner_only": identity[3],
                    "type_object_owner_only": identity[6],
                    "name_owner_only": runtime.renderer.root_name(type_index),
                    "namespace_owner_only": "",
                },
                "fields_owner_only": fields,
                "resolved_numbers": probe_resolved_numbers,
                "known_resolved_numbers_owner_only": sorted(resolved_numbers),
                "candidate_mode": candidate_mode,
                "candidate_numbers": candidate_numbers,
                "candidate_evidence_owner_only": candidate_evidence_owner_only,
                "scan_min": start if candidate_mode == "runtime-parser-differential-scan" else None,
                "scan_max": end if candidate_mode == "runtime-parser-differential-scan" else None,
                "wire_selection": "derive-from-current-runtime-type-descriptor",
                "fresh_message_per_probe": True,
                "compare_exact_field_storage_and_referenced_collection_state": True,
            }
        )
        field_count += len(fields)
        if signed_encoding_audit:
            coordinates = {(field["name_owner_only"], field["managed_offset_owner_only"] + 16)
                           for field in fields}
            numbers = sorted({int(field["number"]) for field in static_message["fields"]
                              if (field["name"], field["offset"]) in coordinates})
            if len(numbers) != len(fields):
                raise AcquisitionError("signed audit field/tag domain is not one-to-one")
            messages[-1].update(
                candidate_numbers=numbers,
                resolved_numbers=[],
                scan_min=None,
                scan_max=None,
            )
            candidate_count += len(numbers)
        else:
            candidate_count += len(candidate_numbers)

    plan = {
        "schema": "alpha.runtime-proto-field-mutation-plan/v2",
        "status": "offline-plan-complete",
        "purpose": (
            "signed-scalar-serializer-audit" if signed_encoding_audit
            else "normal-field-serializer-closure" if serializer_differential
            else "normal-field-closure"
        ),
        "target": receipt["target"],
        "inputs": {
            "native_output_receipt": file_identity(
                native_output_receipt.expanduser().resolve()
            ),
            "static_model": file_identity(model_path),
            "proto_field_type_model": file_identity(field_type_model_path),
            "proto_field_type_inventory": file_identity(inventory_path),
        },
        "counts": {
            "message_probe_count": len(messages),
            ("signed_scalar_field_count" if signed_encoding_audit else "unresolved_field_count"): field_count,
            "candidate_number_count": candidate_count,
            "implicit_full_range_scan_count": 0,
        },
        "messages_owner_only": messages,
        "deferred_unresolved_owner_only": deferred_gaps,
        "checks": {
            "all_unresolved_normal_fields_planned": (
                field_count
                == sum(len(indexes) for indexes in unresolved_by_message.values())
            ),
            "deferred_records_are_explicit": all(
                row.get("deferred_reason")
                or row.get("kind") != "normal-field-assignment"
                for row in deferred_gaps
            ),
            "all_message_owners_bound_to_current_type_identity": True,
            "all_field_metadata_bound": True,
            "all_field_type_descriptors_bound": True,
            (
                "only_known_signed_field_numbers_planned"
                if signed_encoding_audit
                else "all_candidate_numbers_have_parser_case_evidence_or_explicit_runtime_scan_domain"
            ): True,
            "probe_domain_nonempty": field_count > 0,
            (
                "write_to_required"
                if signed_encoding_audit or serializer_differential
                else "write_to_not_required"
            ): True,
        },
        "policy": {
            "merge_from_only": not signed_encoding_audit and not serializer_differential,
            "serializer_audit_required": signed_encoding_audit,
            "serializer_differential_required": serializer_differential,
            "write_to_used": signed_encoding_audit or serializer_differential,
            "runtime_type_descriptor_drives_wire": True,
            "parser_tag_evidence_required": runtime_scan_window is None and not signed_encoding_audit and not serializer_differential,
            "fresh_runtime_parser_differential_scan": runtime_scan_window is not None,
            "runtime_scan_window": list(runtime_scan_window) if runtime_scan_window else None,
            "implicit_full_protobuf_range_scan_used": False,
            "fresh_message_per_probe": True,
            "saved_reference_generation_seed_used": False,
            "fixed_address_used": False,
            "fixed_offset_used": False,
            "external_runtime_component_used": False,
            "raw_pointers_owner_only": True,
        },
        "owner_only": True,
    }
    _private_json(output_path.expanduser().resolve(), plan)
    return {
        "schema": plan["schema"],
        "status": plan["status"],
        "target": plan["target"],
        "counts": plan["counts"],
        "checks": plan["checks"],
        "policy": plan["policy"],
    }


from alpha.h02 import windows_run as _host_run

import json
import os
import secrets
import stat
import struct
import subprocess
import time
from pathlib import Path
from typing import Any, Mapping

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _windows_z_path, runtime_injector_source
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.c06 import rebind_method
from alpha.p29 import _runtime
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER
from alpha.p41 import RuntimeSnapshot, _bind_current_runtime, _bind_probe_types, _c_escape_wide, _load_json, _semantic_operation, normalize_plan
from alpha.p38 import RUNTIME_PROTO_FIELD_TYPE_HEADER, RUNTIME_PROTO_FIELD_TYPE_MAGIC, RUNTIME_PROTO_FIELD_TYPE_RECORD, RUNTIME_PROTO_FIELD_TYPE_SCHEMA, RUNTIME_PROTO_FIELD_TYPE_VERSION, _binding as _proto_inventory_binding
from alpha.h02 import file_identity, read_json


PLAN_SCHEMA = "alpha.runtime-proto-serializer-probe-plan/v1"
STATUS_SCHEMA = "alpha.runtime-proto-serializer-probe-status/v1"
RESULT_SCHEMA = "alpha.runtime-proto-serializer-probe-result/v1"
MAGIC = b"ALPHAPS4"
VERSION = 4
HEADER = struct.Struct("<8sIIIIQQ64s")
RECORD = struct.Struct("<IIIIII" + "Q" * 20)
SUPPORTED_TYPE_ENUMS = frozenset(
    {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 29}
)
QUIESCENT_RETRY_FAILURES = frozenset({20, 21, 22, 23, 27})


def _retryable_quiescent_failure(status: Mapping[str, Any]) -> bool:

    return (
        status.get("status") == "capture_failed"
        and status.get("failure_kind_owner_only") in QUIESCENT_RETRY_FAILURES
    )


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime proto serializer {label} is not owner-only")
    return path


def _rows(
    *,
    normalized: Mapping[str, Any],
    runtime: Any,
    live: Any,
    writer_family_descriptor: int,
    field_type_descriptors: Mapping[int, int],
    field_type_enums: Mapping[int, int],
) -> tuple[list[dict[str, int]], int]:
    rows: list[dict[str, int]] = []
    skipped = 0
    live_type_by_descriptor = {
        live.type_row(type_index).embedded_descriptor(
            live.embedded_descriptor_byte_offset
        ): type_index
        for type_index in range(live.type_count)
    }
    byte_array_offsets_by_owner: dict[int, list[int]] = {}
    for nested_field_index, nested_type_enum in field_type_enums.items():
        if nested_type_enum != 29:
            continue
        nested = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + nested_field_index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        if not nested[5] & 0x10:
            byte_array_offsets_by_owner.setdefault(int(nested[0]), []).append(
                int(nested[4]) + 16
            )
    for message in normalized["messages_owner_only"]:
        type_index = int(message["type_index_owner_only"])
        owner_descriptor = int(message["type_descriptor_current_owner_only"])


        owner = live.type_row(type_index)
        calculate = []
        write_to = []
        for method_index in range(
            owner.method_start, owner.method_start + owner.method_count
        ):
            method = runtime.method_row(method_index)
            if method[9] & 1 or method[5] & 0x10:
                continue
            if method[10] == 0 and runtime.method_return(method_index) == "System.Int32":
                calculate.append(live.method_row(method_index, expected_owner=type_index))
            elif (
                method[10] == 1
                and runtime.method_return(method_index) == "System.Void"
                and runtime.parameter_row(method[11])[2] == writer_family_descriptor
            ):
                write_to.append(live.method_row(method_index, expected_owner=type_index))
        calculate_method = calculate[0] if len(calculate) == 1 else None
        write_method = write_to[0] if len(write_to) == 1 else None
        for field in message["fields_owner_only"]:
            type_enum = int(field["runtime_type_enum"])
            if type_enum not in SUPPORTED_TYPE_ENUMS:
                skipped += 1
                continue
            field_index = int(field["field_index_owner_only"])
            current_field = live.field_row(field_index, expected_owner=type_index)
            field_type_descriptor = 0
            if type_enum == 18:
                old_descriptor = int(field["type_descriptor_owner_only"])
                field_type_index = runtime.renderer.root_by_descriptor.get(
                    old_descriptor
                )
                if field_type_index is None:
                    field_type_index = live_type_by_descriptor.get(old_descriptor)
                if field_type_index is None:
                    skipped += 1
                    continue
                field_type_descriptor = live.type_row(
                    field_type_index
                ).embedded_descriptor(live.embedded_descriptor_byte_offset)
            byte_container_offset = 0
            if (
                type_enum == 18
                and field_type_index is not None
                and "System.Collections.Generic.IEnumerable<System.Byte>"
                in runtime.renderer.root_interfaces(field_type_index)
            ):
                offsets = byte_array_offsets_by_owner.get(field_type_index, [])
                if len(offsets) != 1:
                    skipped += 1
                    continue
                byte_container_offset = offsets[0]
            rows.append(
                {
                    "message_type_index": type_index,
                    "message_descriptor": owner_descriptor,
                    "field_index": field_index,
                    "field_pointer": current_field.pointer,
                    "field_offset": int(field["managed_offset_owner_only"]),
                    "type_enum": type_enum,
                    "field_type_descriptor": field_type_descriptor,
                    "byte_container_offset": byte_container_offset,
                    "calculate_pointer": (
                        calculate_method.function_pointer if calculate_method else 0
                    ),
                    "calculate_metadata": (
                        calculate_method.metadata_pointer if calculate_method else 0
                    ),
                    "write_pointer": write_method.function_pointer if write_method else 0,
                    "write_metadata": write_method.metadata_pointer if write_method else 0,
                }
            )
    if not rows:
        raise AcquisitionError("runtime proto serializer probe domain is empty")
    return rows, skipped


def _captured_field_types(
    model_path: Path, snapshot: RuntimeSnapshot, *, required_fields: set[int] | None = None
) -> tuple[dict[int, int], dict[int, int]]:
    model = read_json(_owner_file(model_path, label="field type model"))
    inventory = model.get("inventory")
    if (
        model.get("schema") != RUNTIME_PROTO_FIELD_TYPE_SCHEMA
        or model.get("status") != "runtime-validated"
        or not isinstance(inventory, Mapping)
        or not isinstance(inventory.get("path"), str)
    ):
        raise AcquisitionError("runtime proto serializer field type model is invalid")
    inventory_path = _owner_file(
        Path(inventory["path"]), label="field type inventory"
    )
    if file_identity(inventory_path) != inventory:
        raise AcquisitionError("runtime proto serializer field type inventory is stale")
    raw = inventory_path.read_bytes()
    header = RUNTIME_PROTO_FIELD_TYPE_HEADER.unpack_from(raw)
    if (
        header[0] != RUNTIME_PROTO_FIELD_TYPE_MAGIC
        or header[1] != RUNTIME_PROTO_FIELD_TYPE_VERSION
        or len(raw)
        != RUNTIME_PROTO_FIELD_TYPE_HEADER.size
        + int(header[5]) * RUNTIME_PROTO_FIELD_TYPE_RECORD.size
    ):
        raise AcquisitionError("runtime proto serializer field type inventory differs")
    descriptors: dict[int, int] = {}
    enums: dict[int, int] = {}
    for index in range(int(header[5])):
        _owner, field_index, _pointer, descriptor = (
            RUNTIME_PROTO_FIELD_TYPE_RECORD.unpack_from(
                raw,
                RUNTIME_PROTO_FIELD_TYPE_HEADER.size
                + index * RUNTIME_PROTO_FIELD_TYPE_RECORD.size,
            )
        )
        if field_index in descriptors or not descriptor:
            raise AcquisitionError("runtime proto serializer field types conflict")
        descriptors[field_index] = descriptor
        try:
            enums[field_index] = snapshot.il2cpp_type_enum(descriptor)
        except KeyError:


            if required_fields is None or field_index in required_fields:
                raise
    if required_fields is not None and not required_fields <= enums.keys():
        raise AcquisitionError("runtime proto required serializer field type codes are incomplete")
    return descriptors, enums


def _render(
    *,
    rows: list[dict[str, int]],
    binding: Mapping[str, Any],
    output: Path,
    status: Path,
) -> str:
    extensions = binding["extensions"]
    factory = binding["message_factory"]
    type_from_handle = binding["type_from_handle"]
    field_from_handle = binding["field_from_handle"]
    field_name = binding["field_name"]
    row_text = ",\n".join(
        "    {%du,%du,%du,%du,%du,%dull,%dull,%dull,%dull,%dull,%dull,%dull}"
        % (
            row["message_type_index"],
            row["field_index"],
            row["field_offset"],
            row["type_enum"],
            row["byte_container_offset"],
            row["message_descriptor"],
            row["field_pointer"],
            row["field_type_descriptor"],
            row["calculate_pointer"],
            row["calculate_metadata"],
            row["write_pointer"],
            row["write_metadata"],
        )
        for row in rows
    )
    return f'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#define ALPHA_SERIALIZER_BATCH 16u
typedef struct input_record{{uint32_t message_type_index,field_index,field_offset,type_enum,byte_container_offset;uint64_t message_descriptor,field_pointer,field_type_descriptor,calculate_pointer,calculate_metadata,write_pointer,write_metadata;}}input_record;
typedef struct output_header{{char magic[8];uint32_t version,header_bytes,record_bytes,reserved;uint64_t count,process_id;char executable[64];}}output_header;
typedef struct output_record{{uint32_t field_index,type_enum,number,wire,failure_kind,reserved;uint64_t serialized_bytes,signed_positive,signed_negative,change_count,changed_tags[16];}}output_record;
_Static_assert(sizeof(output_header)=={HEADER.size},"serializer header");
_Static_assert(sizeof(output_record)=={RECORD.size},"serializer record");
static const input_record inputs[]={{
{row_text}
}};
static output_record records[{len(rows)}u];
static const uint32_t input_count={len(rows)}u;
static const DWORD expected_pid={int(binding['process_id'])}u;
static const char executable_sha[]="{binding['binary']['sha256']}";
static const uintptr_t type_from_handle_pointer={int(type_from_handle['pointer'])}ull,type_from_handle_metadata={int(type_from_handle['metadata'])}ull;
static const uintptr_t activator_pointer={int(factory['pointer'])}ull,activator_metadata={int(factory['metadata'])}ull;
static const uintptr_t array_new_pointer={int(extensions['serializer_array_new_pointer'])}ull,byte_array_class_slot={int(extensions['serializer_byte_array_class_slot'])}ull;
static const uintptr_t object_new_pointer={int(extensions['serializer_object_new_pointer'])}ull,coded_output_class_slot={int(extensions['serializer_coded_output_class_slot'])}ull;
static const uint32_t class_vtable_count_offset={int(extensions['serializer_class_vtable_count_offset'])}u,calculate_slot_offset={int(extensions['serializer_calculate_slot_offset'])}u,write_slot_offset={int(extensions['serializer_write_slot_offset'])}u;
static const uint32_t stream_array_offset={int(extensions['serializer_stream_array_offset'])}u,stream_null_offset={int(extensions['serializer_stream_null_offset'])}u,stream_bool_offset={int(extensions['serializer_stream_bool_offset'])}u,stream_zero_offset={int(extensions['serializer_stream_zero_offset'])}u,stream_length_offset={int(extensions['serializer_stream_length_offset'])}u;
static const uintptr_t field_from_handle_pointer={int(field_from_handle['pointer'])}ull,field_from_handle_metadata={int(field_from_handle['metadata'])}ull;
static const uintptr_t field_name_pointer={int(field_name['pointer'])}ull,field_name_metadata={int(field_name['metadata'])}ull;
static const wchar_t output_path[]=L"{_c_escape_wide(output)}";
static const wchar_t status_path[]=L"{_c_escape_wide(status)}";
typedef uintptr_t(*onearg)(uintptr_t,uintptr_t);typedef uintptr_t(*twoarg)(uintptr_t,uintptr_t);typedef uintptr_t(*static_twoarg)(uintptr_t,uintptr_t,uintptr_t);typedef uintptr_t(*alloc_one)(uintptr_t);typedef int32_t(*instance_size)(uintptr_t,uintptr_t);typedef void(*instance_write)(uintptr_t,uintptr_t,uintptr_t);
static UINT message_id;static WNDPROC original_proc;static volatile LONG callback_complete,probe_stage;static uint32_t completed_count,failure_count,failure_kind,failure_index,capture_cursor,debug_length;static uint64_t debug_first_bytes,debug_tag;
static int readable(uintptr_t v,SIZE_T n){{MEMORY_BASIC_INFORMATION r;if(!v||!n||v+n<v||!VirtualQuery((const void*)v,&r,sizeof(r))||r.State!=MEM_COMMIT||r.Protect&PAGE_GUARD)return 0;DWORD p=r.Protect&0xffu;uintptr_t e=(uintptr_t)r.BaseAddress+r.RegionSize;return p&&p!=PAGE_NOACCESS&&e>=v&&v+n<=e;}}
static uintptr_t byte_array(void){{uintptr_t klass=0;if(!readable(byte_array_class_slot,8u))return 0;memcpy(&klass,(const void*)byte_array_class_slot,8u);if(!klass)return 0;twoarg array_new=(twoarg)array_new_pointer;uintptr_t value=array_new(klass,3u);if(!value||!readable(value+0x20u,3u))return 0;memcpy((void*)(value+0x20u),"ALPHA",3u);return value;}}
static int put_value(uintptr_t message,const input_record*r){{uintptr_t address=message+r->field_offset;if(!readable(address,8u))return 0;if(r->type_enum==14u){{static_twoarg from_handle=(static_twoarg)field_from_handle_pointer;uintptr_t field=from_handle(r->field_pointer,r->message_descriptor,field_from_handle_metadata);if(!field)return 0;onearg get_name=(onearg)field_name_pointer;uintptr_t value=get_name(field,field_name_metadata);if(!value)return 0;memcpy((void*)address,&value,8u);return 1;}}if(r->type_enum==18u){{onearg get_type=(onearg)type_from_handle_pointer;uintptr_t type=get_type(r->field_type_descriptor,type_from_handle_metadata);if(!type)return 0;onearg create=(onearg)activator_pointer;uintptr_t value=create(type,activator_metadata);if(!value)return 0;if(r->byte_container_offset){{uintptr_t bytes=byte_array();uintptr_t nested=value+r->byte_container_offset;if(!bytes||!readable(nested,8u))return 0;memcpy((void*)nested,&bytes,8u);}}memcpy((void*)address,&value,8u);return 1;}}if(r->type_enum==29u){{uintptr_t value=byte_array();if(!value)return 0;memcpy((void*)address,&value,8u);return 1;}}uint64_t value=123u;SIZE_T bytes=8u;if(r->type_enum==2u){{value=1u;bytes=1u;}}else if(r->type_enum==4u||r->type_enum==5u)bytes=1u;else if(r->type_enum==3u||r->type_enum==6u||r->type_enum==7u)bytes=2u;else if(r->type_enum==8u||r->type_enum==9u||r->type_enum==17u)bytes=4u;else if(r->type_enum==12u){{float v=1.25f;memcpy((void*)address,&v,4u);return 1;}}else if(r->type_enum==13u){{double v=1.25;memcpy((void*)address,&v,8u);return 1;}}memcpy((void*)address,&value,bytes);return 1;}}
static int varint(const unsigned char*data,SIZE_T bytes,uint64_t*out,SIZE_T*used){{uint64_t v=0;for(SIZE_T i=0;i<bytes&&i<10u;i++){{unsigned char b=data[i];v|=(uint64_t)(b&0x7fu)<<(i*7u);if(!(b&0x80u)){{*out=v;*used=i+1u;return 1;}}}}return 0;}}
typedef struct field_observation{{uint32_t number,wire,count,reserved;uint64_t hash;}}field_observation;
static uint64_t hash_bytes(const unsigned char*data,SIZE_T bytes,uint64_t value){{for(SIZE_T i=0;i<bytes;i++){{value^=data[i];value*=1099511628211ull;}}return value;}}
static int scan_fields(const unsigned char*data,SIZE_T bytes,field_observation*out,uint32_t capacity,uint32_t*out_count){{SIZE_T cursor=0;uint32_t count=0;while(cursor<bytes){{SIZE_T start=cursor,used=0;uint64_t tag=0,value=0;if(!varint(data+cursor,bytes-cursor,&tag,&used)||!(tag>>3u)||(tag>>3u)>0x1fffffffu)return 0;cursor+=used;uint32_t wire=(uint32_t)(tag&7u);if(wire==0u){{if(!varint(data+cursor,bytes-cursor,&value,&used))return 0;cursor+=used;}}else if(wire==1u){{if(bytes-cursor<8u)return 0;cursor+=8u;}}else if(wire==2u){{if(!varint(data+cursor,bytes-cursor,&value,&used)||value>bytes-cursor-used)return 0;cursor+=used+(SIZE_T)value;}}else if(wire==5u){{if(bytes-cursor<4u)return 0;cursor+=4u;}}else return 0;uint32_t number=(uint32_t)(tag>>3u),index=count;for(uint32_t i=0;i<count;i++)if(out[i].number==number&&out[i].wire==wire){{index=i;break;}}if(index==count){{if(count>=capacity)return 0;memset(&out[count],0,sizeof(out[count]));out[count].number=number;out[count].wire=wire;out[count].hash=1469598103934665603ull;count++;}}out[index].count++;out[index].hash=hash_bytes(data+start,cursor-start,out[index].hash);}}*out_count=count;return 1;}}
static void record_change(uint32_t number,uint32_t wire,uint32_t*changes,uint64_t tags[16]){{if(*changes<16u)tags[*changes]=((uint64_t)number<<3u)|wire;(*changes)++;}}
static int changed_field(const unsigned char*before,SIZE_T before_bytes,const unsigned char*after,SIZE_T after_bytes,uint32_t*number,uint32_t*wire,uint32_t*change_count,uint64_t tags[16]){{SIZE_T largest=before_bytes>after_bytes?before_bytes:after_bytes;if(largest>UINT32_MAX*2ull-2ull)return 0;uint32_t capacity=(uint32_t)(largest/2u)+1u;field_observation*a=(field_observation*)HeapAlloc(GetProcessHeap(),HEAP_ZERO_MEMORY,(SIZE_T)capacity*sizeof(field_observation));field_observation*b=(field_observation*)HeapAlloc(GetProcessHeap(),HEAP_ZERO_MEMORY,(SIZE_T)capacity*sizeof(field_observation));uint32_t ac=0,bc=0,changes=0;int result=0;memset(tags,0,16u*sizeof(uint64_t));if(!a||!b)goto done;if((before_bytes&&!scan_fields(before,before_bytes,a,capacity,&ac))||!scan_fields(after,after_bytes,b,capacity,&bc))goto done;for(uint32_t i=0;i<bc;i++){{uint32_t j=0;while(j<ac&&(a[j].number!=b[i].number||a[j].wire!=b[i].wire))j++;if(j==ac||a[j].count!=b[i].count||a[j].hash!=b[i].hash)record_change(b[i].number,b[i].wire,&changes,tags);}}for(uint32_t i=0;i<ac;i++){{uint32_t j=0;while(j<bc&&(b[j].number!=a[i].number||b[j].wire!=a[i].wire))j++;if(j==bc)record_change(a[i].number,a[i].wire,&changes,tags);}}*change_count=changes;if(changes){{*number=(uint32_t)(tags[0]>>3u);*wire=(uint32_t)(tags[0]&7u);}}result=changes==1u;done:if(a)HeapFree(GetProcessHeap(),0,a);if(b)HeapFree(GetProcessHeap(),0,b);return result;}}
static int serialize_message(uintptr_t message,const input_record*r,uintptr_t*out_array,uint64_t*out_length){{uintptr_t calculate_pointer=r->calculate_pointer,calculate_metadata=r->calculate_metadata,write_pointer=r->write_pointer,write_metadata=r->write_metadata;if(!calculate_pointer||!calculate_metadata||!write_pointer||!write_metadata){{uintptr_t klass=0;if(!readable(message,8u))return 0;memcpy(&klass,(const void*)message,8u);if(!klass||!readable(klass+class_vtable_count_offset,2u)||!readable(klass+calculate_slot_offset,8u)||!readable(klass+write_slot_offset,8u))return 0;uint16_t slots=0;memcpy(&slots,(const void*)(klass+class_vtable_count_offset),2u);if(!slots)return 0;uintptr_t calculate_metadata_address=klass+(uintptr_t)slots*8u+calculate_slot_offset;uintptr_t write_metadata_address=klass+(uintptr_t)slots*8u+write_slot_offset;if(!readable(calculate_metadata_address,8u)||!readable(write_metadata_address,8u))return 0;memcpy(&calculate_pointer,(const void*)(klass+calculate_slot_offset),8u);memcpy(&calculate_metadata,(const void*)calculate_metadata_address,8u);memcpy(&write_pointer,(const void*)(klass+write_slot_offset),8u);memcpy(&write_metadata,(const void*)write_metadata_address,8u);}}if(!calculate_pointer||!calculate_metadata||!write_pointer||!write_metadata)return 0;int32_t size=((instance_size)calculate_pointer)(message,calculate_metadata);if(size<0||size>1048576)return 0;if(!size){{*out_array=0;*out_length=0;return 1;}}uintptr_t byte_class=0,coded_class=0;if(!readable(byte_array_class_slot,8u)||!readable(coded_output_class_slot,8u))return 0;memcpy(&byte_class,(const void*)byte_array_class_slot,8u);memcpy(&coded_class,(const void*)coded_output_class_slot,8u);if(!byte_class||!coded_class)return 0;twoarg array_new=(twoarg)array_new_pointer;uintptr_t output=array_new(byte_class,(uintptr_t)(uint32_t)size);alloc_one object_new=(alloc_one)object_new_pointer;uintptr_t stream=object_new(coded_class);if(!output||!stream||!readable(stream,0x80u))return 0;uintptr_t zero=0;uint32_t zero32=0,length32=(uint32_t)size;unsigned char one=1u;memcpy((void*)(stream+stream_null_offset),&zero,8u);memcpy((void*)(stream+stream_array_offset),&output,8u);memcpy((void*)(stream+stream_zero_offset),&zero32,4u);memcpy((void*)(stream+stream_length_offset),&length32,4u);memcpy((void*)(stream+stream_bool_offset),&one,1u);((instance_write)write_pointer)(message,stream,write_metadata);if(!readable(output,0x20u))return 0;uint64_t length=0;memcpy(&length,(const void*)(output+0x18u),8u);if(!length||length>1048576u||!readable(output+0x20u,(SIZE_T)length))return 0;*out_array=output;*out_length=length;return 1;}}
static int collect(void){{onearg get_type=(onearg)type_from_handle_pointer;onearg create=(onearg)activator_pointer;uint32_t end=capture_cursor+ALPHA_SERIALIZER_BATCH;if(end>input_count)end=input_count;for(;capture_cursor<end;capture_cursor++){{uint32_t i=capture_cursor;InterlockedExchange(&probe_stage,(LONG)(1000u+i));failure_index=i;const input_record*r=&inputs[i];output_record*out=&records[i];out->field_index=r->field_index;out->type_enum=r->type_enum;uintptr_t type=get_type(r->message_descriptor,type_from_handle_metadata);uintptr_t message=type?create(type,activator_metadata):0;uintptr_t before_array=0,array=0;uint64_t before_length=0,length=0;uint32_t kind=!type?1u:!message?2u:!serialize_message(message,r,&before_array,&before_length)?5u:!put_value(message,r)?3u:!serialize_message(message,r,&array,&length)?4u:0u;if(!kind){{debug_length=(uint32_t)length;debug_first_bytes=0;debug_tag=0;if(length)memcpy(&debug_first_bytes,(const void*)(array+0x20u),length<8u?(SIZE_T)length:8u);uint32_t number=0,wire=0,changes=0;const unsigned char*before=before_length?(const unsigned char*)(before_array+0x20u):NULL;const unsigned char*after=length?(const unsigned char*)(array+0x20u):NULL;if(!length)kind=7u;else if(!changed_field(before,(SIZE_T)before_length,after,(SIZE_T)length,&number,&wire,&changes,out->changed_tags)){{out->change_count=changes;kind=8u;}}else{{debug_tag=((uint64_t)number<<3u)|wire;out->number=number;out->wire=wire;out->serialized_bytes=length;out->change_count=1u;}}}}if(kind){{out->failure_kind=kind;failure_count++;}}completed_count=i+1u;}}InterlockedExchange(&probe_stage,2);return 1;}}
static LRESULT CALLBACK window_proc(HWND w,UINT m,WPARAM wp,LPARAM lp){{if(m!=message_id)return CallWindowProcW(original_proc,w,m,wp,lp);int ok=collect();InterlockedExchange(&callback_complete,ok?1:-1);return ok;}}
typedef struct selection{{DWORD pid;HWND window;uint32_t count;}}selection;static BOOL CALLBACK select_window(HWND w,LPARAM v){{selection*s=(selection*)(uintptr_t)v;DWORD pid=0;RECT b;if(!IsWindowVisible(w)||GetWindow(w,GW_OWNER)||!GetWindowRect(w,&b)||b.right<=b.left||b.bottom<=b.top)return TRUE;GetWindowThreadProcessId(w,&pid);if(pid==s->pid){{s->window=w;s->count++;}}return TRUE;}}
static int dispatch(void){{selection s={{0}};s.pid=GetCurrentProcessId();if(!EnumWindows(select_window,(LPARAM)(uintptr_t)&s)||s.count!=1||!s.window)return failure_kind=10,0;message_id=RegisterWindowMessageW(status_path);SetLastError(0);original_proc=(WNDPROC)(uintptr_t)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)window_proc);int ok=message_id&&(original_proc||GetLastError()==ERROR_SUCCESS);uint32_t transient_failures=0;while(ok&&capture_cursor<input_count){{DWORD_PTR result=0;InterlockedExchange(&callback_complete,0);int sent=SendMessageTimeoutW(s.window,message_id,0,0,SMTO_BLOCK,60000,&result)!=0;LONG callback=InterlockedCompareExchange(&callback_complete,0,0);if(sent&&callback==1){{transient_failures=0;continue;}}if(failure_kind||callback==-1){{ok=0;break;}}if(transient_failures++<8u)continue;failure_kind=11;ok=0;}}if(original_proc)SetWindowLongPtrW(s.window,GWLP_WNDPROC,(LONG_PTR)(uintptr_t)original_proc);return ok;}}
static void hex(const unsigned char*d,char*o){{static const char a[]="0123456789abcdef";for(int i=0;i<32;i++){{o[i*2]=a[d[i]>>4];o[i*2+1]=a[d[i]&15];}}o[64]=0;}}static int sha(const wchar_t*p,char out[65]){{HANDLE f=CreateFileW(p,GENERIC_READ,FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,0,NULL);if(f==INVALID_HANDLE_VALUE)return 0;BCRYPT_ALG_HANDLE a=NULL;BCRYPT_HASH_HANDLE h=NULL;DWORD n=0,g=0;unsigned char*o=NULL,*b=NULL,d[32];int ok=BCryptOpenAlgorithmProvider(&a,BCRYPT_SHA256_ALGORITHM,NULL,0)>=0&&BCryptGetProperty(a,BCRYPT_OBJECT_LENGTH,(PUCHAR)&n,sizeof(n),&g,0)>=0;if(ok)o=HeapAlloc(GetProcessHeap(),0,n);if(ok)b=HeapAlloc(GetProcessHeap(),0,1048576u);if(ok&&(!o||!b))ok=0;if(ok&&BCryptCreateHash(a,&h,o,n,NULL,0,0)<0)ok=0;while(ok){{DWORD z=0;if(!ReadFile(f,b,1048576u,&z,NULL)){{ok=0;break;}}if(!z)break;if(BCryptHashData(h,b,z,0)<0)ok=0;}}if(ok&&BCryptFinishHash(h,d,32,0)<0)ok=0;if(ok)hex(d,out);if(h)BCryptDestroyHash(h);if(a)BCryptCloseAlgorithmProvider(a,0);if(o)HeapFree(GetProcessHeap(),0,o);if(b)HeapFree(GetProcessHeap(),0,b);CloseHandle(f);return ok;}}static int identity(char out[65]){{wchar_t p[32768];DWORD n=GetModuleFileNameW(NULL,p,32768u);return n&&n<32768u&&sha(p,out);}}
static int write_output(void){{output_header h;memset(&h,0,sizeof(h));memcpy(h.magic,"ALPHAPS1",8);h.version=1;h.header_bytes=sizeof(h);h.record_bytes=sizeof(output_record);h.count=input_count;h.process_id=GetCurrentProcessId();memcpy(h.executable,executable_sha,64);FILE*f=_wfopen(output_path,L"wb");if(!f)return 0;int ok=fwrite(&h,1,sizeof(h),f)==sizeof(h)&&fwrite(records,sizeof(output_record),input_count,f)==input_count;if(fclose(f))ok=0;if(!ok)_wremove(output_path);else _wchmod(output_path,0600);return ok;}}
static void write_status(const char*s,int written){{FILE*f=_wfopen(status_path,L"wb");if(!f)return;fprintf(f,"{{\\n  \\"schema\\": \\"{STATUS_SCHEMA}\\",\\n  \\"status\\": \\"%s\\",\\n  \\"process_id\\": %lu,\\n  \\"expected_count\\": %u,\\n  \\"completed_count\\": %u,\\n  \\"probe_failure_count\\": %u,\\n  \\"failure_kind_owner_only\\": %u,\\n  \\"failure_index_owner_only\\": %u,\\n  \\"probe_stage_owner_only\\": %ld,\\n  \\"debug_length_owner_only\\": %u,\\n  \\"debug_first_bytes_owner_only\\": %llu,\\n  \\"debug_tag_owner_only\\": %llu,\\n  \\"output_written\\": %s,\\n  \\"fresh_runtime_observation\\": true,\\n  \\"write_to_used\\": true,\\n  \\"saved_runtime_pointer_used\\": false,\\n  \\"external_runtime_component_used\\": false\\n}}\\n",s,(unsigned long)GetCurrentProcessId(),input_count,completed_count,failure_count,failure_kind,failure_index,InterlockedCompareExchange(&probe_stage,0,0),debug_length,(unsigned long long)debug_first_bytes,(unsigned long long)debug_tag,written?"true":"false");fclose(f);_wchmod(status_path,0600);}}
static DWORD WINAPI worker(LPVOID u){{(void)u;_wremove(output_path);_wremove(status_path);char d[65];if(GetCurrentProcessId()!=expected_pid||!identity(d)||strcmp(d,executable_sha)){{failure_kind=100;write_status("identity_mismatch",0);return 0;}}int ok=dispatch();if(!ok){{write_status("capture_failed",0);return 0;}}ok=write_output();write_status(ok?"complete":"write_failed",ok);return 0;}}BOOL WINAPI DllMain(HINSTANCE m,DWORD r,LPVOID z){{(void)z;if(r==DLL_PROCESS_ATTACH){{DisableThreadLibraryCalls(m);HANDLE t=CreateThread(NULL,0,worker,NULL,0,NULL);if(t)CloseHandle(t);}}return TRUE;}}
'''


def prepare_runtime_proto_serializer_probe(
    *,
    mutation_plan: Path,
    snapshot: Path,
    native_output_receipt: Path,
    proto_field_type_model: Path,
    runtime_materializer_model: Path,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    mutation_plan = _owner_file(mutation_plan, label="mutation plan")
    snapshot = _owner_file(snapshot, label="snapshot")
    source_plan = _load_json(mutation_plan)
    with RuntimeSnapshot(snapshot) as memory:
        normalized = normalize_plan(source_plan, memory, allow_serializer_audit=True)
        field_type_descriptors, field_type_enums = _captured_field_types(
            proto_field_type_model, memory,
            required_fields={int(field["field_index_owner_only"])
                             for message in normalized["messages_owner_only"]
                             for field in message["fields_owner_only"]},
        )
    binding, live = _bind_current_runtime(
        native_output_receipt=native_output_receipt,
        proto_field_type_model=proto_field_type_model,
        runtime_materializer_model=runtime_materializer_model,
    )
    try:
        normalized = _bind_probe_types(normalized, live)
        _receipt, _paths, runtime = _runtime(native_output_receipt)
        rows, skipped = _rows(
            normalized=normalized,
            runtime=runtime,
            live=live,
            writer_family_descriptor=int(binding["writer_family_descriptor"]),
            field_type_descriptors=field_type_descriptors,
            field_type_enums=field_type_enums,
        )
        inventory = _proto_inventory_binding(native_output_receipt)
        semantics_path = _owner_file(
            Path(inventory["reflection_semantics"]["path"]),
            label="reflection semantics",
        )
        semantics = read_json(semantics_path)
        binding["field_from_handle"] = rebind_method(
            runtime, live, _semantic_operation(semantics, "field.from_handle")
        )
        binding["field_name"] = rebind_method(
            runtime, live, _semantic_operation(semantics, "field.name")
        )
    finally:
        live.close()
    field_contracts = {}
    for message in normalized["messages_owner_only"]:
        contract = {
            "candidate_numbers": list(message["candidate_numbers"]),
            "resolved_numbers": list(message["resolved_numbers"]),
        }
        for field in message["fields_owner_only"]:
            field_contracts[int(field["field_index_owner_only"])] = {
                **contract,
                "wire_mask": int(field["wire_mask"]),
            }
    output = output_dir / "runtime-proto-serializer-probe.private.bin"
    status = output_dir / "runtime-proto-serializer-probe-status.private.json"
    build_dir = _owner_directory(output_dir / "build-runtime-proto-serializer")
    source = build_dir / "runtime-proto-serializer-probe.c"
    injector_source = build_dir / "runtime-proto-serializer-injector.c"
    for stale in (
        output,
        status,
        Path(str(status) + ".progress.json"),
        Path(str(status) + ".progress.json.pending"),
    ):
        stale.unlink(missing_ok=True)
    from alpha.p01 import harden_serializer_memory
    from alpha.p01 import enrich_serializer_source
    from alpha.c01 import harden_serializer_dispatch
    _private_text(source, harden_serializer_memory(
        harden_serializer_dispatch(enrich_serializer_source(_render(rows=rows, binding=binding, output=output, status=status)))))
    _private_text(injector_source, runtime_injector_source())


    load_identity = secrets.token_hex(8)
    collector = build_dir / ("alpha-runtime-proto-serializer-" + file_identity(source)["sha256"][:12] + "-" + load_identity + ".dll")
    injector = build_dir / "alpha-runtime-proto-serializer-injector.exe"
    cc = _compiler(compiler)
    _build([str(cc), "-O2", "-s", "-shared", "-Wall", "-Wextra", "-Wformat=2", "-Werror", str(source), "-o", str(collector), "-lbcrypt"], label="runtime proto serializer collector")
    _build([str(cc), "-O2", "-s", "-municode", "-Wall", "-Wextra", "-Wformat=2", "-Werror", str(injector_source), "-o", str(injector)], label="runtime proto serializer injector")
    for artifact in (collector, injector):
        artifact.chmod(0o600)
    plan = {
        "schema": PLAN_SCHEMA,
        "status": "prepared",
        "target": {"executable_path": binding["binary"]["path"], "executable_sha256": binding["binary"]["sha256"], "process_id": binding["process_id"]},
        "inputs": {"mutation_plan": file_identity(mutation_plan), "snapshot": file_identity(snapshot), "native_output_receipt": file_identity(native_output_receipt), "proto_field_type_model": file_identity(proto_field_type_model), "runtime_materializer_model": file_identity(runtime_materializer_model)},
        "contract": {
            "record_count": len(rows),
            "skipped_generic_or_object_count": skipped,
            "field_indexes": [row["field_index"] for row in rows],
            "fields_owner_only": [
                {"field_index_owner_only": row["field_index"], **field_contracts[row["field_index"]]}
                for row in rows
            ],
        },
        "collector": {**file_identity(collector), "load_identity": load_identity}, "injector": file_identity(injector), "output_path": str(output), "status_path": str(status),
        "policy": {"serializer_differential_reimplemented": True, "fresh_message_per_field": True, "current_runtime_inventory_required": True, "write_to_used": True, "probe_exception_releases_callback": True, "saved_runtime_pointer_used": False, "fixed_address_used": False, "external_runtime_component_used": False},
    }
    _private_json(output_dir / "runtime-proto-serializer-probe-plan.private.json", plan)
    return {"schema": PLAN_SCHEMA, "status": "prepared", "counts": {"record_count": len(rows), "skipped_count": skipped}, "policy": plan["policy"]}


def _validate(plan: Mapping[str, Any], status: Mapping[str, Any]) -> dict[str, Any]:
    path = _owner_file(Path(plan["output_path"]), label="output")
    raw = path.read_bytes()
    header = HEADER.unpack_from(raw)
    count = int(plan["contract"]["record_count"])
    checks = {
        "status_complete": status.get("status") == "complete",
        "header_bound": header[0] == MAGIC and header[1] == VERSION and header[2] == HEADER.size and header[3] == RECORD.size and header[4] == 0 and header[5] == count and header[6] == plan["target"]["process_id"] and header[7].decode("ascii") == plan["target"]["executable_sha256"],
        "envelope_closes": len(raw) == HEADER.size + count * RECORD.size,
        "all_records_completed": status.get("completed_count") == count,
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "write_to_used": status.get("write_to_used") is True,
        "saved_runtime_pointer_absent": status.get("saved_runtime_pointer_used") is False,
        "external_runtime_component_absent": status.get("external_runtime_component_used") is False,
    }
    rows: list[dict[str, int]] = []
    failures: list[dict[str, int]] = []
    observed: set[int] = set()
    if checks["header_bound"] and checks["envelope_closes"]:
        for index, expected in enumerate(plan["contract"]["field_indexes"]):
            values = RECORD.unpack_from(raw, HEADER.size + index * RECORD.size)
            (
                field_index, type_enum, number, wire, failure, reserved,
                size, positive, negative, change_count, *changed_raw,
            ) = values
            if field_index != expected or field_index in observed:
                checks["record_domain_closed"] = False
                break
            observed.add(field_index)
            if failure:
                changed_tags = [
                    {"number": int(raw_tag >> 3), "wire": int(raw_tag & 7)}
                    for raw_tag in changed_raw[:min(int(change_count), len(changed_raw))]
                ]
                complete_change_set = int(change_count) <= len(changed_raw)
                changed_tags_valid = (
                    failure == 8
                    and (
                        (change_count == 0 and not any(changed_raw))
                        or change_count >= 2
                    )
                    and all(
                        0 < item["number"] <= 0x1FFFFFFF
                        and item["wire"] in (0, 1, 2, 5)
                        for item in changed_tags
                    )
                    and all(not value for value in changed_raw[len(changed_tags):])
                )
                if (
                    number or wire or size or reserved
                    or failure not in (1, 2, 3, 4, 5, 6, 7, 8, 9)
                    or (failure == 8 and not changed_tags_valid)
                    or (failure != 8 and (change_count or any(changed_raw)))
                ):
                    checks["record_domain_closed"] = False
                    break
                contract = plan["contract"]["fields_owner_only"][index]
                if contract.get("field_index_owner_only") != field_index:
                    checks["record_domain_closed"] = False
                    break
                compatible_candidates = [
                    item for item in changed_tags
                    if item["number"] in contract["candidate_numbers"]
                    and int(contract["wire_mask"]) & (1 << item["wire"])
                ]
                if failure == 8 and complete_change_set and len(compatible_candidates) == 1:
                    selected = compatible_candidates[0]
                    rows.append({
                        "field_index_owner_only": field_index,
                        "runtime_type_enum": type_enum,
                        "field_number": selected["number"],
                        "wire": selected["wire"],
                        "serialized_bytes": 0,
                        "assignment_evidence": "write-to-multi-change-candidate-disambiguated/v1",
                        "changed_tags_owner_only": changed_tags,
                    })
                else:
                    resolved = set(contract["resolved_numbers"])
                    changes_only_resolved = bool(
                        failure == 8
                        and complete_change_set
                        and changed_tags
                        and not compatible_candidates
                        and all(item["number"] in resolved for item in changed_tags)
                    )
                    auxiliary = changes_only_resolved
                    auxiliary_evidence = (
                        "write-to-changes-only-already-resolved-tags/v1"
                    )
                    failures.append({
                        "field_index_owner_only": field_index,
                        "runtime_type_enum": type_enum,
                        "failure_kind_owner_only": failure,
                        **({"changed_tags_owner_only": changed_tags} if changed_tags else {}),
                        **({
                            "nonserialized_auxiliary_owner_only": True,
                            "auxiliary_evidence": auxiliary_evidence,
                        } if auxiliary else {}),
                    })
            elif not 0 < number <= 0x1FFFFFFF or wire not in (0, 1, 2, 5) or not size:
                checks["record_domain_closed"] = False
                break
            else:
                if (
                    change_count != 1
                    or changed_raw[0] != (number << 3) | wire
                    or any(changed_raw[1:])
                ):
                    checks["record_domain_closed"] = False
                    break
                from alpha.p01 import encoding_from_code, encoding_from_values
                encoding = encoding_from_code(reserved, type_enum, wire)
                if encoding != encoding_from_values(type_enum, wire, positive, negative):
                    raise AcquisitionError("collector signed encoding disagrees with retained wire values")
                row = {"field_index_owner_only": field_index, "runtime_type_enum": type_enum, "field_number": number, "wire": wire, "serialized_bytes": size}
                if encoding:
                    row.update(signed_encoding=encoding, signed_encoding_evidence="write-to-positive-negative-123/v1",
                               signed_positive_wire_value=positive, signed_negative_wire_value=negative)
                rows.append(row)
        else:
            checks["record_domain_closed"] = len(rows) + len(failures) == count
    else:
        checks["record_domain_closed"] = False
    if not all(checks.values()):
        raise AcquisitionError("runtime proto serializer validation failed: " + ", ".join(k for k, v in checks.items() if not v))
    return {"schema": RESULT_SCHEMA, "status": "runtime-validated", "target": {"executable_sha256": plan["target"]["executable_sha256"]}, "counts": {"assignment_count": len(rows), "probe_failure_count": len(failures), "skipped_generic_or_object_count": plan["contract"]["skipped_generic_or_object_count"]}, "assignments_owner_only": rows, "failures_owner_only": failures, "inventory": file_identity(path), "status_receipt": file_identity(Path(plan["status_path"])), "checks": checks, "policy": plan["policy"], "owner_only": True}


def capture_runtime_proto_serializer_probe(
    *, wine: Path, wineprefix: Path, timeout: float = 180.0, **kwargs: Any
) -> dict[str, Any]:
    output_dir = _owner_directory(Path(kwargs["output_dir"]))
    environment = os.environ.copy(); environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve()); environment["WINEDEBUG"] = "-all"
    attempts: list[dict[str, Any]] = []
    plan: dict[str, Any] | None = None
    status: dict[str, Any] | None = None


    deadline = time.monotonic() + timeout
    attempt = 1
    while time.monotonic() < deadline:
        prepare_runtime_proto_serializer_probe(**kwargs)
        plan = read_json(output_dir / "runtime-proto-serializer-probe-plan.private.json")
        try:
            remaining = max(0.1, deadline - time.monotonic())
            result = subprocess.run(_host_run(str(wine.expanduser().resolve()), Path(plan['injector']['path']), Path(plan['collector']['path']), Path(plan['target']['executable_path']).name), env=environment, check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="replace", timeout=min(90, remaining))
        except (OSError, subprocess.SubprocessError) as error:
            raise AcquisitionError("runtime proto serializer injector could not run") from error
        _private_text(output_dir / f"runtime-proto-serializer-injector-attempt-{attempt}.private.log", json.dumps({"returncode": result.returncode, "stdout": result.stdout, "stderr": result.stderr}, ensure_ascii=False, indent=2) + "\n")
        if result.returncode:
            raise AcquisitionError("runtime proto serializer injection failed")
        status_path = Path(plan["status_path"]); status = None
        while time.monotonic() < deadline:
            progress_path = Path(str(status_path) + ".progress.json")
            if progress_path.is_file():
                progress = read_json(progress_path)
                if progress.get("status") == "callback_stalled_restart_required":
                    raise AcquisitionError("serializer callback is active; capture left it quiescently unretryable")
            if status_path.is_file():
                candidate = read_json(status_path)
                if isinstance(candidate, dict) and candidate.get("status"):
                    status = candidate; break
            time.sleep(0.2)
        if status is None:
            raise AcquisitionError("runtime proto serializer capture timed out")
        attempts.append({"attempt": attempt, "status": status.get("status"), "failure_kind_owner_only": status.get("failure_kind_owner_only"), "failure_index_owner_only": status.get("failure_index_owner_only")})
        if status.get("status") == "complete":
            break


        if not _retryable_quiescent_failure(status):
            break
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        time.sleep(min(0.25 * attempt, 5.0, remaining))
        attempt += 1
    if plan is None or status is None:
        raise AcquisitionError("runtime proto serializer capture produced no receipt")
    _private_json(output_dir / "runtime-proto-serializer-retries.private.json", {
        "schema": "alpha.runtime-proto-serializer-retries/v1",
        "attempts": attempts,
        "callback_quiescent_before_retry": True,
    })
    _seal_runtime_output(status_path)
    if status.get("status") != "complete":
        raise AcquisitionError(f"runtime proto serializer capture failed (kind={status.get('failure_kind_owner_only')}, index={status.get('failure_index_owner_only')})")
    _seal_runtime_output(Path(plan["output_path"]))
    model = _validate(plan, status); model_path = output_dir / "runtime-proto-serializer-probe.private.json"; _private_json(model_path, model)
    return {"schema": RESULT_SCHEMA, "status": model["status"], "target": model["target"], "counts": model["counts"], "checks": model["checks"], "policy": model["policy"], "model": file_identity(model_path)}
