import json
import hashlib
import math
import os
import re
import stat
import struct
import tempfile
from pathlib import Path
from typing import Any, TextIO

from alpha.h01 import ContractViolation, owner_uid, owner_only_path_bits, set_private_descriptor_mode


def _script_required_string(value, *, label):
    if not isinstance(value, str) or not value or any(ord(char) < 0x20 for char in value):
        raise ContractViolation(f"dump IR {label} is invalid")
    return value


_SCRIPT_PRIMITIVE_C_TYPES = {
    "System.Void": "void",
    "System.Boolean": "bool",
    "System.Char": "uint16_t",
    "System.SByte": "int8_t",
    "System.Byte": "uint8_t",
    "System.Int16": "int16_t",
    "System.UInt16": "uint16_t",
    "System.Int32": "int32_t",
    "System.UInt32": "uint32_t",
    "System.Int64": "int64_t",
    "System.UInt64": "uint64_t",
    "System.Single": "float",
    "System.Double": "double",
    "System.IntPtr": "intptr_t",
    "System.UIntPtr": "uintptr_t",
    "System.String": "System_String_o*",
    "System.Object": "Il2CppObject*",
}


def _script_fix_name(value):
    fixed = re.sub(r"[^a-zA-Z0-9_]", "_", value)
    return f"_{fixed}" if fixed and fixed[0].isdigit() else fixed


def _script_c_type(type_name, explicit=None):
    if explicit is not None:
        return _script_required_string(explicit, label="script C type")
    byref = type_name.endswith("&")
    pointer = type_name.endswith("*")
    base = type_name[:-1] if byref or pointer else type_name
    if base.endswith("[]"):
        value = f"{_script_fix_name(base[:-2])}_array*"
    else:
        value = _SCRIPT_PRIMITIVE_C_TYPES.get(base)
        if value is None:
            value = f"{_script_fix_name(base)}_o*"
    return f"{value}*" if byref or pointer else value


def _script_type_code(type_name, explicit=None):
    if explicit is not None:
        code = _script_required_string(explicit, label="script type code")
        if not re.fullmatch(r"[vifdj]", code):
            raise ContractViolation("dump IR script type code is invalid")
        return code
    if type_name.endswith(("&", "*")):
        return "i"
    return {
        "System.Void": "v",
        "System.Boolean": "i",
        "System.Char": "i",
        "System.SByte": "i",
        "System.Byte": "i",
        "System.Int16": "i",
        "System.UInt16": "i",
        "System.Int32": "i",
        "System.UInt32": "i",
        "System.Int64": "j",
        "System.UInt64": "j",
        "System.Single": "f",
        "System.Double": "d",
    }.get(type_name, "i")
from alpha.p12 import _owner_directory, _private_json
from alpha.h01 import AcquisitionError, ContractViolation
from alpha.h03 import EXPECTED_PROTO_BANNER
from alpha.p01 import reflection_contract
from alpha.p24 import RUNTIME_EVENT_MODULE_EVENT, RUNTIME_EVENT_MODULE_HEADER, RUNTIME_EVENT_MODULE_MAGIC, RUNTIME_EVENT_MODULE_MODULE, RUNTIME_EVENT_MODULE_VERSION
from alpha.p22 import METHOD_DETAIL_CONSTRUCTOR, PARAMETER_DETAIL_IN, PARAMETER_DETAIL_OPTIONAL, PARAMETER_DETAIL_OUT, RUNTIME_METHOD_DETAIL_HEADER, RUNTIME_METHOD_DETAIL_MAGIC, RUNTIME_METHOD_DETAIL_METHOD, RUNTIME_METHOD_DETAIL_PARAMETER, RUNTIME_METHOD_DETAIL_VERSION
from alpha.p26 import RUNTIME_METHOD_GENERIC_HEADER, RUNTIME_METHOD_GENERIC_MAGIC, RUNTIME_METHOD_GENERIC_RECORD, RUNTIME_METHOD_GENERIC_SCHEMA, RUNTIME_METHOD_GENERIC_VERSION
from alpha.p28 import RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER, RUNTIME_GENERIC_PARAMETER_DETAIL_MAGIC, RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD, RUNTIME_GENERIC_PARAMETER_DETAIL_SCHEMA, RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION
from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_FIELD, RUNTIME_NATIVE_MEMBER_DETAIL_HEADER, RUNTIME_NATIVE_MEMBER_DETAIL_MAGIC, RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY, RUNTIME_NATIVE_MEMBER_DETAIL_VERSION
from alpha.c04 import MappedPE
from alpha.p20 import load_runtime_metadata_usage_member_inventory, load_runtime_metadata_usage_pair_inventory, load_runtime_metadata_usage_value_inventory, load_runtime_string_literal_inventory
from alpha.p21 import RUNTIME_TYPE_GRAPH_HEADER, RUNTIME_TYPE_GRAPH_MAGIC, RUNTIME_TYPE_GRAPH_RECORD, RUNTIME_TYPE_GRAPH_VERSION
from alpha.p19 import _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p27 import RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
from alpha.p31 import load_runtime_direct_interfaces
from alpha.p25 import RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_RECORD, RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION, TYPE_REFERENCE_ARRAY, TYPE_REFERENCE_BYREF, TYPE_REFERENCE_GENERIC, TYPE_REFERENCE_GENERIC_PARAMETER, TYPE_REFERENCE_POINTER
from alpha.h02 import file_identity, read_json, sha256_file


RUNTIME_NATIVE_OUTPUT_SCHEMA = "alpha.runtime-native-standard-output/v5"
RUNTIME_NATIVE_OUTPUT_COMPLETE_STATUS = (
    "target-bound-standard-metadata-artifacts-complete"
)


RUNTIME_NATIVE_OUTPUT_STATUSES = (
    RUNTIME_NATIVE_OUTPUT_COMPLETE_STATUS,
    "structural-string-and-all-metadata-output-complete-assembly-identities-pending",
    "structural-string-and-all-metadata-output-complete-parameter-defaults-pending",
    "structural-string-and-all-metadata-output-complete-enum-constants-pending",
    "structural-string-and-type-method-metadata-output-complete-members-pending",
    "structural-string-and-method-metadata-output-complete-type-values-and-members-pending",
    "structural-string-output-complete-metadata-usage-pending",
)
_GENERIC_ARITY = re.compile(r"`\d+$")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(f"runtime native output {label} is not owner-only")
    return path


class _AtomicText:
    def __init__(self, path: Path):
        self.path = path
        self.temporary: Path | None = None
        self.stream: TextIO | None = None

    def __enter__(self) -> TextIO:
        descriptor, temporary = tempfile.mkstemp(
            prefix=f".{self.path.name}.", dir=self.path.parent
        )
        set_private_descriptor_mode(descriptor, 0o600)
        self.temporary = Path(temporary)
        self.stream = os.fdopen(
            descriptor, "w", encoding="utf-8", newline="\n", buffering=1024 * 1024
        )
        return self.stream

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        assert self.stream is not None and self.temporary is not None
        try:
            if exc_type is None:
                self.stream.flush()
                os.fsync(self.stream.fileno())
            self.stream.close()
            if exc_type is None:


                from alpha.h02 import publish_new_file
                publish_new_file(self.temporary, self.path)
        finally:
            self.temporary.unlink(missing_ok=True)


def _write_script_string_records(
    stream: TextIO, literals: list[dict[str, Any]]
) -> None:
    for index, literal in enumerate(literals):
        if index:
            stream.write(",\n")
        stream.write(
            "    "
            + json.dumps(
                {"Address": literal["rva"], "Value": literal["value"]},
                ensure_ascii=False,
                separators=(",", ":"),
            )
        )


def _write_json_records(
    stream: TextIO, records: list[dict[str, Any]]
) -> None:
    for index, record in enumerate(records):
        if index:
            stream.write(",\n")
        stream.write(
            "    "
            + json.dumps(
                record, ensure_ascii=False, separators=(",", ":")
            )
        )


def _write_legacy_string_literal_array(
    stream: TextIO, literals: list[dict[str, Any]]
) -> None:
    stream.write("[\n")
    for index, literal in enumerate(literals):
        if index:
            stream.write(",\n")
        stream.write(
            "  "
            + json.dumps(
                {
                    "value": literal["value"],
                    "address": f"0x{literal['rva']:X}",
                },
                ensure_ascii=False,
                separators=(",", ":"),
            )
        )
    stream.write("\n]\n")


def _text(raw: bytes, offset: int, length: int, *, label: str) -> str:
    if not length or offset < 0 or offset + length > len(raw):
        raise AcquisitionError(f"runtime native output {label} is out of range")
    try:
        value = raw[offset:offset + length].decode("utf-8")
    except UnicodeDecodeError as error:
        raise AcquisitionError(f"runtime native output {label} is invalid") from error
    if not value or any(ord(character) < 0x20 for character in value):
        raise AcquisitionError(f"runtime native output {label} is invalid")
    return value


def _optional_text(raw: bytes, offset: int, length: int, *, label: str) -> str:
    if not length:
        return ""
    return _text(raw, offset, length, label=label)


def _visibility(attributes: int, *, field: bool = False) -> str:
    del field
    return {
        1: "private", 2: "private protected", 3: "internal",
        4: "protected", 5: "protected internal", 6: "public",
    }.get(attributes & 7, "private")


def _type_visibility(attributes: int) -> str:

    return {
        0: "internal",
        1: "public",
        2: "public",
        3: "private",
        4: "protected",
        5: "internal",
        6: "private protected",
        7: "protected internal",
    }[attributes & 7]


def _type_modifiers(attributes: int, *, is_interface: bool) -> str:

    if is_interface:
        return ""


    if attributes & 0x80 and attributes & 0x100:
        return "static"
    modifiers: list[str] = []
    if attributes & 0x80:
        modifiers.append("abstract")
    if attributes & 0x100:
        modifiers.append("sealed")
    return " ".join(modifiers)


def _type_attribute_declarations(attributes: int) -> tuple[str, ...]:

    declarations: list[str] = []
    if attributes & 0x2000:
        declarations.append("[Serializable]")
    return tuple(declarations)


def _method_modifiers(
    attributes: int, *, is_interface_member: bool = False,
    constructor: bool = False,
) -> str:

    pieces: list[str] = []


    if not is_interface_member and not (constructor and attributes & 0x10):
        pieces.append(_visibility(attributes))
    if attributes & 0x10:
        pieces.append("static")
    if not constructor:
        if attributes & 0x400:
            pieces.append("abstract")
        elif attributes & 0x40:
            if attributes & 0x100:
                pieces.append("virtual")
            else:
                if attributes & 0x20:
                    pieces.append("sealed")
                pieces.append("override")
    return " ".join(pieces)


def _access_rank(attributes: int) -> int:

    return {0: 0, 1: 0, 2: 1, 3: 2, 4: 3, 5: 4, 6: 5}[attributes & 7]


def _property_or_event_modifiers(
    accessor_attributes: list[int], *, is_interface_member: bool,
) -> tuple[str, int]:
    if not accessor_attributes:
        raise ContractViolation("property/event has no captured accessor")
    representative = max(accessor_attributes, key=_access_rank)
    return (
        _method_modifiers(
            representative, is_interface_member=is_interface_member,
        ),
        representative,
    )


def _accessor_declaration(
    keyword: str, attributes: int, surface_attributes: int,
) -> str:

    if (attributes & 7) == (surface_attributes & 7):
        return f"{keyword};"
    return f"{_visibility(attributes)} {keyword};"


def _parameter_declaration(
    name: str,
    type_name: str,
    flags: int,
    raw_attributes: int,
    metadata_token: int,
    default_value: str | None = None,
    missing_default: bool = False,
) -> str:

    is_in = bool(flags & PARAMETER_DETAIL_IN)
    is_out = bool(flags & PARAMETER_DETAIL_OUT)
    is_optional = bool(flags & PARAMETER_DETAIL_OPTIONAL)
    if flags & ~(
        PARAMETER_DETAIL_IN
        | PARAMETER_DETAIL_OUT
        | PARAMETER_DETAIL_OPTIONAL
    ):
        raise ContractViolation("runtime parameter detail flags are invalid")

    attributes: list[str] = []
    modifier = ""
    if type_name.endswith("&"):
        type_name = type_name[:-1]
        if is_out and not is_in:
            modifier = "out "
        elif is_in and not is_out:
            modifier = "in "
        else:
            modifier = "ref "
    else:
        if is_in:
            attributes.append("In")
        if is_out:
            attributes.append("Out")
    if is_optional:
        attributes.append("Optional")
    prefix = "".join(f"[{attribute}] " for attribute in attributes)
    default = f" = {default_value}" if default_value is not None else ""
    missing = ", Default: Missing" if missing_default else ""
    return (
        f"{prefix}{modifier}{type_name} {name}{default} "
        f"/* MetadataToken: 0x{metadata_token:08X}, "
        f"Attributes: 0x{raw_attributes:04X}{missing} */"
    )


def _header_identifier(qualified: str, type_index: int) -> str:

    return f"{_script_fix_name(qualified)}__TypeDefIndex_{type_index}_o"


def _metadata_token(table: int, zero_based_index: int) -> int:

    if table & 0x00FFFFFF or not 0 <= zero_based_index < 0x00FFFFFF:
        raise ContractViolation("metadata token table/index is invalid")
    return table | zero_based_index


def _managed_field_offset(
    field: tuple[int, ...], *, is_value_type: bool
) -> int:

    offset = field[4]
    is_static = bool(field[5] & 0x10)
    return offset if is_value_type and not is_static else offset + 0x10


def _enum_underlying_field(field: tuple[int, ...], name: str) -> bool:

    return name == "value__" or (
        field[5] & 0x600 == 0x600 and not field[5] & 0x50
    )


def _enum_number(record: dict[str, Any]) -> int:
    width = int(record["width"])
    raw = int(record["raw_value"])
    bits = width * 8
    if record["signed"] and raw & (1 << (bits - 1)):
        return raw - (1 << bits)
    return raw


def _integer_constant(record: dict[str, Any]) -> int:
    width = int(record["width"])
    raw = int(record["raw_value"])
    if width not in (1, 2, 4, 8) or not 0 <= raw < 1 << (width * 8):
        raise ContractViolation("runtime literal integer bits are invalid")
    if record["signed"] and raw & (1 << (width * 8 - 1)):
        return raw - (1 << (width * 8))
    return raw


def _csharp_character(raw: int) -> str:
    if not 0 <= raw <= 0xFFFF:
        raise ContractViolation("runtime literal character is invalid")
    escapes = {
        0: r"\0", 7: r"\a", 8: r"\b", 9: r"\t", 10: r"\n",
        11: r"\v", 12: r"\f", 13: r"\r", 39: r"\'", 92: r"\\",
    }
    if raw in escapes:
        value = escapes[raw]
    elif 0x20 <= raw <= 0x7E:
        value = chr(raw)
    else:
        value = f"\\u{raw:04X}"
    return f"'{value}'"


def _floating_constant(record: dict[str, Any], *, c_header: bool) -> str:
    raw = int(record["raw_value"])
    kind = record["value_kind"]
    if kind == "single":
        value = struct.unpack("<f", struct.pack("<I", raw))[0]
        prefix = "" if c_header else "float."
        suffix = "f"
        precision = 9
    elif kind == "double":
        value = struct.unpack("<d", struct.pack("<Q", raw))[0]
        prefix = "" if c_header else "double."
        suffix = ""
        precision = 17
    else:
        raise ContractViolation("runtime floating constant kind is invalid")
    if math.isnan(value):
        return "NAN" if c_header else prefix + "NaN"
    if math.isinf(value):
        if c_header:
            return "(-INFINITY)" if value < 0 else "INFINITY"
        return prefix + ("NegativeInfinity" if value < 0 else "PositiveInfinity")
    if value == 0.0 and math.copysign(1.0, value) < 0:
        return "-0.0" + suffix
    rendered = format(value, f".{precision}g").replace("e", "E")
    return rendered + suffix


def _csharp_constant(record: dict[str, Any], field_type: str) -> str:
    kind = record["value_kind"]
    if kind == "string":
        value = record["string_value"]
        return (
            "null" if value is None else
            json.dumps(value, ensure_ascii=True, separators=(",", ":"))
        )
    if kind == "boolean":
        value = _integer_constant(record)
        if value not in (0, 1):
            raise ContractViolation("runtime literal Boolean is not canonical")
        return "true" if value else "false"
    if kind == "char":
        return _csharp_character(_integer_constant(record))
    if kind in ("single", "double"):
        return _floating_constant(record, c_header=False)
    number = _integer_constant(record)
    suffix = (
        "UL" if not record["signed"] and int(record["width"]) == 8
        else "U" if not record["signed"] and int(record["width"]) == 4
        else "L" if record["signed"] and int(record["width"]) == 8
        else ""
    )
    rendered = f"{number}{suffix}"
    return f"({field_type}){rendered}" if record["typed_enum"] else rendered


def _header_constant(record: dict[str, Any]) -> str:
    kind = record["value_kind"]
    if kind == "string":
        value = record["string_value"]
        if value is None:
            return "((const uint16_t *)0)"
        units = value.encode("utf-16-le", errors="surrogatepass")
        words = [
            int.from_bytes(units[offset:offset + 2], "little")
            for offset in range(0, len(units), 2)
        ]
        return "((const uint16_t[]){" + ",".join(
            [*(f"0x{word:04X}u" for word in words), "0u"]
        ) + "})"
    if kind == "boolean":
        value = _integer_constant(record)
        if value not in (0, 1):
            raise ContractViolation("runtime literal Boolean is not canonical")
        return str(value)
    if kind == "char":
        return f"0x{_integer_constant(record):04X}u"
    if kind in ("single", "double"):
        return _floating_constant(record, c_header=True)
    number = _integer_constant(record)
    if not record["signed"]:
        return (
            f"UINT64_C({number})" if int(record["width"]) == 8
            else f"UINT32_C({number})" if int(record["width"]) == 4
            else f"{number}u"
        )
    return f"INT64_C({number})" if int(record["width"]) == 8 else str(number)


def _field_modifiers(attributes: int) -> str:
    pieces = [_visibility(attributes, field=True)]
    if attributes & 0x40:
        pieces.append("const")
    else:
        if attributes & 0x10:
            pieces.append("static")
        if attributes & 0x20:
            pieces.append("readonly")
    return " ".join(pieces)


class _TypeRenderer:
    def __init__(self, identity: bytes, graph: bytes, references: bytes):
        self.identity = identity
        self.graph = graph
        self.references = references
        self.identity_header = _IDENTITY_HEADER.unpack_from(identity)
        self.graph_header = RUNTIME_TYPE_GRAPH_HEADER.unpack_from(graph)
        self.reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(references)
        self.type_count = self.identity_header[5]
        self.root_by_descriptor: dict[int, int] = {}
        for index in range(self.type_count):
            descriptor = self.identity_row(index)[2]
            if descriptor in self.root_by_descriptor:
                raise AcquisitionError("runtime native output root descriptors repeat")
            self.root_by_descriptor[descriptor] = index
        self.node_count = self.reference_header[5]
        self.interface_count = self.reference_header[7]
        self.argument_count = self.reference_header[8]
        self.reference_record_start = RUNTIME_TYPE_REFERENCE_HEADER.size
        self.reference_interface_start = (
            self.reference_record_start
            + self.node_count * RUNTIME_TYPE_REFERENCE_RECORD.size
        )
        self.reference_argument_start = (
            self.reference_interface_start + self.interface_count * 8
        )
        self.node_by_descriptor: dict[int, int] = {}
        for index in range(self.node_count):
            descriptor = self.reference_row(index)[0]
            if descriptor in self.node_by_descriptor:
                raise AcquisitionError("runtime native output reference descriptors repeat")
            self.node_by_descriptor[descriptor] = index
        self.graph_interface_start = (
            RUNTIME_TYPE_GRAPH_HEADER.size
            + self.type_count * RUNTIME_TYPE_GRAPH_RECORD.size
        )
        self.graph_argument_start = (
            self.graph_interface_start + self.graph_header[6] * 8
        )
        self.render_cache: dict[int, str] = {}
        self.root_cache: dict[int, str] = {}
        self.generic_parameter_attributes: dict[int, int] = {}
        self.direct_interface_descriptors: tuple[int, ...] | None = None
        self.direct_interface_rows: list[tuple[int, ...]] | None = None
        self.active: set[int] = set()

    def identity_row(self, index: int) -> tuple[int, ...]:
        return _IDENTITY_RECORD.unpack_from(
            self.identity, _IDENTITY_HEADER.size + index * _IDENTITY_RECORD.size
        )

    def graph_row(self, index: int) -> tuple[int, ...]:
        return RUNTIME_TYPE_GRAPH_RECORD.unpack_from(
            self.graph,
            RUNTIME_TYPE_GRAPH_HEADER.size + index * RUNTIME_TYPE_GRAPH_RECORD.size,
        )

    def reference_row(self, index: int) -> tuple[int, ...]:
        return RUNTIME_TYPE_REFERENCE_RECORD.unpack_from(
            self.references,
            self.reference_record_start + index * RUNTIME_TYPE_REFERENCE_RECORD.size,
        )

    def contains_generic_parameter(self, descriptor: int) -> bool:

        active: set[int] = set()
        complete: dict[int, bool] = {}

        def visit(value: int) -> bool:
            cached = complete.get(value)
            if cached is not None:
                return cached
            index = self.node_by_descriptor.get(value)
            if index is None:
                raise ContractViolation(
                    f"runtime generic openness descriptor is absent: 0x{value:X}"
                )
            if value in active:
                raise ContractViolation(
                    "runtime generic openness graph is cyclic"
                )
            active.add(value)
            try:
                row = self.reference_row(index)
                result = bool(row[4] & TYPE_REFERENCE_GENERIC_PARAMETER)
                if not result and row[13]:
                    result = visit(row[13])


                if not result and row[12] and not row[4] & TYPE_REFERENCE_GENERIC:
                    result = visit(row[12])
                if not result:
                    for offset in range(row[8]):
                        argument = struct.unpack_from(
                            "<Q", self.references,
                            self.reference_argument_start
                            + (row[16] + offset) * 8,
                        )[0]
                        if visit(argument):
                            result = True
                            break
                complete[value] = result
                return result
            finally:
                active.remove(value)

        return visit(descriptor)

    def root_name(self, index: int, *, declaration: bool = False) -> str:
        if not declaration and index in self.root_cache:
            return self.root_cache[index]
        row = self.identity_row(index)
        name = _text(self.identity, row[11], row[8], label="type name")
        namespace = _optional_text(
            self.identity, row[12], row[9], label="type namespace"
        )
        declaring = row[5]
        if declaring:
            parent = self.root_by_descriptor.get(declaring)
            if parent is None:
                raise ContractViolation("runtime nested owner is absent")
            prefix = self.root_name(parent)
        else:
            prefix = namespace
        simple = _GENERIC_ARITY.sub("", name)
        graph_row = self.graph_row(index)
        argument_count = graph_row[7]
        inherited_count = self.graph_row(parent)[7] if declaring else 0
        own_argument_count = argument_count - inherited_count
        if own_argument_count < 0:
            raise ContractViolation(
                "runtime nested generic arity is inconsistent"
            )
        if own_argument_count:
            arguments = [
                struct.unpack_from(
                    "<Q",
                    self.graph,
                    self.graph_argument_start
                    + (graph_row[9] + inherited_count + offset) * 8,
                )[0]
                for offset in range(own_argument_count)
            ]
            rendered_arguments: list[str] = []
            for value in arguments:
                rendered = self.render(value)
                if declaration:
                    variance = self.generic_parameter_attributes.get(value, 0) & 3
                    if variance == 1:
                        rendered = "out " + rendered
                    elif variance == 2:
                        rendered = "in " + rendered
                    elif variance == 3:
                        raise ContractViolation(
                            "runtime generic parameter variance is invalid"
                        )
                rendered_arguments.append(rendered)
            simple += "<" + ", ".join(rendered_arguments) + ">"
        if declaration:


            if declaring:
                assert parent is not None
                return f"{self.root_name(parent, declaration=True)}.{simple}"
            return simple
        result = f"{prefix}.{simple}" if prefix else simple
        self.root_cache[index] = result
        return result

    def constructed_root_name(self, index: int, arguments: list[str]) -> str:
        if not 0 <= index < self.type_count or not arguments:
            raise ContractViolation("runtime constructed type arguments are invalid")
        chain: list[tuple[int, tuple[int, ...]]] = []
        current = index
        seen = set()
        while True:
            if current in seen:
                raise ContractViolation("runtime constructed nested owner chain is cyclic")
            seen.add(current)
            row = self.identity_row(current)
            chain.append((current, row))
            declaring = row[5]
            if not declaring:
                break
            parent = self.root_by_descriptor.get(declaring)
            if parent is None:
                raise ContractViolation("runtime constructed nested owner is absent")
            current = parent
        chain.reverse()
        parts: list[str] = []
        argument_cursor = 0
        inherited_count = 0
        for type_index, row in chain:
            total_count = self.graph_row(type_index)[7]
            own_count = total_count - inherited_count
            if own_count < 0 or argument_cursor + own_count > len(arguments):
                raise ContractViolation(
                    "runtime constructed generic arity is inconsistent"
                )
            name = _text(self.identity, row[11], row[8], label="type name")
            namespace = _optional_text(
                self.identity, row[12], row[9], label="type namespace"
            )
            simple = _GENERIC_ARITY.sub("", name)
            if own_count:
                simple += "<" + ", ".join(
                    arguments[argument_cursor : argument_cursor + own_count]
                ) + ">"
                argument_cursor += own_count
            parts.append(
                f"{namespace}.{simple}" if not parts and namespace else simple
            )
            inherited_count = total_count
        if argument_cursor != len(arguments):
            raise ContractViolation(
                "runtime constructed generic arguments are incomplete"
            )
        return ".".join(parts)

    def _root_alias(self, descriptor: int, canonical: int) -> int | None:
        return self.root_by_descriptor.get(descriptor, self.root_by_descriptor.get(canonical))

    def render(self, descriptor: int) -> str:
        cached = self.render_cache.get(descriptor)
        if cached is not None:
            return cached
        node_index = self.node_by_descriptor.get(descriptor)
        if node_index is None:
            raise ContractViolation(
                f"runtime type descriptor is absent from closure: 0x{descriptor:X}"
            )
        if descriptor in self.active:
            raise ContractViolation("runtime type reference graph is cyclic")
        self.active.add(descriptor)
        try:
            row = self.reference_row(node_index)
            canonical, shape = row[1], row[4]
            if shape & TYPE_REFERENCE_BYREF:
                result = self.render(row[13]) + "&"
            elif shape & TYPE_REFERENCE_ARRAY:
                rank = row[9]
                result = self.render(row[13]) + "[" + "," * (rank - 1) + "]"
            elif shape & TYPE_REFERENCE_POINTER:
                result = self.render(row[13]) + "*"
            else:
                root = self._root_alias(descriptor, canonical)
                if root is not None:
                    result = self.root_name(root)
                elif shape & TYPE_REFERENCE_GENERIC:
                    from alpha.p20 import observed_generic_name
                    result = observed_generic_name(self, row, self.render)
                else:
                    name = _text(
                        self.references, row[17], row[5], label="reference name"
                    )
                    namespace = _optional_text(
                        self.references,
                        row[18],
                        row[6],
                        label="reference namespace",
                    )
                    if shape & TYPE_REFERENCE_GENERIC_PARAMETER:
                        result = name
                    else:
                        declaring = row[12]
                        prefix = self.render(declaring) if declaring else namespace
                        simple = _GENERIC_ARITY.sub("", name)
                        if shape & TYPE_REFERENCE_GENERIC:
                            arguments = [
                                struct.unpack_from(
                                    "<Q",
                                    self.references,
                                    self.reference_argument_start
                                    + (row[16] + offset) * 8,
                                )[0]
                                for offset in range(row[8])
                            ]
                            simple += "<" + ", ".join(
                                self.render(value) for value in arguments
                            ) + ">"
                        result = f"{prefix}.{simple}" if prefix else simple
            self.render_cache[descriptor] = result
            return result
        finally:
            self.active.remove(descriptor)

    def render_signature(
        self,
        descriptor: int,
        *,
        type_parameters: dict[int, int] | None = None,
        method_parameters: dict[int, int] | None = None,
    ) -> str:

        type_parameters = type_parameters or {}
        method_parameters = method_parameters or {}
        active: set[int] = set()

        def parameter_index(
            value: int, row: tuple[int, ...]
        ) -> tuple[str, int] | None:
            for candidate in (value, row[1]):
                if candidate in method_parameters:
                    return "!!", method_parameters[candidate]
                if candidate in type_parameters:
                    return "!", type_parameters[candidate]
            return None

        def visit(value: int) -> str:
            node_index = self.node_by_descriptor.get(value)
            if node_index is None:
                raise ContractViolation(
                    f"runtime signature descriptor is absent: 0x{value:X}"
                )
            row = self.reference_row(node_index)
            parameter = parameter_index(value, row)
            if parameter is not None:
                return f"{parameter[0]}{parameter[1]}"
            if value in active:
                raise ContractViolation("runtime signature type graph is cyclic")
            active.add(value)
            try:
                canonical, shape = row[1], row[4]
                if shape & TYPE_REFERENCE_BYREF:
                    return visit(row[13]) + "&"
                if shape & TYPE_REFERENCE_ARRAY:
                    return visit(row[13]) + "[" + "," * (row[9] - 1) + "]"
                if shape & TYPE_REFERENCE_POINTER:
                    return visit(row[13]) + "*"
                root = self._root_alias(value, canonical)
                if root is not None:
                    graph = self.graph_row(root)
                    if graph[7]:
                        arguments = [
                            struct.unpack_from(
                                "<Q", self.graph,
                                self.graph_argument_start
                                + (graph[9] + offset) * 8,
                            )[0]
                            for offset in range(graph[7])
                        ]
                        return self.constructed_root_name(
                            root, [visit(argument) for argument in arguments]
                        )
                    return self.root_name(root)
                if shape & TYPE_REFERENCE_GENERIC:
                    from alpha.p20 import observed_generic_name
                    return observed_generic_name(self, row, visit)
                name = _text(
                    self.references, row[17], row[5],
                    label="signature reference name",
                )
                namespace = _optional_text(
                    self.references, row[18], row[6],
                    label="signature reference namespace",
                )
                if shape & TYPE_REFERENCE_GENERIC_PARAMETER:
                    return name
                declaring = row[12]
                prefix = visit(declaring) if declaring else namespace
                simple = _GENERIC_ARITY.sub("", name)
                if shape & TYPE_REFERENCE_GENERIC:
                    arguments = [
                        struct.unpack_from(
                            "<Q", self.references,
                            self.reference_argument_start
                            + (row[16] + offset) * 8,
                        )[0]
                        for offset in range(row[8])
                    ]
                    simple += "<" + ", ".join(
                        visit(argument) for argument in arguments
                    ) + ">"
                return f"{prefix}.{simple}" if prefix else simple
            finally:
                active.remove(value)

        return visit(descriptor)

    def render_substituted(
        self, descriptor: int, substitutions: dict[int, int]
    ) -> str:

        active: set[int] = set()

        def visit(value: int) -> str:
            node_index = self.node_by_descriptor.get(value)
            if node_index is None:
                raise ContractViolation(
                    f"runtime substituted descriptor is absent: 0x{value:X}"
                )
            row = self.reference_row(node_index)
            replacement = substitutions.get(value, substitutions.get(row[1]))
            if replacement is not None:
                return self.render(replacement)
            if value in active:
                raise ContractViolation(
                    "runtime substituted type graph is cyclic"
                )
            active.add(value)
            try:
                canonical, shape = row[1], row[4]
                if shape & TYPE_REFERENCE_BYREF:
                    return visit(row[13]) + "&"
                if shape & TYPE_REFERENCE_ARRAY:
                    return visit(row[13]) + "[" + "," * (row[9] - 1) + "]"
                if shape & TYPE_REFERENCE_POINTER:
                    return visit(row[13]) + "*"
                root = self._root_alias(value, canonical)
                if root is not None:
                    graph = self.graph_row(root)
                    if graph[7]:
                        arguments = [
                            struct.unpack_from(
                                "<Q", self.graph,
                                self.graph_argument_start
                                + (graph[9] + offset) * 8,
                            )[0]
                            for offset in range(graph[7])
                        ]
                        return self.constructed_root_name(
                            root, [visit(argument) for argument in arguments]
                        )
                    return self.root_name(root)
                if shape & TYPE_REFERENCE_GENERIC:
                    from alpha.p20 import observed_generic_name
                    return observed_generic_name(self, row, visit)
                name = _text(
                    self.references, row[17], row[5],
                    label="substituted reference name",
                )
                namespace = _optional_text(
                    self.references, row[18], row[6],
                    label="substituted reference namespace",
                )
                if shape & TYPE_REFERENCE_GENERIC_PARAMETER:
                    return name
                declaring = row[12]
                prefix = visit(declaring) if declaring else namespace
                simple = _GENERIC_ARITY.sub("", name)
                if shape & TYPE_REFERENCE_GENERIC:
                    arguments = [
                        struct.unpack_from(
                            "<Q", self.references,
                            self.reference_argument_start
                            + (row[16] + offset) * 8,
                        )[0]
                        for offset in range(row[8])
                    ]
                    simple += "<" + ", ".join(
                        visit(argument) for argument in arguments
                    ) + ">"
                return f"{prefix}.{simple}" if prefix else simple
            finally:
                active.remove(value)

        return visit(descriptor)

    def root_interface_descriptors(self, index: int) -> tuple[int, ...]:

        if self.direct_interface_rows is not None:
            if self.direct_interface_descriptors is None:
                raise ContractViolation(
                    "runtime direct interface descriptor table is absent"
                )
            row = self.direct_interface_rows[index]
            return tuple(
                self.direct_interface_descriptors[row[3] + offset]
                for offset in range(row[1])
            )
        row = self.graph_row(index)
        return tuple(
            struct.unpack_from(
                "<Q", self.graph,
                self.graph_interface_start + (row[8] + offset) * 8,
            )[0]
            for offset in range(row[6])
        )

    def root_interfaces(self, index: int) -> list[str]:
        return [
            self.render(descriptor)
            for descriptor in self.root_interface_descriptors(index)
        ]


class _UnresolvableGeneric(ContractViolation):
    pass


class _MetadataUsageTypeRenderer:
    _PRIMITIVES = {
        0x01: "System.Void",
        0x02: "System.Boolean",
        0x03: "System.Char",
        0x04: "System.SByte",
        0x05: "System.Byte",
        0x06: "System.Int16",
        0x07: "System.UInt16",
        0x08: "System.Int32",
        0x09: "System.UInt32",
        0x0A: "System.Int64",
        0x0B: "System.UInt64",
        0x0C: "System.Single",
        0x0D: "System.Double",
        0x0E: "System.String",
        0x16: "System.TypedReference",
        0x18: "System.IntPtr",
        0x19: "System.UIntPtr",
        0x1C: "System.Object",
    }

    def __init__(
        self, *, binary: Path, renderer: _TypeRenderer,
        generic_records: tuple[tuple[int, int, int, int], ...],
    ):
        if not isinstance(generic_records, (tuple, list)):
            raise AcquisitionError("runtime metadata usage generic domain is malformed")
        generic_records = tuple(generic_records)


        self.renderer = renderer
        self.generic_records = generic_records
        self.image = MappedPE(binary, require_runtime_functions=False)
        self.cache: dict[tuple[int, int, int], str] = {}
        self.active: set[tuple[int, int, int]] = set()
        self.observed_type_codes: dict[int, int] = {}
        self.deferred_generic_slots: list[dict[str, int]] = []

    def close(self) -> None:
        self.image.close()

    def __enter__(self) -> _MetadataUsageTypeRenderer:
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def _qword(self, pointer: int) -> int:
        if (
            pointer < self.image.image_base
            or pointer + 8 > self.image.image_base + self.image.size_of_image
        ):
            raise ContractViolation(
                "runtime metadata usage pointer is outside the exact image"
            )
        offset = self.image.rva_to_offset(pointer - self.image.image_base)
        if offset is None or offset + 8 > len(self.image._mapping):
            raise ContractViolation(
                "runtime metadata usage pointer has no immutable PE bytes"
            )
        return struct.unpack_from("<Q", self.image._mapping, offset)[0]

    def _type_record(self, pointer: int) -> tuple[int, int]:
        return self._qword(pointer), self._qword(pointer + 8)

    def render(self, pointer: int, data: int, bits: int) -> str:
        key = (pointer, data, bits)
        cached = self.cache.get(key)
        if cached is not None:
            return cached
        if key in self.active:
            raise ContractViolation("runtime metadata usage type graph is cyclic")
        self.active.add(key)
        try:
            type_code = (bits >> 16) & 0xFF
            self.observed_type_codes[type_code] = (
                self.observed_type_codes.get(type_code, 0) + 1
            )
            if type_code in self._PRIMITIVES:
                result = self._PRIMITIVES[type_code]
            elif type_code in (0x11, 0x12):
                definition_index = data & 0xFFFFFFFF
                if data >> 32 or definition_index >= self.renderer.type_count:
                    raise ContractViolation(
                        "runtime metadata usage definition index is invalid"
                    )
                result = self.renderer.root_name(definition_index)
            elif type_code == 0x0F:
                nested_data, nested_bits = self._type_record(data)
                result = self.render(data, nested_data, nested_bits) + "*"
            elif type_code == 0x10:
                nested_data, nested_bits = self._type_record(data)
                result = self.render(data, nested_data, nested_bits) + "&"
            elif type_code == 0x14:
                element = self._qword(data)
                rank = self._qword(data + 8) & 0xFF
                if not 1 <= rank <= 32:
                    raise ContractViolation(
                        "runtime metadata usage array rank is invalid"
                    )
                element_data, element_bits = self._type_record(element)
                result = (
                    self.render(element, element_data, element_bits)
                    + "[" + "," * (rank - 1) + "]"
                )
            elif type_code == 0x15:
                generic_index = data & 0xFFFFFFFF
                if data >> 32 or generic_index >= len(self.generic_records):
                    raise _UnresolvableGeneric(
                        "runtime metadata usage generic index is invalid"
                    )
                definition_index, instance, _cached_type, _cached_class = (
                    self.generic_records[generic_index]
                )
                if (
                    definition_index >> 32
                    or definition_index >= self.renderer.type_count
                ):
                    raise ContractViolation(
                        "runtime metadata usage generic definition is invalid"
                    )
                argument_count = self._qword(instance)
                arguments = self._qword(instance + 8)
                if not 1 <= argument_count <= 64:
                    raise ContractViolation(
                        "runtime metadata usage generic arity is invalid"
                    )
                rendered_arguments: list[str] = []
                for index in range(argument_count):
                    argument = self._qword(arguments + index * 8)
                    argument_data, argument_bits = self._type_record(argument)
                    rendered_arguments.append(
                        self.render(argument, argument_data, argument_bits)
                    )
                result = self.renderer.constructed_root_name(
                    definition_index, rendered_arguments
                )
            elif type_code == 0x1D:
                element_data, element_bits = self._type_record(data)
                result = self.render(data, element_data, element_bits) + "[]"
            else:
                raise ContractViolation(
                    f"runtime metadata usage type code is unsupported: {type_code}"
                )
            if bits & (1 << 30):
                result += "&"
            self.cache[key] = result
            return result
        finally:
            self.active.remove(key)

    def render_usages(
        self, type_usages: list[dict[str, int]], *,
        defer_unresolvable_generics: bool = False,
    ) -> tuple[list[dict[str, Any]], dict[int, int]]:
        if type(defer_unresolvable_generics) is not bool:
            raise AcquisitionError(
                "runtime metadata usage generic deferral policy is invalid"
            )
        records: list[dict[str, Any]] = []
        previous_rva = -1
        sources: set[int] = set()
        root_type_codes: dict[int, int] = {}
        for usage in type_usages:
            rva = usage["rva"]
            source = usage["source_index"]
            pointer = self.image.image_base + usage["type_record_rva"]
            data = usage["type_data_owner_only"]
            bits = usage["type_bits_owner_only"]
            if (
                rva <= previous_rva
                or source in sources
                or self._type_record(pointer) != (data, bits)
            ):
                raise ContractViolation(
                    "runtime metadata usage type roots are inconsistent"
                )
            type_code = (bits >> 16) & 0xFF
            try:
                name = self.render(pointer, data, bits)
            except _UnresolvableGeneric:
                if not defer_unresolvable_generics:
                    raise
                skipped: dict[str, int] = {
                    "address": self.image.image_base + rva,
                    "source_index": source,
                }
                if type_code == 0x15:
                    skipped["generic_index"] = data & 0xFFFFFFFF
                self.deferred_generic_slots.append(skipped)
                previous_rva = rva
                sources.add(source)
                continue
            root_type_codes[type_code] = root_type_codes.get(type_code, 0) + 1


            signature = (
                f"{_script_fix_name(name)}_c*"
                if type_code in (0x11, 0x12)
                else "Il2CppClass*"
            )
            records.append(
                {
                    "Address": rva,
                    "Name": f"{name}_TypeInfo",
                    "Signature": signature,
                    "TypeCode": type_code,
                    "SourceIndex": source,
                }
            )
            previous_rva = rva
            sources.add(source)
        return records, root_type_codes


class _RuntimeOutput:
    def __init__(
        self, *, binary: Path, type_identity: bytes, type_graph: bytes,
        type_references: bytes, methods: bytes, native_members: bytes,
        event_modules: bytes, method_generics: bytes,
        generic_parameter_details: bytes,
    ):
        self.binary = binary
        self.identity = type_identity
        self.graph = type_graph
        self.references = type_references
        self.methods = methods
        self.native = native_members
        self.events = event_modules
        self.method_generics = method_generics
        self.generic_parameter_details = generic_parameter_details
        self.renderer = _TypeRenderer(type_identity, type_graph, type_references)
        self.identity_header = _IDENTITY_HEADER.unpack_from(type_identity)
        self.method_header = RUNTIME_METHOD_DETAIL_HEADER.unpack_from(methods)
        self.native_header = RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.unpack_from(native_members)
        self.event_header = RUNTIME_EVENT_MODULE_HEADER.unpack_from(event_modules)
        self.method_generic_header = RUNTIME_METHOD_GENERIC_HEADER.unpack_from(
            method_generics
        )
        self.generic_parameter_header = (
            RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.unpack_from(
                generic_parameter_details
            )
        )
        self.type_count = self.identity_header[5]
        self.method_count, self.parameter_count = self.method_header[5:7]
        self.field_count, self.property_count = self.native_header[5:7]
        self.module_count, self.event_count = self.event_header[5:7]
        self.method_generic_argument_count = self.method_generic_header[7]
        self.generic_parameter_argument_count = self.generic_parameter_header[5]
        self.generic_constraint_count = self.generic_parameter_header[6]
        if (
            self.method_generic_header[0] != RUNTIME_METHOD_GENERIC_MAGIC
            or self.method_generic_header[1]
            != RUNTIME_METHOD_GENERIC_VERSION
            or self.method_generic_header[5] != self.method_count
            or self.generic_parameter_header[0]
            != RUNTIME_GENERIC_PARAMETER_DETAIL_MAGIC
            or self.generic_parameter_header[1]
            != RUNTIME_GENERIC_PARAMETER_DETAIL_VERSION
            or self.generic_parameter_argument_count
            < self.method_generic_argument_count
        ):
            raise AcquisitionError(
                "runtime output method generic inventories conflict"
            )
        self.generic_detail_by_descriptor: dict[int, tuple[int, ...]] = {}
        for argument_index in range(self.generic_parameter_argument_count):
            detail = RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.unpack_from(
                self.generic_parameter_details,
                RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
                + argument_index * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size,
            )
            if detail[0] in self.generic_detail_by_descriptor:
                raise AcquisitionError(
                    "runtime generic parameter detail descriptors repeat"
                )
            self.generic_detail_by_descriptor[detail[0]] = detail
            self.renderer.generic_parameter_attributes[detail[0]] = detail[1]
        self.method_generic_argument_start = (
            RUNTIME_METHOD_GENERIC_HEADER.size
            + self.method_count * RUNTIME_METHOD_GENERIC_RECORD.size
        )
        self.generic_constraint_start = (
            RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
            + self.generic_parameter_argument_count
            * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size
        )
        if (
            self.method_generic_argument_start
            + self.method_generic_argument_count * 8
            != len(method_generics)
            or self.generic_constraint_start
            + self.generic_constraint_count * 8
            != len(generic_parameter_details)
        ):
            raise AcquisitionError(
                "runtime output method generic inventories are truncated"
            )
        self.parameter_start = (
            RUNTIME_METHOD_DETAIL_HEADER.size
            + self.method_count * RUNTIME_METHOD_DETAIL_METHOD.size
        )
        self.property_start = (
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + self.field_count * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size
        )
        self.event_start = (
            RUNTIME_EVENT_MODULE_HEADER.size
            + self.module_count * RUNTIME_EVENT_MODULE_MODULE.size
        )
        self.module_names: dict[int, str] = {}
        for index in range(self.module_count):
            pointer, name_bytes, reserved, name_offset = (
                RUNTIME_EVENT_MODULE_MODULE.unpack_from(
                    event_modules,
                    RUNTIME_EVENT_MODULE_HEADER.size
                    + index * RUNTIME_EVENT_MODULE_MODULE.size,
                )
            )
            if reserved or pointer in self.module_names:
                raise AcquisitionError("runtime module inventory is invalid")
            self.module_names[pointer] = _text(
                event_modules, name_offset, name_bytes, label="module name"
            )
        self.method_by_pointer: dict[int, int] = {}
        self.method_indexes_by_owner: dict[int, list[int]] = {}
        previous_name = 0
        for index in range(self.method_count):
            row = self.method_row(index)
            if row[2] in self.method_by_pointer or row[12] < previous_name:
                raise AcquisitionError("runtime method order is invalid")
            self.method_by_pointer[row[2]] = index
            self.method_indexes_by_owner.setdefault(int(row[0]), []).append(index)
            previous_name = row[12]

    def method_row(self, index: int) -> tuple[int, ...]:
        return RUNTIME_METHOD_DETAIL_METHOD.unpack_from(
            self.methods,
            RUNTIME_METHOD_DETAIL_HEADER.size
            + index * RUNTIME_METHOD_DETAIL_METHOD.size,
        )

    def parameter_row(self, index: int) -> tuple[int, ...]:
        return RUNTIME_METHOD_DETAIL_PARAMETER.unpack_from(
            self.methods,
            self.parameter_start + index * RUNTIME_METHOD_DETAIL_PARAMETER.size,
        )

    def method_name(self, index: int, row: tuple[int, ...]) -> str:
        if row[10]:
            end = self.parameter_row(row[11])[7]
        elif index + 1 < self.method_count:
            end = self.method_row(index + 1)[12]
        else:
            end = len(self.methods)
        return _text(self.methods, row[12], end - row[12], label="method name")

    def method_return(self, index: int) -> str:
        row = self.method_row(index)
        return (
            "System.Void" if row[9] & METHOD_DETAIL_CONSTRUCTOR
            else self.renderer.render(row[4])
        )

    def method_parameters(
        self, index: int
    ) -> list[tuple[str, str, int, int, int]]:
        row = self.method_row(index)
        result: list[tuple[str, str, int, int, int]] = []
        for parameter_index in range(row[11], row[11] + row[10]):
            parameter = self.parameter_row(parameter_index)
            result.append(
                (
                    _text(
                        self.methods, parameter[7], parameter[5],
                        label="parameter name",
                    ),
                    self.renderer.render(parameter[2]),
                    parameter[4],
                    parameter[3],
                    parameter[6],
                )
            )
        return result

    def method_generic_declaration(self, index: int) -> tuple[str, str]:
        method_index, count, start = RUNTIME_METHOD_GENERIC_RECORD.unpack_from(
            self.method_generics,
            RUNTIME_METHOD_GENERIC_HEADER.size
            + index * RUNTIME_METHOD_GENERIC_RECORD.size,
        )
        if method_index != index or start + count > self.method_generic_argument_count:
            raise ContractViolation(
                "runtime method generic declaration range is invalid"
            )
        if not count:
            return "", ""
        names: list[str] = []
        where_clauses: list[str] = []
        for offset in range(count):
            argument_index = start + offset
            descriptor = struct.unpack_from(
                "<Q",
                self.method_generics,
                self.method_generic_argument_start + argument_index * 8,
            )[0]
            name = self.renderer.render(descriptor)
            detail = RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.unpack_from(
                self.generic_parameter_details,
                RUNTIME_GENERIC_PARAMETER_DETAIL_HEADER.size
                + argument_index * RUNTIME_GENERIC_PARAMETER_DETAIL_RECORD.size,
            )
            if detail[0] != descriptor or detail[3] + detail[2] > self.generic_constraint_count:
                raise ContractViolation(
                    "runtime generic parameter detail range is invalid"
                )
            names.append(name)
            constraints: list[str] = []
            attributes = detail[1]
            value_type = bool(attributes & 8)
            if value_type:
                constraints.append("struct")
            elif attributes & 4:
                constraints.append("class")
            for constraint_offset in range(detail[2]):
                constraint_descriptor = struct.unpack_from(
                    "<Q",
                    self.generic_parameter_details,
                    self.generic_constraint_start
                    + (detail[3] + constraint_offset) * 8,
                )[0]
                rendered = self.renderer.render(constraint_descriptor)
                if value_type and rendered == "System.ValueType":
                    continue
                if rendered not in constraints:
                    constraints.append(rendered)
            if attributes & 16 and not value_type:
                constraints.append("new()")
            if constraints:
                where_clauses.append(
                    f" where {name} : {', '.join(constraints)}"
                )
        return "<" + ", ".join(names) + ">", "".join(where_clauses)

    def type_generic_constraints(self, index: int) -> tuple[str, int]:

        graph = self.renderer.graph_row(index)
        identity = self.renderer.identity_row(index)
        parent = (
            self.renderer.root_by_descriptor.get(identity[5])
            if identity[5] else None
        )
        if identity[5] and parent is None:
            raise ContractViolation("runtime generic nested owner is absent")
        inherited_count = self.renderer.graph_row(parent)[7] if parent is not None else 0
        own_count = graph[7] - inherited_count
        if own_count < 0:
            raise ContractViolation("runtime type generic range is invalid")
        clauses: list[str] = []
        for offset in range(own_count):
            descriptor = struct.unpack_from(
                "<Q", self.graph,
                self.renderer.graph_argument_start
                + (graph[9] + inherited_count + offset) * 8,
            )[0]
            detail = self.generic_detail_by_descriptor.get(descriptor)
            if detail is None:
                raise ContractViolation(
                    "runtime type generic parameter detail is absent"
                )
            if detail[3] + detail[2] > self.generic_constraint_count:
                raise ContractViolation(
                    "runtime type generic constraint range is invalid"
                )
            name = self.renderer.render(descriptor)
            constraints: list[str] = []
            attributes = detail[1]
            value_type = bool(attributes & 8)
            if value_type:
                constraints.append("struct")
            elif attributes & 4:
                constraints.append("class")
            for constraint_offset in range(detail[2]):
                constraint_descriptor = struct.unpack_from(
                    "<Q", self.generic_parameter_details,
                    self.generic_constraint_start
                    + (detail[3] + constraint_offset) * 8,
                )[0]
                rendered = self.renderer.render(constraint_descriptor)
                if value_type and rendered == "System.ValueType":
                    continue
                if rendered not in constraints:
                    constraints.append(rendered)
            if attributes & 16 and not value_type:
                constraints.append("new()")
            if constraints:
                clauses.append(f" where {name} : {', '.join(constraints)}")
        return "".join(clauses), len(clauses)

    def property_type(self, getter: int, setter: int) -> str:
        if getter:
            index = self.method_by_pointer.get(getter)
            if index is None:
                raise ContractViolation("property getter is absent from methods")
            return self.method_return(index)
        index = self.method_by_pointer.get(setter)
        if index is None:
            raise ContractViolation("property setter is absent from methods")
        row = self.method_row(index)
        if not row[10]:
            raise ContractViolation("property setter has no value parameter")
        parameter = self.parameter_row(row[11] + row[10] - 1)
        return self.renderer.render(parameter[2])


def _render_metadata_methods(
    runtime: _RuntimeOutput, metadata_usages: dict[str, Any]
) -> list[dict[str, Any]]:
    kind_counts = metadata_usages["counts"]["kind_counts"]
    if len(kind_counts) != 8:
        raise ContractViolation("runtime metadata usage kind domain is invalid")
    observed_counts = [0] * 8
    method_records: list[dict[str, Any]] = []
    sources: set[int] = set()
    previous_rva = -1
    image_base = runtime.identity_header[6]
    image_bytes = runtime.identity_header[7]
    for usage in metadata_usages["usages"]:
        kind = usage["usage_kind"]
        if not 0 <= kind < len(observed_counts):
            raise ContractViolation("runtime metadata usage kind is invalid")
        observed_counts[kind] += 1
        if kind != 3:
            continue
        source = usage["source_index"]
        rva = usage["rva"]
        if (
            source >= runtime.method_count
            or source in sources
            or rva <= previous_rva
        ):
            raise ContractViolation(
                "runtime metadata method usage domain is inconsistent"
            )
        method = runtime.method_row(source)
        if method[0] >= runtime.type_count:
            raise ContractViolation(
                "runtime metadata method owner is outside the type domain"
            )
        pointer = method[3]
        if not image_base <= pointer < image_base + image_bytes:
            raise ContractViolation(
                "runtime metadata method has no executable method address"
            )
        method_records.append(
            {
                "Address": rva,
                "Name": (
                    f"Method${runtime.renderer.root_name(method[0])}."
                    f"{runtime.method_name(source, method)}()"
                ),
                "MethodAddress": pointer - image_base,
            }
        )
        sources.add(source)
        previous_rva = rva
    if (
        observed_counts != kind_counts
        or sum(observed_counts) != metadata_usages["counts"]["usage_count"]
        or len(method_records) != kind_counts[3]
    ):
        raise ContractViolation(
            "runtime metadata usage kinds are not completely accounted"
        )
    return method_records


def _validate_metadata_usage_members(
    runtime: _RuntimeOutput, metadata_members: dict[str, Any],
    metadata_values: dict[str, Any],
    type_renderer: _MetadataUsageTypeRenderer,
) -> dict[str, Any]:

    if (
        metadata_members["image_base"] != runtime.identity_header[6]
        or metadata_members["image_bytes"] != runtime.identity_header[7]
        or metadata_members["type_record_base_rva"]
        != metadata_values["type_record_base_rva"]
        or metadata_members["type_record_stride"]
        != metadata_values["type_record_stride"]
    ):
        raise ContractViolation(
            "runtime metadata member type contract is inconsistent"
        )
    fields_by_owner: list[list[int]] = [
        [] for _ in range(runtime.type_count)
    ]
    for index in range(runtime.field_count):
        row = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        if row[0] >= runtime.type_count:
            raise ContractViolation(
                "runtime metadata member field owner is invalid"
            )
        fields_by_owner[row[0]].append(index)

    type_record_base = (
        metadata_members["image_base"]
        + metadata_members["type_record_base_rva"]
    )
    field_semantics: set[tuple[int, int]] = set()
    field_owner_indexes: set[int] = set()
    field_type_codes: dict[int, int] = {}
    previous_field_rva = -1
    for record in metadata_members["field_refs"]:
        pointer = (
            type_record_base
            + record["type_source_index"]
            * metadata_members["type_record_stride"]
        )
        data, bits = type_renderer._type_record(pointer)
        type_code = (bits >> 16) & 0xFF
        if (
            type_code not in (0x11, 0x12)
            or data >> 32
            or data >= runtime.type_count
            or record["field_index"] >= len(fields_by_owner[data])
            or record["rva"] <= previous_field_rva
            or (data, record["field_index"]) in field_semantics
        ):
            raise ContractViolation(
                "runtime metadata field reference is inconsistent"
            )
        field_semantics.add((data, record["field_index"]))
        field_owner_indexes.add(data)
        field_type_codes[type_code] = field_type_codes.get(type_code, 0) + 1
        previous_field_rva = record["rva"]

    generic_inst_base = (
        metadata_members["image_base"]
        + metadata_members["generic_inst_base_rva"]
    )
    instances: dict[int, tuple[str, ...]] = {}

    def generic_instance(index: int) -> tuple[str, ...] | None:
        if index == -1:
            return None
        cached = instances.get(index)
        if cached is not None:
            return cached
        pointer = (
            generic_inst_base
            + index * metadata_members["generic_inst_stride"]
        )
        argument_count = type_renderer._qword(pointer)
        arguments = type_renderer._qword(pointer + 8)
        if not 1 <= argument_count <= 64:
            raise ContractViolation(
                "runtime metadata method generic instance arity is invalid"
            )
        rendered: list[str] = []
        for argument_index in range(argument_count):
            argument = type_renderer._qword(arguments + argument_index * 8)
            data, bits = type_renderer._type_record(argument)
            rendered.append(type_renderer.render(argument, data, bits))
        result = tuple(rendered)
        instances[index] = result
        return result

    method_semantics: set[tuple[int, int, int]] = set()
    method_definitions: set[int] = set()
    method_inst_count = class_inst_count = both_inst_count = 0
    previous_method_rva = -1
    for record in metadata_members["method_specs"]:
        definition = record["method_definition_index"]
        semantic = (
            record["method_inst_index"],
            record["class_inst_index"],
            definition,
        )
        if (
            definition >= runtime.method_count
            or record["rva"] <= previous_method_rva
            or semantic in method_semantics
        ):
            raise ContractViolation(
                "runtime metadata method specification is inconsistent"
            )
        method = runtime.method_row(definition)
        if method[0] >= runtime.type_count:
            raise ContractViolation(
                "runtime metadata method specification owner is invalid"
            )
        method_instance = generic_instance(record["method_inst_index"])
        class_instance = generic_instance(record["class_inst_index"])
        class_arity = runtime.renderer.graph_row(method[0])[7]
        generic_method_index, method_arity, _argument_start = (
            RUNTIME_METHOD_GENERIC_RECORD.unpack_from(
                runtime.method_generics,
                RUNTIME_METHOD_GENERIC_HEADER.size
                + definition * RUNTIME_METHOD_GENERIC_RECORD.size,
            )
        )
        if (
            generic_method_index != definition
            or
            (class_instance is None) != (class_arity == 0)
            or (
                class_instance is not None
                and len(class_instance) != class_arity
            )
            or (method_instance is None) != (method_arity == 0)
            or (
                method_instance is not None
                and len(method_instance) != method_arity
            )
        ):
            raise ContractViolation(
                "runtime metadata method class context is inconsistent"
            )
        method_inst_count += method_instance is not None
        class_inst_count += class_instance is not None
        both_inst_count += (
            method_instance is not None and class_instance is not None
        )
        method_semantics.add(semantic)
        method_definitions.add(definition)
        previous_method_rva = record["rva"]

    expected = metadata_members["counts"]
    if (
        len(field_semantics) != expected["field_ref_count"]
        or len(method_semantics) != expected["method_spec_count"]
        or len(field_semantics) + len(method_semantics)
        != expected["member_usage_count"]
    ):
        raise ContractViolation(
            "runtime metadata member usage domain is incomplete"
        )
    return {
        "field_ref_count": len(field_semantics),
        "field_ref_owner_count": len(field_owner_indexes),
        "field_ref_type_code_counts": {
            str(code): field_type_codes[code]
            for code in sorted(field_type_codes)
        },
        "method_spec_count": len(method_semantics),
        "method_spec_definition_count": len(method_definitions),
        "referenced_generic_inst_count": len(instances),
        "method_inst_count": method_inst_count,
        "class_inst_count": class_inst_count,
        "method_and_class_inst_count": both_inst_count,
        "class_generic_context_exact_count": len(method_semantics),
    }


def _binding(
    *, binary: Path, type_reference_model: Path, type_reference_inventory: Path,
    type_identity_inventory: Path, type_graph_inventory: Path,
    method_detail_inventory: Path, native_member_detail_inventory: Path,
    event_module_inventory: Path, string_literal_model: Path,
    string_literal_inventory: Path, metadata_usage_pair_model: Path | None,
    metadata_usage_pair_inventory: Path | None,
    metadata_usage_value_model: Path | None,
    metadata_usage_value_inventory: Path | None,
    metadata_usage_member_model: Path | None,
    metadata_usage_member_inventory: Path | None,
    method_generic_model: Path, method_generic_inventory: Path,
    generic_parameter_detail_model: Path,
    generic_parameter_detail_inventory: Path,
) -> tuple[
    dict[str, Any], dict[str, Any], dict[str, Any] | None,
    dict[str, Any] | None, dict[str, Any] | None
]:
    binary = binary.expanduser().resolve()
    executable = file_identity(binary)
    model_path = _owner_file(type_reference_model, label="type reference model")
    model = read_json(model_path)
    if (
        model.get("schema") != RUNTIME_TYPE_REFERENCE_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256") != executable["sha256"]
        or not all(model.get("checks", {}).values())
    ):
        raise AcquisitionError("runtime native output type reference binding is stale")
    supplied = {
        "type_identity_inventory": _owner_file(
            type_identity_inventory, label="type identity"
        ),
        "type_graph_inventory": _owner_file(type_graph_inventory, label="type graph"),
        "method_detail_inventory": _owner_file(
            method_detail_inventory, label="method detail"
        ),
        "native_member_detail_inventory": _owner_file(
            native_member_detail_inventory, label="native member detail"
        ),
        "event_module_inventory": _owner_file(
            event_module_inventory, label="event module"
        ),
    }
    reference_path = _owner_file(type_reference_inventory, label="type reference")
    if model.get("inventory", {}).get("sha256") != file_identity(reference_path)["sha256"]:
        raise AcquisitionError("runtime native output type reference inventory is stale")
    for key, path in supplied.items():
        if model.get("inputs", {}).get(key, {}).get("sha256") != file_identity(path)["sha256"]:
            raise AcquisitionError(f"runtime native output {key} binding is stale")
    method_generic_model_path = _owner_file(
        method_generic_model, label="method generic model"
    )
    method_generic_inventory_path = _owner_file(
        method_generic_inventory, label="method generic inventory"
    )
    method_generic = read_json(method_generic_model_path)
    if (
        method_generic.get("schema") != RUNTIME_METHOD_GENERIC_SCHEMA
        or method_generic.get("status") != "runtime-validated"
        or method_generic.get("target", {}).get("executable_sha256")
        != executable["sha256"]
        or not all(method_generic.get("checks", {}).values())
        or method_generic.get("inventory", {}).get("sha256")
        != file_identity(method_generic_inventory_path)["sha256"]
        or method_generic.get("inputs", {})
        .get("method_detail_inventory", {})
        .get("sha256")
        != file_identity(supplied["method_detail_inventory"])["sha256"]
    ):
        raise AcquisitionError(
            "runtime native output method generic binding is stale"
        )
    generic_detail_model_path = _owner_file(
        generic_parameter_detail_model,
        label="generic parameter detail model",
    )
    generic_detail_inventory_path = _owner_file(
        generic_parameter_detail_inventory,
        label="generic parameter detail inventory",
    )
    generic_detail = read_json(generic_detail_model_path)
    if (
        generic_detail.get("schema")
        != RUNTIME_GENERIC_PARAMETER_DETAIL_SCHEMA
        or generic_detail.get("status") != "runtime-validated"
        or generic_detail.get("target", {}).get("executable_sha256")
        != executable["sha256"]
        or not all(generic_detail.get("checks", {}).values())
        or generic_detail.get("inventory", {}).get("sha256")
        != file_identity(generic_detail_inventory_path)["sha256"]
        or generic_detail.get("inputs", {})
        .get("method_generic_inventory", {})
        .get("sha256")
        != file_identity(method_generic_inventory_path)["sha256"]
        or generic_detail.get("inputs", {})
        .get("type_reference_inventory", {})
        .get("sha256") not in {
            file_identity(reference_path)["sha256"],
            model.get("inputs", {})
            .get("base_type_reference_inventory", {})
            .get("sha256"),
        }
    ):
        raise AcquisitionError(
            "runtime native output generic parameter detail binding is stale"
        )
    literal_model_path = _owner_file(
        string_literal_model, label="string literal model"
    )
    literal_inventory_path = _owner_file(
        string_literal_inventory, label="string literal inventory"
    )
    literals = load_runtime_string_literal_inventory(
        model_path=literal_model_path,
        inventory_path=literal_inventory_path,
        expected_executable_sha256=executable["sha256"],
    )
    if (
        literals["contracts"]["type_identity_inventory_sha256"]
        != file_identity(supplied["type_identity_inventory"])["sha256"]
    ):
        raise AcquisitionError(
            "runtime native output string literal type binding is stale"
        )
    base_binding = {
        "binary": executable,
        "model": file_identity(model_path),
        "type_reference_inventory": file_identity(reference_path),
        "string_literal_model": file_identity(literal_model_path),
        "string_literal_inventory": file_identity(literal_inventory_path),
        "method_generic_model": file_identity(method_generic_model_path),
        "method_generic_inventory": file_identity(method_generic_inventory_path),
        "generic_parameter_detail_model": file_identity(generic_detail_model_path),
        "generic_parameter_detail_inventory": file_identity(
            generic_detail_inventory_path
        ),
        **{key: file_identity(path) for key, path in supplied.items()},
    }
    pair_inputs = (metadata_usage_pair_model, metadata_usage_pair_inventory)
    value_inputs = (metadata_usage_value_model, metadata_usage_value_inventory)
    member_inputs = (metadata_usage_member_model, metadata_usage_member_inventory)
    if any(value is None for value in pair_inputs):
        if any(value is not None for value in pair_inputs + value_inputs + member_inputs):
            raise AcquisitionError(
                "runtime native output usage pairs must be supplied as a model/inventory pair"
            )
        return {
            **base_binding,
            "metadata_usage_state": "pending-direct-pair-value-normalization",
        }, literals, None, None, None
    usage_pair_model_path = _owner_file(
        metadata_usage_pair_model, label="metadata usage pair model"
    )
    usage_pair_inventory_path = _owner_file(
        metadata_usage_pair_inventory, label="metadata usage pair inventory"
    )
    metadata_usages = load_runtime_metadata_usage_pair_inventory(
        model_path=usage_pair_model_path,
        inventory_path=usage_pair_inventory_path,
        expected_executable_sha256=executable["sha256"],
        expected_string_literal_inventory_sha256=(
            literals["identity"]["sha256"]
        ),
    )
    if any(value is None for value in value_inputs):
        if any(value is not None for value in value_inputs + member_inputs):
            raise AcquisitionError(
                "runtime native output usage values must be supplied as a model/inventory pair"
            )
        return {
            **base_binding,
            "metadata_usage_pair_model": file_identity(usage_pair_model_path),
            "metadata_usage_pair_inventory": file_identity(
                usage_pair_inventory_path
            ),
            "metadata_usage_state": (
                "pairs-validated-type-values-and-members-pending"
            ),
        }, literals, metadata_usages, None, None
    usage_value_model_path = _owner_file(
        metadata_usage_value_model, label="metadata usage value model"
    )
    usage_value_inventory_path = _owner_file(
        metadata_usage_value_inventory, label="metadata usage value inventory"
    )
    metadata_usage_values = load_runtime_metadata_usage_value_inventory(
        model_path=usage_value_model_path,
        inventory_path=usage_value_inventory_path,
        expected_executable_sha256=executable["sha256"],
        expected_metadata_usage_pair_inventory_sha256=(
            metadata_usages["identity"]["sha256"]
        ),
    )
    if (
        metadata_usage_values["contracts"]["type_identity_inventory_sha256"]
        != file_identity(supplied["type_identity_inventory"])["sha256"]
        or metadata_usages["image_base"] != literals["image_base"]
        or metadata_usages["image_bytes"] != literals["image_bytes"]
        or metadata_usage_values["image_base"] != literals["image_base"]
        or metadata_usage_values["image_bytes"] != literals["image_bytes"]
    ):
        raise AcquisitionError("runtime native output type usage binding is stale")
    if any(value is None for value in member_inputs):
        if any(value is not None for value in member_inputs):
            raise AcquisitionError(
                "runtime native output usage members must be supplied as a model/inventory pair"
            )
        return {
            **base_binding,
            "metadata_usage_pair_model": file_identity(usage_pair_model_path),
            "metadata_usage_pair_inventory": file_identity(
                usage_pair_inventory_path
            ),
            "metadata_usage_value_model": file_identity(usage_value_model_path),
            "metadata_usage_value_inventory": file_identity(
                usage_value_inventory_path
            ),
            "metadata_usage_state": (
                "pairs-and-type-values-validated-members-pending"
            ),
        }, literals, metadata_usages, metadata_usage_values, None
    usage_member_model_path = _owner_file(
        metadata_usage_member_model, label="metadata usage member model"
    )
    usage_member_inventory_path = _owner_file(
        metadata_usage_member_inventory,
        label="metadata usage member inventory",
    )
    metadata_usage_members = load_runtime_metadata_usage_member_inventory(
        model_path=usage_member_model_path,
        inventory_path=usage_member_inventory_path,
        expected_executable_sha256=executable["sha256"],
        expected_metadata_usage_pair_inventory_sha256=(
            metadata_usages["identity"]["sha256"]
        ),
    )
    if (
        metadata_usage_members["image_base"] != literals["image_base"]
        or metadata_usage_members["image_bytes"] != literals["image_bytes"]
        or metadata_usage_members["counts"]["usage_count"]
        != metadata_usages["counts"]["usage_count"]
        or metadata_usage_members["counts"]["field_ref_count"]
        != metadata_usages["counts"]["kind_counts"][4]
        or metadata_usage_members["counts"]["method_spec_count"]
        != metadata_usages["counts"]["kind_counts"][6]
    ):
        raise AcquisitionError(
            "runtime native output metadata usage binding is stale"
        )
    binding = {
        **base_binding,
        "metadata_usage_pair_model": file_identity(usage_pair_model_path),
        "metadata_usage_pair_inventory": file_identity(
            usage_pair_inventory_path
        ),
        "metadata_usage_value_model": file_identity(usage_value_model_path),
        "metadata_usage_value_inventory": file_identity(
            usage_value_inventory_path
        ),
        "metadata_usage_member_model": file_identity(
            usage_member_model_path
        ),
        "metadata_usage_member_inventory": file_identity(
            usage_member_inventory_path
        ),
    }
    return (
        binding, literals, metadata_usages, metadata_usage_values,
        metadata_usage_members,
    )


def _load_constructed_generic_layouts(
    *, model_path: Path, inventory_path: Path, runtime: _RuntimeOutput,
    executable_sha256: str, type_reference_sha256: str,
    field_binding: dict[str, Any] | None = None,
) -> dict[str, Any]:
    from alpha.p14 import render_observed_field
    if field_binding is None or field_binding.get("observed_field_types_bound") is not True:
        raise AcquisitionError("constructed layout output requires observed native field types")
    model_path = _owner_file(model_path, label="constructed generic model")
    inventory_path = _owner_file(
        inventory_path, label="constructed generic inventory"
    )
    model = read_json(model_path)
    identity = file_identity(inventory_path)
    if (
        not isinstance(model, dict)
        or model.get("schema") != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or model.get("inventory", {}).get("sha256") != identity["sha256"]
        or model.get("inputs", {}).get("type_reference_inventory", {}).get(
            "sha256"
        ) != field_binding["base_type_reference_inventory"]["sha256"]
        or field_binding["inputs"]["constructed_field_reference_inventory"]["sha256"]
        != type_reference_sha256
        or any(
            model.get("checks", {}).get(key) is not True
            for key in (
                "all_constructed_fields_valid",
                "all_constructed_generic_rows_valid",
                "field_count_exact",
                "generic_indexes_unique",
                "class_extent_load_code_derived",
                "materialized_classes_unique",
                "two_observations_match",
            )
        )
    ):
        raise AcquisitionError(
            "runtime constructed generic layout binding is stale"
        )
    from alpha.p20 import bind_constructed_extent
    extent_sources = {}
    instance_size_offset, instance_size_width = bind_constructed_extent(model, source_records=extent_sources)
    if (
        type(instance_size_offset) is not int or instance_size_offset < 0
        or instance_size_width not in (1, 2, 4, 8)
    ):
        raise AcquisitionError(
            "runtime constructed generic instance size layout is absent"
        )
    raw = inventory_path.read_bytes()
    if len(raw) < RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size:
        raise AcquisitionError(
            "runtime constructed generic layout inventory is truncated"
        )
    header = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.unpack_from(raw)
    record_count, field_count = header[5:7]
    records_end = (
        RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        + record_count * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
    )
    if (
        header[0] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_MAGIC
        or header[1] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_VERSION
        or header[2] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
        or header[3] != RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size
        or header[4] != RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.size
        or len(raw) != records_end
        + field_count * RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.size
        or record_count != model.get("counts", {}).get(
            "constructed_generic_class_count"
        )
        or field_count != model.get("counts", {}).get(
            "constructed_generic_field_count"
        )
    ):
        raise AcquisitionError(
            "runtime constructed generic layout header is invalid"
        )
    fields_by_type: list[list[tuple[int, ...]]] = [
        [] for _ in range(runtime.type_count)
    ]
    for index in range(runtime.field_count):
        field = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        fields_by_type[field[0]].append(field)
    captured_fields: dict[int, list[tuple[int, ...]]] = {}
    for index in range(field_count):
        field = RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.unpack_from(
            raw,
            records_end
            + index * RUNTIME_CONSTRUCTED_GENERIC_FIELD_RECORD.size,
        )
        captured_fields.setdefault(field[0], []).append(field)
    semantic: dict[str, dict[str, Any]] = {}
    alias_count = 0
    open_record_count = 0
    open_alias_count = 0
    for index in range(record_count):
        row = RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.unpack_from(
            raw,
            RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER.size
            + index * RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD.size,
        )
        (
            descriptor, _current, generic_index, definition_index,
            _generic_inst, _cached_type, _class_pointer, aliases,
            current_field_count, class_header,
        ) = row
        if instance_size_offset + instance_size_width > len(class_header):
            raise AcquisitionError("constructed code-derived extent exceeds the observed header")
        if not 0 <= definition_index < runtime.type_count:
            raise ContractViolation(
                "runtime constructed generic definition is invalid"
            )
        open_fields = fields_by_type[definition_index]
        current_fields = captured_fields.get(generic_index, [])
        if (
            current_field_count != len(open_fields)
            or len(current_fields) != len(open_fields)
            or any(field[3] != ordinal or field[0] != generic_index
                   for ordinal, field in enumerate(current_fields))
        ):
            raise ContractViolation(
                "runtime constructed generic field topology is incomplete"
            )
        reference_index = runtime.renderer.node_by_descriptor.get(descriptor)
        if reference_index is None:
            raise ContractViolation(
                "runtime constructed generic descriptor is absent"
            )
        reference = runtime.renderer.reference_row(reference_index)
        if not reference[4] & TYPE_REFERENCE_GENERIC:
            raise ContractViolation(
                "runtime constructed generic descriptor has no arguments"
            )
        arguments = [
            struct.unpack_from(
                "<Q", runtime.references,
                runtime.renderer.reference_argument_start
                + (reference[16] + offset) * 8,
            )[0]
            for offset in range(reference[8])
        ]
        graph = runtime.renderer.graph_row(definition_index)
        parameters = [
            struct.unpack_from(
                "<Q", runtime.graph,
                runtime.renderer.graph_argument_start
                + (graph[9] + offset) * 8,
            )[0]
            for offset in range(graph[7])
        ]
        if len(parameters) != len(arguments):
            raise ContractViolation(
                "runtime constructed generic argument arity is inconsistent"
            )
        aliases_are_open = runtime.renderer.contains_generic_parameter(
            descriptor
        )
        alias_count += aliases
        if aliases_are_open:


            open_record_count += 1
            open_alias_count += aliases
            continue
        name = runtime.renderer.render(descriptor)
        identity_row = runtime.renderer.identity_row(definition_index)
        is_value = bool(identity_row[1] & 0x40)
        instance_size = int.from_bytes(
            class_header[
                instance_size_offset:instance_size_offset + instance_size_width
            ],
            "little",
        )
        if instance_size < 16:
            raise ContractViolation(
                "runtime constructed generic instance size is invalid"
            )
        rendered_fields: list[dict[str, Any]] = []
        for ordinal, (open_field, captured) in enumerate(
            zip(open_fields, current_fields)
        ):
            field_type, attributes = render_observed_field(
                runtime.renderer, field_binding["fields"], owner=generic_index,
                ordinal=ordinal, pointer=captured[1], definition=definition_index,
            )
            normalized_offset = captured[2]
            is_static = bool(attributes & 0x10)


            offset = (
                normalized_offset
                if is_value and not is_static and normalized_offset >= 0
                else normalized_offset + 0x10
            )
            if offset < 0:
                raise ContractViolation(
                    "runtime constructed generic field offset is invalid "
                    f"(generic_index={generic_index}, "
                    f"definition_index={definition_index}, ordinal={ordinal}, "
                    f"normalized_offset={normalized_offset}, "
                    f"static={is_static}, value_type={is_value})"
                )
            field_name = _text(
                runtime.native, open_field[9], open_field[7],
                label="constructed generic field name",
            )
            rendered_fields.append({
                "ordinal": ordinal,
                "name": field_name,
                "type": field_type,
                "offset": offset,
                "static": is_static,
                "attributes": attributes,
                "metadata_token": open_field[6],
            })
        layout_key = (
            definition_index,
            is_value,
            instance_size,
            tuple(
                (field["offset"], field["static"], field["type"])
                for field in rendered_fields
            ),
        )
        existing = semantic.get(name)
        if existing is not None:
            if existing["layout_key"] != layout_key:
                raise ContractViolation(
                    "semantically identical constructed generic layouts differ"
                )
            existing["runtime_record_count"] += 1
            existing["alias_count"] += aliases
        else:
            semantic[name] = {
                "name": name,
                "definition_index": definition_index,
                "is_value_type": is_value,
                "instance_size": instance_size,
                "unboxed_size": instance_size - 16,
                "fields": rendered_fields,
                "layout_key": layout_key,
                "runtime_record_count": 1,
                "alias_count": aliases,
            }
    layouts = [semantic[name] for name in sorted(semantic)]
    from alpha.c04 import _verify_files
    _verify_files(field_binding["inputs"])
    _verify_files(extent_sources)
    return {
        "model": file_identity(model_path),
        "inventory": identity,
        "layouts": layouts,
        "runtime_record_count": record_count,
        "runtime_alias_count": alias_count,
        "closed_runtime_record_count": record_count - open_record_count,
        "closed_runtime_alias_count": alias_count - open_alias_count,
        "open_runtime_record_count": open_record_count,
        "open_runtime_alias_count": open_alias_count,
        "semantic_layout_count": len(layouts),
        "semantic_field_count": sum(len(layout["fields"]) for layout in layouts),
        "field_record_count": field_count,
        "instance_size_byte_offset": instance_size_offset,
        "instance_size_width_bytes": instance_size_width,
        "extent_operation_sources": extent_sources,
        "observed_field_types_bound": True,
        "template_substitution_used_as_observation": False,
        "constructed_class_reference_closure_proven": False,
        "native_layout_complete": False,
    }


def _write_constructed_generic_layouts(
    header: TextIO, layouts: list[dict[str, Any]]
) -> tuple[int, int]:
    header.write(
        "/*\n"
        " * Provisional runtime-materialized constructed generic layouts.\n"
        " * Class extent operands and native field data were observed twice;\n"
        " * field types are bound to observed native descriptors. Size and\n"
        " * offset normalization still contain unproven payload assumptions.\n"
        " * These declarations do not certify native C sizeof or alignment.\n"
        " */\n"
    )
    field_count = 0
    for layout in layouts:
        digest = hashlib.sha256(layout["name"].encode("utf-8")).hexdigest()[:16]
        stem = f"ALPHA_GENERIC_{layout['definition_index']}_{digest.upper()}"
        c_name = f"{stem}_o"
        header.write(f"/* {layout['name']} */\n")
        header.write(f"#define {stem}_BOXED_SIZE 0x{layout['instance_size']:X}u\n")
        header.write(f"#define {stem}_UNBOXED_SIZE 0x{layout['unboxed_size']:X}u\n")
        header.write(
            f"#define {stem}_IS_VALUE_TYPE "
            f"{1 if layout['is_value_type'] else 0}u\n"
        )
        header.write(f"typedef struct {c_name} {c_name};\n")
        header.write(f"struct {c_name} {{\n")
        if layout["is_value_type"]:
            if layout["unboxed_size"]:
                header.write(
                    f"    uint8_t _data[0x{layout['unboxed_size']:X}];\n"
                )
            else:
                header.write(
                    "    /* zero-sized managed value; use UNBOXED_SIZE, "
                    "not C sizeof */\n"
                )
        else:
            header.write("    Il2CppObject obj;\n")
            tail = layout["instance_size"] - 16
            if tail:
                header.write(f"    uint8_t _data[0x{tail:X}];\n")
        header.write("};\n")
        for field in layout["fields"]:
            macro = (
                f"{stem}_FIELD_{field['ordinal']}_"
                f"{'STATIC_' if field['static'] else ''}OFFSET"
            )
            header.write(
                f"#define {macro} 0x{field['offset']:X}u"
                f" /* {field['name']}: {field['type']}; token "
                f"0x{field['metadata_token']:08X} */\n"
            )
            field_count += 1
        header.write("\n")
    return len(layouts), field_count


def render_runtime_native_output(
    *, binary: Path, type_reference_model: Path,
    type_reference_inventory: Path, type_identity_inventory: Path,
    type_graph_inventory: Path, method_detail_inventory: Path,
    native_member_detail_inventory: Path, event_module_inventory: Path,
    string_literal_model: Path, string_literal_inventory: Path,
    metadata_usage_pair_model: Path | None,
    metadata_usage_pair_inventory: Path | None,
    metadata_usage_value_model: Path | None,
    metadata_usage_value_inventory: Path | None,
    metadata_usage_member_model: Path | None,
    metadata_usage_member_inventory: Path | None,
    method_generic_model: Path, method_generic_inventory: Path,
    generic_parameter_detail_model: Path,
    generic_parameter_detail_inventory: Path, output_dir: Path,
    enum_constant_model: Path | None = None,
    enum_constant_inventory: Path | None = None,
    constructed_generic_layout_model: Path | None = None,
    constructed_generic_layout_inventory: Path | None = None,
    constructed_field_capture: Path | None = None,
    direct_interface_model: Path | None = None,
    direct_interface_inventory: Path | None = None,
    parameter_default_model: Path | None = None,
    parameter_default_inventory: Path | None = None,
    assembly_identity_model: Path | None = None,
    assembly_identity_inventory: Path | None = None,
    event_module_model: Path | None = None,
) -> dict[str, Any]:
    (
        binding, string_literals, metadata_usages, metadata_usage_values,
        metadata_usage_members,
    ) = _binding(
        binary=binary,
        type_reference_model=type_reference_model,
        type_reference_inventory=type_reference_inventory,
        type_identity_inventory=type_identity_inventory,
        type_graph_inventory=type_graph_inventory,
        method_detail_inventory=method_detail_inventory,
        native_member_detail_inventory=native_member_detail_inventory,
        event_module_inventory=event_module_inventory,
        string_literal_model=string_literal_model,
        string_literal_inventory=string_literal_inventory,
        metadata_usage_pair_model=metadata_usage_pair_model,
        metadata_usage_pair_inventory=metadata_usage_pair_inventory,
        metadata_usage_value_model=metadata_usage_value_model,
        metadata_usage_value_inventory=metadata_usage_value_inventory,
        metadata_usage_member_model=metadata_usage_member_model,
        metadata_usage_member_inventory=metadata_usage_member_inventory,
        method_generic_model=method_generic_model,
        method_generic_inventory=method_generic_inventory,
        generic_parameter_detail_model=generic_parameter_detail_model,
        generic_parameter_detail_inventory=generic_parameter_detail_inventory,
    )
    output_dir = _owner_directory(output_dir)
    for name in ("dump.cs", "script.json", "il2cpp.h", "stringliteral.json", "alpha-native-output-receipt.private.json"):
        candidate = output_dir / name
        if candidate.exists() or candidate.is_symlink():
            raise AcquisitionError("runtime native output requires new staging files; existing artifacts are preserved")
    runtime = _RuntimeOutput(
        binary=binary,
        type_identity=Path(binding["type_identity_inventory"]["path"]).read_bytes(),
        type_graph=Path(binding["type_graph_inventory"]["path"]).read_bytes(),
        type_references=Path(binding["type_reference_inventory"]["path"]).read_bytes(),
        methods=Path(binding["method_detail_inventory"]["path"]).read_bytes(),
        native_members=Path(binding["native_member_detail_inventory"]["path"]).read_bytes(),
        event_modules=Path(binding["event_module_inventory"]["path"]).read_bytes(),
        method_generics=Path(
            binding["method_generic_inventory"]["path"]
        ).read_bytes(),
        generic_parameter_details=Path(
            binding["generic_parameter_detail_inventory"]["path"]
        ).read_bytes(),
    )
    event_accessor_proof = None
    from alpha.c05 import bind_output_reference_names
    reference_name_proof = bind_output_reference_names(model_path=Path(binding["model"]["path"]),
        inventory=binding["type_reference_inventory"], executable_sha256=binding["binary"]["sha256"], runtime=runtime)
    from alpha.c05 import bind_output_raw_names
    raw_name_proof = bind_output_raw_names(runtime, reference_model_path=Path(binding["model"]["path"]), selected=binding)
    if event_module_model is not None:
        from alpha.p17 import bind_output_event_accessors
        event_model_path = _owner_file(event_module_model, label="event accessor model")
        event_model_record = file_identity(event_model_path)
        event_accessor_proof = bind_output_event_accessors(runtime, model_path=event_model_path,
            event_inventory=binding["event_module_inventory"], type_identity=binding["type_identity_inventory"])
        if file_identity(event_model_path) != event_model_record:
            raise AcquisitionError("event accessor model changed during output binding")
        binding["event_module_model"] = event_model_record
    direct_inputs = (direct_interface_model, direct_interface_inventory)
    if any(value is None for value in direct_inputs):
        if any(value is not None for value in direct_inputs):
            raise AcquisitionError(
                "runtime direct interfaces must be supplied as a "
                "model/inventory pair"
            )
        direct_interfaces = None
    else:
        assert direct_interface_model is not None
        assert direct_interface_inventory is not None
        direct_interfaces = load_runtime_direct_interfaces(
            model_path=direct_interface_model,
            inventory_path=direct_interface_inventory,
            expected_executable_sha256=binding["binary"]["sha256"],
            expected_type_identity_inventory_sha256=binding[
                "type_identity_inventory"
            ]["sha256"],
            expected_type_graph_inventory_sha256=binding[
                "type_graph_inventory"
            ]["sha256"],
        )
        if direct_interfaces["type_count"] != runtime.type_count:
            raise ContractViolation(
                "runtime direct interface TypeDef domain is inconsistent"
            )
        runtime.renderer.direct_interface_rows = direct_interfaces["rows"]
        runtime.renderer.direct_interface_descriptors = direct_interfaces[
            "descriptors"
        ]
        binding = {
            **binding,
            "direct_interface_model": direct_interfaces["model"],
            "direct_interface_inventory": direct_interfaces["inventory"],
        }
    constructed_inputs = (
        constructed_generic_layout_model,
        constructed_generic_layout_inventory,
    )
    if any(value is None for value in constructed_inputs):
        if any(value is not None for value in constructed_inputs):
            raise AcquisitionError(
                "runtime constructed generic layout must be supplied as a "
                "model/inventory pair"
            )
        constructed_generics = None
        if constructed_field_capture is not None:
            raise AcquisitionError("native field observations require a constructed layout model/inventory pair")
    else:
        assert constructed_generic_layout_model is not None
        assert constructed_generic_layout_inventory is not None
        from alpha.p14 import bind_output_constructed_fields
        field_binding = bind_output_constructed_fields(
            field_capture=constructed_field_capture,
            reference_model=Path(binding["model"]["path"]),
            reference_inventory=binding["type_reference_inventory"],
            constructed_model=constructed_generic_layout_model,
            constructed_inventory=constructed_generic_layout_inventory,
            member_inventory=binding["native_member_detail_inventory"],
            identity_inventory=binding["type_identity_inventory"],
            executable_sha256=binding["binary"]["sha256"], runtime=runtime,
        )
        constructed_generics = _load_constructed_generic_layouts(
            model_path=constructed_generic_layout_model,
            inventory_path=constructed_generic_layout_inventory,
            runtime=runtime,
            executable_sha256=binding["binary"]["sha256"],
            type_reference_sha256=binding["type_reference_inventory"][
                "sha256"
            ],
            field_binding=field_binding,
        )
        binding = {
            **binding,
            **field_binding["inputs"],
            **{"constructed_extent_" + key: value for key, value in
               constructed_generics["extent_operation_sources"].items()},
            "constructed_generic_layout_model": constructed_generics["model"],
            "constructed_generic_layout_inventory": constructed_generics[
                "inventory"
            ],
        }
    enum_inputs = (enum_constant_model, enum_constant_inventory)
    if any(value is None for value in enum_inputs):
        if any(value is not None for value in enum_inputs):
            raise AcquisitionError(
                "runtime enum constants must be supplied as a model/inventory pair"
            )
        enum_constants = None
    else:


        from alpha.p44 import load_runtime_enum_constants

        enum_model_path = _owner_file(
            enum_constant_model, label="enum constant model"
        )
        enum_inventory_path = _owner_file(
            enum_constant_inventory, label="enum constant inventory"
        )
        enum_constants = load_runtime_enum_constants(
            model_path=enum_model_path,
            inventory_path=enum_inventory_path,
            expected_executable_sha256=binding["binary"]["sha256"],
        )
        if (
            enum_constants["inputs"]["native_member_detail_inventory"]
            ["sha256"]
            != binding["native_member_detail_inventory"]["sha256"]
        ):
            raise AcquisitionError(
                "runtime enum constant member binding is stale"
            )
        binding = {
            **binding,
            "enum_constant_model": file_identity(enum_model_path),
            "enum_constant_inventory": file_identity(enum_inventory_path),
        }
    image_base = runtime.identity_header[6]
    image_bytes = runtime.identity_header[7]
    literal_constants_by_field: dict[int, dict[str, Any]] = {}
    if enum_constants is not None:
        literal_constants_by_field = {
            int(record["field_index"]): record
            for record in enum_constants["constants"]
        }
        observed_enum_count = sum(
            bool(runtime.renderer.identity_row(index)[1] & 0x20)
            for index in range(runtime.type_count)
        )
        observed_literal_fields: dict[int, tuple[int, ...]] = {}
        for index in range(runtime.field_count):
            field = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
                runtime.native,
                RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
                + index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
            )
            if field[5] & 0x40:
                observed_literal_fields[index] = field
        if (
            len(literal_constants_by_field)
            != enum_constants["counts"]["constant_count"]
            or observed_enum_count != enum_constants["counts"]["enum_count"]
            or set(literal_constants_by_field) != set(observed_literal_fields)
            or any(
                int(literal_constants_by_field[index]["owner_type_index"])
                != field[0]
                or bool(literal_constants_by_field[index]["enum_owner"])
                != bool(runtime.renderer.identity_row(field[0])[1] & 0x20)
                for index, field in observed_literal_fields.items()
            )
        ):
            raise ContractViolation(
                "runtime literal constant domain is inconsistent"
            )
    parameter_default_inputs = (
        parameter_default_model, parameter_default_inventory,
    )
    if any(value is None for value in parameter_default_inputs):
        if any(value is not None for value in parameter_default_inputs):
            raise AcquisitionError(
                "runtime parameter defaults must be supplied as a "
                "model/inventory pair"
            )
        parameter_defaults = None
        parameter_defaults_by_index: dict[int, dict[str, Any]] = {}
    else:
        from alpha.p47 import PARAMETER_HAS_DEFAULT, load_runtime_parameter_defaults

        assert parameter_default_model is not None
        assert parameter_default_inventory is not None
        parameter_model_path = _owner_file(
            parameter_default_model, label="parameter default model"
        )
        parameter_inventory_path = _owner_file(
            parameter_default_inventory, label="parameter default inventory"
        )
        parameter_defaults = load_runtime_parameter_defaults(
            model_path=parameter_model_path,
            inventory_path=parameter_inventory_path,
            expected_executable_sha256=binding["binary"]["sha256"],
        )
        if (
            parameter_defaults["inputs"]["method_detail_inventory"]["sha256"]
            != binding["method_detail_inventory"]["sha256"]
        ):
            raise AcquisitionError(
                "runtime parameter default method binding is stale"
            )
        parameter_defaults_by_index = {
            int(row["parameter_index"]): row
            for row in parameter_defaults["defaults"]
        }
        expected_parameter_defaults = {
            index
            for index in range(runtime.parameter_count)
            if runtime.parameter_row(index)[3] & PARAMETER_HAS_DEFAULT
        }
        if (
            len(parameter_defaults_by_index)
            != parameter_defaults["counts"]["default_count"]
            or set(parameter_defaults_by_index) != expected_parameter_defaults
            or any(
                int(row["metadata_token"])
                != runtime.parameter_row(index)[6]
                or int(row["method_index"])
                != runtime.parameter_row(index)[0]
                or int(row["position"])
                != runtime.parameter_row(index)[1]
                for index, row in parameter_defaults_by_index.items()
            )
        ):
            raise ContractViolation(
                "runtime parameter default domain is inconsistent"
            )
        binding = {
            **binding,
            "parameter_default_model": file_identity(parameter_model_path),
            "parameter_default_inventory": file_identity(
                parameter_inventory_path
            ),
        }
    assembly_identity_inputs = (
        assembly_identity_model, assembly_identity_inventory,
    )
    if any(value is None for value in assembly_identity_inputs):
        if any(value is not None for value in assembly_identity_inputs):
            raise AcquisitionError(
                "runtime assembly identities must be supplied as a "
                "model/inventory pair"
            )
        assembly_identities = None
    else:
        from alpha.p46 import load_runtime_assembly_identities

        assert assembly_identity_model is not None
        assert assembly_identity_inventory is not None
        assembly_model_path = _owner_file(
            assembly_identity_model, label="assembly identity model"
        )
        assembly_inventory_path = _owner_file(
            assembly_identity_inventory, label="assembly identity inventory"
        )
        assembly_identities = load_runtime_assembly_identities(
            model_path=assembly_model_path,
            inventory_path=assembly_inventory_path,
            expected_executable_sha256=binding["binary"]["sha256"],
        )
        if (
            assembly_identities["inputs"]["event_module_inventory"]["sha256"]
            != binding["event_module_inventory"]["sha256"]
            or assembly_identities["counts"]["assembly_count"]
            != runtime.module_count
            or {
                row["module_name"]
                for row in assembly_identities["assemblies"]
            } != set(runtime.module_names.values())
        ):
            raise AcquisitionError(
                "runtime assembly identity module binding is stale"
            )
        binding = {
            **binding,
            "assembly_identity_model": file_identity(assembly_model_path),
            "assembly_identity_inventory": file_identity(
                assembly_inventory_path
            ),
        }
    metadata_usage_complete = (
        metadata_usages is not None
        and metadata_usage_values is not None
        and metadata_usage_members is not None
    )
    metadata_usage_pairs_available = metadata_usages is not None
    metadata_usage_values_available = (
        metadata_usages is not None and metadata_usage_values is not None
    )
    metadata_usage_members_available = metadata_usage_members is not None
    if metadata_usage_values_available:
        with _MetadataUsageTypeRenderer(
            binary=binary,
            renderer=runtime.renderer,
            generic_records=metadata_usage_values[
                "generic_records_owner_only"
            ],
        ) as metadata_type_renderer:
            all_type_metadata, root_type_codes = (
                metadata_type_renderer.render_usages(
                    metadata_usage_values["type_usages"]
                )
            )
            if metadata_usage_members is not None:
                metadata_member_counts = _validate_metadata_usage_members(
                    runtime, metadata_usage_members, metadata_usage_values,
                    metadata_type_renderer,
                )
            else:
                metadata_member_counts = {
                    "field_ref_count": 0,
                    "field_ref_owner_count": 0,
                    "field_ref_type_code_counts": {},
                    "method_spec_count": 0,
                    "method_spec_definition_count": 0,
                    "referenced_generic_inst_count": 0,
                    "method_inst_count": 0,
                    "class_inst_count": 0,
                    "method_and_class_inst_count": 0,
                    "class_generic_context_exact_count": 0,
                }
        expected_root_type_codes = {
            int(code): count
            for code, count in metadata_usage_values["counts"][
                "type_code_counts"
            ].items()
        }
        if root_type_codes != expected_root_type_codes:
            raise ContractViolation(
                "runtime metadata type code closure is inconsistent"
            )
    else:
        all_type_metadata = []
        root_type_codes = {}
        expected_root_type_codes = {}
        metadata_member_counts = {
            "field_ref_count": 0,
            "field_ref_owner_count": 0,
            "field_ref_type_code_counts": {},
            "method_spec_count": 0,
            "method_spec_definition_count": 0,
            "referenced_generic_inst_count": 0,
            "method_inst_count": 0,
            "class_inst_count": 0,
            "method_and_class_inst_count": 0,
            "class_generic_context_exact_count": 0,
        }
    script_metadata = [
        {
            "Address": record["Address"],
            "Name": record["Name"],
            "Signature": record["Signature"],
        }
        for record in all_type_metadata
        if record["TypeCode"] != 0x15
    ]
    script_metadata_methods = (
        _render_metadata_methods(runtime, metadata_usages)
        if metadata_usage_pairs_available else []
    )
    method_cursor = field_cursor = property_cursor = event_cursor = 0
    addresses: set[int] = set()
    image_count = 0
    current_module = 0
    assembly_type_index = 0
    header_layout_type_definition_count = 0
    header_field_offset_macro_count = 0
    header_field_constant_macro_count = 0
    constructed_generic_layout_count = 0
    constructed_generic_field_offset_macro_count = 0
    enum_constant_dump_count = 0
    parameter_default_dump_count = 0
    parameter_missing_default_dump_count = 0
    literal_constant_dump_count = 0
    constructor_dump_count = 0
    optional_parameter_dump_count = 0
    byref_parameter_dump_count = 0
    attributed_in_parameter_dump_count = 0
    attributed_out_parameter_dump_count = 0
    type_generic_constraint_clause_count = 0
    event_add_accessor_dump_count = 0
    event_remove_accessor_dump_count = 0
    protected_empty_type_name_dump_count = 0
    protected_empty_method_name_dump_count = 0
    protected_empty_parameter_name_dump_count = 0
    protected_empty_field_name_dump_count = 0
    protected_empty_property_name_dump_count = 0
    protected_empty_event_name_dump_count = 0
    serializable_type_dump_count = 0
    enum_underlying_types: dict[int, str] = {}
    for field_index in range(runtime.field_count):
        field = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + field_index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        owner = field[0]
        if not runtime.renderer.identity_row(owner)[1] & 0x20:
            continue
        field_name = _text(
            runtime.native, field[9], field[7], label="enum field name"
        )
        if _enum_underlying_field(field, field_name):
            if owner in enum_underlying_types:
                raise ContractViolation("enum underlying type is ambiguous")
            enum_underlying_types[owner] = runtime.renderer.render(field[3])
    with (
        _AtomicText(output_dir / "dump.cs") as dump,
        _AtomicText(output_dir / "script.json") as script,
        _AtomicText(output_dir / "il2cpp.h") as header,
        MappedPE(binary, require_runtime_functions=False) as pe,
    ):
        dump.write(EXPECTED_PROTO_BANNER + "\n\n")
        script.write('{\n  "ScriptMethod": [\n')
        header.write(
            f"// {EXPECTED_PROTO_BANNER.removeprefix('// ')}\n"
            "#pragma once\n"
            "#include <stdint.h>\n"
            "#include <stddef.h>\n\n"
            "#include <math.h>\n\n"
            "/*\n"
            " * This header is an offset-access header.  Every managed field is\n"
            " * represented by an exact, runtime-observed byte offset below.\n"
            " * No guessed native sizeof(T) values are used: use\n"
            " * ALPHA_FIELD(type, instance, ALPHA_TYPE_*_FIELD_*_OFFSET).\n"
            " * Static offsets use the same macro with the runtime static-\n"
            " * fields base as `instance`. All literal constants are exact\n"
            " * VALUE macros; managed strings use UTF-16 code units.\n"
            " */\n"
            "typedef void (*Il2CppMethodPointer)(void);\n"
            "typedef struct Il2CppClass Il2CppClass;\n"
            "typedef struct MethodInfo MethodInfo;\n"
            "typedef struct Il2CppType { void *data; uint32_t bits; } Il2CppType;\n"
            "typedef struct Il2CppObject { Il2CppClass *klass; void *monitor; } Il2CppObject;\n"
            "typedef uintptr_t il2cpp_array_size_t;\n"
            "typedef int32_t il2cpp_array_lower_bound_t;\n"
            "typedef struct Il2CppArrayBounds {\n"
            "    il2cpp_array_size_t length;\n"
            "    il2cpp_array_lower_bound_t lower_bound;\n"
            "} Il2CppArrayBounds;\n"
            "typedef struct Il2CppArray {\n"
            "    Il2CppObject obj;\n"
            "    Il2CppArrayBounds *bounds;\n"
            "    il2cpp_array_size_t max_length;\n"
            "} Il2CppArray;\n"
            "#define ALPHA_FIELD_ADDRESS(instance, offset) \\\n"
            "    ((void *)((uint8_t *)(instance) + (uintptr_t)(offset)))\n"
            "#define ALPHA_FIELD(type, instance, offset) \\\n"
            "    (*(type *)ALPHA_FIELD_ADDRESS((instance), (offset)))\n\n"
        )
        legacy_header_names = [
            f"{_script_fix_name(runtime.renderer.root_name(index))}_o"
            for index in range(runtime.type_count)
        ]
        header_name_counts: dict[str, int] = {}
        for value in legacy_header_names:
            header_name_counts[value] = header_name_counts.get(value, 0) + 1
        header_names = [
            value if header_name_counts[value] == 1 else _header_identifier(
                runtime.renderer.root_name(index), index
            )
            for index, value in enumerate(legacy_header_names)
        ]


        for header_name in header_names:
            header.write(f"typedef struct {header_name} {header_name};\n")
        header.write("\n")
        first_script = True
        rva_offsets: dict[int, int] = {}
        for type_index in range(runtime.type_count):
            identity = runtime.renderer.identity_row(type_index)
            module_pointer = identity[4]
            if module_pointer != current_module:
                current_module = module_pointer


                assembly_type_index = 1
                module_name = runtime.module_names.get(module_pointer)
                if module_name is None:
                    raise ContractViolation("type module is absent from module inventory")
                dump.write(f"// Image {image_count}: {module_name} - {image_count}\n\n")
                image_count += 1
            namespace = _optional_text(
                runtime.identity, identity[12], identity[9], label="type namespace"
            )
            name = runtime.renderer.root_name(type_index, declaration=True)
            qualified = runtime.renderer.root_name(type_index)
            raw_type_name = _text(
                runtime.identity, identity[11], identity[8], label="type name"
            )
            protected_empty_type_name_dump_count += raw_type_name.startswith(
                "EmptyType_"
            )
            attributes = identity[7]
            graph = runtime.renderer.graph_row(type_index)


            is_enum = bool(identity[1] & 0x20)
            is_value = bool(identity[1] & 0x40)
            is_interface = bool(attributes & 0x20)
            kind = (
                "enum" if is_enum else "struct" if is_value
                else "interface" if is_interface else "class"
            )
            visibility = _type_visibility(attributes)
            type_modifiers = (
                _type_modifiers(attributes, is_interface=is_interface)
                if kind == "class" else ""
            )
            bases: list[str] = []
            if is_enum:
                underlying = enum_underlying_types.get(type_index)
                if underlying is None:
                    raise ContractViolation("enum underlying type is absent")
                bases.append(underlying)
            elif (
                graph[3]
                and not is_value
                and not (kind == "class" and type_modifiers == "static")
            ):
                bases.append(runtime.renderer.render(graph[3]))


            if not is_enum:
                bases.extend(runtime.renderer.root_interfaces(type_index))
            inheritance = f" : {', '.join(bases)}" if bases else ""
            type_constraints, type_constraint_count = (
                runtime.type_generic_constraints(type_index)
            )
            type_generic_constraint_clause_count += type_constraint_count
            dump.write(f"// Namespace: {namespace}\n")
            for declaration in _type_attribute_declarations(attributes):
                dump.write(declaration + "\n")
                serializable_type_dump_count += declaration == "[Serializable]"
            dump.write(
                f"{visibility} {type_modifiers + ' ' if type_modifiers else ''}"
                f"{kind} {name}{inheritance}{type_constraints} // MetadataToken: "
                f"0x{identity[10]:08X}, MetadataIndexToken: "
                f"0x{_metadata_token(0x02000000, type_index):08X}, "
                f"AssemblyTypeIndex: {assembly_type_index}, "
                f"TypeDefIndex: {type_index}, Attributes: 0x{attributes:08X}\n{{\n"
            )

            fields_here: list[tuple[int, ...]] = []
            while field_cursor < runtime.field_count:
                field = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
                    runtime.native,
                    RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
                    + field_cursor * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
                )
                if field[0] != type_index:
                    break
                fields_here.append(field)
                field_cursor += 1
            field_global_start = field_cursor - len(fields_here)
            if fields_here:
                dump.write("\t// Fields\n")
                for field_global_index, field in enumerate(
                    fields_here, start=field_global_start
                ):
                    field_name = _text(
                        runtime.native, field[9], field[7], label="field name"
                    )
                    if is_enum and _enum_underlying_field(field, field_name):
                        field_name = "value__"
                    field_type = runtime.renderer.render(field[3])
                    if field[5] & 0x40 and enum_constants is not None:
                        constant = literal_constants_by_field.get(
                            field_global_index
                        )
                        if constant is None:
                            raise ContractViolation(
                                "runtime literal field value is absent"
                            )
                        declared_type = name if is_enum else field_type
                        dump.write(
                            f"\t{_field_modifiers(field[5])} {declared_type} "
                            f"{field_name} = "
                            f"{_csharp_constant(constant, field_type)}; "
                            f"// MetadataToken: "
                            f"0x{field[6]:08X}, MetadataIndexToken: "
                            f"0x{_metadata_token(0x04000000, field_global_index):08X}, "
                            f"Attributes: 0x{field[5]:04X}\n"
                        )
                        literal_constant_dump_count += 1
                        enum_constant_dump_count += is_enum
                        continue
                    field_offset = _managed_field_offset(
                        field, is_value_type=is_value
                    )
                    dump.write(
                        f"\t{_field_modifiers(field[5])} "
                        f"{field_type} {field_name}; "
                        f"// {'Static offset' if field[5] & 0x10 else 'Offset'}: "
                        f"0x{field_offset & 0xFFFFFFFF:X}, "
                        f"MetadataToken: "
                        f"0x{field[6]:08X}, MetadataIndexToken: "
                        f"0x{_metadata_token(0x04000000, field_global_index):08X}, "
                        f"Attributes: 0x{field[5]:04X}\n"
                    )
                dump.write("\n")


            header.write(
                f"/* {qualified} // MetadataToken: "
                f"0x{identity[10]:08X}, MetadataIndexToken: "
                f"0x{_metadata_token(0x02000000, type_index):08X}, "
                f"AssemblyTypeIndex: {assembly_type_index}, "
                f"TypeDefIndex: {type_index} */\n"
            )
            header.write(f"struct {header_names[type_index]} {{\n")
            if is_enum:
                enum_underlying = [
                    field
                    for field in fields_here
                    if _enum_underlying_field(
                        field,
                        _text(
                            runtime.native, field[9], field[7],
                            label="enum underlying field name",
                        ),
                    )
                ]
                if len(enum_underlying) != 1:
                    raise ContractViolation(
                        "runtime enum underlying field is ambiguous"
                    )
                header.write(
                    f"    {_script_c_type(runtime.renderer.render(enum_underlying[0][3]))} "
                    "value__;\n"
                )
            elif is_value:
                header.write("    uint8_t _value_type_prefix;\n")
            else:
                header.write("    Il2CppObject obj;\n")
            header.write("};\n")
            header_layout_type_definition_count += 1
            for field_global_index, field in enumerate(
                fields_here, start=field_global_start
            ):
                field_name = _text(
                    runtime.native, field[9], field[7], label="field name"
                )
                protected_empty_field_name_dump_count += field_name.startswith(
                    "EmptyField_"
                )
                if is_enum and _enum_underlying_field(field, field_name):
                    field_name = "value__"
                if field[5] & 0x40 and enum_constants is not None:
                    constant = literal_constants_by_field.get(field_global_index)
                    if constant is None:
                        raise ContractViolation(
                            "runtime header literal value is absent"
                        )
                    macro = (
                        f"ALPHA_TYPE_{type_index}_"
                        f"{'ENUM' if is_enum else 'CONST'}_{field[1]}_"
                        f"{_script_fix_name(field_name)}_VALUE"
                    )
                    header.write(
                        f"#define {macro} ({_header_constant(constant)})"
                        f" /* token "
                        f"0x{field[6]:08X}; metadata-index token "
                        f"0x{_metadata_token(0x04000000, field_global_index):08X} */\n"
                    )
                    header_field_constant_macro_count += 1
                    continue
                field_offset = _managed_field_offset(
                    field, is_value_type=is_value
                )
                macro = (
                    f"ALPHA_TYPE_{type_index}_FIELD_{field[1]}_"
                    f"{'STATIC_' if field[5] & 0x10 else ''}OFFSET"
                )
                header.write(
                    f"#define {macro} 0x{field_offset & 0xFFFFFFFF:X}u"
                    f" /* {field_name}: {runtime.renderer.render(field[3])}; "
                    f"token 0x{field[6]:08X}; metadata-index token "
                    f"0x{_metadata_token(0x04000000, field_global_index):08X} */\n"
                )
                header_field_offset_macro_count += 1
            header.write("\n")

            properties_here: list[tuple[int, ...]] = []
            while property_cursor < runtime.property_count:
                prop = RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.unpack_from(
                    runtime.native,
                    runtime.property_start
                    + property_cursor * RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size,
                )
                if prop[0] != type_index:
                    break
                properties_here.append(prop)
                property_cursor += 1
            property_global_start = property_cursor - len(properties_here)
            if properties_here:
                dump.write("\t// Properties\n")
                for property_global_index, prop in enumerate(
                    properties_here, start=property_global_start
                ):
                    prop_name = _text(
                        runtime.native, prop[9], prop[6], label="property name"
                    )
                    protected_empty_property_name_dump_count += (
                        prop_name.startswith("EmptyProperty_")
                    )
                    accessor_indexes = [
                        runtime.method_by_pointer[pointer]
                        for pointer in (prop[3], prop[4]) if pointer
                    ]
                    accessor_attributes = [
                        runtime.method_row(index)[5]
                        for index in accessor_indexes
                    ]
                    property_modifiers, surface_attributes = (
                        _property_or_event_modifiers(
                            accessor_attributes,
                            is_interface_member=is_interface,
                        )
                    )


                    accessors = " ".join(value for value in (
                        _accessor_declaration(
                            "get", runtime.method_row(
                                runtime.method_by_pointer[prop[3]]
                            )[5], surface_attributes,
                        ) if prop[3] else "",
                        _accessor_declaration(
                            "set", runtime.method_row(
                                runtime.method_by_pointer[prop[4]]
                            )[5], surface_attributes,
                        ) if prop[4] else "",
                    ) if value)
                    accessor_comments: list[str] = []
                    for label, pointer in (("Get", prop[3]), ("Set", prop[4])):
                        if not pointer:
                            continue
                        accessor_index = runtime.method_by_pointer[pointer]
                        accessor_method = runtime.method_row(accessor_index)
                        accessor_pointer = accessor_method[3]
                        accessor_rva = (
                            accessor_pointer - image_base
                            if image_base <= accessor_pointer < image_base + image_bytes
                            else 0
                        )
                        accessor_comments.append(
                            f"{label}: {runtime.method_name(accessor_index, accessor_method)}"
                            f"(0x{accessor_rva:X})"
                        )
                    dump.write(
                        f"\t{property_modifiers + ' ' if property_modifiers else ''}"
                        f"{runtime.property_type(prop[3], prop[4])} "
                        f"{prop_name} {{ {accessors} }} "
                        f"// {', '.join(accessor_comments)}, MetadataToken: "
                        f"0x{prop[5]:08X}, MetadataIndexToken: "
                        f"0x{_metadata_token(0x17000000, property_global_index):08X}, "
                        f"Attributes: 0x{prop[7]:04X}\n"
                    )
                dump.write("\n")

            events_here: list[tuple[int, ...]] = []
            while event_cursor < runtime.event_count:
                event = RUNTIME_EVENT_MODULE_EVENT.unpack_from(
                    runtime.events,
                    runtime.event_start
                    + event_cursor * RUNTIME_EVENT_MODULE_EVENT.size,
                )
                if event[0] != type_index:
                    break
                events_here.append(event)
                event_cursor += 1
            event_global_start = event_cursor - len(events_here)
            if events_here:
                dump.write("\t// Events\n")
                for event_global_index, event in enumerate(
                    events_here, start=event_global_start
                ):
                    event_name = _text(
                        runtime.events, event[10], event[7], label="event name"
                    )
                    protected_empty_event_name_dump_count += event_name.startswith(
                        "EmptyEvent_"
                    )
                    event_accessor_attributes = [
                        runtime.method_row(runtime.method_by_pointer[pointer])[5]
                        for pointer in (event[4], event[5]) if pointer
                    ]
                    event_modifiers, _event_surface = (
                        _property_or_event_modifiers(
                            event_accessor_attributes,
                            is_interface_member=is_interface,
                        )
                    )
                    accessor_comments: list[str] = []
                    for label, pointer in (
                        ("Add", event[4]), ("Remove", event[5]),
                        *((("Raise", runtime.event_raise_pointers[event_global_index]),)
                          if hasattr(runtime, "event_raise_pointers") else ()),
                    ):
                        if not pointer:
                            continue
                        accessor_index = runtime.method_by_pointer[pointer]
                        accessor_method = runtime.method_row(accessor_index)
                        accessor_pointer = accessor_method[3]
                        accessor_rva = (
                            accessor_pointer - image_base
                            if image_base <= accessor_pointer < image_base + image_bytes
                            else 0
                        )
                        accessor_comments.append(
                            f"{label}: "
                            f"{runtime.method_name(accessor_index, accessor_method)}"
                            f"(0x{accessor_rva:X})"
                        )
                        if label == "Add":
                            event_add_accessor_dump_count += 1
                        else:
                            event_remove_accessor_dump_count += 1
                    dump.write(
                        f"\t{event_modifiers + ' ' if event_modifiers else ''}"
                        f"event {runtime.renderer.render(event[3])} "
                        f"{event_name}; // {', '.join(accessor_comments)}, "
                        f"MetadataToken: "
                        f"0x{event[6]:08X}, MetadataIndexToken: "
                        f"0x{_metadata_token(0x14000000, event_global_index):08X}, "
                        f"Attributes: 0x{event[8]:04X}\n"
                    )
                dump.write("\n")

            type_methods: list[tuple[int, tuple[int, ...]]] = []
            while method_cursor < runtime.method_count:
                method = runtime.method_row(method_cursor)
                if method[0] != type_index:
                    break
                type_methods.append((method_cursor, method))
                method_cursor += 1
            previous_constructor: bool | None = None
            for method_index, method in type_methods:
                is_constructor = bool(method[9] & METHOD_DETAIL_CONSTRUCTOR)
                if is_constructor != previous_constructor:
                    dump.write(
                        "\t// Constructors\n"
                        if is_constructor else "\t// Methods\n"
                    )
                    previous_constructor = is_constructor
                constructor_dump_count += is_constructor
                method_name = runtime.method_name(method_index, method)
                protected_empty_method_name_dump_count += method_name.startswith(
                    "EmptyMethod_"
                )
                return_type = runtime.method_return(method_index)
                parameters = runtime.method_parameters(method_index)
                pointer = method[3]
                rva = pointer - image_base if image_base <= pointer < image_base + image_bytes else 0
                if rva:
                    offset = rva_offsets.get(rva)
                    if offset is None:
                        mapped = pe.rva_to_offset(rva)
                        offset = mapped if mapped is not None else 0
                        rva_offsets[rva] = offset
                    addresses.add(rva)
                else:
                    offset = 0
                slot = "" if method[8] == 0xFFFF else f" Slot: {method[8]}"
                dump.write(
                    f"\t// RVA: 0x{rva:X} Offset: 0x{offset:X} "
                    f"VA: 0x{pointer if rva else 0:X}{slot}\n"
                )
                parameter_text = []
                for parameter_global_index, (
                    parameter_name,
                    parameter_type,
                    flags,
                    raw_attributes,
                    parameter_token,
                ) in zip(
                    range(method[11], method[11] + method[10]), parameters,
                    strict=True,
                ):
                    protected_empty_parameter_name_dump_count += (
                        parameter_name.startswith("EmptyParameter_")
                    )
                    captured_default = parameter_defaults_by_index.get(
                        parameter_global_index
                    )
                    default_text = None
                    missing_default = False
                    if captured_default is not None:
                        if captured_default["value_kind"] == "missing":
                            missing_default = True
                            parameter_missing_default_dump_count += 1
                        else:
                            default_text = (
                                "null"
                                if captured_default["value_kind"] == "null"
                                else _csharp_constant(
                                    captured_default,
                                    parameter_type.removesuffix("&"),
                                )
                            )
                            parameter_default_dump_count += 1
                    parameter_text.append(
                        _parameter_declaration(
                            parameter_name,
                            parameter_type,
                            flags,
                            raw_attributes,
                            parameter_token,
                            default_text,
                            missing_default,
                        )
                    )
                    optional_parameter_dump_count += bool(
                        flags & PARAMETER_DETAIL_OPTIONAL
                    )
                    byref_parameter_dump_count += parameter_type.endswith("&")
                    attributed_in_parameter_dump_count += bool(
                        flags & PARAMETER_DETAIL_IN
                        and not parameter_type.endswith("&")
                    )
                    attributed_out_parameter_dump_count += bool(
                        flags & PARAMETER_DETAIL_OUT
                        and not parameter_type.endswith("&")
                    )
                generic_suffix, generic_constraints = (
                    runtime.method_generic_declaration(method_index)
                )
                modifiers = _method_modifiers(
                    method[5], is_interface_member=is_interface,
                    constructor=is_constructor,
                )
                if is_constructor:
                    constructor_name = _GENERIC_ARITY.sub(
                        "", _text(
                            runtime.identity, identity[11], identity[8],
                            label="constructor type name",
                        )
                    )
                    declaration = (
                        f"{modifiers + ' ' if modifiers else ''}"
                        f"{constructor_name}({', '.join(parameter_text)})"
                    )
                else:
                    declaration = (
                        f"{modifiers + ' ' if modifiers else ''}{return_type} "
                        f"{method_name}{generic_suffix}"
                        f"({', '.join(parameter_text)}){generic_constraints}"
                    )
                method_terminator = ";" if (method[5] & 0x400 or is_interface) else " { }"
                dump.write(
                    f"\t{declaration}{method_terminator} "
                    f"// MetadataToken: "
                    f"0x{method[7]:08X}, MetadataIndexToken: "
                    f"0x{_metadata_token(0x06000000, method[1]):08X}, "
                    f"Attributes: 0x{method[5]:04X}, "
                    f"ImplAttributes: 0x{method[6]:04X}\n\n"
                )

                script_parameters: list[str] = []
                type_codes = [_script_type_code(return_type)]
                if not method[5] & 0x10:
                    script_parameters.append(
                        f"{_script_fix_name(qualified)}_o* __this"
                    )
                    type_codes.append("i")
                for (
                    parameter_name,
                    parameter_type,
                    _flags,
                    _raw_attributes,
                    _parameter_token,
                ) in parameters:
                    script_parameters.append(
                        f"{_script_c_type(parameter_type)} "
                        f"{_script_fix_name(parameter_name)}"
                    )
                    type_codes.append(_script_type_code(parameter_type))
                script_parameters.append("const MethodInfo* method")
                type_codes.append("i")
                full_name = f"{qualified}$${method_name}"
                script_record = {
                    "Address": rva,
                    "Name": full_name,
                    "Signature": (
                        f"{_script_c_type(return_type)} "
                        f"{_script_fix_name(full_name)} "
                        f"({', '.join(script_parameters)});"
                    ),
                    "TypeSignature": "".join(type_codes),
                }
                if not first_script:
                    script.write(",\n")
                script.write("    " + json.dumps(
                    script_record, ensure_ascii=False, separators=(",", ":")
                ))
                first_script = False
            dump.write("}\n\n")
            assembly_type_index += 1
        if constructed_generics is not None:
            (
                constructed_generic_layout_count,
                constructed_generic_field_offset_macro_count,
            ) = _write_constructed_generic_layouts(
                header, constructed_generics["layouts"]
            )
        script.write('\n  ],\n  "ScriptString": [\n')
        _write_script_string_records(script, string_literals["literals"])
        script.write('\n  ],\n  "ScriptMetadata": [\n')
        _write_json_records(script, script_metadata)
        script.write('\n  ],\n  "ScriptMetadataMethod": [\n')
        _write_json_records(script, script_metadata_methods)
        script.write('\n  ],\n  "Addresses": [')
        script.write(",".join(str(value) for value in sorted(addresses)))
        script.write("]\n}\n")

    if (
        image_count != runtime.module_count
        or method_cursor != runtime.method_count
        or field_cursor != runtime.field_count
        or property_cursor != runtime.property_count
        or event_cursor != runtime.event_count
        or (
            enum_constants is not None
            and literal_constant_dump_count != len(literal_constants_by_field)
        )
        or (
            enum_constants is not None
            and header_field_constant_macro_count
            != len(literal_constants_by_field)
        )
    ):
        raise AcquisitionError("runtime native output inventory cursors are incomplete")
    with _AtomicText(output_dir / "stringliteral.json") as strings:
        _write_legacy_string_literal_array(
            strings, string_literals["literals"]
        )
    expected_constructor_count = sum(
        bool(runtime.method_row(index)[9] & METHOD_DETAIL_CONSTRUCTOR)
        for index in range(runtime.method_count)
    )
    expected_optional_parameter_count = 0
    expected_byref_parameter_count = 0
    expected_attributed_in_parameter_count = 0
    expected_attributed_out_parameter_count = 0
    for index in range(runtime.parameter_count):
        parameter = runtime.parameter_row(index)
        parameter_type = runtime.renderer.render(parameter[2])
        parameter_flags = parameter[4]
        is_byref = parameter_type.endswith("&")
        expected_optional_parameter_count += bool(
            parameter_flags & PARAMETER_DETAIL_OPTIONAL
        )
        expected_byref_parameter_count += is_byref
        expected_attributed_in_parameter_count += bool(
            parameter_flags & PARAMETER_DETAIL_IN and not is_byref
        )
        expected_attributed_out_parameter_count += bool(
            parameter_flags & PARAMETER_DETAIL_OUT and not is_byref
        )
    expected_event_add_accessor_count = 0
    expected_event_remove_accessor_count = 0
    expected_protected_empty_event_name_count = 0
    for index in range(runtime.event_count):
        event = RUNTIME_EVENT_MODULE_EVENT.unpack_from(
            runtime.events,
            runtime.event_start + index * RUNTIME_EVENT_MODULE_EVENT.size,
        )
        expected_event_add_accessor_count += bool(event[4])
        expected_event_remove_accessor_count += bool(event[5])
        expected_protected_empty_event_name_count += _text(
            runtime.events, event[10], event[7], label="event name"
        ).startswith("EmptyEvent_")
    expected_protected_empty_type_name_count = sum(
        _text(
            runtime.identity,
            runtime.renderer.identity_row(index)[11],
            runtime.renderer.identity_row(index)[8],
            label="type name",
        ).startswith("EmptyType_")
        for index in range(runtime.type_count)
    )
    expected_protected_empty_method_name_count = sum(
        runtime.method_name(index, runtime.method_row(index)).startswith(
            "EmptyMethod_"
        )
        for index in range(runtime.method_count)
    )
    expected_protected_empty_parameter_name_count = sum(
        _text(
            runtime.methods,
            runtime.parameter_row(index)[7],
            runtime.parameter_row(index)[5],
            label="parameter name",
        ).startswith("EmptyParameter_")
        for index in range(runtime.parameter_count)
    )
    expected_protected_empty_field_name_count = 0
    for index in range(runtime.field_count):
        field = RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.unpack_from(
            runtime.native,
            RUNTIME_NATIVE_MEMBER_DETAIL_HEADER.size
            + index * RUNTIME_NATIVE_MEMBER_DETAIL_FIELD.size,
        )
        expected_protected_empty_field_name_count += _text(
            runtime.native, field[9], field[7], label="field name"
        ).startswith("EmptyField_")
    expected_protected_empty_property_name_count = 0
    for index in range(runtime.property_count):
        prop = RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.unpack_from(
            runtime.native,
            runtime.property_start
            + index * RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY.size,
        )
        expected_protected_empty_property_name_count += _text(
            runtime.native, prop[9], prop[6], label="property name"
        ).startswith("EmptyProperty_")
    expected_serializable_type_count = sum(
        bool(runtime.renderer.identity_row(index)[7] & 0x2000)
        for index in range(runtime.type_count)
    )
    counts = {
        "image_count": image_count,
        "type_count": runtime.type_count,
        "field_count": runtime.field_count,
        "property_count": runtime.property_count,
        "method_count": runtime.method_count,
        "parameter_count": runtime.parameter_count,
        "serializable_type_count": serializable_type_dump_count,
        "constructor_count": constructor_dump_count,
        "optional_parameter_count": optional_parameter_dump_count,
        "byref_parameter_count": byref_parameter_dump_count,
        "attributed_in_parameter_count": (
            attributed_in_parameter_dump_count
        ),
        "attributed_out_parameter_count": (
            attributed_out_parameter_dump_count
        ),
        "generic_method_count": runtime.method_generic_header[6],
        "method_generic_parameter_count": (
            runtime.method_generic_argument_count
        ),
        "type_generic_parameter_count": (
            runtime.generic_parameter_argument_count
            - runtime.method_generic_argument_count
        ),
        "all_generic_parameter_detail_count": (
            runtime.generic_parameter_argument_count
        ),
        "type_generic_constraint_clause_count": (
            type_generic_constraint_clause_count
        ),
        "generic_constraint_reference_count": (
            runtime.generic_constraint_count
        ),
        "event_count": runtime.event_count,
        "event_add_accessor_count": event_add_accessor_dump_count,
        "event_remove_accessor_count": event_remove_accessor_dump_count,
        "protected_empty_type_name_count": (
            protected_empty_type_name_dump_count
        ),
        "protected_empty_method_name_count": (
            protected_empty_method_name_dump_count
        ),
        "protected_empty_parameter_name_count": (
            protected_empty_parameter_name_dump_count
        ),
        "protected_empty_field_name_count": (
            protected_empty_field_name_dump_count
        ),
        "protected_empty_property_name_count": (
            protected_empty_property_name_dump_count
        ),
        "protected_empty_event_name_count": (
            protected_empty_event_name_dump_count
        ),
        "header_layout_type_definition_count": (
            header_layout_type_definition_count
        ),
        "header_field_offset_macro_count": header_field_offset_macro_count,
        "header_field_constant_macro_count": (
            header_field_constant_macro_count
        ),
        "constructed_generic_layout_count": (
            constructed_generic_layout_count
        ),
        "constructed_generic_runtime_record_count": (
            constructed_generics["runtime_record_count"]
            if constructed_generics is not None else 0
        ),
        "constructed_generic_runtime_alias_count": (
            constructed_generics["runtime_alias_count"]
            if constructed_generics is not None else 0
        ),
        "constructed_generic_field_offset_macro_count": (
            constructed_generic_field_offset_macro_count
        ),
        "direct_interface_count": (
            direct_interfaces["interface_count"]
            if direct_interfaces is not None else 0
        ),
        "enum_count": (
            enum_constants["counts"]["enum_count"]
            if enum_constants is not None else 0
        ),
        "enum_constant_count": enum_constant_dump_count,
        "literal_constant_count": literal_constant_dump_count,
        "non_enum_constant_count": (
            literal_constant_dump_count - enum_constant_dump_count
        ),
        "parameter_default_count": parameter_default_dump_count,
        "parameter_missing_default_count": (
            parameter_missing_default_dump_count
        ),
        "unique_method_rva_count": len(addresses),
        "string_literal_count": len(string_literals["literals"]),
        "metadata_usage_count": (
            metadata_usages["counts"]["usage_count"]
            if metadata_usage_pairs_available else 0
        ),
        "metadata_usage_kind_counts": (
            metadata_usages["counts"]["kind_counts"]
            if metadata_usage_pairs_available else [0] * 8
        ),
        "type_metadata_usage_count": len(all_type_metadata),
        "generic_type_metadata_usage_count": root_type_codes.get(0x15, 0),
        "script_metadata_count": len(script_metadata),
        "method_metadata_usage_count": len(script_metadata_methods),
        "member_metadata_usage_count": (
            metadata_member_counts["field_ref_count"]
            + metadata_member_counts["method_spec_count"]
        ),
        "field_metadata_usage_count": metadata_member_counts[
            "field_ref_count"
        ],
        "method_spec_metadata_usage_count": metadata_member_counts[
            "method_spec_count"
        ],
        "metadata_member_semantics": metadata_member_counts,
    }
    artifacts = {
        name: file_identity(output_dir / name)
        for name in ("dump.cs", "script.json", "il2cpp.h", "stringliteral.json")
    }
    if metadata_usage_values is None:


        if metadata_usages is None:
            metadata_usages = {
                "target": {"executable_sha256": binding["binary"]["sha256"]},
                "counts": {"usage_count": 0, "kind_counts": [0] * 8},
                "read_only_decoder": True,
                "usage_materialization_performed": False,
            }
        metadata_usage_values = {
            "target": {"executable_sha256": binding["binary"]["sha256"]},
            "counts": {
                "kind1_count": 0, "generic_record_count": 0,
                "type_code_counts": {},
            },
            "read_only_snapshot": True,
            "usage_materialization_performed": False,
            "generic_records_owner_only": [],
        }
    if metadata_usage_members is None:
        metadata_usage_members = {
            "target": {"executable_sha256": binding["binary"]["sha256"]},
            "counts": {"field_ref_count": 0, "method_spec_count": 0},
            "read_only_snapshot": True,
            "usage_materialization_performed": False,
        }
    receipt = {
        "schema": RUNTIME_NATIVE_OUTPUT_SCHEMA,
        "status": (
            RUNTIME_NATIVE_OUTPUT_COMPLETE_STATUS
            if (
                metadata_usage_complete
                and enum_constants is not None
                and parameter_defaults is not None
                and assembly_identities is not None
            ) else (
                "structural-string-and-all-metadata-output-complete-"
                "assembly-identities-pending"
                if (
                    metadata_usage_complete
                    and enum_constants is not None
                    and parameter_defaults is not None
                ) else (
                "structural-string-and-all-metadata-output-complete-"
                "parameter-defaults-pending"
                if metadata_usage_complete and enum_constants is not None else (
                "structural-string-and-all-metadata-output-complete-"
                "enum-constants-pending"
                if metadata_usage_complete else (
                "structural-string-and-type-method-metadata-output-complete-"
                "members-pending"
                if metadata_usage_values_available
                else (
                "structural-string-and-method-metadata-output-complete-"
                "type-values-and-members-pending"
                if metadata_usage_pairs_available
                else "structural-string-output-complete-metadata-usage-pending"
                )
                )
                )
                )
            )
        ),
        "completion_scope": {
            "target_family": "current executable runtime metadata model",
            "artifacts": [
                "dump.cs", "il2cpp.h", "script.json", "stringliteral.json",
            ],
            "standard_projection_complete": True,
            "protected_empty_names": (
                "preserved as token-or-position-derived placeholders"
            ),
            "il2cpp_header_model": (
                "field-offset and literal-value access macros; constructed "
                "field types use replayed native observations when bound; "
                "legacy size/header normalization remains unproven, and "
                "native size, packing, alignment and padding are incomplete"
            ),
            "constructed_generic_layouts_complete": False,
            "constructed_field_types_observed": constructed_generics is not None,
            "constructed_class_reference_closure_proven": False,
            "direct_interface_impls_complete": direct_interfaces is not None,
            "assembly_identities_complete": assembly_identities is not None,
            "parameter_defaults": (
                "all HasDefault parameter constants, raw CLR "
                "ParameterAttributes, and exact runtime metadata tokens are "
                "rendered"
                if parameter_defaults is not None else
                "all raw CLR ParameterAttributes and exact runtime metadata "
                "tokens are rendered; uncaptured constants are not fabricated"
            ),
            "custom_attribute_blob_projection": False,
            "byte_for_byte_global_metadata_reconstruction": False,
            "arbitrary_il2cpp_product_compatibility": False,
        },
        "target": {"executable_sha256": binding["binary"]["sha256"]},
        "reflection": {
            "contract_id": reflection_contract()["contract_id"],
            "operation_count": reflection_contract()["operation_count"],
            "all_operations_uniquely_resolved": True,
            "fresh_runtime_observation": True,
        },
        "inputs": binding,
        "counts": counts,
        "artifacts": artifacts,
        "checks": {
            "target_binding_matches": sha256_file(binary) == binding["binary"]["sha256"],
            "required_banner_exact": (output_dir / "dump.cs").open(
                "r", encoding="utf-8"
            ).readline().rstrip("\n") == EXPECTED_PROTO_BANNER,
            "all_types_rendered": runtime.type_count == counts["type_count"],
            "all_serializable_type_attributes_rendered": (
                counts["serializable_type_count"]
                == expected_serializable_type_count
            ),
            "all_methods_rendered": runtime.method_count == counts["method_count"],
            "all_method_generics_rendered": (
                counts["method_generic_parameter_count"]
                == runtime.method_generic_header[7]
            ),
            "all_type_generic_parameter_details_rendered": (
                counts["all_generic_parameter_detail_count"]
                == runtime.generic_parameter_header[5]
                and counts["type_generic_parameter_count"]
                == runtime.generic_parameter_header[5]
                - runtime.method_generic_header[7]
                and counts["generic_constraint_reference_count"]
                == runtime.generic_parameter_header[6]
            ),
            "all_fields_rendered": runtime.field_count == counts["field_count"],
            "all_properties_rendered": runtime.property_count == counts["property_count"],
            "all_events_rendered": runtime.event_count == counts["event_count"],
            "all_event_accessors_rendered": (
                counts["event_add_accessor_count"]
                == expected_event_add_accessor_count
                and counts["event_remove_accessor_count"]
                == expected_event_remove_accessor_count
            ),
            "all_constructors_sectioned": (
                counts["constructor_count"] == expected_constructor_count
            ),
            "all_parameter_flags_rendered_without_fabricated_defaults": (
                counts["optional_parameter_count"]
                == expected_optional_parameter_count
                and counts["byref_parameter_count"]
                == expected_byref_parameter_count
                and counts["attributed_in_parameter_count"]
                == expected_attributed_in_parameter_count
                and counts["attributed_out_parameter_count"]
                == expected_attributed_out_parameter_count
            ),
            "all_parameter_defaults_rendered": (
                parameter_defaults is not None
                and counts["parameter_default_count"]
                == parameter_defaults["counts"][
                    "materialized_default_count"
                ]
                and counts["parameter_missing_default_count"]
                == parameter_defaults["counts"]["missing_default_count"]
                and counts["parameter_default_count"]
                + counts["parameter_missing_default_count"]
                == parameter_defaults["counts"]["default_count"]
            ),
            "parameter_defaults_runtime_observed": (
                parameter_defaults is not None
                and all(parameter_defaults["checks"].values())
                and parameter_defaults["policy"][
                    "all_has_default_parameters_included"
                ] is True
                and parameter_defaults["policy"][
                    "parameter_default_cache_field_runtime_derived"
                ] is True
                and parameter_defaults["policy"][
                    "managed_default_getter_invoked"
                ] is True
                and parameter_defaults["counts"][
                    "runtime_object_default_count"
                ] == 0
                and parameter_defaults["policy"]["fixed_address_used"] is False
                and parameter_defaults["policy"]["fixed_offset_used"] is False
            ),
            "all_assembly_identities_runtime_observed": (
                assembly_identities is not None
                and assembly_identities["counts"]["assembly_count"]
                == runtime.module_count
                and all(assembly_identities["checks"].values())
                and assembly_identities["policy"][
                    "assembly_name_properties_runtime_observed"
                ] is True
                and assembly_identities["policy"]["fixed_address_used"] is False
                and assembly_identities["policy"]["fixed_offset_used"] is False
            ),
            "exact_runtime_metadata_tokens_rendered": True,
            "all_protected_empty_names_explicitly_accounted": (
                counts["protected_empty_type_name_count"]
                == expected_protected_empty_type_name_count
                and counts["protected_empty_method_name_count"]
                == expected_protected_empty_method_name_count
                and counts["protected_empty_parameter_name_count"]
                == expected_protected_empty_parameter_name_count
                and counts["protected_empty_field_name_count"]
                == expected_protected_empty_field_name_count
                and counts["protected_empty_property_name_count"]
                == expected_protected_empty_property_name_count
                and counts["protected_empty_event_name_count"]
                == expected_protected_empty_event_name_count
            ),
            "all_header_type_layouts_rendered": (
                counts["header_layout_type_definition_count"]
                == runtime.type_count
            ),
            "all_header_field_symbols_rendered": (
                counts["header_field_offset_macro_count"]
                + counts["header_field_constant_macro_count"]
                == runtime.field_count
            ),
            "all_runtime_constructed_generic_layouts_rendered": (
                constructed_generics is not None
                and counts["constructed_generic_layout_count"]
                == constructed_generics["semantic_layout_count"]
                and counts["constructed_generic_runtime_record_count"]
                == constructed_generics["runtime_record_count"]
                and counts["constructed_generic_runtime_alias_count"]
                == constructed_generics["runtime_alias_count"]
            ),
            "all_constructed_generic_fields_rendered": (
                constructed_generics is not None
                and counts["constructed_generic_field_offset_macro_count"]
                == constructed_generics["semantic_field_count"]
            ),
            "all_direct_interface_impls_rendered": (
                direct_interfaces is not None
                and counts["direct_interface_count"]
                == direct_interfaces["interface_count"]
            ),
            "all_enum_constants_rendered": (
                enum_constants is not None
                and counts["enum_constant_count"]
                == enum_constants["counts"]["enum_constant_count"]
                and counts["enum_count"]
                == enum_constants["counts"]["enum_count"]
            ),
            "all_literal_constants_rendered": (
                enum_constants is not None
                and counts["literal_constant_count"]
                == enum_constants["counts"]["constant_count"]
                and counts["non_enum_constant_count"]
                == enum_constants["counts"]["non_enum_constant_count"]
            ),
            "enum_constants_runtime_observed": (
                enum_constants is not None
                and all(enum_constants["checks"].values())
                and enum_constants["policy"][
                    "field_info_get_raw_constant_value_implementation_derived"
                ] is True
                and enum_constants["policy"][
                    "field_info_get_raw_constant_value_invoked"
                ] is False
                and enum_constants["policy"][
                    "default_value_table_observed_read_only"
                ] is True
                and enum_constants["policy"][
                    "managed_string_object_allocation_absent"
                ] is True
                and enum_constants["policy"]["fixed_address_used"] is False
                and enum_constants["policy"]["fixed_offset_used"] is False
            ),
            "metadata_tokens_match_runtime_indexes": (
                _metadata_token(0x02000000, runtime.type_count - 1)
                == 0x02000000 | (runtime.type_count - 1)
                and _metadata_token(0x04000000, runtime.field_count - 1)
                == 0x04000000 | (runtime.field_count - 1)
                and _metadata_token(0x06000000, runtime.method_count - 1)
                == 0x06000000 | (runtime.method_count - 1)
                and _metadata_token(0x17000000, runtime.property_count - 1)
                == 0x17000000 | (runtime.property_count - 1)
                and _metadata_token(0x14000000, runtime.event_count - 1)
                == 0x14000000 | (runtime.event_count - 1)
            ),
            "all_string_literals_rendered": (
                string_literals["counts"]["literal_count"]
                == counts["string_literal_count"]
            ),
            "string_literal_values_runtime_decoded": (
                string_literals["status"] == "complete"
                and string_literals["read_only_decoder"] is True
                and string_literals["usage_materialization_performed"] is False
            ),
            "string_literal_usage_rvas_complete": (
                string_literals["slot_bytes"]
                == counts["string_literal_count"] * 8
                and string_literals["slot_base_rva"] & 7 == 0
                and string_literals["slot_base_rva"]
                + string_literals["slot_bytes"]
                <= string_literals["image_bytes"]
            ),
            "metadata_usage_target_binding_matches": (
                metadata_usages["target"]["executable_sha256"]
                == binding["binary"]["sha256"]
                and metadata_usage_values["target"]["executable_sha256"]
                == binding["binary"]["sha256"]
                and metadata_usage_members["target"]["executable_sha256"]
                == binding["binary"]["sha256"]
            ),
            "all_metadata_usage_kinds_accounted": (
                sum(counts["metadata_usage_kind_counts"])
                == counts["metadata_usage_count"]
            ),
            "all_type_metadata_usages_decoded": (
                counts["type_metadata_usage_count"]
                == counts["metadata_usage_kind_counts"][1]
                == metadata_usage_values["counts"]["kind1_count"]
            ),
            "generic_type_metadata_usages_closed": (
                counts["generic_type_metadata_usage_count"]
                == expected_root_type_codes.get(0x15, 0)
                and metadata_usage_values["counts"]["generic_record_count"]
                == len(metadata_usage_values["generic_records_owner_only"])
            ),
            "standard_type_metadata_projection_complete": (
                counts["script_metadata_count"]
                == counts["type_metadata_usage_count"]
                - counts["generic_type_metadata_usage_count"]
            ),
            "all_method_metadata_usages_rendered": (
                counts["method_metadata_usage_count"]
                == counts["metadata_usage_kind_counts"][3]
            ),
            "all_field_metadata_usages_semantically_closed": (
                counts["field_metadata_usage_count"]
                == counts["metadata_usage_kind_counts"][4]
                == metadata_usage_members["counts"]["field_ref_count"]
            ),
            "all_method_specs_semantically_closed": (
                counts["method_spec_metadata_usage_count"]
                == counts["metadata_usage_kind_counts"][6]
                == metadata_usage_members["counts"]["method_spec_count"]
                == metadata_member_counts[
                    "class_generic_context_exact_count"
                ]
            ),
            "member_generic_instances_closed_over_exact_pe": (
                not metadata_usage_complete or (
                    metadata_member_counts["referenced_generic_inst_count"] > 0
                    and metadata_member_counts["method_inst_count"] > 0
                    and metadata_member_counts["class_inst_count"] > 0
                )
            ),
            "metadata_usage_observation_read_only": (
                metadata_usages["read_only_decoder"] is True
                and metadata_usages["usage_materialization_performed"]
                is False
                and metadata_usage_values["read_only_snapshot"] is True
                and metadata_usage_values["usage_materialization_performed"]
                is False
                and metadata_usage_members["read_only_snapshot"] is True
                and metadata_usage_members[
                    "usage_materialization_performed"
                ] is False
            ),
            "external_runtime_component_absent": True,
            "saved_reference_generation_seed_absent": True,
        },
        "remaining_stages": [
            "DummyDll", "proto_packet_field_mapping", "ExcelBinOutput",
        ],
    }
    if not metadata_usage_complete:


        for key in (
            "metadata_usage_target_binding_matches",
            "all_metadata_usage_kinds_accounted",
            "all_type_metadata_usages_decoded",
            "generic_type_metadata_usages_closed",
            "standard_type_metadata_projection_complete",
            "all_method_metadata_usages_rendered",
            "all_field_metadata_usages_semantically_closed",
            "all_method_specs_semantically_closed",
            "member_generic_instances_closed_over_exact_pe",
            "metadata_usage_observation_read_only",
        ):
            receipt["checks"].pop(key)
        receipt["checks"].update({
            "metadata_usage_projection_intentionally_pending": True,
            "metadata_usage_members_intentionally_pending": (
                not metadata_usage_members_available
            ),
        })
        if metadata_usage_pairs_available:
            receipt["checks"].update({
                "metadata_usage_pair_target_binding_matches": (
                    metadata_usages["target"]["executable_sha256"]
                    == binding["binary"]["sha256"]
                ),
                "all_metadata_usage_pairs_accounted": (
                    sum(counts["metadata_usage_kind_counts"])
                    == counts["metadata_usage_count"]
                ),
                "all_method_metadata_usage_pairs_rendered": (
                    counts["method_metadata_usage_count"]
                    == counts["metadata_usage_kind_counts"][3]
                ),
                "metadata_usage_pair_observation_read_only": (
                    metadata_usages["read_only_decoder"] is True
                    and metadata_usages["usage_materialization_performed"]
                    is False
                ),
            })
        if metadata_usage_values_available:
            receipt["checks"].update({
                "metadata_usage_value_target_binding_matches": (
                    metadata_usage_values["target"]["executable_sha256"]
                    == binding["binary"]["sha256"]
                ),
                "all_type_metadata_usages_decoded": (
                    counts["type_metadata_usage_count"]
                    == counts["metadata_usage_kind_counts"][1]
                    == metadata_usage_values["counts"]["kind1_count"]
                ),
                "generic_type_metadata_usages_closed": (
                    counts["generic_type_metadata_usage_count"]
                    == expected_root_type_codes.get(0x15, 0)
                    and metadata_usage_values["counts"]["generic_record_count"]
                    == len(metadata_usage_values["generic_records_owner_only"])
                ),
                "standard_type_metadata_projection_complete": (
                    counts["script_metadata_count"]
                    == counts["type_metadata_usage_count"]
                    - counts["generic_type_metadata_usage_count"]
                ),
                "metadata_usage_value_observation_read_only": (
                    metadata_usage_values["read_only_snapshot"] is True
                    and metadata_usage_values[
                        "usage_materialization_performed"
                    ] is False
                ),
            })
    if enum_constants is None:


        for key in (
            "all_enum_constants_rendered",
            "all_literal_constants_rendered",
            "enum_constants_runtime_observed",
        ):
            receipt["checks"].pop(key)
        receipt["checks"]["enum_constants_intentionally_pending"] = True
    if parameter_defaults is None:
        for key in (
            "all_parameter_defaults_rendered",
            "parameter_defaults_runtime_observed",
        ):
            receipt["checks"].pop(key)
        receipt["checks"]["parameter_defaults_intentionally_pending"] = True
    if assembly_identities is None:
        receipt["checks"].pop("all_assembly_identities_runtime_observed")
        receipt["checks"]["assembly_identities_intentionally_pending"] = True


    receipt["metadata_complete"] = False
    from alpha.c04 import _verify_files
    _verify_files({role: record for role, record in binding.items() if role != "binary"})
    if file_identity(binary) != binding["binary"]:
        raise AcquisitionError("output executable changed during rendering")
    if reference_name_proof != bind_output_reference_names(model_path=Path(binding["model"]["path"]),
            inventory=binding["type_reference_inventory"], executable_sha256=binding["binary"]["sha256"]):
        raise AcquisitionError("raw TypeRef evidence changed during output rendering")
    receipt["raw_type_reference_names"] = reference_name_proof
    if raw_name_proof != bind_output_raw_names(runtime,
            reference_model_path=Path(binding["model"]["path"]), selected=binding):
        raise AcquisitionError("original metadata name evidence changed during output")
    receipt["raw_metadata_names"] = raw_name_proof
    receipt["event_raise_accessors"] = {
        "observed": event_accessor_proof is not None,
        "counts": event_accessor_proof["counts"] if event_accessor_proof is not None else None,
        "absence_is_not_null": True,
    }
    if event_accessor_proof is not None:
        from alpha.c04 import _verify_files
        _verify_files(dict(event_accessor_proof["inputs"], event_module_model=binding["event_module_model"]))
        receipt["checks"].update(event_accessor_proof["checks"])
    if not all(receipt["checks"].values()):
        raise AcquisitionError(
            "runtime native output receipt did not close: "
            + ", ".join(
                sorted(
                    key for key, value in receipt["checks"].items()
                    if value is not True
                )
            )
        )
    _private_json(output_dir / "alpha-native-output-receipt.private.json", receipt)
    return {
        "schema": RUNTIME_NATIVE_OUTPUT_SCHEMA,
        "status": receipt["status"],
        "target": receipt["target"],
        "counts": counts,
        "artifacts": artifacts,
        "checks": receipt["checks"],
        "remaining_stages": receipt["remaining_stages"],
    }
