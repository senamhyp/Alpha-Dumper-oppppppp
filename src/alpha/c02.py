import re
import struct
from dataclasses import dataclass

from alpha.h01 import AcquisitionError
from alpha.c01 import decode_x64


_REGS = ("rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp") + tuple(
    f"r{i}" for i in range(8, 16)
)
_ALIASES = {}
for full, short, word, byte in (
    ("rax", "eax", "ax", "al"), ("rbx", "ebx", "bx", "bl"),
    ("rcx", "ecx", "cx", "cl"), ("rdx", "edx", "dx", "dl"),
    ("rsi", "esi", "si", "sil"), ("rdi", "edi", "di", "dil"),
    ("rbp", "ebp", "bp", "bpl"), ("rsp", "esp", "sp", "spl"),
):
    for name, width in ((full, 8), (short, 4), (word, 2), (byte, 1)):
        _ALIASES[name] = (full, width)
for number in range(8, 16):
    for suffix, width in (("", 8), ("d", 4), ("w", 2), ("b", 1)):
        _ALIASES[f"r{number}{suffix}"] = (f"r{number}", width)
_VOLATILE = ("rax", "rcx", "rdx", "r8", "r9", "r10", "r11")
_OBJECT = ("object",)
_STACK = ("stack",)
_MEM = re.compile(r"(?:(BYTE|WORD|DWORD|QWORD) PTR )?\[(\w+)(?:([+-])(0x[0-9a-f]+|[0-9]+))?\]")
_WIDTH = {"BYTE": 1, "WORD": 2, "DWORD": 4, "QWORD": 8}


def _add(value, displacement):
    if value is None:
        return None
    if value[0] == "constant":
        return ("constant", value[1] + displacement)
    if value[0] == "add":
        return _add(value[1], value[2] + displacement)
    return ("add", value, displacement) if displacement else value


def _base_offset(value):
    return (value[1], value[2]) if value and value[0] == "add" else (value, 0)


def _integer(operand):
    try:
        value = int(operand, 0)
        return value - (1 << 64) if (1 << 63) <= value < (1 << 64) else value
    except ValueError:
        return None


def _address(operand, registers):
    match = _MEM.fullmatch(operand)
    if not match or match[2] not in _REGS:
        return None, None
    displacement = int(match[4], 0) if match[4] else 0
    if match[3] == "-":
        displacement = -displacement
    return _add(registers[match[2]], displacement), _WIDTH.get(match[1])


@dataclass(frozen=True, order=True)
class ExtentCopyCandidate:
    object_class_pointer_offset: int
    class_extent_offset: int
    class_extent_width: int
    payload_offset: int
    class_load_instruction: int
    extent_load_instruction: int
    allocation_call_instruction: int
    allocation_callee_offset: int
    allocation_extent_argument: int
    copy_call_instruction: int
    copy_callee_offset: int
    return_instruction: int


def _candidate(arguments, call_offset, callee):
    destination, source, count, _ = arguments
    allocation, header = _base_offset(destination)
    source_base, source_header = _base_offset(source)
    extent, negative_header = _base_offset(count)
    if (not allocation or allocation[0] != "call" or header <= 0
        or source_base != _OBJECT or source_header != header
        or negative_header != -header or not extent or extent[0] != "load"):
        return None
    class_pointer, size_offset = _base_offset(extent[1])
    if not class_pointer or class_pointer[0] != "load" or class_pointer[2] != 8:
        return None
    object_base, class_offset = _base_offset(class_pointer[1])
    if object_base != _OBJECT or min(size_offset, class_offset) < 0:
        return None
    positions = [index for index, value in enumerate(allocation[3]) if value == extent]
    if len(positions) != 1:
        return None
    values = (class_offset, size_offset, extent[2], header, class_pointer[3], extent[3],
              allocation[1], allocation[2], positions[0], call_offset, callee)
    return allocation, values


def discover_extent_copy_candidates(code: bytes) -> tuple[ExtentCopyCandidate, ...]:

    instructions = decode_x64(code)
    positions = {offset: index for index, (offset, _) in enumerate(instructions)}
    registers = dict.fromkeys(_REGS)
    registers.update(rcx=_OBJECT, rsp=_STACK)
    pending = [(0, registers, ())]
    seen, matches = set(), set()
    while pending:
        index, registers, candidates = pending.pop()
        if not 0 <= index < len(instructions):
            continue
        key = (index, tuple(registers.items()), candidates)
        if key in seen:
            continue
        seen.add(key)
        if len(seen) > max(1024, len(instructions) * 256):
            raise AcquisitionError("object extent data flow exceeded bounded analysis")
        offset, instruction = instructions[index]
        parts = instruction.split(None, 1)
        operation = parts[0]
        operands = tuple(part.strip() for part in parts[1].split(",")) if len(parts) == 2 else ()
        successors = [index + 1]
        if operation.startswith("ret"):
            for allocation, values in candidates:
                if registers["rax"] == allocation:
                    matches.add(ExtentCopyCandidate(*values, offset))
            continue
        if operation.startswith("j"):
            target = _integer(operands[0]) if operands else None
            successors = [] if operation == "jmp" else successors
            if target in positions:
                successors.append(positions[target])
        elif operation in ("test", "cmp", "nop", "nopl", "nopw", "endbr64", "push"):
            pass
        elif operation == "pop" and operands[0] in _ALIASES:
            registers[_ALIASES[operands[0]][0]] = None
        elif operation in ("mov", "movabs", "movzx", "lea") and len(operands) == 2:
            destination, source = operands
            if destination not in _ALIASES:
                address, _ = _address(destination, registers)
                if _base_offset(address)[0] != _STACK:

                    registers = dict.fromkeys(_REGS)
                    candidates = ()
            else:
                full, destination_width = _ALIASES[destination]
                address, load_width = _address(source, registers)
                value = None
                if operation == "lea":
                    value = address if destination_width == 8 else None
                elif source in _ALIASES and operation in ("mov", "movabs"):
                    source_full, source_width = _ALIASES[source]
                    if source_width == destination_width == 8:
                        value = registers[source_full]
                    elif source_width == destination_width == 4:
                        original = registers[source_full]
                        if original and original[0] == "load" and original[2] <= 4:
                            value = original
                elif address is not None and load_width:
                    if (operation == "movzx" and load_width < destination_width and destination_width >= 4
                        or operation in ("mov", "movabs") and load_width == destination_width and destination_width >= 4):
                        value = ("load", address, load_width, offset)
                else:
                    constant = _integer(source)
                    if constant is not None and destination_width >= 4:
                        value = ("constant", constant)
                registers[full] = value
        elif operation in ("add", "sub") and len(operands) == 2 and operands[0] in _ALIASES:
            full, width = _ALIASES[operands[0]]
            constant = _integer(operands[1])
            registers[full] = _add(registers[full], constant * (1 if operation == "add" else -1)) if width == 8 and constant is not None else None
        elif operation == "call":
            arguments = tuple(registers[register] for register in ("rcx", "rdx", "r8", "r9"))
            direct = code[offset:offset + 1] == b"\xe8" and offset + 5 <= len(code)
            if direct:
                callee = offset + 5 + struct.unpack_from("<i", code, offset + 1)[0]
                candidate = _candidate(arguments, offset, callee)
                if candidate is not None:
                    candidates = (*candidates, candidate)
            for register in _VOLATILE:
                registers[register] = None
            if direct:
                registers["rax"] = ("call", offset, callee, arguments)
        elif (operation in ("xor", "and", "or", "shr", "shl", "sar", "inc", "dec", "neg", "not")
              or operation.startswith("set")) and operands and operands[0] in _ALIASES:
            registers[_ALIASES[operands[0]][0]] = None
        else:
            registers = dict.fromkeys(_REGS)
            candidates = ()
        pending.extend((successor, dict(registers), candidates) for successor in successors)
    return tuple(sorted(matches))


import json
from string import Template

from alpha.h01 import AcquisitionError
from alpha.c01 import direct_reference_getter
from alpha.c01 import RawMetadataName

SCHEMA = "alpha.module-name-getter-io/v1"


def _operations(model):
    records = model.get("resolved")
    if not isinstance(records, list) or not 1 <= len(records) <= 4096:
        raise AcquisitionError("module getter candidate domain is absent or excessive")
    result = {}
    for row in records:
        if (not isinstance(row, dict) or any(type(row.get(key)) is not int or not 0 < row[key] < 1 << 64
                for key in ("class_pointer", "method_pointer", "metadata_pointer", "byte_offset"))
                or row["class_pointer"] in result or row["class_pointer"] & 7
                or row["metadata_pointer"] & 7 or not isinstance(row.get("code_hex"), str)):
            raise AcquisitionError("module getter candidate identity is invalid")
        try:
            raw = bytes.fromhex(row["code_hex"])
        except ValueError as error:
            raise AcquisitionError("module getter candidate code encoding is invalid") from error
        getter = direct_reference_getter(raw)
        if any(row.get(key) != value for key, value in getter.items()):
            raise AcquisitionError("module getter field displacement differs from its complete code")
        result[row["class_pointer"]] = row
    return result


def probe_source(source, *, model, modules, binding):

    start, end = "static DWORD WINAPI worker(LPVOID unused)", "BOOL WINAPI DllMain("
    if source.count(start) != 1 or source.count(end) != 1 or "static int alpha_raw_identity(" not in source:
        raise AcquisitionError("module getter probe requires the current-instance-guarded collector")
    worker = native_getter_support(model=model, modules=modules, binding=binding)
    return source[:source.index(start)] + worker + source[source.index(end):]


def native_getter_support(*, model, modules, binding, entrypoint="worker", destination="output_path",
                          after_read="", finish_string_io=True):

    operations = _operations(model)
    if (not modules or len(modules) > 4096 or len(set(modules)) != len(modules)
            or any(type(p) is not int or not 0 < p < 1 << 64 or p & 7 for p in modules)):
        raise AcquisitionError("module getter probe owner domain is invalid")
    rows = []
    for row in operations.values():
        data = bytes.fromhex(row["code_hex"])
        rows.append("{" + ",".join(str(row[key]) + "ull" for key in
                    ("class_pointer", "method_pointer", "metadata_pointer", "byte_offset")) +
                    "," + str(len(data)) + ",{" + ",".join(str(b) for b in data) + "}}")
    prefix = json.dumps({"schema": SCHEMA, "binding": binding}, separators=(",", ":"))[:-1] + ',"rows":['
    return _WORKER.substitute(operations=",".join(rows), modules=",".join(str(p) + "ull" for p in modules),
        prefix=json.dumps(prefix), entrypoint=entrypoint, destination=destination, after_read=after_read,
        finish_io="|| !write_string_io_probe()" if finish_string_io else "")


def validate_probe(value, *, model, modules, binding):
    operations = _operations(model)
    if (not isinstance(value, dict) or value.get("schema") != SCHEMA
            or json.dumps(value.get("binding"), sort_keys=True) != json.dumps(binding, sort_keys=True)
            or value.get("status") != "complete" or value.get("metadata_complete") is not False
            or type(value.get("failure_kind")) is not int or value["failure_kind"] != 0
            or type(value.get("completed_modules")) is not int or value["completed_modules"] != len(modules)):
        raise AcquisitionError("module getter probe identity or completion differs")
    rows = value.get("rows")
    if not modules or len(set(modules)) != len(modules) or not isinstance(rows, list) or len(rows) != len(modules):
        raise AcquisitionError("module getter probe owner domain does not close")
    names, used = [], set()
    for index, (pointer, row) in enumerate(zip(modules, rows)):
        if (not isinstance(row, list) or len(row) != 11
                or any(type(n) is not int or not 0 <= n < 1 << 64 for n in row[:10])
                or row[:2] != [index, pointer] or row[2] not in operations):
            raise AcquisitionError("module getter probe row or owner differs")
        operation = operations[row[2]]
        if (row[3:6] != [operation["metadata_pointer"], operation["method_pointer"], operation["byte_offset"]]
                or not row[6] or row[6] & 7 or row[6:10] != [row[6]] * 4
                or not isinstance(row[10], str) or len(row[10]) > 131072):
            raise AcquisitionError("module getter return/field repeat or operation binding differs")
        try:
            data = bytes.fromhex(row[10]); data.decode("utf-8", errors="strict")
        except (ValueError, UnicodeError) as error:
            raise AcquisitionError("module getter name is not exact UTF-8") from error
        if data.hex() != row[10]:
            raise AcquisitionError("module getter name encoding is not canonical")
        names.append(RawMetadataName("module", index, data)); used.add(row[2])
    return tuple(names), {"module_count": len(names), "observed_module_class_count": len(used),
        "empty_name_count": sum(name.value == b"" for name in names), "getter_io_replayed": True,
        "all_observed_module_classes_covered": True, "module_name_role_proven": False,
        "image_file_name_role_proven": False, "metadata_complete": False}


_WORKER = Template(r'''
typedef struct module_getter_operation {
    uintptr_t klass, pointer, metadata, offset;
    uint32_t code_bytes;
    unsigned char code[8];
} module_getter_operation;
static const module_getter_operation module_getters[] = {$operations};
static const uintptr_t observed_modules[] = {$modules};
static int module_probe_current(void) {
    char eh[65], ih[65], mh[65], nh[65];
    return alpha_raw_identity() && GetCurrentProcessId() == expected_pid &&
        executable_identity(eh) && !strcmp(eh, executable_sha256) &&
        sha256_file(identity_path, ih) && !strcmp(ih, identity_sha256) &&
        sha256_file(member_path, mh) && !strcmp(mh, member_sha256) &&
        sha256_file(native_path, nh) && !strcmp(nh, native_sha256);
}
static int module_getter_code_matches(const module_getter_operation *op) {
    return op->code_bytes && op->code_bytes <= sizeof(op->code) &&
        readable(op->pointer, op->code_bytes) && !memcmp((const void *)op->pointer, op->code, op->code_bytes);
}
static DWORD WINAPI $entrypoint(LPVOID unused) {
    (void)unused;
    FILE *out = open_private_output($destination);
    if (!out) return 9;
    fputs($prefix, out);
    uint64_t completed = 0; uint32_t failure = 0;
    if (!module_probe_current()) failure = 1;
    const uint64_t count = sizeof(observed_modules) / sizeof(observed_modules[0]);
    for (uint64_t i = 0; !failure && i < count; i++) {
        uintptr_t object = observed_modules[i], klass = 0;
        if (!alpha_raw_identity() || !readable(object, sizeof(klass))) { failure = 2; break; }
        memcpy(&klass, (const void *)object, sizeof(klass));
        const module_getter_operation *op = NULL;
        for (size_t j = 0; j < sizeof(module_getters) / sizeof(module_getters[0]); j++)
            if (module_getters[j].klass == klass) {
                if (op) { failure = 3; break; }
                op = &module_getters[j];
            }
        if (failure) break;
        if (!op || !module_getter_code_matches(op) || object > UINTPTR_MAX - op->offset ||
            !readable(object + op->offset, sizeof(uintptr_t))) { failure = 4; break; }
        uintptr_t before = 0, after = 0;
        memcpy(&before, (const void *)(object + op->offset), sizeof(before));
        uintptr_t first = ((instance_noarg)op->pointer)(object, op->metadata);
        if (!module_getter_code_matches(op) || !first || first != before) { failure = 5; break; }
        char *name = NULL; uint32_t bytes = 0;
        if (!managed_utf8_recorded(first, &name, &bytes)) { free(name); failure = 6; break; }
        if (!module_getter_code_matches(op) || !alpha_raw_identity()) { free(name); failure = 7; break; }
        uintptr_t second = ((instance_noarg)op->pointer)(object, op->metadata);
        memcpy(&after, (const void *)(object + op->offset), sizeof(after));
        uintptr_t final_class = 0; memcpy(&final_class, (const void *)object, sizeof(final_class));
        if (first != second || before != after || final_class != klass ||
            !module_getter_code_matches(op) || !alpha_raw_identity()) { free(name); failure = 7; break; }
        $after_read
        fprintf(out, "%s[%llu,%llu,%llu,%llu,%llu,%llu,%llu,%llu,%llu,%llu,\"",
            completed ? "," : "", (unsigned long long)i, (unsigned long long)object,
            (unsigned long long)klass, (unsigned long long)op->metadata, (unsigned long long)op->pointer,
            (unsigned long long)op->offset, (unsigned long long)before, (unsigned long long)first,
            (unsigned long long)after, (unsigned long long)second);
        for (uint32_t b = 0; b < bytes; b++) fprintf(out, "%02x", (unsigned char)name[b]);
        fputs("\"]", out); free(name); completed++;
    }
    if (!failure && (!module_probe_current() $finish_io)) failure = 8;
    fprintf(out, "],\"status\":\"%s\",\"completed_modules\":%llu,\"failure_kind\":%u,\"metadata_complete\":false}\n",
        !failure && completed == count ? "complete" : "rejected", (unsigned long long)completed, failure);
    if (fclose(out) && !failure) failure = 10;
    return failure;
}
''')


from alpha.c01 import NAME_DOMAINS, _binding_digest


def native_raw_name_writer_source(*, binding, counts):
    digest = _binding_digest(binding, counts)
    domains = []
    start = 0
    for domain in sorted(counts, key=NAME_DOMAINS.__getitem__):
        domains.append("{%du, %dull, %dull}" % (NAME_DOMAINS[domain], counts[domain], start))
        start += counts[domain]
    declarations = (
        "static const uint64_t alpha_raw_expected_count = %dull;\n" % start
        + "static const uint64_t alpha_raw_expected_creation = %dull;\n" % binding["creation_filetime"]
        + "static const uint64_t alpha_raw_expected_pid = %dull;\n" % binding["process_id"]
        + "static const unsigned char alpha_raw_binding[32] = {"
        + ",".join(str(value) for value in digest) + "};\n"
        + "static const struct alpha_raw_domain alpha_raw_domains[] = {"
        + ",".join(domains) + "};\n"
    )
    return _DECLARATIONS + declarations + _IMPLEMENTATION


_DECLARATIONS = r'''

struct alpha_raw_domain { uint32_t domain; uint64_t count, start; };
struct alpha_raw_header {
    char magic[8]; uint32_t version, header_bytes, row_bytes, reserved;
    uint64_t count, bytes; unsigned char binding[32];
};
struct alpha_raw_row {
    uint32_t domain, index, flags, reserved; uint64_t offset, length;
};
_Static_assert(sizeof(struct alpha_raw_header) == 72, "ALPHARN1 header");
_Static_assert(sizeof(struct alpha_raw_row) == 32, "ALPHARN1 row");
'''

_IMPLEMENTATION = r'''
static struct alpha_raw_row *alpha_raw_rows;
static unsigned char *alpha_raw_seen, *alpha_raw_pool;
static uint64_t alpha_raw_completed, alpha_raw_bytes, alpha_raw_capacity;
static int alpha_raw_initialized, alpha_raw_written;

static int alpha_raw_identity(void) {
    FILETIME creation, exit_time, kernel_time, user_time;
    if ((uint64_t)GetCurrentProcessId() != alpha_raw_expected_pid ||
        !GetProcessTimes(GetCurrentProcess(), &creation, &exit_time, &kernel_time, &user_time)) return 0;
    uint64_t observed = ((uint64_t)creation.dwHighDateTime << 32) | creation.dwLowDateTime;
    return observed == alpha_raw_expected_creation;
}

static int alpha_raw_initialize(void) {
    if (alpha_raw_initialized || !alpha_raw_identity() || alpha_raw_expected_count > 16000000ull ||
        alpha_raw_expected_count > SIZE_MAX / sizeof(*alpha_raw_rows)) return 0;
    size_t count = (size_t)(alpha_raw_expected_count ? alpha_raw_expected_count : 1u);
    alpha_raw_rows = calloc(count, sizeof(*alpha_raw_rows));
    alpha_raw_seen = calloc(count, 1u);
    if (!alpha_raw_rows || !alpha_raw_seen) {
        free(alpha_raw_rows); free(alpha_raw_seen); alpha_raw_rows = NULL; alpha_raw_seen = NULL;
        return 0;
    }
    alpha_raw_initialized = 1;
    return 1;
}


static int alpha_raw_append(uint32_t domain, uint32_t index, int is_null,
                          const void *text, uint64_t bytes) {
    if (!alpha_raw_initialized || alpha_raw_written || (is_null != 0 && is_null != 1) ||
        (is_null && bytes) || (!text && bytes) || bytes > 268435456ull - alpha_raw_bytes) return 0;
    uint64_t position = UINT64_MAX;
    for (size_t i = 0; i < sizeof(alpha_raw_domains) / sizeof(*alpha_raw_domains); i++) {
        if (alpha_raw_domains[i].domain != domain) continue;
        if ((uint64_t)index >= alpha_raw_domains[i].count) return 0;
        position = alpha_raw_domains[i].start + index;
        break;
    }
    if (position >= alpha_raw_expected_count || alpha_raw_seen[position]) return 0;
    uint64_t required = alpha_raw_bytes + bytes;
    if (required > alpha_raw_capacity) {
        uint64_t capacity = alpha_raw_capacity ? alpha_raw_capacity : 1024u;
        while (capacity < required) capacity *= 2u;
        if (capacity > 268435456ull || capacity > SIZE_MAX) return 0;
        unsigned char *grown = realloc(alpha_raw_pool, (size_t)capacity);
        if (!grown) return 0;
        alpha_raw_pool = grown; alpha_raw_capacity = capacity;
    }
    alpha_raw_rows[position] = (struct alpha_raw_row){domain, index, is_null ? 1u : 0u, 0,
                                                alpha_raw_bytes, bytes};
    if (bytes) memcpy(alpha_raw_pool + alpha_raw_bytes, text, (size_t)bytes);
    alpha_raw_seen[position] = 1;
    alpha_raw_bytes = required; alpha_raw_completed++;
    return 1;
}


static int alpha_raw_write(FILE *output) {
    if (!output || !alpha_raw_initialized || alpha_raw_written || !alpha_raw_identity() ||
        alpha_raw_completed != alpha_raw_expected_count) return 0;
    struct alpha_raw_header header = {0};
    memcpy(header.magic, "ALPHARN1", 8);
    header.version = 1; header.header_bytes = sizeof(header);
    header.row_bytes = sizeof(struct alpha_raw_row);
    header.count = alpha_raw_expected_count; header.bytes = alpha_raw_bytes;
    memcpy(header.binding, alpha_raw_binding, 32);
    if (fwrite(&header, 1, sizeof(header), output) != sizeof(header)) return 0;
    uint64_t cursor = 0;
    for (uint64_t i = 0; i < alpha_raw_expected_count; i++) {
        if (!alpha_raw_seen[i]) return 0;
        struct alpha_raw_row row = alpha_raw_rows[i];
        row.offset = cursor; cursor += row.length;
        if (fwrite(&row, 1, sizeof(row), output) != sizeof(row)) return 0;
    }
    if (cursor != alpha_raw_bytes) return 0;
    for (uint64_t i = 0; i < alpha_raw_expected_count; i++) {
        struct alpha_raw_row row = alpha_raw_rows[i];
        if (row.length && fwrite(alpha_raw_pool + row.offset, 1, (size_t)row.length, output) != row.length)
            return 0;
    }
    if (!alpha_raw_identity() || ferror(output)) return 0;
    alpha_raw_written = 1;
    return 1;
}


static void alpha_raw_release_after_quiescence(void) {
    free(alpha_raw_rows); free(alpha_raw_seen); free(alpha_raw_pool);
    alpha_raw_rows = NULL; alpha_raw_seen = NULL; alpha_raw_pool = NULL;
    alpha_raw_completed = alpha_raw_bytes = alpha_raw_capacity = 0;
    alpha_raw_initialized = alpha_raw_written = 0;
}
'''


from alpha.h01 import owner_private_status, owner_uid

import hashlib
import struct
from string import Template

from alpha.h01 import AcquisitionError
from alpha.c01 import RawMetadataName, _binding_digest


RAW_PARAMETER_HEADER = struct.Struct("<8sIIIIQQQQ64s64s64s64s")
RAW_PARAMETER_ROW = struct.Struct("<IIQQ")
_INPUT_ROLES = ("native_inventory", "type_identity_inventory", "method_name_observation")


def decode_raw_parameter_names(raw, *, expected_binding, method_count, parameter_count):
    counts = {"method": method_count, "parameter": parameter_count}
    _binding_digest(expected_binding, counts)
    if set(expected_binding["inputs"]) != set(_INPUT_ROLES):
        raise AcquisitionError("raw parameter name source roles differ")
    if not isinstance(raw, bytes) or len(raw) < RAW_PARAMETER_HEADER.size:
        raise AcquisitionError("raw parameter name header is truncated")
    header = RAW_PARAMETER_HEADER.unpack_from(raw)
    start = RAW_PARAMETER_HEADER.size + parameter_count * RAW_PARAMETER_ROW.size
    expected = (b"ALPHARP1", 1, RAW_PARAMETER_HEADER.size, RAW_PARAMETER_ROW.size, 0,
                method_count, parameter_count, expected_binding["process_id"],
                expected_binding["creation_filetime"],
                expected_binding["executable_sha256"].encode("ascii"),
                *(expected_binding["inputs"][key].encode("ascii") for key in _INPUT_ROLES))
    if header != expected or not start <= len(raw) <= start + 256 * 1024 * 1024:
        raise AcquisitionError("raw parameter name identity, counts or extent differs")
    cursor = 0
    names = []


    rows = RAW_PARAMETER_ROW.iter_unpack(
        memoryview(raw)[RAW_PARAMETER_HEADER.size:
                        RAW_PARAMETER_HEADER.size + parameter_count * RAW_PARAMETER_ROW.size])
    for index, (flags, reserved, offset, length) in enumerate(rows):
        if (flags & ~1 or reserved or offset != cursor or flags & 1 and length or
            length > len(raw) - start - cursor):
            raise AcquisitionError("raw parameter name range or null marker is invalid")
        value = None if flags & 1 else raw[start + cursor:start + cursor + length]
        names.append(RawMetadataName("parameter", index, value))
        cursor += length
    if start + cursor != len(raw):
        raise AcquisitionError("raw parameter name payload has unclaimed bytes")
    return tuple(names)


_C_SOURCE = Template(r'''
typedef struct {
    char magic[8];
    uint32_t version, header_bytes, row_bytes, reserved;
    uint64_t method_count, parameter_count, process_id, creation_filetime;
    char executable_sha256[64], native_inventory_sha256[64];
    char type_identity_sha256[64], method_names_sha256[64];
} alpha_raw_parameter_header;
typedef struct {
    uint32_t flags, reserved;
    uint64_t offset, bytes;
} alpha_raw_parameter_name;
_Static_assert(sizeof(alpha_raw_parameter_header) == $header_size, "raw parameter header");
_Static_assert(sizeof(alpha_raw_parameter_name) == $row_size, "raw parameter name");
static alpha_raw_parameter_name *raw_parameter_names;
static unsigned char *raw_parameter_text;
static uint64_t raw_parameter_count, raw_parameter_bytes, raw_parameter_capacity;

static uint64_t raw_name_process_creation(void) {
    FILETIME creation, exit_time, kernel, user;
    if (!GetProcessTimes(GetCurrentProcess(), &creation, &exit_time, &kernel, &user))return 0;
    return ((uint64_t)creation.dwHighDateTime << 32) | creation.dwLowDateTime;
}
static int allocate_raw_parameter_names(void) {
    if (expected_parameter_count > 16000000ull ||
        expected_parameter_count > SIZE_MAX / sizeof(*raw_parameter_names))return 0;
    raw_parameter_names = calloc((SIZE_T)(expected_parameter_count ? expected_parameter_count : 1u),
                                 sizeof(*raw_parameter_names));
    return raw_parameter_names != NULL;
}
static int capture_raw_parameter_name(uint64_t index, int is_null, const char *value, uint32_t bytes) {
    if (!raw_parameter_names || index != raw_parameter_count || index >= expected_parameter_count ||
        (is_null != 0 && is_null != 1) || (is_null && bytes) || (!value && bytes) ||
        bytes > 256ull * 1024ull * 1024ull - raw_parameter_bytes)return 0;
    uint64_t required = raw_parameter_bytes + bytes;
    if (required > raw_parameter_capacity) {
        uint64_t capacity = raw_parameter_capacity ? raw_parameter_capacity : 65536u;
        while(capacity < required)capacity *= 2u;
        if (capacity > SIZE_MAX)return 0;
        unsigned char *grown = realloc(raw_parameter_text, (SIZE_T)capacity);
        if (!grown)return 0;
        raw_parameter_text = grown; raw_parameter_capacity = capacity;
    }
    alpha_raw_parameter_name *row = &raw_parameter_names[index];
    row->flags = (uint32_t)is_null; row->reserved = 0;
    row->offset = raw_parameter_bytes; row->bytes = bytes;
    if (bytes)memcpy(raw_parameter_text + raw_parameter_bytes, value, bytes);
    raw_parameter_bytes = required; raw_parameter_count++;
    return 1;
}
static int write_raw_parameter_names(void) {
    uint64_t creation = raw_name_process_creation();
    if (!creation || creation != expected_creation_filetime ||
        GetCurrentProcessId() != expected_process_id ||
        raw_parameter_count != expected_parameter_count)return 0;
    alpha_raw_parameter_header header = {0};
    memcpy(header.magic, "ALPHARP1", 8);
    header.version = 1; header.header_bytes = sizeof(header);
    header.row_bytes = sizeof(alpha_raw_parameter_name);
    header.method_count = expected_method_count;
    header.parameter_count = expected_parameter_count;
    header.process_id = GetCurrentProcessId(); header.creation_filetime = creation;
    memcpy(header.executable_sha256, expected_executable_sha256, 64);
    memcpy(header.native_inventory_sha256, expected_native_inventory_sha256, 64);
    memcpy(header.type_identity_sha256, expected_type_identity_sha256, 64);
    memcpy(header.method_names_sha256, expected_method_names_sha256, 64);
    FILE *output = _wfopen(raw_parameter_output, L"wb");
    if (!output)return 0;
    int ok = fwrite(&header, 1, sizeof(header), output) == sizeof(header) &&
        fwrite(raw_parameter_names, sizeof(*raw_parameter_names), raw_parameter_count, output) == raw_parameter_count &&
        (!raw_parameter_bytes || fwrite(raw_parameter_text, 1, raw_parameter_bytes, output) == raw_parameter_bytes);
    if (fclose(output))ok = 0;
    if (!ok)_wremove(raw_parameter_output);
    return ok;
}
''')


def raw_parameter_name_source():
    return _C_SOURCE.substitute(header_size=RAW_PARAMETER_HEADER.size, row_size=RAW_PARAMETER_ROW.size)


def attach_raw_parameter_name_capture(source, *, creation_filetime, output_path):

    from pathlib import Path
    from alpha.p12 import _wide_literal, _windows_z_path
    if type(creation_filetime) is not int or not 0 < creation_filetime < 1 << 64:
        raise AcquisitionError("raw name capture requires a bound process creation time")

    def replace_once(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise AcquisitionError("raw name collector template integration seam differs")
        source = source.replace(old, new, 1)

    declaration = "static volatile LONG callback_action, callback_complete;"
    replace_once(declaration, declaration +
        f"\nstatic const uint64_t expected_creation_filetime = {creation_filetime}ull;\n" +
        "static const wchar_t raw_parameter_output[] = " +
        _wide_literal(_windows_z_path(Path(output_path))) + ";\n" + raw_parameter_name_source())
    replace_once("    _wremove(status_output);", "    _wremove(status_output);\n    _wremove(raw_parameter_output);")
    condition = "    if (GetCurrentProcessId() != expected_process_id ||"
    replace_once(condition, condition + "\n        raw_name_process_creation() != expected_creation_filetime ||")
    replace_once("    if (!detail_methods || !detail_parameters) {",
                 "    if (!detail_methods || !detail_parameters || !allocate_raw_parameter_names()) {")
    append = "            if (bytes) {\n                output->name_bytes = bytes;"
    replace_once(append, """            if (!capture_raw_parameter_name(completed_parameter_count,
                    !name_object, text, bytes)) {
                free(text);
                failure_index = index + 1u;
                failure_kind = 18u;
                return 0;
            }
""" + append)
    replace_once("    ok = write_output();", "    ok = write_raw_parameter_names() && write_output();")
    return source


def _native_method_rows(raw, *, expected_binding, method_count, image_bytes, _precomputed_native_sha256=None):

    from alpha.p17 import _NATIVE_INVENTORY_HEADER as header_type, _NATIVE_TYPE_RECORD as type_row, _NATIVE_METHOD_RECORD as method_row, _NATIVE_INVENTORY_MAGIC as magic, _NATIVE_INVENTORY_VERSION as version
    if len(raw) < header_type.size:
        raise AcquisitionError("raw name native source is truncated")
    header = header_type.unpack_from(raw)
    start = header_type.size + header[5] * type_row.size
    names_start = start + method_count * method_row.size


    native_digest = (_precomputed_native_sha256 if isinstance(_precomputed_native_sha256, str)
                     else hashlib.sha256(raw).hexdigest())
    if (header[:5] != (magic, version, type_row.size, method_row.size, 0) or
        header[6:9] != (method_count, image_bytes, expected_binding["executable_sha256"].encode("ascii")) or
        header[17] or names_start > len(raw) or
        native_digest != expected_binding["inputs"]["native_inventory"]):
        raise AcquisitionError("raw name native source header or binding differs")


    owner_rows = type_row.iter_unpack(
        memoryview(raw)[header_type.size:start])
    method_rows = method_row.iter_unpack(
        memoryview(raw)[start:start + method_count * method_row.size])
    cursor, name_cursor = 0, names_start
    for owner, row in enumerate(owner_rows):
        count = row[7]
        if (row[0] != owner or row[8] or row[9] != cursor or count > method_count - cursor or
            row[10] != name_cursor or row[1] > 4096 or row[1] > len(raw) - name_cursor):
            raise AcquisitionError("raw name native owner ranges differ")
        name_cursor += row[1]
        for local_index in range(count):
            native = next(method_rows)
            if native[:2] != (owner, local_index) or not native[2]:
                raise AcquisitionError(f"raw name native owner/index differs (index={cursor})")
            yield native
            cursor += 1
    if cursor != method_count or name_cursor != len(raw):
        raise AcquisitionError("raw name native source ranges do not close")


def project_raw_method_parameter_names(*, parameter_observation, method_observation, native_inventory,
                                      detail_inventory, expected_binding,
                                      expected_method_count, image_base, image_bytes):

    from alpha.p22 import RUNTIME_METHOD_DETAIL_HEADER as detail_header, RUNTIME_METHOD_DETAIL_METHOD as method_row, RUNTIME_METHOD_DETAIL_PARAMETER as parameter_row, RUNTIME_METHOD_DETAIL_MAGIC as detail_magic, RUNTIME_METHOD_DETAIL_VERSION as detail_version
    from alpha.p16 import METHOD_NAME_DECODE_OPERATION_CODES
    from alpha.p18 import RUNTIME_METHOD_NAME_HEADER as name_header, RUNTIME_METHOD_NAME_RECORD as name_row, RUNTIME_METHOD_NAME_MAGIC as name_magic, RUNTIME_METHOD_NAME_VERSION as name_version
    if len(detail_inventory) < detail_header.size or len(method_observation) < name_header.size:
        raise AcquisitionError("raw name projection inputs are truncated")
    detail = detail_header.unpack_from(detail_inventory)
    header = name_header.unpack_from(method_observation)
    method_count, parameter_count = detail[5:7]
    parameters = decode_raw_parameter_names(parameter_observation,
        expected_binding=expected_binding, method_count=expected_method_count,
        parameter_count=parameter_count)
    inputs = expected_binding["inputs"]
    parameters_start = detail_header.size + method_count * method_row.size
    detail_start = parameters_start + parameter_count * parameter_row.size
    name_start = name_header.size + method_count * name_row.size
    hashes = (expected_binding["executable_sha256"], inputs["native_inventory"],
              inputs["type_identity_inventory"], inputs["method_name_observation"])
    if (method_count != expected_method_count or
        detail[:6] != (detail_magic, detail_version, detail_header.size, method_row.size,
                       parameter_row.size, expected_method_count) or
        detail[8:10] != (image_base, image_bytes) or detail[11] or
        detail[12:] != tuple(value.encode("ascii") for value in hashes) or
        detail_start + detail[7] != len(detail_inventory) or
        header[:6] != (name_magic, name_version, name_header.size, name_row.size, 0, method_count) or
        header[8] != image_bytes or header[9:11] != tuple(value.encode("ascii") for value in hashes[:2]) or
        header[14] not in METHOD_NAME_DECODE_OPERATION_CODES.values() or
        header[15] or not header[16] or not header[17] or
        name_start + header[7] != len(method_observation) or
        hashlib.sha256(method_observation).hexdigest() != inputs["method_name_observation"]):
        raise AcquisitionError("raw name projection header or source binding differs")
    originals = []
    next_name, next_display, next_parameter = name_start, detail_start, 0
    nonempty, empty_methods, empty_parameters, null_parameters = 0, 0, 0, 0


    detail_method_rows = method_row.iter_unpack(
        memoryview(detail_inventory)[detail_header.size:
                                     detail_header.size + method_count * method_row.size])
    detail_name_rows = name_row.iter_unpack(
        memoryview(method_observation)[name_header.size:
                                       name_header.size + method_count * name_row.size])
    detail_parameter_rows = parameter_row.iter_unpack(
        memoryview(detail_inventory)[parameters_start:
                                     parameters_start + parameter_count * parameter_row.size])
    for index, native in enumerate(_native_method_rows(native_inventory,
            expected_binding=expected_binding, method_count=method_count, image_bytes=image_bytes)):
        method = next(detail_method_rows)
        name = next(detail_name_rows)


        if (method[1] != index or name[:3] != native[:3] or
            (method[0], method[2]) != (native[0], native[2]) or name[3] != next_name or
            name[4] > 16384 or name[4] > len(method_observation) - next_name or
            name[5] != bool(name[4]) or method[12] != next_display or
            method[11] != next_parameter or method[10] > parameter_count - next_parameter):
            raise AcquisitionError(f"raw method name or parameter range differs (index={index})")
        value = method_observation[next_name:next_name + name[4]]
        originals.append(RawMetadataName("method", index, value))
        next_name += len(value)
        nonempty += bool(value)
        empty_methods += not value
        display = value if value else f"EmptyMethod_{method[7]:X}".encode("ascii")
        if detail_inventory[next_display:next_display + len(display)] != display:
            raise AcquisitionError("raw method name and display projection differ")
        next_display += len(display)
        for position in range(method[10]):
            parameter = next(detail_parameter_rows)
            original = parameters[next_parameter].value
            empty_parameters += original == b""
            null_parameters += original is None
            display = original if original else f"EmptyParameter_{position}".encode("ascii")
            if (parameter[:2] != (index, position) or parameter[5] != len(display) or
                parameter[7] != next_display or
                detail_inventory[next_display:next_display + len(display)] != display):
                raise AcquisitionError("raw parameter name and display projection differ")
            next_display += len(display)
            next_parameter += 1
    if (next_parameter != parameter_count or next_display != len(detail_inventory) or
        next_name != len(method_observation) or nonempty != header[6]):
        raise AcquisitionError("raw name projection does not cover the entire domain")
    return tuple(originals) + parameters, {
        "method": method_count, "parameter": parameter_count,
        "empty_method_names": empty_methods, "empty_parameter_names": empty_parameters,
        "null_parameter_names": null_parameters,
    }


def finalize_raw_method_parameter_names(*, plan, output_path):

    import os
    from pathlib import Path
    from alpha.p13 import _safe_path, _file_record
    from alpha.c01 import encode_raw_metadata_names, decode_raw_metadata_names

    if not isinstance(plan, dict) or any(key not in plan for key in (
            "target", "inputs", "output_path", "raw_parameter_names_path", "contract")):
        raise AcquisitionError("raw name acquisition plan is incomplete")
    output_path = _safe_path(Path(output_path))
    if output_path.exists():
        raise AcquisitionError("raw name output already exists")
    inputs = {role: dict(plan["inputs"][role]) for role in _INPUT_ROLES}
    for role, key in (("method_detail_inventory", "output_path"),
                      ("raw_parameter_observation", "raw_parameter_names_path")):
        path = _safe_path(Path(plan[key]))
        inputs[role] = dict(_file_record(path), path=str(path))
    if False and output_path.parent != Path(inputs["method_detail_inventory"]["path"]).parent:
        raise AcquisitionError("raw name output must remain in its capture directory")
    parent = output_path.parent.stat()
    if False or not owner_private_status(parent):
        raise AcquisitionError("raw name capture directory is not owner-only")

    def verify():
        for record in inputs.values():
            path = _safe_path(Path(record["path"]))
            if str(path) != record["path"] or _file_record(path) != {
                    "bytes": record["bytes"], "sha256": record["sha256"]}:
                raise AcquisitionError("raw name source file changed")

    verify()
    source = {role: Path(inputs[role]["path"]).read_bytes()
              for role in ("native_inventory", "method_name_observation", "method_detail_inventory", "raw_parameter_observation")}
    if any(hashlib.sha256(raw).hexdigest() != inputs[role]["sha256"] for role, raw in source.items()):
        raise AcquisitionError("raw name source changed during read")
    target = plan["target"]
    binding = {"executable_sha256": target["executable_sha256"], "process_id": target["process_id"],
               "creation_filetime": target.get("creation_filetime"),
               "inputs": {role: inputs[role]["sha256"] for role in _INPUT_ROLES}}
    names, counts = project_raw_method_parameter_names(
        native_inventory=source["native_inventory"],
        parameter_observation=source["raw_parameter_observation"],
        method_observation=source["method_name_observation"],
        detail_inventory=source["method_detail_inventory"], expected_binding=binding,
        expected_method_count=plan["contract"]["method_count"],
        image_base=target["image_base_owner_only"], image_bytes=target["image_bytes"])
    binding["inputs"] = {role: record["sha256"] for role, record in inputs.items()}
    domains = {role: counts[role] for role in ("method", "parameter")}
    encoded = encode_raw_metadata_names(names, binding=binding, expected_counts=domains)
    if decode_raw_metadata_names(encoded, expected_binding=binding, expected_counts=domains) != names:
        raise AcquisitionError("raw name semantic roundtrip failed")
    verify()
    descriptor = os.open(
        output_path,
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0),
        0o600,
    )
    with os.fdopen(descriptor, "wb") as output:
        output.write(encoded)
        output.flush()
        os.fsync(output.fileno())
    if output_path.read_bytes() != encoded:
        raise AcquisitionError("raw name byte roundtrip failed")
    verify()
    return {
        "schema": "alpha.raw-method-parameter-names/v1", "binding": binding,
        "inputs": inputs, "inventory": dict(_file_record(output_path), path=str(output_path)),
        "counts": counts, "domain_counts": domains,
        "checks": {"raw_name_domain_closed": True, "raw_name_display_projection_exact": True,
                   "raw_name_null_and_empty_distinct": True, "raw_name_byte_roundtrip": True,
                   "raw_name_semantic_roundtrip": True, "raw_name_sources_unchanged": True},
        "metadata_complete": False,
    }


def load_raw_method_parameter_names(*, model, inventory_path, expected_identity,
                                    expected_inputs, expected_counts):

    from pathlib import Path
    from alpha.p13 import _safe_path, _file_record
    from alpha.c01 import encode_raw_metadata_names, decode_raw_metadata_names

    roles = set(_INPUT_ROLES) | {"method_detail_inventory", "raw_parameter_observation"}
    if (not isinstance(model, dict) or model.get("schema") != "alpha.raw-method-parameter-names/v1" or
        model.get("metadata_complete") is not False or set(expected_inputs) != roles or
        model.get("inputs") != expected_inputs or set(expected_counts) != {"method", "parameter"} or
        model.get("domain_counts") != expected_counts):
        raise AcquisitionError("raw name model or explicit input identities differ")
    binding = {"executable_sha256": expected_identity["executable_sha256"],
               "process_id": expected_identity["process_id"],
               "creation_filetime": expected_identity["creation_filetime"],
               "inputs": {role: record["sha256"] for role, record in expected_inputs.items()}}
    if model.get("binding") != binding:
        raise AcquisitionError("raw name model process or source binding differs")
    inventory_path = _safe_path(Path(inventory_path))
    inventory = model.get("inventory", {})
    if inventory.get("path") != str(inventory_path):
        raise AcquisitionError("raw name inventory path differs")
    files = dict(expected_inputs, normalized_inventory=inventory)

    def verify():
        for record in files.values():
            path = _safe_path(Path(record["path"]))
            if str(path) != record["path"] or _file_record(path) != {
                    "bytes": record["bytes"], "sha256": record["sha256"]}:
                raise AcquisitionError("raw name loader source changed")

    verify()
    buffers = {role: Path(files[role]["path"]).read_bytes() for role in (
        "native_inventory", "method_name_observation", "method_detail_inventory", "raw_parameter_observation", "normalized_inventory")}
    if any(hashlib.sha256(raw).hexdigest() != files[role]["sha256"] for role, raw in buffers.items()):
        raise AcquisitionError("raw name loader source changed during read")
    source_binding = dict(binding, inputs={role: expected_inputs[role]["sha256"] for role in _INPUT_ROLES})
    names, counts = project_raw_method_parameter_names(
        native_inventory=buffers["native_inventory"],
        parameter_observation=buffers["raw_parameter_observation"],
        method_observation=buffers["method_name_observation"],
        detail_inventory=buffers["method_detail_inventory"], expected_binding=source_binding,
        expected_method_count=expected_counts["method"],
        image_base=expected_identity["image_base"], image_bytes=expected_identity["image_bytes"])
    raw = buffers["normalized_inventory"]
    if (counts != model.get("counts") or
        decode_raw_metadata_names(raw, expected_binding=binding, expected_counts=expected_counts) != names or
        encode_raw_metadata_names(names, binding=binding, expected_counts=expected_counts) != raw):
        raise AcquisitionError("raw name source replay or roundtrip differs")
    verify()
    return names, counts


import stat
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_mode_ok
from alpha.p02 import runtime_inventory_contract
from alpha.h02 import file_identity


RUNTIME_INVENTORY_DISPATCH_SCHEMA = "alpha.runtime-inventory-dispatch/v1"
RUNTIME_INVENTORY_DISPATCH_MAGIC = b"ALPHAID1"
RUNTIME_INVENTORY_DISPATCH_VERSION = 1
RUNTIME_INVENTORY_DISPATCH_HEADER = struct.Struct("<8sIIII64s64sQ")
RUNTIME_INVENTORY_DISPATCH_ENTRY = struct.Struct("<IHHIIQQQ")


def _contract_digest(contract_id: str) -> str:
    prefix = "runtime-inventory-contract:sha256:"
    digest = contract_id.removeprefix(prefix)
    if not contract_id.startswith(prefix) or len(digest) != 64:
        raise AcquisitionError("runtime inventory contract id is invalid")
    try:
        bytes.fromhex(digest)
    except ValueError as error:
        raise AcquisitionError("runtime inventory contract digest is invalid") from error
    return digest


def _ascii_digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
        bytes.fromhex(value)
    except (UnicodeDecodeError, ValueError) as error:
        raise AcquisitionError(f"runtime inventory dispatch {label} is invalid") from error
    if len(value) != 64:
        raise AcquisitionError(
            f"runtime inventory dispatch {label} has an invalid length"
        )
    return value


def load_runtime_inventory_dispatch_manifest(
    path: Path,
    *,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime inventory dispatch manifest is unavailable")
    status = path.stat()
    if not owner_only_mode_ok(status, 0o600):
        raise AcquisitionError("runtime inventory dispatch manifest is not owner-only")
    contract = runtime_inventory_contract()
    expected_bytes = RUNTIME_INVENTORY_DISPATCH_HEADER.size + (
        contract["operation_count"] * RUNTIME_INVENTORY_DISPATCH_ENTRY.size
    )
    if status.st_size != expected_bytes:
        raise AcquisitionError("runtime inventory dispatch manifest size is invalid")
    data = path.read_bytes()
    (
        magic,
        version,
        header_bytes,
        operation_count,
        pointer_bytes,
        executable_raw,
        contract_raw,
        method_record_count,
    ) = RUNTIME_INVENTORY_DISPATCH_HEADER.unpack_from(data)
    executable_sha256 = _ascii_digest(executable_raw, label="executable binding")
    contract_sha256 = _ascii_digest(contract_raw, label="contract binding")
    if (
        magic != RUNTIME_INVENTORY_DISPATCH_MAGIC
        or version != RUNTIME_INVENTORY_DISPATCH_VERSION
        or header_bytes != RUNTIME_INVENTORY_DISPATCH_HEADER.size
        or operation_count != contract["operation_count"]
        or pointer_bytes != 8
        or contract_sha256 != _contract_digest(contract["contract_id"])
        or not method_record_count
    ):
        raise AcquisitionError("runtime inventory dispatch header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.casefold()
    ):
        raise AcquisitionError("runtime inventory dispatch target binding is stale")

    entries: list[dict[str, Any]] = []
    cursor = RUNTIME_INVENTORY_DISPATCH_HEADER.size
    for expected_index, operation in enumerate(contract["operations"]):
        (
            operation_index,
            parameter_count,
            reserved,
            name_candidate_count,
            arity_candidate_count,
            class_pointer,
            metadata_pointer,
            method_pointer,
        ) = RUNTIME_INVENTORY_DISPATCH_ENTRY.unpack_from(data, cursor)
        cursor += RUNTIME_INVENTORY_DISPATCH_ENTRY.size
        if (
            operation_index != expected_index
            or parameter_count != operation["parameter_count"]
            or reserved
            or not name_candidate_count
            or arity_candidate_count != 1
            or not class_pointer
            or not metadata_pointer
            or not method_pointer
        ):
            raise AcquisitionError(
                "runtime inventory dispatch operation is not uniquely resolved"
            )
        entries.append(
            {
                "key": operation["key"],
                "runtime_owners": operation["runtime_owners"],
                "runtime_name": operation["runtime_name"],
                "parameter_count": parameter_count,
                "name_candidate_count": name_candidate_count,
                "arity_candidate_count": arity_candidate_count,
                "class_pointer": class_pointer,
                "metadata_pointer": metadata_pointer,
                "method_pointer": method_pointer,
            }
        )
    if cursor != len(data):
        raise AcquisitionError("runtime inventory dispatch manifest has a trailer")
    return {
        "schema": RUNTIME_INVENTORY_DISPATCH_SCHEMA,
        "status": "complete",
        "identity": file_identity(path),
        "executable_sha256": executable_sha256,
        "contract_id": contract["contract_id"],
        "method_record_count": method_record_count,
        "operation_count": len(entries),
        "operations": entries,
        "owner_only": True,
    }


def inspect_runtime_inventory_dispatch_manifest(
    path: Path,
    *,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_inventory_dispatch_manifest(
        path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_INVENTORY_DISPATCH_SCHEMA,
        "status": model["status"],
        "identity": model["identity"],
        "executable_sha256": model["executable_sha256"],
        "contract_id": model["contract_id"],
        "method_record_count": model["method_record_count"],
        "operation_count": model["operation_count"],
        "all_operations_uniquely_resolved": model["operation_count"]
        == runtime_inventory_contract()["operation_count"],
        "raw_pointers_owner_only": True,
    }
