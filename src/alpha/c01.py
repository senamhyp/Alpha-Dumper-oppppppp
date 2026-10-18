import re
import shutil
import struct
import subprocess
import tempfile
from operator import attrgetter
from pathlib import Path

from alpha.h01 import AcquisitionError, DependencyUnavailable


_REGISTERS = {"rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi"} | {
    f"r{number}" for number in range(8, 16)
}
_VOLATILE = {"rax", "rcx", "rdx", "r8", "r9", "r10", "r11"}
_MEMORY = re.compile(r"(?:QWORD PTR )?\[(r(?:ax|cx|dx|bx|sp|bp|si|di|[89]|1[0-5]))(?:([+-])(0x[0-9a-f]+|[0-9]+))?\]")


_DECODE_LINE = re.compile(r"^\s*([0-9a-f]+):\s+(.+)$")


def decode_x64(code: bytes) -> tuple[tuple[int, str], ...]:
    tool = shutil.which("x86_64-w64-mingw32-objdump")
    if tool is None:
        raise DependencyUnavailable("x86-64 instruction decoder (MinGW objdump) unavailable")
    if not code:
        return ()
    with tempfile.TemporaryDirectory(prefix="alpha-abi-code-") as temporary:
        binary = Path(temporary) / "code.bin"
        binary.write_bytes(code)
        binary.chmod(0o600)
        result = subprocess.run([tool, "-D", "-z", "-b", "binary", "-m", "i386:x86-64",
                                 "-M", "intel", "--no-show-raw-insn", str(binary)],
                                capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=30, check=False)
    if result.returncode:
        raise AcquisitionError("x86-64 instruction decoding failed")
    instructions = []
    match_line = _DECODE_LINE.match
    for line in result.stdout.splitlines():
        match = match_line(line)
        if match:
            offset = int(match[1], 16)
            if offset >= len(code) or (instructions and offset <= instructions[-1][0]):
                raise AcquisitionError("x86-64 decoded instruction boundaries invalid")
            instructions.append((offset, match[2].strip().split("#", 1)[0].strip()))
    if not instructions or instructions[0][0] != 0:
        raise AcquisitionError("x86-64 instruction decoding is incomplete")
    return tuple(instructions)


_DECODE_BATCH_CHUNK = 512
_DECODE_FILE_HEADER = re.compile(r"^(code-\d{5}\.bin):\s+file format binary$")


_DECODE_BATCH_LINE = re.compile(r"^\s*([0-9a-f]+):\s+(.+)$")


def decode_x64_batch(codes: list[bytes]) -> list[tuple[tuple[int, str], ...]]:
    tool = shutil.which("x86_64-w64-mingw32-objdump")
    if tool is None:
        raise DependencyUnavailable("x86-64 instruction decoder (MinGW objdump) unavailable")
    results: list[tuple[tuple[int, str], ...]] = [() for _ in codes]
    indexed = [(index, code) for index, code in enumerate(codes) if code]
    for start in range(0, len(indexed), _DECODE_BATCH_CHUNK):
        chunk = indexed[start:start + _DECODE_BATCH_CHUNK]
        with tempfile.TemporaryDirectory(prefix="alpha-abi-code-") as temporary:
            entries: list[tuple[int, str, bytes]] = []
            for sequence, (index, code) in enumerate(chunk):
                binary = Path(temporary) / f"code-{sequence:05d}.bin"
                binary.write_bytes(code)
                binary.chmod(0o600)
                entries.append((index, binary.name, code))
            result = subprocess.run(
                [tool, "-D", "-z", "-b", "binary", "-m", "i386:x86-64",
                 "-M", "intel", "--no-show-raw-insn", *[name for _, name, _ in entries]],
                capture_output=True, text=True, encoding="utf-8", errors="replace",
                timeout=600, check=False, cwd=temporary)
        if result.returncode:
            raise AcquisitionError("x86-64 instruction decoding failed")
        by_name: dict[str, tuple[bytes, list[tuple[int, str]]]] = {
            name: (code, []) for _, name, code in entries}
        current_name = ""
        current_code = b""
        current_instructions: list[tuple[int, str]] = []
        match_header = _DECODE_FILE_HEADER.match
        match_line = _DECODE_BATCH_LINE.match
        for line in result.stdout.splitlines():
            header = match_header(line)
            if header:
                current_name = header[1]
                current_code, current_instructions = by_name[current_name]
                continue
            if not current_name:
                continue
            match = match_line(line)
            if match:
                offset = int(match[1], 16)
                if offset >= len(current_code) or (
                        current_instructions and offset <= current_instructions[-1][0]):
                    raise AcquisitionError("x86-64 decoded instruction boundaries invalid")
                current_instructions.append((offset, match[2].strip().split("#", 1)[0].strip()))
        for index, name, _ in entries:
            instructions = by_name[name][1]
            if not instructions or instructions[0][0] != 0:
                raise AcquisitionError("x86-64 instruction decoding is incomplete")
            results[index] = tuple(instructions)
    return results


def decode_x64_many(codes: list[bytes]) -> dict[bytes, tuple | AcquisitionError]:
    unique: list[bytes] = []
    for code in codes:
        if code and code not in unique:
            unique.append(code)
    results: dict[bytes, tuple | AcquisitionError] = {}
    if not unique:
        return results
    try:
        decoded = decode_x64_batch(unique)
        for code, rows in zip(unique, decoded):
            results[code] = rows
        return results
    except AcquisitionError:
        pass
    for code in unique:
        try:
            results[code] = decode_x64(code)
        except AcquisitionError as error:
            results[code] = error
    return results


def discover_interface_map_calls(code: bytes) -> tuple[tuple[int, int], ...]:

    instructions = decode_x64(code)
    if not instructions:
        return ()
    by_offset = {offset: index for index, (offset, _) in enumerate(instructions)}
    matches = set()

    def initial(origin):
        return {register: ("input", origin, register) for register in _REGISTERS}

    def address(operand, registers):
        match = _MEMORY.fullmatch(operand)
        if match is None:
            return None
        displacement = int(match[3], 0) if match[3] else 0
        if match[2] == "-":
            displacement = -displacement
        base = registers[match[1]]
        if base[0] == "address":
            return (base[1], base[2] + displacement)
        return (base, displacement)

    pending = [(0, initial(-1), {})]
    visited = set()
    while pending:
        index, registers, stores = pending.pop()
        if not 0 <= index < len(instructions):
            continue
        key = (index, tuple(sorted(registers.items())), frozenset(stores.items()))
        if key in visited:
            continue
        visited.add(key)
        if len(visited) > max(1024, len(instructions) * 256):
            raise AcquisitionError("interface-map ABI control-flow evidence exceeded bounded analysis")
        offset, instruction = instructions[index]
        pieces = instruction.split(None, 1)
        operation = pieces[0]
        operands = [part.strip() for part in pieces[1].split(",")] if len(pieces) == 2 else []
        successors = [index + 1]
        handled = False
        if operation.startswith("ret"):
            continue
        if operation.startswith("j"):


            try:
                target = int(operands[0], 0)
            except (ValueError, IndexError):
                target = None
            successors = [] if operation == "jmp" else [index + 1]
            if target in by_offset:
                successors.append(by_offset[target])
            handled = True
        if operation in ("nop", "nopl", "nopw", "endbr64"):
            handled = True
        if operation in ("mov", "movabs", "lea") and len(operands) == 2:
            destination, source = operands
            if destination in _REGISTERS:
                source_address = address(source, registers)
                if operation == "lea":
                    if source_address is None:
                        registers = initial(offset)
                        stores = {}
                    else:
                        registers[destination] = ("address", *source_address)
                elif source in _REGISTERS:
                    registers[destination] = registers[source]
                else:


                    registers[destination] = ("value", offset)
                handled = True
            else:
                destination_address = address(destination, registers)
                if operation == "mov" and destination_address is not None and source in _REGISTERS:
                    stores[destination_address] = registers[source]
                    handled = True
        if operation == "call":
            first, second = registers["r8"], registers["r9"]
            matched = False
            if (first[0] == second[0] == "address" and first[1] == second[1]
                and second[2] == first[2] + 8
                and registers["rcx"] != registers["rdx"]
                and stores.get((first[1], first[2] - 16)) == registers["rcx"]
                and stores.get((first[1], first[2] - 8)) == registers["rdx"]
                and code[offset:offset + 1] == b"\xe8" and offset + 5 <= len(code)):
                callee = offset + 5 + struct.unpack_from("<i", code, offset + 1)[0]
                matches.add((offset, callee))
                matched = True


            if not matched:
                stores.clear()
            for register in _VOLATILE:
                registers[register] = ("call-clobbered", offset, register)
            handled = True
        if operation in ("test", "cmp"):
            handled = True
        if not handled:
            registers = initial(offset)
            stores = {}
        pending.extend((successor, dict(registers), dict(stores)) for successor in successors)
    return tuple(sorted(matches))


from dataclasses import dataclass

from alpha.h01 import AcquisitionError


@dataclass(frozen=True)
class InterfaceSlotProjection:
    interface_method: int
    observed_source_method: int
    observed_interface_metadata: int
    observed_source_metadata: int
    virtual_slot: int
    declaration_method: int
    class_declaration_method: int | None
    implementation_method: int | None
    declaration_role: int


def project_interface_pair(mappings, *, target, interface, descriptor, offset,
                           expected_interface_methods, methods, target_lineage,
                           records, words, projection, metadata_indexes):
    if (not 0 <= target < len(records) or not 0 <= interface < len(records)
        or not descriptor or offset < 0 or not records[interface][1] & 0x20
        or len(mappings) != len(expected_interface_methods)
        or offset + len(mappings) > records[target][6]):
        raise AcquisitionError('interface slot projection pair domain is invalid')
    seen, slots, result = set(), set(), []
    for interface_method, source_method, interface_metadata, source_metadata in mappings:
        if (not 0 <= interface_method < len(methods) or not 0 <= source_method < len(methods)
            or interface_method not in expected_interface_methods or interface_method in seen
            or metadata_indexes.get(interface_metadata) != interface_method
            or metadata_indexes.get(source_metadata) != source_method):
            raise AcquisitionError('interface slot projection raw MethodInfo identity differs')
        declared = methods[interface_method]
        slot = declared[8]
        if (declared[0] != interface or not declared[5] & 0x40 or declared[5] & 0x10
            or not 0 <= slot < len(mappings) or slot in slots):
            raise AcquisitionError('interface slot projection own virtual domain differs')
        absolute = records[target][5] + offset + slot
        if not 0 <= absolute < len(words) or absolute >= len(projection.source_method_indexes):
            raise AcquisitionError('interface slot projection global range differs')
        if source_method != projection.source_method_indexes[absolute]:
            raise AcquisitionError('interface runtime map differs from observed vtable MethodDef')
        expected_metadata = words[absolute] if records[target][2] == 2 else methods[source_method][2]
        if source_metadata != expected_metadata:
            raise AcquisitionError('interface runtime map differs from observed vtable MethodInfo')
        declaration = projection.declaration_method_indexes[absolute]
        role = projection.declaration_roles[absolute]
        unimplemented = projection.unimplemented[absolute]
        if not 0 <= declaration < len(methods) or role not in (0, 1, 2) or unimplemented != (role != 0):
            raise AcquisitionError('interface vtable declaration role is invalid')
        resolved = methods[declaration]
        if (resolved[5] & 0x10 or resolved[9] & 1 or not resolved[5] & 0x40
            or bool(resolved[5] & 0x400) != bool(unimplemented)
            or resolved[10] != declared[10]):
            raise AcquisitionError('interface vtable declaration attributes/arity differ')
        if unimplemented and not records[target][1] & 0x80:
            raise AcquisitionError('unimplemented interface slot is on a nonabstract class')
        if role == 2:
            if (declaration != interface_method or (descriptor, interface_method)
                not in projection.interface_only_contexts.get(absolute, ())):
                raise AcquisitionError('unimplemented interface-only contract context differs')
            class_declaration = None
        else:
            if resolved[0] not in target_lineage:
                raise AcquisitionError('interface class declaration is outside its lineage')
            class_declaration = declaration
        result.append(InterfaceSlotProjection(interface_method, source_method, interface_metadata, source_metadata,
            offset + slot, declaration, class_declaration, None if unimplemented else declaration, role))
        seen.add(interface_method)
        slots.add(slot)
    if seen != expected_interface_methods or slots != set(range(len(mappings))):
        raise AcquisitionError('interface slot projection method domain is not closed')
    return result


from alpha.h01 import AcquisitionError


def direct_reference_getter(code):

    if not isinstance(code, bytes):
        raise AcquisitionError("module getter code is not bytes")
    if len(code) >= 5 and code[:3] == b"\x48\x8b\x41" and code[4] == 0xC3:
        offset, extent = int.from_bytes(code[3:4], "little", signed=True), 5
    elif len(code) >= 8 and code[:3] == b"\x48\x8b\x81" and code[7] == 0xC3:
        offset, extent = int.from_bytes(code[3:7], "little", signed=True), 8
    else:
        raise AcquisitionError("module string override is not a proven direct reference getter")
    if offset <= 0 or offset & 7 or offset > 1 << 20:
        raise AcquisitionError("module getter field displacement is outside its bounded reference domain")
    return {"byte_offset": offset, "code_hex": code[:extent].hex(), "instruction_bytes": extent}


def derive_operations(*, identity_rows, ancestry_rows, method_rows, module_operation, string_class, read_code):

    identities, descriptors, classes = {}, {}, {}
    for row in identity_rows:
        if (len(row) != 13 or row[0] in identities or not row[2] or row[2] in descriptors
                or not row[3] or row[3] in classes):
            raise AcquisitionError("module operation identity domain repeats or is invalid")
        identities[row[0]] = row; descriptors[row[2]] = row[0]; classes[row[3]] = row[0]
    parents = {}
    for row in ancestry_rows:
        if (len(row) != 5 or row[0] not in identities or row[0] in parents
                or row[2] != identities[row[0]][3] or row[1] not in (1, 2)
                or (row[1] == 1) != (row[3] == 0) or bool(row[3]) != bool(row[4])):
            raise AcquisitionError("module operation ancestry is inconsistent")
        if row[3] in classes and identities[classes[row[3]]][2] != row[4]:
            raise AcquisitionError("module operation parent class and descriptor disagree")
        parents[row[0]] = classes.get(row[3]) if row[3] else None
        if row[3] and row[3] not in classes:
            parents[row[0]] = "unresolved"
    if set(parents) != set(identities):
        raise AcquisitionError("module operation ancestry does not cover the selected TypeDef domain")
    if string_class not in classes:
        raise AcquisitionError("module operation has no independently derived String class")
    string_descriptor = identities[classes[string_class]][2]
    methods, metadata = {}, set()
    factory = []
    for index, row in enumerate(method_rows):
        if len(row) != 13 or row[0] not in identities or not row[2] or row[2] in metadata:
            raise AcquisitionError("module operation MethodDef ownership is invalid")
        metadata.add(row[2]); methods.setdefault(row[0], []).append((index, row))
        if (row[2] == module_operation.get("metadata_pointer") and
                row[3] == module_operation.get("method_pointer")):
            factory.append((index, row))
    if (len(factory) != 1 or factory[0][1][5] & 0x10 or factory[0][1][10]
            or factory[0][1][9] & 1 or factory[0][1][4] not in descriptors):
        raise AcquisitionError("resolved type-to-module operation does not bind a unique reference return")
    module_owner = descriptors[factory[0][1][4]]

    def lineage(owner):
        result, seen = [], set()
        while owner is not None:
            if owner == "unresolved":
                return None
            if owner in seen:
                raise AcquisitionError("module operation ancestry is cyclic")
            seen.add(owner); result.append(owner); owner = parents[owner]
        return result

    base_chain = lineage(module_owner)
    if base_chain is None:
        raise AcquisitionError("module return type has an unresolved root lineage")
    root = base_chain[-1]

    def string_virtual(row):
        return (row[4] == string_descriptor and not row[5] & 0x10 and row[5] & 0x40
                and not row[9] & 1 and not row[10] and 0 <= row[8] < 0xFFFF)

    roots = [(index, row) for index, row in methods.get(root, ()) if string_virtual(row)]
    if len(roots) != 1 or not roots[0][1][5] & 0x100:
        raise AcquisitionError("root virtual string operation is not structurally unique")
    slot = roots[0][1][8]


    slot_candidates: dict[int, list[tuple[int, tuple]]] = {}
    for declaring, entries in methods.items():
        matches = [
            (index, row) for index, row in entries
            if row[5] & 0x40 and row[8] == slot
        ]
        if matches:
            slot_candidates[declaring] = matches


    lineage_cache: dict[int | str, list[int] | None] = {}

    def cached_lineage(owner):
        if owner in lineage_cache:
            return lineage_cache[owner]
        trail: list[int] = []
        trail_set: set[int] = set()
        cursor = owner
        while cursor is not None:
            if cursor == "unresolved":
                for member in trail:
                    lineage_cache[member] = None
                return None
            if cursor in lineage_cache:
                tail = lineage_cache[cursor]
                if tail is None:
                    for member in trail:
                        lineage_cache[member] = None
                    return None
                chain = trail + list(tail)
                for member in trail:
                    lineage_cache[member] = chain[trail.index(member):]
                return chain
            if cursor in trail_set:
                raise AcquisitionError("module operation ancestry is cyclic")
            trail_set.add(cursor)
            trail.append(cursor)
            cursor = parents[cursor]
        for position, member in enumerate(trail):
            lineage_cache[member] = trail[position:]
        return trail

    resolved, rejected = [], []
    for owner in identities:
        chain = cached_lineage(owner)
        if chain is None or module_owner not in chain:
            continue
        override = None
        for declaring in chain:
            matches = slot_candidates.get(declaring)
            if matches:
                if len(matches) != 1 or not string_virtual(matches[0][1]):
                    raise AcquisitionError("module string virtual slot has conflicting declarations")
                override = matches[0]
                break
        if override is None or override[1][0] == root or override[1][5] & (0x100 | 0x400) or not override[1][3]:
            rejected.append({"type_index": owner, "reason": "no concrete inherited string override"})
            continue
        try:
            getter = direct_reference_getter(read_code(override[1][3]))
        except AcquisitionError as error:
            rejected.append({"type_index": owner, "reason": str(error)})
            continue
        resolved.append({"type_index": owner, "class_pointer": identities[owner][3],
            "declaring_type_index": override[1][0], "method_index": override[0],
            "method_pointer": override[1][3], "metadata_pointer": override[1][2],
            "lineage": chain, **getter})
    if not resolved:
        raise AcquisitionError("module string override has no bounded code-derived candidate")
    return {"schema": "alpha.module-name-operation-candidates/v1", "module_type_index": module_owner,
            "root_type_index": root, "root_string_method_index": roots[0][0], "virtual_slot": slot,
            "resolved": resolved, "rejected": rejected, "name_seed_used": False,
            "suffix_predicate_used": False, "fixed_offset_used": False,
            "live_module_class_coverage_proven": False, "getter_io_replayed": False,
            "module_name_role_proven": False, "metadata_complete": False}


from contextlib import contextmanager
from contextvars import ContextVar
from pathlib import Path

from alpha.h01 import AcquisitionError


_BINDING: ContextVar[tuple[int, int, str] | None] = ContextVar("metadata_process_binding", default=None)


def current_runtime_process_binding() -> tuple[int, int, str] | None:
    return _BINDING.get()


@contextmanager
def bind_runtime_process(identity):
    pid = identity.get("process_id")
    creation = identity.get("creation_filetime")
    path = identity.get("executable_path")
    if (type(pid) is not int or not 0 < pid <= 0xFFFFFFFF
        or type(creation) is not int or not 0 < creation <= 0xFFFFFFFFFFFFFFFF
        or not isinstance(path, str) or not Path(path).is_absolute()):
        raise AcquisitionError("runtime injection process binding is incomplete")
    token = _BINDING.set((pid, creation, path))
    try:
        yield
    finally:
        _BINDING.reset(token)


from alpha.h01 import AcquisitionError
from alpha.p01 import GLOBALS, WINDOW_PROC, DISPATCH
from alpha.p01 import GUARD

PROGRESS = r'''
static void write_progress(const char*status){
    wchar_t path[32768],pending[32768];
    if(swprintf(path,32768,L"%ls.progress.json",status_path)<0||
       swprintf(pending,32768,L"%ls.pending",path)<0)return;
    FILE*f=_wfopen(pending,L"wb");if(!f)return;
    fprintf(f,"{\"schema\":\"alpha.runtime-proto-serializer-progress/v1\","
        "\"status\":\"%s\",\"callback_active\":%ld,\"probe_stage\":%ld,"
        "\"exception_code\":%lu,\"dispatch_attempt\":%ld,\"dispatch_error\":%ld}\n",
        status,(long)InterlockedCompareExchange(&callback_active,0,0),
        (long)InterlockedCompareExchange(&probe_stage,0,0),
        (unsigned long)InterlockedCompareExchange(&probe_exception_code,0,0),
        (long)InterlockedCompareExchange(&dispatch_attempt,0,0),
        (long)InterlockedCompareExchange(&dispatch_error,0,0));
    if(fclose(f)){_wremove(pending);return;}_wchmod(pending,0600);
    if(!MoveFileExW(pending,path,MOVEFILE_REPLACE_EXISTING|MOVEFILE_WRITE_THROUGH))_wremove(pending);
}
'''


def harden_serializer_dispatch(source):
    def line(prefix, replacement):
        nonlocal source
        matches=[item for item in source.splitlines() if item.startswith(prefix)]
        if len(matches)!=1:
            raise AcquisitionError('serializer dispatch source contract changed: '+prefix)
        source=source.replace(matches[0],replacement,1)
    globals_=GLOBALS.replace('probe_exception_code,probe_phase','probe_exception_code')
    line('static LRESULT CALLBACK window_proc(', globals_ + GUARD.replace('capture_batch()', 'collect()')
         + WINDOW_PROC + PROGRESS)
    dispatch=DISPATCH.replace('message_cursor','capture_cursor').replace('message_count','input_count').replace('completed_probes','completed_count')
    line('static int dispatch(void)', dispatch)
    old='if(!ok){write_status("capture_failed",0);return 0;}'
    if source.count(old)!=1:
        raise AcquisitionError('serializer worker source contract changed')


    return source.replace(old,'if(!ok){if(InterlockedCompareExchange(&callback_active,0,0))return 0;write_status("capture_failed",0);return 0;}')


import hashlib
import json
import struct
from dataclasses import dataclass
from typing import Mapping, Sequence

from alpha.h01 import AcquisitionError


_HEADER = struct.Struct("<8sIIIIQQ32s")
_ROW = struct.Struct("<IIIIQQ")
_MAGIC = b"ALPHARN1"
_VERSION = 1
_NULL = 1
NAME_DOMAINS = {
    "type": 1, "method": 2, "parameter": 3, "field": 4,
    "property": 5, "event": 6, "type_reference": 7,
    "generic_parameter": 8, "image": 9, "module": 10, "assembly": 11,
    "type_namespace": 12,
    "type_reference_namespace": 13,
}
_MAX_NAMES = 16_000_000
_MAX_PAYLOAD = 256 * 1024 * 1024
_INDEX_GETTER = attrgetter("index")


@dataclass(frozen=True)
class RawMetadataName:
    domain: str
    index: int


    value: bytes | None


def _binding_digest(binding: Mapping[str, object], counts: Mapping[str, int]) -> bytes:
    required = {"executable_sha256", "process_id", "creation_filetime", "inputs"}
    if not isinstance(binding, Mapping) or set(binding) != required:
        raise AcquisitionError("raw-name binding fields are incomplete or unexpected")
    for key in ("process_id", "creation_filetime"):
        if type(binding[key]) is not int or not 0 < binding[key] < 1 << 64:
            raise AcquisitionError("raw-name process identity is invalid")
    inputs = binding["inputs"]
    if not isinstance(inputs, dict) or not inputs:
        raise AcquisitionError("raw-name source digest binding is empty")
    digests = [binding["executable_sha256"]]
    for key, digest in inputs.items():
        if not isinstance(key, str) or not key:
            raise AcquisitionError("raw-name source role is invalid")
        digests.append(digest)
    if any(not isinstance(value, str) or len(value) != 64 or
           any(char not in "0123456789abcdef" for char in value) for value in digests):
        raise AcquisitionError("raw-name source digest is invalid")
    if not isinstance(counts, Mapping) or not counts or any(domain not in NAME_DOMAINS or type(count) is not int or
                         not 0 <= count <= _MAX_NAMES for domain, count in counts.items()):
        raise AcquisitionError("raw-name domain counts are invalid")
    if sum(counts.values()) > _MAX_NAMES:
        raise AcquisitionError("raw-name domain exceeds resource bound")
    canonical = json.dumps({"binding": dict(binding), "counts": dict(counts)},
                           sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(canonical.encode("ascii")).digest()


def encode_raw_metadata_names(
    names: Sequence[RawMetadataName], *, binding: Mapping[str, object],
    expected_counts: Mapping[str, int],
) -> bytes:

    digest = _binding_digest(binding, expected_counts)
    if len(names) != sum(expected_counts.values()):
        raise AcquisitionError("raw-name domain count does not close")


    domain_order = sorted(expected_counts, key=NAME_DOMAINS.__getitem__)
    buckets: dict[str, list] = {domain: [] for domain in domain_order}
    seen = set()
    for name in names:
        if (not isinstance(name, RawMetadataName) or not isinstance(name.domain, str) or
            name.domain not in expected_counts or
            type(name.index) is not int or not 0 <= name.index < expected_counts[name.domain] or
            name.value is not None and not isinstance(name.value, bytes)):
            raise AcquisitionError("raw-name record is invalid")
        key = (name.domain, name.index)
        if key in seen:
            raise AcquisitionError("raw-name domain has duplicate indexes")
        seen.add(key)
        buckets[name.domain].append(name)
    strings = bytearray()
    rows = bytearray()
    position = 0
    ordered_count = 0
    row_pack = _ROW.pack
    for domain in domain_order:
        bucket = buckets[domain]
        bucket.sort(key=_INDEX_GETTER)
        domain_code = NAME_DOMAINS[domain]
        for name in bucket:
            value = name.value
            length = 0 if value is None else len(value)
            if position + length > _MAX_PAYLOAD:
                raise AcquisitionError("raw-name bytes exceed resource bound")
            rows.extend(row_pack(domain_code, name.index,
                                 _NULL if value is None else 0, 0,
                                 position, length))
            if value is not None:
                strings.extend(value)
            position += length
            ordered_count += 1
    return (_HEADER.pack(_MAGIC, _VERSION, _HEADER.size, _ROW.size, 0,
                         ordered_count, position, digest) + rows + strings)


def decode_raw_metadata_names(
    raw: bytes, *, expected_binding: Mapping[str, object],
    expected_counts: Mapping[str, int],
) -> tuple[RawMetadataName, ...]:

    digest = _binding_digest(expected_binding, expected_counts)
    if not isinstance(raw, bytes) or len(raw) < _HEADER.size:
        raise AcquisitionError("raw-name header is truncated")
    magic, version, header_size, row_size, reserved, count, size, source = _HEADER.unpack_from(raw)
    data_start = _HEADER.size + count * _ROW.size
    if (magic != _MAGIC or version != _VERSION or header_size != _HEADER.size or
        row_size != _ROW.size or reserved or source != digest or
        count != sum(expected_counts.values()) or size > _MAX_PAYLOAD or
        data_start + size != len(raw)):
        raise AcquisitionError("raw-name header, source binding or extent is invalid")
    names = []
    position = 0


    domain_cursor = [
        (NAME_DOMAINS[domain], domain, expected_counts[domain])
        for domain in sorted(expected_counts, key=NAME_DOMAINS.__getitem__)
    ]
    slot = 0
    domain_code, domain, remaining = domain_cursor[0] if domain_cursor else (0, "", 0)
    index = 0
    for kind, observed_index, flags, reserved, start, length in _ROW.iter_unpack(
            memoryview(raw)[_HEADER.size:data_start]):
        while not remaining:
            slot += 1
            if slot == len(domain_cursor):
                break
            domain_code, domain, remaining = domain_cursor[slot]
            index = 0
        if not remaining:
            raise AcquisitionError("raw-name record order, flags or range is invalid")
        if (kind != domain_code or observed_index != index or reserved or
            flags & ~_NULL or flags & _NULL and length or start != position or
            length > size - position):
            raise AcquisitionError("raw-name record order, flags or range is invalid")
        value = None if flags & _NULL else raw[data_start + start:data_start + start + length]
        names.append(RawMetadataName(domain, index, value))
        position += length
        index += 1
        remaining -= 1
    if position != size:
        raise AcquisitionError("raw-name payload contains unclaimed bytes")
    return tuple(names)


from alpha.h01 import AcquisitionError


def protect_reference_source(source, *, creation_filetime):
    if type(creation_filetime) is not int or not 0 < creation_filetime < 1 << 64:
        raise AcquisitionError("type-reference native creation binding is absent")
    def once(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise AcquisitionError("type-reference capture source seam differs")
        source = source.replace(old, new, 1)
    once("static int capture_batch(void){", _GUARD.replace("CREATION_FILETIME", str(creation_filetime)) +
         "\nstatic int capture_batch(void){if(!reference_instance_current()){failure_kind=15001u;return 0;}")
    once("_wremove(output_path);_wremove(status_path);", "")
    once("if(GetCurrentProcessId()!=expected_pid||", "if(!reference_instance_current()||GetCurrentProcessId()!=expected_pid||")
    once("FILE*out=_wfopen(output_path,L\"wb\");", "FILE*out=reference_private_output(output_path);")
    once("FILE*out=_wfopen(status_path,L\"wb\");", "FILE*out=reference_private_output(status_path);")
    once("int ok=write_output();", "int ok=reference_instance_current()&&write_output();")
    once(r'\"process_id\": %lu,\n', r'\"creation_filetime\": ' + str(creation_filetime) + r',\n  \"process_id\": %lu,\n')


    once(r'\"fixed_offset_used\": false', r'\"fixed_offset_used\": true')
    return source


_GUARD = r'''
#include <io.h>
#include <fcntl.h>
#include <sys/stat.h>
static int reference_instance_current(void) {
    FILETIME created, exited, kernel, user;
    if (GetCurrentProcessId() != expected_pid ||
        !GetProcessTimes(GetCurrentProcess(), &created, &exited, &kernel, &user)) return 0;
    return (((uint64_t)created.dwHighDateTime << 32) | created.dwLowDateTime) == CREATION_FILETIMEull;
}
static FILE *reference_private_output(const wchar_t *path) {
    int descriptor = _wopen(path, _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY, _S_IREAD | _S_IWRITE);
    if (descriptor < 0) return NULL;
    FILE *out = _fdopen(descriptor, "wb");
    if (!out) { _close(descriptor); _wremove(path); }
    return out;
}
'''


from alpha.h01 import AcquisitionError


def group_source_records(records):
    if not isinstance(records, dict): raise AcquisitionError("runtime source records are malformed")
    grouped = {}
    for record in records.values():
        if (not isinstance(record, dict) or not isinstance(record.get("path"), str) or not record["path"]
                or type(record.get("bytes")) is not int or record["bytes"] < 0
                or not isinstance(record.get("sha256"), str) or len(record["sha256"]) != 64
                or any(c not in "0123456789abcdef" for c in record["sha256"])):
            raise AcquisitionError("runtime source file record is malformed")
        expected = {"bytes":record["bytes"],"sha256":record["sha256"]}
        if record["path"] in grouped and grouped[record["path"]] != expected:
            raise AcquisitionError("runtime source roles disagree on the same file identity")
        grouped[record["path"]] = expected
    return grouped


from contextlib import contextmanager
from contextvars import ContextVar

from alpha.h01 import AcquisitionError


_ACTIVE = ContextVar("readonly_source_verification_transaction", default=None)
_STAT_KEYS = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns", "st_uid", "st_gid", "st_mode")


def _stamp(path):
    from alpha.p13 import _safe_path
    info = _safe_path(path).stat()
    return tuple(getattr(info, key) for key in _STAT_KEYS)


def verify_source(path, expected, hash_source):
    state = _ACTIVE.get()
    if state is None:
        if hash_source(path) != expected:
            raise AcquisitionError("raw member-name source file changed")
        return
    key = str(path)
    previous = state.get(key)
    current = _stamp(path)
    if previous is not None:
        if previous[1] != expected or previous[2] != current:
            raise AcquisitionError("source identity changed inside read-only verification transaction")
        return
    if len(state) >= 4096:
        raise AcquisitionError("read-only verification transaction source bound exceeded")
    if hash_source(path) != expected or _stamp(path) != current:
        raise AcquisitionError("source changed during transaction entry hash")
    state[key] = (path, dict(expected), current, hash_source)


@contextmanager
def source_verification_scope():
    if _ACTIVE.get() is not None:
        yield
        return
    state = {}
    token = _ACTIVE.set(state)
    try:
        yield


        for path, expected, original, hash_source in state.values():
            if (_stamp(path) != original or hash_source(path) != expected
                    or _stamp(path) != original):
                raise AcquisitionError("source changed before read-only verification commit")
    finally:
        _ACTIVE.reset(token)


def current_source_verification_active():
    return _ACTIVE.get() is not None


import array
from collections import Counter, defaultdict
from dataclasses import dataclass

from alpha.h01 import AcquisitionError


@dataclass(frozen=True)
class MethodDeclaration:
    owner: int
    metadata: int
    code: int
    attributes: int
    slot: int
    constructor: bool = False


@dataclass(frozen=True)
class InterfaceContract:
    target: int
    descriptor: int
    interface: int
    offset: int
    methods: tuple[int, ...]


@dataclass(frozen=True)
class DeclarationProjection:


    source_method_indexes: array.array
    declaration_method_indexes: array.array
    unimplemented: bytes


    declaration_roles: bytes
    interface_only_contexts: dict[int, tuple[tuple[int, int], ...]]
    counts: dict[str, int]


def project_vtable_declarations(*, records, words, native_entries, methods,
                               lineages, dispatch, native_methods, interface_contracts=()):

    if len(records) != len(lineages) or len(words) != len(native_entries) or not methods:
        raise AcquisitionError("vtable declaration input domains differ")
    index_mask, tag_mask, compared_tag = (dispatch[key] for key in ("index_mask", "tag_mask", "compared_tag"))
    if (type(index_mask) is not int or not 0 < index_mask < 0xFFFFFFFF
        or index_mask & (index_mask + 1) or tag_mask != (0xFFFFFFFF ^ index_mask)
        or type(compared_tag) is not int or compared_tag & ~tag_mask):
        raise AcquisitionError("vtable declaration dispatch masks are invalid")
    for owner, lineage in enumerate(lineages):
        if owner not in lineage or any(type(ancestor) is not int or not 0 <= ancestor < len(lineages) for ancestor in lineage):
            raise AcquisitionError("vtable declaration lineage is invalid")


        ordered = sorted(lineage, key=lambda ancestor: len(lineages[ancestor]))
        previous = frozenset()
        for ancestor in ordered:
            if lineages[ancestor] != previous | {ancestor}:
                raise AcquisitionError("vtable declaration lineage is not a closed chain")
            previous = lineages[ancestor]
    virtuals = defaultdict(list)
    owner_virtuals = defaultdict(set)
    for index, method in enumerate(methods):
        if not 0 <= method.owner < len(lineages):
            raise AcquisitionError("vtable MethodDef owner is outside the domain")
        if method.slot != 0xFFFF:
            virtuals[method.owner, method.slot].append(index)
            owner_virtuals[method.owner].add(index)
    interface_slots = defaultdict(list)
    interface_keys = set()
    for contract in interface_contracts:
        if (not 0 <= contract.target < len(records) or not 0 <= contract.interface < len(records)
            or not contract.descriptor or contract.offset < 0
            or not records[contract.interface][1] & 0x20
            or (contract.target, contract.descriptor) in interface_keys):
            raise AcquisitionError('vtable interface contract identity is invalid')
        interface_keys.add((contract.target, contract.descriptor))
        expected = owner_virtuals[contract.interface]
        if (len(contract.methods) != len(expected) or set(contract.methods) != expected
            or {methods[index].slot for index in expected} != set(range(len(expected)))
            or contract.offset + len(expected) > records[contract.target][6]):
            raise AcquisitionError('vtable interface contract slot domain is invalid')
        for index in contract.methods:
            method = methods[index]
            interface_slots[contract.target, contract.offset + method.slot].append((contract.descriptor, index))


    zero_owners = set()
    for owner, attributes, kind, reserved, klass, first, count in records:
        if kind == 1 and 0 <= first <= first + count <= len(words):
            if any(words[first + slot] == 0 for slot in range(count)):
                zero_owners.add(owner)
    zero_index = 0 & index_mask
    fallback = methods[zero_index]
    fallback_pointer_supported = (len(zero_owners) >= 2 and compared_tag != 0
        and (fallback.slot == 0xFFFF or fallback.constructor or bool(fallback.attributes & 0x10)))
    sources, declarations = array.array("I"), array.array("I")
    unimplemented = bytearray()
    roles = bytearray()
    interface_only = {}
    counts = Counter()
    cursor = 0
    for definition, record in enumerate(records):
        owner, attributes, kind, reserved, klass, first, count = record
        if (owner != definition or reserved or not klass or first != cursor or count < 0
            or first + count > len(words) or kind not in (0, 1, 2) or (kind == 0) != (count == 0)):
            raise AcquisitionError("vtable declaration source ranges are not closed")
        lineage = lineages[owner]
        for slot in range(count):
            raw, code = words[first + slot], native_entries[first + slot]
            is_raw_zero = kind == 1 and raw == 0
            is_shared_fallback = (kind == 2 and fallback_pointer_supported and raw == fallback.metadata)
            is_fallback = is_raw_zero or is_shared_fallback
            if kind == 1:
                if not 0 <= raw <= 0xFFFFFFFF:
                    raise AcquisitionError("encoded vtable word exceeds uint32")
                if raw & tag_mask == compared_tag:
                    raise AcquisitionError("encoded MethodSpec declaration projection is not yet proven")
                source = raw & index_mask
                if source >= len(methods):
                    raise AcquisitionError("vtable source MethodDef is outside the domain")
                expected_code = methods[source].code
                counts["encoded_source_slots"] += 1
            else:
                if not raw or raw not in native_methods:
                    raise AcquisitionError("vtable native MethodInfo is outside the domain")
                source, expected_code = native_methods[raw]
                if not 0 <= source < len(methods):
                    raise AcquisitionError("vtable native MethodDef is outside the domain")
                counts["native_pointer_source_slots"] += 1
            if code != expected_code:
                raise AcquisitionError("vtable executable address differs from its observed MethodInfo")
            declaration = source
            role = 0
            if is_fallback:
                if is_raw_zero and not (fallback.slot == 0xFFFF or fallback.constructor or fallback.attributes & 0x10):
                    raise AcquisitionError("raw zero source could itself be a virtual declaration")
                if is_shared_fallback and source != zero_index:
                    raise AcquisitionError("shared fallback MethodInfo identity conflicts")
                if not attributes & 0x80:
                    raise AcquisitionError("raw zero vtable slot is not on an abstract class")
                candidates = [index for ancestor in lineage for index in virtuals.get((ancestor, slot), ())]
                if candidates:
                    depth = max(len(lineages[methods[index].owner]) for index in candidates)
                    candidates = [index for index in candidates if len(lineages[methods[index].owner]) == depth]
                if not candidates:
                    contexts = tuple(sorted(set(interface_slots.get((owner, slot), ()))))
                    candidates = sorted({index for descriptor, index in contexts})
                    if len(candidates) == 1:
                        role = 2
                        interface_only[first + slot] = contexts
                else:
                    role = 1
                if len(candidates) != 1:
                    raise AcquisitionError(f"raw zero vtable declaration is absent or ambiguous (definition={owner}, slot={slot}, candidates={candidates}, source_kind={kind})")
                declaration = candidates[0]
                if not methods[declaration].attributes & 0x400:
                    raise AcquisitionError("raw zero nearest vtable declaration is not abstract")
                counts["raw_zero_abstract_slots" if is_raw_zero else "shared_fallback_abstract_slots"] += 1
            method = methods[declaration]
            is_unimplemented = bool(method.attributes & 0x400)
            if is_unimplemented:
                if not attributes & 0x80:
                    raise AcquisitionError('abstract vtable declaration belongs to a nonabstract class')
                role = role or 1
                counts['unimplemented_abstract_slots'] += 1
                counts['interface_only_unimplemented_slots' if role == 2 else 'class_abstract_unimplemented_slots'] += 1
                if not is_fallback:
                    counts['direct_abstract_declaration_slots'] += 1
            if ((role != 2 and method.owner not in lineage) or method.attributes & 0x10 or method.constructor):
                raise AcquisitionError("vtable declaration is not an instance method in its lineage")
            if not method.attributes & 0x40 or method.slot == 0xFFFF:
                raise AcquisitionError("vtable declaration is not virtual")
            sources.append(source)
            declarations.append(declaration)
            unimplemented.append(is_unimplemented)
            roles.append(role)
            counts["code_pointer_crosschecks"] += 1
        cursor += count
    if cursor != len(words):
        raise AcquisitionError("vtable declaration slot domain is not closed")
    counts["type_count"] = len(records)
    counts["slot_count"] = cursor
    counts["raw_zero_supporting_classes"] = len(zero_owners)
    return DeclarationProjection(sources, declarations, bytes(unimplemented), bytes(roles), interface_only, dict(counts))


from pathlib import Path
from typing import Any, Iterable

from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity, read_json


RUNTIME_OWNER_ROOT_SCHEMA = "alpha.runtime-owner-roots/v1"
MAXIMUM_OWNER_ROOT_MANIFEST_BYTES = 1024 * 1024


def _positive_integer(value: object) -> bool:
    return type(value) is int and value > 0


def load_runtime_owner_roots(
    path: Path,
    *,
    executable_sha256: str,
    image_base: int,
    image_bytes: int,
    required_owner_pairs: Iterable[tuple[str, str]],
    state_slot_rva: int | None = None,
    resolver_helper_rva: int | None = None,
) -> dict[str, Any]:

    path = path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime owner-root manifest is unavailable")
    if path.stat().st_size > MAXIMUM_OWNER_ROOT_MANIFEST_BYTES:
        raise AcquisitionError("runtime owner-root manifest exceeds its size bound")
    value = read_json(path)
    if not isinstance(value, dict) or value.get("schema") != RUNTIME_OWNER_ROOT_SCHEMA:
        raise AcquisitionError("runtime owner-root manifest schema is invalid")
    if (
        value.get("executable_sha256") != executable_sha256
        or value.get("image_base") != image_base
        or value.get("image_bytes") != image_bytes
    ):
        raise AcquisitionError("runtime owner-root manifest target binding is stale")
    observed_state_slot_rva = value.get("state_slot_rva")
    observed_resolver_helper_rva = value.get("resolver_helper_rva")
    if (
        not _positive_integer(observed_state_slot_rva)
        or not _positive_integer(observed_resolver_helper_rva)
        or observed_state_slot_rva >= image_bytes
        or observed_resolver_helper_rva >= image_bytes
    ):
        raise AcquisitionError("runtime owner-root resolver binding is invalid")
    if state_slot_rva is not None and observed_state_slot_rva != state_slot_rva:
        raise AcquisitionError("runtime owner-root state-slot binding is stale")
    if (
        resolver_helper_rva is not None
        and observed_resolver_helper_rva != resolver_helper_rva
    ):
        raise AcquisitionError("runtime owner-root helper binding is stale")

    required_pairs = tuple(sorted(required_owner_pairs))
    if len(set(required_pairs)) != len(required_pairs):
        raise AcquisitionError("runtime owner-root contract contains duplicates")
    owners = value.get("owners")
    if (
        type(value.get("owner_count")) is not int
        or value["owner_count"] != len(required_pairs)
        or not isinstance(owners, list)
        or len(owners) != len(required_pairs)
    ):
        raise AcquisitionError("runtime owner-root manifest count is inconsistent")
    roots: dict[str, int] = {}
    observed_pairs: list[tuple[str, str]] = []
    observed_pointers: set[int] = set()
    for record in owners:
        if not isinstance(record, dict):
            raise AcquisitionError("runtime owner-root record is invalid")
        namespace = record.get("namespace")
        type_name = record.get("type_name")
        class_pointer = record.get("class_pointer")
        if (
            not isinstance(namespace, str)
            or not namespace
            or not isinstance(type_name, str)
            or not type_name
            or not _positive_integer(class_pointer)
        ):
            raise AcquisitionError("runtime owner-root record is incomplete")
        pair = (namespace, type_name)
        owner = f"{namespace}.{type_name}"
        if pair in observed_pairs or class_pointer in observed_pointers:
            raise AcquisitionError("runtime owner-root manifest contains duplicates")
        observed_pairs.append(pair)
        observed_pointers.add(class_pointer)
        roots[owner] = class_pointer
    if tuple(sorted(observed_pairs)) != required_pairs:
        raise AcquisitionError("runtime owner-root manifest contract is stale")
    return {
        "schema": RUNTIME_OWNER_ROOT_SCHEMA,
        "identity": file_identity(path),
        "executable_sha256": executable_sha256,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "state_slot_rva": observed_state_slot_rva,
        "resolver_helper_rva": observed_resolver_helper_rva,
        "owner_count": len(roots),
        "roots": roots,
        "checks": {
            "schema_valid": True,
            "target_hash_bound": True,
            "snapshot_image_bound": True,
            "resolver_binding_bound": True,
            "required_owner_set_exact": True,
            "class_pointers_unique": True,
            "fixed_address_seed_used": False,
            "saved_reference_value_used": False,
        },
    }


import stat
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError, owner_only_mode_ok
from alpha.p01 import reflection_contract
from alpha.h02 import file_identity


RUNTIME_DISPATCH_SCHEMA = "alpha.runtime-reflection-dispatch/v1"
RUNTIME_DISPATCH_MAGIC = b"ALPHARD1"
RUNTIME_DISPATCH_VERSION = 1
RUNTIME_DISPATCH_HEADER = struct.Struct("<8sIIII64s64sQ")
RUNTIME_DISPATCH_ENTRY = struct.Struct("<IHHIIQQQ")


def _contract_digest(contract_id: str) -> str:
    prefix = "runtime-reflection-contract:sha256:"
    digest = contract_id.removeprefix(prefix)
    if not contract_id.startswith(prefix) or len(digest) != 64:
        raise AcquisitionError("runtime dispatch reflection contract id is invalid")
    try:
        bytes.fromhex(digest)
    except ValueError as error:
        raise AcquisitionError(
            "runtime dispatch reflection contract digest is invalid"
        ) from error
    return digest


def _ascii_digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
        bytes.fromhex(value)
    except (UnicodeDecodeError, ValueError) as error:
        raise AcquisitionError(f"runtime dispatch {label} is invalid") from error
    if len(value) != 64:
        raise AcquisitionError(f"runtime dispatch {label} has an invalid length")
    return value


def load_runtime_dispatch_manifest(
    path: Path,
    *,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    path = path.expanduser().resolve()
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError("runtime reflection dispatch manifest is unavailable")
    status = path.stat()
    if not owner_only_mode_ok(status, 0o600):
        raise AcquisitionError("runtime reflection dispatch manifest is not owner-only")
    contract = reflection_contract()
    expected_bytes = RUNTIME_DISPATCH_HEADER.size + (
        contract["operation_count"] * RUNTIME_DISPATCH_ENTRY.size
    )
    if status.st_size != expected_bytes:
        raise AcquisitionError("runtime reflection dispatch manifest size is invalid")
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
    ) = RUNTIME_DISPATCH_HEADER.unpack_from(data)
    executable_sha256 = _ascii_digest(executable_raw, label="executable binding")
    contract_sha256 = _ascii_digest(contract_raw, label="contract binding")
    if (
        magic != RUNTIME_DISPATCH_MAGIC
        or version != RUNTIME_DISPATCH_VERSION
        or header_bytes != RUNTIME_DISPATCH_HEADER.size
        or operation_count != contract["operation_count"]
        or pointer_bytes != 8
        or contract_sha256 != _contract_digest(contract["contract_id"])
        or not method_record_count
    ):
        raise AcquisitionError("runtime reflection dispatch header is invalid")
    if (
        expected_executable_sha256 is not None
        and executable_sha256 != expected_executable_sha256.casefold()
    ):
        raise AcquisitionError("runtime reflection dispatch target binding is stale")

    entries: list[dict[str, Any]] = []
    cursor = RUNTIME_DISPATCH_HEADER.size
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
        ) = RUNTIME_DISPATCH_ENTRY.unpack_from(data, cursor)
        cursor += RUNTIME_DISPATCH_ENTRY.size
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
                "runtime reflection dispatch operation is not uniquely resolved"
            )
        entries.append(
            {
                "key": operation["key"],
                "runtime_owner": operation["runtime_owner"],
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
        raise AcquisitionError("runtime reflection dispatch manifest has a trailer")
    return {
        "schema": RUNTIME_DISPATCH_SCHEMA,
        "status": "complete",
        "identity": file_identity(path),
        "executable_sha256": executable_sha256,
        "contract_id": contract["contract_id"],
        "method_record_count": method_record_count,
        "operation_count": len(entries),
        "operations": entries,
        "owner_only": True,
    }


def inspect_runtime_dispatch_manifest(
    path: Path,
    *,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model = load_runtime_dispatch_manifest(
        path,
        expected_executable_sha256=expected_executable_sha256,
    )
    return {
        "schema": RUNTIME_DISPATCH_SCHEMA,
        "status": model["status"],
        "identity": model["identity"],
        "executable_sha256": model["executable_sha256"],
        "contract_id": model["contract_id"],
        "method_record_count": model["method_record_count"],
        "operation_count": model["operation_count"],
        "all_operations_uniquely_resolved": model["operation_count"]
        == reflection_contract()["operation_count"],
        "raw_pointers_owner_only": True,
    }
