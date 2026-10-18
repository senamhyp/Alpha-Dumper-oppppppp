
import json
import os
import re
import struct
import subprocess
import time
from pathlib import Path
from string import Template
from typing import Any, Iterable, Mapping

from alpha.h01 import AcquisitionError, owner_uid
from alpha.h02 import file_identity, windows_run as _host_run
from alpha.p12 import (
    _build,
    _compiler,
    _owner_directory,
    _private_json,
    _private_text,
    _wide_literal,
    _windows_z_path,
    runtime_injector_source,
)


USAGE_PROBE_SCHEMA = "alpha.usage-live-probe/v1"
USAGE_PROBE_MAGIC = b"ALPHAPR1"
USAGE_PROBE_HEADER = struct.Struct("<8sIIIIQ")
USAGE_PROBE_RANGE = struct.Struct("<QQQQ")

_PROBE_TEMPLATE = Template(
    r'''
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

#define ALPHA_PROBE_MAGIC "ALPHAPR1"

static const wchar_t observation_output[] = $output_path;
static const wchar_t status_output[] = $status_path;
static const DWORD expected_process_id = ${process_id}u;
static const char expected_executable_sha256[] =
    "$executable_sha256";
static const uintptr_t expected_image_base = ${image_base}ull;

typedef struct probe_range {
    uintptr_t address;
    uint64_t bytes;
} probe_range;

static const probe_range probe_ranges[] = {
$range_rows
};
#define PROBE_RANGE_COUNT (sizeof(probe_ranges)/sizeof(probe_ranges[0]))

static void digest_hex(const unsigned char *digest, char output[65]) {
    static const char digits[] = "0123456789abcdef";
    for (int index = 0; index < 32; index++) {
        output[index * 2] = digits[digest[index] >> 4];
        output[index * 2 + 1] = digits[digest[index] & 15];
    }
    output[64] = 0;
}

static int sha256_file(const wchar_t *path, char output[65]) {
    HANDLE input = CreateFileW(
        path, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (input == INVALID_HANDLE_VALUE) return 0;
    BCRYPT_ALG_HANDLE algorithm = NULL;
    BCRYPT_HASH_HANDLE hash = NULL;
    DWORD object_size = 0, received = 0, read = 0;
    unsigned char *object = NULL, *buffer = NULL;
    unsigned char digest[32];
    int ok = BCryptOpenAlgorithmProvider(
        &algorithm, BCRYPT_SHA256_ALGORITHM, NULL, 0
    ) >= 0 && BCryptGetProperty(
        algorithm, BCRYPT_OBJECT_LENGTH, (PUCHAR)&object_size,
        sizeof(object_size), &received, 0
    ) >= 0 && object_size && received == sizeof(object_size);
    if (ok) object = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, object_size
    );
    if (ok) buffer = (unsigned char *)HeapAlloc(GetProcessHeap(), 0, 65536);
    if (ok && (!object || !buffer)) ok = 0;
    if (ok && BCryptCreateHash(
            algorithm, &hash, object, object_size, NULL, 0, 0
        ) < 0) ok = 0;
    while (ok) {
        if (!ReadFile(input, buffer, 65536, &read, NULL)) { ok = 0; break; }
        if (!read) break;
        if (BCryptHashData(hash, buffer, read, 0) < 0) ok = 0;
    }
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) < 0) ok = 0;
    if (ok) digest_hex(digest, output);
    if (hash) BCryptDestroyHash(hash);
    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);
    if (object) HeapFree(GetProcessHeap(), 0, object);
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    CloseHandle(input);
    return ok;
}

static int executable_identity(char output[65]) {
    wchar_t path[32768];
    DWORD length = GetModuleFileNameW(
        NULL, path, (DWORD)(sizeof(path) / sizeof(path[0]))
    );
    return length && length < sizeof(path) / sizeof(path[0]) &&
        sha256_file(path, output);
}

static int readable(uintptr_t value, SIZE_T bytes) {
    MEMORY_BASIC_INFORMATION region;
    if (!value || !bytes || value + bytes < value ||
        !VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Protect & PAGE_GUARD)
        return 0;
    DWORD protect = region.Protect & 0xffu;
    if (!protect || protect == PAGE_NOACCESS) return 0;
    uintptr_t end = (uintptr_t)region.BaseAddress + region.RegionSize;
    return end >= value && value + bytes <= end;
}

static void write_status(
    const char *status,
    const char *observed_sha256,
    uint64_t range_count,
    uint64_t readable_count,
    uint64_t bytes_written
) {
    FILE *output = _wfopen(status_output, L"wb");
    if (!output) return;
    fprintf(output,
        "{\n"
        "  \"schema\": \"$status_schema\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"image_base\": %llu,\n"
        "  \"range_count\": %llu,\n"
        "  \"readable_range_count\": %llu,\n"
        "  \"bytes_written\": %llu,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"read_only_probe\": true,\n"
        "  \"process_memory_mutated\": false\n"
        "}\n",
        status,
        (unsigned long)GetCurrentProcessId(),
        (unsigned long)expected_process_id,
        expected_executable_sha256,
        observed_sha256 ? observed_sha256 : "",
        (unsigned long long)expected_image_base,
        (unsigned long long)range_count,
        (unsigned long long)readable_count,
        (unsigned long long)bytes_written
    );
    fflush(output);
    fclose(output);
    _wchmod(status_output, 0600);
}

static DWORD WINAPI worker(LPVOID unused) {
    (void)unused;
    _wremove(observation_output);
    _wremove(status_output);
    char observed[65] = {0};
    if (GetCurrentProcessId() != expected_process_id ||
        !executable_identity(observed) ||
        strcmp(observed, expected_executable_sha256)) {
        write_status("identity_mismatch", observed, 0, 0, 0);
        return 0;
    }
    if ((uintptr_t)GetModuleHandleW(NULL) != expected_image_base) {
        write_status("image_mismatch", observed, 0, 0, 0);
        return 0;
    }
    FILE *output = _wfopen(observation_output, L"wb");
    if (!output) {
        write_status("output_unavailable", observed, 0, 0, 0);
        return 0;
    }
    uint64_t range_count = (uint64_t)PROBE_RANGE_COUNT;
    uint64_t payload = 0;
    for (uint64_t index = 0; index < range_count; index++)
        payload += probe_ranges[index].bytes;
    unsigned char header[32];
    memset(header, 0, sizeof(header));
    memcpy(header, ALPHA_PROBE_MAGIC, 8);
    uint32_t version = 1u, header_bytes = (uint32_t)sizeof(header);
    uint32_t count32 = (uint32_t)range_count;
    memcpy(header + 8, &version, 4);
    memcpy(header + 12, &header_bytes, 4);
    memcpy(header + 16, &count32, 4);
    memcpy(header + 24, &payload, 8);
    int ok = fwrite(header, 1, sizeof(header), output) == sizeof(header);
    uint64_t readable_count = 0, written = 0;
    for (uint64_t index = 0; ok && index < range_count; index++) {
        uintptr_t address = probe_ranges[index].address;
        uint64_t bytes = probe_ranges[index].bytes;
        int present = bytes && bytes <= (64ull << 20) &&
            readable(address, (SIZE_T)bytes);
        unsigned char meta[32];
        memset(meta, 0, sizeof(meta));
        memcpy(meta, &address, 8);
        memcpy(meta + 8, &bytes, 8);
        uint32_t present32 = present ? 1u : 0u;
        memcpy(meta + 16, &present32, 4);
        if (fwrite(meta, 1, sizeof(meta), output) != sizeof(meta)) ok = 0;
        if (ok && present) {
            if (fwrite((const void *)address, 1, (SIZE_T)bytes, output) !=
                (SIZE_T)bytes) ok = 0;
            else {
                readable_count++;
                written += bytes;
            }
        }
    }
    if (fclose(output)) ok = 0;
    if (ok) _wchmod(observation_output, 0600);
    else _wremove(observation_output);
    write_status(
        ok ? "complete" : "write_failed", observed,
        range_count, readable_count, written
    );
    return 0;
}

BOOL WINAPI DllMain(HINSTANCE instance, DWORD reason, LPVOID reserved) {
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {
        DisableThreadLibraryCalls(instance);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }
    return TRUE;
}
'''
)


def _range_rows(ranges: Iterable[tuple[int, int]]) -> str:
    return ",\n".join(
        f"    {{{address}ull, {bytes}ull}}"
        for address, bytes in ranges
    )


def prepare_usage_probe(
    *,
    process_id: int,
    executable_sha256: str,
    image_base: int,
    ranges: list[tuple[int, int]],
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    if (
        type(process_id) is not int
        or not 0 < process_id <= 0xFFFFFFFF
        or len(executable_sha256) != 64
        or any(character not in "0123456789abcdef" for character in executable_sha256)
    ):
        raise AcquisitionError("usage probe process binding is invalid")
    if (
        not ranges
        or len(ranges) > 512
        or any(
            type(address) is not int
            or address < 0x10000
            or type(bytes) is not int
            or not 0 < bytes <= (64 << 20)
            for address, bytes in ranges
        )
    ):
        raise AcquisitionError("usage probe range list is invalid")
    build_dir = _owner_directory(output_dir / "build-usage-probe")
    source_path = build_dir / "usage-live-probe.c"
    injector_source_path = build_dir / "usage-live-probe-injector.c"
    injector_path = build_dir / "alpha-usage-live-probe-injector.exe"
    observation_path = output_dir / "usage-live-probe.bin"
    status_path = output_dir / "usage-live-probe-status.private.json"
    collector_path = build_dir / "alpha-usage-live-probe.dll"
    _private_text(
        source_path,
        _PROBE_TEMPLATE.substitute(
            output_path=_wide_literal(_windows_z_path(observation_path)),
            status_path=_wide_literal(_windows_z_path(status_path)),
            process_id=process_id,
            executable_sha256=executable_sha256,
            image_base=image_base,
            range_rows=_range_rows(ranges),
            status_schema=USAGE_PROBE_SCHEMA,
        ),
    )
    _private_text(injector_source_path, runtime_injector_source())
    selected = _compiler(compiler)
    _build(
        [
            str(selected), "-O2", "-s", "-shared", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(source_path),
            "-o", str(collector_path), "-lbcrypt",
        ],
        label="usage live probe",
    )
    _build(
        [
            str(selected), "-O2", "-s", "-municode", "-Wall", "-Wextra",
            "-Wformat=2", "-Werror=format", str(injector_source_path),
            "-o", str(injector_path),
        ],
        label="usage live probe injector",
    )
    for artifact in (collector_path, injector_path):
        if not artifact.is_file() or not artifact.stat().st_size:
            raise AcquisitionError("usage live probe build is incomplete")
        artifact.chmod(0o600)
    plan = {
        "schema": USAGE_PROBE_SCHEMA,
        "status": "prepared",
        "process_id": process_id,
        "executable_sha256": executable_sha256,
        "image_base": image_base,
        "ranges": [[address, bytes] for address, bytes in ranges],
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "observation": str(observation_path),
        "status_path": str(status_path),
    }
    _private_json(output_dir / "usage-live-probe-plan.private.json", plan)
    return plan


def capture_usage_probe(
    *,
    plan: dict[str, Any],
    wine: Path,
    wineprefix: Path,
    process_name: str,
    timeout: float = 120.0,
) -> dict[str, Any]:
    injector = Path(plan["injector"]["path"])
    collector = Path(plan["collector"]["path"])
    status_path = Path(plan["status_path"])
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix.expanduser().resolve())
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine.expanduser().resolve()), injector, collector, process_name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError("usage live probe injector could not run") from error
    deadline = time.monotonic() + timeout
    status: dict[str, Any] | None = None
    while time.monotonic() < deadline:
        if status_path.is_file():
            try:
                candidate = json.loads(status_path.read_text())
            except (OSError, ValueError):
                candidate = None
            if isinstance(candidate, dict) and candidate.get("status"):
                status = candidate
                break
        time.sleep(0.2)
    if status is None:
        raise AcquisitionError(
            "usage live probe timed out "
            f"(injector_returncode={injected.returncode})"
        )
    if status.get("status") != "complete":
        raise AcquisitionError(
            "usage live probe failed "
            f"(status={status.get('status')}, "
            f"readable={status.get('readable_range_count')})"
        )
    return status


def read_usage_probe(path: Path) -> list[tuple[int, int, bytes]]:
    raw = path.read_bytes()
    if len(raw) < USAGE_PROBE_HEADER.size:
        raise AcquisitionError("usage probe observation is truncated")
    magic, version, header_bytes, count, reserved, payload = (
        USAGE_PROBE_HEADER.unpack_from(raw, 0)
    )
    if (
        magic != USAGE_PROBE_MAGIC
        or version != 1
        or header_bytes != USAGE_PROBE_HEADER.size
        or count > 512
    ):
        raise AcquisitionError("usage probe observation header is invalid")
    position = USAGE_PROBE_HEADER.size
    rows: list[tuple[int, int, bytes]] = []
    for _ in range(count):
        if position + USAGE_PROBE_RANGE.size > len(raw):
            raise AcquisitionError("usage probe observation record is truncated")
        address, bytes_count, present, marker = (
            USAGE_PROBE_RANGE.unpack_from(raw, position)
        )
        position += USAGE_PROBE_RANGE.size
        if marker:
            raise AcquisitionError("usage probe observation marker is invalid")
        if not present:
            rows.append((address, bytes_count, b""))
            continue
        if position + bytes_count > len(raw):
            raise AcquisitionError("usage probe observation payload is truncated")
        rows.append((address, bytes_count, raw[position:position + bytes_count]))
        position += bytes_count
    if position != len(raw):
        raise AcquisitionError("usage probe observation has trailing bytes")
    return rows


def _instruction_stream(image: Any, begin_rva: int, end_rva: int) -> list[Any]:
    from capstone import CS_ARCH_X86, CS_MODE_64, Cs

    offset = image.rva_to_offset(begin_rva)
    if offset is None:
        raise AcquisitionError("usage initializer code is unavailable")
    end_offset = image.rva_to_offset(end_rva - 1)
    if end_offset is None:
        raise AcquisitionError("usage initializer extent is unavailable")
    code = bytes(image._mapping[offset:end_offset + 1])
    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    decoder.detail = True
    return list(decoder.disasm(code, begin_rva))


_CALL_SITE_TARGETS_PATTERN = re.compile(rb"\xb9(?=.{4}\xe8)", re.DOTALL)


_CALL_SITE_TARGETS_CACHE_FINGERPRINT: tuple[int, ...] | None = None
_CALL_SITE_TARGETS_CACHE: dict[int, tuple[tuple[int, int, int], ...]] = {}


def _call_site_targets_fingerprint(image: Any) -> tuple[int, ...] | None:
    path = getattr(image, "path", None)
    if not isinstance(path, Path):
        return None
    try:
        status = os.stat(path)
    except OSError:
        return None
    return (
        str(path),
        status.st_dev,
        status.st_ino,
        status.st_size,
        status.st_mtime_ns,
        status.st_ctime_ns,
    )


def _call_site_targets(
    image: Any, *, limit: int = 8
) -> list[tuple[int, int, int]]:
    global _CALL_SITE_TARGETS_CACHE_FINGERPRINT, _CALL_SITE_TARGETS_CACHE
    fingerprint = _call_site_targets_fingerprint(image)
    if (
        fingerprint is not None
        and _CALL_SITE_TARGETS_CACHE_FINGERPRINT == fingerprint
    ):
        ranked = _CALL_SITE_TARGETS_CACHE.get(limit)
        if ranked is not None:
            return list(ranked)
    import struct as _struct
    from collections import Counter

    counts: Counter[int] = Counter()
    maximum: dict[int, int] = {}
    mapping = image._mapping
    unpack = _struct.unpack_from
    finditer = _CALL_SITE_TARGETS_PATTERN.finditer
    for section in image.executable_sections:
        base = section.raw_offset


        stop = section.raw_end - 6
        virtual_address = section.virtual_address
        for match in finditer(mapping, base, stop + 1):
            position = match.start()
            value = unpack("<I", mapping, position + 1)[0]
            if value >= 2_000_000:
                continue
            displacement = unpack("<i", mapping, position + 6)[0]
            target = virtual_address + (position - base) + 10 + displacement
            counts[target] += 1
            if value > maximum.get(target, -1):
                maximum[target] = value
    ranked = [
        (target, count, maximum.get(target, -1))
        for target, count in counts.most_common(limit)
    ]
    if fingerprint is not None:
        _CALL_SITE_TARGETS_CACHE_FINGERPRINT = fingerprint
        _CALL_SITE_TARGETS_CACHE = {limit: tuple(ranked)}
    return list(ranked)


def derive_usage_codec_v2(
    *,
    binary: Path,
    snapshot: MemorySnapshot,
) -> dict[str, Any]:
    from alpha.c04 import MappedPE

    binary = binary.expanduser().resolve()
    with MappedPE(binary) as image:
        ranked = _call_site_targets(image)
        if not ranked or ranked[0][1] < 1024:
            raise AcquisitionError(
                "usage initializer call sites are unavailable "
                f"(best={ranked[0][1] if ranked else 0})"
            )
        initializer_rva = ranked[0][0]
        call_site_max_index = ranked[0][2]
        function = image.containing_function(initializer_rva)
        if (
            function is None
            or function.begin_rva != initializer_rva
            or not 256 <= function.end_rva - function.begin_rva <= 16384
        ):
            raise AcquisitionError(
                "usage initializer extent is not a single bounded function"
            )
        instructions = _instruction_stream(
            image, function.begin_rva, function.end_rva
        )
        image_base = snapshot.image_base

        def rip_global(instruction: Any) -> int:
            operand = instruction.operands[-1]
            if operand.type != 3 or operand.mem.base != 41:
                raise AcquisitionError("usage codec global load is invalid")
            return image_base + instruction.address + instruction.size + operand.mem.disp

        def read_global(address: int) -> int:
            raw = snapshot.read(address, 8)
            if not raw:
                raise AcquisitionError("usage codec global is unreadable")
            return int.from_bytes(raw, "little")

        def descriptor_field(displacement: int) -> int:
            raw = snapshot.read(descriptor + displacement, 4)
            if not raw:
                raise AcquisitionError("usage descriptor field is unreadable")
            return int.from_bytes(raw, "little")


        descriptor = metadata_base = 0
        descriptor_global = metadata_base_global = 0
        for instruction in instructions[:32]:
            if instruction.mnemonic != "mov" or len(instruction.operands) != 2:
                continue
            destination, source = instruction.operands
            if destination.type != 1 or source.type != 3:
                continue
            if source.mem.base != 41 or not 8 <= destination.size <= 8:
                continue
            name = instruction.reg_name(destination.reg)
            if name == "r8" and not descriptor:
                descriptor_global = rip_global(instruction)
                descriptor = read_global(descriptor_global)
            elif name == "r12" and not metadata_base:
                metadata_base_global = rip_global(instruction)
                metadata_base = read_global(metadata_base_global)
        if not descriptor or not metadata_base:
            raise AcquisitionError(
                "usage descriptor or metadata base binding is absent"
            )


        range_add = range_field = None
        range_multiplier = range_second = range_mix = range_final_xor = None
        first_shift = second_shift = None
        for position, instruction in enumerate(instructions):
            if (
                instruction.mnemonic == "add"
                and len(instruction.operands) == 2
                and instruction.operands[0].type == 1
                and instruction.operands[1].type == 3
                and not instruction.operands[1].mem.index
                and instruction.reg_name(instruction.operands[1].mem.base)
                == "r8"
            ):
                previous = instructions[position - 1]
                if (
                    previous.mnemonic != "mov"
                    or len(previous.operands) != 2
                    or previous.operands[0].type != 1
                    or previous.operands[1].type != 2
                    or instruction.reg_name(previous.operands[0].reg)
                    != instruction.reg_name(instruction.operands[0].reg)
                ):
                    continue
                window = instructions[position + 1:position + 5]
                if not any(
                    item.mnemonic == "mov"
                    and len(item.operands) == 2
                    and item.operands[1].type == 3
                    and item.reg_name(item.operands[0].reg) == "r12"
                    for item in window
                ):
                    continue
                if not any(
                    item.mnemonic == "add"
                    and len(item.operands) == 2
                    and item.operands[1].type == 1
                    and item.reg_name(item.operands[1].reg) == "r12"
                    for item in window
                ):
                    continue
                range_add = previous.operands[1].imm & 0xFFFFFFFF
                range_field = instruction.operands[1].mem.disp
                break
        if range_add is None or range_field is None:
            raise AcquisitionError("usage range table binding is absent")
        wide: dict[str, int] = {}
        for instruction in instructions:
            if (
                instruction.mnemonic == "movabs"
                and len(instruction.operands) == 2
                and instruction.operands[-1].type == 2
                and 1 << 40 < instruction.operands[-1].imm < 1 << 56
            ):
                wide[instruction.reg_name(instruction.operands[0].reg)] = (
                    instruction.operands[-1].imm
                )
        index_sequences: list[dict[str, Any]] = []
        for position, instruction in enumerate(instructions):
            if (
                instruction.mnemonic != "imul"
                or len(instruction.operands) != 2
                or instruction.operands[1].type != 1
            ):
                continue
            source = instruction.reg_name(instruction.operands[1].reg)
            if source not in wide:
                continue
            tail = instructions[position + 1:position + 7]
            shifts = [
                item.operands[-1].imm
                for item in tail
                if item.mnemonic == "shr" and item.operands
            ]
            xors = [
                item.operands[-1].imm & 0xFFFFFFFF
                for item in tail
                if item.mnemonic == "xor"
                and item.operands
                and item.operands[-1].type == 2
            ]
            seconds = [
                item.operands[-1].imm
                for item in tail
                if item.mnemonic == "imul"
                and len(item.operands) == 3
                and item.operands[-1].type == 2
            ]
            if shifts and seconds:
                index_sequences.append(
                    {
                        "multiplier": wide[source],
                        "shifts": shifts,
                        "xors": xors,
                        "second": seconds[0],
                    }
                )
        if index_sequences:
            range_multiplier = index_sequences[0]["multiplier"]
            first_shift = index_sequences[0]["shifts"][0]
            range_second = index_sequences[0]["second"]
            if len(index_sequences[0]["shifts"]) > 1:
                second_shift = index_sequences[0]["shifts"][1]
        for instruction in instructions:
            if (
                instruction.mnemonic == "imul"
                and len(instruction.operands) == 3
                and instruction.operands[-1].type == 2
                and instruction.operands[-1].imm
                not in (range_multiplier, range_second)
            ):
                candidate = instruction.operands[-1].imm & 0xFFFFFFFF
                if range_mix is None and candidate and candidate < 0x100000000:
                    range_mix = candidate
                elif range_mix is not None and candidate != range_mix:
                    continue
            if (
                instruction.mnemonic == "xor"
                and len(instruction.operands) == 2
                and instruction.operands[0].type == 1
                and instruction.operands[1].type == 2
                and instruction.operands[1].imm > 0xFFFF
            ):
                if range_final_xor is None:
                    range_final_xor = instruction.operands[1].imm & 0xFFFFFFFF


        pair_field = pair_bias = None
        pair_multiplier = pair_multiplier2 = None
        pair_xor = pair_shift = pair_shift2 = None
        pair_add = pair_value_add = None
        for position, instruction in enumerate(instructions):
            if (
                instruction.mnemonic == "xor"
                and instruction.operands
                and instruction.operands[-1].type == 2
                and instruction.operands[-1].imm > 0xFFFF
                and instructions[position - 1].mnemonic in ("movsxd", "mov")
                and instructions[position - 1].operands
                and instructions[position - 1].operands[-1].type == 3
            ):
                bias = instruction.operands[-1].imm & 0xFFFFFFFF
                field = instructions[position - 1].operands[-1].mem.disp
                if field and pair_field is None:
                    pair_field = field
                    pair_bias = bias
        for sequence in index_sequences:
            if sequence["multiplier"] == range_multiplier:
                continue
            if pair_multiplier is None:
                pair_multiplier = sequence["multiplier"]
                pair_shift = sequence["shifts"][0]
                pair_xor = sequence["xors"][0] if sequence["xors"] else None
                pair_multiplier2 = sequence["second"]
                if len(sequence["shifts"]) > 1:
                    pair_shift2 = sequence["shifts"][1]
        known = {
            range_add,
            range_mix,
            range_final_xor,
            pair_xor,
            pair_shift,
            pair_shift2,
            first_shift,
            second_shift,
        }
        mixed_constants: list[int] = []
        for instruction in instructions:
            if (
                instruction.mnemonic == "mov"
                and len(instruction.operands) == 2
                and instruction.operands[0].type == 1
                and instruction.operands[0].size == 4
                and instruction.operands[1].type == 2
                and instruction.operands[1].imm is not None
            ):
                immediate = instruction.operands[1].imm & 0xFFFFFFFF
                if (
                    immediate < 0x10000000
                    or immediate in known
                    or immediate in mixed_constants
                ):
                    continue
                mixed_constants.append(immediate)
        if len(mixed_constants) >= 2:
            pair_add = mixed_constants[0]
            pair_value_add = mixed_constants[1]

    if (
        range_multiplier is None
        or range_second is None
        or range_mix is None
        or range_final_xor is None
        or first_shift is None
        or second_shift is None
        or pair_field is None
        or pair_bias is None
        or pair_multiplier is None
        or pair_multiplier2 is None
        or pair_xor is None
        or pair_shift is None
        or pair_shift2 is None
        or pair_add is None
        or pair_value_add is None
    ):
        raise AcquisitionError(
            "usage codec derivation is incomplete "
            f"(initializer={initializer_rva:#x})"
        )
    return {
        "initializer_rva": initializer_rva,
        "call_site_count": ranked[0][1],
        "call_site_max_index": call_site_max_index,
        "descriptor": descriptor,
        "metadata_base": metadata_base,
        "descriptor_global": descriptor_global,
        "metadata_base_global": metadata_base_global,
        "range_field": range_field,
        "range_add": range_add,
        "range_multiplier": range_multiplier,
        "range_first_shift": first_shift,
        "range_second_multiplier": range_second,
        "range_second_shift": second_shift,
        "range_mix_multiplier": range_mix,
        "range_final_xor": range_final_xor,
        "pair_field": pair_field,
        "pair_bias": pair_bias,
        "pair_multiplier": pair_multiplier,
        "pair_shift": pair_shift,
        "pair_xor": pair_xor,
        "pair_second_multiplier": pair_multiplier2,
        "pair_second_shift": pair_shift2,
        "pair_add": pair_add,
        "pair_value_add": pair_value_add,
    }


def decode_usage_pairs_v2(
    *,
    codec: Mapping[str, Any],
    snapshot: MemorySnapshot,
    dump: Mapping[int, bytes],
    index_limit: int = 2_000_000,
    occurrence_limit: int = 4_000_000,
) -> dict[str, Any]:
    mask32 = (1 << 32) - 1
    mask64 = (1 << 64) - 1
    import bisect as _bisect

    segments = sorted(
        (address, address + len(payload), bytes(payload))
        for address, payload in dump.items()
        if payload
    )
    starts = [segment[0] for segment in segments]

    def read(addr: int, count: int) -> bytes | None:
        out = bytearray()
        cursor = addr
        left = count
        while left:
            index = _bisect.bisect_right(starts, cursor) - 1
            if index < 0:
                return None
            begin, end, payload = segments[index]
            if not begin <= cursor < end:
                return None
            take = min(left, end - cursor)
            out += payload[cursor - begin:cursor - begin + take]
            cursor += take
            left -= take
        return bytes(out)

    descriptor = int(codec["descriptor"])
    metadata_base = int(codec["metadata_base"])
    descriptor_window = snapshot.read(descriptor, 0x400)
    if not descriptor_window:
        raise AcquisitionError("usage descriptor is unreadable")

    def field32(displacement: int) -> int:
        return struct.unpack_from("<I", descriptor_window, displacement)[0]

    def s32(value: int) -> int:
        return value - (1 << 32) if value >> 31 else value

    range_base = metadata_base + s32(
        (field32(codec["range_field"]) + codec["range_add"]) & mask32
    )
    pair_base = metadata_base + s32(
        (field32(codec["pair_field"]) ^ codec["pair_bias"]) & mask32
    )

    def range_value(index: int, encrypted: int) -> int:
        mixed = (index * codec["range_multiplier"]) & mask64
        mixed >>= codec["range_first_shift"]
        mixed = (mixed * codec["range_second_multiplier"]) & mask64
        mixed >>= codec["range_second_shift"]
        return (
            (encrypted ^ ((mixed * codec["range_mix_multiplier"]) & mask32))
            ^ codec["range_final_xor"]
        ) & mask32

    def pair_mix(index: int) -> int:
        mixed = (index * codec["pair_multiplier"]) & mask64
        mixed >>= codec["pair_shift"]
        mixed ^= codec["pair_xor"]
        mixed = (mixed * codec["pair_second_multiplier"]) & mask64
        mixed >>= codec["pair_second_shift"]
        return mixed & mask32


    ranges: list[int] = []
    previous = 0
    domain = int(codec.get("call_site_max_index", -1)) + 2
    if not 3 <= domain <= index_limit:
        raise AcquisitionError("usage index domain is unavailable")
    for index in range(domain):
        raw = read(range_base + index * 4, 4)
        if raw is None:
            raise AcquisitionError("usage range table is not fully captured")
        value = range_value(index, struct.unpack("<I", raw)[0])
        if index and value < previous:
            raise AcquisitionError("usage range table is not monotone")
        ranges.append(value)
        previous = value
    if ranges[0] != 0:
        raise AcquisitionError("usage range domain is unavailable")
    occurrences = ranges[-1]
    if occurrences <= 0 or occurrences > occurrence_limit:
        raise AcquisitionError("usage occurrence domain is out of bounds")

    pair_raw = read(pair_base, occurrences * 8)
    if pair_raw is None:


        raise AcquisitionError("usage pair table is not fully captured")

    records: list[dict[str, int]] = []
    kind_counts = [0] * 8
    for occurrence in range(occurrences):
        raw_destination, raw_encoded = struct.unpack_from(
            "<II", pair_raw, occurrence * 8
        )
        mixed = pair_mix(occurrence)
        encoded = ((raw_destination + codec["pair_add"]) & mask32) ^ mixed
        destination = ((raw_encoded + codec["pair_value_add"]) & mask32) ^ mixed


        kind = encoded >> 29
        source = encoded & 0x1FFFFFFF
        if kind >= 8:
            raise AcquisitionError("usage kind is out of range")
        kind_counts[kind] += 1
        records.append(
            {
                "first_occurrence_index": occurrence,
                "destination_index": destination,
                "usage_kind": kind,
                "source_index": source,
            }
        )
    return {
        "range_base": range_base,
        "pair_base": pair_base,
        "range_count": len(ranges),
        "occurrence_count": occurrences,
        "ranges": ranges,
        "kind_counts": kind_counts,
        "records": records,
    }


def derive_field_reference_codec_v2(
    *,
    binary: Path,
    snapshot: MemorySnapshot,
) -> dict[str, int]:
    from alpha.c04 import MappedPE

    binary = binary.expanduser().resolve()
    with MappedPE(binary) as image:
        ranked = _call_site_targets(image)
        if not ranked or ranked[0][1] < 1024:
            raise AcquisitionError("usage initializer call sites are unavailable")
        initializer_rva = ranked[0][0]
        function = image.containing_function(initializer_rva)
        if function is None or function.begin_rva != initializer_rva:
            raise AcquisitionError("usage initializer extent is unavailable")
        instructions = _instruction_stream(
            image, function.begin_rva, function.end_rva
        )
        image_base = snapshot.image_base
        descriptor = metadata_base = 0
        for instruction in instructions[:32]:
            if instruction.mnemonic != "mov" or len(instruction.operands) != 2:
                continue
            destination, source = instruction.operands
            if (
                destination.type != 1
                or source.type != 3
                or source.mem.base != 41
            ):
                continue
            address = (
                image_base + instruction.address + instruction.size
                + source.mem.disp
            )
            raw = snapshot.read(address, 8)
            if not raw:
                continue
            name = instruction.reg_name(destination.reg)
            if name == "r8" and not descriptor:
                descriptor = int.from_bytes(raw, "little")
            elif name == "r12" and not metadata_base:
                metadata_base = int.from_bytes(raw, "little")
        if not descriptor or not metadata_base:
            raise AcquisitionError("usage descriptor binding is absent")
        window = snapshot.read(descriptor, 0x400)
        if not window:
            raise AcquisitionError("usage descriptor is unreadable")


        targets = _switch_targets(image, function, instructions)
        if len(targets) != 8 or not targets[4]:
            raise AcquisitionError("usage kind dispatch is unavailable")
        handler_begin = targets[4]
        handler_end = min(
            [target for target in targets if target and target > handler_begin]
            or [handler_begin + 256]
        )
        if handler_end <= handler_begin:
            handler_end = handler_begin + 256
        handler = [
            instruction
            for instruction in instructions
            if handler_begin <= instruction.address < handler_end
        ]

        base_field = base_xor = None
        for position, instruction in enumerate(handler):
            if instruction.mnemonic not in ("movsxd", "mov"):
                continue
            if len(instruction.operands) != 2:
                continue
            destination, source = instruction.operands
            if (
                source.type != 3
                or source.size != 4
                or instruction.reg_name(source.mem.base) != "r8"
            ):
                continue
            register = instruction.reg_name(destination.reg)
            for follow in handler[position + 1:position + 3]:
                if (
                    follow.mnemonic == "xor"
                    and len(follow.operands) == 2
                    and follow.operands[1].type == 2
                    and follow.reg_name(follow.operands[0].reg) == register
                    and follow.operands[1].imm > 0xFFFF
                ):
                    candidate = follow.operands[1].imm & 0xFFFFFFFF
                    if candidate != 0x5E3191F6:
                        base_field = source.mem.disp
                        base_xor = candidate
                    break
            if base_field is not None:
                break

        multipliers: list[int] = []
        xors: list[int] = []
        adds: list[int] = []
        for position, instruction in enumerate(handler):
            if (
                instruction.mnemonic == "imul"
                and len(instruction.operands) == 3
                and instruction.operands[-1].type == 2
            ):
                value = instruction.operands[-1].imm & 0xFFFFFFFF
                if value not in (0x283B0DC2, 0x5612D438, 0x3691B541) and value:
                    multipliers.append(value)
            elif (
                instruction.mnemonic == "xor"
                and len(instruction.operands) == 2
                and instruction.operands[-1].type == 2
                and instruction.operands[-1].imm > 0xFFFF
            ):
                value = instruction.operands[-1].imm & 0xFFFFFFFF
                if value != base_xor:
                    xors.append(value)
            elif (
                instruction.mnemonic == "mov"
                and len(instruction.operands) == 2
                and instruction.operands[1].type == 2
                and instruction.operands[0].type == 1
                and instruction.operands[0].size == 4
                and instruction.operands[1].imm > 0xFFFF
            ):


                register = instruction.reg_name(instruction.operands[0].reg)
                following = handler[position + 1:position + 3]
                if any(
                    item.mnemonic == "xor"
                    and len(item.operands) == 2
                    and item.operands[1].type == 1
                    and item.reg_name(item.operands[1].reg) == register
                    for item in following
                ):
                    xors.append(instruction.operands[1].imm & 0xFFFFFFFF)
            elif (
                instruction.mnemonic == "add"
                and len(instruction.operands) == 2
                and instruction.operands[-1].type == 2
                and 0x100000 < instruction.operands[-1].imm < 0x10000000
            ):
                adds.append(instruction.operands[-1].imm & 0xFFFFFFFF)
        if base_field is None or base_xor is None:
            raise AcquisitionError("field reference base is unavailable")
        if len(multipliers) < 2 or len(xors) < 3 or not adds:
            raise AcquisitionError("field reference codec is incomplete")
        return {
            "descriptor": descriptor,
            "metadata_base": metadata_base,
            "field_base_field": base_field,
            "field_base_xor": base_xor,
            "index_multiplier": multipliers[0],
            "index_xor": xors[0],
            "index_mix_multiplier": multipliers[1],
            "index_mix_add": adds[0],
            "index_final_xor": xors[1],
            "value0_xor": xors[2],
            "value1_xor": xors[3] if len(xors) > 3 else xors[2],
        }


def _switch_targets(
    image: Any, function: Any, instructions: list[Any]
) -> list[int]:
    import struct as _struct

    for instruction in instructions:
        if (
            instruction.mnemonic != "lea"
            or len(instruction.operands) != 2
            or instruction.operands[1].type != 3
            or instruction.operands[1].mem.base != 41
        ):
            continue
        table = (
            image.rva_to_offset(instruction.address + instruction.size
                                + instruction.operands[1].mem.disp)
        )
        if table is None:
            continue
        raw = bytes(image._mapping[table:table + 32])
        if len(raw) < 32:
            continue
        targets = [
            instruction.address + instruction.size
            + instruction.operands[1].mem.disp
            + _struct.unpack_from("<i", raw, index * 4)[0]
            for index in range(8)
        ]
        if all(
            function.begin_rva <= target < function.end_rva
            for target in targets
        ) and len(set(targets)) >= 6:
            return targets
    raise AcquisitionError("usage switch table is unavailable")


def decode_field_references_v2(
    *,
    codec: Mapping[str, int],
    snapshot: MemorySnapshot,
    dump: Mapping[int, bytes],
    source_indices: Iterable[int],
) -> dict[int, tuple[int, int] | None]:
    import bisect as _bisect

    mask32 = (1 << 32) - 1
    segments = sorted(
        (address, address + len(payload), bytes(payload))
        for address, payload in dump.items()
        if payload
    )
    starts = [segment[0] for segment in segments]

    def read(addr: int, count: int) -> bytes | None:
        out = bytearray()
        cursor = addr
        left = count
        while left:
            index = _bisect.bisect_right(starts, cursor) - 1
            if index < 0:
                return None
            begin, end, payload = segments[index]
            if not begin <= cursor < end:
                return None
            take = min(left, end - cursor)
            out += payload[cursor - begin:cursor - begin + take]
            cursor += take
            left -= take
        return bytes(out)

    descriptor_window = snapshot.read(int(codec["descriptor"]), 0x400)
    if not descriptor_window:
        raise AcquisitionError("usage descriptor is unreadable")

    def field32(displacement: int) -> int:
        return struct.unpack_from("<I", descriptor_window, displacement)[0]

    def s32(value: int) -> int:
        return value - (1 << 32) if value >> 31 else value

    base = int(codec["metadata_base"]) + s32(
        (field32(int(codec["field_base_field"])) + int(codec["field_base_xor"]))
        & mask32
    )
    results: dict[int, tuple[int, int] | None] = {}
    for source in source_indices:
        raw = read(base + source * 8, 8)
        if raw is None:
            results[source] = None
            continue
        encoded0, encoded1 = struct.unpack("<II", raw)
        key = (source * int(codec["index_multiplier"])) & mask32
        key ^= int(codec["index_xor"])
        key = (key * int(codec["index_mix_multiplier"])) & mask32
        key = (key + int(codec["index_mix_add"])) & mask32
        key ^= int(codec["index_final_xor"])
        value0 = (((encoded0 ^ int(codec["value0_xor"])) & mask32) - key) & mask32
        value1 = (((encoded1 ^ int(codec["value1_xor"])) & mask32) - key) & mask32
        results[source] = (value0, value1)
    return results


def derive_method_spec_codec_v2(
    *,
    binary: Path,
    snapshot: MemorySnapshot,
) -> dict[str, int]:
    from alpha.c04 import MappedPE

    binary = binary.expanduser().resolve()
    with MappedPE(binary) as image:
        ranked = _call_site_targets(image)
        if not ranked or ranked[0][1] < 1024:
            raise AcquisitionError("usage initializer call sites are unavailable")
        initializer_rva = ranked[0][0]
        function = image.containing_function(initializer_rva)
        if function is None or function.begin_rva != initializer_rva:
            raise AcquisitionError("usage initializer extent is unavailable")
        instructions = _instruction_stream(
            image, function.begin_rva, function.end_rva
        )
        targets = _switch_targets(image, function, instructions)
        if len(targets) != 8 or not targets[6]:
            raise AcquisitionError("usage kind dispatch is unavailable")
        begin = targets[6]
        end = min(
            [target for target in targets if target and target > begin]
            or [begin + 512]
        )
        if end <= begin:
            end = begin + 512
        handler = [
            instruction
            for instruction in instructions
            if begin <= instruction.address < end
        ]
        descriptor = metadata_base = 0
        for instruction in instructions[:32]:
            if instruction.mnemonic != "mov" or len(instruction.operands) != 2:
                continue
            destination, source = instruction.operands
            if (
                destination.type != 1
                or source.type != 3
                or source.mem.base != 41
            ):
                continue
            address = (
                snapshot.image_base + instruction.address + instruction.size
                + source.mem.disp
            )
            raw = snapshot.read(address, 8)
            if not raw:
                continue
            name = instruction.reg_name(destination.reg)
            if name == "r8" and not descriptor:
                descriptor = int.from_bytes(raw, "little")
            elif name == "r12" and not metadata_base:
                metadata_base = int.from_bytes(raw, "little")
        if not descriptor or not metadata_base:
            raise AcquisitionError("usage descriptor binding is absent")
        base_field = base_xor = stride = None
        for position, instruction in enumerate(handler):
            if instruction.mnemonic not in ("movsxd", "mov"):
                continue
            if len(instruction.operands) != 2:
                continue
            destination, source = instruction.operands
            if (
                source.type != 3
                or source.size != 4
                or instruction.reg_name(source.mem.base) != "r8"
            ):
                continue
            register = instruction.reg_name(destination.reg)
            for follow in handler[position + 1:position + 3]:
                if (
                    follow.mnemonic == "xor"
                    and len(follow.operands) == 2
                    and follow.operands[1].type == 2
                    and follow.reg_name(follow.operands[0].reg) == register
                    and follow.operands[1].imm > 0xFFFF
                ):
                    base_field = source.mem.disp
                    base_xor = follow.operands[1].imm & 0xFFFFFFFF
                    break
            if base_field is not None:
                break
        for instruction in handler:
            if (
                instruction.mnemonic == "lea"
                and len(instruction.operands) == 2
                and instruction.operands[1].type == 3
                and instruction.operands[1].mem.scale in (2, 3, 4, 5, 8, 9)
            ):

                base = instruction.reg_name(instruction.operands[1].mem.base)
                index = instruction.reg_name(instruction.operands[1].mem.index)
                if base == index and instruction.operands[1].mem.scale == 2:
                    stride = 12
                    break
        if base_field is None or base_xor is None:
            raise AcquisitionError("method spec base is unavailable")
        if stride is None:
            stride = 12
        return {
            "descriptor": descriptor,
            "metadata_base": metadata_base,
            "method_spec_field": base_field,
            "method_spec_xor": base_xor,
            "method_spec_stride": stride,
        }


def observe_literal_layout(
    *,
    snapshot: MemorySnapshot,
    dump: Mapping[int, bytes] | None = None,
    slot_pointers: Iterable[int],
) -> dict[str, int]:
    def read(addr: int, count: int) -> bytes | None:
        return snapshot.read(addr, count)

    candidates = [(0x10, 0x14), (0x8, 0xC), (0x10, 0x18), (0xC, 0x10)]
    best: tuple[int, tuple[int, int]] | None = None
    for length_offset, data_offset in candidates:
        valid = 0
        for pointer in slot_pointers:
            header = read(pointer, data_offset + 8)
            if header is None or length_offset + 4 > len(header):
                continue
            length = struct.unpack_from("<I", header, length_offset)[0]
            if not 0 < length < 0x100000:
                continue
            body = read(pointer + data_offset, length * 2)
            if body is None or len(body) < length * 2:
                continue
            try:
                text = body[: length * 2].decode("utf-16-le")
            except UnicodeDecodeError:
                continue
            if not text or "\x00" in text:
                continue
            valid += 1
        if valid and (best is None or valid > best[0]):
            best = (valid, (length_offset, data_offset))
    if best is None or best[0] < 4:
        raise AcquisitionError("managed string layout is unavailable")
    observed = best[1]
    return {
        "string_length_offset": observed[0],
        "string_data_offset": observed[1],
    }


def decode_literals_v2(
    *,
    snapshot: MemorySnapshot,
    layout: Mapping[str, int],
    slot_pointers: Mapping[int, int],
) -> dict[int, str]:
    length_offset = int(layout["string_length_offset"])
    data_offset = int(layout["string_data_offset"])
    literals: dict[int, str] = {}
    for index, pointer in slot_pointers.items():
        header = snapshot.read(pointer, data_offset + 8)
        if not header:
            continue
        length = struct.unpack_from("<I", header, length_offset)[0]
        if not 0 < length < 0x100000:
            continue
        body = snapshot.read(pointer + data_offset, length * 2)
        if not body or len(body) < length * 2:
            continue
        try:
            literals[index] = body[: length * 2].decode("utf-16-le")
        except UnicodeDecodeError:
            continue
    return literals


def derive_literal_codec_v2(
    *,
    binary: Path,
    snapshot: MemorySnapshot,
) -> dict[str, int]:
    from alpha.c04 import MappedPE

    binary = binary.expanduser().resolve()
    with MappedPE(binary) as image:
        ranked = _call_site_targets(image)
        if not ranked or ranked[0][1] < 1024:
            raise AcquisitionError("usage initializer call sites are unavailable")
        function = image.containing_function(ranked[0][0])
        if function is None or function.begin_rva != ranked[0][0]:
            raise AcquisitionError("usage initializer extent is unavailable")
        instructions = _instruction_stream(
            image, function.begin_rva, function.end_rva
        )
        targets = _switch_targets(image, function, instructions)
        if len(targets) != 8 or not targets[5]:
            raise AcquisitionError("usage kind dispatch is unavailable")
        begin = targets[5]
        end = min(
            [target for target in targets if target and target > begin]
            or [begin + 256]
        )
        handler = [
            instruction
            for instruction in instructions
            if begin <= instruction.address < end
        ]
        base_field = base_xor = None
        index_multiplier = index_add = value_add = second_index_add = None
        descriptor_field = descriptor_bias = None
        for position, instruction in enumerate(handler):
            operands = instruction.operands
            if (
                instruction.mnemonic in ("movsxd", "mov")
                and len(operands) == 2
                and operands[1].type == 3
                and operands[1].size == 4
                and instruction.reg_name(operands[1].mem.base) == "r8"
            ):
                if base_field is None and instruction.mnemonic == "movsxd":
                    base_field = operands[1].mem.disp
                    for follow in handler[position + 1:position + 3]:
                        if (
                            follow.mnemonic == "xor"
                            and follow.operands[-1].type == 2
                            and follow.operands[-1].imm > 0xFFFF
                        ):
                            base_xor = follow.operands[-1].imm & 0xFFFFFFFF
                elif descriptor_field is None and instruction.mnemonic == "mov":
                    descriptor_field = operands[1].mem.disp
            elif (
                instruction.mnemonic == "imul"
                and len(operands) == 3
                and operands[-1].type == 2
                and index_multiplier is None
            ):
                index_multiplier = operands[-1].imm & 0xFFFFFFFF
            elif (
                instruction.mnemonic == "lea"
                and len(operands) == 2
                and operands[1].type == 3
                and operands[1].mem.base != 0
                and operands[1].mem.index == 0
                and operands[1].mem.disp
                and index_add is None
            ):
                index_add = operands[1].mem.disp & 0xFFFFFFFF
            elif (
                instruction.mnemonic == "mov"
                and len(operands) == 2
                and operands[0].type == 1
                and operands[1].type == 2
                and operands[1].imm > 0xFFFF
            ):
                register = instruction.reg_name(operands[0].reg)
                for follow in handler[position + 1:position + 3]:
                    if (
                        follow.mnemonic == "add"
                        and len(follow.operands) == 2
                        and follow.operands[1].type == 1
                        and follow.reg_name(follow.operands[1].reg) == register
                    ):
                        if value_add is None:
                            value_add = operands[1].imm & 0xFFFFFFFF
                        elif descriptor_bias is None and descriptor_field is not None:
                            descriptor_bias = operands[1].imm & 0xFFFFFFFF
                        break
            elif (
                instruction.mnemonic == "add"
                and len(operands) == 2
                and operands[1].type == 2
                and operands[1].imm > 0xFFFF
                and second_index_add is None
            ):
                second_index_add = operands[1].imm & 0xFFFFFFFF


        helper = None
        for instruction in handler:
            if (
                instruction.mnemonic == "call"
                and instruction.operands
                and instruction.operands[0].type == 2
            ):
                helper = instruction.operands[0].imm
        if helper is None:
            raise AcquisitionError("string literal byte codec helper is absent")
        helper_function = image.containing_function(helper)
        if helper_function is None:
            raise AcquisitionError("string literal byte codec helper is unavailable")
        helper_instructions = _instruction_stream(
            image, helper, max(helper_function.end_rva, helper + 256)
        )
        wide: list[int] = []
        for instruction in helper_instructions[:64]:
            if instruction.mnemonic == "movabs" and instruction.operands:
                value = instruction.operands[-1].imm & 0xFFFFFFFFFFFFFFFF
                if value > (1 << 32):
                    wide.append(value)
        if len(wide) < 5:
            raise AcquisitionError("string literal byte codec constants are absent")
        stream_step, key_multiplier, key_add, key_xor, key_bias = wide[:5]
        required = (
            base_field,
            base_xor,
            index_multiplier,
            index_add,
            value_add,
            second_index_add,
            descriptor_field,
            descriptor_bias,
        )
        if any(value is None for value in required):
            raise AcquisitionError(
                "string literal codec derivation is incomplete"
            )
        window = snapshot.read(snapshot.image_base, 8)
        del window
        return {
            "literal_stream_step": stream_step,
            "literal_key_multiplier": key_multiplier,
            "literal_key_add": key_add,
            "literal_key_xor": key_xor,
            "literal_key_bias": key_bias,
            "literal_base_field": base_field,
            "literal_base_xor": base_xor,
            "literal_index_multiplier": index_multiplier,
            "literal_index_add": index_add,
            "literal_value_add": value_add,
            "literal_second_index_add": second_index_add,
            "literal_descriptor_field": descriptor_field,
            "literal_descriptor_bias": descriptor_bias,
        }


def derive_generic_instance_contract_v2(
    *,
    binary: Path,
    snapshot: MemorySnapshot,
) -> dict[str, int]:
    from alpha.c04 import MappedPE

    binary = binary.expanduser().resolve()
    with MappedPE(binary) as image:
        ranked = _call_site_targets(image)
        if not ranked or ranked[0][1] < 1024:
            raise AcquisitionError("usage initializer call sites are unavailable")
        function = image.containing_function(ranked[0][0])
        if function is None or function.begin_rva != ranked[0][0]:
            raise AcquisitionError("usage initializer extent is unavailable")
        instructions = _instruction_stream(
            image, function.begin_rva, function.end_rva
        )
        targets = _switch_targets(image, function, instructions)
        if len(targets) != 8 or not targets[6]:
            raise AcquisitionError("usage kind dispatch is unavailable")
        begin = targets[6]
        end = min(
            [target for target in targets if target and target > begin]
            or [begin + 512]
        )
        handler = [
            instruction
            for instruction in instructions
            if begin <= instruction.address < end
        ]
        shift_stride = None
        global_field = None
        for position, instruction in enumerate(handler):
            if instruction.mnemonic != "shl":
                continue
            if len(instruction.operands) != 2 or instruction.operands[1].type != 2:
                continue
            stride = 1 << instruction.operands[1].imm
            for follow in handler[position + 1:position + 4]:
                if (
                    follow.mnemonic == "add"
                    and len(follow.operands) == 2
                    and follow.operands[1].type == 3
                    and follow.operands[1].mem.base != 0
                ):
                    shift_stride = stride
                    global_field = follow.operands[1].mem.disp
                    break
            if shift_stride is not None:
                break
        if shift_stride is None or global_field is None:
            raise AcquisitionError("generic instance stride is unavailable")

        global_address = None
        for instruction in handler:
            if (
                instruction.mnemonic == "mov"
                and len(instruction.operands) == 2
                and instruction.operands[1].type == 3
                and instruction.operands[1].mem.base == 41
            ):
                global_address = (
                    snapshot.image_base + instruction.address + instruction.size
                    + instruction.operands[1].mem.disp
                )
        if global_address is None:
            raise AcquisitionError("generic instance state global is unavailable")
        raw = snapshot.read(global_address, 8)
        if not raw:
            raise AcquisitionError("generic instance state global is unreadable")
        state = int.from_bytes(raw, "little")
        base_raw = snapshot.read(state + global_field, 8)
        if not base_raw:
            raise AcquisitionError("generic instance base is unreadable")
        base = int.from_bytes(base_raw, "little")
        if not base:
            raise AcquisitionError("generic instance base is absent")
        return {
            "generic_instance_state_global": state,
            "generic_instance_state_field": global_field,
            "generic_instance_base": base,
            "generic_instance_stride": shift_stride,
        }


def _observe_helper_table(
    *,
    image: Any,
    snapshot: MemorySnapshot,
    helper_rva: int,
    stride_shift: int,
) -> dict[str, int]:
    function = image.containing_function(helper_rva)
    if function is None:
        raise AcquisitionError("usage helper extent is unavailable")
    instructions = _instruction_stream(image, function.begin_rva, function.end_rva)
    global_address = None
    state_field = None
    for position, instruction in enumerate(instructions):
        if (
            instruction.mnemonic != "shl"
            or len(instruction.operands) != 2
            or instruction.operands[1].type != 2
            or instruction.operands[1].imm != stride_shift
        ):
            continue
        window = instructions[max(0, position - 6):position]
        for candidate in reversed(window):
            if (
                candidate.mnemonic == "mov"
                and len(candidate.operands) == 2
                and candidate.operands[1].type == 3
                and candidate.operands[1].mem.base == 41
            ):
                global_address = (
                    snapshot.image_base + candidate.address + candidate.size
                    + candidate.operands[1].mem.disp
                )
                break
        if global_address is None:
            continue
        for follow in instructions[position + 1:position + 4]:
            if (
                follow.mnemonic == "add"
                and len(follow.operands) == 2
                and follow.operands[1].type == 3
                and follow.operands[1].mem.base != 0
            ):
                state_field = follow.operands[1].mem.disp
                break
        if state_field is not None:
            break
    if global_address is None or state_field is None:
        raise AcquisitionError("usage helper table base is unavailable")
    raw = snapshot.read(global_address, 8)
    if not raw:
        raise AcquisitionError("usage helper state global is unreadable")
    state = int.from_bytes(raw, "little")
    base_raw = snapshot.read(state + state_field, 8)
    if not base_raw:
        raise AcquisitionError("usage helper table base is unreadable")
    return {
        "state_global": state,
        "state_field": state_field,
        "base": int.from_bytes(base_raw, "little"),
        "stride_shift": stride_shift,
    }


def derive_type_record_contract_v2(
    *,
    binary: Path,
    snapshot: MemorySnapshot,
) -> dict[str, int]:
    from alpha.c04 import MappedPE

    binary = binary.expanduser().resolve()
    with MappedPE(binary) as image:
        ranked = _call_site_targets(image)
        if not ranked or ranked[0][1] < 1024:
            raise AcquisitionError("usage initializer call sites are unavailable")
        function = image.containing_function(ranked[0][0])
        if function is None or function.begin_rva != ranked[0][0]:
            raise AcquisitionError("usage initializer extent is unavailable")
        instructions = _instruction_stream(
            image, function.begin_rva, function.end_rva
        )
        targets = _switch_targets(image, function, instructions)
        if len(targets) != 8 or not targets[1]:
            raise AcquisitionError("usage kind dispatch is unavailable")
        begin = targets[1]
        end = min(
            [target for target in targets if target and target > begin]
            or [begin + 256]
        )
        helper = None
        for instruction in instructions:
            if begin <= instruction.address < end and instruction.mnemonic == "call":
                operand = instruction.operands[0]
                if operand.type == 2:
                    helper = operand.imm
        if helper is None:
            raise AcquisitionError("type resolver helper is unavailable")
        result = _observe_helper_table(
            image=image, snapshot=snapshot, helper_rva=helper, stride_shift=4
        )
        result["helper_rva"] = helper
        return result


def derive_type_generic_record_contract_v2(
    *,
    binary: Path,
    snapshot: MemorySnapshot,
) -> dict[str, int]:
    from alpha.c04 import MappedPE

    binary = binary.expanduser().resolve()
    with MappedPE(binary) as image:
        ranked = _call_site_targets(image)
        if not ranked or ranked[0][1] < 1024:
            raise AcquisitionError("usage initializer call sites are unavailable")
        function = image.containing_function(ranked[0][0])
        if function is None or function.begin_rva != ranked[0][0]:
            raise AcquisitionError("usage initializer extent is unavailable")
        instructions = _instruction_stream(
            image, function.begin_rva, function.end_rva
        )
        targets = _switch_targets(image, function, instructions)
        if len(targets) != 8 or not targets[1]:
            raise AcquisitionError("usage kind dispatch is unavailable")
        begin = targets[1]
        end = min(
            [target for target in targets if target and target > begin]
            or [begin + 256]
        )
        resolver = None
        for instruction in instructions:
            if (
                begin <= instruction.address < end
                and instruction.mnemonic == "call"
                and instruction.operands
                and instruction.operands[0].type == 2
            ):
                resolver = instruction.operands[0].imm
        if resolver is None:
            raise AcquisitionError("type resolver is unavailable")
        extent = image.containing_function(resolver)
        if extent is None:
            raise AcquisitionError("type resolver extent is unavailable")


        candidates = [resolver]
        for instruction in _instruction_stream(image, resolver, extent.end_rva):
            if (
                instruction.mnemonic == "call"
                and instruction.operands
                and instruction.operands[0].type == 2
            ):
                candidates.append(instruction.operands[0].imm)
        code_table = None
        dispatcher_extent = None
        for candidate_function in candidates:
            candidate_extent = image.containing_function(candidate_function)
            if candidate_extent is None:
                continue
            candidate_instructions = _instruction_stream(
                image, candidate_function, candidate_extent.end_rva
            )
            for instruction in candidate_instructions:
                operands = instruction.operands
                if (
                    instruction.mnemonic != "lea"
                    or len(operands) != 2
                    or operands[1].type != 3
                    or operands[1].mem.base != 41
                ):
                    continue
                table = (
                    instruction.address + instruction.size
                    + operands[1].mem.disp
                )
                offset = image.rva_to_offset(table)
                if offset is None:
                    continue
                raw = image._mapping[offset:offset + 0x1E * 4]
                if len(raw) != 0x1E * 4:
                    continue
                entries = struct.unpack("<30i", raw)
                resolved = [table + entry for entry in entries]
                if all(
                    candidate_extent.begin_rva
                    <= entry
                    < candidate_extent.end_rva
                    for entry in resolved
                ) and len(set(resolved)) >= 12:
                    code_table = (table, resolved)
                    dispatcher_extent = candidate_extent
                    break
            if code_table is not None:
                break
        if code_table is None or dispatcher_extent is None:
            raise AcquisitionError("type code dispatch is unavailable")
        arm = code_table[1][0x14]
        arm_instructions = _instruction_stream(
            image, arm, min(dispatcher_extent.end_rva, arm + 96)
        )
        state_global = None
        stride_shift = None
        state_field = None
        for position, instruction in enumerate(arm_instructions):
            if instruction.mnemonic in ("mov", "movabs") and len(instruction.operands) == 2:
                operand = instruction.operands[1]
                if operand.type == 3 and operand.mem.base == 41:
                    state_global = (
                        snapshot.image_base + instruction.address
                        + instruction.size + operand.mem.disp
                    )
            if (
                instruction.mnemonic == "shl"
                and len(instruction.operands) == 2
                and instruction.operands[1].type == 2
            ):
                stride_shift = instruction.operands[1].imm
                for follow in arm_instructions[position + 1:position + 3]:
                    if (
                        follow.mnemonic == "add"
                        and len(follow.operands) == 2
                        and follow.operands[1].type == 3
                        and follow.operands[1].mem.base != 0
                    ):
                        state_field = follow.operands[1].mem.disp
                        break
            if stride_shift is not None and state_field is not None:
                break
        if state_global is None or stride_shift is None or state_field is None:
            raise AcquisitionError("type generic record contract is unavailable")
        if not 4 <= stride_shift <= 8:
            raise AcquisitionError("type generic record stride is invalid")
        base_raw = snapshot.read(state_global + state_field, 8)
        if not base_raw:
            raise AcquisitionError("type generic record base is unreadable")
        return {
            "state_global": state_global,
            "state_field": state_field,
            "stride_shift": stride_shift,
            "base": int.from_bytes(base_raw, "little"),
        }


METHOD_SPEC_RECORD = struct.Struct("<iii")


def decode_method_specs_v2(
    *,
    codec: Mapping[str, int],
    generic: Mapping[str, int],
    snapshot: MemorySnapshot,
    source_indices: Iterable[int],
    image_base: int,
    image_bytes: int,
) -> dict[int, tuple[int, int, int] | None]:
    window = snapshot.read(int(codec["descriptor"]), 0x400)
    if not window:
        raise AcquisitionError("usage descriptor is unreadable")
    field = int(codec["method_spec_field"])
    if field + 4 > len(window):
        raise AcquisitionError("method spec field is unavailable")

    def s32(value: int) -> int:
        return value - (1 << 32) if value >> 31 else value

    base = int(codec["metadata_base"]) + s32(
        (struct.unpack_from("<I", window, field)[0] ^ int(codec["method_spec_xor"]))
        & 0xFFFFFFFF
    )
    results: dict[int, tuple[int, int, int] | None] = {}
    for source in source_indices:
        raw = snapshot.read(base + source * int(codec["method_spec_stride"]), 12)
        if raw is None:
            results[source] = None
            continue
        first, second, method_index = METHOD_SPEC_RECORD.unpack(raw)
        valid = True
        for index in (first, second):
            if index == -1:
                continue
            if not 0 <= index < 2_000_000:
                valid = False
                break
            pointer = int(generic["generic_instance_base"]) + index * int(
                generic["generic_instance_stride"]
            )
            if not image_base <= pointer < image_base + image_bytes:
                valid = False
                break
            record = snapshot.read(pointer, 16)
            if not record:
                valid = False
                break
            count, arguments = struct.unpack("<QQ", record)
            if not 1 <= count <= 64:
                valid = False
                break
            if not snapshot.read(arguments, 8):
                valid = False
                break
        if not 0 <= method_index < 2_000_000:
            valid = False
        results[source] = (first, second, method_index) if valid else None
    return results
