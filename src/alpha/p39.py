from alpha.h02 import windows_run as _host_run

import json
import os
import stat
import struct
import subprocess
import time
from collections import Counter
from pathlib import Path
from string import Template
from typing import Any

from alpha.p12 import _compiler, _owner_directory, _private_json, _private_text, _seal_runtime_output, _wide_literal, _windows_z_path, cached_windows_build
from alpha.h01 import AcquisitionError, owner_uid, owner_only_path_bits
from alpha.c06 import LiveRuntimeInventory
from alpha.p29 import _runtime
from alpha.p19 import RUNTIME_TYPE_IDENTITY_SCHEMA, _IDENTITY_HEADER, _IDENTITY_MAGIC, _IDENTITY_RECORD, _IDENTITY_VERSION
from alpha.p25 import RUNTIME_TYPE_REFERENCE_MAGIC, RUNTIME_TYPE_REFERENCE_HEADER, RUNTIME_TYPE_REFERENCE_RECORD, RUNTIME_TYPE_REFERENCE_SCHEMA, RUNTIME_TYPE_REFERENCE_VERSION
from alpha.h02 import file_identity, read_json, sha256_file


RUNTIME_TYPE_DESCRIPTOR_VALUE_SCHEMA = (
    "alpha.runtime-type-descriptor-value-inventory/v1"
)
RUNTIME_TYPE_DESCRIPTOR_VALUE_MAGIC = b"ALPHATV1"
RUNTIME_TYPE_DESCRIPTOR_VALUE_VERSION = 1
RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER = struct.Struct(
    "<8sIIIIQQQ64s64s64s"
)
RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD = struct.Struct("<QQQQ")


def _owner_file(path: Path, *, label: str) -> Path:
    path = path.expanduser().resolve()
    if (
        not path.is_file()
        or path.is_symlink()
        or False
        or owner_only_path_bits(path)
    ):
        raise AcquisitionError(
            f"runtime type descriptor value {label} is not owner-only"
        )
    return path


_COLLECTOR = Template(r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <tlhelp32.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

typedef struct identity_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t type_count, image_base, image_bytes, string_bytes;
    char executable_sha256[64], native_sha256[64], semantics_sha256[64];
} identity_header;
typedef struct identity_record {
    uint32_t definition_index, flags;
    uint64_t descriptor, class_pointer, module_pointer, declaring_descriptor;
    uint64_t type_object;
    uint32_t attributes, name_bytes, namespace_bytes, reserved;
    uint64_t name_offset, namespace_offset;
} identity_record;
typedef struct native_header {
    char magic[8]; uint32_t version, type_record_bytes, method_record_bytes;
    uint32_t reserved; uint64_t type_count, method_count, image_bytes;
    char executable_sha256[64], model_sha256[64]; uint32_t layout[8];
} native_header;
typedef struct native_type {
    uint32_t definition_index, name_bytes;
    uint64_t type_flags, descriptor_rva, class_pointer, parent_pointer;
    uint64_t declaring_pointer;
    uint32_t method_count, reserved;
    uint64_t method_start, name_offset;
} native_type;
typedef struct reference_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t node_count, seed_count, interface_count, argument_count;
    uint64_t string_bytes, image_base, image_bytes;
    char executable_sha256[64], seed_sha256[64], identity_sha256[64];
    char graph_sha256[64], semantics_sha256[64];
} reference_header;
typedef struct reference_record {
    uint64_t descriptor, canonical, type_object;
    uint32_t attributes, shape, name_bytes, namespace_bytes;
    uint32_t interface_count, argument_count, rank, reserved;
    uint64_t base, declaring, element, generic_definition;
    uint64_t interface_start, argument_start, name_offset, namespace_offset;
} reference_record;
typedef struct output_header {
    char magic[8]; uint32_t version, header_bytes, record_bytes, reserved;
    uint64_t node_count, root_substitution_count, process_id;
    char executable_sha256[64], reference_sha256[64], native_sha256[64];
} output_header;
typedef struct output_record {
    uint64_t descriptor, current_pointer, data, bits;
} output_record;
typedef struct root_pair { uint64_t old_pointer, current_pointer; } root_pair;

_Static_assert(sizeof(identity_header) == $identity_header_bytes, "identity header");
_Static_assert(sizeof(identity_record) == $identity_record_bytes, "identity record");
_Static_assert(sizeof(native_header) == $native_header_bytes, "native header");
_Static_assert(sizeof(native_type) == $native_type_bytes, "native type");
_Static_assert(sizeof(reference_header) == $reference_header_bytes, "reference header");
_Static_assert(sizeof(reference_record) == $reference_record_bytes, "reference record");
_Static_assert(sizeof(output_header) == $output_header_bytes, "output header");
_Static_assert(sizeof(output_record) == $output_record_bytes, "output record");

static const wchar_t process_name[] = $process_name;
static const wchar_t identity_path[] = $identity_path;
static const wchar_t native_path[] = $native_path;
static const wchar_t reference_path[] = $reference_path;
static const wchar_t output_path[] = $output_path;
static const uint64_t expected_pid = $process_id;
static const uint64_t expected_type_count = $type_count;
static const uint64_t expected_node_count = $node_count;
static const uint64_t descriptor_offset = $descriptor_offset;
static const char executable_sha256[] = "$executable_sha256";
static const char reference_sha256[] = "$reference_sha256";
static const char native_sha256[] = "$native_sha256";

static int read_file(const wchar_t *path, unsigned char **data, uint64_t *size) {
    FILE *input = _wfopen(path, L"rb");
    if (!input) return 0;
    if (_fseeki64(input, 0, SEEK_END) || (*size = (uint64_t)_ftelli64(input)) == 0 ||
        _fseeki64(input, 0, SEEK_SET) || *size > SIZE_MAX) {
        fclose(input); return 0;
    }
    *data = (unsigned char *)malloc((size_t)*size);
    int ok = *data && fread(*data, 1, (size_t)*size, input) == (size_t)*size;
    if (fclose(input)) ok = 0;
    if (!ok) { free(*data); *data = NULL; }
    return ok;
}

static DWORD unique_process(int *matches) {
    *matches = 0; DWORD selected = 0;
    HANDLE snapshot = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (snapshot == INVALID_HANDLE_VALUE) return 0;
    PROCESSENTRY32W entry; memset(&entry, 0, sizeof(entry)); entry.dwSize = sizeof(entry);
    if (Process32FirstW(snapshot, &entry)) do {
        if (!_wcsicmp(entry.szExeFile, process_name)) {
            selected = entry.th32ProcessID; (*matches)++;
        }
    } while (Process32NextW(snapshot, &entry));
    CloseHandle(snapshot);
    return *matches == 1 ? selected : 0;
}

static int pair_compare(const void *left, const void *right) {
    uint64_t a = ((const root_pair *)left)->old_pointer;
    uint64_t b = ((const root_pair *)right)->old_pointer;
    return a < b ? -1 : a > b ? 1 : 0;
}

static uint64_t substitute(root_pair *pairs, uint64_t count, uint64_t value, int *changed) {
    root_pair key = {value, 0};
    root_pair *found = (root_pair *)bsearch(&key, pairs, (size_t)count,
                                            sizeof(*pairs), pair_compare);
    if (!found) { *changed = 0; return value; }
    *changed = found->current_pointer != value;
    return found->current_pointer;
}

int wmain(void) {
    int matches = 0; DWORD pid = unique_process(&matches);
    if (!pid || pid != (DWORD)expected_pid) return 10;
    HANDLE process = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, FALSE, pid);
    if (!process) return 11;
    unsigned char *identity_raw = NULL, *native_raw = NULL, *reference_raw = NULL;
    uint64_t identity_bytes = 0, native_bytes = 0, reference_bytes = 0;
    int ok = read_file(identity_path, &identity_raw, &identity_bytes) &&
             read_file(native_path, &native_raw, &native_bytes) &&
             read_file(reference_path, &reference_raw, &reference_bytes);
    if (!ok) { CloseHandle(process); free(identity_raw); free(native_raw); free(reference_raw); return 12; }
    identity_header *ih = (identity_header *)identity_raw;
    native_header *nh = (native_header *)native_raw;
    reference_header *rh = (reference_header *)reference_raw;
    uint64_t identity_need = sizeof(*ih) + expected_type_count * sizeof(identity_record);
    uint64_t native_need = sizeof(*nh) + expected_type_count * sizeof(native_type);
    uint64_t reference_need = sizeof(*rh) + expected_node_count * sizeof(reference_record);
    if (identity_bytes < identity_need || native_bytes < native_need ||
        reference_bytes < reference_need || memcmp(ih->magic, "ALPHATI1", 8) ||
        memcmp(nh->magic, "ALPHANI1", 8) || memcmp(rh->magic, "ALPHATR1", 8) ||
        ih->type_count != expected_type_count || nh->type_count != expected_type_count ||
        rh->node_count != expected_node_count ||
        memcmp(ih->executable_sha256, executable_sha256, 64) ||
        memcmp(nh->executable_sha256, executable_sha256, 64) ||
        memcmp(rh->executable_sha256, executable_sha256, 64)) {
        CloseHandle(process); free(identity_raw); free(native_raw); free(reference_raw); return 13;
    }
    identity_record *identities = (identity_record *)(identity_raw + sizeof(*ih));
    native_type *types = (native_type *)(native_raw + sizeof(*nh));
    reference_record *references = (reference_record *)(reference_raw + sizeof(*rh));
    root_pair *pairs = (root_pair *)calloc((size_t)expected_type_count, sizeof(*pairs));
    output_record *records = (output_record *)calloc((size_t)expected_node_count, sizeof(*records));
    if (!pairs || !records) { ok = 0; }
    for (uint64_t i = 0; ok && i < expected_type_count; i++) {
        if (identities[i].definition_index != i || types[i].definition_index != i ||
            !identities[i].descriptor || !types[i].class_pointer) { ok = 0; break; }
        pairs[i].old_pointer = identities[i].descriptor;
        pairs[i].current_pointer = types[i].class_pointer + descriptor_offset;
        if (pairs[i].current_pointer < types[i].class_pointer) { ok = 0; break; }
    }
    if (ok) qsort(pairs, (size_t)expected_type_count, sizeof(*pairs), pair_compare);
    uint64_t substitutions = 0, failure_index = UINT64_MAX;
    uint32_t failure_stage = 0;
    for (uint64_t i = 0; ok && i < expected_node_count; i++) {
        int changed = 0; SIZE_T received = 0;
        uint64_t pointer = substitute(pairs, expected_type_count,
                                      references[i].descriptor, &changed);
        records[i].descriptor = references[i].descriptor;
        records[i].current_pointer = pointer;
        if (!pointer || !ReadProcessMemory(process, (const void *)(uintptr_t)pointer,
                &records[i].data, 16, &received) || received != 16) {
            failure_index = i; failure_stage = 1; ok = 0; break;
        }
        uint32_t code = (uint32_t)((records[i].bits >> 16) & 0xffu);
        if (records[i].bits >> 32 || code < 1 || code > 0x1eu) {
            failure_index = i; failure_stage = 2; ok = 0; break;
        }
        substitutions += changed != 0;
    }
    if (ok) {
        FILE *output = _wfopen(output_path, L"wb");
        output_header header; memset(&header, 0, sizeof(header));
        memcpy(header.magic, "ALPHATV1", 8);
        header.version = $output_version;
        header.header_bytes = sizeof(header);
        header.record_bytes = sizeof(output_record);
        header.node_count = expected_node_count;
        header.root_substitution_count = substitutions;
        header.process_id = pid;
        memcpy(header.executable_sha256, executable_sha256, 64);
        memcpy(header.reference_sha256, reference_sha256, 64);
        memcpy(header.native_sha256, native_sha256, 64);
        ok = output && fwrite(&header, 1, sizeof(header), output) == sizeof(header) &&
             fwrite(records, sizeof(*records), (size_t)expected_node_count, output)
                == (size_t)expected_node_count;
        if (output && fclose(output)) ok = 0;
        if (!ok) _wremove(output_path);
    }
    free(pairs); free(records); free(identity_raw); free(native_raw); free(reference_raw);
    CloseHandle(process);
    if (!ok) fwprintf(stderr,
        L"descriptor capture failure stage=%lu index=%llu win32=%lu\n",
        (unsigned long)failure_stage, (unsigned long long)failure_index,
        (unsigned long)GetLastError());
    return ok ? 0 : 14;
}
''')


def _ascii_digest(raw: bytes, *, label: str) -> str:
    try:
        value = raw.decode("ascii")
    except UnicodeDecodeError as error:
        raise AcquisitionError(
            f"runtime type descriptor value {label} digest is invalid"
        ) from error
    if len(value) != 64 or any(
        character not in "0123456789abcdef" for character in value
    ):
        raise AcquisitionError(
            f"runtime type descriptor value {label} digest is invalid"
        )
    return value


def _validate(
    *, output_path: Path, executable_sha256: str,
    reference_sha256: str, native_sha256: str,
    node_count: int, process_id: int,
) -> tuple[dict[str, Any], list[tuple[int, int, int, int]]]:
    raw = _owner_file(output_path, label="inventory").read_bytes()
    if len(raw) < RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.size:
        raise AcquisitionError("runtime type descriptor value output is truncated")
    header = RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.unpack_from(raw)
    expected_size = (
        RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.size
        + node_count * RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size
    )
    checks = {
        "magic": header[0] == RUNTIME_TYPE_DESCRIPTOR_VALUE_MAGIC,
        "version": header[1] == RUNTIME_TYPE_DESCRIPTOR_VALUE_VERSION,
        "header_size": header[2] == RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.size,
        "record_size": header[3] == RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size,
        "reserved_zero": header[4] == 0,
        "node_count_exact": header[5] == node_count,
        "process_id_fresh": header[7] == process_id,
        "executable_bound": _ascii_digest(header[8], label="executable")
        == executable_sha256,
        "reference_bound": _ascii_digest(header[9], label="reference")
        == reference_sha256,
        "native_bound": _ascii_digest(header[10], label="native")
        == native_sha256,
        "size_exact": len(raw) == expected_size,
    }
    records: list[tuple[int, int, int, int]] = []
    descriptors: set[int] = set()
    current_pointers: set[int] = set()
    rows_valid = checks["size_exact"]
    if rows_valid:


        for row in RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.iter_unpack(
            memoryview(raw)[RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.size:]
        ):
            descriptor, current_pointer, data, bits = row
            code = (bits >> 16) & 0xFF
            if (
                not descriptor
                or descriptor & 7
                or descriptor in descriptors
                or not current_pointer
                or current_pointer & 7
                or current_pointer in current_pointers
                or bits >> 32
                or not 1 <= code <= 0x1E
            ):
                rows_valid = False
                break
            descriptors.add(descriptor)
            current_pointers.add(current_pointer)
            records.append(row)
    checks.update(
        {
            "rows_structurally_valid": rows_valid,
            "all_descriptors_unique": rows_valid
            and len(descriptors) == node_count,
            "all_current_pointers_unique": rows_valid
            and len(current_pointers) == node_count,
            "root_substitutions_bounded": 0 <= header[6] <= node_count,
        }
    )
    if not all(checks.values()):
        failed = [key for key, value in checks.items() if not value]
        raise AcquisitionError(
            "runtime type descriptor value validation failed: "
            + ", ".join(failed)
        )
    codes = Counter((row[3] >> 16) & 0xFF for row in records)
    return {
        "node_count": node_count,
        "root_substitution_count": header[6],
        "process_id": header[7],
        "type_code_counts": {
            str(code): codes[code] for code in sorted(codes)
        },
        "checks": checks,
    }, records


def _direct_runtime_inputs(
    *, binary: Path, type_identity_model: Path,
    type_identity_inventory: Path, type_reference_model: Path,
    type_reference_inventory: Path,
) -> tuple[dict[str, Path], str, int, dict[str, Any]]:
    binary = binary.expanduser().resolve()
    if not binary.is_file():
        raise AcquisitionError(
            "runtime type descriptor value binary is unavailable"
        )
    executable_sha256 = sha256_file(binary)
    identity_model_path = _owner_file(
        type_identity_model, label="type identity model"
    )
    identity_path = _owner_file(
        type_identity_inventory, label="type identity inventory"
    )
    reference_model_path = _owner_file(
        type_reference_model, label="type reference model"
    )
    reference_path = _owner_file(
        type_reference_inventory, label="type reference inventory"
    )
    identity_model = read_json(identity_model_path)
    reference_model = read_json(reference_model_path)
    identity_identity = file_identity(identity_path)
    reference_identity = file_identity(reference_path)
    identity_raw = identity_path.read_bytes()
    reference_raw = reference_path.read_bytes()
    if (
        len(identity_raw) < _IDENTITY_HEADER.size
        or len(reference_raw) < RUNTIME_TYPE_REFERENCE_HEADER.size
    ):
        raise AcquisitionError(
            "runtime type descriptor value direct inventory is truncated"
        )
    identity_header = _IDENTITY_HEADER.unpack_from(identity_raw)
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
    type_count = int(identity_header[5])
    if (
        identity_model.get("schema") != RUNTIME_TYPE_IDENTITY_SCHEMA
        or identity_model.get("status") != "runtime-validated"
        or identity_model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or not identity_model.get("checks")
        or not all(identity_model["checks"].values())
        or identity_model.get("identity_inventory") != identity_identity
        or reference_model.get("schema") != RUNTIME_TYPE_REFERENCE_SCHEMA
        or reference_model.get("status") != "runtime-validated"
        or reference_model.get("target", {}).get("executable_sha256")
        != executable_sha256
        or not reference_model.get("checks")
        or not all(reference_model["checks"].values())
        or reference_model.get("inventory") != reference_identity
        or reference_model.get("inputs", {})
        .get("type_identity_inventory", {})
        .get("sha256")
        != identity_identity["sha256"]
        or identity_header[0] != _IDENTITY_MAGIC
        or identity_header[1] != _IDENTITY_VERSION
        or identity_header[2] != _IDENTITY_HEADER.size
        or identity_header[3] != _IDENTITY_RECORD.size
        or not type_count
        or _IDENTITY_HEADER.size + type_count * _IDENTITY_RECORD.size
        > len(identity_raw)
        or reference_header[0] != RUNTIME_TYPE_REFERENCE_MAGIC
        or reference_header[1] != RUNTIME_TYPE_REFERENCE_VERSION
        or reference_header[2] != RUNTIME_TYPE_REFERENCE_HEADER.size
        or reference_header[3] != RUNTIME_TYPE_REFERENCE_RECORD.size
        or reference_header[4] != 0
    ):
        raise AcquisitionError(
            "runtime type descriptor value direct binding is stale"
        )
    return (
        {
            "binary": binary,
            "type_identity_inventory": identity_path,
            "type_reference_inventory": reference_path,
        },
        executable_sha256,
        type_count,
        {
            "type_identity_model": file_identity(identity_model_path),
            "type_identity_inventory": identity_identity,
            "type_reference_model": file_identity(reference_model_path),
            "type_reference_inventory": reference_identity,
        },
    )


def capture_runtime_type_descriptor_values(
    *, native_output_receipt: Path | None = None,
    binary: Path | None = None, type_identity_model: Path | None = None,
    type_identity_inventory: Path | None = None,
    type_reference_model: Path | None = None,
    type_reference_inventory: Path | None = None,
    live_materializer_model: Path, output_dir: Path,
    compiler: Path | None = None, wine: Path, wineprefix: Path,
    timeout: float = 180.0,
) -> dict[str, Any]:
    started = time.monotonic()
    direct = (
        binary,
        type_identity_model,
        type_identity_inventory,
        type_reference_model,
        type_reference_inventory,
    )
    if native_output_receipt is not None:
        if any(value is not None for value in direct):
            raise AcquisitionError(
                "runtime type descriptor value inputs are ambiguous"
            )
        receipt, paths, runtime = _runtime(native_output_receipt)
        executable_sha256 = receipt["target"]["executable_sha256"]
        type_count = runtime.type_count
        input_binding = {
            "native_output_receipt": file_identity(
                native_output_receipt.expanduser().resolve()
            )
        }
    else:
        if any(value is None for value in direct):
            raise AcquisitionError(
                "runtime type descriptor value direct inputs are incomplete"
            )
        paths, executable_sha256, type_count, input_binding = (
            _direct_runtime_inputs(
                binary=binary,
                type_identity_model=type_identity_model,
                type_identity_inventory=type_identity_inventory,
                type_reference_model=type_reference_model,
                type_reference_inventory=type_reference_inventory,
            )
        )
    live_model_path = _owner_file(
        live_materializer_model, label="live materializer model"
    )
    output_dir = _owner_directory(output_dir)
    output_path = output_dir / "runtime-type-descriptor-values.private.bin"
    model_path = output_dir / "runtime-type-descriptor-values.private.json"
    build_dir = _owner_directory(output_dir / "build-type-descriptor-values")
    source_path = build_dir / "runtime-type-descriptor-values.c"
    executable_path = build_dir / "alpha-runtime-type-descriptor-values.exe"

    reference_path = paths["type_reference_inventory"]
    identity_path = paths["type_identity_inventory"]
    reference_raw = reference_path.read_bytes()
    reference_header = RUNTIME_TYPE_REFERENCE_HEADER.unpack_from(reference_raw)
    node_count = int(reference_header[5])
    if (
        RUNTIME_TYPE_REFERENCE_HEADER.size
        + node_count * RUNTIME_TYPE_REFERENCE_RECORD.size
        > len(reference_raw)
    ):
        raise AcquisitionError("runtime type reference input is truncated")

    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise AcquisitionError("runtime type descriptor value Wine is unavailable")

    with LiveRuntimeInventory(
        materializer_model=live_model_path, binary=paths["binary"]
    ) as live:
        if live.type_count != type_count:
            raise AcquisitionError(
                "runtime type descriptor value live type count differs"
            )
        native_path = live.native_path
        native_identity = file_identity(native_path)
        process_id = live.process_id
        descriptor_offset = live.embedded_descriptor_byte_offset

    source = _COLLECTOR.substitute(
        identity_header_bytes=_IDENTITY_HEADER.size,
        identity_record_bytes=_IDENTITY_RECORD.size,
        native_header_bytes=struct.calcsize("<8sIIIIQQQ64s64sIIIIIIII"),
        native_type_bytes=struct.calcsize("<IIQQQQQIIQQ"),
        reference_header_bytes=RUNTIME_TYPE_REFERENCE_HEADER.size,
        reference_record_bytes=RUNTIME_TYPE_REFERENCE_RECORD.size,
        output_header_bytes=RUNTIME_TYPE_DESCRIPTOR_VALUE_HEADER.size,
        output_record_bytes=RUNTIME_TYPE_DESCRIPTOR_VALUE_RECORD.size,
        process_name=_wide_literal(paths["binary"].name),
        identity_path=_wide_literal(_windows_z_path(identity_path)),
        native_path=_wide_literal(_windows_z_path(native_path)),
        reference_path=_wide_literal(_windows_z_path(reference_path)),
        output_path=_wide_literal(_windows_z_path(output_path)),
        process_id=process_id,
        type_count=type_count,
        node_count=node_count,
        descriptor_offset=descriptor_offset,
        executable_sha256=executable_sha256,
        reference_sha256=sha256_file(reference_path),
        native_sha256=native_identity["sha256"],
        output_version=RUNTIME_TYPE_DESCRIPTOR_VALUE_VERSION,
    )
    _private_text(source_path, source)
    compiler_path = _compiler(compiler)
    cached_windows_build(
        [
            str(compiler_path), "-std=c11", "-O2", "-Wall", "-Wextra",
            "-municode", str(source_path), "-o", str(executable_path),
        ],
        label="runtime type descriptor value collector",
        source_path=source_path,
        output_path=executable_path,
    )
    executable_path.chmod(0o700)
    output_path.unlink(missing_ok=True)
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    try:
        result = subprocess.run(
            _host_run(str(wine), executable_path),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=timeout,
            env=environment,
            check=False,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(
            "runtime type descriptor value collector could not run"
        ) from error
    if result.returncode:
        raise AcquisitionError(
            "runtime type descriptor value collector failed "
            f"({result.returncode}): {result.stderr[-2000:]}"
        )
    _seal_runtime_output(output_path)
    model, _records = _validate(
        output_path=output_path,
        executable_sha256=executable_sha256,
        reference_sha256=sha256_file(reference_path),
        native_sha256=native_identity["sha256"],
        node_count=node_count,
        process_id=process_id,
    )
    payload = {
        "schema": RUNTIME_TYPE_DESCRIPTOR_VALUE_SCHEMA,
        "status": "runtime-validated",
        "target": {
            "executable_sha256": executable_sha256,
            "process_id": process_id,
        },
        "inputs": {
            **input_binding,
            "live_materializer_model": file_identity(live_model_path),
            "type_reference_inventory": file_identity(reference_path),
            "type_identity_inventory": file_identity(identity_path),
            "fresh_native_inventory": native_identity,
        },
        "counts": {
            "node_count": model["node_count"],
            "root_substitution_count": model["root_substitution_count"],
            "type_code_counts": model["type_code_counts"],
        },
        "inventory": file_identity(output_path),
        "checks": {
            **model["checks"],
            "fresh_runtime_observation": True,
            "fixed_address_used": False,
            "fixed_rva_used": False,
            "descriptor_used_only_as_current_process_lookup_key": True,
            "all_descriptor_values_read_from_current_process": True,
        },
        "policy": {
            "fail_closed_on_any_unreadable_descriptor": True,
            "root_addresses_rebound_from_fresh_materializer": True,
            "raw_runtime_pointers_owner_only": True,
        },
    }
    _private_json(model_path, payload)
    return {
        "schema": payload["schema"],
        "status": payload["status"],
        "target": payload["target"],
        "counts": payload["counts"],
        "checks": payload["checks"],
        "model": file_identity(model_path),
        "inventory": payload["inventory"],
        "elapsed_seconds": time.monotonic() - started,
    }


def load_runtime_type_descriptor_values(
    *, model_path: Path, inventory_path: Path,
    expected_executable_sha256: str | None = None,
) -> dict[str, Any]:
    model_path = _owner_file(model_path, label="model")
    inventory_path = _owner_file(inventory_path, label="inventory")
    model = json.loads(model_path.read_text(encoding="utf-8"))
    target_sha256 = model.get("target", {}).get("executable_sha256")
    reference_sha256 = model.get("inputs", {}).get(
        "type_reference_inventory", {}
    ).get("sha256")
    native_sha256 = model.get("inputs", {}).get(
        "fresh_native_inventory", {}
    ).get("sha256")
    node_count = model.get("counts", {}).get("node_count")
    process_id = model.get("target", {}).get("process_id")
    if (
        model.get("schema") != RUNTIME_TYPE_DESCRIPTOR_VALUE_SCHEMA
        or model.get("status") != "runtime-validated"
        or model.get("inventory") != file_identity(inventory_path)
        or not isinstance(node_count, int)
        or not isinstance(process_id, int)
        or not isinstance(reference_sha256, str)
        or not isinstance(native_sha256, str)
        or expected_executable_sha256 is not None
        and target_sha256 != expected_executable_sha256.lower()
    ):
        raise AcquisitionError("runtime type descriptor value binding is stale")
    current, records = _validate(
        output_path=inventory_path,
        executable_sha256=target_sha256,
        reference_sha256=reference_sha256,
        native_sha256=native_sha256,
        node_count=node_count,
        process_id=process_id,
    )
    model_checks = model.get("checks", {})
    negative_checks = {"fixed_address_used", "fixed_rva_used"}
    checks_complete = (
        isinstance(model_checks, dict)
        and model_checks
        and all(
            value is (False if key in negative_checks else True)
            for key, value in model_checks.items()
        )
        and negative_checks <= set(model_checks)
    )
    if (
        current["root_substitution_count"]
        != model.get("counts", {}).get("root_substitution_count")
        or current["type_code_counts"]
        != model.get("counts", {}).get("type_code_counts")
        or not checks_complete
    ):
        raise AcquisitionError(
            "runtime type descriptor value validation is stale"
        )
    return {
        "schema": model["schema"],
        "status": "complete",
        "target": model["target"],
        "counts": model["counts"],
        "records": records,
        "identity": file_identity(inventory_path),
        "inputs": model["inputs"],
    }
