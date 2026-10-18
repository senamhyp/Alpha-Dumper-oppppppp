from alpha.h02 import windows_run as _host_run

import json
import hashlib
import os
import shutil
import stat
import struct
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any, Callable

from alpha.h01 import AcquisitionError, DependencyUnavailable, owner_uid, owner_only_mode_ok, set_private_descriptor_mode
from alpha.h03 import CollectionContext, collect_target
from alpha.p01 import reflection_contract
from alpha.c01 import RUNTIME_DISPATCH_ENTRY, RUNTIME_DISPATCH_HEADER, RUNTIME_DISPATCH_MAGIC, RUNTIME_DISPATCH_VERSION, load_runtime_dispatch_manifest
from alpha.p02 import runtime_inventory_contract
from alpha.c01 import load_runtime_owner_roots
from alpha.c02 import RUNTIME_INVENTORY_DISPATCH_ENTRY, RUNTIME_INVENTORY_DISPATCH_HEADER, RUNTIME_INVENTORY_DISPATCH_MAGIC, RUNTIME_INVENTORY_DISPATCH_VERSION, load_runtime_inventory_dispatch_manifest
from alpha.p03 import RUNTIME_INVENTORY_OBSERVATION_ENTRY, RUNTIME_INVENTORY_OBSERVATION_HEADER, RUNTIME_INVENTORY_OBSERVATION_MAGIC, RUNTIME_INVENTORY_OBSERVATION_VERSION, load_runtime_inventory_observation
from alpha.c03 import RUNTIME_MEMBER_OBSERVATION_ENTRY, RUNTIME_MEMBER_OBSERVATION_HEADER, RUNTIME_MEMBER_OBSERVATION_MAGIC, RUNTIME_MEMBER_OBSERVATION_VERSION, load_runtime_member_observation
from alpha.p04 import METHOD_DETAIL_CONSTRUCTOR, METHOD_DETAIL_GENERIC, METHOD_DETAIL_GENERIC_DEFINITION, PARAMETER_DETAIL_IN, PARAMETER_DETAIL_OPTIONAL, PARAMETER_DETAIL_OUT, RUNTIME_MEMBER_DETAIL_EVENT, RUNTIME_MEMBER_DETAIL_FIELD, RUNTIME_MEMBER_DETAIL_HEADER, RUNTIME_MEMBER_DETAIL_MAGIC, RUNTIME_MEMBER_DETAIL_METHOD, RUNTIME_MEMBER_DETAIL_PARAMETER, RUNTIME_MEMBER_DETAIL_PROPERTY, RUNTIME_MEMBER_DETAIL_TYPE, RUNTIME_MEMBER_DETAIL_VERSION, load_runtime_member_detail_observation
from alpha.c03 import RUNTIME_TYPE_IDENTITY_ASSEMBLY, RUNTIME_TYPE_IDENTITY_ENTRY, RUNTIME_TYPE_IDENTITY_HEADER, RUNTIME_TYPE_IDENTITY_MAGIC, RUNTIME_TYPE_IDENTITY_VERSION, TYPE_SHAPE_BYREF, TYPE_SHAPE_ENUM, TYPE_SHAPE_GENERIC, TYPE_SHAPE_GENERIC_DEFINITION, TYPE_SHAPE_INTERFACE, TYPE_SHAPE_VALUE_TYPE, load_runtime_type_identity_observation
from alpha.p06 import NO_GENERIC_PARAMETER_POSITION, RUNTIME_TYPE_GRAPH_ENTRY, RUNTIME_TYPE_GRAPH_HEADER, RUNTIME_TYPE_GRAPH_MAGIC, RUNTIME_TYPE_GRAPH_VERSION, TYPE_SHAPE_GENERIC_PARAMETER, TYPE_SHAPE_ARRAY, TYPE_SHAPE_POINTER, load_runtime_type_graph_observation
from alpha.p08 import RUNTIME_METHOD_NATIVE_ENTRY, RUNTIME_METHOD_NATIVE_HEADER, RUNTIME_METHOD_NATIVE_MAGIC, RUNTIME_METHOD_NATIVE_VERSION, load_runtime_method_native_observation
from alpha.p09 import RUNTIME_FIELD_NATIVE_ENTRY, RUNTIME_FIELD_NATIVE_HEADER, RUNTIME_FIELD_NATIVE_MAGIC, RUNTIME_FIELD_NATIVE_VERSION, load_runtime_field_native_observation
from alpha.p10 import RUNTIME_METADATA_USAGE_ENTRY, RUNTIME_METADATA_USAGE_HEADER, RUNTIME_METADATA_USAGE_MAGIC, RUNTIME_METADATA_USAGE_VERSION, load_runtime_metadata_usage_observation
from alpha.p07 import RUNTIME_TYPE_NATIVE_ENTRY, RUNTIME_TYPE_NATIVE_HEADER, RUNTIME_TYPE_NATIVE_MAGIC, RUNTIME_TYPE_NATIVE_VERSION, load_runtime_type_native_observation
from alpha.p11 import RUNTIME_TYPE_METADATA_USAGE_ENTRY, RUNTIME_TYPE_METADATA_USAGE_HEADER, RUNTIME_TYPE_METADATA_USAGE_MAGIC, RUNTIME_TYPE_METADATA_USAGE_VERSION, load_runtime_type_metadata_usage_observation
from alpha.h02 import atomic_write_json, file_identity, sha256_file


RUNTIME_SCHEMA = "alpha.runtime-metadata-capture/v1"
PLAN_SCHEMA = "alpha.runtime-dump-plan/v1"
SNAPSHOT_SCHEMA = "alpha.runtime-memory-capture/v5"
SNAPSHOT_PLAN_SCHEMA = "alpha.runtime-memory-plan/v5"
SNAPSHOT_MAGIC = b"ALPHAMS5"
SNAPSHOT_VERSION = 5
SNAPSHOT_LEGACY_IDENTITIES = {
    (b"ALPHAMS1", 1),
    (b"ALPHAMS2", 2),
    (b"ALPHAMS3", 3),
    (b"ALPHAMS4", 4),
}
SNAPSHOT_HEADER = struct.Struct("<8sIIQQQQQ3Q")
SNAPSHOT_RECORD = struct.Struct("<QQIIII")
RUNTIME_NAME_OPERATION_KEYS = (
    "method.name",
    "field.name",
    "property.name",
    "parameter.name",
)
RUNTIME_DIRECT_OBJECT_OPERATION_KEYS = ("parameter.type",)
RUNTIME_PARAMETER_FLAG_OPERATION_KEYS = (
    "parameter.is_in",
    "parameter.is_out",
    "parameter.is_optional",
)
RUNTIME_SENTINEL_FIELD_OPERATION_KEYS = ("parameter.default_value",)
RUNTIME_DIRECT_DWORD_OPERATION_KEYS = ("field.attributes",)
RUNTIME_PROPERTY_ACCESSOR_OPERATION_KEYS = (
    "property.getter",
    "property.setter",
)
RUNTIME_SEMANTIC_OPERATION_KEYS = (
    *RUNTIME_NAME_OPERATION_KEYS,
    *RUNTIME_DIRECT_OBJECT_OPERATION_KEYS,
    *RUNTIME_PARAMETER_FLAG_OPERATION_KEYS,
    *RUNTIME_SENTINEL_FIELD_OPERATION_KEYS,
    *RUNTIME_DIRECT_DWORD_OPERATION_KEYS,
    *RUNTIME_PROPERTY_ACCESSOR_OPERATION_KEYS,
)


def _owner_directory(path: Path) -> Path:
    path = path.expanduser().resolve()
    if path.exists() and (path.is_symlink() or not path.is_dir()):
        raise AcquisitionError(f"private dump directory boundary rejected: {path}")
    path.mkdir(parents=True, exist_ok=True, mode=0o700)
    path.chmod(0o700)
    directory_status = path.stat()
    if (
        False
        or not owner_only_mode_ok(directory_status, 0o700)
    ):
        raise AcquisitionError(f"private dump directory is not owner-only: {path}")
    descriptor, probe_name = tempfile.mkstemp(prefix=".alpha-owner-probe.", dir=path)
    probe = Path(probe_name)
    try:
        set_private_descriptor_mode(descriptor, 0o600)
        probe_status = os.fstat(descriptor)
        if (
            False
            or not owner_only_mode_ok(probe_status, 0o600)
        ):
            raise AcquisitionError(
                f"private dump filesystem cannot enforce owner-only files: {path}"
            )
    finally:
        os.close(descriptor)
        probe.unlink(missing_ok=True)
    return path


def _seal_runtime_output(path: Path) -> bool:

    if not path.exists():
        return False
    if path.is_symlink() or not path.is_file():
        raise AcquisitionError(f"runtime output boundary rejected: {path}")
    path.chmod(0o600)
    status = path.stat()
    if False or not owner_only_mode_ok(status, 0o600):
        raise AcquisitionError(f"runtime output is not owner-only: {path}")
    return True


def _assert_owner_file(path: Path) -> None:
    status = path.stat()
    if False or not owner_only_mode_ok(status, 0o600):
        raise AcquisitionError(f"private artifact is not owner-only: {path}")


def _private_text(path: Path, value: str) -> None:
    path = path.expanduser().resolve()
    _owner_directory(path.parent)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary_path = Path(temporary)
    try:
        set_private_descriptor_mode(descriptor, 0o600)
        with os.fdopen(descriptor, "w", encoding="utf-8") as sink:
            sink.write(value)
            sink.flush()
            os.fsync(sink.fileno())
        os.replace(temporary_path, path)
        path.chmod(0o600)
        _assert_owner_file(path)
    finally:
        temporary_path.unlink(missing_ok=True)


def _private_bytes(path: Path, value: bytes) -> None:
    path = path.expanduser().resolve()
    _owner_directory(path.parent)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary_path = Path(temporary)
    try:
        set_private_descriptor_mode(descriptor, 0o600)
        with os.fdopen(descriptor, "wb") as sink:
            sink.write(value)
            sink.flush()
            os.fsync(sink.fileno())
        os.replace(temporary_path, path)
        path.chmod(0o600)
        _assert_owner_file(path)
    finally:
        temporary_path.unlink(missing_ok=True)


def _private_json(path: Path, value: dict[str, Any]) -> None:
    path = path.expanduser().resolve()
    _owner_directory(path.parent)
    atomic_write_json(path, value)
    path.chmod(0o600)
    _assert_owner_file(path)


def _windows_z_path(path: Path) -> str:
    path = path.expanduser().resolve()
    if not path.is_absolute():
        raise AcquisitionError("runtime artifact path must be absolute")
    if os.name == "nt":
        return str(path)
    return "Z:" + str(path).replace("/", "\\")


def _wide_literal(value: str) -> str:
    escaped = value.replace("\\", "\\\\").replace('"', '\\"')
    return f'L"{escaped}"'


def _reflection_owner_table_source(
    expected_cached_owners: tuple[tuple[str, str], ...],
) -> tuple[str, int]:
    minimum_counts: dict[tuple[str, str], int] = {}
    layout_participants: set[tuple[str, str]] = set()
    for operation in reflection_contract()["operations"]:
        namespace, type_name = operation["runtime_owner"].rsplit(".", 1)
        pair = (namespace, type_name)
        minimum_counts[pair] = minimum_counts.get(pair, 0) + 1
        layout_participants.add(pair)
    for operation in runtime_inventory_contract()["operations"]:
        for runtime_owner in operation["runtime_owners"]:
            namespace, type_name = runtime_owner.rsplit(".", 1)
            pair = (namespace, type_name)
            minimum_counts[pair] = minimum_counts.get(pair, 0) + 1
            if operation["stage"] != "execution":
                layout_participants.add(pair)
    for runtime_owner in runtime_inventory_contract()[
        "additional_required_runtime_owners"
    ]:
        namespace, type_name = runtime_owner.rsplit(".", 1)
        pair = (namespace, type_name)
        minimum_counts.setdefault(pair, 0)
        layout_participants.add(pair)
    expected = set(expected_cached_owners)
    if len(expected) != len(expected_cached_owners) or not expected.issubset(
        minimum_counts
    ):
        raise AcquisitionError(
            "runtime collector cached reflection owner contract is invalid"
        )
    rows = [
        f'    {{"{namespace}", "{type_name}", {minimum_counts[(namespace, type_name)]}u, '
        f'{1 if (namespace, type_name) in expected else 0}, '
        f'{1 if (namespace, type_name) in layout_participants else 0}}}'
        for namespace, type_name in sorted(minimum_counts)
    ]
    return ",\n".join(rows), len(expected)


def _reflection_operation_table_source() -> tuple[str, int]:
    operations = reflection_contract()["operations"]
    rows = []
    for operation in operations:
        namespace, type_name = operation["runtime_owner"].rsplit(".", 1)
        rows.append(
            "    {"
            f'"{operation["key"]}", '
            f'"{namespace}", '
            f'"{type_name}", '
            f'"{operation["runtime_name"]}", '
            f'{operation["parameter_count"]}u'
            "}"
        )
    return ",\n".join(rows), len(rows)


def _inventory_operation_table_source() -> tuple[str, int, int]:
    operations = runtime_inventory_contract()["operations"]
    rows: list[str] = []
    for operation_index, operation in enumerate(operations):
        for runtime_owner in operation["runtime_owners"]:
            namespace, type_name = runtime_owner.rsplit(".", 1)
            rows.append(
                "    {"
                f'{operation_index}u, '
                f'"{operation["key"]}", '
                f'"{namespace}", '
                f'"{type_name}", '
                f'"{operation["runtime_name"]}", '
                f'{operation["parameter_count"]}u'
                "}"
            )
    return ",\n".join(rows), len(operations), len(rows)


def _required_runtime_owner_pairs() -> tuple[tuple[str, str], ...]:
    owners: set[tuple[str, str]] = set()
    for operation in reflection_contract()["operations"]:
        owners.add(tuple(operation["runtime_owner"].rsplit(".", 1)))
    inventory = runtime_inventory_contract()
    for operation in inventory["operations"]:
        owners.update(
            tuple(owner.rsplit(".", 1)) for owner in operation["runtime_owners"]
        )
    owners.update(
        tuple(owner.rsplit(".", 1))
        for owner in inventory["additional_required_runtime_owners"]
    )
    return tuple(sorted(owners))


def runtime_collector_source(
    *,
    expected_executable_sha256: str,
    metadata_path: Path,
    status_path: Path,
    reflection_dispatch_path: Path,
    inventory_dispatch_path: Path | None = None,
    inventory_observation_path: Path | None = None,
    member_observation_path: Path | None = None,
    type_identity_observation_path: Path | None = None,
    member_detail_observation_path: Path | None = None,
    type_graph_observation_path: Path | None = None,
    method_native_observation_path: Path | None = None,
    field_native_observation_path: Path | None = None,
    metadata_usage_observation_path: Path | None = None,
    type_native_observation_path: Path | None = None,
    type_metadata_usage_observation_path: Path | None = None,
    expected_reflection_type_cache_count: int = 0,
    expected_reflection_state_slot_rva: int = 0,
    expected_reflection_cached_owners: tuple[tuple[str, str], ...] = (),
) -> str:
    if len(expected_executable_sha256) != 64:
        raise AcquisitionError("runtime collector requires an exact executable SHA-256")
    if expected_reflection_type_cache_count < 0:
        raise AcquisitionError("runtime collector reflection cache count is invalid")
    if expected_reflection_state_slot_rva < 0:
        raise AcquisitionError("runtime collector reflection state slot is invalid")
    reflection_owner_table, expected_reflection_owner_count = (
        _reflection_owner_table_source(expected_reflection_cached_owners)
    )
    reflection_operation_table, reflection_operation_count = (
        _reflection_operation_table_source()
    )
    (
        inventory_operation_table,
        inventory_operation_count,
        inventory_operation_candidate_count,
    ) = _inventory_operation_table_source()
    reflection = reflection_contract()
    reflection_contract_sha256 = reflection["contract_id"].rsplit(":", 1)[-1]
    inventory = runtime_inventory_contract()
    inventory_contract_sha256 = inventory["contract_id"].rsplit(":", 1)[-1]
    declared_member_binding_flags = inventory[
        "declared_member_binding_flags"
    ]["value"]
    metadata_literal = _wide_literal(_windows_z_path(metadata_path))
    status_literal = _wide_literal(_windows_z_path(status_path))
    reflection_dispatch_literal = _wide_literal(
        _windows_z_path(reflection_dispatch_path)
    )
    if inventory_dispatch_path is None:
        inventory_dispatch_path = reflection_dispatch_path.with_name(
            "runtime-inventory-dispatch.private.bin"
        )
    inventory_dispatch_literal = _wide_literal(
        _windows_z_path(inventory_dispatch_path)
    )
    if inventory_observation_path is None:
        inventory_observation_path = reflection_dispatch_path.with_name(
            "runtime-inventory-observation.private.bin"
        )
    inventory_observation_literal = _wide_literal(
        _windows_z_path(inventory_observation_path)
    )
    if member_observation_path is None:
        member_observation_path = reflection_dispatch_path.with_name(
            "runtime-member-observation.private.bin"
        )
    member_observation_literal = _wide_literal(
        _windows_z_path(member_observation_path)
    )
    if type_identity_observation_path is None:
        type_identity_observation_path = reflection_dispatch_path.with_name(
            "runtime-type-identity-observation.private.bin"
        )
    type_identity_observation_literal = _wide_literal(
        _windows_z_path(type_identity_observation_path)
    )
    if member_detail_observation_path is None:
        member_detail_observation_path = reflection_dispatch_path.with_name(
            "runtime-member-detail-observation.private.bin"
        )
    member_detail_observation_literal = _wide_literal(
        _windows_z_path(member_detail_observation_path)
    )
    if type_graph_observation_path is None:
        type_graph_observation_path = reflection_dispatch_path.with_name(
            "runtime-type-graph-observation.private.bin"
        )
    type_graph_observation_literal = _wide_literal(
        _windows_z_path(type_graph_observation_path)
    )
    if method_native_observation_path is None:
        method_native_observation_path = reflection_dispatch_path.with_name(
            "runtime-method-native-observation.private.bin"
        )
    method_native_observation_literal = _wide_literal(
        _windows_z_path(method_native_observation_path)
    )
    if field_native_observation_path is None:
        field_native_observation_path = reflection_dispatch_path.with_name(
            "runtime-field-native-observation.private.bin"
        )
    field_native_observation_literal = _wide_literal(
        _windows_z_path(field_native_observation_path)
    )
    if metadata_usage_observation_path is None:
        metadata_usage_observation_path = reflection_dispatch_path.with_name(
            "runtime-metadata-usage-observation.private.bin"
        )
    metadata_usage_observation_literal = _wide_literal(
        _windows_z_path(metadata_usage_observation_path)
    )
    if type_native_observation_path is None:
        type_native_observation_path = reflection_dispatch_path.with_name(
            "runtime-type-native-observation.private.bin"
        )
    type_native_observation_literal = _wide_literal(
        _windows_z_path(type_native_observation_path)
    )
    if type_metadata_usage_observation_path is None:
        type_metadata_usage_observation_path = reflection_dispatch_path.with_name(
            "runtime-type-metadata-usage-observation.private.bin"
        )
    type_metadata_usage_observation_literal = _wide_literal(
        _windows_z_path(type_metadata_usage_observation_path)
    )
    return rf'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

#define ALPHA_SCAN_CHUNK (1024u * 1024u)
#define ALPHA_MAX_HEADER 0x4000u
#define ALPHA_MAX_METADATA (1024ull * 1024ull * 1024ull)
#define ALPHA_MAX_CANDIDATES 128
#define ALPHA_MAX_RESOLVER_ANCHORS 8192
#define ALPHA_MAX_REFLECTION_OWNERS 32
#define ALPHA_MAX_REFLECTION_METHODS 8192
#define ALPHA_NAME_OPERATION_COUNT 4
#define ALPHA_PARAMETER_FLAG_OPERATION_COUNT 3
#define ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT 2
#define ALPHA_REFLECTION_OPERATION_COUNT {reflection_operation_count}
#define ALPHA_INVENTORY_OPERATION_COUNT {inventory_operation_count}
#define ALPHA_INVENTORY_OPERATION_CANDIDATE_COUNT {inventory_operation_candidate_count}
#define ALPHA_METHOD_PARAMETER_SCAN_BYTES 256
#define ALPHA_MAX_METHOD_PARAMETER_COUNT 64
#define ALPHA_DISPATCH_HEADER_BYTES {RUNTIME_DISPATCH_HEADER.size}u
#define ALPHA_DISPATCH_ENTRY_BYTES {RUNTIME_DISPATCH_ENTRY.size}u
#define ALPHA_INVENTORY_DISPATCH_HEADER_BYTES {RUNTIME_INVENTORY_DISPATCH_HEADER.size}u
#define ALPHA_INVENTORY_DISPATCH_ENTRY_BYTES {RUNTIME_INVENTORY_DISPATCH_ENTRY.size}u
#define ALPHA_INVENTORY_OBSERVATION_HEADER_BYTES {RUNTIME_INVENTORY_OBSERVATION_HEADER.size}u
#define ALPHA_INVENTORY_OBSERVATION_ENTRY_BYTES {RUNTIME_INVENTORY_OBSERVATION_ENTRY.size}u
#define ALPHA_MAX_ASSEMBLY_COUNT 4096u
#define ALPHA_MAX_TYPE_COUNT 2000000u
#define ALPHA_MEMBER_OBSERVATION_HEADER_BYTES {RUNTIME_MEMBER_OBSERVATION_HEADER.size}u
#define ALPHA_MEMBER_OBSERVATION_ENTRY_BYTES {RUNTIME_MEMBER_OBSERVATION_ENTRY.size}u
#define ALPHA_DECLARED_MEMBER_BINDING_FLAGS {declared_member_binding_flags}u
#define ALPHA_MEMBER_CATEGORY_COUNT 6u
#define ALPHA_MAX_MEMBER_OBJECT_COUNT 8000000ull
#define ALPHA_TYPE_IDENTITY_HEADER_BYTES {RUNTIME_TYPE_IDENTITY_HEADER.size}u
#define ALPHA_TYPE_IDENTITY_ASSEMBLY_BYTES {RUNTIME_TYPE_IDENTITY_ASSEMBLY.size}u
#define ALPHA_TYPE_IDENTITY_ENTRY_BYTES {RUNTIME_TYPE_IDENTITY_ENTRY.size}u
#define ALPHA_MEMBER_DETAIL_HEADER_BYTES {RUNTIME_MEMBER_DETAIL_HEADER.size}u
#define ALPHA_MEMBER_DETAIL_TYPE_BYTES {RUNTIME_MEMBER_DETAIL_TYPE.size}u
#define ALPHA_MEMBER_DETAIL_FIELD_BYTES {RUNTIME_MEMBER_DETAIL_FIELD.size}u
#define ALPHA_MEMBER_DETAIL_METHOD_BYTES {RUNTIME_MEMBER_DETAIL_METHOD.size}u
#define ALPHA_MEMBER_DETAIL_PARAMETER_BYTES {RUNTIME_MEMBER_DETAIL_PARAMETER.size}u
#define ALPHA_MEMBER_DETAIL_PROPERTY_BYTES {RUNTIME_MEMBER_DETAIL_PROPERTY.size}u
#define ALPHA_MEMBER_DETAIL_EVENT_BYTES {RUNTIME_MEMBER_DETAIL_EVENT.size}u
#define ALPHA_TYPE_GRAPH_HEADER_BYTES {RUNTIME_TYPE_GRAPH_HEADER.size}u
#define ALPHA_TYPE_GRAPH_ENTRY_BYTES {RUNTIME_TYPE_GRAPH_ENTRY.size}u
#define ALPHA_METHOD_NATIVE_HEADER_BYTES {RUNTIME_METHOD_NATIVE_HEADER.size}u
#define ALPHA_METHOD_NATIVE_ENTRY_BYTES {RUNTIME_METHOD_NATIVE_ENTRY.size}u
#define ALPHA_METHOD_METADATA_OBJECT_SCAN_QWORDS 32u
#define ALPHA_METHOD_METADATA_SAMPLE_BYTES 256u
#define ALPHA_METHOD_ATTRIBUTE_VIRTUAL 0x40u
#define ALPHA_FIELD_NATIVE_HEADER_BYTES {RUNTIME_FIELD_NATIVE_HEADER.size}u
#define ALPHA_FIELD_NATIVE_ENTRY_BYTES {RUNTIME_FIELD_NATIVE_ENTRY.size}u
#define ALPHA_FIELD_METADATA_OBJECT_SCAN_QWORDS 32u
#define ALPHA_FIELD_METADATA_SAMPLE_BYTES 256u
#define ALPHA_METADATA_USAGE_HEADER_BYTES {RUNTIME_METADATA_USAGE_HEADER.size}u
#define ALPHA_METADATA_USAGE_ENTRY_BYTES {RUNTIME_METADATA_USAGE_ENTRY.size}u
#define ALPHA_TYPE_NATIVE_HEADER_BYTES {RUNTIME_TYPE_NATIVE_HEADER.size}u
#define ALPHA_TYPE_NATIVE_ENTRY_BYTES {RUNTIME_TYPE_NATIVE_ENTRY.size}u
#define ALPHA_TYPE_METADATA_USAGE_HEADER_BYTES {RUNTIME_TYPE_METADATA_USAGE_HEADER.size}u
#define ALPHA_TYPE_METADATA_USAGE_ENTRY_BYTES {RUNTIME_TYPE_METADATA_USAGE_ENTRY.size}u
#define ALPHA_MAX_DEFINITION_STRIDE 256u
#define ALPHA_MAX_METADATA_TABLE_PAIRS ((ALPHA_MAX_HEADER - 8u) / 8u)
#define ALPHA_TYPE_SHAPE_GENERIC_PARAMETER {TYPE_SHAPE_GENERIC_PARAMETER}u
#define ALPHA_TYPE_SHAPE_ARRAY {TYPE_SHAPE_ARRAY}u
#define ALPHA_TYPE_SHAPE_POINTER {TYPE_SHAPE_POINTER}u
#define ALPHA_NO_GENERIC_PARAMETER_POSITION {NO_GENERIC_PARAMETER_POSITION}u
#define ALPHA_MAX_TYPE_GRAPH_NODES 2000000ull
#define ALPHA_METHOD_DETAIL_CONSTRUCTOR {METHOD_DETAIL_CONSTRUCTOR}u
#define ALPHA_METHOD_DETAIL_GENERIC {METHOD_DETAIL_GENERIC}u
#define ALPHA_METHOD_DETAIL_GENERIC_DEFINITION {METHOD_DETAIL_GENERIC_DEFINITION}u
#define ALPHA_PARAMETER_DETAIL_IN {PARAMETER_DETAIL_IN}u
#define ALPHA_PARAMETER_DETAIL_OUT {PARAMETER_DETAIL_OUT}u
#define ALPHA_PARAMETER_DETAIL_OPTIONAL {PARAMETER_DETAIL_OPTIONAL}u
#define ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES (512ull * 1024ull * 1024ull)
#define ALPHA_TYPE_SHAPE_ENUM {TYPE_SHAPE_ENUM}u
#define ALPHA_TYPE_SHAPE_VALUE_TYPE {TYPE_SHAPE_VALUE_TYPE}u
#define ALPHA_TYPE_SHAPE_GENERIC {TYPE_SHAPE_GENERIC}u
#define ALPHA_TYPE_SHAPE_GENERIC_DEFINITION {TYPE_SHAPE_GENERIC_DEFINITION}u
#define ALPHA_TYPE_SHAPE_BYREF {TYPE_SHAPE_BYREF}u
#define ALPHA_TYPE_SHAPE_INTERFACE {TYPE_SHAPE_INTERFACE}u
#define ALPHA_TYPE_ATTRIBUTE_INTERFACE 0x20u

static const char expected_executable_sha256[] = "{expected_executable_sha256.lower()}";
static const char expected_reflection_contract_sha256[] = "{reflection_contract_sha256}";
static const char expected_inventory_contract_sha256[] = "{inventory_contract_sha256}";
static const uint64_t expected_reflection_type_cache_count = {expected_reflection_type_cache_count}ull;
static const uint64_t expected_reflection_state_slot_rva = {expected_reflection_state_slot_rva}ull;
static const uint32_t expected_reflection_owner_count = {expected_reflection_owner_count}u;
static const wchar_t metadata_output[] = {metadata_literal};
static const wchar_t status_output[] = {status_literal};
static const wchar_t reflection_dispatch_output[] = {reflection_dispatch_literal};
static const wchar_t inventory_dispatch_output[] = {inventory_dispatch_literal};
static const wchar_t inventory_observation_output[] = {inventory_observation_literal};
static const wchar_t member_observation_output[] = {member_observation_literal};
static const wchar_t type_identity_observation_output[] = {type_identity_observation_literal};
static const wchar_t member_detail_observation_output[] = {member_detail_observation_literal};
static const wchar_t type_graph_observation_output[] = {type_graph_observation_literal};
static const wchar_t method_native_observation_output[] = {method_native_observation_literal};
static const wchar_t field_native_observation_output[] = {field_native_observation_literal};
static const wchar_t metadata_usage_observation_output[] = {metadata_usage_observation_literal};
static const wchar_t type_native_observation_output[] = {type_native_observation_literal};
static const wchar_t type_metadata_usage_observation_output[] = {type_metadata_usage_observation_literal};
static HMODULE self_module;
static uintptr_t *captured_type_native_handles;
static uint64_t captured_type_native_handle_count;

typedef struct {{
    uintptr_t address;
    uint64_t extent;
    uint32_t table_pairs;
    char sha256[65];
}} alpha_candidate;

typedef struct {{
    uint32_t pair_index;
    uint32_t offset;
    uint32_t bytes;
}} alpha_metadata_table;

typedef struct {{
    uint32_t pair_table_index;
    uint32_t pair_table_offset;
    uint32_t pair_table_bytes;
    uint32_t pair_stride;
    uint32_t destination_dword;
    uint32_t encoded_dword;
}} alpha_metadata_usage_layout;

typedef struct {{
    uint32_t destination_index;
    uint32_t source_index;
    uintptr_t type_handle;
}} alpha_type_metadata_usage_entry;

typedef struct {{
    alpha_candidate values[ALPHA_MAX_CANDIDATES];
    int count;
    int overflow;
    uint64_t regions;
    uint64_t bytes;
}} alpha_scan;

typedef struct {{
    uintptr_t values[ALPHA_MAX_RESOLVER_ANCHORS];
    uint32_t anchor_count;
    uint64_t reference_count;
    uint64_t candidate_count;
    uint32_t strong_count;
    uint64_t selected_target_direct_caller_count;
    uintptr_t selected_reference;
    uintptr_t selected_call;
    uintptr_t selected_target;
}} alpha_resolver_scan;

typedef struct {{
    uintptr_t state_slot;
    uintptr_t state_value;
    uintptr_t type_resolver_helper;
    uintptr_t string_class;
    uintptr_t dbnull_class;
    uint32_t bootstrap_attempt_count;
    uint64_t bootstrap_wait_milliseconds;
    uint64_t type_cache_count;
    uint64_t initialized_type_cache_count;
    uint32_t distinct_type_resolver_helper_count;
    uintptr_t required_owner_classes[ALPHA_MAX_REFLECTION_OWNERS];
    uint32_t initialized_required_owner_count;
    uint32_t dynamically_resolved_required_owner_count;
    int all_required_owner_classes_available;
    uint32_t vtable_start_qword;
    uint32_t vtable_candidate_count;
    uint32_t method_array_pointer_qword;
    uint32_t method_count_byte_offset;
    uint32_t method_layout_candidate_count;
    uint64_t method_record_count;
    uint32_t declaring_class_qword;
    uint32_t declaring_class_candidate_count;
    uint32_t method_pointer_qword;
    uint32_t method_pointer_candidate_count;
    uint64_t executable_method_pointer_count;
    int observed_class_layout_complete;
    uint64_t name_object_reference_count[ALPHA_NAME_OPERATION_COUNT];
    uint32_t cached_name_field_candidate_count[ALPHA_NAME_OPERATION_COUNT];
    uint32_t cached_name_field_qword[ALPHA_NAME_OPERATION_COUNT];
    uint64_t cached_name_field_support[ALPHA_NAME_OPERATION_COUNT];
    int cached_name_field_semantically_unique[ALPHA_NAME_OPERATION_COUNT];
    uint32_t name_getter_candidate_count[ALPHA_NAME_OPERATION_COUNT];
    uintptr_t name_getter_metadata[ALPHA_NAME_OPERATION_COUNT];
    uintptr_t name_getter_pointer[ALPHA_NAME_OPERATION_COUNT];
    uint32_t parameter_type_field_candidate_count;
    uint32_t parameter_type_field_qword;
    uint64_t parameter_type_field_support;
    int parameter_type_field_semantically_unique;
    uint32_t parameter_type_getter_candidate_count;
    uintptr_t parameter_type_getter_metadata;
    uintptr_t parameter_type_getter_pointer;
    int parameter_type_getter_semantically_unique;
    uint32_t parameter_flag_field_byte_offset[ALPHA_PARAMETER_FLAG_OPERATION_COUNT];
    uint32_t parameter_flag_getter_candidate_count[ALPHA_PARAMETER_FLAG_OPERATION_COUNT];
    uintptr_t parameter_flag_getter_metadata[ALPHA_PARAMETER_FLAG_OPERATION_COUNT];
    uintptr_t parameter_flag_getter_pointer[ALPHA_PARAMETER_FLAG_OPERATION_COUNT];
    uint64_t parameter_flag_object_reference_count;
    uint64_t parameter_flag_set_count[ALPHA_PARAMETER_FLAG_OPERATION_COUNT];
    uint64_t parameter_flag_clear_count[ALPHA_PARAMETER_FLAG_OPERATION_COUNT];
    int parameter_flag_field_semantically_unique;
    int parameter_flag_observation_complete;
    int parameter_flag_getters_semantically_unique;
    uint32_t parameter_default_field_candidate_count;
    uint32_t parameter_default_field_qword;
    uint64_t parameter_default_field_support;
    int parameter_default_field_semantically_unique;
    uint32_t parameter_default_getter_candidate_count;
    uintptr_t parameter_default_getter_metadata;
    uintptr_t parameter_default_getter_pointer;
    int parameter_default_getter_semantically_unique;
    uint32_t field_attributes_byte_offset;
    uint32_t field_attributes_getter_candidate_count;
    uintptr_t field_attributes_getter_metadata;
    uintptr_t field_attributes_getter_pointer;
    uint64_t field_attributes_object_reference_count;
    uint32_t field_attributes_first_value;
    uint64_t field_attributes_invalid_value_count;
    int field_attributes_distinct_values_observed;
    int field_attributes_getter_semantically_unique;
    int field_attributes_observation_complete;
    uint64_t property_named_object_reference_count;
    uint32_t property_accessor_field_candidate_count[ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT];
    uint32_t property_accessor_field_qword[ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT];
    uint64_t property_accessor_field_support[ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT];
    int property_accessor_field_semantically_unique[ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT];
    uint32_t property_accessor_getter_candidate_count[ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT];
    uintptr_t property_accessor_getter_metadata[ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT];
    uintptr_t property_accessor_getter_pointer[ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT];
    int property_accessors_semantically_unique;
    uint32_t method_name_metadata_field_qword;
    uint32_t method_name_node_field_qword;
    uint32_t method_name_encoded_field_qword;
    uint64_t method_name_xor_key;
    uintptr_t method_name_length_helper;
    uintptr_t method_name_managed_string_helper;
    uintptr_t method_name_lazy_initializer;
    uint64_t method_name_getter_rva;
    uint64_t method_name_length_helper_rva;
    uint64_t method_name_managed_string_helper_rva;
    uint64_t method_name_lazy_initializer_rva;
    int method_name_decoder_derived;
    int method_name_lazy_initializer_semantically_bound;
    uint32_t method_name_window_candidate_count;
    uint32_t method_name_window_thread_id;
    uint32_t method_name_callback_thread_id;
    int method_name_managed_callback_complete;
    uint64_t method_name_decode_attempt_count;
    uint64_t method_name_decode_success_count;
    uint64_t method_name_lazy_initialization_count;
    uint32_t method_name_decode_failure_reason;
    uint64_t method_name_decode_failure_index;
    uint64_t method_name_decode_failure_method_rva;
    uint32_t method_name_decode_failure_owner_index;
    uint32_t method_name_decode_failure_byte_index;
    uint32_t method_name_decode_failure_byte_value;
    uint32_t method_parameter_count_byte_offset;
    uint32_t method_parameter_count_field_candidate_count;
    int method_parameter_count_field_semantically_unique;
    int method_parameter_count_observation_complete;
    uint32_t runtime_named_operation_candidate_count[ALPHA_REFLECTION_OPERATION_COUNT];
    uint32_t runtime_named_operation_match_count;
    uint32_t runtime_named_operation_unique_count;
    uint32_t runtime_arity_operation_candidate_count[ALPHA_REFLECTION_OPERATION_COUNT];
    uintptr_t runtime_arity_operation_class[ALPHA_REFLECTION_OPERATION_COUNT];
    uintptr_t runtime_arity_operation_metadata[ALPHA_REFLECTION_OPERATION_COUNT];
    uintptr_t runtime_arity_operation_pointer[ALPHA_REFLECTION_OPERATION_COUNT];
    uint32_t runtime_arity_operation_match_count;
    uint32_t runtime_arity_operation_unique_count;
    int reflection_dispatch_contract_complete;
    int reflection_dispatch_manifest_written;
    uint32_t inventory_named_operation_candidate_count[ALPHA_INVENTORY_OPERATION_COUNT];
    uint32_t inventory_named_operation_match_count;
    uint32_t inventory_arity_operation_candidate_count[ALPHA_INVENTORY_OPERATION_COUNT];
    uintptr_t inventory_arity_operation_class[ALPHA_INVENTORY_OPERATION_COUNT];
    uintptr_t inventory_arity_operation_metadata[ALPHA_INVENTORY_OPERATION_COUNT];
    uintptr_t inventory_arity_operation_pointer[ALPHA_INVENTORY_OPERATION_COUNT];
    uint32_t inventory_arity_operation_match_count;
    uint32_t inventory_arity_operation_unique_count;
    int inventory_dispatch_contract_complete;
    int inventory_dispatch_manifest_written;
    uint32_t managed_window_candidate_count;
    uint32_t managed_window_thread_id;
    uint32_t managed_probe_callback_thread_id;
    int managed_thread_object_observed;
    int managed_thread_class_matches;
    int current_domain_object_observed;
    int current_domain_class_matches;
    int managed_thread_observation_complete;
    uintptr_t current_domain_object;
    uintptr_t assembly_array_pointer;
    uint32_t assembly_array_length_qword;
    uint32_t assembly_array_vector_qword;
    uint32_t assembly_array_layout_candidate_count;
    uint32_t assembly_count;
    int assembly_array_observed;
    int assembly_array_layout_unique;
    int all_assembly_objects_class_valid;
    int assembly_root_inventory_complete;
    uint32_t type_inventory_assembly_count;
    uint64_t type_inventory_type_count;
    uint32_t type_inventory_completed_slice_count;
    int type_inventory_all_objects_class_valid;
    int type_inventory_globally_unique;
    int type_inventory_observation_written;
    int type_inventory_observation_complete;
    char type_inventory_observation_sha256[65];
    uint64_t member_inventory_type_count;
    uint64_t member_inventory_totals[ALPHA_MEMBER_CATEGORY_COUNT];
    uint32_t member_inventory_completed_slice_count;
    int member_inventory_all_objects_class_valid;
    int member_inventory_globally_unique;
    int member_inventory_observation_written;
    int member_inventory_observation_complete;
    uint32_t type_identity_assembly_count;
    uint64_t type_identity_type_count;
    uint64_t type_identity_relation_count;
    int type_identity_all_names_valid;
    int type_identity_references_valid;
    int type_identity_observation_written;
    int type_identity_observation_complete;
    uint64_t member_detail_type_count;
    uint64_t member_detail_observation_bytes;
    int member_detail_observation_written;
    int member_detail_observation_complete;
    uint64_t type_graph_root_count;
    uint64_t type_graph_node_count;
    uint64_t type_graph_observation_bytes;
    int type_graph_reference_closure_complete;
    int type_graph_observation_written;
    int type_graph_observation_complete;
    uint64_t method_native_type_count;
    uint64_t method_native_method_count;
    uint64_t method_native_executable_count;
    uint64_t method_native_unique_metadata_count;
    uint64_t method_native_observation_bytes;
    uint32_t method_native_slot_byte_offset;
    int method_native_metadata_resolution_unique;
    int method_native_slot_layout_unique;
    int method_native_observation_written;
    int method_native_observation_complete;
    uint64_t field_native_type_count;
    uint64_t field_native_field_count;
    uint64_t field_native_unique_metadata_count;
    uint64_t field_native_observation_bytes;
    uint32_t field_native_metadata_stride;
    uint32_t field_native_offset_dword_index;
    uint32_t field_native_token_dword_index;
    int field_native_metadata_resolution_unique;
    int field_native_layout_derived;
    int field_native_observation_written;
    int field_native_observation_complete;
    uint64_t metadata_usage_count;
    uint64_t metadata_usage_array_rva;
    uint32_t metadata_usage_layout_match_count;
    uint32_t metadata_usage_array_match_count;
    uint64_t metadata_usage_observation_bytes;
    int metadata_usage_layout_derived;
    int metadata_usage_slots_unique;
    int metadata_usage_observation_written;
    int metadata_usage_observation_complete;
    uint64_t type_native_node_count;
    uint64_t type_native_unique_handle_count;
    uint64_t type_native_observation_bytes;
    int type_native_roundtrip_complete;
    int type_native_observation_written;
    int type_native_observation_complete;
    uint64_t type_metadata_usage_count;
    uint64_t type_registration_count;
    uint64_t type_registration_array_rva;
    uint32_t type_registration_array_match_count;
    uint64_t type_metadata_usage_observation_bytes;
    int type_metadata_usage_handles_unique;
    int type_metadata_usage_observation_written;
    int type_metadata_usage_observation_complete;
    uint32_t semantic_operation_count;
    int name_getters_semantically_unique;
}} alpha_reflection_scan;

typedef struct {{
    const char *namespace_name;
    const char *type_name;
    uint16_t minimum_method_count;
    int expected_cache;
    int layout_participant;
}} alpha_required_owner;

typedef struct {{
    uintptr_t metadata_pointer;
    uintptr_t class_pointer;
    uintptr_t method_pointer;
    uint16_t parameter_count;
    char runtime_name[512];
}} alpha_method_record;

typedef struct {{
    const char *key;
    const char *namespace_name;
    const char *type_name;
    const char *runtime_name;
    uint16_t parameter_count;
}} alpha_required_operation;

typedef struct {{
    uint32_t operation_index;
    const char *key;
    const char *namespace_name;
    const char *type_name;
    const char *runtime_name;
    uint16_t parameter_count;
}} alpha_inventory_operation_candidate;

static const alpha_required_owner required_reflection_owners[] = {{
{reflection_owner_table}
}};

static const uint32_t required_reflection_owner_count =
    (uint32_t)(sizeof(required_reflection_owners) /
               sizeof(required_reflection_owners[0]));

static const alpha_required_operation required_reflection_operations[] = {{
{reflection_operation_table}
}};

static const uint32_t required_reflection_operation_count =
    (uint32_t)(sizeof(required_reflection_operations) /
               sizeof(required_reflection_operations[0]));

static const alpha_inventory_operation_candidate required_inventory_operation_candidates[] = {{
{inventory_operation_table}
}};

static const uint32_t required_inventory_operation_candidate_count =
    (uint32_t)(sizeof(required_inventory_operation_candidates) /
               sizeof(required_inventory_operation_candidates[0]));

static const uint32_t required_inventory_operation_count =
    ALPHA_INVENTORY_OPERATION_COUNT;

static uint32_t rd32(const unsigned char *value) {{
    return ((uint32_t)value[0]) | ((uint32_t)value[1] << 8) |
           ((uint32_t)value[2] << 16) | ((uint32_t)value[3] << 24);
}}

static int readable_protection(DWORD protect) {{
    DWORD base = protect & 0xffu;
    if ((protect & PAGE_GUARD) || base == PAGE_NOACCESS || base == 0) return 0;
    return base == PAGE_READONLY || base == PAGE_READWRITE ||
           base == PAGE_WRITECOPY;
}}

static int read_exact(uintptr_t address, void *output, SIZE_T size) {{
    SIZE_T received = 0;
    return ReadProcessMemory(
        GetCurrentProcess(), (const void *)address, output, size, &received
    ) && received == size;
}}

static int ascii_name_char(unsigned char value) {{
    return (value >= 'a' && value <= 'z') ||
           (value >= 'A' && value <= 'Z') ||
           (value >= '0' && value <= '9') ||
           value == '_' || value == '-' || value == '.';
}}

static unsigned char ascii_lower(unsigned char value) {{
    return value >= 'A' && value <= 'Z' ? (unsigned char)(value + 32) : value;
}}

static int pointer_compare(const void *left_value, const void *right_value) {{
    uintptr_t left = *(const uintptr_t *)left_value;
    uintptr_t right = *(const uintptr_t *)right_value;
    return left < right ? -1 : left > right ? 1 : 0;
}}

static int anchor_present(const alpha_resolver_scan *scan, uintptr_t value) {{
    uint32_t lower = 0, upper = scan->anchor_count;
    while (lower < upper) {{
        uint32_t middle = lower + (upper - lower) / 2;
        uintptr_t candidate = scan->values[middle];
        if (candidate < value) lower = middle + 1;
        else upper = middle;
    }}
    return lower < scan->anchor_count && scan->values[lower] == value;
}}

static uint64_t section_extent(const IMAGE_SECTION_HEADER *section) {{
    uint64_t virtual_size = section->Misc.VirtualSize;
    return virtual_size > section->SizeOfRawData
        ? virtual_size : section->SizeOfRawData;
}}

static int rva_in_executable_section(
    const IMAGE_SECTION_HEADER *sections,
    WORD section_count,
    uint32_t rva
) {{
    for (WORD index = 0; index < section_count; index++) {{
        uint64_t begin = sections[index].VirtualAddress;
        uint64_t end = begin + section_extent(&sections[index]);
        if ((sections[index].Characteristics & IMAGE_SCN_MEM_EXECUTE) &&
            rva >= begin && rva < end) return 1;
    }}
    return 0;
}}

static const RUNTIME_FUNCTION *containing_runtime_function(
    const RUNTIME_FUNCTION *functions,
    uint32_t function_count,
    uint32_t rva
) {{
    uint32_t lower = 0, upper = function_count;
    while (lower < upper) {{
        uint32_t middle = lower + (upper - lower) / 2;
        if (functions[middle].BeginAddress <= rva) lower = middle + 1;
        else upper = middle;
    }}
    if (!lower) return NULL;
    const RUNTIME_FUNCTION *function = &functions[lower - 1];
    return rva >= function->BeginAddress && rva < function->EndAddress
        ? function : NULL;
}}

static int code_has_rax_dereference(
    const unsigned char *begin,
    const unsigned char *end
) {{
    for (const unsigned char *cursor = begin; cursor + 3 <= end; cursor++) {{
        unsigned char rex = cursor[0], opcode = cursor[1], modrm = cursor[2];
        unsigned char shape = modrm & 0xc7u;
        if (rex >= 0x48 && rex <= 0x4f && !(rex & 1u) && opcode == 0x8b &&
            (shape == 0x00 || shape == 0x40 || shape == 0x80)) return 1;
    }}
    return 0;
}}

static int code_has_rip_relative_store(
    const unsigned char *begin,
    const unsigned char *end
) {{
    for (const unsigned char *cursor = begin; cursor + 3 <= end; cursor++) {{
        unsigned char rex = cursor[0], opcode = cursor[1], modrm = cursor[2];
        if (rex >= 0x40 && rex <= 0x4f && opcode == 0x89 &&
            (modrm & 0xc7u) == 0x05) return 1;
    }}
    return 0;
}}

static int scan_runtime_resolver(alpha_resolver_scan *scan) {{
    memset(scan, 0, sizeof(*scan));
    unsigned char *base = (unsigned char *)GetModuleHandleW(NULL);
    if (!base) return 0;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)base;
    if (dos->e_magic != IMAGE_DOS_SIGNATURE || dos->e_lfanew <= 0) return 0;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(base + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE ||
        nt->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC ||
        !nt->FileHeader.NumberOfSections ||
        !nt->OptionalHeader.SizeOfImage) return 0;
    IMAGE_SECTION_HEADER *sections = IMAGE_FIRST_SECTION(nt);
    WORD section_count = nt->FileHeader.NumberOfSections;
    uint64_t image_size = nt->OptionalHeader.SizeOfImage;

    for (WORD section_index = 0; section_index < section_count; section_index++) {{
        const IMAGE_SECTION_HEADER *section = &sections[section_index];
        if (!(section->Characteristics & IMAGE_SCN_MEM_READ) ||
            (section->Characteristics & IMAGE_SCN_MEM_EXECUTE)) continue;
        uint64_t extent = section_extent(section);
        uint64_t section_rva = section->VirtualAddress;
        if (!extent || section_rva + extent > image_size) continue;
        const unsigned char *bytes = base + section_rva;
        for (uint64_t offset = 0; offset + 5 <= extent; offset++) {{
            if (bytes[offset] != '.' || ascii_lower(bytes[offset + 1]) != 'd' ||
                ascii_lower(bytes[offset + 2]) != 'l' ||
                ascii_lower(bytes[offset + 3]) != 'l' || bytes[offset + 4]) continue;
            uint64_t start = offset;
            while (start && offset - start < 128 && ascii_name_char(bytes[start - 1])) start--;
            if (start == offset || offset - start >= 128) continue;
            if (scan->anchor_count >= ALPHA_MAX_RESOLVER_ANCHORS) return 0;
            scan->values[scan->anchor_count++] = (uintptr_t)(bytes + start);
        }}
    }}
    if (!scan->anchor_count) return 0;
    qsort(
        scan->values, scan->anchor_count, sizeof(scan->values[0]), pointer_compare
    );
    uint32_t unique_count = 0;
    for (uint32_t index = 0; index < scan->anchor_count; index++) {{
        if (!unique_count || scan->values[index] != scan->values[unique_count - 1]) {{
            scan->values[unique_count++] = scan->values[index];
        }}
    }}
    scan->anchor_count = unique_count;

    IMAGE_DATA_DIRECTORY exception =
        nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXCEPTION];
    if (!exception.VirtualAddress || exception.Size < sizeof(RUNTIME_FUNCTION) ||
        exception.Size % sizeof(RUNTIME_FUNCTION) ||
        (uint64_t)exception.VirtualAddress + exception.Size > image_size) return 0;
    const RUNTIME_FUNCTION *functions =
        (const RUNTIME_FUNCTION *)(base + exception.VirtualAddress);
    uint32_t function_count = exception.Size / sizeof(RUNTIME_FUNCTION);

    for (WORD section_index = 0; section_index < section_count; section_index++) {{
        const IMAGE_SECTION_HEADER *section = &sections[section_index];
        if (!(section->Characteristics & IMAGE_SCN_MEM_EXECUTE)) continue;
        uint64_t extent = section_extent(section);
        uint64_t section_rva = section->VirtualAddress;
        if (!extent || section_rva + extent > image_size) continue;
        const unsigned char *bytes = base + section_rva;
        const unsigned char *section_end = bytes + extent;
        for (uint64_t offset = 0; offset + 7 <= extent; offset++) {{
            const unsigned char *instruction = bytes + offset;
            unsigned char rex = instruction[0];
            unsigned char opcode = instruction[1];
            unsigned char modrm = instruction[2];
            if (rex < 0x40 || rex > 0x4f ||
                (opcode != 0x8b && opcode != 0x8d) ||
                (modrm & 0xc7u) != 0x05) continue;
            int32_t displacement = 0;
            memcpy(&displacement, instruction + 3, sizeof(displacement));
            uintptr_t target = (uintptr_t)(instruction + 7) + (intptr_t)displacement;
            if (!anchor_present(scan, target)) continue;
            scan->reference_count++;
            uint32_t reference_rva = (uint32_t)(section_rva + offset);
            const RUNTIME_FUNCTION *function = containing_runtime_function(
                functions, function_count, reference_rva
            );
            if (!function || function->EndAddress > image_size) continue;
            const unsigned char *scan_begin = instruction + 7;
            const unsigned char *function_end = base + function->EndAddress;
            const unsigned char *call_end = scan_begin + 40;
            if (call_end > function_end) call_end = function_end;
            if (call_end > section_end) call_end = section_end;
            for (const unsigned char *call = scan_begin; call + 5 <= call_end; call++) {{
                if (*call != 0xe8) continue;
                int32_t call_displacement = 0;
                memcpy(&call_displacement, call + 1, sizeof(call_displacement));
                uintptr_t call_target =
                    (uintptr_t)(call + 5) + (intptr_t)call_displacement;
                if (call_target < (uintptr_t)base ||
                    call_target - (uintptr_t)base >= image_size ||
                    !rva_in_executable_section(
                        sections, section_count,
                        (uint32_t)(call_target - (uintptr_t)base)
                    )) continue;
                scan->candidate_count++;
                const unsigned char *after_call = call + 5;
                const unsigned char *return_end = after_call + 40;
                const unsigned char *store_end = after_call + 64;
                if (return_end > function_end) return_end = function_end;
                if (return_end > section_end) return_end = section_end;
                if (store_end > function_end) store_end = function_end;
                if (store_end > section_end) store_end = section_end;
                unsigned int destination_register =
                    ((modrm >> 3) & 7u) | ((rex & 4u) ? 8u : 0u);
                int argument_load = opcode == 0x8d &&
                    (destination_register == 1 || destination_register == 2 ||
                     destination_register == 8 || destination_register == 9);
                int return_dereference = code_has_rax_dereference(
                    after_call, return_end
                );
                int global_store = code_has_rip_relative_store(after_call, store_end);
                uint64_t call_distance = (uint64_t)(call - scan_begin);
                int score = (argument_load ? 3 : 0) + 2 + 2 +
                    (call_distance <= 16 ? 2 : 1) +
                    (return_dereference ? 4 : 0) + (global_store ? 2 : 0);
                if (score >= 13 && return_dereference && global_store) {{
                    scan->strong_count++;
                    if (scan->strong_count == 1) {{
                        scan->selected_reference = (uintptr_t)instruction;
                        scan->selected_call = (uintptr_t)call;
                        scan->selected_target = call_target;
                    }} else {{
                        scan->selected_reference = 0;
                        scan->selected_call = 0;
                        scan->selected_target = 0;
                    }}
                }}
            }}
        }}
    }}
    if (scan->strong_count == 1 && scan->selected_target) {{
        for (WORD section_index = 0; section_index < section_count; section_index++) {{
            const IMAGE_SECTION_HEADER *section = &sections[section_index];
            if (!(section->Characteristics & IMAGE_SCN_MEM_EXECUTE)) continue;
            uint64_t extent = section_extent(section);
            uint64_t section_rva = section->VirtualAddress;
            if (!extent || section_rva + extent > image_size) continue;
            const unsigned char *bytes = base + section_rva;
            for (uint64_t offset = 0; offset + 5 <= extent; offset++) {{
                if (bytes[offset] != 0xe8) continue;
                int32_t displacement = 0;
                memcpy(&displacement, bytes + offset + 1, sizeof(displacement));
                uintptr_t target =
                    (uintptr_t)(bytes + offset + 5) + (intptr_t)displacement;
                if (target == scan->selected_target) {{
                    scan->selected_target_direct_caller_count++;
                }}
            }}
        }}
    }}
    return scan->strong_count == 1 && scan->selected_target != 0 &&
           scan->selected_target_direct_caller_count >= 2;
}}

static int semantic_name_character(unsigned char value) {{
    return (value >= 'a' && value <= 'z') ||
           (value >= 'A' && value <= 'Z') ||
           (value >= '0' && value <= '9') ||
           value == '_' || value == '.' || value == '`' || value == '+' ||
           value == '<' || value == '>' || value == '-';
}}

static int semantic_image_string(
    const unsigned char *base,
    uint64_t image_size,
    uintptr_t value
) {{
    if (value < (uintptr_t)base || value - (uintptr_t)base >= image_size) return 0;
    const unsigned char *text = (const unsigned char *)value;
    uint64_t remaining = image_size - (uint64_t)(value - (uintptr_t)base);
    uint64_t limit = remaining < 161 ? remaining : 161;
    if (!limit || !semantic_name_character(text[0])) return 0;
    for (uint64_t index = 1; index < limit; index++) {{
        if (!text[index]) return 1;
        if (!semantic_name_character(text[index])) return 0;
    }}
    return 0;
}}

static int rax_load_length(const unsigned char *cursor, const unsigned char *end) {{
    if (cursor + 3 > end || cursor[0] < 0x48 || cursor[0] > 0x4f ||
        (cursor[0] & 1u) || cursor[1] != 0x8b) return 0;
    unsigned char shape = cursor[2] & 0xc7u;
    if (shape == 0x00) return 3;
    if (shape == 0x40 && cursor + 4 <= end) return 4;
    if (shape == 0x80 && cursor + 7 <= end) return 7;
    return 0;
}}

static int memory_pointer_kind(uintptr_t value) {{
    if (!value) return 0;
    MEMORY_BASIC_INFORMATION info;
    if (!VirtualQuery((const void *)value, &info, sizeof(info)) ||
        info.State != MEM_COMMIT || (info.Protect & PAGE_GUARD)) return 0;
    DWORD protection = info.Protect & 0xffu;
    if (!protection || protection == PAGE_NOACCESS) return 0;
    if (protection == PAGE_EXECUTE || protection == PAGE_EXECUTE_READ ||
        protection == PAGE_EXECUTE_READWRITE ||
        protection == PAGE_EXECUTE_WRITECOPY) return 2;
    if (protection == PAGE_READONLY || protection == PAGE_READWRITE ||
        protection == PAGE_WRITECOPY) return 1;
    return 0;
}}

static int method_array_is_metadata(
    uintptr_t pointer,
    uint16_t count
) {{
    uint32_t metadata = 0;
    if (!pointer || !count || count > 4096) return 0;
    for (uint32_t index = 0; index < count; index++) {{
        if (index > (UINTPTR_MAX - pointer) / sizeof(uintptr_t)) return 0;
        uintptr_t entry = 0;
        if (!read_exact(
                pointer + index * sizeof(uintptr_t),
                &entry,
                sizeof(entry)
            )) return 0;
        if (memory_pointer_kind(entry) == 1) metadata++;
    }}
    return (uint64_t)metadata * 10u >= (uint64_t)count * 9u;
}}

static uintptr_t required_owner_class(
    const alpha_reflection_scan *scan,
    const char *namespace_name,
    const char *type_name
) {{
    if (!scan) return 0;
    for (uint32_t index = 0; index < required_reflection_owner_count; index++) {{
        if (!strcmp(
                required_reflection_owners[index].namespace_name,
                namespace_name
            ) && !strcmp(
                required_reflection_owners[index].type_name,
                type_name
            )) return scan->required_owner_classes[index];
    }}
    return 0;
}}

static int runtime_managed_string(
    uintptr_t value,
    uintptr_t string_class
) {{
    uintptr_t observed_class = 0;
    int32_t length = 0;
    if (!value || !string_class || memory_pointer_kind(value) != 1 ||
        !read_exact(value, &observed_class, sizeof(observed_class)) ||
        observed_class != string_class ||
        value > UINTPTR_MAX - 20 ||
        !read_exact(value + 16, &length, sizeof(length)) ||
        length <= 0 || length > 512) return 0;
    uint64_t bytes = (uint64_t)length * 2u;
    if (bytes > UINTPTR_MAX - (value + 20)) return 0;
    unsigned char terminal[2] = {{0xff, 0xff}};
    return read_exact(value + 20 + (uintptr_t)bytes, terminal, sizeof(terminal)) &&
           terminal[0] == 0 && terminal[1] == 0;
}}

static char *copy_runtime_managed_utf8(
    uintptr_t value,
    uintptr_t string_class,
    int allow_null
) {{
    uintptr_t observed_class = 0;
    int32_t length = 0;
    WCHAR *wide = NULL;
    char *utf8 = NULL;
    if (!value) {{
        if (!allow_null) return NULL;
        utf8 = (char *)calloc(1, 1);
        return utf8;
    }}
    if (!string_class || memory_pointer_kind(value) != 1 ||
        !read_exact(value, &observed_class, sizeof(observed_class)) ||
        observed_class != string_class || value > UINTPTR_MAX - 20 ||
        !read_exact(value + 16, &length, sizeof(length)) ||
        length < 0 || length > 8192 || (!allow_null && !length))
        return NULL;
    wide = (WCHAR *)calloc((SIZE_T)length + 1, sizeof(WCHAR));
    if (!wide || (length && !read_exact(
            value + 20,
            wide,
            (SIZE_T)length * sizeof(WCHAR)
        ))) {{
        free(wide);
        return NULL;
    }}
    for (int32_t index = 0; index < length; index++) {{
        if (wide[index] < 0x20) {{
            free(wide);
            return NULL;
        }}
    }}
    int bytes = WideCharToMultiByte(
        CP_UTF8, WC_ERR_INVALID_CHARS, wide, length, NULL, 0, NULL, NULL
    );
    if (bytes < 0 || (length && !bytes) || (!allow_null && !bytes)) {{
        free(wide);
        return NULL;
    }}
    utf8 = (char *)calloc((SIZE_T)bytes + 1, 1);
    if (!utf8 || (bytes && WideCharToMultiByte(
            CP_UTF8,
            WC_ERR_INVALID_CHARS,
            wide,
            length,
            utf8,
            bytes,
            NULL,
            NULL
        ) != bytes)) {{
        free(wide);
        free(utf8);
        return NULL;
    }}
    free(wide);
    return utf8;
}}

static int runtime_object_has_class(
    uintptr_t value,
    uintptr_t target_class
) {{
    uintptr_t observed_class = 0;
    return value && target_class && memory_pointer_kind(value) == 1 &&
           read_exact(value, &observed_class, sizeof(observed_class)) &&
           observed_class == target_class;
}}

static int runtime_accessor_name_matches(
    uintptr_t property_name,
    uintptr_t method_name,
    uintptr_t string_class,
    uint32_t accessor
) {{
    int32_t property_length = 0, method_length = 0;
    uint16_t property_value[508], method_value[512];
    static const uint16_t prefixes[ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT][4] = {{
        {{'g', 'e', 't', '_'}},
        {{'s', 'e', 't', '_'}}
    }};
    if (accessor >= ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT ||
        !runtime_managed_string(property_name, string_class) ||
        !runtime_managed_string(method_name, string_class) ||
        !read_exact(property_name + 16, &property_length, sizeof(property_length)) ||
        !read_exact(method_name + 16, &method_length, sizeof(method_length)) ||
        property_length <= 0 || property_length > 508 ||
        method_length != property_length + 4 ||
        !read_exact(
            property_name + 20,
            property_value,
            (SIZE_T)property_length * sizeof(uint16_t)
        ) || !read_exact(
            method_name + 20,
            method_value,
            (SIZE_T)method_length * sizeof(uint16_t)
        )) return 0;
    return !memcmp(method_value, prefixes[accessor], sizeof(prefixes[accessor])) &&
           !memcmp(
               method_value + 4,
               property_value,
               (SIZE_T)property_length * sizeof(uint16_t)
           );
}}

static int select_unique_supported_field(
    const uint64_t support[10],
    uint32_t *candidate_count,
    uint32_t *selected_field,
    uint64_t *selected_support,
    uint64_t minimum_support
) {{
    uint64_t strongest = 0;
    uint32_t strongest_count = 0;
    if (!support || !candidate_count || !selected_field || !selected_support)
        return 0;
    *candidate_count = 0;
    *selected_field = 0;
    *selected_support = 0;
    for (uint32_t field = 0; field < 10; field++) {{
        if (support[field]) (*candidate_count)++;
        if (support[field] > strongest) {{
            strongest = support[field];
            strongest_count = 1;
            *selected_field = field;
        }} else if (support[field] == strongest && strongest) {{
            strongest_count++;
        }}
    }}
    *selected_support = strongest;
    return strongest_count == 1 && strongest >= minimum_support;
}}

static int code_loads_cached_name_field(
    uintptr_t method_pointer,
    uint32_t field_qword
) {{
    if (!method_pointer || memory_pointer_kind(method_pointer) != 2 ||
        field_qword >= 16 || field_qword * 8u > 0x7fu) return 0;
    unsigned char code[256];
    if (!read_exact(method_pointer, code, sizeof(code))) return 0;
    unsigned char displacement = (unsigned char)(field_qword * 8u);
    for (uint32_t offset = 0; offset <= 32 && offset + 9 <= sizeof(code); offset++) {{
        if (code[offset] != 0x48 || code[offset + 1] != 0x8b ||
            code[offset + 2] != 0x41 || code[offset + 3] != displacement ||
            code[offset + 4] != 0x48 || code[offset + 5] != 0x85 ||
            code[offset + 6] != 0xc0) continue;
        int branches = code[offset + 7] == 0x74 || code[offset + 7] == 0x75 ||
            (code[offset + 7] == 0x0f &&
             (code[offset + 8] == 0x84 || code[offset + 8] == 0x85));
        if (!branches) continue;
        for (uint32_t tail = offset + 7; tail < sizeof(code); tail++) {{
            if (code[tail] == 0xc3) return 1;
        }}
    }}
    return 0;
}}

static int code_directly_returns_name_field(
    uintptr_t method_pointer,
    uint32_t field_qword
) {{
    if (!method_pointer || memory_pointer_kind(method_pointer) != 2 ||
        field_qword >= 16 || field_qword * 8u > 0x7fu) return 0;
    unsigned char code[5];
    return read_exact(method_pointer, code, sizeof(code)) &&
           code[0] == 0x48 && code[1] == 0x8b && code[2] == 0x41 &&
           code[3] == (unsigned char)(field_qword * 8u) && code[4] == 0xc3;
}}

static int code_returns_rsi_field(
    uintptr_t method_pointer,
    uint32_t field_qword
) {{
    if (!method_pointer || memory_pointer_kind(method_pointer) != 2 ||
        field_qword >= 16 || field_qword * 8u > 0x7fu) return 0;
    unsigned char code[256];
    if (!read_exact(method_pointer, code, sizeof(code))) return 0;
    uint32_t first_return = sizeof(code);
    for (uint32_t index = 0; index < sizeof(code); index++) {{
        if (code[index] == 0xc3) {{
            first_return = index;
            break;
        }}
    }}
    uint32_t alias = sizeof(code), load = sizeof(code);
    for (uint32_t index = 0; index + 3 <= first_return; index++) {{
        if (code[index] == 0x48 && code[index + 1] == 0x89 &&
            code[index + 2] == 0xce) alias = index;
    }}
    for (uint32_t index = 0; index + 4 <= first_return; index++) {{
        if (code[index] == 0x48 && code[index + 1] == 0x8b &&
            code[index + 2] == 0x46 &&
            code[index + 3] == (unsigned char)(field_qword * 8u)) load = index;
    }}
    return alias < load && load < first_return && first_return - load <= 16;
}}

static int name_getter_shape(
    uint32_t operation,
    uintptr_t method_pointer,
    uint32_t field_qword
) {{
    if (operation == 0) return code_loads_cached_name_field(
        method_pointer, field_qword
    );
    if (operation == 1) return code_directly_returns_name_field(
        method_pointer, field_qword
    );
    if (operation == 2) return code_returns_rsi_field(
        method_pointer, field_qword
    );
    if (operation == 3) return code_directly_returns_name_field(
        method_pointer, field_qword
    );
    return 0;
}}

static int parameter_flag_getter_shape(
    uintptr_t method_pointer,
    uint32_t *byte_offset,
    unsigned char *semantic_mask
) {{
    unsigned char code[16];
    uint32_t cursor = 0;
    int32_t signed_offset = 0;
    if (!method_pointer || !byte_offset || !semantic_mask ||
        memory_pointer_kind(method_pointer) != 2 ||
        !read_exact(method_pointer, code, sizeof(code)) ||
        code[0] != 0x0f || code[1] != 0xb6) return 0;
    if (code[2] == 0x41) {{
        signed_offset = code[3];
        cursor = 4;
    }} else if (code[2] == 0x81) {{
        memcpy(&signed_offset, code + 3, sizeof(signed_offset));
        cursor = 7;
    }} else return 0;
    if (signed_offset < 0 || code[cursor] != 0x24) return 0;
    unsigned char mask = code[cursor + 1];
    if (!mask || (mask & (mask - 1u))) return 0;
    cursor += 2;
    uint32_t shift = 0;
    for (unsigned char value = mask; value > 1; value >>= 1) shift++;
    if (shift == 1 && code[cursor] == 0xd0 && code[cursor + 1] == 0xe8) {{
        cursor += 2;
    }} else if (shift) {{
        if (code[cursor] != 0xc0 || code[cursor + 1] != 0xe8 ||
            code[cursor + 2] != shift) return 0;
        cursor += 3;
    }}
    if (code[cursor] != 0xc3) return 0;
    *byte_offset = (uint32_t)signed_offset;
    *semantic_mask = mask;
    return 1;
}}

static int direct_dword_getter_shape(
    uintptr_t method_pointer,
    uint32_t *byte_offset
) {{
    unsigned char code[7];
    int32_t signed_offset = 0;
    if (!method_pointer || !byte_offset ||
        memory_pointer_kind(method_pointer) != 2 ||
        !read_exact(method_pointer, code, sizeof(code)) || code[0] != 0x8b)
        return 0;
    if (code[1] == 0x41 && code[3] == 0xc3) {{
        *byte_offset = code[2];
        return 1;
    }}
    if (code[1] != 0x81 || code[6] != 0xc3) return 0;
    memcpy(&signed_offset, code + 2, sizeof(signed_offset));
    if (signed_offset < 0) return 0;
    *byte_offset = (uint32_t)signed_offset;
    return 1;
}}

static int code_contains_bytes(
    const unsigned char *code,
    SIZE_T code_size,
    const unsigned char *pattern,
    SIZE_T pattern_size
) {{
    if (!code || !pattern || !pattern_size || pattern_size > code_size) return 0;
    for (SIZE_T offset = 0; offset + pattern_size <= code_size; offset++) {{
        if (!memcmp(code + offset, pattern, pattern_size)) return 1;
    }}
    return 0;
}}

static int property_accessor_getter_shape(
    uintptr_t method_pointer,
    uint32_t field_qword
) {{
    if (!method_pointer || field_qword >= 16 || field_qword * 8u > 0x7fu ||
        memory_pointer_kind(method_pointer) != 2) return 0;
    unsigned char code[256];
    if (!read_exact(method_pointer, code, sizeof(code))) return 0;
    unsigned char field_load[] = {{
        0x48, 0x8b, 0x46, (unsigned char)(field_qword * 8u)
    }};
    static const unsigned char save_boolean[] = {{0x89, 0xd3}};
    static const unsigned char alias_this[] = {{0x48, 0x89, 0xce}};
    static const unsigned char test_result[] = {{0x48, 0x85, 0xc0}};
    static const unsigned char test_boolean[] = {{0x84, 0xdb}};
    static const unsigned char access_mask[] = {{0x83, 0xe1, 0x07}};
    static const unsigned char public_access[] = {{0x83, 0xf9, 0x06}};
    static const unsigned char return_instruction[] = {{0xc3}};
    return code_contains_bytes(code, sizeof(code), field_load, sizeof(field_load)) &&
           code_contains_bytes(
               code, sizeof(code), save_boolean, sizeof(save_boolean)
           ) && code_contains_bytes(code, sizeof(code), alias_this, sizeof(alias_this)) &&
           code_contains_bytes(code, sizeof(code), test_result, sizeof(test_result)) &&
           code_contains_bytes(
               code, sizeof(code), test_boolean, sizeof(test_boolean)
           ) && code_contains_bytes(code, sizeof(code), access_mask, sizeof(access_mask)) &&
           code_contains_bytes(
               code, sizeof(code), public_access, sizeof(public_access)
           ) && code_contains_bytes(
               code, sizeof(code), return_instruction, sizeof(return_instruction)
           );
}}

static SIZE_T code_bytes_offset_from(
    const unsigned char *code,
    SIZE_T code_size,
    const unsigned char *pattern,
    SIZE_T pattern_size,
    SIZE_T start
) {{
    if (!code || !pattern || !pattern_size || start > code_size ||
        pattern_size > code_size - start) return SIZE_MAX;
    for (SIZE_T offset = start;
         offset + pattern_size <= code_size;
         offset++) {{
        if (!memcmp(code + offset, pattern, pattern_size)) return offset;
    }}
    return SIZE_MAX;
}}

static int current_image_bounds(uintptr_t *image_base, uint64_t *image_bytes) {{
    unsigned char *base = (unsigned char *)GetModuleHandleW(NULL);
    if (!base || !image_base || !image_bytes) return 0;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)base;
    if (dos->e_magic != IMAGE_DOS_SIGNATURE || dos->e_lfanew <= 0) return 0;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(base + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE ||
        nt->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC ||
        !nt->OptionalHeader.SizeOfImage ||
        nt->OptionalHeader.SizeOfImage > UINT32_MAX) return 0;
    *image_base = (uintptr_t)base;
    *image_bytes = nt->OptionalHeader.SizeOfImage;
    return 1;
}}

static int current_image_executable_pointer(uintptr_t pointer) {{
    uintptr_t image_base = 0;
    uint64_t image_bytes = 0;
    if (!current_image_bounds(&image_base, &image_bytes) ||
        pointer < image_base || pointer - image_base >= image_bytes)
        return 0;
    unsigned char *base = (unsigned char *)image_base;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)base;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(base + dos->e_lfanew);
    if (
        pointer - (uintptr_t)base >= nt->OptionalHeader.SizeOfImage ||
        pointer - (uintptr_t)base > UINT32_MAX) return 0;
    return rva_in_executable_section(
        IMAGE_FIRST_SECTION(nt),
        nt->FileHeader.NumberOfSections,
        (uint32_t)(pointer - (uintptr_t)base)
    ) && memory_pointer_kind(pointer) == 2;
}}

static int read_current_runtime_function(
    uintptr_t pointer,
    unsigned char *output,
    SIZE_T capacity,
    SIZE_T *received
) {{
    unsigned char *base = (unsigned char *)GetModuleHandleW(NULL);
    if (!output || !capacity || !received ||
        !current_image_executable_pointer(pointer)) return 0;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)base;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(base + dos->e_lfanew);
    IMAGE_DATA_DIRECTORY exception =
        nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXCEPTION];
    if (!exception.VirtualAddress || exception.Size < sizeof(RUNTIME_FUNCTION) ||
        exception.Size % sizeof(RUNTIME_FUNCTION) ||
        (uint64_t)exception.VirtualAddress + exception.Size >
            nt->OptionalHeader.SizeOfImage) return 0;
    uint32_t rva = (uint32_t)(pointer - (uintptr_t)base);
    const RUNTIME_FUNCTION *functions =
        (const RUNTIME_FUNCTION *)(base + exception.VirtualAddress);
    const RUNTIME_FUNCTION *function = containing_runtime_function(
        functions,
        exception.Size / sizeof(RUNTIME_FUNCTION),
        rva
    );
    if (!function || function->EndAddress <= rva ||
        function->EndAddress > nt->OptionalHeader.SizeOfImage) return 0;
    SIZE_T amount = (SIZE_T)(function->EndAddress - rva);
    if (amount > capacity) amount = capacity;
    if (!amount || !read_exact(pointer, output, amount)) return 0;
    *received = amount;
    return 1;
}}

static int relative_call_target(
    uintptr_t method_pointer,
    const unsigned char *code,
    SIZE_T code_size,
    SIZE_T call_offset,
    uintptr_t *target
) {{
    int32_t displacement = 0;
    if (!code || !target || call_offset > code_size ||
        code_size - call_offset < 5 || code[call_offset] != 0xe8 ||
        method_pointer > UINTPTR_MAX - call_offset - 5) return 0;
    memcpy(&displacement, code + call_offset + 1, sizeof(displacement));
    uintptr_t origin = method_pointer + call_offset + 5;
    uintptr_t value = displacement < 0
        ? origin - (uintptr_t)(-(int64_t)displacement)
        : origin + (uintptr_t)displacement;
    if (!current_image_executable_pointer(value)) return 0;
    *target = value;
    return 1;
}}

static int find_keyed_rax_qword_xor(
    const unsigned char *code,
    SIZE_T code_size,
    SIZE_T start,
    SIZE_T *key_at,
    SIZE_T *xor_at,
    SIZE_T *xor_bytes,
    unsigned char *memory_offset,
    uint64_t *key
) {{
    uint32_t match_count = 0;
    if (!code || !key_at || !xor_at || !xor_bytes || !memory_offset ||
        !key || start >= code_size) return 0;
    for (SIZE_T load = start; load + 10 <= code_size; load++) {{
        unsigned char rex = code[load];
        unsigned char opcode = code[load + 1];
        if ((rex & 0xf8u) != 0x48u || opcode < 0xb8u || opcode > 0xbfu)
            continue;
        uint32_t destination = (opcode - 0xb8u) |
            ((rex & 0x04u) ? 8u : 0u);
        uint64_t immediate = 0;
        memcpy(&immediate, code + load + 2, sizeof(immediate));
        if (!immediate) continue;
        for (SIZE_T operation = load + 10;
             operation + 3 <= code_size;
             operation++) {{
            unsigned char operation_rex = code[operation];
            if ((operation_rex & 0xf8u) != 0x48u ||
                code[operation + 1] != 0x33u) continue;
            unsigned char modrm = code[operation + 2];
            uint32_t observed_destination = ((modrm >> 3) & 7u) |
                ((operation_rex & 0x04u) ? 8u : 0u);
            uint32_t base = (modrm & 7u) |
                ((operation_rex & 0x01u) ? 8u : 0u);
            uint32_t mode = modrm >> 6;
            if (observed_destination != destination || base != 0u ||
                mode == 3u) continue;
            int64_t displacement = 0;
            SIZE_T instruction_bytes = 3;
            if (mode == 1u) {{
                if (operation + 4 > code_size) continue;
                displacement = (int8_t)code[operation + 3];
                instruction_bytes = 4;
            }} else if (mode == 2u) {{
                int32_t value = 0;
                if (operation + 7 > code_size) continue;
                memcpy(&value, code + operation + 3, sizeof(value));
                displacement = value;
                instruction_bytes = 7;
            }}
            if (displacement < 0 || displacement > 0x78 ||
                (displacement & 7)) continue;
            match_count++;
            if (match_count == 1) {{
                *key_at = load;
                *xor_at = operation;
                *xor_bytes = instruction_bytes;
                *memory_offset = (unsigned char)displacement;
                *key = immediate;
            }}
        }}
    }}
    return match_count == 1;
}}

static int lazy_name_initializer_matches(
    const alpha_reflection_scan *scan
) {{
    unsigned char code[512];
    SIZE_T code_size = 0;
    if (!scan || !scan->method_name_lazy_initializer ||
        scan->method_name_node_field_qword >= 16 ||
        scan->method_name_encoded_field_qword >= 16 ||
        !read_current_runtime_function(
            scan->method_name_lazy_initializer,
            code,
            sizeof(code),
            &code_size
        )) return 0;
    unsigned char alias[] = {{0x48, 0x89, 0xce}};
    unsigned char node_load[] = {{
        0x48, 0x8b, 0x46,
        (unsigned char)(scan->method_name_node_field_qword * 8u)
    }};
    unsigned char key_load[10] = {{0x48, 0xbb}};
    memcpy(key_load + 2, &scan->method_name_xor_key, sizeof(uint64_t));
    unsigned char node_store[] = {{
        0x48, 0x89, 0x46,
        (unsigned char)(scan->method_name_node_field_qword * 8u)
    }};
    static const unsigned char xor_first[] = {{0x48, 0x31, 0xdf}};
    static const unsigned char xor_second[] = {{0x48, 0x33, 0xfb}};
    static const unsigned char return_instruction[] = {{0xc3}};
    return code_contains_bytes(code, code_size, alias, sizeof(alias)) &&
           code_contains_bytes(code, code_size, node_load, sizeof(node_load)) &&
           code_contains_bytes(code, code_size, key_load, sizeof(key_load)) &&
           code_contains_bytes(code, code_size, node_store, sizeof(node_store)) &&
           (code_contains_bytes(
                code, code_size, xor_first, sizeof(xor_first)
            ) || code_contains_bytes(
                code, code_size, xor_second, sizeof(xor_second)
            )) && code_contains_bytes(
                code, code_size,
                return_instruction, sizeof(return_instruction)
            );
}}

static int derive_method_name_decoder(alpha_reflection_scan *scan) {{
    unsigned char code[1024];
    SIZE_T code_size = 0;
    if (!scan || !scan->name_getter_pointer[0] ||
        scan->cached_name_field_qword[0] >= 16 ||
        required_reflection_operation_count != ALPHA_REFLECTION_OPERATION_COUNT ||
        !read_current_runtime_function(
            scan->name_getter_pointer[0], code, sizeof(code), &code_size
        ) || code_size < 32) return 0;
    unsigned char cached_load[] = {{
        0x48, 0x8b, 0x41,
        (unsigned char)(scan->cached_name_field_qword[0] * 8u)
    }};
    unsigned char cached_store[] = {{
        0x48, 0x89, 0x46,
        (unsigned char)(scan->cached_name_field_qword[0] * 8u)
    }};
    static const unsigned char alias[] = {{0x48, 0x89, 0xce}};
    static const unsigned char metadata_load_prefix[] = {{0x48, 0x8b, 0x49}};
    static const unsigned char node_load_prefix[] = {{0x48, 0x8b, 0x41}};
    static const unsigned char length_prefix[] = {{0x48, 0x89, 0xf9, 0xe8}};
    static const unsigned char decode_prefix[] = {{
        0x48, 0x89, 0xf9, 0x89, 0xc2, 0xe8
    }};
    static const unsigned char epilogue_prefix[] = {{0x48, 0x83, 0xc4}};
    if (!code_contains_bytes(
            code, code_size, cached_load, sizeof(cached_load)
        ) || !code_contains_bytes(
            code, code_size, cached_store, sizeof(cached_store)
        )) return 0;
    SIZE_T alias_at = code_bytes_offset_from(
        code, code_size, alias, sizeof(alias), 0
    );
    SIZE_T metadata_at = alias_at == SIZE_MAX ? SIZE_MAX : code_bytes_offset_from(
        code, code_size,
        metadata_load_prefix, sizeof(metadata_load_prefix), alias_at + sizeof(alias)
    );
    SIZE_T node_at = metadata_at == SIZE_MAX ? SIZE_MAX : code_bytes_offset_from(
        code, code_size,
        node_load_prefix, sizeof(node_load_prefix),
        metadata_at + sizeof(metadata_load_prefix) + 1
    );
    SIZE_T key_at = SIZE_MAX, encoded_at = SIZE_MAX, encoded_bytes = 0;
    unsigned char encoded_offset = 0;
    uint64_t key = 0;
    if (metadata_at == SIZE_MAX || node_at == SIZE_MAX ||
        metadata_at + 4 > code_size || node_at + 4 > code_size ||
        !find_keyed_rax_qword_xor(
            code, code_size,
            node_at + sizeof(node_load_prefix) + 1,
            &key_at, &encoded_at, &encoded_bytes, &encoded_offset, &key
        )) return 0;
    unsigned char metadata_offset = code[metadata_at + 3];
    unsigned char node_offset = code[node_at + 3];
    if ((metadata_offset & 7u) || (node_offset & 7u) ||
        (encoded_offset & 7u) || metadata_offset > 0x78 ||
        node_offset > 0x78 || encoded_offset > 0x78) return 0;
    SIZE_T length_at = code_bytes_offset_from(
        code, code_size,
        length_prefix, sizeof(length_prefix), encoded_at + encoded_bytes
    );
    SIZE_T decode_at = length_at == SIZE_MAX ? SIZE_MAX : code_bytes_offset_from(
        code, code_size,
        decode_prefix, sizeof(decode_prefix), length_at + sizeof(length_prefix)
    );
    SIZE_T epilogue_at = decode_at == SIZE_MAX ? SIZE_MAX : code_bytes_offset_from(
        code, code_size,
        epilogue_prefix, sizeof(epilogue_prefix), decode_at + sizeof(decode_prefix)
    );
    static const unsigned char return_instruction[] = {{0xc3}};
    SIZE_T return_at = epilogue_at == SIZE_MAX ? SIZE_MAX : code_bytes_offset_from(
        code, code_size,
        return_instruction, sizeof(return_instruction),
        epilogue_at + sizeof(epilogue_prefix)
    );
    SIZE_T lazy_at = return_at == SIZE_MAX ? SIZE_MAX : code_bytes_offset_from(
        code, code_size,
        (const unsigned char *)"\xe8", 1, return_at + 1
    );
    uintptr_t length_helper = 0, managed_string_helper = 0, lazy_initializer = 0;
    if (length_at == SIZE_MAX || decode_at == SIZE_MAX ||
        epilogue_at == SIZE_MAX || return_at == SIZE_MAX ||
        lazy_at == SIZE_MAX || !relative_call_target(
            scan->name_getter_pointer[0], code, code_size,
            length_at + 3, &length_helper
        ) || !relative_call_target(
            scan->name_getter_pointer[0], code, code_size,
            decode_at + 5, &managed_string_helper
        ) || !relative_call_target(
            scan->name_getter_pointer[0], code, code_size,
            lazy_at, &lazy_initializer
        )) return 0;
    scan->method_name_metadata_field_qword = metadata_offset / 8u;
    scan->method_name_node_field_qword = node_offset / 8u;
    scan->method_name_encoded_field_qword = encoded_offset / 8u;
    scan->method_name_xor_key = key;
    scan->method_name_length_helper = length_helper;
    scan->method_name_managed_string_helper = managed_string_helper;
    scan->method_name_lazy_initializer = lazy_initializer;
    unsigned char *image_base = (unsigned char *)GetModuleHandleW(NULL);
    if (!image_base || scan->name_getter_pointer[0] < (uintptr_t)image_base ||
        length_helper < (uintptr_t)image_base ||
        managed_string_helper < (uintptr_t)image_base ||
        lazy_initializer < (uintptr_t)image_base) return 0;
    scan->method_name_getter_rva =
        scan->name_getter_pointer[0] - (uintptr_t)image_base;
    scan->method_name_length_helper_rva =
        length_helper - (uintptr_t)image_base;
    scan->method_name_managed_string_helper_rva =
        managed_string_helper - (uintptr_t)image_base;
    scan->method_name_lazy_initializer_rva =
        lazy_initializer - (uintptr_t)image_base;
    if (!lazy_name_initializer_matches(scan)) return 0;
    scan->method_name_decoder_derived = 1;
    scan->method_name_lazy_initializer_semantically_bound = 1;
    return 1;
}}

typedef uintptr_t (*alpha_lazy_name_initializer)(uintptr_t metadata_pointer);
typedef int32_t (*alpha_method_name_length_helper)(uintptr_t encoded_name);
typedef uintptr_t (*alpha_method_name_string_helper)(
    uintptr_t encoded_name,
    int32_t length
);

static int runtime_method_name_internal(
    alpha_reflection_scan *scan,
    uintptr_t metadata_pointer,
    char *output,
    SIZE_T capacity,
    int record_observation
) {{
    uintptr_t node = 0, encoded = 0, value = 0;
    if (!scan || !metadata_pointer || !output || capacity < 2 ||
        !scan->method_name_decoder_derived ||
        !scan->method_name_lazy_initializer_semantically_bound ||
        scan->method_name_metadata_field_qword >= 16 ||
        scan->method_name_node_field_qword >= 16 ||
        scan->method_name_encoded_field_qword >= 16) {{
        if (scan && record_observation &&
            !scan->method_name_decode_failure_index)
            scan->method_name_decode_failure_reason = 1;
        return 0;
    }}
    if (record_observation && !scan->method_name_decode_failure_index) {{
        scan->method_name_decode_failure_reason = 0;
        scan->method_name_decode_failure_byte_index = 0;
        scan->method_name_decode_failure_byte_value = 0;
    }}
    if (record_observation) scan->method_name_decode_attempt_count++;
    if (!read_exact(
            metadata_pointer + scan->method_name_node_field_qword * 8u,
            &node,
            sizeof(node)
        )) {{
        if (record_observation && !scan->method_name_decode_failure_index)
            scan->method_name_decode_failure_reason = 2;
        return 0;
    }}
    if (node) {{
        if (memory_pointer_kind(node) != 1) {{
            if (record_observation && !scan->method_name_decode_failure_index)
                scan->method_name_decode_failure_reason = 4;
            return 0;
        }}
        if (!read_exact(
                node + scan->method_name_encoded_field_qword * 8u,
                &encoded,
                sizeof(encoded)
            )) {{
            if (record_observation && !scan->method_name_decode_failure_index)
                scan->method_name_decode_failure_reason = 5;
            return 0;
        }}
        value = (uintptr_t)(encoded ^ scan->method_name_xor_key);
    }}
    if (!value) {{
        if (!record_observation) return 0;
        alpha_lazy_name_initializer initialize =
            (alpha_lazy_name_initializer)scan->method_name_lazy_initializer;
        value = initialize(metadata_pointer);
        scan->method_name_lazy_initialization_count++;
    }}
    if (!value || memory_pointer_kind(value) != 1) {{
        if (record_observation && !scan->method_name_decode_failure_index)
            scan->method_name_decode_failure_reason = 6;
        return 0;
    }}
    alpha_method_name_length_helper read_length =
        (alpha_method_name_length_helper)scan->method_name_length_helper;
    alpha_method_name_string_helper create_string =
        (alpha_method_name_string_helper)
            scan->method_name_managed_string_helper;
    int32_t decoded_length = read_length(value);
    if (decoded_length <= 0 || decoded_length > 8192) {{
        if (record_observation && !scan->method_name_decode_failure_index)
            scan->method_name_decode_failure_reason = 8;
        return 0;
    }}
    uintptr_t managed_string = create_string(value, decoded_length);
    char *decoded = copy_runtime_managed_utf8(
        managed_string, scan->string_class, 0
    );
    if (!decoded) {{
        if (record_observation && !scan->method_name_decode_failure_index)
            scan->method_name_decode_failure_reason = 9;
        return 0;
    }}
    SIZE_T decoded_bytes = strlen(decoded);
    if (!decoded_bytes || decoded_bytes + 1u > capacity) {{
        free(decoded);
        if (record_observation && !scan->method_name_decode_failure_index)
            scan->method_name_decode_failure_reason = 10;
        return 0;
    }}
    memcpy(output, decoded, decoded_bytes + 1u);
    free(decoded);
    if (record_observation) {{
        scan->method_name_decode_success_count++;
        if (!scan->method_name_decode_failure_index)
            scan->method_name_decode_failure_reason = 0;
    }}
    return 1;
}}

static int runtime_method_name(
    alpha_reflection_scan *scan,
    uintptr_t metadata_pointer,
    char *output,
    SIZE_T capacity
) {{
    return runtime_method_name_internal(
        scan, metadata_pointer, output, capacity, 1
    );
}}

static int probe_runtime_method_name(
    alpha_reflection_scan *scan,
    uintptr_t metadata_pointer,
    char *output,
    SIZE_T capacity
) {{
    return runtime_method_name_internal(
        scan, metadata_pointer, output, capacity, 0
    );
}}

static int derive_method_parameter_count_field(
    alpha_reflection_scan *scan,
    alpha_method_record *methods,
    uint64_t method_count
) {{
    if (!scan || !methods || !method_count ||
        scan->semantic_operation_count !=
            ALPHA_NAME_OPERATION_COUNT +
            ALPHA_PARAMETER_FLAG_OPERATION_COUNT + 2u ||
        !scan->name_getters_semantically_unique ||
        !scan->parameter_type_getter_semantically_unique ||
        !scan->parameter_flag_getters_semantically_unique ||
        !scan->field_attributes_getter_semantically_unique ||
        scan->property_accessor_getter_candidate_count[1] != 1 ||
        !scan->property_accessor_getter_metadata[1] ||
        !scan->property_accessor_getter_pointer[1]) return 0;

    uintptr_t zero_arity_metadata[
        ALPHA_NAME_OPERATION_COUNT +
        ALPHA_PARAMETER_FLAG_OPERATION_COUNT + 2u
    ];
    uint32_t zero_arity_count = 0;
    for (uint32_t operation = 0;
         operation < ALPHA_NAME_OPERATION_COUNT;
         operation++) {{
        if (!scan->name_getter_metadata[operation]) return 0;
        zero_arity_metadata[zero_arity_count++] =
            scan->name_getter_metadata[operation];
    }}
    if (!scan->parameter_type_getter_metadata) return 0;
    zero_arity_metadata[zero_arity_count++] =
        scan->parameter_type_getter_metadata;
    for (uint32_t operation = 0;
         operation < ALPHA_PARAMETER_FLAG_OPERATION_COUNT;
         operation++) {{
        if (!scan->parameter_flag_getter_metadata[operation]) return 0;
        zero_arity_metadata[zero_arity_count++] =
            scan->parameter_flag_getter_metadata[operation];
    }}
    if (!scan->field_attributes_getter_metadata ||
        zero_arity_count >= sizeof(zero_arity_metadata) /
            sizeof(zero_arity_metadata[0])) return 0;
    zero_arity_metadata[zero_arity_count++] =
        scan->field_attributes_getter_metadata;
    if (zero_arity_count != sizeof(zero_arity_metadata) /
            sizeof(zero_arity_metadata[0])) return 0;

    for (uint32_t byte_offset = 0;
         byte_offset < ALPHA_METHOD_PARAMETER_SCAN_BYTES;
         byte_offset++) {{
        int candidate = 1;
        for (uint64_t method = 0; method < method_count; method++) {{
            unsigned char observed = 0;
            if (!read_exact(
                    methods[method].metadata_pointer + byte_offset,
                    &observed,
                    sizeof(observed)
                ) || observed > ALPHA_MAX_METHOD_PARAMETER_COUNT) {{
                candidate = 0;
                break;
            }}
        }}
        for (uint32_t seed = 0;
             seed < zero_arity_count && candidate;
             seed++) {{
            unsigned char observed = 0;
            if (!read_exact(
                    zero_arity_metadata[seed] + byte_offset,
                    &observed,
                    sizeof(observed)
                ) || observed != 0) candidate = 0;
        }}
        if (candidate) {{
            unsigned char observed = 0;
            if (!read_exact(
                    scan->property_accessor_getter_metadata[1] + byte_offset,
                    &observed,
                    sizeof(observed)
                ) || observed != 1) candidate = 0;
        }}
        if (!candidate) continue;
        scan->method_parameter_count_field_candidate_count++;
        if (scan->method_parameter_count_field_candidate_count == 1)
            scan->method_parameter_count_byte_offset = byte_offset;
    }}
    if (scan->method_parameter_count_field_candidate_count != 1) return 0;
    for (uint64_t method = 0; method < method_count; method++) {{
        unsigned char observed = 0;
        if (!read_exact(
                methods[method].metadata_pointer +
                    scan->method_parameter_count_byte_offset,
                &observed,
                sizeof(observed)
            ) || observed > ALPHA_MAX_METHOD_PARAMETER_COUNT) return 0;
        methods[method].parameter_count = observed;
    }}
    scan->method_parameter_count_field_semantically_unique = 1;
    scan->method_parameter_count_observation_complete = 1;
    return 1;
}}

static int exact_reflection_operation(
    const alpha_reflection_scan *scan,
    const char *key,
    uintptr_t *metadata_pointer,
    uintptr_t *method_pointer
) {{
    if (!scan || !key || !metadata_pointer || !method_pointer) return 0;
    for (uint32_t operation = 0;
         operation < required_reflection_operation_count;
         operation++) {{
        if (strcmp(required_reflection_operations[operation].key, key)) continue;
        if (scan->runtime_arity_operation_candidate_count[operation] != 1 ||
            !scan->runtime_arity_operation_metadata[operation] ||
            !scan->runtime_arity_operation_pointer[operation]) return 0;
        *metadata_pointer = scan->runtime_arity_operation_metadata[operation];
        *method_pointer = scan->runtime_arity_operation_pointer[operation];
        return 1;
    }}
    return 0;
}}

static int observe_runtime_method_names_on_managed_thread(
    alpha_reflection_scan *scan,
    alpha_method_record *methods,
    uint64_t method_count
);
static void write_runtime_method_name_diagnostic(
    const alpha_reflection_scan *scan,
    const alpha_method_record *methods,
    uint64_t method_count
);

static int discover_runtime_operation_names(
    alpha_reflection_scan *scan,
    alpha_method_record *methods,
    uint64_t method_count
) {{
    if (!scan || !methods || !method_count ||
        required_inventory_operation_count != ALPHA_INVENTORY_OPERATION_COUNT ||
        required_inventory_operation_candidate_count !=
            ALPHA_INVENTORY_OPERATION_CANDIDATE_COUNT ||
        !scan->method_parameter_count_field_semantically_unique ||
        !scan->method_parameter_count_observation_complete ||
        !derive_method_name_decoder(scan)) return 0;
    if (!observe_runtime_method_names_on_managed_thread(
            scan, methods, method_count
        )) return 0;
    write_runtime_method_name_diagnostic(scan, methods, method_count);
    if (scan->method_name_decode_attempt_count != method_count ||
        !scan->method_name_decode_success_count ||
        scan->method_name_decode_success_count > method_count) return 0;
    for (uint64_t method = 0; method < method_count; method++) {{
        for (uint32_t operation = 0;
             operation < required_reflection_operation_count;
             operation++) {{
            const alpha_required_operation *requirement =
                &required_reflection_operations[operation];
            uintptr_t owner_class = required_owner_class(
                scan, requirement->namespace_name, requirement->type_name
            );
            if (owner_class && methods[method].class_pointer == owner_class &&
                !strcmp(
                    methods[method].runtime_name,
                    requirement->runtime_name
                )) scan->runtime_named_operation_candidate_count[operation]++;
        }}
        for (uint32_t candidate = 0;
             candidate < required_inventory_operation_candidate_count;
             candidate++) {{
            const alpha_inventory_operation_candidate *requirement =
                &required_inventory_operation_candidates[candidate];
            if (requirement->operation_index >=
                    required_inventory_operation_count) return 0;
            uintptr_t owner_class = required_owner_class(
                scan, requirement->namespace_name, requirement->type_name
            );
            if (owner_class && methods[method].class_pointer == owner_class &&
                !strcmp(
                    methods[method].runtime_name,
                    requirement->runtime_name
                )) scan->inventory_named_operation_candidate_count[
                    requirement->operation_index
                ]++;
        }}
    }}
    for (uint32_t operation = 0;
         operation < required_reflection_operation_count;
         operation++) {{
        uint32_t count =
            scan->runtime_named_operation_candidate_count[operation];
        if (count) scan->runtime_named_operation_match_count++;
        if (count == 1) scan->runtime_named_operation_unique_count++;
    }}
    for (uint32_t operation = 0;
         operation < required_inventory_operation_count;
         operation++) {{
        if (scan->inventory_named_operation_candidate_count[operation])
            scan->inventory_named_operation_match_count++;
    }}
    if (scan->runtime_named_operation_match_count <
            scan->semantic_operation_count) return 0;
    for (uint64_t method = 0; method < method_count; method++) {{
        for (uint32_t operation = 0;
             operation < required_reflection_operation_count;
             operation++) {{
            const alpha_required_operation *requirement =
                &required_reflection_operations[operation];
            uintptr_t owner_class = required_owner_class(
                scan, requirement->namespace_name, requirement->type_name
            );
            if (!owner_class || methods[method].class_pointer != owner_class ||
                strcmp(
                    methods[method].runtime_name,
                    requirement->runtime_name
                )) continue;
            if (methods[method].parameter_count == requirement->parameter_count) {{
                uint32_t count =
                    ++scan->runtime_arity_operation_candidate_count[operation];
                if (count == 1) {{
                    scan->runtime_arity_operation_class[operation] =
                        methods[method].class_pointer;
                    scan->runtime_arity_operation_metadata[operation] =
                        methods[method].metadata_pointer;
                    scan->runtime_arity_operation_pointer[operation] =
                        methods[method].method_pointer;
                }} else {{
                    scan->runtime_arity_operation_class[operation] = 0;
                    scan->runtime_arity_operation_metadata[operation] = 0;
                    scan->runtime_arity_operation_pointer[operation] = 0;
                }}
            }}
        }}
        for (uint32_t candidate = 0;
             candidate < required_inventory_operation_candidate_count;
             candidate++) {{
            const alpha_inventory_operation_candidate *requirement =
                &required_inventory_operation_candidates[candidate];
            if (requirement->operation_index >=
                    required_inventory_operation_count) return 0;
            uintptr_t owner_class = required_owner_class(
                scan, requirement->namespace_name, requirement->type_name
            );
            if (!owner_class || methods[method].class_pointer != owner_class ||
                strcmp(
                    methods[method].runtime_name,
                    requirement->runtime_name
                )) continue;
            uint32_t operation = requirement->operation_index;
            if (methods[method].parameter_count == requirement->parameter_count) {{
                uint32_t count =
                    ++scan->inventory_arity_operation_candidate_count[operation];
                if (count == 1) {{
                    scan->inventory_arity_operation_class[operation] =
                        methods[method].class_pointer;
                    scan->inventory_arity_operation_metadata[operation] =
                        methods[method].metadata_pointer;
                    scan->inventory_arity_operation_pointer[operation] =
                        methods[method].method_pointer;
                }} else {{
                    scan->inventory_arity_operation_class[operation] = 0;
                    scan->inventory_arity_operation_metadata[operation] = 0;
                    scan->inventory_arity_operation_pointer[operation] = 0;
                }}
            }}
        }}
    }}
    for (uint32_t operation = 0;
         operation < required_reflection_operation_count;
         operation++) {{
        uint32_t count =
            scan->runtime_arity_operation_candidate_count[operation];
        if (count) scan->runtime_arity_operation_match_count++;
        if (count == 1 && scan->runtime_arity_operation_class[operation] &&
            scan->runtime_arity_operation_metadata[operation] &&
            scan->runtime_arity_operation_pointer[operation])
            scan->runtime_arity_operation_unique_count++;
    }}
    if (scan->runtime_named_operation_match_count <
            scan->semantic_operation_count ||
        scan->runtime_arity_operation_unique_count <
            scan->semantic_operation_count) return 0;
    scan->semantic_operation_count =
        scan->runtime_arity_operation_unique_count;
    scan->reflection_dispatch_contract_complete =
        scan->runtime_arity_operation_unique_count ==
        required_reflection_operation_count;
    if (!scan->reflection_dispatch_contract_complete ||
        !exact_reflection_operation(
            scan,
            "parameter.default_value",
            &scan->parameter_default_getter_metadata,
            &scan->parameter_default_getter_pointer
        ) || !exact_reflection_operation(
            scan,
            "property.getter",
            &scan->property_accessor_getter_metadata[0],
            &scan->property_accessor_getter_pointer[0]
        ) || !exact_reflection_operation(
            scan,
            "property.setter",
            &scan->property_accessor_getter_metadata[1],
            &scan->property_accessor_getter_pointer[1]
        )) return 0;
    scan->parameter_default_getter_candidate_count = 1;
    scan->parameter_default_getter_semantically_unique = 1;
    for (uint32_t accessor = 0;
         accessor < ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT;
         accessor++)
        scan->property_accessor_getter_candidate_count[accessor] = 1;
    scan->property_accessors_semantically_unique = 1;
    for (uint32_t operation = 0;
         operation < required_inventory_operation_count;
         operation++) {{
        uint32_t count =
            scan->inventory_arity_operation_candidate_count[operation];
        if (count) scan->inventory_arity_operation_match_count++;
        if (count == 1 && scan->inventory_arity_operation_class[operation] &&
            scan->inventory_arity_operation_metadata[operation] &&
            scan->inventory_arity_operation_pointer[operation])
            scan->inventory_arity_operation_unique_count++;
    }}
    scan->inventory_dispatch_contract_complete =
        scan->inventory_arity_operation_unique_count ==
        required_inventory_operation_count;
    return scan->reflection_dispatch_contract_complete &&
        scan->inventory_dispatch_contract_complete;
}}

static int discover_semantic_getters(
    alpha_reflection_scan *scan,
    alpha_method_record *methods,
    uint64_t method_count
) {{
    uintptr_t object_owner_classes[ALPHA_NAME_OPERATION_COUNT] = {{
        required_owner_class(scan, "System.Reflection", "MonoMethod"),
        required_owner_class(scan, "System.Reflection", "MonoField"),
        required_owner_class(scan, "System.Reflection", "MonoProperty"),
        required_owner_class(scan, "System.Reflection", "MonoParameterInfo")
    }};
    uintptr_t method_owner_classes[ALPHA_NAME_OPERATION_COUNT] = {{
        required_owner_class(scan, "System.Reflection", "MonoMethod"),
        required_owner_class(scan, "System.Reflection", "MonoField"),
        required_owner_class(scan, "System.Reflection", "MonoProperty"),
        required_owner_class(scan, "System.Reflection", "ParameterInfo")
    }};
    uintptr_t runtime_type_class =
        required_owner_class(scan, "System", "RuntimeType");
    static const unsigned char parameter_flag_masks[
        ALPHA_PARAMETER_FLAG_OPERATION_COUNT
    ] = {{0x01, 0x02, 0x10}};
    if (!scan || !methods || !method_count || !scan->string_class) return 0;
    for (uint32_t operation = 0;
         operation < ALPHA_NAME_OPERATION_COUNT;
         operation++) {{
        if (!object_owner_classes[operation] ||
            !method_owner_classes[operation]) return 0;
    }}
    if (!runtime_type_class || !scan->dbnull_class) return 0;
    for (uint64_t index = 0; index < method_count; index++) {{
        uint32_t byte_offset = 0;
        if (methods[index].class_pointer != object_owner_classes[1] ||
            !direct_dword_getter_shape(
                methods[index].method_pointer, &byte_offset
            )) continue;
        scan->field_attributes_getter_candidate_count++;
        scan->field_attributes_byte_offset = byte_offset;
        if (scan->field_attributes_getter_candidate_count == 1) {{
            scan->field_attributes_getter_metadata =
                methods[index].metadata_pointer;
            scan->field_attributes_getter_pointer = methods[index].method_pointer;
        }} else {{
            scan->field_attributes_getter_metadata = 0;
            scan->field_attributes_getter_pointer = 0;
        }}
    }}
    if (scan->field_attributes_getter_candidate_count != 1 ||
        !scan->field_attributes_getter_metadata ||
        !scan->field_attributes_getter_pointer) return 0;
    scan->field_attributes_getter_semantically_unique = 1;
    for (uint64_t index = 0; index < method_count; index++) {{
        uint32_t byte_offset = 0;
        unsigned char semantic_mask = 0;
        if (methods[index].class_pointer != method_owner_classes[3] ||
            !parameter_flag_getter_shape(
                methods[index].method_pointer,
                &byte_offset,
                &semantic_mask
            )) continue;
        for (uint32_t operation = 0;
             operation < ALPHA_PARAMETER_FLAG_OPERATION_COUNT;
             operation++) {{
            if (semantic_mask != parameter_flag_masks[operation]) continue;
            scan->parameter_flag_getter_candidate_count[operation]++;
            scan->parameter_flag_field_byte_offset[operation] = byte_offset;
            if (scan->parameter_flag_getter_candidate_count[operation] == 1) {{
                scan->parameter_flag_getter_metadata[operation] =
                    methods[index].metadata_pointer;
                scan->parameter_flag_getter_pointer[operation] =
                    methods[index].method_pointer;
            }} else {{
                scan->parameter_flag_getter_metadata[operation] = 0;
                scan->parameter_flag_getter_pointer[operation] = 0;
            }}
        }}
    }}
    for (uint32_t operation = 0;
         operation < ALPHA_PARAMETER_FLAG_OPERATION_COUNT;
         operation++) {{
        if (scan->parameter_flag_getter_candidate_count[operation] != 1 ||
            !scan->parameter_flag_getter_metadata[operation] ||
            !scan->parameter_flag_getter_pointer[operation] ||
            (operation && scan->parameter_flag_field_byte_offset[operation] !=
                scan->parameter_flag_field_byte_offset[0])) return 0;
    }}
    scan->parameter_flag_field_semantically_unique = 1;
    uint64_t field_support[ALPHA_NAME_OPERATION_COUNT][10] = {{0}};
    uint64_t parameter_type_field_support[10] = {{0}};
    uint64_t parameter_default_field_support[10] = {{0}};
    uint64_t property_accessor_field_support[
        ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT
    ][10] = {{0}};
    unsigned char *buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, ALPHA_SCAN_CHUNK
    );
    if (!buffer) return 0;
    SYSTEM_INFO system;
    GetSystemInfo(&system);
    uintptr_t cursor = (uintptr_t)system.lpMinimumApplicationAddress;
    uintptr_t maximum = (uintptr_t)system.lpMaximumApplicationAddress;
    while (cursor < maximum) {{
        MEMORY_BASIC_INFORMATION info;
        if (!VirtualQuery((const void *)cursor, &info, sizeof(info))) break;
        uintptr_t base = (uintptr_t)info.BaseAddress;
        uintptr_t next = base + info.RegionSize;
        if (next <= cursor) break;
        if (info.State == MEM_COMMIT && readable_protection(info.Protect)) {{
            uintptr_t position = base;
            while (position < next) {{
                SIZE_T amount = (SIZE_T)(next - position > ALPHA_SCAN_CHUNK
                    ? ALPHA_SCAN_CHUNK : next - position);
                if (read_exact(position, buffer, amount)) {{
                    SIZE_T aligned = (SIZE_T)((8u - (position & 7u)) & 7u);
                    for (SIZE_T offset = aligned;
                         offset + sizeof(uintptr_t) <= amount;
                         offset += sizeof(uintptr_t)) {{
                        uintptr_t value = 0;
                        memcpy(&value, buffer + offset, sizeof(value));
                        for (uint32_t operation = 0;
                             operation < ALPHA_NAME_OPERATION_COUNT;
                             operation++) {{
                            if (value != object_owner_classes[operation]) continue;
                            uintptr_t object = position + offset;
                            uintptr_t values[10];
                            if (!read_exact(object, values, sizeof(values)) ||
                                values[0] != object_owner_classes[operation]) continue;
                            scan->name_object_reference_count[operation]++;
                            int managed_string_observed = 0;
                            for (uint32_t field = 0; field < 10; field++) {{
                                if (runtime_managed_string(
                                        values[field], scan->string_class
                                    )) {{
                                    field_support[operation][field]++;
                                    managed_string_observed = 1;
                                }}
                                if (operation == 3 && runtime_object_has_class(
                                        values[field], runtime_type_class
                                    )) parameter_type_field_support[field]++;
                                if (operation == 3 && runtime_object_has_class(
                                        values[field], scan->dbnull_class
                                    )) parameter_default_field_support[field]++;
                            }}
                            if (operation == 1 && managed_string_observed) {{
                                uint32_t attributes = 0;
                                if (!read_exact(
                                        object + scan->field_attributes_byte_offset,
                                        &attributes,
                                        sizeof(attributes)
                                    )) continue;
                                if (!scan->field_attributes_object_reference_count) {{
                                    scan->field_attributes_first_value = attributes;
                                }} else if (attributes !=
                                           scan->field_attributes_first_value) {{
                                    scan->field_attributes_distinct_values_observed = 1;
                                }}
                                scan->field_attributes_object_reference_count++;
                                if (attributes > 0xffffu)
                                    scan->field_attributes_invalid_value_count++;
                            }}
                            if (operation == 2) {{
                                uintptr_t property_name = 0;
                                for (uint32_t name_field = 0;
                                     name_field < 10;
                                     name_field++) {{
                                    if (runtime_managed_string(
                                            values[name_field], scan->string_class
                                        )) {{
                                        property_name = values[name_field];
                                        break;
                                    }}
                                }}
                                if (property_name) {{
                                    scan->property_named_object_reference_count++;
                                    for (uint32_t member_field = 0;
                                         member_field < 10;
                                         member_field++) {{
                                        uintptr_t method_values[10];
                                        if (!values[member_field] ||
                                            !read_exact(
                                                values[member_field],
                                                method_values,
                                                sizeof(method_values)
                                            ) || method_values[0] !=
                                                object_owner_classes[0]) continue;
                                        int matched[
                                            ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT
                                        ] = {{0}};
                                        for (uint32_t method_name_field = 0;
                                             method_name_field < 10;
                                             method_name_field++) {{
                                            for (uint32_t accessor = 0;
                                                 accessor <
                                                    ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT;
                                                 accessor++) {{
                                                if (!matched[accessor] &&
                                                    runtime_accessor_name_matches(
                                                        property_name,
                                                        method_values[method_name_field],
                                                        scan->string_class,
                                                        accessor
                                                    )) matched[accessor] = 1;
                                            }}
                                        }}
                                        for (uint32_t accessor = 0;
                                             accessor <
                                                ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT;
                                             accessor++) {{
                                            if (matched[accessor])
                                                property_accessor_field_support[
                                                    accessor
                                                ][member_field]++;
                                        }}
                                    }}
                                }}
                            }}
                            if (operation == 3) {{
                                unsigned char attributes = 0;
                                if (!read_exact(
                                        object +
                                            scan->parameter_flag_field_byte_offset[0],
                                        &attributes,
                                        sizeof(attributes)
                                    )) continue;
                                scan->parameter_flag_object_reference_count++;
                                for (uint32_t flag = 0;
                                     flag < ALPHA_PARAMETER_FLAG_OPERATION_COUNT;
                                     flag++) {{
                                    if (attributes & parameter_flag_masks[flag])
                                        scan->parameter_flag_set_count[flag]++;
                                    else
                                        scan->parameter_flag_clear_count[flag]++;
                                }}
                            }}
                        }}
                    }}
                }}
                position += amount;
            }}
        }}
        cursor = next;
    }}
    HeapFree(GetProcessHeap(), 0, buffer);

    if (scan->parameter_flag_object_reference_count < 8) return 0;
    for (uint32_t operation = 0;
         operation < ALPHA_PARAMETER_FLAG_OPERATION_COUNT;
         operation++) {{
        if (!scan->parameter_flag_set_count[operation] ||
            !scan->parameter_flag_clear_count[operation]) return 0;
    }}
    scan->parameter_flag_observation_complete = 1;
    if (scan->field_attributes_object_reference_count < 8 ||
        scan->field_attributes_invalid_value_count ||
        !scan->field_attributes_distinct_values_observed) return 0;
    scan->field_attributes_observation_complete = 1;

    for (uint32_t operation = 0;
         operation < ALPHA_NAME_OPERATION_COUNT;
         operation++) {{
        if (!select_unique_supported_field(
                field_support[operation],
                &scan->cached_name_field_candidate_count[operation],
                &scan->cached_name_field_qword[operation],
                &scan->cached_name_field_support[operation],
                8u
            )) return 0;
        scan->cached_name_field_semantically_unique[operation] = 1;
    }}
    if (!select_unique_supported_field(
            parameter_type_field_support,
            &scan->parameter_type_field_candidate_count,
            &scan->parameter_type_field_qword,
            &scan->parameter_type_field_support,
            8u
        )) return 0;
    scan->parameter_type_field_semantically_unique = 1;
    if (!select_unique_supported_field(
            parameter_default_field_support,
            &scan->parameter_default_field_candidate_count,
            &scan->parameter_default_field_qword,
            &scan->parameter_default_field_support,
            8u
        )) return 0;
    scan->parameter_default_field_semantically_unique = 1;
    if (scan->property_named_object_reference_count < 8) return 0;
    for (uint32_t accessor = 0;
         accessor < ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT;
         accessor++) {{
        if (!select_unique_supported_field(
                property_accessor_field_support[accessor],
                &scan->property_accessor_field_candidate_count[accessor],
                &scan->property_accessor_field_qword[accessor],
                &scan->property_accessor_field_support[accessor],
                2u
            )) return 0;
        scan->property_accessor_field_semantically_unique[accessor] = 1;
    }}
    if (scan->property_accessor_field_qword[0] ==
        scan->property_accessor_field_qword[1]) return 0;

    for (uint64_t index = 0; index < method_count; index++) {{
        for (uint32_t operation = 0;
             operation < ALPHA_NAME_OPERATION_COUNT;
             operation++) {{
            if (methods[index].class_pointer != method_owner_classes[operation] ||
                !name_getter_shape(
                    operation,
                    methods[index].method_pointer,
                    scan->cached_name_field_qword[operation]
                )) continue;
            scan->name_getter_candidate_count[operation]++;
            if (scan->name_getter_candidate_count[operation] == 1) {{
                scan->name_getter_metadata[operation] =
                    methods[index].metadata_pointer;
                scan->name_getter_pointer[operation] = methods[index].method_pointer;
            }} else {{
                scan->name_getter_metadata[operation] = 0;
                scan->name_getter_pointer[operation] = 0;
            }}
        }}
        if (methods[index].class_pointer == method_owner_classes[3] &&
            code_directly_returns_name_field(
                methods[index].method_pointer,
                scan->parameter_type_field_qword
            )) {{
            scan->parameter_type_getter_candidate_count++;
            if (scan->parameter_type_getter_candidate_count == 1) {{
                scan->parameter_type_getter_metadata =
                    methods[index].metadata_pointer;
                scan->parameter_type_getter_pointer = methods[index].method_pointer;
            }} else {{
                scan->parameter_type_getter_metadata = 0;
                scan->parameter_type_getter_pointer = 0;
            }}
        }}
        if (methods[index].class_pointer == object_owner_classes[3] &&
            code_returns_rsi_field(
                methods[index].method_pointer,
                scan->parameter_default_field_qword
            )) {{
            scan->parameter_default_getter_candidate_count++;
            if (scan->parameter_default_getter_candidate_count == 1) {{
                scan->parameter_default_getter_metadata =
                    methods[index].metadata_pointer;
                scan->parameter_default_getter_pointer =
                    methods[index].method_pointer;
            }} else {{
                scan->parameter_default_getter_metadata = 0;
                scan->parameter_default_getter_pointer = 0;
            }}
        }}
        for (uint32_t accessor = 0;
             accessor < ALPHA_PROPERTY_ACCESSOR_OPERATION_COUNT;
             accessor++) {{
            if (methods[index].class_pointer != object_owner_classes[2] ||
                !property_accessor_getter_shape(
                    methods[index].method_pointer,
                    scan->property_accessor_field_qword[accessor]
                )) continue;
            scan->property_accessor_getter_candidate_count[accessor]++;
            if (scan->property_accessor_getter_candidate_count[accessor] == 1) {{
                scan->property_accessor_getter_metadata[accessor] =
                    methods[index].metadata_pointer;
                scan->property_accessor_getter_pointer[accessor] =
                    methods[index].method_pointer;
            }} else {{
                scan->property_accessor_getter_metadata[accessor] = 0;
                scan->property_accessor_getter_pointer[accessor] = 0;
            }}
        }}
    }}
    for (uint32_t operation = 0;
         operation < ALPHA_NAME_OPERATION_COUNT;
         operation++) {{
        if (scan->name_getter_candidate_count[operation] != 1 ||
            !scan->name_getter_metadata[operation] ||
            !scan->name_getter_pointer[operation]) return 0;
        scan->semantic_operation_count++;
    }}
    scan->name_getters_semantically_unique =
        scan->semantic_operation_count == ALPHA_NAME_OPERATION_COUNT;
    if (scan->parameter_type_getter_candidate_count != 1 ||
        !scan->parameter_type_getter_metadata ||
        !scan->parameter_type_getter_pointer) return 0;
    scan->parameter_type_getter_semantically_unique = 1;
    scan->semantic_operation_count++;
    scan->parameter_flag_getters_semantically_unique = 1;
    scan->semantic_operation_count += ALPHA_PARAMETER_FLAG_OPERATION_COUNT;
    scan->semantic_operation_count++;
    if (!derive_method_parameter_count_field(scan, methods, method_count))
        return 0;
    if (!discover_runtime_operation_names(scan, methods, method_count)) return 0;
    return scan->name_getters_semantically_unique &&
           scan->parameter_type_field_semantically_unique &&
           scan->parameter_type_getter_semantically_unique &&
           scan->parameter_flag_field_semantically_unique &&
           scan->parameter_flag_observation_complete &&
           scan->parameter_flag_getters_semantically_unique &&
           scan->parameter_default_field_semantically_unique &&
           scan->parameter_default_getter_semantically_unique &&
           scan->field_attributes_getter_semantically_unique &&
           scan->field_attributes_observation_complete &&
           scan->property_accessors_semantically_unique &&
           scan->method_name_decoder_derived &&
           scan->method_name_lazy_initializer_semantically_bound &&
           scan->method_parameter_count_field_semantically_unique &&
           scan->method_parameter_count_observation_complete;
}}

typedef uintptr_t (*alpha_type_resolver)(
    uintptr_t state,
    const char *namespace_name,
    const char *type_name
);

static int resolve_missing_required_owner_classes(
    alpha_reflection_scan *scan
) {{
    if (!scan || !scan->state_value || !scan->type_resolver_helper ||
        scan->distinct_type_resolver_helper_count != 1 ||
        !current_image_executable_pointer(scan->type_resolver_helper) ||
        scan->initialized_required_owner_count != expected_reflection_owner_count)
        return 0;
    alpha_type_resolver resolve =
        (alpha_type_resolver)scan->type_resolver_helper;
    for (uint32_t owner = 0;
         owner < required_reflection_owner_count;
         owner++) {{
        if (scan->required_owner_classes[owner]) continue;
        const alpha_required_owner *requirement =
            &required_reflection_owners[owner];
        uintptr_t value = resolve(
            scan->state_value,
            requirement->namespace_name,
            requirement->type_name
        );
        if (!value || memory_pointer_kind(value) != 1) return 0;
        scan->required_owner_classes[owner] = value;
        scan->dynamically_resolved_required_owner_count++;
    }}
    for (uint32_t owner = 0;
         owner < required_reflection_owner_count;
         owner++) {{
        if (!scan->required_owner_classes[owner]) return 0;
    }}
    scan->all_required_owner_classes_available = 1;
    return 1;
}}

static int scan_runtime_class_layout(alpha_reflection_scan *scan) {{
    if (!scan || !expected_reflection_owner_count ||
        required_reflection_owner_count > ALPHA_MAX_REFLECTION_OWNERS ||
        scan->initialized_required_owner_count != expected_reflection_owner_count ||
        !resolve_missing_required_owner_classes(scan))
        return 0;

    uintptr_t headers[ALPHA_MAX_REFLECTION_OWNERS][64];
    uint32_t owners[ALPHA_MAX_REFLECTION_OWNERS];
    uint32_t owner_count = 0;
    memset(headers, 0, sizeof(headers));
    memset(owners, 0, sizeof(owners));
    for (uint32_t index = 0; index < required_reflection_owner_count; index++) {{
        uintptr_t class_pointer = scan->required_owner_classes[index];
        if (owner_count >= ALPHA_MAX_REFLECTION_OWNERS ||
            memory_pointer_kind(class_pointer) != 1 ||
            !read_exact(
                class_pointer,
                headers[owner_count],
                sizeof(headers[owner_count])
            )) return 0;
        owners[owner_count++] = index;
    }}
    if (owner_count != required_reflection_owner_count) return 0;
    uint32_t layout_owner_count = 0;
    for (uint32_t owner = 0; owner < owner_count; owner++) {{
        if (required_reflection_owners[owners[owner]].layout_participant)
            layout_owner_count++;
    }}
    if (!layout_owner_count) return 0;

    for (uint32_t qword = 0; qword < 64u - 8u; qword++) {{
        int candidate = 1;
        for (uint32_t owner = 0; owner < owner_count && candidate; owner++) {{
            if (!required_reflection_owners[owners[owner]].layout_participant)
                continue;
            if (memory_pointer_kind(headers[owner][qword]) != 2) {{
                candidate = 0;
                break;
            }}
            uint32_t executable = 0;
            for (uint32_t delta = 0; delta < 8; delta++) {{
                if (memory_pointer_kind(headers[owner][qword + delta]) == 2)
                    executable++;
            }}
            /*
             * Il2CppClass::vtable is versioned implementation data.  Some
             * builds store a dense run of callable pointers, while others
             * expose standard VirtualInvokeData pairs (method pointer,
             * MethodInfo pointer).  Eight qwords therefore contain either
             * roughly eight or four executable values.  Three is the
             * fail-closed lower bound that still tolerates one null abstract
             * slot without baking either representation into the dumper.
             * The independent method-array/count proof below remains the
             * actual layout selector.
             */
            if (executable < 3) candidate = 0;
        }}
        if (candidate) {{
            scan->vtable_candidate_count++;
            if (scan->vtable_candidate_count == 1)
                scan->vtable_start_qword = qword;
        }}
    }}
    if (!scan->vtable_candidate_count) return 0;

    uint16_t selected_counts[ALPHA_MAX_REFLECTION_OWNERS];
    memset(selected_counts, 0, sizeof(selected_counts));
    uint32_t header_bytes = scan->vtable_start_qword * sizeof(uintptr_t);
    for (uint32_t pointer_qword = 0;
         pointer_qword < scan->vtable_start_qword;
         pointer_qword++) {{
        int pointer_field = 1;
        for (uint32_t owner = 0; owner < owner_count; owner++) {{
            if (!required_reflection_owners[owners[owner]].layout_participant)
                continue;
            if (memory_pointer_kind(headers[owner][pointer_qword]) != 1) {{
                pointer_field = 0;
                break;
            }}
        }}
        if (!pointer_field) continue;
        for (uint32_t count_offset = 0;
             count_offset + sizeof(uint16_t) <= header_bytes;
             count_offset += sizeof(uint16_t)) {{
            int eligible = 1;
            uint16_t counts[ALPHA_MAX_REFLECTION_OWNERS];
            memset(counts, 0, sizeof(counts));
            for (uint32_t owner = 0; owner < owner_count; owner++) {{
                if (!required_reflection_owners[owners[owner]].layout_participant)
                    continue;
                uint16_t count = 0;
                memcpy(
                    &count,
                    ((const unsigned char *)headers[owner]) + count_offset,
                    sizeof(count)
                );
                const alpha_required_owner *requirement =
                    &required_reflection_owners[owners[owner]];
                if (!count || count > 4096 ||
                    count < requirement->minimum_method_count ||
                    !method_array_is_metadata(
                        headers[owner][pointer_qword], count
                    )) {{
                    eligible = 0;
                    break;
                }}
                counts[owner] = count;
            }}
            if (!eligible) continue;
            scan->method_layout_candidate_count++;
            if (scan->method_layout_candidate_count == 1) {{
                scan->method_array_pointer_qword = pointer_qword;
                scan->method_count_byte_offset = count_offset;
                memcpy(selected_counts, counts, sizeof(selected_counts));
            }}
        }}
    }}
    if (scan->method_layout_candidate_count != 1) return 0;
    for (uint32_t owner = 0; owner < owner_count; owner++) {{
        const alpha_required_owner *requirement =
            &required_reflection_owners[owners[owner]];
        if (requirement->layout_participant) continue;
        uint16_t count = 0;
        memcpy(
            &count,
            ((const unsigned char *)headers[owner]) +
                scan->method_count_byte_offset,
            sizeof(count)
        );
        if (!count || count > 4096 ||
            count < requirement->minimum_method_count ||
            !method_array_is_metadata(
                headers[owner][scan->method_array_pointer_qword], count
            )) return 0;
        selected_counts[owner] = count;
    }}

    uint64_t method_count = 0;
    for (uint32_t owner = 0; owner < owner_count; owner++) {{
        method_count += selected_counts[owner];
    }}
    if (!method_count || method_count > ALPHA_MAX_REFLECTION_METHODS) return 0;
    alpha_method_record *methods = (alpha_method_record *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY,
        (SIZE_T)method_count * sizeof(*methods)
    );
    if (!methods) return 0;

    uint64_t method_index = 0;
    for (uint32_t owner = 0; owner < owner_count; owner++) {{
        uintptr_t array_pointer =
            headers[owner][scan->method_array_pointer_qword];
        uintptr_t class_pointer =
            scan->required_owner_classes[owners[owner]];
        for (uint32_t index = 0; index < selected_counts[owner]; index++) {{
            uintptr_t metadata_pointer = 0;
            if (index > (UINTPTR_MAX - array_pointer) / sizeof(uintptr_t) ||
                !read_exact(
                    array_pointer + index * sizeof(uintptr_t),
                    &metadata_pointer,
                    sizeof(metadata_pointer)
                ) || memory_pointer_kind(metadata_pointer) != 1) {{
                HeapFree(GetProcessHeap(), 0, methods);
                return 0;
            }}
            methods[method_index].metadata_pointer = metadata_pointer;
            methods[method_index].class_pointer = class_pointer;
            method_index++;
        }}
    }}
    scan->method_record_count = method_count;

    for (uint32_t field = 0; field < 32; field++) {{
        int candidate = 1;
        for (uint64_t index = 0; index < method_count; index++) {{
            uintptr_t value = 0;
            uintptr_t pointer = methods[index].metadata_pointer;
            if (field > (UINTPTR_MAX - pointer) / sizeof(uintptr_t) ||
                !read_exact(
                    pointer + field * sizeof(uintptr_t),
                    &value,
                    sizeof(value)
                ) || value != methods[index].class_pointer) {{
                candidate = 0;
                break;
            }}
        }}
        if (candidate) {{
            scan->declaring_class_candidate_count++;
            if (scan->declaring_class_candidate_count == 1)
                scan->declaring_class_qword = field;
        }}
    }}
    if (scan->declaring_class_candidate_count != 1) {{
        HeapFree(GetProcessHeap(), 0, methods);
        return 0;
    }}

    for (uint32_t field = 0; field < scan->declaring_class_qword; field++) {{
        uint64_t executable = 0;
        int candidate = 1;
        for (uint64_t index = 0; index < method_count; index++) {{
            uintptr_t value = 0;
            uintptr_t pointer = methods[index].metadata_pointer;
            if (field > (UINTPTR_MAX - pointer) / sizeof(uintptr_t) ||
                !read_exact(
                    pointer + field * sizeof(uintptr_t),
                    &value,
                    sizeof(value)
                )) {{
                candidate = 0;
                break;
            }}
            if (!value) continue;
            if (memory_pointer_kind(value) != 2) {{
                candidate = 0;
                break;
            }}
            executable++;
        }}
        if (candidate &&
            executable >= method_count * 4u / 5u) {{
            scan->method_pointer_candidate_count++;
            if (scan->method_pointer_candidate_count == 1) {{
                scan->method_pointer_qword = field;
                scan->executable_method_pointer_count = executable;
            }}
        }}
    }}
    if (scan->method_pointer_candidate_count != 1) {{
        HeapFree(GetProcessHeap(), 0, methods);
        return 0;
    }}
    for (uint64_t index = 0; index < method_count; index++) {{
        uintptr_t pointer = methods[index].metadata_pointer;
        if (scan->method_pointer_qword >
                (UINTPTR_MAX - pointer) / sizeof(uintptr_t) ||
            !read_exact(
                pointer + scan->method_pointer_qword * sizeof(uintptr_t),
                &methods[index].method_pointer,
                sizeof(methods[index].method_pointer)
            ) || (methods[index].method_pointer &&
                  memory_pointer_kind(methods[index].method_pointer) != 2)) {{
            HeapFree(GetProcessHeap(), 0, methods);
            return 0;
        }}
    }}
    if (!discover_semantic_getters(scan, methods, method_count)) {{
        HeapFree(GetProcessHeap(), 0, methods);
        return 0;
    }}
    HeapFree(GetProcessHeap(), 0, methods);
    scan->observed_class_layout_complete = 1;
    return 1;
}}

static int scan_runtime_reflection(
    const alpha_resolver_scan *resolver,
    alpha_reflection_scan *scan
) {{
    memset(scan, 0, sizeof(*scan));
    unsigned char *base = (unsigned char *)GetModuleHandleW(NULL);
    if (!base || !resolver || !resolver->selected_call) return 0;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)base;
    if (dos->e_magic != IMAGE_DOS_SIGNATURE || dos->e_lfanew <= 0) return 0;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(base + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE ||
        nt->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC) return 0;
    IMAGE_SECTION_HEADER *sections = IMAGE_FIRST_SECTION(nt);
    WORD section_count = nt->FileHeader.NumberOfSections;
    uint64_t image_size = nt->OptionalHeader.SizeOfImage;

    if (expected_reflection_state_slot_rva) {{
        if (expected_reflection_state_slot_rva >= image_size) return 0;
        scan->state_slot = (uintptr_t)base +
            (uintptr_t)expected_reflection_state_slot_rva;
    }} else {{
        const unsigned char *cursor =
            (const unsigned char *)resolver->selected_call + 5;
        const unsigned char *limit = cursor + 64;
        if (cursor + 10 <= limit && cursor[0] >= 0x48 &&
            cursor[0] <= 0x4f && cursor[1] >= 0xb8 && cursor[1] <= 0xbf)
            cursor += 10;
        int load_length = rax_load_length(cursor, limit);
        if (!load_length) return 0;
        cursor += load_length;
        if (cursor + 3 > limit || cursor[0] < 0x48 || cursor[0] > 0x4f ||
            (cursor[1] != 0x01 && cursor[1] != 0x03)) return 0;
        cursor += 3;
        if (cursor + 7 > limit || cursor[0] < 0x40 || cursor[0] > 0x4f ||
            cursor[1] != 0x89 || (cursor[2] & 0xc7u) != 0x05) return 0;
        int32_t state_displacement = 0;
        memcpy(&state_displacement, cursor + 3, sizeof(state_displacement));
        scan->state_slot =
            (uintptr_t)(cursor + 7) + (intptr_t)state_displacement;
    }}
    if (scan->state_slot < (uintptr_t)base ||
        scan->state_slot - (uintptr_t)base >= image_size ||
        rva_in_executable_section(
            sections, section_count,
            (uint32_t)(scan->state_slot - (uintptr_t)base)
        ) || !read_exact(scan->state_slot, &scan->state_value, sizeof(uintptr_t)) ||
        !scan->state_value) return 0;

    for (WORD section_index = 0; section_index < section_count; section_index++) {{
        const IMAGE_SECTION_HEADER *section = &sections[section_index];
        if (!(section->Characteristics & IMAGE_SCN_MEM_EXECUTE)) continue;
        uint64_t extent = section_extent(section);
        uint64_t section_rva = section->VirtualAddress;
        if (!extent || section_rva + extent > image_size) continue;
        const unsigned char *bytes = base + section_rva;
        for (uint64_t offset = 0; offset + 33 <= extent; offset++) {{
            const unsigned char *site = bytes + offset;
            if (memcmp(site, "\x48\x8b\x0d", 3) ||
                memcmp(site + 7, "\x48\x8d\x15", 3) ||
                memcmp(site + 14, "\x4c\x8d\x05", 3)) continue;
            int32_t state_reference = 0, namespace_reference = 0, type_reference = 0;
            memcpy(&state_reference, site + 3, 4);
            memcpy(&namespace_reference, site + 10, 4);
            memcpy(&type_reference, site + 17, 4);
            if ((uintptr_t)(site + 7) + (intptr_t)state_reference != scan->state_slot)
                continue;
            uintptr_t namespace_value =
                (uintptr_t)(site + 14) + (intptr_t)namespace_reference;
            uintptr_t type_value = (uintptr_t)(site + 21) + (intptr_t)type_reference;
            if (!semantic_image_string(base, image_size, namespace_value) ||
                !semantic_image_string(base, image_size, type_value)) continue;
            const unsigned char *call = NULL;
            for (uint64_t delta = 21; delta <= 37 && offset + delta + 12 <= extent; delta++) {{
                const unsigned char *candidate = site + delta;
                if (candidate[0] == 0xe8 && candidate[5] == 0x48 &&
                    candidate[6] == 0x89 && (candidate[7] & 0xc7u) == 0x05) {{
                    call = candidate;
                    break;
                }}
            }}
            if (!call) continue;
            int32_t call_displacement = 0, result_displacement = 0;
            memcpy(&call_displacement, call + 1, 4);
            memcpy(&result_displacement, call + 8, 4);
            uintptr_t helper = (uintptr_t)(call + 5) + (intptr_t)call_displacement;
            uintptr_t result_slot = (uintptr_t)(call + 12) + (intptr_t)result_displacement;
            if (helper < (uintptr_t)base || helper - (uintptr_t)base >= image_size ||
                !rva_in_executable_section(
                    sections, section_count,
                    (uint32_t)(helper - (uintptr_t)base)
                ) || result_slot < (uintptr_t)base ||
                result_slot - (uintptr_t)base >= image_size ||
                rva_in_executable_section(
                    sections, section_count,
                    (uint32_t)(result_slot - (uintptr_t)base)
                )) continue;
            scan->type_cache_count++;
            uintptr_t initialized_value = 0;
            if (read_exact(result_slot, &initialized_value, sizeof(initialized_value)) &&
                initialized_value) {{
                scan->initialized_type_cache_count++;
                if (!strcmp((const char *)namespace_value, "System") &&
                    !strcmp((const char *)type_value, "String")) {{
                    if (memory_pointer_kind(initialized_value) != 1 ||
                        (scan->string_class &&
                         scan->string_class != initialized_value)) return 0;
                    scan->string_class = initialized_value;
                }}
                if (!strcmp((const char *)namespace_value, "System") &&
                    !strcmp((const char *)type_value, "DBNull")) {{
                    if (memory_pointer_kind(initialized_value) != 1 ||
                        (scan->dbnull_class &&
                         scan->dbnull_class != initialized_value)) return 0;
                    scan->dbnull_class = initialized_value;
                }}
                for (uint32_t owner = 0;
                     owner < required_reflection_owner_count;
                     owner++) {{
                    const alpha_required_owner *requirement =
                        &required_reflection_owners[owner];
                    if (!requirement->expected_cache ||
                        strcmp(
                            (const char *)namespace_value,
                            requirement->namespace_name
                        ) || strcmp(
                            (const char *)type_value,
                            requirement->type_name
                        )) continue;
                    if (memory_pointer_kind(initialized_value) != 1) return 0;
                    if (scan->required_owner_classes[owner] &&
                        scan->required_owner_classes[owner] != initialized_value)
                        return 0;
                    if (!scan->required_owner_classes[owner]) {{
                        scan->required_owner_classes[owner] = initialized_value;
                        scan->initialized_required_owner_count++;
                    }}
                }}
            }}
            if (!scan->type_resolver_helper) {{
                scan->type_resolver_helper = helper;
                scan->distinct_type_resolver_helper_count = 1;
            }} else if (scan->type_resolver_helper != helper) {{
                scan->distinct_type_resolver_helper_count = 2;
            }}
        }}
    }}
    if (!scan->type_cache_count ||
        scan->distinct_type_resolver_helper_count != 1 ||
        (expected_reflection_type_cache_count &&
         scan->type_cache_count != expected_reflection_type_cache_count)) return 0;
    return scan_runtime_class_layout(scan);
}}

static int wait_runtime_reflection(
    const alpha_resolver_scan *resolver,
    alpha_reflection_scan *scan
) {{
    if (!resolver || !scan) return 0;
    ULONGLONG started = GetTickCount64();
    const ULONGLONG timeout = 60000;
    uint32_t attempts = 0;
    for (;;) {{
        attempts++;
        if (scan_runtime_reflection(resolver, scan)) {{
            scan->bootstrap_attempt_count = attempts;
            scan->bootstrap_wait_milliseconds = GetTickCount64() - started;
            return 1;
        }}
        ULONGLONG elapsed = GetTickCount64() - started;
        if (elapsed >= timeout) {{
            scan->bootstrap_attempt_count = attempts;
            scan->bootstrap_wait_milliseconds = elapsed;
            return 0;
        }}
        Sleep(250);
    }}
}}

static void digest_hex(const unsigned char digest[32], char output[65]) {{
    static const char alphabet[] = "0123456789abcdef";
    for (int index = 0; index < 32; index++) {{
        output[index * 2] = alphabet[digest[index] >> 4];
        output[index * 2 + 1] = alphabet[digest[index] & 15];
    }}
    output[64] = 0;
}}

static int hash_begin(
    BCRYPT_ALG_HANDLE *algorithm,
    BCRYPT_HASH_HANDLE *hash,
    unsigned char **object
) {{
    DWORD object_size = 0, received = 0;
    if (BCryptOpenAlgorithmProvider(
            algorithm, BCRYPT_SHA256_ALGORITHM, NULL, 0
        ) < 0) return 0;
    if (BCryptGetProperty(
            *algorithm, BCRYPT_OBJECT_LENGTH,
            (PUCHAR)&object_size, sizeof(object_size), &received, 0
        ) < 0 || !object_size) {{
        BCryptCloseAlgorithmProvider(*algorithm, 0);
        return 0;
    }}
    *object = (unsigned char *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, object_size
    );
    if (!*object || BCryptCreateHash(
            *algorithm, hash, *object, object_size, NULL, 0, 0
        ) < 0) {{
        if (*object) HeapFree(GetProcessHeap(), 0, *object);
        BCryptCloseAlgorithmProvider(*algorithm, 0);
        return 0;
    }}
    return 1;
}}

static void hash_end(
    BCRYPT_ALG_HANDLE algorithm,
    BCRYPT_HASH_HANDLE hash,
    unsigned char *object
) {{
    if (hash) BCryptDestroyHash(hash);
    if (object) HeapFree(GetProcessHeap(), 0, object);
    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);
}}

static int sha256_file(const wchar_t *path, char output[65]) {{
    HANDLE input = CreateFileW(
        path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (input == INVALID_HANDLE_VALUE) return 0;
    BCRYPT_ALG_HANDLE algorithm = NULL;
    BCRYPT_HASH_HANDLE hash = NULL;
    unsigned char *object = NULL;
    unsigned char *buffer = NULL;
    unsigned char digest[32];
    int ok = hash_begin(&algorithm, &hash, &object);
    if (ok) buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, ALPHA_SCAN_CHUNK
    );
    if (!buffer) ok = 0;
    while (ok) {{
        DWORD received = 0;
        if (!ReadFile(input, buffer, ALPHA_SCAN_CHUNK, &received, NULL)) {{
            ok = 0;
            break;
        }}
        if (!received) break;
        if (BCryptHashData(hash, buffer, received, 0) < 0) ok = 0;
    }}
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) >= 0) {{
        digest_hex(digest, output);
    }} else {{
        ok = 0;
    }}
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    hash_end(algorithm, hash, object);
    CloseHandle(input);
    return ok;
}}

static int sha256_memory(uintptr_t address, uint64_t size, char output[65]) {{
    BCRYPT_ALG_HANDLE algorithm = NULL;
    BCRYPT_HASH_HANDLE hash = NULL;
    unsigned char *object = NULL;
    unsigned char *buffer = NULL;
    unsigned char digest[32];
    int ok = hash_begin(&algorithm, &hash, &object);
    if (ok) buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, ALPHA_SCAN_CHUNK
    );
    if (!buffer) ok = 0;
    uint64_t position = 0;
    while (ok && position < size) {{
        DWORD amount = (DWORD)(size - position > ALPHA_SCAN_CHUNK
            ? ALPHA_SCAN_CHUNK : size - position);
        if (!read_exact(address + (uintptr_t)position, buffer, amount) ||
            BCryptHashData(hash, buffer, amount, 0) < 0) {{
            ok = 0;
            break;
        }}
        position += amount;
    }}
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) >= 0) {{
        digest_hex(digest, output);
    }} else {{
        ok = 0;
    }}
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    hash_end(algorithm, hash, object);
    return ok;
}}

static int validate_metadata(uintptr_t address, alpha_candidate *candidate) {{
    unsigned char fixed[16];
    if (!read_exact(address, fixed, sizeof(fixed))) return 0;
    if (rd32(fixed) != 0xfab11bafu) return 0;
    uint32_t version = rd32(fixed + 4);
    uint32_t header_size = rd32(fixed + 8);
    if (!version ||
        header_size < 0x80 || header_size > ALPHA_MAX_HEADER ||
        ((header_size - 8) & 7u)) return 0;
    unsigned char header[ALPHA_MAX_HEADER];
    if (!read_exact(address, header, header_size)) return 0;
    uint32_t pair_count = (header_size - 8) / 8;
    uint32_t nonempty = 0;
    uint64_t previous_end = header_size;
    uint64_t extent = header_size;
    for (uint32_t pair = 0; pair < pair_count; pair++) {{
        uint32_t offset = rd32(header + 8 + pair * 8);
        uint32_t size = rd32(header + 12 + pair * 8);
        if (!offset && !size) continue;
        if (!offset || offset < header_size ||
            (uint64_t)offset + size < offset ||
            (uint64_t)offset + size > ALPHA_MAX_METADATA) return 0;
        if (nonempty && offset != previous_end) return 0;
        if (!nonempty && offset != header_size) return 0;
        previous_end = (uint64_t)offset + size;
        if (previous_end > extent) extent = previous_end;
        nonempty++;
    }}
    if (nonempty < 16 || extent < 1024 * 1024 || extent > ALPHA_MAX_METADATA) return 0;
    candidate->address = address;
    candidate->extent = extent;
    candidate->table_pairs = pair_count;
    candidate->sha256[0] = 0;
    return 1;
}}

static int candidate_seen(const alpha_scan *scan, uintptr_t address) {{
    for (int index = 0; index < scan->count; index++) {{
        if (scan->values[index].address == address) return 1;
    }}
    return 0;
}}

static int scan_runtime(alpha_scan *scan) {{
    memset(scan, 0, sizeof(*scan));
    SYSTEM_INFO system_info;
    GetSystemInfo(&system_info);
    uintptr_t cursor = (uintptr_t)system_info.lpMinimumApplicationAddress;
    uintptr_t maximum = (uintptr_t)system_info.lpMaximumApplicationAddress;
    unsigned char *buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, ALPHA_SCAN_CHUNK + 3
    );
    if (!buffer) return 0;
    while (cursor < maximum) {{
        MEMORY_BASIC_INFORMATION region;
        SIZE_T queried = VirtualQuery((const void *)cursor, &region, sizeof(region));
        if (!queried) break;
        uintptr_t base = (uintptr_t)region.BaseAddress;
        uintptr_t end = base + (uintptr_t)region.RegionSize;
        if (end <= base) break;
        if (region.State == MEM_COMMIT && readable_protection(region.Protect)) {{
            scan->regions++;
            uintptr_t position = base;
            while (position < end) {{
                SIZE_T amount = end - position > ALPHA_SCAN_CHUNK
                    ? ALPHA_SCAN_CHUNK : (SIZE_T)(end - position);
                SIZE_T received = 0;
                if (ReadProcessMemory(
                        GetCurrentProcess(), (const void *)position,
                        buffer, amount, &received
                    ) && received >= 4) {{
                    scan->bytes += received;
                    SIZE_T offset = 0;
                    while (offset + 4 <= received) {{
                        unsigned char *hit = (unsigned char *)memchr(
                            buffer + offset, 0xaf, received - offset - 3
                        );
                        if (!hit) break;
                        offset = (SIZE_T)(hit - buffer);
                        if (buffer[offset + 1] == 0x1b &&
                            buffer[offset + 2] == 0xb1 &&
                            buffer[offset + 3] == 0xfa) {{
                            uintptr_t address = position + offset;
                            alpha_candidate candidate;
                            if (!candidate_seen(scan, address) &&
                                validate_metadata(address, &candidate)) {{
                                if (scan->count < ALPHA_MAX_CANDIDATES) {{
                                    scan->values[scan->count++] = candidate;
                                }} else {{
                                    scan->overflow = 1;
                                }}
                            }}
                        }}
                        offset++;
                    }}
                }}
                if (position + amount <= position) break;
                if (position + amount < end && amount > 3) {{
                    position += amount - 3;
                }} else {{
                    position += amount;
                }}
            }}
        }}
        cursor = end;
    }}
    HeapFree(GetProcessHeap(), 0, buffer);
    for (int index = 0; index < scan->count; index++) {{
        if (!sha256_memory(
                scan->values[index].address,
                scan->values[index].extent,
                scan->values[index].sha256
            )) return 0;
    }}
    return !scan->overflow;
}}

static int distinct_identities(const alpha_scan *scan) {{
    int distinct = 0;
    for (int index = 0; index < scan->count; index++) {{
        int earlier = 0;
        for (int previous = 0; previous < index; previous++) {{
            if (scan->values[index].extent == scan->values[previous].extent &&
                !strcmp(scan->values[index].sha256, scan->values[previous].sha256)) {{
                earlier = 1;
                break;
            }}
        }}
        if (!earlier) distinct++;
    }}
    return distinct;
}}

static const alpha_candidate *unique_identity(const alpha_scan *scan) {{
    if (distinct_identities(scan) != 1 || scan->count < 1) return NULL;
    return &scan->values[0];
}}

static int metadata_tables(
    const alpha_candidate *candidate,
    alpha_metadata_table tables[ALPHA_MAX_METADATA_TABLE_PAIRS],
    uint32_t *table_count
) {{
    unsigned char header[ALPHA_MAX_HEADER];
    if (!candidate || !table_count || !candidate->address ||
        !candidate->table_pairs ||
        candidate->table_pairs > ALPHA_MAX_METADATA_TABLE_PAIRS ||
        !read_exact(candidate->address, header, 16)) return 0;
    uint32_t header_bytes = rd32(header + 8);
    if (header_bytes < 0x80u || header_bytes > ALPHA_MAX_HEADER ||
        (header_bytes - 8u) / 8u != candidate->table_pairs ||
        !read_exact(candidate->address, header, header_bytes)) return 0;
    uint32_t count = 0;
    for (uint32_t pair = 0; pair < candidate->table_pairs; pair++) {{
        uint32_t offset = rd32(header + 8u + pair * 8u);
        uint32_t bytes = rd32(header + 12u + pair * 8u);
        if (!offset && !bytes) continue;
        if (!offset || (uint64_t)offset + bytes > candidate->extent ||
            count >= ALPHA_MAX_METADATA_TABLE_PAIRS) return 0;
        tables[count].pair_index = pair;
        tables[count].offset = offset;
        tables[count].bytes = bytes;
        count++;
    }}
    if (count < 16u) return 0;
    *table_count = count;
    return 1;
}}

static int metadata_utf8_valid(const unsigned char *value, uint32_t bytes) {{
    if (!value && bytes) return 0;
    uint32_t index = 0;
    while (index < bytes) {{
        unsigned char first = value[index++];
        if (first < 0x80u) continue;
        uint32_t continuation = 0;
        uint32_t codepoint = 0;
        uint32_t minimum = 0;
        if (first >= 0xc2u && first <= 0xdfu) {{
            continuation = 1u;
            codepoint = first & 0x1fu;
            minimum = 0x80u;
        }} else if (first >= 0xe0u && first <= 0xefu) {{
            continuation = 2u;
            codepoint = first & 0x0fu;
            minimum = 0x800u;
        }} else if (first >= 0xf0u && first <= 0xf4u) {{
            continuation = 3u;
            codepoint = first & 0x07u;
            minimum = 0x10000u;
        }} else return 0;
        if (continuation > bytes - index) return 0;
        for (uint32_t part = 0; part < continuation; part++) {{
            unsigned char next = value[index++];
            if ((next & 0xc0u) != 0x80u) return 0;
            codepoint = (codepoint << 6u) | (next & 0x3fu);
        }}
        if (codepoint < minimum || codepoint > 0x10ffffu ||
            (codepoint >= 0xd800u && codepoint <= 0xdfffu)) return 0;
    }}
    return 1;
}}

static int discover_metadata_string_literal_count(
    const alpha_candidate *candidate,
    const alpha_metadata_table *tables,
    uint32_t table_count,
    uint64_t *literal_count
) {{
    if (!candidate || !tables || !table_count || !literal_count) return 0;
    uint32_t matches = 0;
    uint64_t selected_count = 0;
    for (uint32_t record_table_index = 0;
         record_table_index < table_count; record_table_index++) {{
        const alpha_metadata_table *record_table =
            &tables[record_table_index];
        for (uint32_t stride = 8u; stride <= ALPHA_MAX_DEFINITION_STRIDE;
             stride += 4u) {{
            if (record_table->bytes % stride) continue;
            uint64_t count = record_table->bytes / stride;
            if (!count) continue;
            uint32_t dwords = stride / 4u;
            const unsigned char *records =
                (const unsigned char *)(candidate->address + record_table->offset);
            for (uint32_t length_dword = 0; length_dword < dwords;
                 length_dword++) {{
                for (uint32_t index_dword = 0; index_dword < dwords;
                     index_dword++) {{
                    if (index_dword == length_dword ||
                        rd32(records + index_dword * 4u) != 0u) continue;
                    const unsigned char *last = records + (count - 1u) * stride;
                    uint32_t last_length = rd32(last + length_dword * 4u);
                    uint32_t last_index = rd32(last + index_dword * 4u);
                    uint64_t final_extent =
                        (uint64_t)last_index + last_length;
                    if (final_extent > UINT32_MAX) continue;
                    for (uint32_t data_table_index = 0;
                         data_table_index < table_count; data_table_index++) {{
                        if (data_table_index == record_table_index) continue;
                        const alpha_metadata_table *data_table =
                            &tables[data_table_index];
                        if (final_extent != data_table->bytes) continue;
                        uint64_t cursor = 0;
                        int valid = 1;
                        for (uint64_t index = 0; index < count; index++) {{
                            const unsigned char *record = records + index * stride;
                            uint32_t length = rd32(record + length_dword * 4u);
                            uint32_t data_index = rd32(record + index_dword * 4u);
                            if (data_index != cursor ||
                                length > data_table->bytes - cursor) {{
                                valid = 0;
                                break;
                            }}
                            cursor += length;
                        }}
                        const unsigned char *literal_data =
                            (const unsigned char *)(
                                candidate->address + data_table->offset
                            );
                        if (!valid || cursor != data_table->bytes ||
                            !metadata_utf8_valid(literal_data, data_table->bytes))
                            continue;
                        if (!matches) selected_count = count;
                        matches++;
                    }}
                }}
            }}
        }}
    }}
    *literal_count = selected_count;
    return matches == 1u && selected_count > 0;
}}

static int metadata_usage_pair_probe(
    const alpha_candidate *candidate,
    const alpha_metadata_table *table,
    uint32_t stride,
    uint32_t destination_dword,
    uint32_t encoded_dword,
    uint64_t string_literal_count,
    uint64_t method_definition_count
) {{
    if (!candidate || !table || stride < 8u || table->bytes % stride ||
        destination_dword == encoded_dword ||
        destination_dword >= stride / 4u || encoded_dword >= stride / 4u)
        return 0;
    uint64_t count = table->bytes / stride;
    if (!count) return 0;
    uint64_t probes[3] = {{0, count / 2u, count - 1u}};
    uint32_t probe_destinations[3] = {{0}};
    uint32_t observed = 0;
    const unsigned char *base =
        (const unsigned char *)(candidate->address + table->offset);
    for (uint32_t probe = 0; probe < 3u; probe++) {{
        int repeated_index = 0;
        for (uint32_t earlier = 0; earlier < probe; earlier++) {{
            if (probes[probe] == probes[earlier]) repeated_index = 1;
        }}
        if (repeated_index) continue;
        const unsigned char *record = base + probes[probe] * stride;
        uint32_t destination = rd32(record + destination_dword * 4u);
        uint32_t encoded = rd32(record + encoded_dword * 4u);
        uint32_t kind = encoded >> 29u;
        uint32_t source = encoded & 0x1fffffffu;
        if (destination >= count || kind < 1u || kind > 6u ||
            (kind == 5u && source >= string_literal_count) ||
            (kind == 3u && source >= method_definition_count)) return 0;
        for (uint32_t earlier = 0; earlier < observed; earlier++) {{
            if (destination == probe_destinations[earlier]) return 0;
        }}
        probe_destinations[observed++] = destination;
    }}
    return observed > 0;
}}

static int metadata_usage_pair_complete(
    const alpha_candidate *candidate,
    const alpha_metadata_table *table,
    uint32_t stride,
    uint32_t destination_dword,
    uint32_t encoded_dword,
    uint64_t maximum_count,
    uint64_t string_literal_count,
    uint64_t method_definition_count
) {{
    if (!metadata_usage_pair_probe(
            candidate, table, stride, destination_dword, encoded_dword,
            string_literal_count, method_definition_count
        )) return 0;
    uint64_t count = table->bytes / stride;
    if (!count || count > maximum_count || count > SIZE_MAX - 7u) return 0;
    SIZE_T seen_bytes = (SIZE_T)((count + 7u) / 8u);
    unsigned char *seen = (unsigned char *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, seen_bytes
    );
    if (!seen) return 0;
    const unsigned char *base =
        (const unsigned char *)(candidate->address + table->offset);
    int valid = 1;
    for (uint64_t index = 0; index < count; index++) {{
        const unsigned char *record = base + index * stride;
        uint32_t destination = rd32(record + destination_dword * 4u);
        uint32_t encoded = rd32(record + encoded_dword * 4u);
        uint32_t kind = encoded >> 29u;
        uint32_t source = encoded & 0x1fffffffu;
        if (destination >= count || kind < 1u || kind > 6u ||
            (kind == 5u && source >= string_literal_count) ||
            (kind == 3u && source >= method_definition_count) ||
            (seen[destination >> 3u] & (1u << (destination & 7u)))) {{
            valid = 0;
            break;
        }}
        seen[destination >> 3u] |= (unsigned char)(1u << (destination & 7u));
    }}
    HeapFree(GetProcessHeap(), 0, seen);
    return valid;
}}

static uint32_t metadata_usage_list_matches(
    const alpha_candidate *candidate,
    const alpha_metadata_table *tables,
    uint32_t table_count,
    uint32_t pair_table_index,
    uint64_t pair_count
) {{
    uint32_t matches = 0;
    for (uint32_t table_index = 0; table_index < table_count; table_index++) {{
        const alpha_metadata_table *table = &tables[table_index];
        if (table->pair_index == pair_table_index) continue;
        for (uint32_t stride = 8u; stride <= ALPHA_MAX_DEFINITION_STRIDE;
             stride += 4u) {{
            if (table->bytes % stride) continue;
            uint64_t list_count = table->bytes / stride;
            if (!list_count) continue;
            uint32_t dwords = stride / 4u;
            const unsigned char *base =
                (const unsigned char *)(candidate->address + table->offset);
            for (uint32_t start_dword = 0; start_dword < dwords;
                 start_dword++) {{
                for (uint32_t count_dword = 0; count_dword < dwords;
                     count_dword++) {{
                    if (count_dword == start_dword) continue;
                    uint64_t cursor = 0;
                    int valid = 1;
                    for (uint64_t index = 0; index < list_count; index++) {{
                        const unsigned char *record = base + index * stride;
                        uint32_t start = rd32(record + start_dword * 4u);
                        uint32_t count = rd32(record + count_dword * 4u);
                        if (start != cursor || count > pair_count - cursor) {{
                            valid = 0;
                            break;
                        }}
                        cursor += count;
                    }}
                    if (valid && cursor == pair_count) matches++;
                }}
            }}
        }}
    }}
    return matches;
}}

static int discover_metadata_usage_count(
    const alpha_candidate *candidate,
    uint64_t image_bytes,
    uint64_t method_definition_count,
    uint64_t *usage_count,
    uint32_t *layout_match_count,
    alpha_metadata_usage_layout *selected_layout
) {{
    alpha_metadata_table tables[ALPHA_MAX_METADATA_TABLE_PAIRS];
    uint32_t table_count = 0;
    if (!candidate || !usage_count || !layout_match_count ||
        !selected_layout ||
        !image_bytes || !method_definition_count ||
        !metadata_tables(candidate, tables, &table_count))
        return 0;
    memset(selected_layout, 0, sizeof(*selected_layout));
    uint64_t string_literal_count = 0;
    if (!discover_metadata_string_literal_count(
            candidate, tables, table_count, &string_literal_count
        )) return 0;
    uint64_t maximum_count = image_bytes / sizeof(uintptr_t);
    uint64_t selected_count = 0;
    uint32_t matches = 0;
    for (uint32_t table_index = 0; table_index < table_count; table_index++) {{
        const alpha_metadata_table *table = &tables[table_index];
        for (uint32_t stride = 8u; stride <= ALPHA_MAX_DEFINITION_STRIDE;
             stride += 4u) {{
            if (table->bytes % stride) continue;
            uint64_t count = table->bytes / stride;
            if (!count || count > maximum_count) continue;
            uint32_t dwords = stride / 4u;
            for (uint32_t destination_dword = 0;
                 destination_dword < dwords; destination_dword++) {{
                for (uint32_t encoded_dword = 0; encoded_dword < dwords;
                     encoded_dword++) {{
                    if (!metadata_usage_pair_complete(
                            candidate, table, stride, destination_dword,
                            encoded_dword, maximum_count,
                            string_literal_count, method_definition_count
                        )) continue;
                    uint32_t list_matches = metadata_usage_list_matches(
                        candidate, tables, table_count, table->pair_index, count
                    );
                    if (!list_matches) continue;
                    if (!matches) {{
                        selected_count = count;
                        selected_layout->pair_table_index = table->pair_index;
                        selected_layout->pair_table_offset = table->offset;
                        selected_layout->pair_table_bytes = table->bytes;
                        selected_layout->pair_stride = stride;
                        selected_layout->destination_dword = destination_dword;
                        selected_layout->encoded_dword = encoded_dword;
                    }}
                    if (UINT32_MAX - matches < list_matches) return 0;
                    matches += list_matches;
                }}
            }}
        }}
    }}
    *usage_count = selected_count;
    *layout_match_count = matches;
    return matches == 1u && selected_count > 0 &&
        selected_layout->pair_table_bytes ==
            selected_count * selected_layout->pair_stride &&
        selected_layout->pair_stride >= 8u &&
        selected_layout->destination_dword !=
            selected_layout->encoded_dword;
}}

static int metadata_usage_slots_unique(
    const uintptr_t *values,
    uint64_t count
) {{
    if (!values || !count || count > SIZE_MAX / sizeof(uintptr_t)) return 0;
    uintptr_t *copy = (uintptr_t *)HeapAlloc(
        GetProcessHeap(), 0, (SIZE_T)(count * sizeof(uintptr_t))
    );
    if (!copy) return 0;
    memcpy(copy, values, (SIZE_T)(count * sizeof(uintptr_t)));
    qsort(copy, (SIZE_T)count, sizeof(copy[0]), pointer_compare);
    int unique = copy[0] != 0;
    for (uint64_t index = 1; unique && index < count; index++) {{
        if (copy[index] == copy[index - 1]) unique = 0;
    }}
    HeapFree(GetProcessHeap(), 0, copy);
    return unique;
}}

static int scan_metadata_usage_array(
    uint64_t usage_count,
    const uintptr_t **selected,
    uint32_t *array_match_count
) {{
    uintptr_t image_base = 0;
    uint64_t image_bytes = 0;
    if (!usage_count || !selected || !array_match_count ||
        !current_image_bounds(&image_base, &image_bytes)) return 0;
    unsigned char *base = (unsigned char *)image_base;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)base;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(base + dos->e_lfanew);
    IMAGE_SECTION_HEADER *sections = IMAGE_FIRST_SECTION(nt);
    uint32_t matches = 0;
    const uintptr_t *result = NULL;
    for (WORD section_index = 0;
         section_index < nt->FileHeader.NumberOfSections; section_index++) {{
        const IMAGE_SECTION_HEADER *section = &sections[section_index];
        if (!(section->Characteristics & IMAGE_SCN_MEM_READ) ||
            (section->Characteristics & IMAGE_SCN_MEM_EXECUTE)) continue;
        uint64_t section_rva = section->VirtualAddress;
        uint64_t extent = section_extent(section);
        if (!extent || section_rva >= image_bytes) continue;
        if (extent > image_bytes - section_rva) extent = image_bytes - section_rva;
        uintptr_t begin_address = image_base + section_rva;
        uintptr_t end_address = begin_address + extent;
        uintptr_t cursor = (begin_address + 7u) & ~(uintptr_t)7u;
        const uintptr_t *run = NULL;
        uint64_t run_count = 0;
        while (cursor <= end_address && end_address - cursor >= sizeof(uintptr_t)) {{
            uintptr_t value = *(const uintptr_t *)cursor;
            int valid = value >= image_base && value < image_base + image_bytes &&
                !(value & 7u);
            if (valid) {{
                if (!run_count) run = (const uintptr_t *)cursor;
                run_count++;
            }} else {{
                if (run_count == usage_count &&
                    metadata_usage_slots_unique(run, run_count)) {{
                    if (!matches) result = run;
                    matches++;
                }}
                run = NULL;
                run_count = 0;
            }}
            cursor += sizeof(uintptr_t);
        }}
        if (run_count == usage_count &&
            metadata_usage_slots_unique(run, run_count)) {{
            if (!matches) result = run;
            matches++;
        }}
    }}
    *selected = result;
    *array_match_count = matches;
    return matches == 1u && result != NULL;
}}

static int dump_memory(const alpha_candidate *candidate) {{
    HANDLE output = CreateFileW(
        metadata_output, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (output == INVALID_HANDLE_VALUE) return 0;
    unsigned char *buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, ALPHA_SCAN_CHUNK
    );
    int ok = buffer != NULL;
    uint64_t position = 0;
    while (ok && position < candidate->extent) {{
        DWORD amount = (DWORD)(candidate->extent - position > ALPHA_SCAN_CHUNK
            ? ALPHA_SCAN_CHUNK : candidate->extent - position);
        DWORD written = 0;
        if (!read_exact(candidate->address + (uintptr_t)position, buffer, amount) ||
            !WriteFile(output, buffer, amount, &written, NULL) || written != amount) {{
            ok = 0;
            break;
        }}
        position += amount;
    }}
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    FlushFileBuffers(output);
    CloseHandle(output);
    _wchmod(metadata_output, 0600);
    if (!ok) DeleteFileW(metadata_output);
    return ok;
}}

static int write_handle_bytes(
    HANDLE output,
    const void *value,
    DWORD byte_count
) {{
    DWORD written = 0;
    return byte_count && WriteFile(
        output, value, byte_count, &written, NULL
    ) && written == byte_count;
}}

static int write_metadata_usage_observation(
    alpha_reflection_scan *scan,
    const alpha_candidate *candidate,
    const char metadata_sha256[65],
    uintptr_t image_base,
    uint64_t image_bytes,
    const uintptr_t *usage_slots,
    uint64_t usage_count,
    uint32_t layout_match_count,
    uint32_t array_match_count
) {{
    char identity_sha256[65] = {{0}};
    char detail_sha256[65] = {{0}};
    if (!scan || !candidate || !metadata_sha256 ||
        strlen(metadata_sha256) != 64 || strlen(expected_executable_sha256) != 64 ||
        strlen(expected_reflection_contract_sha256) != 64 ||
        strlen(expected_inventory_contract_sha256) != 64 ||
        !image_base || (image_base & 0xffffu) || !image_bytes ||
        !usage_slots || !usage_count || usage_count > UINT32_MAX ||
        usage_count > image_bytes / sizeof(uintptr_t) ||
        layout_match_count != 1u || array_match_count != 1u ||
        !sha256_file(type_identity_observation_output, identity_sha256) ||
        !sha256_file(member_detail_observation_output, detail_sha256))
        return 0;
    uintptr_t array_address = (uintptr_t)usage_slots;
    if (array_address < image_base || array_address - image_base >= image_bytes ||
        usage_count * sizeof(uintptr_t) >
            image_bytes - (array_address - image_base) ||
        !metadata_usage_slots_unique(usage_slots, usage_count)) return 0;
    HANDLE output = CreateFileW(
        metadata_usage_observation_output, GENERIC_WRITE, 0, NULL,
        CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (output == INVALID_HANDLE_VALUE) return 0;
    const char magic[] = "{RUNTIME_METADATA_USAGE_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_METADATA_USAGE_VERSION}u;
    uint32_t header_bytes = ALPHA_METADATA_USAGE_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0;
    uint64_t array_rva = array_address - image_base;
    uint32_t unique_slot_count = (uint32_t)usage_count;
    uint64_t written = 0;
    int ok = sizeof(magic) - 1u == 8u &&
        ALPHA_METADATA_USAGE_ENTRY_BYTES == sizeof(uintptr_t);
#define ALPHA_WRITE_USAGE(value) do {{ \
    if (ok) {{ \
        written += sizeof(value); \
        ok = write_handle_bytes(output, &(value), (DWORD)sizeof(value)); \
    }} \
}} while (0)
    if (ok) {{ written += 8u; ok = write_handle_bytes(output, magic, 8u); }}
    ALPHA_WRITE_USAGE(version);
    ALPHA_WRITE_USAGE(header_bytes);
    ALPHA_WRITE_USAGE(pointer_bytes);
    ALPHA_WRITE_USAGE(reserved);
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, expected_executable_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, metadata_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, expected_reflection_contract_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, identity_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, detail_sha256, 64u); }}
    ALPHA_WRITE_USAGE(image_base);
    ALPHA_WRITE_USAGE(image_bytes);
    ALPHA_WRITE_USAGE(usage_count);
    ALPHA_WRITE_USAGE(array_rva);
    ALPHA_WRITE_USAGE(unique_slot_count);
    ALPHA_WRITE_USAGE(array_match_count);
#undef ALPHA_WRITE_USAGE
    uint64_t entry_bytes = usage_count * sizeof(uintptr_t);
    if (ok && (written != ALPHA_METADATA_USAGE_HEADER_BYTES ||
        entry_bytes > UINT32_MAX)) ok = 0;
    if (ok) {{
        written += entry_bytes;
        ok = write_handle_bytes(
            output, usage_slots, (DWORD)entry_bytes
        );
    }}
    if (ok) ok = FlushFileBuffers(output) != 0;
    CloseHandle(output);
    _wchmod(metadata_usage_observation_output, 0600);
    if (!ok) DeleteFileW(metadata_usage_observation_output);
    scan->metadata_usage_count = usage_count;
    scan->metadata_usage_array_rva = array_rva;
    scan->metadata_usage_layout_match_count = layout_match_count;
    scan->metadata_usage_array_match_count = array_match_count;
    scan->metadata_usage_observation_bytes = written;
    scan->metadata_usage_layout_derived = layout_match_count == 1u;
    scan->metadata_usage_slots_unique = ok;
    scan->metadata_usage_observation_written = ok;
    scan->metadata_usage_observation_complete = ok;
    return ok;
}}

static int captured_type_handle_contains(uintptr_t target) {{
    uint64_t left = 0, right = captured_type_native_handle_count;
    if (!target || !captured_type_native_handles || !right) return 0;
    while (left < right) {{
        uint64_t middle = left + (right - left) / 2u;
        if (captured_type_native_handles[middle] < target)
            left = middle + 1u;
        else
            right = middle;
    }}
    return left < captured_type_native_handle_count &&
        captured_type_native_handles[left] == target;
}}

static void release_captured_type_native_handles(void) {{
    free(captured_type_native_handles);
    captured_type_native_handles = NULL;
    captured_type_native_handle_count = 0;
}}

static int collect_type_metadata_usages(
    const alpha_candidate *candidate,
    const alpha_metadata_usage_layout *layout,
    uint64_t usage_count,
    alpha_type_metadata_usage_entry **selected,
    uint64_t *selected_count,
    uint32_t *maximum_source
) {{
    if (!candidate || !layout || !usage_count || !selected ||
        !selected_count || !maximum_source ||
        layout->pair_stride < 8u ||
        layout->pair_table_bytes != usage_count * layout->pair_stride ||
        layout->pair_table_offset >= candidate->extent ||
        layout->pair_table_bytes >
            candidate->extent - layout->pair_table_offset ||
        layout->destination_dword >= layout->pair_stride / 4u ||
        layout->encoded_dword >= layout->pair_stride / 4u ||
        layout->destination_dword == layout->encoded_dword)
        return 0;
    const unsigned char *base = (const unsigned char *)(
        candidate->address + layout->pair_table_offset
    );
    uint64_t count = 0;
    uint32_t largest_source = 0;
    for (uint64_t index = 0; index < usage_count; index++) {{
        const unsigned char *record = base + index * layout->pair_stride;
        uint32_t destination = rd32(
            record + layout->destination_dword * 4u
        );
        uint32_t encoded = rd32(record + layout->encoded_dword * 4u);
        if (destination >= usage_count) return 0;
        if ((encoded >> 29u) != 1u) continue;
        uint32_t source = encoded & 0x1fffffffu;
        if (!count || source > largest_source) largest_source = source;
        count++;
    }}
    if (!count || count > SIZE_MAX / sizeof(alpha_type_metadata_usage_entry))
        return 0;
    alpha_type_metadata_usage_entry *entries =
        (alpha_type_metadata_usage_entry *)HeapAlloc(
            GetProcessHeap(), HEAP_ZERO_MEMORY,
            (SIZE_T)(count * sizeof(*entries))
        );
    if (!entries) return 0;
    uint64_t output = 0;
    for (uint64_t index = 0; index < usage_count; index++) {{
        const unsigned char *record = base + index * layout->pair_stride;
        uint32_t encoded = rd32(record + layout->encoded_dword * 4u);
        if ((encoded >> 29u) != 1u) continue;
        entries[output].destination_index = rd32(
            record + layout->destination_dword * 4u
        );
        entries[output].source_index = encoded & 0x1fffffffu;
        output++;
    }}
    if (output != count) {{
        HeapFree(GetProcessHeap(), 0, entries);
        return 0;
    }}
    *selected = entries;
    *selected_count = count;
    *maximum_source = largest_source;
    return 1;
}}

static int type_registration_run_matches(
    const uintptr_t *run,
    uint64_t run_count,
    alpha_type_metadata_usage_entry *entries,
    uint64_t entry_count,
    uint32_t maximum_source
) {{
    if (!run || !run_count || !entries || !entry_count ||
        run_count <= maximum_source ||
        entry_count > SIZE_MAX / sizeof(uintptr_t)) return 0;
    uintptr_t *selected = (uintptr_t *)HeapAlloc(
        GetProcessHeap(), 0, (SIZE_T)(entry_count * sizeof(uintptr_t))
    );
    if (!selected) return 0;
    int valid = 1;
    for (uint64_t index = 0; index < entry_count; index++) {{
        uint32_t source = entries[index].source_index;
        uintptr_t handle = run[source];
        if (source >= run_count || !captured_type_handle_contains(handle)) {{
            valid = 0;
            break;
        }}
        selected[index] = handle;
    }}
    if (valid) {{
        qsort(
            selected, (SIZE_T)entry_count, sizeof(uintptr_t), pointer_compare
        );
        for (uint64_t index = 0; index < entry_count; index++) {{
            if (!selected[index] ||
                (index && selected[index] == selected[index - 1])) {{
                valid = 0;
                break;
            }}
        }}
    }}
    if (valid) {{
        for (uint64_t index = 0; index < entry_count; index++)
            entries[index].type_handle = run[entries[index].source_index];
    }}
    HeapFree(GetProcessHeap(), 0, selected);
    return valid;
}}

static int scan_type_registration_array(
    alpha_type_metadata_usage_entry *entries,
    uint64_t entry_count,
    uint32_t maximum_source,
    const uintptr_t **selected,
    uint64_t *selected_count,
    uint32_t *array_match_count
) {{
    uintptr_t image_base = 0;
    uint64_t image_bytes = 0;
    if (!entries || !entry_count || !selected || !selected_count ||
        !array_match_count || !captured_type_native_handles ||
        !captured_type_native_handle_count ||
        !current_image_bounds(&image_base, &image_bytes)) return 0;
    unsigned char *base = (unsigned char *)image_base;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)base;
    IMAGE_NT_HEADERS64 *nt = (IMAGE_NT_HEADERS64 *)(base + dos->e_lfanew);
    IMAGE_SECTION_HEADER *sections = IMAGE_FIRST_SECTION(nt);
    const uintptr_t *result = NULL;
    uint64_t result_count = 0;
    uint32_t matches = 0;
    for (WORD section_index = 0;
         section_index < nt->FileHeader.NumberOfSections; section_index++) {{
        const IMAGE_SECTION_HEADER *section = &sections[section_index];
        if (!(section->Characteristics & IMAGE_SCN_MEM_READ) ||
            (section->Characteristics & IMAGE_SCN_MEM_EXECUTE)) continue;
        uint64_t section_rva = section->VirtualAddress;
        uint64_t extent = section_extent(section);
        if (!extent || section_rva >= image_bytes) continue;
        if (extent > image_bytes - section_rva) extent = image_bytes - section_rva;
        uintptr_t begin_address = image_base + section_rva;
        uintptr_t end_address = begin_address + extent;
        uintptr_t cursor = (begin_address + 7u) & ~(uintptr_t)7u;
        const uintptr_t *run = NULL;
        uint64_t run_count = 0;
        for (;;) {{
            int at_end = cursor > end_address ||
                end_address - cursor < sizeof(uintptr_t);
            uintptr_t value = at_end ? 0 : *(const uintptr_t *)cursor;
            int pointer_valid = !at_end && value >= image_base &&
                value < image_base + image_bytes && !(value & 7u);
            if (pointer_valid) {{
                if (!run_count) run = (const uintptr_t *)cursor;
                run_count++;
            }} else {{
                if (run_count > maximum_source &&
                    run_count <= ALPHA_MAX_TYPE_COUNT &&
                    type_registration_run_matches(
                        run, run_count, entries, entry_count, maximum_source
                    )) {{
                    if (!matches) {{
                        result = run;
                        result_count = run_count;
                    }}
                    if (matches == UINT32_MAX) return 0;
                    matches++;
                }}
                run = NULL;
                run_count = 0;
                if (at_end) break;
            }}
            cursor += sizeof(uintptr_t);
        }}
    }}
    *selected = result;
    *selected_count = result_count;
    *array_match_count = matches;
    if (matches != 1u || !result || !result_count ||
        !type_registration_run_matches(
            result, result_count, entries, entry_count, maximum_source
        )) return 0;
    return 1;
}}

static int write_type_metadata_usage_observation(
    alpha_reflection_scan *scan,
    const char metadata_sha256[65],
    uintptr_t image_base,
    uint64_t image_bytes,
    const uintptr_t *types,
    uint64_t type_count,
    const alpha_type_metadata_usage_entry *entries,
    uint64_t entry_count,
    uint32_t array_match_count
) {{
    char type_native_sha256[65] = {{0}};
    char metadata_usage_sha256[65] = {{0}};
    if (!scan || !metadata_sha256 || strlen(metadata_sha256) != 64 ||
        strlen(expected_executable_sha256) != 64 ||
        strlen(expected_reflection_contract_sha256) != 64 ||
        strlen(expected_inventory_contract_sha256) != 64 ||
        !image_base || (image_base & 0xffffu) || !image_bytes || !types ||
        !type_count || !entries || !entry_count || array_match_count != 1u ||
        !sha256_file(type_native_observation_output, type_native_sha256) ||
        !sha256_file(
            metadata_usage_observation_output, metadata_usage_sha256
        )) return 0;
    uintptr_t types_address = (uintptr_t)types;
    if (types_address < image_base ||
        types_address - image_base >= image_bytes ||
        type_count > image_bytes / sizeof(uintptr_t) ||
        type_count * sizeof(uintptr_t) >
            image_bytes - (types_address - image_base) ||
        entry_count > UINT32_MAX ||
        entry_count > (UINT64_MAX - ALPHA_TYPE_METADATA_USAGE_HEADER_BYTES) /
            ALPHA_TYPE_METADATA_USAGE_ENTRY_BYTES)
        return 0;
    HANDLE output = CreateFileW(
        type_metadata_usage_observation_output, GENERIC_WRITE, 0, NULL,
        CREATE_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (output == INVALID_HANDLE_VALUE) return 0;
    const char magic[] = "{RUNTIME_TYPE_METADATA_USAGE_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_TYPE_METADATA_USAGE_VERSION}u;
    uint32_t header_bytes = ALPHA_TYPE_METADATA_USAGE_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0;
    uint64_t types_rva = types_address - image_base;
    uint32_t reserved_two = 0;
    uint64_t written = 0;
    int ok = sizeof(magic) - 1u == 8u &&
        ALPHA_TYPE_METADATA_USAGE_ENTRY_BYTES ==
            sizeof(alpha_type_metadata_usage_entry);
#define ALPHA_WRITE_TYPE_USAGE(value) do {{ \
    if (ok) {{ \
        written += sizeof(value); \
        ok = write_handle_bytes(output, &(value), (DWORD)sizeof(value)); \
    }} \
}} while (0)
    if (ok) {{ written += 8u; ok = write_handle_bytes(output, magic, 8u); }}
    ALPHA_WRITE_TYPE_USAGE(version);
    ALPHA_WRITE_TYPE_USAGE(header_bytes);
    ALPHA_WRITE_TYPE_USAGE(pointer_bytes);
    ALPHA_WRITE_TYPE_USAGE(reserved);
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, expected_executable_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, metadata_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, expected_reflection_contract_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, type_native_sha256, 64u); }}
    if (ok) {{ written += 64u; ok = write_handle_bytes(output, metadata_usage_sha256, 64u); }}
    ALPHA_WRITE_TYPE_USAGE(image_base);
    ALPHA_WRITE_TYPE_USAGE(image_bytes);
    ALPHA_WRITE_TYPE_USAGE(types_rva);
    ALPHA_WRITE_TYPE_USAGE(type_count);
    ALPHA_WRITE_TYPE_USAGE(entry_count);
    ALPHA_WRITE_TYPE_USAGE(array_match_count);
    ALPHA_WRITE_TYPE_USAGE(reserved_two);
#undef ALPHA_WRITE_TYPE_USAGE
    uint64_t entries_bytes =
        entry_count * ALPHA_TYPE_METADATA_USAGE_ENTRY_BYTES;
    if (ok && (written != ALPHA_TYPE_METADATA_USAGE_HEADER_BYTES ||
        entries_bytes > UINT32_MAX)) ok = 0;
    if (ok) {{
        written += entries_bytes;
        ok = write_handle_bytes(output, entries, (DWORD)entries_bytes);
    }}
    if (ok) ok = FlushFileBuffers(output) != 0;
    CloseHandle(output);
    _wchmod(type_metadata_usage_observation_output, 0600);
    if (!ok) DeleteFileW(type_metadata_usage_observation_output);
    scan->type_metadata_usage_count = entry_count;
    scan->type_registration_count = type_count;
    scan->type_registration_array_rva = types_rva;
    scan->type_registration_array_match_count = array_match_count;
    scan->type_metadata_usage_observation_bytes = written;
    scan->type_metadata_usage_handles_unique = ok;
    scan->type_metadata_usage_observation_written = ok;
    scan->type_metadata_usage_observation_complete = ok;
    return ok;
}}

static int write_reflection_dispatch_manifest(alpha_reflection_scan *scan) {{
    if (!scan || !scan->reflection_dispatch_contract_complete ||
        scan->runtime_arity_operation_unique_count !=
            required_reflection_operation_count ||
        strlen(expected_executable_sha256) != 64 ||
        strlen(expected_reflection_contract_sha256) != 64 ||
        sizeof(uintptr_t) != 8 ||
        sizeof("{RUNTIME_DISPATCH_MAGIC.decode('ascii')}") - 1 != 8)
        return 0;
    HANDLE output = CreateFileW(
        reflection_dispatch_output,
        GENERIC_WRITE,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (output == INVALID_HANDLE_VALUE) return 0;
    static const unsigned char magic[8] = "{RUNTIME_DISPATCH_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_DISPATCH_VERSION}u;
    uint32_t header_bytes = ALPHA_DISPATCH_HEADER_BYTES;
    uint32_t operation_count = required_reflection_operation_count;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint64_t method_record_count = scan->method_record_count;
    uint64_t written_total = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{
        written_total += sizeof(magic);
        ok = write_handle_bytes(output, &version, sizeof(version));
    }}
    if (ok) {{
        written_total += sizeof(version);
        ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes));
    }}
    if (ok) {{
        written_total += sizeof(header_bytes);
        ok = write_handle_bytes(output, &operation_count, sizeof(operation_count));
    }}
    if (ok) {{
        written_total += sizeof(operation_count);
        ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes));
    }}
    if (ok) {{
        written_total += sizeof(pointer_bytes);
        ok = write_handle_bytes(output, expected_executable_sha256, 64);
    }}
    if (ok) {{
        written_total += 64;
        ok = write_handle_bytes(
            output, expected_reflection_contract_sha256, 64
        );
    }}
    if (ok) {{
        written_total += 64;
        ok = write_handle_bytes(
            output, &method_record_count, sizeof(method_record_count)
        );
    }}
    if (ok) written_total += sizeof(method_record_count);
    for (uint32_t operation = 0;
         operation < required_reflection_operation_count && ok;
         operation++) {{
        const alpha_required_operation *requirement =
            &required_reflection_operations[operation];
        uint16_t parameter_count = requirement->parameter_count;
        uint16_t reserved = 0;
        uint32_t name_candidates =
            scan->runtime_named_operation_candidate_count[operation];
        uint32_t arity_candidates =
            scan->runtime_arity_operation_candidate_count[operation];
        uint64_t class_pointer =
            scan->runtime_arity_operation_class[operation];
        uint64_t metadata_pointer =
            scan->runtime_arity_operation_metadata[operation];
        uint64_t method_pointer =
            scan->runtime_arity_operation_pointer[operation];
        if (arity_candidates != 1 || !class_pointer || !metadata_pointer ||
            !method_pointer ||
            !write_handle_bytes(output, &operation, sizeof(operation)) ||
            !write_handle_bytes(
                output, &parameter_count, sizeof(parameter_count)
            ) || !write_handle_bytes(output, &reserved, sizeof(reserved)) ||
            !write_handle_bytes(
                output, &name_candidates, sizeof(name_candidates)
            ) || !write_handle_bytes(
                output, &arity_candidates, sizeof(arity_candidates)
            ) || !write_handle_bytes(
                output, &class_pointer, sizeof(class_pointer)
            ) || !write_handle_bytes(
                output, &metadata_pointer, sizeof(metadata_pointer)
            ) || !write_handle_bytes(
                output, &method_pointer, sizeof(method_pointer)
            )) {{
            ok = 0;
            break;
        }}
        written_total += ALPHA_DISPATCH_ENTRY_BYTES;
    }}
    uint64_t expected_bytes = ALPHA_DISPATCH_HEADER_BYTES +
        (uint64_t)required_reflection_operation_count *
            ALPHA_DISPATCH_ENTRY_BYTES;
    if (written_total != expected_bytes || !FlushFileBuffers(output)) ok = 0;
    CloseHandle(output);
    if (ok && _wchmod(reflection_dispatch_output, 0600)) ok = 0;
    if (!ok) DeleteFileW(reflection_dispatch_output);
    scan->reflection_dispatch_manifest_written = ok;
    return ok;
}}

static const alpha_inventory_operation_candidate *inventory_requirement(
    uint32_t operation
) {{
    for (uint32_t candidate = 0;
         candidate < required_inventory_operation_candidate_count;
         candidate++) {{
        if (required_inventory_operation_candidates[candidate].operation_index ==
                operation)
            return &required_inventory_operation_candidates[candidate];
    }}
    return NULL;
}}

static int write_inventory_dispatch_manifest(alpha_reflection_scan *scan) {{
    if (!scan || !scan->inventory_dispatch_contract_complete ||
        scan->inventory_arity_operation_unique_count !=
            required_inventory_operation_count ||
        strlen(expected_executable_sha256) != 64 ||
        strlen(expected_inventory_contract_sha256) != 64 ||
        sizeof(uintptr_t) != 8 ||
        sizeof("{RUNTIME_INVENTORY_DISPATCH_MAGIC.decode('ascii')}") - 1 != 8)
        return 0;
    HANDLE output = CreateFileW(
        inventory_dispatch_output,
        GENERIC_WRITE,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (output == INVALID_HANDLE_VALUE) return 0;
    static const unsigned char magic[8] =
        "{RUNTIME_INVENTORY_DISPATCH_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_INVENTORY_DISPATCH_VERSION}u;
    uint32_t header_bytes = ALPHA_INVENTORY_DISPATCH_HEADER_BYTES;
    uint32_t operation_count = required_inventory_operation_count;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint64_t method_record_count = scan->method_record_count;
    uint64_t written_total = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written_total += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written_total += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written_total += sizeof(header_bytes); ok = write_handle_bytes(output, &operation_count, sizeof(operation_count)); }}
    if (ok) {{ written_total += sizeof(operation_count); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written_total += sizeof(pointer_bytes); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written_total += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written_total += 64; ok = write_handle_bytes(output, &method_record_count, sizeof(method_record_count)); }}
    if (ok) written_total += sizeof(method_record_count);
    for (uint32_t operation = 0;
         operation < required_inventory_operation_count && ok;
         operation++) {{
        const alpha_inventory_operation_candidate *requirement =
            inventory_requirement(operation);
        if (!requirement) {{ ok = 0; break; }}
        uint16_t parameter_count = requirement->parameter_count;
        uint16_t reserved = 0;
        uint32_t name_candidates =
            scan->inventory_named_operation_candidate_count[operation];
        uint32_t arity_candidates =
            scan->inventory_arity_operation_candidate_count[operation];
        uint64_t class_pointer =
            scan->inventory_arity_operation_class[operation];
        uint64_t metadata_pointer =
            scan->inventory_arity_operation_metadata[operation];
        uint64_t method_pointer =
            scan->inventory_arity_operation_pointer[operation];
        if (arity_candidates != 1 || !class_pointer || !metadata_pointer ||
            !method_pointer ||
            !write_handle_bytes(output, &operation, sizeof(operation)) ||
            !write_handle_bytes(output, &parameter_count, sizeof(parameter_count)) ||
            !write_handle_bytes(output, &reserved, sizeof(reserved)) ||
            !write_handle_bytes(output, &name_candidates, sizeof(name_candidates)) ||
            !write_handle_bytes(output, &arity_candidates, sizeof(arity_candidates)) ||
            !write_handle_bytes(output, &class_pointer, sizeof(class_pointer)) ||
            !write_handle_bytes(output, &metadata_pointer, sizeof(metadata_pointer)) ||
            !write_handle_bytes(output, &method_pointer, sizeof(method_pointer))) {{
            ok = 0;
            break;
        }}
        written_total += ALPHA_INVENTORY_DISPATCH_ENTRY_BYTES;
    }}
    uint64_t expected_bytes = ALPHA_INVENTORY_DISPATCH_HEADER_BYTES +
        (uint64_t)required_inventory_operation_count *
            ALPHA_INVENTORY_DISPATCH_ENTRY_BYTES;
    if (written_total != expected_bytes || !FlushFileBuffers(output)) ok = 0;
    CloseHandle(output);
    if (ok && _wchmod(inventory_dispatch_output, 0600)) ok = 0;
    if (!ok) DeleteFileW(inventory_dispatch_output);
    scan->inventory_dispatch_manifest_written = ok;
    return ok;
}}

typedef struct {{
    DWORD process_id;
    uint32_t candidate_count;
    HWND selected_window;
    DWORD selected_thread_id;
}} alpha_window_selection;

static alpha_reflection_scan *managed_name_reflection;
static alpha_method_record *managed_name_methods;
static uint64_t managed_name_method_count;
static HANDLE managed_name_event;
static HHOOK managed_name_hook;
static UINT managed_name_message;
static volatile LONG managed_name_state;
static alpha_reflection_scan *managed_probe_reflection;
static HANDLE managed_probe_event;
static HHOOK managed_probe_hook;
static UINT managed_probe_message;
static volatile LONG managed_probe_state;
static volatile LONG managed_probe_mode;
static uint32_t managed_slice_index;
static uintptr_t *managed_slice_types;
static uint32_t managed_slice_type_count;
static uintptr_t *captured_type_roots;
static uint64_t captured_type_root_count;
static uint32_t *captured_assembly_type_counts;
static char **captured_assembly_full_names;
static char *managed_slice_assembly_full_name;
static uintptr_t *managed_member_arrays[ALPHA_MEMBER_CATEGORY_COUNT];
static uint32_t managed_member_counts[ALPHA_MEMBER_CATEGORY_COUNT];
static uint32_t managed_member_assembly_index;
static uint32_t managed_member_type_index;

typedef struct {{
    unsigned char *values;
    uint64_t count;
    uint64_t capacity;
}} alpha_byte_vector;

static alpha_byte_vector managed_member_detail;
static alpha_byte_vector managed_type_graph_node;
static alpha_byte_vector managed_type_native;
static alpha_byte_vector managed_method_native;
static alpha_byte_vector managed_field_native;

typedef struct {{
    uintptr_t member_object;
    uintptr_t metadata_object;
    uintptr_t declaring_class;
    uintptr_t type_handle;
    uintptr_t declaring_type_object;
    uint32_t metadata_token;
    uint32_t attributes;
    uint32_t name_qword_index;
    uint32_t type_qword_index;
    uint32_t parent_qword_index;
    uint32_t token_dword_index;
    unsigned char metadata_sample[ALPHA_FIELD_METADATA_SAMPLE_BYTES];
}} alpha_field_native_candidate;
static uintptr_t *managed_type_references;
static uint32_t managed_type_reference_count;
static uint32_t managed_type_reference_capacity;
static uintptr_t managed_graph_type_object;

typedef struct {{
    char *name;
    char *namespace_name;
    uint32_t attributes;
    uint32_t shape;
    uintptr_t base_type;
    uintptr_t declaring_type;
    uintptr_t element_type;
    uintptr_t generic_definition;
    uintptr_t *interfaces;
    uint32_t interface_count;
    uintptr_t *generic_arguments;
    uint32_t generic_argument_count;
}} alpha_type_identity_slice;

static alpha_type_identity_slice managed_type_identity;

typedef struct {{
    int is_generic_parameter;
    uint32_t position;
    uint32_t attributes;
    uintptr_t *constraints;
    uint32_t constraint_count;
    int is_array;
    int is_pointer;
    uint32_t element_rank;
}} alpha_type_graph_extra;

static alpha_type_graph_extra managed_type_graph_extra;

static BOOL CALLBACK select_managed_window(HWND window, LPARAM parameter) {{
    alpha_window_selection *selection =
        (alpha_window_selection *)(uintptr_t)parameter;
    DWORD process_id = 0;
    RECT bounds;
    if (!selection || !IsWindowVisible(window) ||
        GetWindow(window, GW_OWNER) != NULL ||
        !GetWindowRect(window, &bounds) ||
        bounds.right <= bounds.left || bounds.bottom <= bounds.top)
        return TRUE;
    DWORD thread_id = GetWindowThreadProcessId(window, &process_id);
    if (!thread_id || process_id != selection->process_id) return TRUE;
    selection->candidate_count++;
    selection->selected_window = window;
    selection->selected_thread_id = thread_id;
    return TRUE;
}}

static void record_runtime_method_name_failure(
    alpha_reflection_scan *scan,
    const alpha_method_record *method,
    uint64_t method_index
) {{
    if (!scan || !method || scan->method_name_decode_failure_index) return;
    unsigned char *image_base =
        (unsigned char *)GetModuleHandleW(NULL);
    scan->method_name_decode_failure_index = method_index + 1;
    if (image_base && method->method_pointer >= (uintptr_t)image_base)
        scan->method_name_decode_failure_method_rva =
            method->method_pointer - (uintptr_t)image_base;
    for (uint32_t owner = 0;
         owner < required_reflection_owner_count;
         owner++) {{
        if (scan->required_owner_classes[owner] == method->class_pointer) {{
            scan->method_name_decode_failure_owner_index = owner + 1;
            break;
        }}
    }}
}}

static LRESULT CALLBACK managed_method_name_probe(
    int code,
    WPARAM parameter,
    LPARAM data
) {{
    (void)parameter;
    MSG *message = (MSG *)(uintptr_t)data;
    alpha_reflection_scan *scan = managed_name_reflection;
    alpha_method_record *methods = managed_name_methods;
    uint64_t method_count = managed_name_method_count;
    if (code == HC_ACTION && message && scan && methods && method_count &&
        managed_name_event && message->message == managed_name_message &&
        InterlockedCompareExchange(&managed_name_state, 1, 0) == 0) {{
        scan->method_name_callback_thread_id = GetCurrentThreadId();
        int callback_complete = scan->method_name_callback_thread_id ==
            scan->method_name_window_thread_id;
        for (uint64_t method = 0;
             method < method_count && callback_complete;
             method++) {{
            memset(
                methods[method].runtime_name,
                0,
                sizeof(methods[method].runtime_name)
            );
            if (!runtime_method_name(
                    scan,
                    methods[method].metadata_pointer,
                    methods[method].runtime_name,
                    sizeof(methods[method].runtime_name)
                ))
                record_runtime_method_name_failure(
                    scan, &methods[method], method
                );
        }}
        callback_complete = callback_complete &&
            scan->method_name_decode_attempt_count == method_count &&
            scan->method_name_decode_success_count > 0 &&
            scan->method_name_decode_success_count <= method_count;
        scan->method_name_managed_callback_complete = callback_complete;
        InterlockedExchange(
            &managed_name_state, callback_complete ? 2 : -1
        );
        SetEvent(managed_name_event);
    }}
    return CallNextHookEx(managed_name_hook, code, parameter, data);
}}

static int observe_runtime_method_names_on_managed_thread(
    alpha_reflection_scan *scan,
    alpha_method_record *methods,
    uint64_t method_count
) {{
    alpha_window_selection selection;
    memset(&selection, 0, sizeof(selection));
    if (!scan || !methods || !method_count ||
        !scan->method_name_decoder_derived ||
        !scan->method_name_lazy_initializer_semantically_bound)
        return 0;
    selection.process_id = GetCurrentProcessId();
    if (!EnumWindows(select_managed_window, (LPARAM)(uintptr_t)&selection))
        return 0;
    scan->method_name_window_candidate_count = selection.candidate_count;
    scan->method_name_window_thread_id = selection.selected_thread_id;
    if (selection.candidate_count != 1 || !selection.selected_window ||
        !selection.selected_thread_id ||
        selection.selected_thread_id == GetCurrentThreadId())
        return 0;
    managed_name_message = RegisterWindowMessageW(
        L"ALPHA v2 fresh runtime method name bootstrap"
    );
    managed_name_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    managed_name_reflection = scan;
    managed_name_methods = methods;
    managed_name_method_count = method_count;
    InterlockedExchange(&managed_name_state, 0);
    if (!managed_name_message || !managed_name_event) goto cleanup;
    managed_name_hook = SetWindowsHookExW(
        WH_GETMESSAGE,
        managed_method_name_probe,
        self_module,
        selection.selected_thread_id
    );
    if (!managed_name_hook || !PostMessageW(
            selection.selected_window, managed_name_message, 0, 0))
        goto cleanup;
    if (WaitForSingleObject(managed_name_event, 15000) != WAIT_OBJECT_0)
        InterlockedExchange(&managed_name_state, -1);

cleanup:
    if (managed_name_hook) UnhookWindowsHookEx(managed_name_hook);
    managed_name_hook = NULL;
    if (managed_name_event) CloseHandle(managed_name_event);
    managed_name_event = NULL;
    managed_name_reflection = NULL;
    managed_name_methods = NULL;
    managed_name_method_count = 0;
    managed_name_message = 0;
    return scan->method_name_managed_callback_complete &&
        managed_name_state == 2;
}}

static void write_runtime_method_name_diagnostic(
    const alpha_reflection_scan *scan,
    const alpha_method_record *methods,
    uint64_t method_count
) {{
    wchar_t path[32768];
    if (!scan || !methods || !method_count || _snwprintf(
            path,
            sizeof(path) / sizeof(path[0]),
            L"%ls.method-names.private.tsv",
            status_output
        ) < 0) return;
    FILE *output = _wfopen(path, L"wb");
    if (!output) return;
    unsigned char *image_base = (unsigned char *)GetModuleHandleW(NULL);
    for (uint64_t method = 0; method < method_count; method++) {{
        uint32_t owner = UINT32_MAX;
        for (uint32_t index = 0;
             index < required_reflection_owner_count;
             index++) {{
            if (scan->required_owner_classes[index] ==
                methods[method].class_pointer) {{
                owner = index;
                break;
            }}
        }}
        uint64_t rva = image_base &&
            methods[method].method_pointer >= (uintptr_t)image_base
            ? methods[method].method_pointer - (uintptr_t)image_base : 0;
        fprintf(
            output,
            "%u\t%u\t%llu\t",
            owner,
            (unsigned)methods[method].parameter_count,
            (unsigned long long)rva
        );
        for (const unsigned char *value =
                 (const unsigned char *)methods[method].runtime_name;
             *value;
             value++) fprintf(output, "%02x", (unsigned)*value);
        fputc('\n', output);
    }}
    fclose(output);
    _wchmod(path, 0600);
}}

static int inventory_operation_slot(
    const char *key,
    uint32_t *selected_operation
) {{
    uint32_t matches = 0, selected = 0;
    if (!key || !selected_operation) return 0;
    for (uint32_t candidate = 0;
         candidate < required_inventory_operation_candidate_count;
         candidate++) {{
        const alpha_inventory_operation_candidate *requirement =
            &required_inventory_operation_candidates[candidate];
        if (strcmp(requirement->key, key)) continue;
        if (!matches) selected = requirement->operation_index;
        if (selected != requirement->operation_index) return 0;
        matches++;
    }}
    if (!matches || selected >= required_inventory_operation_count)
        return 0;
    *selected_operation = selected;
    return 1;
}}

static int reflection_operation_slot(
    const char *key,
    uint32_t *selected_operation
) {{
    uint32_t matches = 0, selected = 0;
    if (!key || !selected_operation) return 0;
    for (uint32_t operation = 0;
         operation < required_reflection_operation_count;
         operation++) {{
        if (strcmp(required_reflection_operations[operation].key, key))
            continue;
        selected = operation;
        matches++;
    }}
    if (matches != 1) return 0;
    *selected_operation = selected;
    return 1;
}}

static uintptr_t required_runtime_owner_class(
    const alpha_reflection_scan *scan,
    const char *namespace_name,
    const char *type_name
) {{
    uintptr_t selected = 0;
    uint32_t matches = 0;
    if (!scan || !namespace_name || !type_name) return 0;
    for (uint32_t index = 0; index < required_reflection_owner_count; index++) {{
        if (strcmp(
                required_reflection_owners[index].namespace_name,
                namespace_name
            ) || strcmp(
                required_reflection_owners[index].type_name,
                type_name
            ))
            continue;
        selected = scan->required_owner_classes[index];
        matches++;
    }}
    return matches == 1 ? selected : 0;
}}

static int runtime_object_class_matches(
    uintptr_t object_pointer,
    uintptr_t expected_class
) {{
    uintptr_t observed_class = 0;
    return object_pointer && expected_class &&
        memory_pointer_kind(object_pointer) == 1 &&
        read_exact(object_pointer, &observed_class, sizeof(observed_class)) &&
        observed_class == expected_class;
}}

typedef uintptr_t (*alpha_static_noarg_method)(uintptr_t method_metadata);
typedef uintptr_t (*alpha_static_onearg_method)(
    uintptr_t value,
    uintptr_t method_metadata
);
typedef uintptr_t (*alpha_static_twoarg_method)(
    uintptr_t first,
    uintptr_t second,
    uintptr_t method_metadata
);
typedef uintptr_t (*alpha_instance_noarg_method)(
    uintptr_t instance,
    uintptr_t method_metadata
);
typedef uintptr_t (*alpha_instance_flags_method)(
    uintptr_t instance,
    uint32_t binding_flags,
    uintptr_t method_metadata
);
typedef uint32_t (*alpha_instance_dword_method)(
    uintptr_t instance,
    uintptr_t method_metadata
);
typedef uint8_t (*alpha_instance_bool_method)(
    uintptr_t instance,
    uintptr_t method_metadata
);
typedef uintptr_t (*alpha_instance_boolarg_method)(
    uintptr_t instance,
    uint32_t value,
    uintptr_t method_metadata
);

static int discover_managed_reference_array(
    uintptr_t array_object,
    uintptr_t expected_element_class,
    uint32_t maximum_count,
    uint32_t *selected_count,
    uint32_t *selected_length_qword,
    uint32_t *selected_vector_qword,
    uint32_t *candidate_count
) {{
    uint32_t candidates = 0, chosen_count = 0, chosen_vector = 0;
    uint32_t chosen_length = 0;
    if (!array_object || !expected_element_class || !maximum_count ||
        !selected_count || !selected_length_qword ||
        !selected_vector_qword || !candidate_count ||
        memory_pointer_kind(array_object) != 1)
        return 0;
    for (uint32_t length_qword = 1; length_qword < 12; length_qword++) {{
        uintptr_t observed_length = 0;
        if (!read_exact(
                array_object + (uintptr_t)length_qword * 8u,
                &observed_length,
                sizeof(observed_length)
            ) || !observed_length || observed_length > maximum_count)
            continue;
        for (uint32_t vector_qword = length_qword + 1;
             vector_qword < 16;
             vector_qword++) {{
            int all_valid = 1;
            for (uintptr_t index = 0; index < observed_length; index++) {{
                uintptr_t element = 0;
                if (!read_exact(
                        array_object + (uintptr_t)vector_qword * 8u + index * 8u,
                        &element,
                        sizeof(element)
                    ) || !runtime_object_class_matches(
                        element, expected_element_class
                    )) {{
                    all_valid = 0;
                    break;
                }}
            }}
            if (!all_valid) continue;
            candidates++;
            chosen_count = (uint32_t)observed_length;
            chosen_length = length_qword;
            chosen_vector = vector_qword;
        }}
    }}
    *candidate_count = candidates;
    if (candidates != 1) return 0;
    *selected_count = chosen_count;
    *selected_length_qword = chosen_length;
    *selected_vector_qword = chosen_vector;
    return 1;
}}

static int copy_managed_reference_array(
    const alpha_reflection_scan *scan,
    uintptr_t array_object,
    uintptr_t expected_element_class,
    uint32_t maximum_count,
    uintptr_t **elements,
    uint32_t *element_count
) {{
    uintptr_t observed_length = 0;
    uintptr_t *copy = NULL;
    if (!scan || !array_object || !expected_element_class ||
        !maximum_count || !elements || !element_count ||
        scan->assembly_array_length_qword >= 16 ||
        scan->assembly_array_vector_qword >= 16 ||
        scan->assembly_array_vector_qword <= scan->assembly_array_length_qword ||
        memory_pointer_kind(array_object) != 1 ||
        !read_exact(
            array_object +
                (uintptr_t)scan->assembly_array_length_qword * 8u,
            &observed_length,
            sizeof(observed_length)
        ) || observed_length > maximum_count)
        return 0;
    if (observed_length) {{
        copy = (uintptr_t *)calloc((SIZE_T)observed_length, sizeof(uintptr_t));
        if (!copy || !read_exact(
                array_object +
                    (uintptr_t)scan->assembly_array_vector_qword * 8u,
                copy,
                (SIZE_T)observed_length * sizeof(uintptr_t)
            )) {{
            free(copy);
            return 0;
        }}
        for (uintptr_t index = 0; index < observed_length; index++) {{
            if (!runtime_object_class_matches(
                    copy[index], expected_element_class
                )) {{
                free(copy);
                return 0;
            }}
        }}
    }}
    *elements = copy;
    *element_count = (uint32_t)observed_length;
    return 1;
}}

static int collect_runtime_type_slice(alpha_reflection_scan *scan) {{
    uint32_t domain_operation = 0, assemblies_operation = 0;
    uint32_t assembly_types_operation = 0, runtime_type_operation = 0;
    uint32_t assembly_full_name_operation = 0;
    uintptr_t assembly_count = 0, assembly_object = 0;
    if (!scan || managed_slice_index >= scan->assembly_count ||
        managed_slice_types || managed_slice_type_count ||
        !inventory_operation_slot("domain.current", &domain_operation) ||
        !inventory_operation_slot("domain.assemblies", &assemblies_operation) ||
        !inventory_operation_slot("assembly.types", &assembly_types_operation) ||
        !inventory_operation_slot(
            "assembly.full_name", &assembly_full_name_operation
        ) ||
        !inventory_operation_slot("type.fields", &runtime_type_operation) ||
        scan->inventory_arity_operation_candidate_count[domain_operation] != 1 ||
        scan->inventory_arity_operation_candidate_count[assemblies_operation] != 1 ||
        scan->inventory_arity_operation_candidate_count[assembly_types_operation] != 1 ||
        scan->inventory_arity_operation_candidate_count[assembly_full_name_operation] != 1 ||
        scan->inventory_arity_operation_candidate_count[runtime_type_operation] != 1)
        return 0;
    alpha_static_noarg_method current_domain =
        (alpha_static_noarg_method)
            scan->inventory_arity_operation_pointer[domain_operation];
    uintptr_t domain_object = current_domain(
        scan->inventory_arity_operation_metadata[domain_operation]
    );
    if (!runtime_object_class_matches(
            domain_object,
            scan->inventory_arity_operation_class[domain_operation]
        ))
        return 0;
    alpha_instance_noarg_method get_assemblies =
        (alpha_instance_noarg_method)
            scan->inventory_arity_operation_pointer[assemblies_operation];
    uintptr_t assembly_array = get_assemblies(
        domain_object,
        scan->inventory_arity_operation_metadata[assemblies_operation]
    );
    if (!assembly_array || !read_exact(
            assembly_array +
                (uintptr_t)scan->assembly_array_length_qword * 8u,
            &assembly_count,
            sizeof(assembly_count)
        ) || assembly_count != scan->assembly_count ||
        !read_exact(
            assembly_array +
                (uintptr_t)scan->assembly_array_vector_qword * 8u +
                (uintptr_t)managed_slice_index * 8u,
            &assembly_object,
            sizeof(assembly_object)
        ) || !runtime_object_class_matches(
            assembly_object,
            scan->inventory_arity_operation_class[assembly_types_operation]
        ))
        return 0;
    alpha_instance_noarg_method get_types =
        (alpha_instance_noarg_method)
            scan->inventory_arity_operation_pointer[assembly_types_operation];
    uintptr_t type_array = get_types(
        assembly_object,
        scan->inventory_arity_operation_metadata[assembly_types_operation]
    );
    if (!copy_managed_reference_array(
            scan,
            type_array,
            scan->inventory_arity_operation_class[runtime_type_operation],
            200000,
            &managed_slice_types,
            &managed_slice_type_count
        ))
        return 0;
    alpha_instance_noarg_method get_full_name =
        (alpha_instance_noarg_method)
            scan->inventory_arity_operation_pointer[assembly_full_name_operation];
    uintptr_t full_name = get_full_name(
        assembly_object,
        scan->inventory_arity_operation_metadata[assembly_full_name_operation]
    );
    managed_slice_assembly_full_name = copy_runtime_managed_utf8(
        full_name, scan->string_class, 0
    );
    if (!managed_slice_assembly_full_name) {{
        free(managed_slice_types);
        managed_slice_types = NULL;
        managed_slice_type_count = 0;
        return 0;
    }}
    return 1;
}}

static void clear_managed_type_identity(void) {{
    free(managed_type_identity.name);
    free(managed_type_identity.namespace_name);
    free(managed_type_identity.interfaces);
    free(managed_type_identity.generic_arguments);
    memset(&managed_type_identity, 0, sizeof(managed_type_identity));
}}

static void clear_managed_type_graph_state(void) {{
    free(managed_type_graph_extra.constraints);
    memset(&managed_type_graph_extra, 0, sizeof(managed_type_graph_extra));
    free(managed_type_graph_node.values);
    memset(&managed_type_graph_node, 0, sizeof(managed_type_graph_node));
    free(managed_type_native.values);
    memset(&managed_type_native, 0, sizeof(managed_type_native));
    free(managed_type_references);
    managed_type_references = NULL;
    managed_type_reference_count = 0;
    managed_type_reference_capacity = 0;
}}

static int append_managed_type_reference(uintptr_t value) {{
    if (!value || value & (sizeof(uintptr_t) - 1u) ||
        managed_type_reference_count >= ALPHA_MAX_TYPE_GRAPH_NODES)
        return 0;
    if (managed_type_reference_count == managed_type_reference_capacity) {{
        uint32_t capacity = managed_type_reference_capacity
            ? managed_type_reference_capacity * 2u : 64u;
        if (capacity < managed_type_reference_capacity ||
            capacity > ALPHA_MAX_TYPE_GRAPH_NODES)
            capacity = (uint32_t)ALPHA_MAX_TYPE_GRAPH_NODES;
        uintptr_t *resized = (uintptr_t *)realloc(
            managed_type_references,
            (SIZE_T)capacity * sizeof(uintptr_t)
        );
        if (!resized) return 0;
        managed_type_references = resized;
        managed_type_reference_capacity = capacity;
    }}
    managed_type_references[managed_type_reference_count++] = value;
    return 1;
}}

static int append_managed_type_graph_bytes(
    const void *value,
    uint64_t bytes
) {{
    if ((!value && bytes) || bytes > 1024ull * 1024ull ||
        managed_type_graph_node.count > 1024ull * 1024ull - bytes)
        return 0;
    uint64_t required = managed_type_graph_node.count + bytes;
    if (required > managed_type_graph_node.capacity) {{
        uint64_t capacity = managed_type_graph_node.capacity
            ? managed_type_graph_node.capacity : 4096;
        while (capacity < required) capacity *= 2u;
        unsigned char *resized = (unsigned char *)realloc(
            managed_type_graph_node.values, (SIZE_T)capacity
        );
        if (!resized) return 0;
        managed_type_graph_node.values = resized;
        managed_type_graph_node.capacity = capacity;
    }}
    if (bytes) memcpy(
        managed_type_graph_node.values + managed_type_graph_node.count,
        value,
        (SIZE_T)bytes
    );
    managed_type_graph_node.count = required;
    return 1;
}}

static int append_managed_type_native_bytes(
    const void *value,
    uint64_t bytes
) {{
    if ((!value && bytes) || bytes > ALPHA_TYPE_NATIVE_ENTRY_BYTES ||
        managed_type_native.count > ALPHA_TYPE_NATIVE_ENTRY_BYTES - bytes)
        return 0;
    uint64_t required = managed_type_native.count + bytes;
    if (required > managed_type_native.capacity) {{
        unsigned char *resized = (unsigned char *)realloc(
            managed_type_native.values, ALPHA_TYPE_NATIVE_ENTRY_BYTES
        );
        if (!resized) return 0;
        managed_type_native.values = resized;
        managed_type_native.capacity = ALPHA_TYPE_NATIVE_ENTRY_BYTES;
    }}
    if (bytes) memcpy(
        managed_type_native.values + managed_type_native.count,
        value,
        (SIZE_T)bytes
    );
    managed_type_native.count = required;
    return 1;
}}

static int resolve_runtime_type_handle(
    alpha_reflection_scan *scan,
    uintptr_t type_object,
    uint32_t handle_operation,
    uint32_t from_handle_operation,
    uintptr_t *type_handle
);

static int collect_runtime_type_native(
    alpha_reflection_scan *scan,
    uintptr_t type_object
) {{
    uint32_t handle_operation = 0, from_handle_operation = 0;
    uintptr_t type_handle = 0;
    if (!scan || !type_object ||
        !inventory_operation_slot("type.handle", &handle_operation) ||
        !inventory_operation_slot("type.from_handle", &from_handle_operation) ||
        !resolve_runtime_type_handle(
            scan, type_object, handle_operation, from_handle_operation,
            &type_handle
        ) || !append_managed_type_native_bytes(
            &type_object, sizeof(type_object)
        ) || !append_managed_type_native_bytes(
            &type_handle, sizeof(type_handle)
        ) || managed_type_native.count != ALPHA_TYPE_NATIVE_ENTRY_BYTES)
        return 0;
    scan->type_native_node_count++;
    return 1;
}}

static int collect_runtime_type_identity(
    alpha_reflection_scan *scan,
    uintptr_t type_object,
    uintptr_t runtime_type_class
) {{
    static const char *keys[] = {{
        "type.name",
        "type.namespace",
        "type.attributes",
        "type.is_enum",
        "type.is_value_type",
        "type.is_generic",
        "type.is_generic_definition",
        "type.is_byref",
        "type.base_type",
        "type.declaring_type",
        "type.interfaces",
        "type.generic_arguments",
        "type.element_type",
        "type.generic_definition"
    }};
    uint32_t operations[sizeof(keys) / sizeof(keys[0])] = {{0}};
    if (!scan || !runtime_object_class_matches(
            type_object, runtime_type_class
        ))
        return 0;
    clear_managed_type_identity();
    for (uint32_t index = 0;
         index < sizeof(keys) / sizeof(keys[0]);
         index++) {{
        if (!reflection_operation_slot(keys[index], &operations[index]) ||
            scan->runtime_arity_operation_candidate_count[
                operations[index]
            ] != 1)
            return 0;
    }}
    alpha_instance_noarg_method name_method =
        (alpha_instance_noarg_method)
            scan->runtime_arity_operation_pointer[operations[0]];
    alpha_instance_noarg_method namespace_method =
        (alpha_instance_noarg_method)
            scan->runtime_arity_operation_pointer[operations[1]];
    uintptr_t name_object = name_method(
        type_object,
        scan->runtime_arity_operation_metadata[operations[0]]
    );
    uintptr_t namespace_object = namespace_method(
        type_object,
        scan->runtime_arity_operation_metadata[operations[1]]
    );
    managed_type_identity.name = copy_runtime_managed_utf8(
        name_object, scan->string_class, 0
    );
    managed_type_identity.namespace_name = copy_runtime_managed_utf8(
        namespace_object, scan->string_class, 1
    );
    if (!managed_type_identity.name ||
        !managed_type_identity.namespace_name)
        goto failed;
    alpha_instance_dword_method attributes_method =
        (alpha_instance_dword_method)
            scan->runtime_arity_operation_pointer[operations[2]];
    managed_type_identity.attributes = attributes_method(
        type_object,
        scan->runtime_arity_operation_metadata[operations[2]]
    );
    for (uint32_t index = 3; index <= 7; index++) {{
        alpha_instance_bool_method boolean_method =
            (alpha_instance_bool_method)
                scan->runtime_arity_operation_pointer[operations[index]];
        uint8_t value = boolean_method(
            type_object,
            scan->runtime_arity_operation_metadata[operations[index]]
        );
        if (value > 1) goto failed;
        if (!value) continue;
        managed_type_identity.shape |= (uint32_t[]){{
            ALPHA_TYPE_SHAPE_ENUM,
            ALPHA_TYPE_SHAPE_VALUE_TYPE,
            ALPHA_TYPE_SHAPE_GENERIC,
            ALPHA_TYPE_SHAPE_GENERIC_DEFINITION,
            ALPHA_TYPE_SHAPE_BYREF
        }}[index - 3];
    }}
    if (managed_type_identity.attributes & ALPHA_TYPE_ATTRIBUTE_INTERFACE)
        managed_type_identity.shape |= ALPHA_TYPE_SHAPE_INTERFACE;
    if ((managed_type_identity.shape & ALPHA_TYPE_SHAPE_GENERIC_DEFINITION) &&
        !(managed_type_identity.shape & ALPHA_TYPE_SHAPE_GENERIC))
        goto failed;
    uintptr_t *single_references[] = {{
        &managed_type_identity.base_type,
        &managed_type_identity.declaring_type,
        &managed_type_identity.element_type
    }};
    uint32_t single_reference_operations[] = {{8, 9, 12}};
    for (uint32_t index = 0; index < 3; index++) {{
        alpha_instance_noarg_method reference_method =
            (alpha_instance_noarg_method)
                scan->runtime_arity_operation_pointer[
                    operations[single_reference_operations[index]]
                ];
        *single_references[index] = reference_method(
            type_object,
            scan->runtime_arity_operation_metadata[
                operations[single_reference_operations[index]]
            ]
        );
        if (*single_references[index] && !runtime_object_class_matches(
                *single_references[index], runtime_type_class
            ))
            goto failed;
    }}
    if (managed_type_identity.shape & ALPHA_TYPE_SHAPE_GENERIC) {{
        alpha_instance_noarg_method arguments_method =
            (alpha_instance_noarg_method)
                scan->runtime_arity_operation_pointer[operations[11]];
        uintptr_t arguments = arguments_method(
            type_object,
            scan->runtime_arity_operation_metadata[operations[11]]
        );
        if (!copy_managed_reference_array(
                scan,
                arguments,
                runtime_type_class,
                65536,
                &managed_type_identity.generic_arguments,
                &managed_type_identity.generic_argument_count
            ))
            goto failed;
        if (!(managed_type_identity.shape &
                ALPHA_TYPE_SHAPE_GENERIC_DEFINITION)) {{
            alpha_instance_noarg_method definition_method =
                (alpha_instance_noarg_method)
                    scan->runtime_arity_operation_pointer[operations[13]];
            managed_type_identity.generic_definition = definition_method(
                type_object,
                scan->runtime_arity_operation_metadata[operations[13]]
            );
            if (!runtime_object_class_matches(
                    managed_type_identity.generic_definition,
                    runtime_type_class
                ))
                goto failed;
        }}
    }}
    alpha_instance_noarg_method interfaces_method =
        (alpha_instance_noarg_method)
            scan->runtime_arity_operation_pointer[operations[10]];
    uintptr_t interfaces = interfaces_method(
        type_object,
        scan->runtime_arity_operation_metadata[operations[10]]
    );
    if (!copy_managed_reference_array(
            scan,
            interfaces,
            runtime_type_class,
            65536,
            &managed_type_identity.interfaces,
            &managed_type_identity.interface_count
        ))
        goto failed;
    return 1;

failed:
    clear_managed_type_identity();
    return 0;
}}

static int collect_runtime_type_graph_extra(
    alpha_reflection_scan *scan,
    uintptr_t type_object,
    uintptr_t runtime_type_class
) {{
    static const char *keys[7] = {{
        "type.is_generic_parameter",
        "type.generic_parameter_position",
        "type.generic_parameter_attributes",
        "type.generic_parameter_constraints",
        "type.is_array",
        "type.is_pointer",
        "type.array_rank"
    }};
    uint32_t operations[7] = {{0}};
    free(managed_type_graph_extra.constraints);
    memset(&managed_type_graph_extra, 0, sizeof(managed_type_graph_extra));
    if (!scan || !runtime_object_class_matches(
            type_object, runtime_type_class
        ))
        return 0;
    for (uint32_t index = 0; index < 7; index++) {{
        if (!inventory_operation_slot(keys[index], &operations[index]) ||
            scan->inventory_arity_operation_candidate_count[
                operations[index]
            ] != 1 || !scan->inventory_arity_operation_pointer[
                operations[index]
            ] || !scan->inventory_arity_operation_metadata[
                operations[index]
            ])
            return 0;
    }}
    alpha_instance_bool_method shape_method =
        (alpha_instance_bool_method)
            scan->inventory_arity_operation_pointer[operations[0]];
    uint8_t is_parameter = shape_method(
        type_object,
        scan->inventory_arity_operation_metadata[operations[0]]
    );
    if (is_parameter > 1) return 0;
    managed_type_graph_extra.is_generic_parameter = is_parameter;
    for (uint32_t index = 0; index < 2; index++) {{
        alpha_instance_bool_method element_shape_method =
            (alpha_instance_bool_method)
                scan->inventory_arity_operation_pointer[operations[4 + index]];
        uint8_t value = element_shape_method(
            type_object,
            scan->inventory_arity_operation_metadata[operations[4 + index]]
        );
        if (value > 1) return 0;
        if (!index) managed_type_graph_extra.is_array = value;
        else managed_type_graph_extra.is_pointer = value;
    }}
    if (managed_type_graph_extra.is_array) {{
        alpha_instance_dword_method rank_method =
            (alpha_instance_dword_method)
                scan->inventory_arity_operation_pointer[operations[6]];
        managed_type_graph_extra.element_rank = rank_method(
            type_object,
            scan->inventory_arity_operation_metadata[operations[6]]
        );
        if (!managed_type_graph_extra.element_rank ||
            managed_type_graph_extra.element_rank > 32)
            return 0;
    }}
    if (!is_parameter) return 1;
    alpha_instance_dword_method position_method =
        (alpha_instance_dword_method)
            scan->inventory_arity_operation_pointer[operations[1]];
    alpha_instance_dword_method attributes_method =
        (alpha_instance_dword_method)
            scan->inventory_arity_operation_pointer[operations[2]];
    managed_type_graph_extra.position = position_method(
        type_object,
        scan->inventory_arity_operation_metadata[operations[1]]
    );
    managed_type_graph_extra.attributes = attributes_method(
        type_object,
        scan->inventory_arity_operation_metadata[operations[2]]
    );
    alpha_instance_noarg_method constraints_method =
        (alpha_instance_noarg_method)
            scan->inventory_arity_operation_pointer[operations[3]];
    uintptr_t constraints = constraints_method(
        type_object,
        scan->inventory_arity_operation_metadata[operations[3]]
    );
    return copy_managed_reference_array(
        scan,
        constraints,
        runtime_type_class,
        65536,
        &managed_type_graph_extra.constraints,
        &managed_type_graph_extra.constraint_count
    );
}}

static int serialize_runtime_type_graph_node(
    alpha_reflection_scan *scan,
    uintptr_t type_object
) {{
    alpha_type_identity_slice *identity = &managed_type_identity;
    alpha_type_graph_extra *extra = &managed_type_graph_extra;
    if (!type_object || !identity->name || !identity->namespace_name)
        return 0;
    SIZE_T name_size = strlen(identity->name);
    SIZE_T namespace_size = strlen(identity->namespace_name);
    if (!name_size || name_size > 16384 || namespace_size > 16384 ||
        identity->interface_count > 65536 ||
        identity->generic_argument_count > 65536 ||
        extra->constraint_count > 65536)
        return 0;
    uint32_t name_bytes = (uint32_t)name_size;
    uint32_t namespace_bytes = (uint32_t)namespace_size;
    uint32_t shape = identity->shape;
    uint32_t position = ALPHA_NO_GENERIC_PARAMETER_POSITION;
    uint32_t parameter_attributes = 0;
    if (extra->is_generic_parameter) {{
        shape |= ALPHA_TYPE_SHAPE_GENERIC_PARAMETER;
        position = extra->position;
        parameter_attributes = extra->attributes;
    }}
    if (extra->is_array) shape |= ALPHA_TYPE_SHAPE_ARRAY;
    if (extra->is_pointer) shape |= ALPHA_TYPE_SHAPE_POINTER;
    uint32_t element_rank = extra->element_rank;
    uint32_t element_shape_count =
        !!(shape & ALPHA_TYPE_SHAPE_ARRAY) +
        !!(shape & ALPHA_TYPE_SHAPE_POINTER) +
        !!(shape & ALPHA_TYPE_SHAPE_BYREF);
    if (element_shape_count > 1 ||
        (!!element_shape_count != !!identity->element_type) ||
        (!!extra->is_array != !!element_rank))
        return 0;
    uint64_t before = managed_type_graph_node.count;
    int ok = append_managed_type_graph_bytes(
            &type_object, sizeof(type_object)
        ) && append_managed_type_graph_bytes(
            &name_bytes, sizeof(name_bytes)
        ) && append_managed_type_graph_bytes(
            &namespace_bytes, sizeof(namespace_bytes)
        ) && append_managed_type_graph_bytes(
            &identity->attributes, sizeof(identity->attributes)
        ) && append_managed_type_graph_bytes(&shape, sizeof(shape)) &&
        append_managed_type_graph_bytes(&position, sizeof(position)) &&
        append_managed_type_graph_bytes(
            &parameter_attributes, sizeof(parameter_attributes)
        ) && append_managed_type_graph_bytes(
            &identity->interface_count, sizeof(identity->interface_count)
        ) && append_managed_type_graph_bytes(
            &identity->generic_argument_count,
            sizeof(identity->generic_argument_count)
        ) && append_managed_type_graph_bytes(
            &extra->constraint_count, sizeof(extra->constraint_count)
        ) && append_managed_type_graph_bytes(
            &element_rank, sizeof(element_rank)
        ) &&
        append_managed_type_graph_bytes(
            &identity->base_type, sizeof(identity->base_type)
        ) && append_managed_type_graph_bytes(
            &identity->declaring_type, sizeof(identity->declaring_type)
        ) && append_managed_type_graph_bytes(
            &identity->element_type, sizeof(identity->element_type)
        ) && append_managed_type_graph_bytes(
            &identity->generic_definition,
            sizeof(identity->generic_definition)
        ) && managed_type_graph_node.count - before ==
            ALPHA_TYPE_GRAPH_ENTRY_BYTES &&
        append_managed_type_graph_bytes(identity->name, name_size) &&
        (!namespace_size || append_managed_type_graph_bytes(
            identity->namespace_name, namespace_size
        )) && (!identity->interface_count || append_managed_type_graph_bytes(
            identity->interfaces,
            (uint64_t)identity->interface_count * sizeof(uintptr_t)
        )) && (!identity->generic_argument_count ||
            append_managed_type_graph_bytes(
                identity->generic_arguments,
                (uint64_t)identity->generic_argument_count *
                    sizeof(uintptr_t)
            )) && (!extra->constraint_count ||
            append_managed_type_graph_bytes(
                extra->constraints,
                (uint64_t)extra->constraint_count * sizeof(uintptr_t)
            ));
    uintptr_t single_references[4] = {{
        identity->base_type,
        identity->declaring_type,
        identity->element_type,
        identity->generic_definition
    }};
    for (uint32_t index = 0; index < 4 && ok; index++) {{
        if (single_references[index])
            ok = append_managed_type_reference(single_references[index]);
    }}
    for (uint32_t index = 0; index < identity->interface_count && ok; index++)
        ok = append_managed_type_reference(identity->interfaces[index]);
    for (uint32_t index = 0;
         index < identity->generic_argument_count && ok;
         index++)
        ok = append_managed_type_reference(identity->generic_arguments[index]);
    for (uint32_t index = 0; index < extra->constraint_count && ok; index++)
        ok = append_managed_type_reference(extra->constraints[index]);
    return ok && collect_runtime_type_native(scan, type_object);
}}

static void clear_managed_member_buffers(void) {{
    for (uint32_t category = 0;
         category < ALPHA_MEMBER_CATEGORY_COUNT;
         category++) {{
        free(managed_member_arrays[category]);
        managed_member_arrays[category] = NULL;
        managed_member_counts[category] = 0;
    }}
}}

static void clear_managed_member_detail(void) {{
    free(managed_member_detail.values);
    memset(&managed_member_detail, 0, sizeof(managed_member_detail));
}}

static int append_managed_member_detail(
    const void *value,
    uint64_t bytes
) {{
    if ((!value && bytes) ||
        bytes > ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES ||
        managed_member_detail.count >
            ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES - bytes)
        return 0;
    uint64_t required = managed_member_detail.count + bytes;
    if (required > managed_member_detail.capacity) {{
        uint64_t capacity = managed_member_detail.capacity
            ? managed_member_detail.capacity : 4096;
        while (capacity < required) {{
            if (capacity > ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES / 2u) {{
                capacity = ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES;
                break;
            }}
            capacity *= 2u;
        }}
        if (capacity < required) return 0;
        unsigned char *resized = (unsigned char *)realloc(
            managed_member_detail.values, (SIZE_T)capacity
        );
        if (!resized) return 0;
        managed_member_detail.values = resized;
        managed_member_detail.capacity = capacity;
    }}
    if (bytes) memcpy(
        managed_member_detail.values + managed_member_detail.count,
        value,
        (SIZE_T)bytes
    );
    managed_member_detail.count = required;
    return 1;
}}

static void clear_managed_method_native(void) {{
    free(managed_method_native.values);
    memset(&managed_method_native, 0, sizeof(managed_method_native));
}}

static int append_managed_method_native(
    const void *value,
    uint64_t bytes
) {{
    if ((!value && bytes) ||
        bytes > ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES ||
        managed_method_native.count >
            ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES - bytes)
        return 0;
    uint64_t required = managed_method_native.count + bytes;
    if (required > managed_method_native.capacity) {{
        uint64_t capacity = managed_method_native.capacity
            ? managed_method_native.capacity : 4096;
        while (capacity < required) {{
            if (capacity > ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES / 2u) {{
                capacity = ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES;
                break;
            }}
            capacity *= 2u;
        }}
        if (capacity < required) return 0;
        unsigned char *resized = (unsigned char *)realloc(
            managed_method_native.values, (SIZE_T)capacity
        );
        if (!resized) return 0;
        managed_method_native.values = resized;
        managed_method_native.capacity = capacity;
    }}
    if (bytes) memcpy(
        managed_method_native.values + managed_method_native.count,
        value,
        (SIZE_T)bytes
    );
    managed_method_native.count = required;
    return 1;
}}

static int runtime_method_metadata_class_membership(
    const alpha_reflection_scan *scan,
    uintptr_t metadata_object,
    uintptr_t *declaring_class
) {{
    uintptr_t class_object = 0, method_array = 0;
    uint16_t method_count = 0;
    uint32_t occurrences = 0;
    if (!scan || !metadata_object || !declaring_class ||
        scan->declaring_class_candidate_count != 1 ||
        scan->method_layout_candidate_count != 1 ||
        scan->declaring_class_qword >
            (UINTPTR_MAX - metadata_object) / sizeof(uintptr_t) ||
        !read_exact(
            metadata_object +
                scan->declaring_class_qword * sizeof(uintptr_t),
            &class_object,
            sizeof(class_object)
        ) || memory_pointer_kind(class_object) != 1 ||
        scan->method_array_pointer_qword >
            (UINTPTR_MAX - class_object) / sizeof(uintptr_t) ||
        !read_exact(
            class_object +
                scan->method_array_pointer_qword * sizeof(uintptr_t),
            &method_array,
            sizeof(method_array)
        ) || memory_pointer_kind(method_array) != 1 ||
        scan->method_count_byte_offset > UINTPTR_MAX - class_object ||
        !read_exact(
            class_object + scan->method_count_byte_offset,
            &method_count,
            sizeof(method_count)
        ) || !method_count)
        return 0;
    for (uint32_t index = 0; index < method_count; index++) {{
        uintptr_t entry = 0;
        if (index > (UINTPTR_MAX - method_array) / sizeof(uintptr_t) ||
            !read_exact(
                method_array + index * sizeof(uintptr_t),
                &entry,
                sizeof(entry)
            ))
            return 0;
        if (entry == metadata_object) occurrences++;
    }}
    if (occurrences != 1) return 0;
    *declaring_class = class_object;
    return 1;
}}

static int derive_runtime_method_slot(
    alpha_reflection_scan *scan,
    uintptr_t metadata_object,
    uint32_t metadata_token,
    uint32_t attributes,
    uint32_t impl_attributes,
    uint32_t parameter_count,
    uint16_t *slot
) {{
    unsigned char sample[ALPHA_METHOD_METADATA_SAMPLE_BYTES];
    unsigned char candidate_offsets[
        ALPHA_METHOD_METADATA_SAMPLE_BYTES / sizeof(uint16_t)
    ];
    if (!scan || !metadata_object || !metadata_token ||
        attributes > 0xffffu || impl_attributes > 0xffffu || !slot ||
        scan->method_parameter_count_byte_offset >= sizeof(sample) ||
        parameter_count > 0xffu || !read_exact(
            metadata_object, sample, sizeof(sample)
        ) || sample[scan->method_parameter_count_byte_offset] != parameter_count)
        return 0;
    memset(candidate_offsets, 0, sizeof(candidate_offsets));
    uint32_t parameter_offset = scan->method_parameter_count_byte_offset;
    for (uint32_t token_offset = 0;
         token_offset + sizeof(uint32_t) <= parameter_offset;
         token_offset += sizeof(uint32_t)) {{
        uint32_t observed_token = 0;
        memcpy(
            &observed_token, sample + token_offset, sizeof(observed_token)
        );
        if (observed_token != metadata_token) continue;
        uint32_t attribute_limit = token_offset + 32u;
        if (attribute_limit > parameter_offset)
            attribute_limit = parameter_offset;
        for (uint32_t attribute_offset = token_offset + sizeof(uint32_t);
             attribute_offset + sizeof(uint16_t) <= attribute_limit;
             attribute_offset += sizeof(uint16_t)) {{
            uint16_t observed_attributes = 0;
            memcpy(
                &observed_attributes, sample + attribute_offset,
                sizeof(observed_attributes)
            );
            if (observed_attributes != (uint16_t)attributes) continue;
            uint32_t implementation_limit = attribute_offset + 16u;
            if (implementation_limit > parameter_offset)
                implementation_limit = parameter_offset;
            for (uint32_t implementation_offset =
                    attribute_offset + sizeof(uint16_t);
                 implementation_offset + sizeof(uint16_t) <=
                    implementation_limit;
                 implementation_offset += sizeof(uint16_t)) {{
                uint16_t observed_implementation = 0;
                memcpy(
                    &observed_implementation,
                    sample + implementation_offset,
                    sizeof(observed_implementation)
                );
                if (observed_implementation != (uint16_t)impl_attributes)
                    continue;
                for (uint32_t slot_offset =
                        implementation_offset + sizeof(uint16_t);
                     slot_offset + sizeof(uint16_t) <= parameter_offset;
                     slot_offset += sizeof(uint16_t)) {{
                    uint16_t observed_slot = 0;
                    memcpy(
                        &observed_slot, sample + slot_offset,
                        sizeof(observed_slot)
                    );
                    int is_virtual =
                        (attributes & ALPHA_METHOD_ATTRIBUTE_VIRTUAL) != 0;
                    if (is_virtual != (observed_slot != 0xffffu)) continue;
                    candidate_offsets[slot_offset / sizeof(uint16_t)] = 1;
                }}
            }}
        }}
    }}
    uint32_t match_count = 0;
    uint32_t selected_offset = 0;
    for (uint32_t index = 0;
         index < sizeof(candidate_offsets); index++) {{
        if (!candidate_offsets[index]) continue;
        match_count++;
        selected_offset = index * sizeof(uint16_t);
    }}
    if (match_count != 1u || !selected_offset) return 0;
    if (scan->method_native_slot_layout_unique) {{
        if (scan->method_native_slot_byte_offset != selected_offset) return 0;
    }} else {{
        scan->method_native_slot_byte_offset = selected_offset;
        scan->method_native_slot_layout_unique = 1;
    }}
    memcpy(slot, sample + selected_offset, sizeof(*slot));
    return 1;
}}

static int append_runtime_method_native(
    alpha_reflection_scan *scan,
    uintptr_t member_object,
    const char *expected_name,
    uint32_t expected_parameter_count,
    uint32_t metadata_token,
    uint32_t attributes,
    uint32_t impl_attributes
) {{
    uintptr_t selected_metadata = 0;
    uintptr_t selected_method_pointer = 0;
    uint32_t distinct_candidate_count = 0;
    SIZE_T name_bytes = expected_name ? strlen(expected_name) : 0;
    char *observed_name = NULL;
    if (!scan || !member_object || !name_bytes || name_bytes > 16384 ||
        expected_parameter_count > ALPHA_MAX_METHOD_PARAMETER_COUNT ||
        !scan->method_parameter_count_observation_complete ||
        scan->method_pointer_candidate_count != 1)
        return 0;
    observed_name = (char *)malloc(name_bytes + 1u);
    if (!observed_name) return 0;
    for (uint32_t field = 0;
         field < ALPHA_METHOD_METADATA_OBJECT_SCAN_QWORDS;
         field++) {{
        uintptr_t metadata_object = 0;
        uintptr_t declaring_class = 0;
        uintptr_t method_pointer = 0;
        unsigned char parameter_count = 0;
        memset(observed_name, 0, name_bytes + 1u);
        if (field > (UINTPTR_MAX - member_object) / sizeof(uintptr_t) ||
            !read_exact(
                member_object + field * sizeof(uintptr_t),
                &metadata_object,
                sizeof(metadata_object)
            ) || !metadata_object || (metadata_object & 7u) ||
            memory_pointer_kind(metadata_object) != 1 ||
            metadata_object == selected_metadata ||
            !probe_runtime_method_name(
                scan,
                metadata_object,
                observed_name,
                name_bytes + 1u
            ) || strcmp(observed_name, expected_name) ||
            scan->method_parameter_count_byte_offset >
                UINTPTR_MAX - metadata_object ||
            !read_exact(
                metadata_object +
                    scan->method_parameter_count_byte_offset,
                &parameter_count,
                sizeof(parameter_count)
            ) || parameter_count != expected_parameter_count ||
            !runtime_method_metadata_class_membership(
                scan, metadata_object, &declaring_class
            ) || !declaring_class ||
            scan->method_pointer_qword >
                (UINTPTR_MAX - metadata_object) / sizeof(uintptr_t) ||
            !read_exact(
                metadata_object +
                    scan->method_pointer_qword * sizeof(uintptr_t),
                &method_pointer,
                sizeof(method_pointer)
            ) || (method_pointer &&
                !current_image_executable_pointer(method_pointer)))
            continue;
        distinct_candidate_count++;
        selected_metadata = metadata_object;
        selected_method_pointer = method_pointer;
    }}
    free(observed_name);
    if (distinct_candidate_count != 1 || !selected_metadata) return 0;
    uintptr_t image_base = 0;
    uint64_t image_bytes = 0;
    uint32_t rva = 0, serialized_slot = 0;
    uint16_t slot = 0;
    if (!current_image_bounds(&image_base, &image_bytes)) return 0;
    if (selected_method_pointer) {{
        uint64_t distance = selected_method_pointer - image_base;
        if (selected_method_pointer < image_base || !distance ||
            distance >= image_bytes || distance > UINT32_MAX)
            return 0;
        rva = (uint32_t)distance;
    }}
    if (!derive_runtime_method_slot(
            scan, selected_metadata, metadata_token, attributes,
            impl_attributes, expected_parameter_count, &slot
        )) return 0;
    serialized_slot = slot;
    if (!append_managed_method_native(
            &member_object, sizeof(member_object)
        ) || !append_managed_method_native(
            &selected_metadata, sizeof(selected_metadata)
        ) || !append_managed_method_native(
            &selected_method_pointer, sizeof(selected_method_pointer)
        ) || !append_managed_method_native(&rva, sizeof(rva)) ||
        !append_managed_method_native(
            &serialized_slot, sizeof(serialized_slot)
        ))
        return 0;
    scan->method_native_method_count++;
    if (selected_method_pointer) scan->method_native_executable_count++;
    return 1;
}}

static void clear_managed_field_native(void) {{
    free(managed_field_native.values);
    memset(&managed_field_native, 0, sizeof(managed_field_native));
}}

static int append_managed_field_native(
    const void *value,
    uint64_t bytes
) {{
    if ((!value && bytes) ||
        bytes > ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES ||
        managed_field_native.count >
            ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES - bytes)
        return 0;
    uint64_t required = managed_field_native.count + bytes;
    if (required > managed_field_native.capacity) {{
        uint64_t capacity = managed_field_native.capacity
            ? managed_field_native.capacity : 4096;
        while (capacity < required) {{
            if (capacity > ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES / 2u) {{
                capacity = ALPHA_MAX_MEMBER_DETAIL_SLICE_BYTES;
                break;
            }}
            capacity *= 2u;
        }}
        if (capacity < required) return 0;
        unsigned char *resized = (unsigned char *)realloc(
            managed_field_native.values, (SIZE_T)capacity
        );
        if (!resized) return 0;
        managed_field_native.values = resized;
        managed_field_native.capacity = capacity;
    }}
    if (bytes) memcpy(
        managed_field_native.values + managed_field_native.count,
        value,
        (SIZE_T)bytes
    );
    managed_field_native.count = required;
    return 1;
}}

static int runtime_utf8_string_equals(
    uintptr_t address,
    const char *expected,
    SIZE_T expected_bytes
) {{
    if (!address || !expected || !expected_bytes || expected_bytes > 16384)
        return 0;
    for (SIZE_T index = 0; index <= expected_bytes; index++) {{
        unsigned char observed = 0;
        if (!read_exact(address + index, &observed, sizeof(observed)) ||
            observed != (unsigned char)expected[index])
            return 0;
    }}
    return 1;
}}

static int resolve_runtime_type_handle(
    alpha_reflection_scan *scan,
    uintptr_t type_object,
    uint32_t handle_operation,
    uint32_t from_handle_operation,
    uintptr_t *type_handle
) {{
    if (!scan || !type_object || !type_handle ||
        scan->runtime_arity_operation_candidate_count[handle_operation] != 1 ||
        scan->runtime_arity_operation_candidate_count[from_handle_operation] != 1)
        return 0;
    alpha_instance_noarg_method get_handle =
        (alpha_instance_noarg_method)
            scan->runtime_arity_operation_pointer[handle_operation];
    alpha_static_onearg_method from_handle =
        (alpha_static_onearg_method)
            scan->runtime_arity_operation_pointer[from_handle_operation];
    uintptr_t value = get_handle(
        type_object,
        scan->runtime_arity_operation_metadata[handle_operation]
    );
    if (!value || (value & 7u) || memory_pointer_kind(value) != 1)
        return 0;
    uintptr_t roundtrip = from_handle(
        value,
        scan->runtime_arity_operation_metadata[from_handle_operation]
    );
    if (roundtrip != type_object) return 0;
    *type_handle = value;
    return 1;
}}

static int runtime_field_roundtrip_contains_metadata(
    alpha_reflection_scan *scan,
    uintptr_t field_object,
    uintptr_t metadata_object,
    uintptr_t declaring_type_handle,
    uint32_t from_handle_operation
) {{
    uintptr_t expected_class = 0;
    if (!scan || !field_object || !metadata_object ||
        !read_exact(field_object, &expected_class, sizeof(expected_class)) ||
        !expected_class)
        return 0;
    alpha_static_twoarg_method from_handle =
        (alpha_static_twoarg_method)
            scan->runtime_arity_operation_pointer[from_handle_operation];
    uintptr_t roundtrip = from_handle(
        metadata_object,
        declaring_type_handle,
        scan->runtime_arity_operation_metadata[from_handle_operation]
    );
    if (!runtime_object_class_matches(roundtrip, expected_class)) return 0;
    uint32_t matches = 0;
    for (uint32_t qword = 0;
         qword < ALPHA_FIELD_METADATA_OBJECT_SCAN_QWORDS;
         qword++) {{
        uintptr_t value = 0;
        if (qword > (UINTPTR_MAX - roundtrip) / sizeof(uintptr_t) ||
            !read_exact(
                roundtrip + qword * sizeof(uintptr_t),
                &value,
                sizeof(value)
            ))
            return 0;
        if (value == metadata_object) matches++;
    }}
    return matches >= 1;
}}

static int append_runtime_field_native(
    alpha_reflection_scan *scan,
    uintptr_t field_object,
    uintptr_t declaring_type_object,
    uintptr_t field_type_object,
    const char *expected_name,
    uint32_t metadata_token,
    uint32_t attributes,
    const uint32_t operations[24]
) {{
    SIZE_T name_bytes = expected_name ? strlen(expected_name) : 0;
    uintptr_t declaring_type_handle = 0, field_type_handle = 0;
    uintptr_t declaring_values[8] = {{0}};
    alpha_field_native_candidate selected;
    uint32_t distinct_candidate_count = 0;
    memset(&selected, 0, sizeof(selected));
    if (!scan || !field_object || !declaring_type_object ||
        !field_type_object || !name_bytes || name_bytes > 16384 ||
        !resolve_runtime_type_handle(
            scan,
            declaring_type_object,
            operations[22],
            operations[23],
            &declaring_type_handle
        ) || !resolve_runtime_type_handle(
            scan,
            field_type_object,
            operations[22],
            operations[23],
            &field_type_handle
        ) || !read_exact(
            declaring_type_handle,
            declaring_values,
            sizeof(declaring_values)
        ))
        return 0;
    for (uint32_t object_qword = 0;
         object_qword < ALPHA_FIELD_METADATA_OBJECT_SCAN_QWORDS;
         object_qword++) {{
        uintptr_t metadata_object = 0;
        alpha_field_native_candidate candidate;
        memset(&candidate, 0, sizeof(candidate));
        if (object_qword >
                (UINTPTR_MAX - field_object) / sizeof(uintptr_t) ||
            !read_exact(
                field_object + object_qword * sizeof(uintptr_t),
                &metadata_object,
                sizeof(metadata_object)
            ) || !metadata_object || (metadata_object & 7u) ||
            memory_pointer_kind(metadata_object) != 1 ||
            metadata_object == selected.metadata_object ||
            !read_exact(
                metadata_object,
                candidate.metadata_sample,
                sizeof(candidate.metadata_sample)
            ))
            continue;
        uint32_t name_matches = 0, type_matches = 0, parent_matches = 0;
        uint32_t token_matches = 0;
        for (uint32_t qword = 0; qword < 8; qword++) {{
            uintptr_t value = 0;
            memcpy(
                &value,
                candidate.metadata_sample + qword * sizeof(uintptr_t),
                sizeof(value)
            );
            if (memory_pointer_kind(value) == 1 &&
                runtime_utf8_string_equals(
                    value, expected_name, name_bytes
                )) {{
                name_matches++;
                candidate.name_qword_index = qword;
            }}
            if (value == field_type_handle) {{
                type_matches++;
                candidate.type_qword_index = qword;
            }}
            int parent_value_match = 0;
            for (uint32_t handle_qword = 0;
                 handle_qword < 8;
                 handle_qword++) {{
                if (value && value == declaring_values[handle_qword] &&
                    memory_pointer_kind(value) == 1) {{
                    parent_value_match = 1;
                    break;
                }}
            }}
            if (parent_value_match) {{
                parent_matches++;
                candidate.parent_qword_index = qword;
                candidate.declaring_class = value;
            }}
        }}
        for (uint32_t dword = 0; dword < 16; dword++) {{
            uint32_t value = 0;
            memcpy(
                &value,
                candidate.metadata_sample + dword * sizeof(uint32_t),
                sizeof(value)
            );
            if (value == metadata_token) {{
                token_matches++;
                candidate.token_dword_index = dword;
            }}
        }}
        if (name_matches != 1 || type_matches != 1 ||
            parent_matches != 1 || token_matches != 1 ||
            candidate.name_qword_index == candidate.type_qword_index ||
            candidate.name_qword_index == candidate.parent_qword_index ||
            candidate.type_qword_index == candidate.parent_qword_index ||
            candidate.token_dword_index / 2u ==
                candidate.name_qword_index ||
            candidate.token_dword_index / 2u ==
                candidate.type_qword_index ||
            candidate.token_dword_index / 2u ==
                candidate.parent_qword_index ||
            !runtime_field_roundtrip_contains_metadata(
                scan,
                field_object,
                metadata_object,
                declaring_type_handle,
                operations[21]
            ))
            continue;
        candidate.member_object = field_object;
        candidate.metadata_object = metadata_object;
        candidate.type_handle = field_type_handle;
        candidate.declaring_type_object = declaring_type_object;
        candidate.metadata_token = metadata_token;
        candidate.attributes = attributes;
        distinct_candidate_count++;
        selected = candidate;
    }}
    if (distinct_candidate_count != 1 || !selected.metadata_object ||
        !append_managed_field_native(&selected, sizeof(selected)))
        return 0;
    scan->field_native_field_count++;
    return 1;
}}

static int required_detail_reflection_operation(
    const alpha_reflection_scan *scan,
    const char *key,
    uint32_t *operation
) {{
    return scan && reflection_operation_slot(key, operation) &&
        scan->runtime_arity_operation_candidate_count[*operation] == 1 &&
        scan->runtime_arity_operation_pointer[*operation] &&
        scan->runtime_arity_operation_metadata[*operation];
}}

static int required_detail_inventory_operation(
    const alpha_reflection_scan *scan,
    const char *key,
    uint32_t *operation
) {{
    return scan && inventory_operation_slot(key, operation) &&
        scan->inventory_arity_operation_candidate_count[*operation] == 1 &&
        scan->inventory_arity_operation_pointer[*operation] &&
        scan->inventory_arity_operation_metadata[*operation];
}}

static char *invoke_detail_reflection_string(
    alpha_reflection_scan *scan,
    uintptr_t object,
    uint32_t operation
) {{
    alpha_instance_noarg_method method = (alpha_instance_noarg_method)
        scan->runtime_arity_operation_pointer[operation];
    uintptr_t value = method(
        object, scan->runtime_arity_operation_metadata[operation]
    );
    return copy_runtime_managed_utf8(value, scan->string_class, 0);
}}

static char *invoke_detail_inventory_string(
    alpha_reflection_scan *scan,
    uintptr_t object,
    uint32_t operation
) {{
    alpha_instance_noarg_method method = (alpha_instance_noarg_method)
        scan->inventory_arity_operation_pointer[operation];
    uintptr_t value = method(
        object, scan->inventory_arity_operation_metadata[operation]
    );
    return copy_runtime_managed_utf8(value, scan->string_class, 0);
}}

static int append_runtime_field_detail(
    alpha_reflection_scan *scan,
    uintptr_t field_object,
    uintptr_t declaring_type_object,
    uintptr_t runtime_type_class,
    const uint32_t operations[24]
) {{
    char *name = invoke_detail_reflection_string(
        scan, field_object, operations[0]
    );
    if (!name) return 0;
    SIZE_T name_size = strlen(name);
    uint32_t name_bytes = (uint32_t)name_size;
    alpha_instance_dword_method attributes_method =
        (alpha_instance_dword_method)
            scan->runtime_arity_operation_pointer[operations[1]];
    alpha_instance_dword_method token_method =
        (alpha_instance_dword_method)
            scan->runtime_arity_operation_pointer[operations[3]];
    alpha_instance_noarg_method type_method =
        (alpha_instance_noarg_method)
            scan->runtime_arity_operation_pointer[operations[2]];
    uint32_t attributes = attributes_method(
        field_object,
        scan->runtime_arity_operation_metadata[operations[1]]
    );
    uint32_t token = token_method(
        field_object,
        scan->runtime_arity_operation_metadata[operations[3]]
    );
    uint32_t reserved = 0;
    uintptr_t type_object = type_method(
        field_object,
        scan->runtime_arity_operation_metadata[operations[2]]
    );
    uint64_t before = managed_member_detail.count;
    int ok = name_size && name_size <= 16384 &&
        runtime_object_class_matches(type_object, runtime_type_class) &&
        append_runtime_field_native(
            scan,
            field_object,
            declaring_type_object,
            type_object,
            name,
            token,
            attributes,
            operations
        ) &&
        append_managed_type_reference(type_object) &&
        append_managed_member_detail(&field_object, sizeof(field_object)) &&
        append_managed_member_detail(&name_bytes, sizeof(name_bytes)) &&
        append_managed_member_detail(&attributes, sizeof(attributes)) &&
        append_managed_member_detail(&token, sizeof(token)) &&
        append_managed_member_detail(&reserved, sizeof(reserved)) &&
        append_managed_member_detail(&type_object, sizeof(type_object)) &&
        managed_member_detail.count - before ==
            ALPHA_MEMBER_DETAIL_FIELD_BYTES &&
        append_managed_member_detail(name, name_size);
    free(name);
    return ok;
}}

static int append_runtime_parameter_detail(
    alpha_reflection_scan *scan,
    uintptr_t parameter_object,
    uintptr_t runtime_type_class,
    const uint32_t operations[21]
) {{
    char *name = invoke_detail_reflection_string(
        scan, parameter_object, operations[8]
    );
    if (!name) return 0;
    SIZE_T name_size = strlen(name);
    uint32_t name_bytes = (uint32_t)name_size;
    alpha_instance_noarg_method type_method =
        (alpha_instance_noarg_method)
            scan->runtime_arity_operation_pointer[operations[9]];
    uintptr_t type_object = type_method(
        parameter_object,
        scan->runtime_arity_operation_metadata[operations[9]]
    );
    uint32_t flags = 0;
    for (uint32_t index = 0; index < 3; index++) {{
        alpha_instance_bool_method flag_method =
            (alpha_instance_bool_method)
                scan->runtime_arity_operation_pointer[operations[10 + index]];
        uint8_t value = flag_method(
            parameter_object,
            scan->runtime_arity_operation_metadata[operations[10 + index]]
        );
        if (value > 1) {{ free(name); return 0; }}
        if (value) flags |= (uint32_t[]){{
            ALPHA_PARAMETER_DETAIL_IN,
            ALPHA_PARAMETER_DETAIL_OUT,
            ALPHA_PARAMETER_DETAIL_OPTIONAL
        }}[index];
    }}
    uint32_t reserved = 0;
    uint32_t reserved_two = 0;
    uint64_t before = managed_member_detail.count;
    int ok = name_size && name_size <= 16384 &&
        runtime_object_class_matches(type_object, runtime_type_class) &&
        append_managed_type_reference(type_object) &&
        append_managed_member_detail(
            &parameter_object, sizeof(parameter_object)
        ) && append_managed_member_detail(&name_bytes, sizeof(name_bytes)) &&
        append_managed_member_detail(&flags, sizeof(flags)) &&
        append_managed_member_detail(&reserved, sizeof(reserved)) &&
        append_managed_member_detail(
            &reserved_two, sizeof(reserved_two)
        ) && append_managed_member_detail(&type_object, sizeof(type_object)) &&
        managed_member_detail.count - before ==
            ALPHA_MEMBER_DETAIL_PARAMETER_BYTES &&
        append_managed_member_detail(name, name_size);
    free(name);
    return ok;
}}

static int append_runtime_method_detail(
    alpha_reflection_scan *scan,
    uintptr_t method_object,
    int constructor,
    uintptr_t runtime_type_class,
    uintptr_t parameter_class,
    const uint32_t reflection_operations[21],
    const uint32_t inventory_operations[9]
) {{
    char *name = constructor
        ? invoke_detail_inventory_string(
            scan, method_object, inventory_operations[0]
        )
        : invoke_detail_reflection_string(
            scan, method_object, reflection_operations[4]
        );
    if (!name) return 0;
    SIZE_T name_size = strlen(name);
    uint32_t name_bytes = (uint32_t)name_size;
    uint32_t attributes = 0;
    if (constructor) {{
        alpha_instance_dword_method attributes_method =
            (alpha_instance_dword_method)
                scan->inventory_arity_operation_pointer[
                    inventory_operations[2]
                ];
        attributes = attributes_method(
            method_object,
            scan->inventory_arity_operation_metadata[
                inventory_operations[2]
            ]
        );
    }} else {{
        alpha_instance_dword_method attributes_method =
            (alpha_instance_dword_method)
                scan->runtime_arity_operation_pointer[
                    reflection_operations[7]
                ];
        attributes = attributes_method(
            method_object,
            scan->runtime_arity_operation_metadata[
                reflection_operations[7]
            ]
        );
    }}
    uint32_t impl_attributes = 0;
    uint32_t impl_operation = constructor
        ? inventory_operations[3] : inventory_operations[5];
    alpha_instance_dword_method implementation_method =
        (alpha_instance_dword_method)
            scan->inventory_arity_operation_pointer[impl_operation];
    impl_attributes = implementation_method(
        method_object,
        scan->inventory_arity_operation_metadata[impl_operation]
    );
    if (impl_attributes > 0xffffu) {{
        free(name);
        return 0;
    }}
    alpha_instance_dword_method token_method =
        (alpha_instance_dword_method)
            scan->runtime_arity_operation_pointer[reflection_operations[3]];
    uint32_t token = token_method(
        method_object,
        scan->runtime_arity_operation_metadata[reflection_operations[3]]
    );
    uintptr_t return_type = 0;
    if (!constructor) {{
        alpha_instance_noarg_method return_method =
            (alpha_instance_noarg_method)
                scan->runtime_arity_operation_pointer[
                    reflection_operations[6]
                ];
        return_type = return_method(
            method_object,
            scan->runtime_arity_operation_metadata[
                reflection_operations[6]
            ]
        );
        if (!runtime_object_class_matches(return_type, runtime_type_class)) {{
            free(name);
            return 0;
        }}
    }}
    alpha_instance_noarg_method parameter_method =
        constructor
        ? (alpha_instance_noarg_method)
            scan->inventory_arity_operation_pointer[inventory_operations[1]]
        : (alpha_instance_noarg_method)
            scan->runtime_arity_operation_pointer[reflection_operations[5]];
    uintptr_t parameter_array = parameter_method(
        method_object,
        constructor
            ? scan->inventory_arity_operation_metadata[inventory_operations[1]]
            : scan->runtime_arity_operation_metadata[reflection_operations[5]]
    );
    uintptr_t *parameters = NULL;
    uint32_t parameter_count = 0;
    if (!copy_managed_reference_array(
            scan,
            parameter_array,
            parameter_class,
            65536,
            &parameters,
            &parameter_count
        )) {{
        free(name);
        return 0;
    }}
    uint32_t detail_flags = constructor
        ? ALPHA_METHOD_DETAIL_CONSTRUCTOR : 0;
    uintptr_t generic_definition = 0;
    uintptr_t *generic_arguments = NULL;
    uint32_t generic_argument_count = 0;
    if (!constructor) {{
        alpha_instance_bool_method generic_method =
            (alpha_instance_bool_method)
                scan->inventory_arity_operation_pointer[
                    inventory_operations[6]
                ];
        alpha_instance_bool_method definition_shape_method =
            (alpha_instance_bool_method)
                scan->inventory_arity_operation_pointer[
                    inventory_operations[7]
                ];
        uint8_t is_generic = generic_method(
            method_object,
            scan->inventory_arity_operation_metadata[inventory_operations[6]]
        );
        uint8_t is_definition = definition_shape_method(
            method_object,
            scan->inventory_arity_operation_metadata[inventory_operations[7]]
        );
        if (is_generic > 1 || is_definition > 1 ||
            (is_definition && !is_generic)) {{
            free(parameters);
            free(name);
            return 0;
        }}
        if (is_generic) {{
            detail_flags |= ALPHA_METHOD_DETAIL_GENERIC;
            if (is_definition)
                detail_flags |= ALPHA_METHOD_DETAIL_GENERIC_DEFINITION;
            alpha_instance_noarg_method arguments_method =
                (alpha_instance_noarg_method)
                    scan->inventory_arity_operation_pointer[
                        inventory_operations[4]
                    ];
            uintptr_t arguments_array = arguments_method(
                method_object,
                scan->inventory_arity_operation_metadata[
                    inventory_operations[4]
                ]
            );
            if (!copy_managed_reference_array(
                    scan,
                    arguments_array,
                    runtime_type_class,
                    65536,
                    &generic_arguments,
                    &generic_argument_count
                ) || !generic_argument_count) {{
                free(generic_arguments);
                free(parameters);
                free(name);
                return 0;
            }}
            if (is_definition) {{
                generic_definition = method_object;
            }} else {{
                alpha_instance_noarg_method definition_method =
                    (alpha_instance_noarg_method)
                        scan->inventory_arity_operation_pointer[
                            inventory_operations[8]
                        ];
                generic_definition = definition_method(
                    method_object,
                    scan->inventory_arity_operation_metadata[
                        inventory_operations[8]
                    ]
                );
                if (!runtime_object_class_matches(
                        generic_definition,
                        scan->inventory_arity_operation_class[
                            inventory_operations[8]
                        ]
                    )) {{
                    free(generic_arguments);
                    free(parameters);
                    free(name);
                    return 0;
                }}
            }}
        }}
    }}
    uint64_t before = managed_member_detail.count;
    int ok = name_size && name_size <= 16384 &&
        append_runtime_method_native(
            scan, method_object, name, parameter_count, token, attributes,
            impl_attributes
        ) &&
        (constructor || append_managed_type_reference(return_type)) &&
        append_managed_member_detail(&method_object, sizeof(method_object)) &&
        append_managed_member_detail(&name_bytes, sizeof(name_bytes)) &&
        append_managed_member_detail(&attributes, sizeof(attributes)) &&
        append_managed_member_detail(
            &impl_attributes, sizeof(impl_attributes)
        ) &&
        append_managed_member_detail(&token, sizeof(token)) &&
        append_managed_member_detail(&detail_flags, sizeof(detail_flags)) &&
        append_managed_member_detail(&return_type, sizeof(return_type)) &&
        append_managed_member_detail(
            &generic_definition, sizeof(generic_definition)
        ) && append_managed_member_detail(
            &parameter_count, sizeof(parameter_count)
        ) && append_managed_member_detail(
            &generic_argument_count, sizeof(generic_argument_count)
        ) && managed_member_detail.count - before ==
            ALPHA_MEMBER_DETAIL_METHOD_BYTES &&
        append_managed_member_detail(name, name_size);
    for (uint32_t index = 0; index < parameter_count && ok; index++)
        ok = append_runtime_parameter_detail(
            scan,
            parameters[index],
            runtime_type_class,
            reflection_operations
        );
    if (ok && generic_argument_count)
        ok = append_managed_member_detail(
            generic_arguments,
            (uint64_t)generic_argument_count * sizeof(uintptr_t)
        );
    for (uint32_t index = 0; index < generic_argument_count && ok; index++)
        ok = append_managed_type_reference(generic_arguments[index]);
    free(generic_arguments);
    free(parameters);
    free(name);
    return ok;
}}

static int append_runtime_property_detail(
    alpha_reflection_scan *scan,
    uintptr_t property_object,
    uintptr_t method_class,
    const uint32_t operations[21]
) {{
    char *name = invoke_detail_reflection_string(
        scan, property_object, operations[13]
    );
    if (!name) return 0;
    SIZE_T name_size = strlen(name);
    uint32_t name_bytes = (uint32_t)name_size;
    alpha_instance_dword_method token_method =
        (alpha_instance_dword_method)
            scan->runtime_arity_operation_pointer[operations[3]];
    uint32_t token = token_method(
        property_object,
        scan->runtime_arity_operation_metadata[operations[3]]
    );
    alpha_instance_boolarg_method getter_method =
        (alpha_instance_boolarg_method)
            scan->runtime_arity_operation_pointer[operations[14]];
    alpha_instance_boolarg_method setter_method =
        (alpha_instance_boolarg_method)
            scan->runtime_arity_operation_pointer[operations[15]];
    uintptr_t getter = getter_method(
        property_object,
        1,
        scan->runtime_arity_operation_metadata[operations[14]]
    );
    uintptr_t setter = setter_method(
        property_object,
        1,
        scan->runtime_arity_operation_metadata[operations[15]]
    );
    uint32_t reserved = 0;
    uint64_t before = managed_member_detail.count;
    int ok = name_size && name_size <= 16384 && (getter || setter) &&
        (!getter || runtime_object_class_matches(getter, method_class)) &&
        (!setter || runtime_object_class_matches(setter, method_class)) &&
        append_managed_member_detail(
            &property_object, sizeof(property_object)
        ) && append_managed_member_detail(&name_bytes, sizeof(name_bytes)) &&
        append_managed_member_detail(&token, sizeof(token)) &&
        append_managed_member_detail(&reserved, sizeof(reserved)) &&
        append_managed_member_detail(&getter, sizeof(getter)) &&
        append_managed_member_detail(&setter, sizeof(setter)) &&
        managed_member_detail.count - before ==
            ALPHA_MEMBER_DETAIL_PROPERTY_BYTES &&
        append_managed_member_detail(name, name_size);
    free(name);
    return ok;
}}

static int append_runtime_event_detail(
    alpha_reflection_scan *scan,
    uintptr_t event_object,
    uintptr_t runtime_type_class,
    uintptr_t method_class,
    const uint32_t operations[21]
) {{
    char *name = invoke_detail_reflection_string(
        scan, event_object, operations[16]
    );
    if (!name) return 0;
    SIZE_T name_size = strlen(name);
    uint32_t name_bytes = (uint32_t)name_size;
    alpha_instance_dword_method token_method =
        (alpha_instance_dword_method)
            scan->runtime_arity_operation_pointer[operations[3]];
    uint32_t token = token_method(
        event_object,
        scan->runtime_arity_operation_metadata[operations[3]]
    );
    alpha_instance_noarg_method handler_method =
        (alpha_instance_noarg_method)
            scan->runtime_arity_operation_pointer[operations[17]];
    uintptr_t handler_type = handler_method(
        event_object,
        scan->runtime_arity_operation_metadata[operations[17]]
    );
    uintptr_t accessors[3] = {{0}};
    for (uint32_t index = 0; index < 3; index++) {{
        alpha_instance_boolarg_method accessor_method =
            (alpha_instance_boolarg_method)
                scan->runtime_arity_operation_pointer[operations[18 + index]];
        accessors[index] = accessor_method(
            event_object,
            1,
            scan->runtime_arity_operation_metadata[operations[18 + index]]
        );
    }}
    uint32_t reserved = 0;
    uint64_t before = managed_member_detail.count;
    int ok = name_size && name_size <= 16384 &&
        runtime_object_class_matches(handler_type, runtime_type_class) &&
        append_managed_type_reference(handler_type) &&
        (accessors[0] || accessors[1]) &&
        (!accessors[0] || runtime_object_class_matches(
            accessors[0], method_class
        )) && (!accessors[1] || runtime_object_class_matches(
            accessors[1], method_class
        )) && (!accessors[2] || runtime_object_class_matches(
            accessors[2], method_class
        )) && append_managed_member_detail(
            &event_object, sizeof(event_object)
        ) && append_managed_member_detail(&name_bytes, sizeof(name_bytes)) &&
        append_managed_member_detail(&token, sizeof(token)) &&
        append_managed_member_detail(&reserved, sizeof(reserved)) &&
        append_managed_member_detail(&handler_type, sizeof(handler_type)) &&
        append_managed_member_detail(&accessors[0], sizeof(accessors[0])) &&
        append_managed_member_detail(&accessors[1], sizeof(accessors[1])) &&
        append_managed_member_detail(&accessors[2], sizeof(accessors[2])) &&
        managed_member_detail.count - before ==
            ALPHA_MEMBER_DETAIL_EVENT_BYTES &&
        append_managed_member_detail(name, name_size);
    free(name);
    return ok;
}}

static int collect_runtime_member_detail(
    alpha_reflection_scan *scan,
    const uintptr_t expected_classes[ALPHA_MEMBER_CATEGORY_COUNT],
    uintptr_t declaring_type_object
) {{
    static const char *reflection_keys[24] = {{
        "field.name", "field.attributes", "field.type",
        "member.metadata_token", "method.name", "method.parameters",
        "method.return_type", "method.attributes", "parameter.name",
        "parameter.type", "parameter.is_in", "parameter.is_out",
        "parameter.is_optional", "property.name", "property.getter",
        "property.setter", "event.name", "event.handler_type",
        "event.add_method", "event.remove_method", "event.raise_method",
        "field.from_handle", "type.handle", "type.from_handle"
    }};
    static const char *inventory_keys[9] = {{
        "constructor.name", "constructor.parameters",
        "constructor.attributes", "constructor.impl_attributes",
        "method.generic_arguments", "method.impl_attributes",
        "method.is_generic", "method.is_generic_definition",
        "method.generic_definition"
    }};
    uint32_t reflection_operations[24] = {{0}};
    uint32_t inventory_operations[9] = {{0}};
    uintptr_t parameter_class = required_runtime_owner_class(
        scan, "System.Reflection", "MonoParameterInfo"
    );
    clear_managed_member_detail();
    clear_managed_method_native();
    clear_managed_field_native();
    if (!scan || !expected_classes || !declaring_type_object ||
        !parameter_class) return 0;
    for (uint32_t index = 0; index < 24; index++) {{
        if (!required_detail_reflection_operation(
                scan, reflection_keys[index], &reflection_operations[index]
            ))
            goto failed;
    }}
    for (uint32_t index = 0; index < 9; index++) {{
        if (!required_detail_inventory_operation(
                scan, inventory_keys[index], &inventory_operations[index]
            ))
            goto failed;
    }}
    if (!append_managed_member_detail(
            managed_member_counts,
            ALPHA_MEMBER_DETAIL_TYPE_BYTES
        ))
        goto failed;
    for (uint32_t index = 0; index < managed_member_counts[0]; index++) {{
        if (!append_runtime_field_detail(
                scan,
                managed_member_arrays[0][index],
                declaring_type_object,
                expected_classes[5],
                reflection_operations
            ))
            goto failed;
    }}
    for (uint32_t index = 0; index < managed_member_counts[1]; index++) {{
        if (!append_runtime_method_detail(
                scan,
                managed_member_arrays[1][index],
                0,
                expected_classes[5],
                parameter_class,
                reflection_operations,
                inventory_operations
            ))
            goto failed;
    }}
    for (uint32_t index = 0; index < managed_member_counts[2]; index++) {{
        if (!append_runtime_method_detail(
                scan,
                managed_member_arrays[2][index],
                1,
                expected_classes[5],
                parameter_class,
                reflection_operations,
                inventory_operations
            ))
            goto failed;
    }}
    for (uint32_t index = 0; index < managed_member_counts[3]; index++) {{
        if (!append_runtime_property_detail(
                scan,
                managed_member_arrays[3][index],
                expected_classes[1],
                reflection_operations
            ))
            goto failed;
    }}
    for (uint32_t index = 0; index < managed_member_counts[4]; index++) {{
        if (!append_runtime_event_detail(
                scan,
                managed_member_arrays[4][index],
                expected_classes[5],
                expected_classes[1],
                reflection_operations
            ))
            goto failed;
    }}
    return managed_member_detail.count >= ALPHA_MEMBER_DETAIL_TYPE_BYTES;

failed:
    clear_managed_member_detail();
    clear_managed_method_native();
    clear_managed_field_native();
    return 0;
}}

static int collect_runtime_member_slice(alpha_reflection_scan *scan) {{
    static const char *operation_keys[ALPHA_MEMBER_CATEGORY_COUNT] = {{
        "type.fields",
        "type.methods",
        "type.constructors",
        "type.properties",
        "type.events",
        "type.nested_types"
    }};
    static const char *expected_namespaces[ALPHA_MEMBER_CATEGORY_COUNT] = {{
        "System.Reflection",
        "System.Reflection",
        "System.Reflection",
        "System.Reflection",
        "System.Reflection",
        "System"
    }};
    static const char *expected_types[ALPHA_MEMBER_CATEGORY_COUNT] = {{
        "MonoField",
        "MonoMethod",
        "MonoCMethod",
        "MonoProperty",
        "MonoEvent",
        "RuntimeType"
    }};
    uint32_t domain_operation = 0, assemblies_operation = 0;
    uint32_t assembly_types_operation = 0;
    uint32_t member_operations[ALPHA_MEMBER_CATEGORY_COUNT] = {{0}};
    uintptr_t expected_classes[ALPHA_MEMBER_CATEGORY_COUNT] = {{0}};
    uintptr_t assembly_count = 0, type_count = 0;
    uintptr_t assembly_object = 0, type_object = 0;
    managed_graph_type_object = 0;
    clear_managed_type_identity();
    clear_managed_member_detail();
    clear_managed_method_native();
    clear_managed_field_native();
    clear_managed_type_graph_state();
    if (!scan || managed_member_assembly_index >= scan->assembly_count ||
        !inventory_operation_slot("domain.current", &domain_operation) ||
        !inventory_operation_slot("domain.assemblies", &assemblies_operation) ||
        !inventory_operation_slot("assembly.types", &assembly_types_operation) ||
        scan->inventory_arity_operation_candidate_count[domain_operation] != 1 ||
        scan->inventory_arity_operation_candidate_count[assemblies_operation] != 1 ||
        scan->inventory_arity_operation_candidate_count[assembly_types_operation] != 1)
        return 0;
    for (uint32_t category = 0;
         category < ALPHA_MEMBER_CATEGORY_COUNT;
         category++) {{
        if (!inventory_operation_slot(
                operation_keys[category], &member_operations[category]
            ) || scan->inventory_arity_operation_candidate_count[
                member_operations[category]
            ] != 1)
            return 0;
        expected_classes[category] = required_runtime_owner_class(
            scan,
            expected_namespaces[category],
            expected_types[category]
        );
        if (!expected_classes[category]) return 0;
    }}
    alpha_static_noarg_method current_domain =
        (alpha_static_noarg_method)
            scan->inventory_arity_operation_pointer[domain_operation];
    uintptr_t domain_object = current_domain(
        scan->inventory_arity_operation_metadata[domain_operation]
    );
    if (!runtime_object_class_matches(
            domain_object,
            scan->inventory_arity_operation_class[domain_operation]
        ))
        return 0;
    alpha_instance_noarg_method get_assemblies =
        (alpha_instance_noarg_method)
            scan->inventory_arity_operation_pointer[assemblies_operation];
    uintptr_t assembly_array = get_assemblies(
        domain_object,
        scan->inventory_arity_operation_metadata[assemblies_operation]
    );
    if (!assembly_array || !read_exact(
            assembly_array +
                (uintptr_t)scan->assembly_array_length_qword * 8u,
            &assembly_count,
            sizeof(assembly_count)
        ) || assembly_count != scan->assembly_count ||
        !read_exact(
            assembly_array +
                (uintptr_t)scan->assembly_array_vector_qword * 8u +
                (uintptr_t)managed_member_assembly_index * 8u,
            &assembly_object,
            sizeof(assembly_object)
        ) || !runtime_object_class_matches(
            assembly_object,
            scan->inventory_arity_operation_class[assembly_types_operation]
        ))
        return 0;
    alpha_instance_noarg_method get_types =
        (alpha_instance_noarg_method)
            scan->inventory_arity_operation_pointer[assembly_types_operation];
    uintptr_t type_array = get_types(
        assembly_object,
        scan->inventory_arity_operation_metadata[assembly_types_operation]
    );
    if (!type_array || !read_exact(
            type_array +
                (uintptr_t)scan->assembly_array_length_qword * 8u,
            &type_count,
            sizeof(type_count)
        ) || managed_member_type_index >= type_count ||
        !read_exact(
            type_array +
                (uintptr_t)scan->assembly_array_vector_qword * 8u +
                (uintptr_t)managed_member_type_index * 8u,
            &type_object,
            sizeof(type_object)
        ) || !runtime_object_class_matches(
            type_object, expected_classes[5]
        ))
        return 0;
    if (!collect_runtime_type_identity(
            scan, type_object, expected_classes[5]
        ))
        return 0;
    managed_graph_type_object = type_object;
    if (!collect_runtime_type_graph_extra(
            scan, type_object, expected_classes[5]
        ) || !serialize_runtime_type_graph_node(scan, type_object)) {{
        clear_managed_type_identity();
        clear_managed_type_graph_state();
        return 0;
    }}
    for (uint32_t category = 0;
         category < ALPHA_MEMBER_CATEGORY_COUNT;
         category++) {{
        alpha_instance_flags_method get_members =
            (alpha_instance_flags_method)
                scan->inventory_arity_operation_pointer[
                    member_operations[category]
                ];
        uintptr_t member_array = get_members(
            type_object,
            ALPHA_DECLARED_MEMBER_BINDING_FLAGS,
            scan->inventory_arity_operation_metadata[
                member_operations[category]
            ]
        );
        if (!copy_managed_reference_array(
                scan,
                member_array,
                expected_classes[category],
                200000,
                &managed_member_arrays[category],
                &managed_member_counts[category]
        )) {{
            clear_managed_member_buffers();
            clear_managed_type_identity();
            clear_managed_member_detail();
            clear_managed_method_native();
            clear_managed_field_native();
            clear_managed_type_graph_state();
            return 0;
        }}
    }}
    if (!collect_runtime_member_detail(scan, expected_classes, type_object)) {{
        clear_managed_member_buffers();
        clear_managed_type_identity();
        clear_managed_member_detail();
        clear_managed_method_native();
        clear_managed_field_native();
        clear_managed_type_graph_state();
        return 0;
    }}
    return 1;
}}

static int collect_runtime_type_graph_slice(alpha_reflection_scan *scan) {{
    uintptr_t runtime_type_class = required_runtime_owner_class(
        scan, "System", "RuntimeType"
    );
    clear_managed_type_identity();
    clear_managed_type_graph_state();
    if (!scan || !managed_graph_type_object || !runtime_type_class ||
        !collect_runtime_type_identity(
            scan, managed_graph_type_object, runtime_type_class
        ) || !collect_runtime_type_graph_extra(
            scan, managed_graph_type_object, runtime_type_class
        ) || !serialize_runtime_type_graph_node(
            scan, managed_graph_type_object
        )) {{
        clear_managed_type_identity();
        clear_managed_type_graph_state();
        return 0;
    }}
    return 1;
}}

static LRESULT CALLBACK managed_thread_probe(
    int code,
    WPARAM parameter,
    LPARAM data
) {{
    (void)parameter;
    MSG *message = (MSG *)(uintptr_t)data;
    alpha_reflection_scan *scan = managed_probe_reflection;
    if (code == HC_ACTION && message && scan && managed_probe_event &&
        message->message == managed_probe_message &&
        InterlockedCompareExchange(&managed_probe_state, 1, 0) == 0) {{
        if (managed_probe_mode == 4) {{
            int slice_complete = collect_runtime_type_graph_slice(scan);
            InterlockedExchange(
                &managed_probe_state, slice_complete ? 2 : -1
            );
            SetEvent(managed_probe_event);
            return CallNextHookEx(
                managed_probe_hook, code, parameter, data
            );
        }}
        if (managed_probe_mode == 3) {{
            int slice_complete = collect_runtime_member_slice(scan);
            if (slice_complete)
                scan->member_inventory_completed_slice_count++;
            InterlockedExchange(
                &managed_probe_state, slice_complete ? 2 : -1
            );
            SetEvent(managed_probe_event);
            return CallNextHookEx(
                managed_probe_hook, code, parameter, data
            );
        }}
        if (managed_probe_mode == 2) {{
            int slice_complete = collect_runtime_type_slice(scan);
            if (slice_complete)
                scan->type_inventory_completed_slice_count++;
            InterlockedExchange(
                &managed_probe_state, slice_complete ? 2 : -1
            );
            SetEvent(managed_probe_event);
            return CallNextHookEx(
                managed_probe_hook, code, parameter, data
            );
        }}
        uint32_t thread_operation = 0, domain_operation = 0;
        uint32_t assemblies_operation = 0, assembly_types_operation = 0;
        scan->managed_probe_callback_thread_id = GetCurrentThreadId();
        if (scan->managed_probe_callback_thread_id ==
                scan->managed_window_thread_id &&
            inventory_operation_slot("thread.current", &thread_operation) &&
            inventory_operation_slot("domain.current", &domain_operation) &&
            inventory_operation_slot(
                "domain.assemblies", &assemblies_operation
            ) &&
            inventory_operation_slot(
                "assembly.types", &assembly_types_operation
            ) &&
            scan->inventory_arity_operation_candidate_count[thread_operation] == 1 &&
            scan->inventory_arity_operation_candidate_count[domain_operation] == 1 &&
            scan->inventory_arity_operation_candidate_count[assemblies_operation] == 1 &&
            scan->inventory_arity_operation_candidate_count[assembly_types_operation] == 1) {{
            alpha_static_noarg_method current_thread =
                (alpha_static_noarg_method)
                    scan->inventory_arity_operation_pointer[thread_operation];
            uintptr_t thread_object = current_thread(
                scan->inventory_arity_operation_metadata[thread_operation]
            );
            scan->managed_thread_object_observed = thread_object != 0;
            scan->managed_thread_class_matches = runtime_object_class_matches(
                thread_object,
                scan->inventory_arity_operation_class[thread_operation]
            );
            if (scan->managed_thread_class_matches) {{
                alpha_static_noarg_method current_domain =
                    (alpha_static_noarg_method)
                        scan->inventory_arity_operation_pointer[domain_operation];
                uintptr_t domain_object = current_domain(
                    scan->inventory_arity_operation_metadata[domain_operation]
                );
                scan->current_domain_object_observed = domain_object != 0;
                scan->current_domain_class_matches = runtime_object_class_matches(
                    domain_object,
                    scan->inventory_arity_operation_class[domain_operation]
                );
                if (scan->current_domain_class_matches) {{
                    scan->current_domain_object = domain_object;
                    alpha_instance_noarg_method get_assemblies =
                        (alpha_instance_noarg_method)
                            scan->inventory_arity_operation_pointer[
                                assemblies_operation
                            ];
                    uintptr_t assembly_array = get_assemblies(
                        domain_object,
                        scan->inventory_arity_operation_metadata[
                            assemblies_operation
                        ]
                    );
                    scan->assembly_array_observed = assembly_array != 0;
                    if (scan->assembly_array_observed &&
                        discover_managed_reference_array(
                            assembly_array,
                            scan->inventory_arity_operation_class[
                                assembly_types_operation
                            ],
                            1024,
                            &scan->assembly_count,
                            &scan->assembly_array_length_qword,
                            &scan->assembly_array_vector_qword,
                            &scan->assembly_array_layout_candidate_count
                        )) {{
                        scan->assembly_array_pointer = assembly_array;
                        scan->assembly_array_layout_unique = 1;
                        scan->all_assembly_objects_class_valid = 1;
                        scan->assembly_root_inventory_complete = 1;
                    }}
                }}
            }}
        }}
        scan->managed_thread_observation_complete =
            scan->managed_thread_object_observed &&
            scan->managed_thread_class_matches &&
            scan->current_domain_object_observed &&
            scan->current_domain_class_matches &&
            scan->assembly_root_inventory_complete;
        InterlockedExchange(
            &managed_probe_state,
            scan->managed_thread_observation_complete ? 2 : -1
        );
        SetEvent(managed_probe_event);
    }}
    return CallNextHookEx(managed_probe_hook, code, parameter, data);
}}

static int observe_managed_thread(alpha_reflection_scan *scan) {{
    alpha_window_selection selection;
    memset(&selection, 0, sizeof(selection));
    if (!scan || !scan->inventory_dispatch_contract_complete) return 0;
    selection.process_id = GetCurrentProcessId();
    if (!EnumWindows(select_managed_window, (LPARAM)(uintptr_t)&selection))
        return 0;
    scan->managed_window_candidate_count = selection.candidate_count;
    scan->managed_window_thread_id = selection.selected_thread_id;
    if (selection.candidate_count != 1 || !selection.selected_window ||
        !selection.selected_thread_id ||
        selection.selected_thread_id == GetCurrentThreadId())
        return 0;
    managed_probe_message = RegisterWindowMessageW(
        L"ALPHA v2 fresh managed runtime inventory probe"
    );
    managed_probe_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    managed_probe_reflection = scan;
    InterlockedExchange(&managed_probe_mode, 1);
    InterlockedExchange(&managed_probe_state, 0);
    if (!managed_probe_message || !managed_probe_event) goto cleanup;
    managed_probe_hook = SetWindowsHookExW(
        WH_GETMESSAGE,
        managed_thread_probe,
        self_module,
        selection.selected_thread_id
    );
    if (!managed_probe_hook || !PostMessageW(
            selection.selected_window, managed_probe_message, 0, 0))
        goto cleanup;
    WaitForSingleObject(managed_probe_event, 15000);

cleanup:
    if (managed_probe_hook) UnhookWindowsHookEx(managed_probe_hook);
    managed_probe_hook = NULL;
    if (managed_probe_event) CloseHandle(managed_probe_event);
    managed_probe_event = NULL;
    managed_probe_reflection = NULL;
    managed_probe_message = 0;
    InterlockedExchange(&managed_probe_mode, 0);
    return scan->managed_thread_observation_complete &&
        managed_probe_state == 2;
}}

static int compare_runtime_pointer(const void *left, const void *right) {{
    uintptr_t a = *(const uintptr_t *)left;
    uintptr_t b = *(const uintptr_t *)right;
    return a < b ? -1 : a > b ? 1 : 0;
}}

static int capture_runtime_types(alpha_reflection_scan *scan) {{
    alpha_window_selection selection;
    uintptr_t **type_records = NULL;
    uint32_t *type_counts = NULL;
    char **assembly_full_names = NULL;
    uintptr_t *all_types = NULL;
    uint64_t total_type_count = 0, written_total = 0;
    HANDLE output = INVALID_HANDLE_VALUE;
    int ok = 0;
    memset(&selection, 0, sizeof(selection));
    if (!scan || !scan->managed_thread_observation_complete ||
        !scan->assembly_root_inventory_complete || !scan->assembly_count ||
        scan->assembly_count > ALPHA_MAX_ASSEMBLY_COUNT)
        return 0;
    selection.process_id = GetCurrentProcessId();
    if (!EnumWindows(select_managed_window, (LPARAM)(uintptr_t)&selection) ||
        selection.candidate_count != 1 || !selection.selected_window ||
        selection.selected_thread_id != scan->managed_window_thread_id)
        return 0;
    type_records = (uintptr_t **)calloc(
        scan->assembly_count, sizeof(uintptr_t *)
    );
    type_counts = (uint32_t *)calloc(
        scan->assembly_count, sizeof(uint32_t)
    );
    assembly_full_names = (char **)calloc(
        scan->assembly_count, sizeof(char *)
    );
    if (!type_records || !type_counts || !assembly_full_names) goto cleanup;
    managed_probe_message = RegisterWindowMessageW(
        L"ALPHA v2 fresh runtime type inventory slice"
    );
    managed_probe_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    managed_probe_reflection = scan;
    InterlockedExchange(&managed_probe_mode, 2);
    if (!managed_probe_message || !managed_probe_event) goto cleanup;
    managed_probe_hook = SetWindowsHookExW(
        WH_GETMESSAGE,
        managed_thread_probe,
        self_module,
        selection.selected_thread_id
    );
    if (!managed_probe_hook) goto cleanup;
    for (uint32_t index = 0; index < scan->assembly_count; index++) {{
        managed_slice_index = index;
        managed_slice_types = NULL;
        managed_slice_type_count = 0;
        free(managed_slice_assembly_full_name);
        managed_slice_assembly_full_name = NULL;
        ResetEvent(managed_probe_event);
        InterlockedExchange(&managed_probe_state, 0);
        if (!PostMessageW(
                selection.selected_window, managed_probe_message, 0, 0
            ) || WaitForSingleObject(managed_probe_event, 15000) !=
                WAIT_OBJECT_0 || managed_probe_state != 2)
            goto cleanup;
        type_records[index] = managed_slice_types;
        type_counts[index] = managed_slice_type_count;
        assembly_full_names[index] = managed_slice_assembly_full_name;
        managed_slice_types = NULL;
        managed_slice_type_count = 0;
        managed_slice_assembly_full_name = NULL;
        total_type_count += type_counts[index];
        if (total_type_count > ALPHA_MAX_TYPE_COUNT) goto cleanup;
    }}
    if (!total_type_count ||
        scan->type_inventory_completed_slice_count != scan->assembly_count)
        goto cleanup;
    all_types = (uintptr_t *)calloc(
        (SIZE_T)total_type_count, sizeof(uintptr_t)
    );
    if (!all_types) goto cleanup;
    uint64_t cursor = 0;
    for (uint32_t index = 0; index < scan->assembly_count; index++) {{
        if (type_counts[index]) {{
            memcpy(
                all_types + cursor,
                type_records[index],
                (SIZE_T)type_counts[index] * sizeof(uintptr_t)
            );
            cursor += type_counts[index];
        }}
    }}
    if (cursor != total_type_count) goto cleanup;
    qsort(
        all_types,
        (SIZE_T)total_type_count,
        sizeof(uintptr_t),
        compare_runtime_pointer
    );
    for (uint64_t index = 1; index < total_type_count; index++) {{
        if (!all_types[index] || all_types[index] == all_types[index - 1])
            goto cleanup;
    }}
    if (!all_types[0]) goto cleanup;
    scan->type_inventory_all_objects_class_valid = 1;
    scan->type_inventory_globally_unique = 1;

    output = CreateFileW(
        inventory_observation_output,
        GENERIC_WRITE,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (output == INVALID_HANDLE_VALUE) goto cleanup;
    static const unsigned char magic[8] =
        "{RUNTIME_INVENTORY_OBSERVATION_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_INVENTORY_OBSERVATION_VERSION}u;
    uint32_t header_bytes = ALPHA_INVENTORY_OBSERVATION_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0;
    uint64_t assembly_count = scan->assembly_count;
    ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written_total += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written_total += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written_total += sizeof(header_bytes); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written_total += sizeof(pointer_bytes); ok = write_handle_bytes(output, &reserved, sizeof(reserved)); }}
    if (ok) {{ written_total += sizeof(reserved); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written_total += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written_total += 64; ok = write_handle_bytes(output, &assembly_count, sizeof(assembly_count)); }}
    if (ok) {{ written_total += sizeof(assembly_count); ok = write_handle_bytes(output, &total_type_count, sizeof(total_type_count)); }}
    if (ok) written_total += sizeof(total_type_count);
    for (uint32_t index = 0; index < scan->assembly_count && ok; index++) {{
        ok = write_handle_bytes(output, &index, sizeof(index)) &&
            write_handle_bytes(
                output, &type_counts[index], sizeof(type_counts[index])
            ) && (!type_counts[index] || write_handle_bytes(
                    output,
                    type_records[index],
                    (SIZE_T)type_counts[index] * sizeof(uintptr_t)
                ));
        written_total += ALPHA_INVENTORY_OBSERVATION_ENTRY_BYTES +
            (uint64_t)type_counts[index] * sizeof(uintptr_t);
    }}
    uint64_t expected_bytes = ALPHA_INVENTORY_OBSERVATION_HEADER_BYTES +
        (uint64_t)scan->assembly_count *
            ALPHA_INVENTORY_OBSERVATION_ENTRY_BYTES +
        total_type_count * sizeof(uintptr_t);
    if (!ok || written_total != expected_bytes || !FlushFileBuffers(output))
        ok = 0;

cleanup:
    if (managed_probe_hook) UnhookWindowsHookEx(managed_probe_hook);
    managed_probe_hook = NULL;
    if (managed_probe_event) CloseHandle(managed_probe_event);
    managed_probe_event = NULL;
    managed_probe_reflection = NULL;
    managed_probe_message = 0;
    InterlockedExchange(&managed_probe_mode, 0);
    free(managed_slice_types);
    managed_slice_types = NULL;
    managed_slice_type_count = 0;
    free(managed_slice_assembly_full_name);
    managed_slice_assembly_full_name = NULL;
    if (output != INVALID_HANDLE_VALUE) CloseHandle(output);
    if (ok && _wchmod(inventory_observation_output, 0600)) ok = 0;
    if (ok && !sha256_file(
            inventory_observation_output,
            scan->type_inventory_observation_sha256
        ))
        ok = 0;
    if (ok) {{
        captured_type_roots = all_types;
        captured_type_root_count = total_type_count;
        captured_assembly_type_counts = type_counts;
        captured_assembly_full_names = assembly_full_names;
        all_types = NULL;
        type_counts = NULL;
        assembly_full_names = NULL;
    }}
    if (!ok) DeleteFileW(inventory_observation_output);
    if (type_records) {{
        for (uint32_t index = 0; index < scan->assembly_count; index++)
            free(type_records[index]);
    }}
    free(type_records);
    free(type_counts);
    free(all_types);
    if (assembly_full_names) {{
        for (uint32_t index = 0; index < scan->assembly_count; index++)
            free(assembly_full_names[index]);
    }}
    free(assembly_full_names);
    if (ok) {{
        scan->type_inventory_assembly_count = scan->assembly_count;
        scan->type_inventory_type_count = total_type_count;
        scan->type_inventory_observation_written = 1;
        scan->type_inventory_observation_complete =
            scan->type_inventory_all_objects_class_valid &&
            scan->type_inventory_globally_unique &&
            scan->type_inventory_completed_slice_count == scan->assembly_count;
    }}
    return ok && scan->type_inventory_observation_complete;
}}

typedef struct {{
    uintptr_t *values;
    uint64_t count;
    uint64_t capacity;
}} alpha_pointer_vector;

static int append_pointer_vector(
    alpha_pointer_vector *vector,
    const uintptr_t *values,
    uint32_t count
) {{
    if (!vector || (count && !values) ||
        vector->count + count > ALPHA_MAX_MEMBER_OBJECT_COUNT)
        return 0;
    uint64_t required = vector->count + count;
    if (required > vector->capacity) {{
        uint64_t capacity = vector->capacity ? vector->capacity : 64;
        while (capacity < required) {{
            if (capacity >= ALPHA_MAX_MEMBER_OBJECT_COUNT / 2) {{
                capacity = ALPHA_MAX_MEMBER_OBJECT_COUNT;
                break;
            }}
            capacity *= 2;
        }}
        uintptr_t *resized = (uintptr_t *)realloc(
            vector->values, (SIZE_T)capacity * sizeof(uintptr_t)
        );
        if (!resized) return 0;
        vector->values = resized;
        vector->capacity = capacity;
    }}
    if (count) memcpy(
        vector->values + vector->count,
        values,
        (SIZE_T)count * sizeof(uintptr_t)
    );
    vector->count = required;
    return 1;
}}

static int append_byte_vector(
    alpha_byte_vector *vector,
    const void *value,
    uint64_t bytes,
    uint64_t maximum
) {{
    if (!vector || (!value && bytes) || !maximum || bytes > maximum ||
        vector->count > maximum - bytes)
        return 0;
    uint64_t required = vector->count + bytes;
    if (required > vector->capacity) {{
        uint64_t capacity = vector->capacity ? vector->capacity : 4096;
        while (capacity < required) {{
            if (capacity > maximum / 2u) {{
                capacity = maximum;
                break;
            }}
            capacity *= 2u;
        }}
        if (capacity < required || capacity > SIZE_MAX) return 0;
        unsigned char *resized = (unsigned char *)realloc(
            vector->values, (SIZE_T)capacity
        );
        if (!resized) return 0;
        vector->values = resized;
        vector->capacity = capacity;
    }}
    if (bytes) memcpy(vector->values + vector->count, value, (SIZE_T)bytes);
    vector->count = required;
    return 1;
}}

static int sorted_pointer_contains(
    const uintptr_t *values,
    uint64_t count,
    uintptr_t target
) {{
    uint64_t left = 0, right = count;
    while (left < right) {{
        uint64_t middle = left + (right - left) / 2;
        if (values[middle] < target) left = middle + 1;
        else right = middle;
    }}
    return left < count && values[left] == target;
}}

static int pointer_vector_is_unique(alpha_pointer_vector *vector) {{
    if (!vector) return 0;
    if (vector->count) qsort(
        vector->values,
        (SIZE_T)vector->count,
        sizeof(uintptr_t),
        compare_runtime_pointer
    );
    for (uint64_t index = 0; index < vector->count; index++) {{
        if (!vector->values[index] ||
            (index && vector->values[index] == vector->values[index - 1]))
            return 0;
    }}
    return 1;
}}

static int pointer_vector_sort_dedupe(alpha_pointer_vector *vector) {{
    if (!vector) return 0;
    if (vector->count) qsort(
        vector->values,
        (SIZE_T)vector->count,
        sizeof(uintptr_t),
        compare_runtime_pointer
    );
    uint64_t output = 0;
    for (uint64_t index = 0; index < vector->count; index++) {{
        uintptr_t value = vector->values[index];
        if (!value) return 0;
        if (!output || vector->values[output - 1] != value)
            vector->values[output++] = value;
    }}
    vector->count = output;
    return 1;
}}

static int append_unseen_type_graph_nodes(
    alpha_pointer_vector *nodes,
    alpha_pointer_vector *references,
    uint64_t *first_new_node
) {{
    if (!nodes || !references || !first_new_node ||
        nodes->count > ALPHA_MAX_TYPE_GRAPH_NODES ||
        !pointer_vector_sort_dedupe(references))
        return 0;
    uintptr_t *sorted_nodes = NULL;
    if (nodes->count) {{
        sorted_nodes = (uintptr_t *)malloc(
            (SIZE_T)nodes->count * sizeof(uintptr_t)
        );
        if (!sorted_nodes) return 0;
        memcpy(
            sorted_nodes,
            nodes->values,
            (SIZE_T)nodes->count * sizeof(uintptr_t)
        );
        qsort(
            sorted_nodes,
            (SIZE_T)nodes->count,
            sizeof(uintptr_t),
            compare_runtime_pointer
        );
        for (uint64_t index = 1; index < nodes->count; index++) {{
            if (sorted_nodes[index] == sorted_nodes[index - 1]) {{
                free(sorted_nodes);
                return 0;
            }}
        }}
    }}
    *first_new_node = nodes->count;
    for (uint64_t index = 0; index < references->count; index++) {{
        uintptr_t value = references->values[index];
        if (sorted_pointer_contains(sorted_nodes, nodes->count, value))
            continue;
        if (nodes->count >= ALPHA_MAX_TYPE_GRAPH_NODES ||
            !append_pointer_vector(nodes, &value, 1)) {{
            free(sorted_nodes);
            return 0;
        }}
    }}
    references->count = 0;
    free(sorted_nodes);
    return 1;
}}

static int sorted_vectors_disjoint(
    const alpha_pointer_vector *left,
    const alpha_pointer_vector *right
) {{
    uint64_t a = 0, b = 0;
    if (!left || !right) return 0;
    while (a < left->count && b < right->count) {{
        if (left->values[a] == right->values[b]) return 0;
        if (left->values[a] < right->values[b]) a++;
        else b++;
    }}
    return 1;
}}

static int write_member_observation_header(
    HANDLE output,
    const alpha_reflection_scan *scan,
    const uint64_t totals[ALPHA_MEMBER_CATEGORY_COUNT]
) {{
    if (output == INVALID_HANDLE_VALUE || !scan || !totals ||
        strlen(scan->type_inventory_observation_sha256) != 64)
        return 0;
    static const unsigned char magic[8] =
        "{RUNTIME_MEMBER_OBSERVATION_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_MEMBER_OBSERVATION_VERSION}u;
    uint32_t header_bytes = ALPHA_MEMBER_OBSERVATION_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t binding_flags = ALPHA_DECLARED_MEMBER_BINDING_FLAGS;
    uint64_t written = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written += sizeof(header_bytes); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written += sizeof(pointer_bytes); ok = write_handle_bytes(output, &binding_flags, sizeof(binding_flags)); }}
    if (ok) {{ written += sizeof(binding_flags); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, scan->type_inventory_observation_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, &scan->type_inventory_type_count, sizeof(scan->type_inventory_type_count)); }}
    if (ok) written += sizeof(scan->type_inventory_type_count);
    for (uint32_t category = 0;
         category < ALPHA_MEMBER_CATEGORY_COUNT && ok;
         category++) {{
        ok = write_handle_bytes(
            output, &totals[category], sizeof(totals[category])
        );
        written += sizeof(totals[category]);
    }}
    return ok && written == ALPHA_MEMBER_OBSERVATION_HEADER_BYTES;
}}

static int write_type_identity_header(
    HANDLE output,
    const alpha_reflection_scan *scan
) {{
    if (output == INVALID_HANDLE_VALUE || !scan ||
        strlen(scan->type_inventory_observation_sha256) != 64)
        return 0;
    static const unsigned char magic[8] =
        "{RUNTIME_TYPE_IDENTITY_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_TYPE_IDENTITY_VERSION}u;
    uint32_t header_bytes = ALPHA_TYPE_IDENTITY_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0;
    uint64_t assembly_count = scan->assembly_count;
    uint64_t written = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written += sizeof(header_bytes); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written += sizeof(pointer_bytes); ok = write_handle_bytes(output, &reserved, sizeof(reserved)); }}
    if (ok) {{ written += sizeof(reserved); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, scan->type_inventory_observation_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, &assembly_count, sizeof(assembly_count)); }}
    if (ok) {{ written += sizeof(assembly_count); ok = write_handle_bytes(output, &scan->type_inventory_type_count, sizeof(scan->type_inventory_type_count)); }}
    if (ok) written += sizeof(scan->type_inventory_type_count);
    return ok && written == ALPHA_TYPE_IDENTITY_HEADER_BYTES;
}}

static int write_member_detail_header(
    HANDLE output,
    const alpha_reflection_scan *scan,
    const uint64_t totals[ALPHA_MEMBER_CATEGORY_COUNT],
    const char member_observation_sha256[65],
    const char type_identity_sha256[65]
) {{
    if (output == INVALID_HANDLE_VALUE || !scan || !totals ||
        strlen(scan->type_inventory_observation_sha256) != 64 ||
        !member_observation_sha256 ||
        strlen(member_observation_sha256) != 64 ||
        !type_identity_sha256 || strlen(type_identity_sha256) != 64)
        return 0;
    static const unsigned char magic[8] =
        "{RUNTIME_MEMBER_DETAIL_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_MEMBER_DETAIL_VERSION}u;
    uint32_t header_bytes = ALPHA_MEMBER_DETAIL_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0;
    uint64_t written = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written += sizeof(header_bytes); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written += sizeof(pointer_bytes); ok = write_handle_bytes(output, &reserved, sizeof(reserved)); }}
    if (ok) {{ written += sizeof(reserved); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_reflection_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, scan->type_inventory_observation_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, member_observation_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, type_identity_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, &scan->type_inventory_type_count, sizeof(scan->type_inventory_type_count)); }}
    if (ok) written += sizeof(scan->type_inventory_type_count);
    for (uint32_t category = 0; category < 5 && ok; category++) {{
        ok = write_handle_bytes(
            output, &totals[category], sizeof(totals[category])
        );
        written += sizeof(totals[category]);
    }}
    return ok && written == ALPHA_MEMBER_DETAIL_HEADER_BYTES;
}}

static int write_type_graph_header(
    HANDLE output,
    const alpha_reflection_scan *scan,
    const char type_identity_sha256[65],
    const char member_detail_sha256[65],
    uint64_t node_count,
    uint64_t root_count
) {{
    if (output == INVALID_HANDLE_VALUE || !scan ||
        strlen(scan->type_inventory_observation_sha256) != 64 ||
        !type_identity_sha256 || strlen(type_identity_sha256) != 64 ||
        !member_detail_sha256 || strlen(member_detail_sha256) != 64 ||
        node_count < root_count || !root_count ||
        node_count > ALPHA_MAX_TYPE_GRAPH_NODES)
        return 0;
    static const unsigned char magic[8] =
        "{RUNTIME_TYPE_GRAPH_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_TYPE_GRAPH_VERSION}u;
    uint32_t header_bytes = ALPHA_TYPE_GRAPH_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0;
    uint64_t written = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written += sizeof(header_bytes); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written += sizeof(pointer_bytes); ok = write_handle_bytes(output, &reserved, sizeof(reserved)); }}
    if (ok) {{ written += sizeof(reserved); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, scan->type_inventory_observation_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, type_identity_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, member_detail_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, &node_count, sizeof(node_count)); }}
    if (ok) {{ written += sizeof(node_count); ok = write_handle_bytes(output, &root_count, sizeof(root_count)); }}
    if (ok) written += sizeof(root_count);
    return ok && written == ALPHA_TYPE_GRAPH_HEADER_BYTES;
}}

static int write_type_native_header(
    HANDLE output,
    const alpha_reflection_scan *scan,
    const char type_graph_sha256[65],
    uint64_t node_count,
    uint64_t unique_handle_count
) {{
    if (output == INVALID_HANDLE_VALUE || !scan ||
        !type_graph_sha256 || strlen(type_graph_sha256) != 64 ||
        !node_count || node_count > ALPHA_MAX_TYPE_GRAPH_NODES ||
        unique_handle_count != node_count ||
        scan->type_native_node_count != node_count)
        return 0;
    static const unsigned char magic[8] =
        "{RUNTIME_TYPE_NATIVE_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_TYPE_NATIVE_VERSION}u;
    uint32_t header_bytes = ALPHA_TYPE_NATIVE_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0;
    uint64_t written = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written += sizeof(header_bytes); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written += sizeof(pointer_bytes); ok = write_handle_bytes(output, &reserved, sizeof(reserved)); }}
    if (ok) {{ written += sizeof(reserved); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_reflection_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, type_graph_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, &node_count, sizeof(node_count)); }}
    if (ok) {{ written += sizeof(node_count); ok = write_handle_bytes(output, &unique_handle_count, sizeof(unique_handle_count)); }}
    if (ok) written += sizeof(unique_handle_count);
    return ok && written == ALPHA_TYPE_NATIVE_HEADER_BYTES;
}}

static int write_method_native_header(
    HANDLE output,
    const alpha_reflection_scan *scan,
    const char member_detail_sha256[65],
    const char type_graph_sha256[65],
    uint64_t image_base,
    uint64_t image_bytes,
    uint64_t type_count,
    uint64_t method_count
) {{
    if (output == INVALID_HANDLE_VALUE || !scan ||
        !member_detail_sha256 || strlen(member_detail_sha256) != 64 ||
        !type_graph_sha256 || strlen(type_graph_sha256) != 64 ||
        !image_base || (image_base & 0xffffu) || !image_bytes ||
        image_bytes > UINT32_MAX || !type_count ||
        method_count != scan->method_native_method_count)
        return 0;
    static const unsigned char magic[8] =
        "{RUNTIME_METHOD_NATIVE_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_METHOD_NATIVE_VERSION}u;
    uint32_t header_bytes = ALPHA_METHOD_NATIVE_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0;
    uint64_t written = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written += sizeof(header_bytes); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written += sizeof(pointer_bytes); ok = write_handle_bytes(output, &reserved, sizeof(reserved)); }}
    if (ok) {{ written += sizeof(reserved); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_reflection_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, member_detail_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, type_graph_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, &image_base, sizeof(image_base)); }}
    if (ok) {{ written += sizeof(image_base); ok = write_handle_bytes(output, &image_bytes, sizeof(image_bytes)); }}
    if (ok) {{ written += sizeof(image_bytes); ok = write_handle_bytes(output, &type_count, sizeof(type_count)); }}
    if (ok) {{ written += sizeof(type_count); ok = write_handle_bytes(output, &method_count, sizeof(method_count)); }}
    if (ok) written += sizeof(method_count);
    return ok && written == ALPHA_METHOD_NATIVE_HEADER_BYTES;
}}

static int write_field_native_header(
    HANDLE output,
    const alpha_reflection_scan *scan,
    const char member_detail_sha256[65],
    const char type_graph_sha256[65],
    const char method_native_sha256[65],
    uint64_t type_count,
    uint64_t field_count,
    uint32_t metadata_stride,
    uint32_t offset_dword_index,
    uint32_t token_dword_index
) {{
    if (output == INVALID_HANDLE_VALUE || !scan ||
        !member_detail_sha256 || strlen(member_detail_sha256) != 64 ||
        !type_graph_sha256 || strlen(type_graph_sha256) != 64 ||
        !method_native_sha256 || strlen(method_native_sha256) != 64 ||
        !type_count || field_count != scan->field_native_field_count ||
        metadata_stride < 24 ||
        metadata_stride > ALPHA_FIELD_METADATA_SAMPLE_BYTES ||
        (metadata_stride & 7u) ||
        offset_dword_index >= metadata_stride / sizeof(uint32_t) ||
        token_dword_index >= metadata_stride / sizeof(uint32_t) ||
        offset_dword_index == token_dword_index)
        return 0;
    static const unsigned char magic[8] =
        "{RUNTIME_FIELD_NATIVE_MAGIC.decode('ascii')}";
    uint32_t version = {RUNTIME_FIELD_NATIVE_VERSION}u;
    uint32_t header_bytes = ALPHA_FIELD_NATIVE_HEADER_BYTES;
    uint32_t pointer_bytes = sizeof(uintptr_t);
    uint32_t reserved = 0, reserved_two = 0;
    uint64_t written = 0;
    int ok = write_handle_bytes(output, magic, sizeof(magic));
    if (ok) {{ written += sizeof(magic); ok = write_handle_bytes(output, &version, sizeof(version)); }}
    if (ok) {{ written += sizeof(version); ok = write_handle_bytes(output, &header_bytes, sizeof(header_bytes)); }}
    if (ok) {{ written += sizeof(header_bytes); ok = write_handle_bytes(output, &pointer_bytes, sizeof(pointer_bytes)); }}
    if (ok) {{ written += sizeof(pointer_bytes); ok = write_handle_bytes(output, &reserved, sizeof(reserved)); }}
    if (ok) {{ written += sizeof(reserved); ok = write_handle_bytes(output, expected_executable_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_reflection_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, expected_inventory_contract_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, member_detail_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, type_graph_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, method_native_sha256, 64); }}
    if (ok) {{ written += 64; ok = write_handle_bytes(output, &type_count, sizeof(type_count)); }}
    if (ok) {{ written += sizeof(type_count); ok = write_handle_bytes(output, &field_count, sizeof(field_count)); }}
    if (ok) {{ written += sizeof(field_count); ok = write_handle_bytes(output, &metadata_stride, sizeof(metadata_stride)); }}
    if (ok) {{ written += sizeof(metadata_stride); ok = write_handle_bytes(output, &offset_dword_index, sizeof(offset_dword_index)); }}
    if (ok) {{ written += sizeof(offset_dword_index); ok = write_handle_bytes(output, &token_dword_index, sizeof(token_dword_index)); }}
    if (ok) {{ written += sizeof(token_dword_index); ok = write_handle_bytes(output, &reserved_two, sizeof(reserved_two)); }}
    if (ok) written += sizeof(reserved_two);
    return ok && written == ALPHA_FIELD_NATIVE_HEADER_BYTES;
}}

static int write_type_identity_slice(
    HANDLE output,
    alpha_reflection_scan *scan,
    uint64_t *written_total
) {{
    alpha_type_identity_slice *identity = &managed_type_identity;
    if (output == INVALID_HANDLE_VALUE || !scan || !written_total ||
        !identity->name || !identity->namespace_name)
        return 0;
    SIZE_T name_size = strlen(identity->name);
    SIZE_T namespace_size = strlen(identity->namespace_name);
    if (!name_size || name_size > 16384 || namespace_size > 16384 ||
        identity->interface_count > 65536 ||
        identity->generic_argument_count > 65536 ||
        (identity->declaring_type && !sorted_pointer_contains(
            captured_type_roots,
            captured_type_root_count,
            identity->declaring_type
        )))
        return 0;
    uint32_t name_bytes = (uint32_t)name_size;
    uint32_t namespace_bytes = (uint32_t)namespace_size;
    int ok = write_handle_bytes(output, &name_bytes, sizeof(name_bytes)) &&
        write_handle_bytes(
            output, &namespace_bytes, sizeof(namespace_bytes)
        ) && write_handle_bytes(
            output, &identity->attributes, sizeof(identity->attributes)
        ) && write_handle_bytes(
            output, &identity->shape, sizeof(identity->shape)
        ) && write_handle_bytes(
            output, &identity->base_type, sizeof(identity->base_type)
        ) && write_handle_bytes(
            output, &identity->declaring_type, sizeof(identity->declaring_type)
        ) && write_handle_bytes(
            output, &identity->element_type, sizeof(identity->element_type)
        ) && write_handle_bytes(
            output,
            &identity->generic_definition,
            sizeof(identity->generic_definition)
        ) && write_handle_bytes(
            output,
            &identity->interface_count,
            sizeof(identity->interface_count)
        ) && write_handle_bytes(
            output,
            &identity->generic_argument_count,
            sizeof(identity->generic_argument_count)
        ) && write_handle_bytes(output, identity->name, name_size) &&
        (!namespace_size || write_handle_bytes(
            output, identity->namespace_name, namespace_size
        )) && (!identity->interface_count || write_handle_bytes(
            output,
            identity->interfaces,
            (SIZE_T)identity->interface_count * sizeof(uintptr_t)
        )) && (!identity->generic_argument_count || write_handle_bytes(
            output,
            identity->generic_arguments,
            (SIZE_T)identity->generic_argument_count * sizeof(uintptr_t)
        ));
    if (!ok) return 0;
    *written_total += ALPHA_TYPE_IDENTITY_ENTRY_BYTES + name_size +
        namespace_size +
        ((uint64_t)identity->interface_count +
            identity->generic_argument_count) * sizeof(uintptr_t);
    scan->type_identity_relation_count += identity->interface_count +
        identity->generic_argument_count;
    return 1;
}}

static int capture_runtime_members(alpha_reflection_scan *scan) {{
    alpha_window_selection selection;
    alpha_pointer_vector vectors[ALPHA_MEMBER_CATEGORY_COUNT];
    alpha_pointer_vector type_graph_nodes;
    alpha_pointer_vector type_graph_references;
    alpha_pointer_vector type_native_handles;
    alpha_pointer_vector method_metadata_objects;
    alpha_pointer_vector field_metadata_objects;
    alpha_byte_vector field_native_candidates;
    unsigned char empty_header[ALPHA_MEMBER_OBSERVATION_HEADER_BYTES];
    unsigned char empty_detail_header[ALPHA_MEMBER_DETAIL_HEADER_BYTES];
    unsigned char empty_graph_header[ALPHA_TYPE_GRAPH_HEADER_BYTES];
    unsigned char empty_type_native_header[ALPHA_TYPE_NATIVE_HEADER_BYTES];
    unsigned char empty_method_native_header[ALPHA_METHOD_NATIVE_HEADER_BYTES];
    unsigned char empty_field_native_header[ALPHA_FIELD_NATIVE_HEADER_BYTES];
    HANDLE output = INVALID_HANDLE_VALUE;
    HANDLE identity_output = INVALID_HANDLE_VALUE;
    HANDLE detail_output = INVALID_HANDLE_VALUE;
    HANDLE graph_output = INVALID_HANDLE_VALUE;
    HANDLE type_native_output = INVALID_HANDLE_VALUE;
    HANDLE method_native_output = INVALID_HANDLE_VALUE;
    HANDLE field_native_output = INVALID_HANDLE_VALUE;
    uint64_t written_total = ALPHA_MEMBER_OBSERVATION_HEADER_BYTES;
    uint64_t identity_written_total = ALPHA_TYPE_IDENTITY_HEADER_BYTES;
    uint64_t detail_written_total = ALPHA_MEMBER_DETAIL_HEADER_BYTES;
    uint64_t graph_written_total = ALPHA_TYPE_GRAPH_HEADER_BYTES;
    uint64_t type_native_written_total = ALPHA_TYPE_NATIVE_HEADER_BYTES;
    uint64_t method_native_written_total = ALPHA_METHOD_NATIVE_HEADER_BYTES;
    uint64_t field_native_written_total = ALPHA_FIELD_NATIVE_HEADER_BYTES;
    uint64_t observed_type_count = 0;
    uintptr_t image_base = 0;
    uint64_t image_bytes = 0;
    uint32_t field_metadata_stride = 0;
    uint32_t field_offset_dword_index = UINT32_MAX;
    uint32_t field_token_dword_index = UINT32_MAX;
    char member_observation_sha256[65] = {{0}};
    char type_identity_sha256[65] = {{0}};
    char member_detail_sha256[65] = {{0}};
    char type_graph_sha256[65] = {{0}};
    char method_native_sha256[65] = {{0}};
    int ok = 0;
    memset(&selection, 0, sizeof(selection));
    memset(vectors, 0, sizeof(vectors));
    memset(&type_graph_nodes, 0, sizeof(type_graph_nodes));
    memset(&type_graph_references, 0, sizeof(type_graph_references));
    memset(&type_native_handles, 0, sizeof(type_native_handles));
    memset(&method_metadata_objects, 0, sizeof(method_metadata_objects));
    memset(&field_metadata_objects, 0, sizeof(field_metadata_objects));
    memset(&field_native_candidates, 0, sizeof(field_native_candidates));
    memset(empty_header, 0, sizeof(empty_header));
    memset(empty_detail_header, 0, sizeof(empty_detail_header));
    memset(empty_graph_header, 0, sizeof(empty_graph_header));
    memset(
        empty_type_native_header,
        0,
        sizeof(empty_type_native_header)
    );
    memset(
        empty_method_native_header,
        0,
        sizeof(empty_method_native_header)
    );
    memset(
        empty_field_native_header,
        0,
        sizeof(empty_field_native_header)
    );
    free(captured_type_native_handles);
    captured_type_native_handles = NULL;
    captured_type_native_handle_count = 0;
    if (!scan || !scan->type_inventory_observation_complete ||
        !captured_type_roots ||
        captured_type_root_count != scan->type_inventory_type_count ||
        !captured_assembly_type_counts || !captured_assembly_full_names)
        goto cleanup;
    selection.process_id = GetCurrentProcessId();
    if (!EnumWindows(select_managed_window, (LPARAM)(uintptr_t)&selection) ||
        selection.candidate_count != 1 || !selection.selected_window ||
        selection.selected_thread_id != scan->managed_window_thread_id)
        goto cleanup;
    output = CreateFileW(
        member_observation_output,
        GENERIC_WRITE | GENERIC_READ,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (output == INVALID_HANDLE_VALUE || !write_handle_bytes(
            output, empty_header, sizeof(empty_header)
        ))
        goto cleanup;
    identity_output = CreateFileW(
        type_identity_observation_output,
        GENERIC_WRITE,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (identity_output == INVALID_HANDLE_VALUE ||
        !write_type_identity_header(identity_output, scan))
        goto cleanup;
    detail_output = CreateFileW(
        member_detail_observation_output,
        GENERIC_WRITE | GENERIC_READ,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (detail_output == INVALID_HANDLE_VALUE || !write_handle_bytes(
            detail_output,
            empty_detail_header,
            sizeof(empty_detail_header)
        ))
        goto cleanup;
    graph_output = CreateFileW(
        type_graph_observation_output,
        GENERIC_WRITE | GENERIC_READ,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (graph_output == INVALID_HANDLE_VALUE || !write_handle_bytes(
            graph_output, empty_graph_header, sizeof(empty_graph_header)
        ))
        goto cleanup;
    type_native_output = CreateFileW(
        type_native_observation_output,
        GENERIC_WRITE | GENERIC_READ,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (type_native_output == INVALID_HANDLE_VALUE || !write_handle_bytes(
            type_native_output,
            empty_type_native_header,
            sizeof(empty_type_native_header)
        ))
        goto cleanup;
    method_native_output = CreateFileW(
        method_native_observation_output,
        GENERIC_WRITE | GENERIC_READ,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (method_native_output == INVALID_HANDLE_VALUE ||
        !write_handle_bytes(
            method_native_output,
            empty_method_native_header,
            sizeof(empty_method_native_header)
        ) || !current_image_bounds(&image_base, &image_bytes))
        goto cleanup;
    field_native_output = CreateFileW(
        field_native_observation_output,
        GENERIC_WRITE | GENERIC_READ,
        0,
        NULL,
        CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL,
        NULL
    );
    if (field_native_output == INVALID_HANDLE_VALUE ||
        !write_handle_bytes(
            field_native_output,
            empty_field_native_header,
            sizeof(empty_field_native_header)
        ))
        goto cleanup;
    for (uint32_t assembly = 0; assembly < scan->assembly_count; assembly++) {{
        if (!captured_assembly_full_names[assembly]) goto cleanup;
        SIZE_T length = strlen(captured_assembly_full_names[assembly]);
        if (!length || length > 16384) goto cleanup;
        uint32_t bytes = (uint32_t)length;
        if (!write_handle_bytes(identity_output, &bytes, sizeof(bytes)) ||
            !write_handle_bytes(
                identity_output,
                captured_assembly_full_names[assembly],
                length
            ))
            goto cleanup;
        identity_written_total += ALPHA_TYPE_IDENTITY_ASSEMBLY_BYTES + length;
    }}
    managed_probe_message = RegisterWindowMessageW(
        L"ALPHA v2 fresh runtime member inventory slice"
    );
    managed_probe_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    managed_probe_reflection = scan;
    InterlockedExchange(&managed_probe_mode, 3);
    if (!managed_probe_message || !managed_probe_event) goto cleanup;
    managed_probe_hook = SetWindowsHookExW(
        WH_GETMESSAGE,
        managed_thread_probe,
        self_module,
        selection.selected_thread_id
    );
    if (!managed_probe_hook) goto cleanup;
    for (uint32_t assembly = 0; assembly < scan->assembly_count; assembly++) {{
        for (uint32_t type = 0;
             type < captured_assembly_type_counts[assembly];
             type++) {{
            managed_member_assembly_index = assembly;
            managed_member_type_index = type;
            clear_managed_member_buffers();
            clear_managed_type_identity();
            clear_managed_member_detail();
            clear_managed_method_native();
            clear_managed_field_native();
            ResetEvent(managed_probe_event);
            InterlockedExchange(&managed_probe_state, 0);
            if (!PostMessageW(
                    selection.selected_window, managed_probe_message, 0, 0
                ) || WaitForSingleObject(managed_probe_event, 15000) !=
                    WAIT_OBJECT_0 || managed_probe_state != 2)
                goto cleanup;
            if (!write_type_identity_slice(
                    identity_output, scan, &identity_written_total
                ))
                goto cleanup;
            if (!managed_member_detail.values ||
                managed_member_detail.count <
                    ALPHA_MEMBER_DETAIL_TYPE_BYTES ||
                !write_handle_bytes(
                    detail_output,
                    managed_member_detail.values,
                    (SIZE_T)managed_member_detail.count
                ))
                goto cleanup;
            detail_written_total += managed_member_detail.count;
            uint64_t slice_field_count = managed_member_counts[0];
            if (slice_field_count >
                    UINT64_MAX / sizeof(alpha_field_native_candidate) ||
                (slice_field_count && !managed_field_native.values) ||
                managed_field_native.count != slice_field_count *
                    sizeof(alpha_field_native_candidate))
                goto cleanup;
            alpha_field_native_candidate *slice_fields =
                (alpha_field_native_candidate *)managed_field_native.values;
            uintptr_t *slice_metadata = NULL;
            if (slice_field_count > 1) {{
                slice_metadata = (uintptr_t *)malloc(
                    (SIZE_T)slice_field_count * sizeof(uintptr_t)
                );
                if (!slice_metadata) goto cleanup;
            }}
            for (uint64_t field_index = 0;
                 field_index < slice_field_count;
                 field_index++) {{
                alpha_field_native_candidate *field =
                    &slice_fields[field_index];
                if (field->member_object !=
                        managed_member_arrays[0][field_index] ||
                    field->declaring_type_object !=
                        managed_graph_type_object ||
                    !field->metadata_object || !field->declaring_class ||
                    !field->type_handle || !append_pointer_vector(
                        &field_metadata_objects,
                        &field->metadata_object,
                        1
                    )) {{
                    free(slice_metadata);
                    goto cleanup;
                }}
                if (slice_metadata)
                    slice_metadata[field_index] = field->metadata_object;
            }}
            if (slice_metadata) {{
                qsort(
                    slice_metadata,
                    (SIZE_T)slice_field_count,
                    sizeof(uintptr_t),
                    compare_runtime_pointer
                );
                uint32_t slice_stride = 0;
                for (uint64_t field_index = 1;
                     field_index < slice_field_count;
                     field_index++) {{
                    uint64_t distance = slice_metadata[field_index] -
                        slice_metadata[field_index - 1];
                    if (!distance ||
                        distance > ALPHA_FIELD_METADATA_SAMPLE_BYTES ||
                        (distance & 7u) || distance > UINT32_MAX ||
                        (slice_stride && slice_stride != distance)) {{
                        free(slice_metadata);
                        goto cleanup;
                    }}
                    slice_stride = (uint32_t)distance;
                }}
                free(slice_metadata);
                if (!slice_stride ||
                    (field_metadata_stride &&
                        field_metadata_stride != slice_stride))
                    goto cleanup;
                field_metadata_stride = slice_stride;
            }}
            if (!append_byte_vector(
                    &field_native_candidates,
                    managed_field_native.values,
                    managed_field_native.count,
                    ALPHA_MAX_MEMBER_OBJECT_COUNT *
                        sizeof(alpha_field_native_candidate)
                ))
                goto cleanup;
            uint64_t slice_method_count =
                (uint64_t)managed_member_counts[1] +
                managed_member_counts[2];
            if (slice_method_count >
                    UINT64_MAX / ALPHA_METHOD_NATIVE_ENTRY_BYTES ||
                (slice_method_count && !managed_method_native.values) ||
                managed_method_native.count !=
                    slice_method_count * ALPHA_METHOD_NATIVE_ENTRY_BYTES)
                goto cleanup;
            for (uint64_t method_index = 0;
                 method_index < slice_method_count;
                 method_index++) {{
                const unsigned char *entry =
                    managed_method_native.values +
                    method_index * ALPHA_METHOD_NATIVE_ENTRY_BYTES;
                uintptr_t member_object = 0, metadata_object = 0;
                uintptr_t expected_member = method_index <
                        managed_member_counts[1]
                    ? managed_member_arrays[1][method_index]
                    : managed_member_arrays[2][
                        method_index - managed_member_counts[1]
                    ];
                memcpy(&member_object, entry, sizeof(member_object));
                memcpy(
                    &metadata_object,
                    entry + sizeof(uintptr_t),
                    sizeof(metadata_object)
                );
                if (member_object != expected_member || !metadata_object ||
                    !append_pointer_vector(
                        &method_metadata_objects, &metadata_object, 1
                    ))
                    goto cleanup;
            }}
            if (managed_method_native.count && !write_handle_bytes(
                    method_native_output,
                    managed_method_native.values,
                    (SIZE_T)managed_method_native.count
                ))
                goto cleanup;
            method_native_written_total += managed_method_native.count;
            uintptr_t native_type_object = 0, native_type_handle = 0;
            if (!managed_type_native.values ||
                managed_type_native.count != ALPHA_TYPE_NATIVE_ENTRY_BYTES)
                goto cleanup;
            memcpy(
                &native_type_object,
                managed_type_native.values,
                sizeof(native_type_object)
            );
            memcpy(
                &native_type_handle,
                managed_type_native.values + sizeof(uintptr_t),
                sizeof(native_type_handle)
            );
            if (native_type_object != managed_graph_type_object ||
                !native_type_handle ||
                !append_pointer_vector(
                    &type_native_handles, &native_type_handle, 1
                ) || !write_handle_bytes(
                    type_native_output,
                    managed_type_native.values,
                    ALPHA_TYPE_NATIVE_ENTRY_BYTES
                ))
                goto cleanup;
            type_native_written_total += ALPHA_TYPE_NATIVE_ENTRY_BYTES;
            if (!managed_graph_type_object ||
                !managed_type_graph_node.values ||
                managed_type_graph_node.count <
                    ALPHA_TYPE_GRAPH_ENTRY_BYTES ||
                !append_pointer_vector(
                    &type_graph_nodes, &managed_graph_type_object, 1
                ) || !append_pointer_vector(
                    &type_graph_references,
                    managed_type_references,
                    managed_type_reference_count
                ) || !write_handle_bytes(
                    graph_output,
                    managed_type_graph_node.values,
                    (SIZE_T)managed_type_graph_node.count
                ))
                goto cleanup;
            graph_written_total += managed_type_graph_node.count;
            if (!write_handle_bytes(
                    output,
                    managed_member_counts,
                    ALPHA_MEMBER_OBSERVATION_ENTRY_BYTES
                ))
                goto cleanup;
            written_total += ALPHA_MEMBER_OBSERVATION_ENTRY_BYTES;
            for (uint32_t category = 0;
                 category < ALPHA_MEMBER_CATEGORY_COUNT;
                 category++) {{
                if (!append_pointer_vector(
                        &vectors[category],
                        managed_member_arrays[category],
                        managed_member_counts[category]
                    ) || (managed_member_counts[category] &&
                        !write_handle_bytes(
                            output,
                            managed_member_arrays[category],
                            (SIZE_T)managed_member_counts[category] *
                                sizeof(uintptr_t)
                        )))
                    goto cleanup;
                written_total +=
                    (uint64_t)managed_member_counts[category] *
                        sizeof(uintptr_t);
            }}
            clear_managed_member_buffers();
            clear_managed_type_identity();
            clear_managed_member_detail();
            clear_managed_method_native();
            clear_managed_field_native();
            clear_managed_type_graph_state();
            observed_type_count++;
        }}
    }}
    if (observed_type_count != captured_type_root_count ||
        scan->member_inventory_completed_slice_count != observed_type_count ||
        type_graph_nodes.count != observed_type_count ||
        method_metadata_objects.count != scan->method_native_method_count ||
        field_metadata_objects.count != scan->field_native_field_count ||
        field_native_candidates.count != field_metadata_objects.count *
            sizeof(alpha_field_native_candidate))
        goto cleanup;
    InterlockedExchange(&managed_probe_mode, 4);
    for (;;) {{
        uint64_t first_new_node = 0;
        if (!append_unseen_type_graph_nodes(
                &type_graph_nodes,
                &type_graph_references,
                &first_new_node
            ))
            goto cleanup;
        if (first_new_node == type_graph_nodes.count) break;
        for (uint64_t node_index = first_new_node;
             node_index < type_graph_nodes.count;
             node_index++) {{
            managed_graph_type_object = type_graph_nodes.values[node_index];
            clear_managed_type_identity();
            clear_managed_type_graph_state();
            managed_graph_type_object = type_graph_nodes.values[node_index];
            ResetEvent(managed_probe_event);
            InterlockedExchange(&managed_probe_state, 0);
            if (!PostMessageW(
                    selection.selected_window, managed_probe_message, 0, 0
                ) || WaitForSingleObject(managed_probe_event, 15000) !=
                    WAIT_OBJECT_0 || managed_probe_state != 2 ||
                !managed_type_native.values ||
                managed_type_native.count != ALPHA_TYPE_NATIVE_ENTRY_BYTES ||
                !managed_type_graph_node.values ||
                managed_type_graph_node.count <
                    ALPHA_TYPE_GRAPH_ENTRY_BYTES ||
                !append_pointer_vector(
                    &type_graph_references,
                    managed_type_references,
                    managed_type_reference_count
                ) || !write_handle_bytes(
                    graph_output,
                    managed_type_graph_node.values,
                    (SIZE_T)managed_type_graph_node.count
                ))
                goto cleanup;
            uintptr_t native_type_object = 0, native_type_handle = 0;
            memcpy(
                &native_type_object,
                managed_type_native.values,
                sizeof(native_type_object)
            );
            memcpy(
                &native_type_handle,
                managed_type_native.values + sizeof(uintptr_t),
                sizeof(native_type_handle)
            );
            if (native_type_object != managed_graph_type_object ||
                !native_type_handle ||
                !append_pointer_vector(
                    &type_native_handles, &native_type_handle, 1
                ) || !write_handle_bytes(
                    type_native_output,
                    managed_type_native.values,
                    ALPHA_TYPE_NATIVE_ENTRY_BYTES
                ))
                goto cleanup;
            type_native_written_total += ALPHA_TYPE_NATIVE_ENTRY_BYTES;
            graph_written_total += managed_type_graph_node.count;
            clear_managed_type_identity();
            clear_managed_type_graph_state();
        }}
    }}
    for (uint64_t index = 0; index < vectors[5].count; index++) {{
        if (!sorted_pointer_contains(
                captured_type_roots,
                captured_type_root_count,
                vectors[5].values[index]
            ))
            goto cleanup;
    }}
    if (type_native_handles.count != type_graph_nodes.count ||
        type_native_handles.count != scan->type_native_node_count ||
        !pointer_vector_is_unique(&type_native_handles))
        goto cleanup;
    scan->type_native_unique_handle_count = type_native_handles.count;
    scan->type_native_roundtrip_complete = 1;
    for (uint32_t category = 0;
         category < ALPHA_MEMBER_CATEGORY_COUNT;
         category++) {{
        if (!pointer_vector_is_unique(&vectors[category])) goto cleanup;
        scan->member_inventory_totals[category] = vectors[category].count;
    }}
    if (!sorted_vectors_disjoint(&vectors[1], &vectors[2])) goto cleanup;
    if (method_metadata_objects.count != vectors[1].count + vectors[2].count ||
        method_metadata_objects.count != scan->method_native_method_count ||
        !pointer_vector_is_unique(&method_metadata_objects))
        goto cleanup;
    scan->method_native_unique_metadata_count = method_metadata_objects.count;
    scan->method_native_metadata_resolution_unique = 1;
    if (field_metadata_objects.count != vectors[0].count ||
        field_metadata_objects.count != scan->field_native_field_count ||
        !field_metadata_stride ||
        !pointer_vector_is_unique(&field_metadata_objects))
        goto cleanup;
    alpha_field_native_candidate *field_candidates =
        (alpha_field_native_candidate *)field_native_candidates.values;
    uint64_t field_candidate_count = field_metadata_objects.count;
    uint32_t layout_candidate_count = 0;
    if (!field_candidate_count || !field_candidates) goto cleanup;
    field_token_dword_index = field_candidates[0].token_dword_index;
    for (uint64_t field_index = 0;
         field_index < field_candidate_count;
         field_index++) {{
        alpha_field_native_candidate *field = &field_candidates[field_index];
        if (field->token_dword_index != field_token_dword_index ||
            field->token_dword_index >=
                field_metadata_stride / sizeof(uint32_t) ||
            field->name_qword_index >=
                field_metadata_stride / sizeof(uintptr_t) ||
            field->type_qword_index >=
                field_metadata_stride / sizeof(uintptr_t) ||
            field->parent_qword_index >=
                field_metadata_stride / sizeof(uintptr_t))
            goto cleanup;
    }}
    for (uint32_t dword = 0;
         dword < field_metadata_stride / sizeof(uint32_t);
         dword++) {{
        int candidate = 1;
        for (uint64_t field_index = 0;
             field_index < field_candidate_count;
             field_index++) {{
            alpha_field_native_candidate *field =
                &field_candidates[field_index];
            if (dword == field->token_dword_index ||
                dword / 2u == field->name_qword_index ||
                dword / 2u == field->type_qword_index ||
                dword / 2u == field->parent_qword_index) {{
                candidate = 0;
                break;
            }}
        }}
        if (!candidate) continue;
        layout_candidate_count++;
        if (layout_candidate_count == 1)
            field_offset_dword_index = dword;
    }}
    if (layout_candidate_count != 1 ||
        field_offset_dword_index == UINT32_MAX ||
        field_offset_dword_index == field_token_dword_index)
        goto cleanup;
    for (uint64_t field_index = 0;
         field_index < field_candidate_count;
         field_index++) {{
        alpha_field_native_candidate *field = &field_candidates[field_index];
        uint32_t field_offset = 0, reserved = 0;
        memcpy(
            &field_offset,
            field->metadata_sample +
                field_offset_dword_index * sizeof(uint32_t),
            sizeof(field_offset)
        );
        if (!write_handle_bytes(
                field_native_output,
                &field->member_object,
                sizeof(field->member_object)
            ) || !write_handle_bytes(
                field_native_output,
                &field->metadata_object,
                sizeof(field->metadata_object)
            ) || !write_handle_bytes(
                field_native_output,
                &field->declaring_class,
                sizeof(field->declaring_class)
            ) || !write_handle_bytes(
                field_native_output,
                &field->type_handle,
                sizeof(field->type_handle)
            ) || !write_handle_bytes(
                field_native_output,
                &field_offset,
                sizeof(field_offset)
            ) || !write_handle_bytes(
                field_native_output,
                &field->metadata_token,
                sizeof(field->metadata_token)
            ) || !write_handle_bytes(
                field_native_output,
                &field->attributes,
                sizeof(field->attributes)
            ) || !write_handle_bytes(
                field_native_output,
                &reserved,
                sizeof(reserved)
            ))
            goto cleanup;
        field_native_written_total += ALPHA_FIELD_NATIVE_ENTRY_BYTES;
    }}
    scan->field_native_unique_metadata_count = field_candidate_count;
    scan->field_native_metadata_stride = field_metadata_stride;
    scan->field_native_offset_dword_index = field_offset_dword_index;
    scan->field_native_token_dword_index = field_token_dword_index;
    scan->field_native_metadata_resolution_unique = 1;
    scan->field_native_layout_derived = 1;
    scan->member_inventory_all_objects_class_valid = 1;
    scan->member_inventory_globally_unique = 1;
    LARGE_INTEGER beginning;
    beginning.QuadPart = 0;
    if (!SetFilePointerEx(output, beginning, NULL, FILE_BEGIN) ||
        !write_member_observation_header(
            output, scan, scan->member_inventory_totals
        ) || !FlushFileBuffers(output))
        goto cleanup;
    uint64_t expected_bytes = ALPHA_MEMBER_OBSERVATION_HEADER_BYTES +
        captured_type_root_count * ALPHA_MEMBER_OBSERVATION_ENTRY_BYTES;
    for (uint32_t category = 0;
         category < ALPHA_MEMBER_CATEGORY_COUNT;
         category++)
        expected_bytes += vectors[category].count * sizeof(uintptr_t);
    if (written_total != expected_bytes) goto cleanup;
    LARGE_INTEGER identity_size, detail_size, graph_size, type_native_size;
    LARGE_INTEGER method_native_size;
    LARGE_INTEGER field_native_size;
    if (!FlushFileBuffers(identity_output) ||
        !GetFileSizeEx(identity_output, &identity_size) ||
        identity_size.QuadPart < 0 ||
        (uint64_t)identity_size.QuadPart != identity_written_total)
        goto cleanup;
    if (!FlushFileBuffers(detail_output) ||
        !GetFileSizeEx(detail_output, &detail_size) ||
        detail_size.QuadPart < 0 ||
        (uint64_t)detail_size.QuadPart != detail_written_total)
        goto cleanup;
    if (!FlushFileBuffers(graph_output) ||
        !GetFileSizeEx(graph_output, &graph_size) ||
        graph_size.QuadPart < 0 ||
        (uint64_t)graph_size.QuadPart != graph_written_total)
        goto cleanup;
    if (!FlushFileBuffers(type_native_output) ||
        !GetFileSizeEx(type_native_output, &type_native_size) ||
        type_native_size.QuadPart < 0 ||
        (uint64_t)type_native_size.QuadPart != type_native_written_total)
        goto cleanup;
    if (!FlushFileBuffers(method_native_output) ||
        !GetFileSizeEx(method_native_output, &method_native_size) ||
        method_native_size.QuadPart < 0 ||
        (uint64_t)method_native_size.QuadPart != method_native_written_total)
        goto cleanup;
    if (!FlushFileBuffers(field_native_output) ||
        !GetFileSizeEx(field_native_output, &field_native_size) ||
        field_native_size.QuadPart < 0 ||
        (uint64_t)field_native_size.QuadPart != field_native_written_total)
        goto cleanup;
    CloseHandle(output);
    output = INVALID_HANDLE_VALUE;
    CloseHandle(identity_output);
    identity_output = INVALID_HANDLE_VALUE;
    if (!sha256_file(
            member_observation_output, member_observation_sha256
        ) || !sha256_file(
            type_identity_observation_output, type_identity_sha256
        ) || !SetFilePointerEx(
            detail_output, beginning, NULL, FILE_BEGIN
        ) || !write_member_detail_header(
            detail_output,
            scan,
            scan->member_inventory_totals,
            member_observation_sha256,
            type_identity_sha256
        ) || !FlushFileBuffers(detail_output))
        goto cleanup;
    CloseHandle(detail_output);
    detail_output = INVALID_HANDLE_VALUE;
    if (!sha256_file(
            member_detail_observation_output, member_detail_sha256
        ) || !SetFilePointerEx(
            graph_output, beginning, NULL, FILE_BEGIN
        ) || !write_type_graph_header(
            graph_output,
            scan,
            type_identity_sha256,
            member_detail_sha256,
            type_graph_nodes.count,
            observed_type_count
        ) || !FlushFileBuffers(graph_output))
        goto cleanup;
    CloseHandle(graph_output);
    graph_output = INVALID_HANDLE_VALUE;
    if (!sha256_file(
            type_graph_observation_output, type_graph_sha256
        ) || !SetFilePointerEx(
            type_native_output, beginning, NULL, FILE_BEGIN
        ) || !write_type_native_header(
            type_native_output,
            scan,
            type_graph_sha256,
            type_graph_nodes.count,
            type_native_handles.count
        ) || !FlushFileBuffers(type_native_output))
        goto cleanup;
    CloseHandle(type_native_output);
    type_native_output = INVALID_HANDLE_VALUE;
    if (!SetFilePointerEx(
            method_native_output, beginning, NULL, FILE_BEGIN
        ) || !write_method_native_header(
            method_native_output,
            scan,
            member_detail_sha256,
            type_graph_sha256,
            image_base,
            image_bytes,
            observed_type_count,
            method_metadata_objects.count
        ) || !FlushFileBuffers(method_native_output))
        goto cleanup;
    CloseHandle(method_native_output);
    method_native_output = INVALID_HANDLE_VALUE;
    if (!sha256_file(
            method_native_observation_output, method_native_sha256
        ) || !SetFilePointerEx(
            field_native_output, beginning, NULL, FILE_BEGIN
        ) || !write_field_native_header(
            field_native_output,
            scan,
            member_detail_sha256,
            type_graph_sha256,
            method_native_sha256,
            observed_type_count,
            field_candidate_count,
            field_metadata_stride,
            field_offset_dword_index,
            field_token_dword_index
        ) || !FlushFileBuffers(field_native_output))
        goto cleanup;
    scan->type_identity_assembly_count = scan->assembly_count;
    scan->type_identity_type_count = observed_type_count;
    scan->type_identity_all_names_valid = 1;
    scan->type_identity_references_valid = 1;
    scan->member_detail_type_count = observed_type_count;
    scan->member_detail_observation_bytes = detail_written_total;
    scan->type_graph_root_count = observed_type_count;
    scan->type_graph_node_count = type_graph_nodes.count;
    scan->type_graph_observation_bytes = graph_written_total;
    scan->type_graph_reference_closure_complete = 1;
    scan->type_native_observation_bytes = type_native_written_total;
    scan->method_native_type_count = observed_type_count;
    scan->method_native_observation_bytes = method_native_written_total;
    scan->field_native_type_count = observed_type_count;
    scan->field_native_observation_bytes = field_native_written_total;
    ok = 1;

cleanup:
    if (managed_probe_hook) UnhookWindowsHookEx(managed_probe_hook);
    managed_probe_hook = NULL;
    if (managed_probe_event) CloseHandle(managed_probe_event);
    managed_probe_event = NULL;
    managed_probe_reflection = NULL;
    managed_probe_message = 0;
    InterlockedExchange(&managed_probe_mode, 0);
    clear_managed_member_buffers();
    clear_managed_type_identity();
    clear_managed_member_detail();
    clear_managed_method_native();
    clear_managed_field_native();
    clear_managed_type_graph_state();
    if (output != INVALID_HANDLE_VALUE) CloseHandle(output);
    if (identity_output != INVALID_HANDLE_VALUE) CloseHandle(identity_output);
    if (detail_output != INVALID_HANDLE_VALUE) CloseHandle(detail_output);
    if (graph_output != INVALID_HANDLE_VALUE) CloseHandle(graph_output);
    if (type_native_output != INVALID_HANDLE_VALUE) CloseHandle(type_native_output);
    if (method_native_output != INVALID_HANDLE_VALUE)
        CloseHandle(method_native_output);
    if (field_native_output != INVALID_HANDLE_VALUE)
        CloseHandle(field_native_output);
    if (ok && _wchmod(member_observation_output, 0600)) ok = 0;
    if (ok && _wchmod(type_identity_observation_output, 0600)) ok = 0;
    if (ok && _wchmod(member_detail_observation_output, 0600)) ok = 0;
    if (ok && _wchmod(type_graph_observation_output, 0600)) ok = 0;
    if (ok && _wchmod(type_native_observation_output, 0600)) ok = 0;
    if (ok && _wchmod(method_native_observation_output, 0600)) ok = 0;
    if (ok && _wchmod(field_native_observation_output, 0600)) ok = 0;
    if (!ok) DeleteFileW(member_observation_output);
    if (!ok) DeleteFileW(type_identity_observation_output);
    if (!ok) DeleteFileW(member_detail_observation_output);
    if (!ok) DeleteFileW(type_graph_observation_output);
    if (!ok) DeleteFileW(type_native_observation_output);
    if (!ok) DeleteFileW(method_native_observation_output);
    if (!ok) DeleteFileW(field_native_observation_output);
    if (ok) {{
        captured_type_native_handles = type_native_handles.values;
        captured_type_native_handle_count = type_native_handles.count;
        type_native_handles.values = NULL;
        type_native_handles.capacity = 0;
    }}
    for (uint32_t category = 0;
         category < ALPHA_MEMBER_CATEGORY_COUNT;
         category++)
        free(vectors[category].values);
    free(type_graph_nodes.values);
    free(type_graph_references.values);
    free(type_native_handles.values);
    free(method_metadata_objects.values);
    free(field_metadata_objects.values);
    free(field_native_candidates.values);
    free(captured_type_roots);
    captured_type_roots = NULL;
    captured_type_root_count = 0;
    free(captured_assembly_type_counts);
    captured_assembly_type_counts = NULL;
    if (captured_assembly_full_names) {{
        for (uint32_t assembly = 0; assembly < scan->assembly_count; assembly++)
            free(captured_assembly_full_names[assembly]);
    }}
    free(captured_assembly_full_names);
    captured_assembly_full_names = NULL;
    if (ok) {{
        scan->member_inventory_type_count = observed_type_count;
        scan->member_inventory_observation_written = 1;
        scan->member_inventory_observation_complete =
            scan->member_inventory_all_objects_class_valid &&
            scan->member_inventory_globally_unique &&
            scan->member_inventory_completed_slice_count ==
                observed_type_count;
        scan->type_identity_observation_written = 1;
        scan->type_identity_observation_complete =
            scan->type_identity_all_names_valid &&
            scan->type_identity_references_valid &&
            scan->type_identity_type_count == observed_type_count &&
            scan->type_identity_assembly_count == scan->assembly_count;
        scan->member_detail_observation_written = 1;
        scan->member_detail_observation_complete =
            scan->member_detail_type_count == observed_type_count &&
            scan->member_detail_observation_bytes == detail_written_total;
        scan->type_graph_observation_written = 1;
        scan->type_graph_observation_complete =
            scan->type_graph_reference_closure_complete &&
            scan->type_graph_root_count == observed_type_count &&
            scan->type_graph_node_count == type_graph_nodes.count &&
            scan->type_graph_observation_bytes == graph_written_total;
        scan->type_native_observation_written = 1;
        scan->type_native_observation_complete =
            scan->type_native_roundtrip_complete &&
            scan->type_native_node_count == type_graph_nodes.count &&
            scan->type_native_unique_handle_count == type_graph_nodes.count &&
            scan->type_native_observation_bytes == type_native_written_total;
        scan->method_native_observation_written = 1;
        scan->method_native_observation_complete =
            scan->method_native_metadata_resolution_unique &&
            scan->method_native_slot_layout_unique &&
            scan->method_native_type_count == observed_type_count &&
            scan->method_native_method_count ==
                vectors[1].count + vectors[2].count &&
            scan->method_native_unique_metadata_count ==
                scan->method_native_method_count &&
            scan->method_native_observation_bytes ==
                method_native_written_total;
        scan->field_native_observation_written = 1;
        scan->field_native_observation_complete =
            scan->field_native_metadata_resolution_unique &&
            scan->field_native_layout_derived &&
            scan->field_native_type_count == observed_type_count &&
            scan->field_native_field_count == vectors[0].count &&
            scan->field_native_unique_metadata_count ==
                scan->field_native_field_count &&
            scan->field_native_observation_bytes ==
                field_native_written_total;
    }}
    return ok && scan->member_inventory_observation_complete &&
        scan->type_identity_observation_complete &&
        scan->member_detail_observation_complete &&
        scan->type_graph_observation_complete &&
        scan->type_native_observation_complete &&
        scan->method_native_observation_complete &&
        scan->field_native_observation_complete;
}}

static void write_status(
    const char *status,
    const char *observed_executable_sha256,
    const alpha_resolver_scan *resolver,
    const alpha_reflection_scan *reflection,
    const alpha_scan *scan,
    const alpha_candidate *candidate,
    const char *metadata_sha256
) {{
    FILE *output = _wfopen(status_output, L"wb");
    if (!output) return;
    uint32_t cached_name_field_unique_operation_count = 0;
    uint32_t name_getter_unique_operation_count = 0;
    uintptr_t image_base = (uintptr_t)GetModuleHandleW(NULL);
    if (reflection) {{
        for (uint32_t operation = 0;
             operation < ALPHA_NAME_OPERATION_COUNT;
             operation++) {{
            if (reflection->cached_name_field_semantically_unique[operation])
                cached_name_field_unique_operation_count++;
            if (reflection->name_getter_candidate_count[operation] == 1)
                name_getter_unique_operation_count++;
        }}
    }}
    fprintf(output,
        "{{\n"
        "  \"schema\": \"alpha.runtime-metadata-capture/v1\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"executable_hash_matches\": %s,\n"
        "  \"fresh_runtime_observation\": true,\n"
        "  \"runtime_resolver_anchor_count\": %u,\n"
        "  \"runtime_resolver_reference_count\": %llu,\n"
        "  \"runtime_resolver_candidate_count\": %llu,\n"
        "  \"runtime_resolver_strong_count\": %u,\n"
        "  \"runtime_resolver_direct_caller_count\": %llu,\n"
        "  \"runtime_resolver_unique\": %s,\n"
        "  \"reflection_state_initialized\": %s,\n"
        "  \"reflection_bootstrap_attempt_count\": %u,\n"
        "  \"reflection_bootstrap_wait_milliseconds\": %llu,\n"
        "  \"reflection_type_cache_count\": %llu,\n"
        "  \"reflection_initialized_type_cache_count\": %llu,\n"
        "  \"reflection_type_resolver_helper_unique\": %s,\n"
        "  \"reflection_type_cache_count_matches_preflight\": %s,\n"
        "  \"reflection_expected_owner_class_count\": %u,\n"
        "  \"reflection_initialized_owner_class_count\": %u,\n"
        "  \"reflection_contract_owner_class_count\": %u,\n"
        "  \"reflection_dynamically_resolved_owner_class_count\": %u,\n"
        "  \"reflection_all_contract_owner_classes_available\": %s,\n"
        "  \"reflection_vtable_boundary_derived\": %s,\n"
        "  \"reflection_method_layout_unique\": %s,\n"
        "  \"reflection_method_record_count\": %llu,\n"
        "  \"reflection_declaring_class_field_unique\": %s,\n"
        "  \"reflection_method_pointer_field_unique\": %s,\n"
        "  \"reflection_observed_class_layout_complete\": %s,\n"
        "  \"reflection_name_object_reference_counts\": {{\n"
        "    \"method.name\": %llu,\n"
        "    \"field.name\": %llu,\n"
        "    \"property.name\": %llu,\n"
        "    \"parameter.name\": %llu\n"
        "  }},\n"
        "  \"reflection_cached_name_field_unique_operation_count\": %u,\n"
        "  \"reflection_name_getter_candidate_counts\": {{\n"
        "    \"method.name\": %u,\n"
        "    \"field.name\": %u,\n"
        "    \"property.name\": %u,\n"
        "    \"parameter.name\": %u\n"
        "  }},\n"
        "  \"reflection_name_getter_unique_operation_count\": %u,\n"
        "  \"reflection_name_getter_rvas\": {{\n"
        "    \"method.name\": %llu,\n"
        "    \"field.name\": %llu,\n"
        "    \"property.name\": %llu,\n"
        "    \"parameter.name\": %llu\n"
        "  }},\n"
        "  \"reflection_name_getters_semantically_unique\": %s,\n"
        "  \"reflection_parameter_type_object_reference_count\": %llu,\n"
        "  \"reflection_parameter_type_field_semantically_unique\": %s,\n"
        "  \"reflection_parameter_type_getter_candidate_count\": %u,\n"
        "  \"reflection_parameter_type_getter_semantically_unique\": %s,\n"
        "  \"reflection_parameter_flag_object_reference_count\": %llu,\n"
        "  \"reflection_parameter_flag_getter_candidate_counts\": {{\n"
        "    \"parameter.is_in\": %u,\n"
        "    \"parameter.is_out\": %u,\n"
        "    \"parameter.is_optional\": %u\n"
        "  }},\n"
        "  \"reflection_parameter_flag_field_semantically_unique\": %s,\n"
        "  \"reflection_parameter_flag_observation_complete\": %s,\n"
        "  \"reflection_parameter_flag_getters_semantically_unique\": %s,\n"
        "  \"reflection_parameter_default_field_semantically_unique\": %s,\n"
        "  \"reflection_parameter_default_getter_candidate_count\": %u,\n"
        "  \"reflection_parameter_default_getter_semantically_unique\": %s,\n"
        "  \"reflection_field_attributes_object_reference_count\": %llu,\n"
        "  \"reflection_field_attributes_getter_candidate_count\": %u,\n"
        "  \"reflection_field_attributes_getter_semantically_unique\": %s,\n"
        "  \"reflection_field_attributes_observation_complete\": %s,\n"
        "  \"reflection_property_named_object_reference_count\": %llu,\n"
        "  \"reflection_property_accessor_field_support_counts\": {{\n"
        "    \"property.getter\": %llu,\n"
        "    \"property.setter\": %llu\n"
        "  }},\n"
        "  \"reflection_property_accessor_getter_candidate_counts\": {{\n"
        "    \"property.getter\": %u,\n"
        "    \"property.setter\": %u\n"
        "  }},\n"
        "  \"reflection_property_accessors_semantically_unique\": %s,\n"
        "  \"reflection_method_name_decoder_derived\": %s,\n"
        "  \"reflection_method_name_lazy_initializer_semantically_bound\": %s,\n"
        "  \"reflection_method_name_window_candidate_count\": %u,\n"
        "  \"reflection_method_name_window_thread_matches_callback\": %s,\n"
        "  \"reflection_method_name_managed_callback_complete\": %s,\n"
        "  \"reflection_method_name_metadata_field_qword\": %u,\n"
        "  \"reflection_method_name_node_field_qword\": %u,\n"
        "  \"reflection_method_name_encoded_field_qword\": %u,\n"
        "  \"reflection_method_name_getter_rva\": %llu,\n"
        "  \"reflection_method_name_length_helper_rva\": %llu,\n"
        "  \"reflection_method_name_managed_string_helper_rva\": %llu,\n"
        "  \"reflection_method_name_lazy_initializer_rva\": %llu,\n"
        "  \"reflection_method_name_decode_attempt_count\": %llu,\n"
        "  \"reflection_method_name_decode_success_count\": %llu,\n"
        "  \"reflection_method_name_lazy_initialization_count\": %llu,\n"
        "  \"reflection_method_name_decode_failure_reason\": %u,\n"
        "  \"reflection_method_name_decode_failure_index\": %llu,\n"
        "  \"reflection_method_name_decode_failure_method_rva\": %llu,\n"
        "  \"reflection_method_name_decode_failure_owner_index\": %u,\n"
        "  \"reflection_method_name_decode_failure_byte_index\": %u,\n"
        "  \"reflection_method_name_decode_failure_byte_value\": %u,\n"
        "  \"reflection_method_parameter_count_field_candidate_count\": %u,\n"
        "  \"reflection_method_parameter_count_field_semantically_unique\": %s,\n"
        "  \"reflection_method_parameter_count_observation_complete\": %s,\n"
        "  \"reflection_runtime_operation_name_contract_count\": %u,\n"
        "  \"reflection_runtime_named_operation_match_count\": %u,\n"
        "  \"reflection_runtime_named_operation_unique_count\": %u,\n"
        "  \"reflection_runtime_arity_operation_match_count\": %u,\n"
        "  \"reflection_runtime_arity_operation_unique_count\": %u,\n"
        "  \"reflection_dispatch_contract_complete\": %s,\n"
        "  \"reflection_dispatch_manifest_written\": %s,\n"
        "  \"inventory_runtime_operation_contract_count\": %u,\n"
        "  \"inventory_runtime_named_operation_match_count\": %u,\n"
        "  \"inventory_runtime_arity_operation_match_count\": %u,\n"
        "  \"inventory_runtime_arity_operation_unique_count\": %u,\n"
        "  \"inventory_dispatch_contract_complete\": %s,\n"
        "  \"inventory_dispatch_manifest_written\": %s,\n"
        "  \"managed_window_candidate_count\": %u,\n"
        "  \"managed_window_thread_matches_callback\": %s,\n"
        "  \"managed_thread_object_observed\": %s,\n"
        "  \"managed_thread_class_matches\": %s,\n"
        "  \"current_domain_object_observed\": %s,\n"
        "  \"current_domain_class_matches\": %s,\n"
        "  \"managed_thread_observation_complete\": %s,\n"
        "  \"assembly_array_observed\": %s,\n"
        "  \"assembly_array_layout_candidate_count\": %u,\n"
        "  \"assembly_array_layout_unique\": %s,\n"
        "  \"assembly_count\": %u,\n"
        "  \"all_assembly_objects_class_valid\": %s,\n"
        "  \"assembly_root_inventory_complete\": %s,\n"
        "  \"type_inventory_assembly_count\": %u,\n"
        "  \"type_inventory_type_count\": %llu,\n"
        "  \"type_inventory_completed_slice_count\": %u,\n"
        "  \"type_inventory_all_objects_class_valid\": %s,\n"
        "  \"type_inventory_globally_unique\": %s,\n"
        "  \"type_inventory_observation_written\": %s,\n"
        "  \"type_inventory_observation_complete\": %s,\n"
        "  \"member_inventory_type_count\": %llu,\n"
        "  \"member_inventory_field_count\": %llu,\n"
        "  \"member_inventory_method_count\": %llu,\n"
        "  \"member_inventory_constructor_count\": %llu,\n"
        "  \"member_inventory_property_count\": %llu,\n"
        "  \"member_inventory_event_count\": %llu,\n"
        "  \"member_inventory_nested_type_count\": %llu,\n"
        "  \"member_inventory_completed_slice_count\": %u,\n"
        "  \"member_inventory_all_objects_class_valid\": %s,\n"
        "  \"member_inventory_globally_unique\": %s,\n"
        "  \"member_inventory_observation_written\": %s,\n"
        "  \"member_inventory_observation_complete\": %s,\n"
        "  \"type_identity_assembly_count\": %u,\n"
        "  \"type_identity_type_count\": %llu,\n"
        "  \"type_identity_relation_count\": %llu,\n"
        "  \"type_identity_all_names_valid\": %s,\n"
        "  \"type_identity_references_valid\": %s,\n"
        "  \"type_identity_observation_written\": %s,\n"
        "  \"type_identity_observation_complete\": %s,\n"
        "  \"member_detail_type_count\": %llu,\n"
        "  \"member_detail_observation_bytes\": %llu,\n"
        "  \"member_detail_observation_written\": %s,\n"
        "  \"member_detail_observation_complete\": %s,\n"
        "  \"type_graph_root_count\": %llu,\n"
        "  \"type_graph_node_count\": %llu,\n"
        "  \"type_graph_observation_bytes\": %llu,\n"
        "  \"type_graph_reference_closure_complete\": %s,\n"
        "  \"type_graph_observation_written\": %s,\n"
        "  \"type_graph_observation_complete\": %s,\n"
        "  \"type_native_node_count\": %llu,\n"
        "  \"type_native_unique_handle_count\": %llu,\n"
        "  \"type_native_observation_bytes\": %llu,\n"
        "  \"type_native_roundtrip_complete\": %s,\n"
        "  \"type_native_observation_written\": %s,\n"
        "  \"type_native_observation_complete\": %s,\n"
        "  \"method_native_type_count\": %llu,\n"
        "  \"method_native_method_count\": %llu,\n"
        "  \"method_native_executable_count\": %llu,\n"
        "  \"method_native_unique_metadata_count\": %llu,\n"
        "  \"method_native_observation_bytes\": %llu,\n"
        "  \"method_native_slot_byte_offset\": %u,\n"
        "  \"method_native_metadata_resolution_unique\": %s,\n"
        "  \"method_native_slot_layout_unique\": %s,\n"
        "  \"method_native_observation_written\": %s,\n"
        "  \"method_native_observation_complete\": %s,\n"
        "  \"field_native_type_count\": %llu,\n"
        "  \"field_native_field_count\": %llu,\n"
        "  \"field_native_unique_metadata_count\": %llu,\n"
        "  \"field_native_observation_bytes\": %llu,\n"
        "  \"field_native_metadata_stride\": %u,\n"
        "  \"field_native_offset_dword_index\": %u,\n"
        "  \"field_native_token_dword_index\": %u,\n"
        "  \"field_native_metadata_resolution_unique\": %s,\n"
        "  \"field_native_layout_derived\": %s,\n"
        "  \"field_native_observation_written\": %s,\n"
        "  \"field_native_observation_complete\": %s,\n"
        "  \"metadata_usage_count\": %llu,\n"
        "  \"metadata_usage_layout_match_count\": %u,\n"
        "  \"metadata_usage_array_match_count\": %u,\n"
        "  \"metadata_usage_observation_bytes\": %llu,\n"
        "  \"metadata_usage_layout_derived\": %s,\n"
        "  \"metadata_usage_slots_unique\": %s,\n"
        "  \"metadata_usage_observation_written\": %s,\n"
        "  \"metadata_usage_observation_complete\": %s,\n"
        "  \"type_metadata_usage_count\": %llu,\n"
        "  \"type_registration_count\": %llu,\n"
        "  \"type_registration_array_match_count\": %u,\n"
        "  \"type_metadata_usage_observation_bytes\": %llu,\n"
        "  \"type_metadata_usage_handles_unique\": %s,\n"
        "  \"type_metadata_usage_observation_written\": %s,\n"
        "  \"type_metadata_usage_observation_complete\": %s,\n"
        "  \"reflection_semantic_operation_count\": %u,\n"
        "  \"candidate_count\": %d,\n"
        "  \"candidate_identity_count\": %d,\n"
        "  \"memory_region_count\": %llu,\n"
        "  \"memory_bytes_observed\": %llu,\n"
        "  \"metadata_bytes\": %llu,\n"
        "  \"metadata_table_pairs\": %u,\n"
        "  \"metadata_sha256\": \"%s\",\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_heap_range_used\": false,\n"
        "  \"network_used\": false,\n"
        "  \"external_runtime_plugin_used\": false\n"
        "}}\n",
        status,
        (unsigned long)GetCurrentProcessId(),
        expected_executable_sha256,
        observed_executable_sha256 ? observed_executable_sha256 : "",
        observed_executable_sha256 &&
            !strcmp(observed_executable_sha256, expected_executable_sha256)
            ? "true" : "false",
        resolver ? resolver->anchor_count : 0,
        (unsigned long long)(resolver ? resolver->reference_count : 0),
        (unsigned long long)(resolver ? resolver->candidate_count : 0),
        resolver ? resolver->strong_count : 0,
        (unsigned long long)(
            resolver ? resolver->selected_target_direct_caller_count : 0
        ),
        resolver && resolver->strong_count == 1 && resolver->selected_target &&
            resolver->selected_target_direct_caller_count >= 2
            ? "true" : "false",
        reflection && reflection->state_slot && reflection->state_value
            ? "true" : "false",
        reflection ? reflection->bootstrap_attempt_count : 0,
        (unsigned long long)(reflection
            ? reflection->bootstrap_wait_milliseconds : 0),
        (unsigned long long)(reflection ? reflection->type_cache_count : 0),
        (unsigned long long)(
            reflection ? reflection->initialized_type_cache_count : 0
        ),
        reflection && reflection->distinct_type_resolver_helper_count == 1
            ? "true" : "false",
        reflection && (!expected_reflection_type_cache_count ||
            reflection->type_cache_count == expected_reflection_type_cache_count)
            ? "true" : "false",
        expected_reflection_owner_count,
        reflection ? reflection->initialized_required_owner_count : 0,
        required_reflection_owner_count,
        reflection ? reflection->dynamically_resolved_required_owner_count : 0,
        reflection && reflection->all_required_owner_classes_available
            ? "true" : "false",
        reflection && reflection->vtable_candidate_count
            ? "true" : "false",
        reflection && reflection->method_layout_candidate_count == 1
            ? "true" : "false",
        (unsigned long long)(reflection ? reflection->method_record_count : 0),
        reflection && reflection->declaring_class_candidate_count == 1
            ? "true" : "false",
        reflection && reflection->method_pointer_candidate_count == 1
            ? "true" : "false",
        reflection && reflection->observed_class_layout_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->name_object_reference_count[0] : 0),
        (unsigned long long)(reflection
            ? reflection->name_object_reference_count[1] : 0),
        (unsigned long long)(reflection
            ? reflection->name_object_reference_count[2] : 0),
        (unsigned long long)(reflection
            ? reflection->name_object_reference_count[3] : 0),
        cached_name_field_unique_operation_count,
        reflection ? reflection->name_getter_candidate_count[0] : 0,
        reflection ? reflection->name_getter_candidate_count[1] : 0,
        reflection ? reflection->name_getter_candidate_count[2] : 0,
        reflection ? reflection->name_getter_candidate_count[3] : 0,
        name_getter_unique_operation_count,
        (unsigned long long)(reflection && image_base &&
            reflection->name_getter_pointer[0] >= image_base
                ? reflection->name_getter_pointer[0] - image_base : 0),
        (unsigned long long)(reflection && image_base &&
            reflection->name_getter_pointer[1] >= image_base
                ? reflection->name_getter_pointer[1] - image_base : 0),
        (unsigned long long)(reflection && image_base &&
            reflection->name_getter_pointer[2] >= image_base
                ? reflection->name_getter_pointer[2] - image_base : 0),
        (unsigned long long)(reflection && image_base &&
            reflection->name_getter_pointer[3] >= image_base
                ? reflection->name_getter_pointer[3] - image_base : 0),
        reflection && reflection->name_getters_semantically_unique
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->name_object_reference_count[3] : 0),
        reflection && reflection->parameter_type_field_semantically_unique
            ? "true" : "false",
        reflection ? reflection->parameter_type_getter_candidate_count : 0,
        reflection && reflection->parameter_type_getter_semantically_unique
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->parameter_flag_object_reference_count : 0),
        reflection ? reflection->parameter_flag_getter_candidate_count[0] : 0,
        reflection ? reflection->parameter_flag_getter_candidate_count[1] : 0,
        reflection ? reflection->parameter_flag_getter_candidate_count[2] : 0,
        reflection && reflection->parameter_flag_field_semantically_unique
            ? "true" : "false",
        reflection && reflection->parameter_flag_observation_complete
            ? "true" : "false",
        reflection && reflection->parameter_flag_getters_semantically_unique
            ? "true" : "false",
        reflection && reflection->parameter_default_field_semantically_unique
            ? "true" : "false",
        reflection ? reflection->parameter_default_getter_candidate_count : 0,
        reflection && reflection->parameter_default_getter_semantically_unique
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->field_attributes_object_reference_count : 0),
        reflection ? reflection->field_attributes_getter_candidate_count : 0,
        reflection && reflection->field_attributes_getter_semantically_unique
            ? "true" : "false",
        reflection && reflection->field_attributes_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->property_named_object_reference_count : 0),
        (unsigned long long)(reflection
            ? reflection->property_accessor_field_support[0] : 0),
        (unsigned long long)(reflection
            ? reflection->property_accessor_field_support[1] : 0),
        reflection ? reflection->property_accessor_getter_candidate_count[0] : 0,
        reflection ? reflection->property_accessor_getter_candidate_count[1] : 0,
        reflection && reflection->property_accessors_semantically_unique
            ? "true" : "false",
        reflection && reflection->method_name_decoder_derived
            ? "true" : "false",
        reflection &&
            reflection->method_name_lazy_initializer_semantically_bound
            ? "true" : "false",
        reflection ? reflection->method_name_window_candidate_count : 0,
        reflection && reflection->method_name_window_thread_id &&
            reflection->method_name_window_thread_id ==
                reflection->method_name_callback_thread_id
            ? "true" : "false",
        reflection && reflection->method_name_managed_callback_complete
            ? "true" : "false",
        reflection ? reflection->method_name_metadata_field_qword : 0,
        reflection ? reflection->method_name_node_field_qword : 0,
        reflection ? reflection->method_name_encoded_field_qword : 0,
        (unsigned long long)(reflection
            ? reflection->method_name_getter_rva : 0),
        (unsigned long long)(reflection
            ? reflection->method_name_length_helper_rva : 0),
        (unsigned long long)(reflection
            ? reflection->method_name_managed_string_helper_rva : 0),
        (unsigned long long)(reflection
            ? reflection->method_name_lazy_initializer_rva : 0),
        (unsigned long long)(reflection
            ? reflection->method_name_decode_attempt_count : 0),
        (unsigned long long)(reflection
            ? reflection->method_name_decode_success_count : 0),
        (unsigned long long)(reflection
            ? reflection->method_name_lazy_initialization_count : 0),
        reflection ? reflection->method_name_decode_failure_reason : 0,
        (unsigned long long)(reflection
            ? reflection->method_name_decode_failure_index : 0),
        (unsigned long long)(reflection
            ? reflection->method_name_decode_failure_method_rva : 0),
        reflection ? reflection->method_name_decode_failure_owner_index : 0,
        reflection ? reflection->method_name_decode_failure_byte_index : 0,
        reflection ? reflection->method_name_decode_failure_byte_value : 0,
        reflection
            ? reflection->method_parameter_count_field_candidate_count : 0,
        reflection &&
            reflection->method_parameter_count_field_semantically_unique
            ? "true" : "false",
        reflection && reflection->method_parameter_count_observation_complete
            ? "true" : "false",
        required_reflection_operation_count,
        reflection ? reflection->runtime_named_operation_match_count : 0,
        reflection ? reflection->runtime_named_operation_unique_count : 0,
        reflection ? reflection->runtime_arity_operation_match_count : 0,
        reflection ? reflection->runtime_arity_operation_unique_count : 0,
        reflection && reflection->reflection_dispatch_contract_complete
            ? "true" : "false",
        reflection && reflection->reflection_dispatch_manifest_written
            ? "true" : "false",
        required_inventory_operation_count,
        reflection ? reflection->inventory_named_operation_match_count : 0,
        reflection ? reflection->inventory_arity_operation_match_count : 0,
        reflection ? reflection->inventory_arity_operation_unique_count : 0,
        reflection && reflection->inventory_dispatch_contract_complete
            ? "true" : "false",
        reflection && reflection->inventory_dispatch_manifest_written
            ? "true" : "false",
        reflection ? reflection->managed_window_candidate_count : 0,
        reflection && reflection->managed_window_thread_id &&
            reflection->managed_window_thread_id ==
                reflection->managed_probe_callback_thread_id
            ? "true" : "false",
        reflection && reflection->managed_thread_object_observed
            ? "true" : "false",
        reflection && reflection->managed_thread_class_matches
            ? "true" : "false",
        reflection && reflection->current_domain_object_observed
            ? "true" : "false",
        reflection && reflection->current_domain_class_matches
            ? "true" : "false",
        reflection && reflection->managed_thread_observation_complete
            ? "true" : "false",
        reflection && reflection->assembly_array_observed
            ? "true" : "false",
        reflection ? reflection->assembly_array_layout_candidate_count : 0,
        reflection && reflection->assembly_array_layout_unique
            ? "true" : "false",
        reflection ? reflection->assembly_count : 0,
        reflection && reflection->all_assembly_objects_class_valid
            ? "true" : "false",
        reflection && reflection->assembly_root_inventory_complete
            ? "true" : "false",
        reflection ? reflection->type_inventory_assembly_count : 0,
        (unsigned long long)(reflection
            ? reflection->type_inventory_type_count : 0),
        reflection ? reflection->type_inventory_completed_slice_count : 0,
        reflection && reflection->type_inventory_all_objects_class_valid
            ? "true" : "false",
        reflection && reflection->type_inventory_globally_unique
            ? "true" : "false",
        reflection && reflection->type_inventory_observation_written
            ? "true" : "false",
        reflection && reflection->type_inventory_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->member_inventory_type_count : 0),
        (unsigned long long)(reflection
            ? reflection->member_inventory_totals[0] : 0),
        (unsigned long long)(reflection
            ? reflection->member_inventory_totals[1] : 0),
        (unsigned long long)(reflection
            ? reflection->member_inventory_totals[2] : 0),
        (unsigned long long)(reflection
            ? reflection->member_inventory_totals[3] : 0),
        (unsigned long long)(reflection
            ? reflection->member_inventory_totals[4] : 0),
        (unsigned long long)(reflection
            ? reflection->member_inventory_totals[5] : 0),
        reflection ? reflection->member_inventory_completed_slice_count : 0,
        reflection && reflection->member_inventory_all_objects_class_valid
            ? "true" : "false",
        reflection && reflection->member_inventory_globally_unique
            ? "true" : "false",
        reflection && reflection->member_inventory_observation_written
            ? "true" : "false",
        reflection && reflection->member_inventory_observation_complete
            ? "true" : "false",
        reflection ? reflection->type_identity_assembly_count : 0,
        (unsigned long long)(reflection
            ? reflection->type_identity_type_count : 0),
        (unsigned long long)(reflection
            ? reflection->type_identity_relation_count : 0),
        reflection && reflection->type_identity_all_names_valid
            ? "true" : "false",
        reflection && reflection->type_identity_references_valid
            ? "true" : "false",
        reflection && reflection->type_identity_observation_written
            ? "true" : "false",
        reflection && reflection->type_identity_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->member_detail_type_count : 0),
        (unsigned long long)(reflection
            ? reflection->member_detail_observation_bytes : 0),
        reflection && reflection->member_detail_observation_written
            ? "true" : "false",
        reflection && reflection->member_detail_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->type_graph_root_count : 0),
        (unsigned long long)(reflection
            ? reflection->type_graph_node_count : 0),
        (unsigned long long)(reflection
            ? reflection->type_graph_observation_bytes : 0),
        reflection && reflection->type_graph_reference_closure_complete
            ? "true" : "false",
        reflection && reflection->type_graph_observation_written
            ? "true" : "false",
        reflection && reflection->type_graph_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->type_native_node_count : 0),
        (unsigned long long)(reflection
            ? reflection->type_native_unique_handle_count : 0),
        (unsigned long long)(reflection
            ? reflection->type_native_observation_bytes : 0),
        reflection && reflection->type_native_roundtrip_complete
            ? "true" : "false",
        reflection && reflection->type_native_observation_written
            ? "true" : "false",
        reflection && reflection->type_native_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->method_native_type_count : 0),
        (unsigned long long)(reflection
            ? reflection->method_native_method_count : 0),
        (unsigned long long)(reflection
            ? reflection->method_native_executable_count : 0),
        (unsigned long long)(reflection
            ? reflection->method_native_unique_metadata_count : 0),
        (unsigned long long)(reflection
            ? reflection->method_native_observation_bytes : 0),
        reflection ? reflection->method_native_slot_byte_offset : 0,
        reflection && reflection->method_native_metadata_resolution_unique
            ? "true" : "false",
        reflection && reflection->method_native_slot_layout_unique
            ? "true" : "false",
        reflection && reflection->method_native_observation_written
            ? "true" : "false",
        reflection && reflection->method_native_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->field_native_type_count : 0),
        (unsigned long long)(reflection
            ? reflection->field_native_field_count : 0),
        (unsigned long long)(reflection
            ? reflection->field_native_unique_metadata_count : 0),
        (unsigned long long)(reflection
            ? reflection->field_native_observation_bytes : 0),
        reflection ? reflection->field_native_metadata_stride : 0,
        reflection ? reflection->field_native_offset_dword_index : 0,
        reflection ? reflection->field_native_token_dword_index : 0,
        reflection && reflection->field_native_metadata_resolution_unique
            ? "true" : "false",
        reflection && reflection->field_native_layout_derived
            ? "true" : "false",
        reflection && reflection->field_native_observation_written
            ? "true" : "false",
        reflection && reflection->field_native_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->metadata_usage_count : 0),
        reflection ? reflection->metadata_usage_layout_match_count : 0,
        reflection ? reflection->metadata_usage_array_match_count : 0,
        (unsigned long long)(reflection
            ? reflection->metadata_usage_observation_bytes : 0),
        reflection && reflection->metadata_usage_layout_derived
            ? "true" : "false",
        reflection && reflection->metadata_usage_slots_unique
            ? "true" : "false",
        reflection && reflection->metadata_usage_observation_written
            ? "true" : "false",
        reflection && reflection->metadata_usage_observation_complete
            ? "true" : "false",
        (unsigned long long)(reflection
            ? reflection->type_metadata_usage_count : 0),
        (unsigned long long)(reflection
            ? reflection->type_registration_count : 0),
        reflection ? reflection->type_registration_array_match_count : 0,
        (unsigned long long)(reflection
            ? reflection->type_metadata_usage_observation_bytes : 0),
        reflection && reflection->type_metadata_usage_handles_unique
            ? "true" : "false",
        reflection && reflection->type_metadata_usage_observation_written
            ? "true" : "false",
        reflection && reflection->type_metadata_usage_observation_complete
            ? "true" : "false",
        reflection ? reflection->semantic_operation_count : 0,
        scan ? scan->count : 0,
        scan ? distinct_identities(scan) : 0,
        (unsigned long long)(scan ? scan->regions : 0),
        (unsigned long long)(scan ? scan->bytes : 0),
        (unsigned long long)(candidate ? candidate->extent : 0),
        candidate ? candidate->table_pairs : 0,
        metadata_sha256 ? metadata_sha256 : ""
    );
    fclose(output);
    _wchmod(status_output, 0600);
}}

static DWORD WINAPI worker(void *unused) {{
    (void)unused;
    wchar_t executable[MAX_PATH * 8];
    char executable_sha256[65] = {{0}};
    DWORD length = GetModuleFileNameW(
        NULL, executable, (DWORD)(sizeof(executable) / sizeof(executable[0]))
    );
    alpha_scan empty_scan;
    alpha_resolver_scan resolver;
    alpha_reflection_scan reflection_scan;
    memset(&empty_scan, 0, sizeof(empty_scan));
    memset(&resolver, 0, sizeof(resolver));
    memset(&reflection_scan, 0, sizeof(reflection_scan));
    if (!length || length >= sizeof(executable) / sizeof(executable[0]) ||
        !sha256_file(executable, executable_sha256) ||
        strcmp(executable_sha256, expected_executable_sha256)) {{
        write_status(
            "executable-binding-rejected", executable_sha256,
            &resolver, &reflection_scan, &empty_scan, NULL, NULL
        );
        return 2;
    }}
    if (!scan_runtime_resolver(&resolver)) {{
        write_status(
            "runtime-resolver-identity-not-unique", executable_sha256,
            &resolver, &reflection_scan, &empty_scan, NULL, NULL
        );
        return 3;
    }}
    if (!wait_runtime_reflection(&resolver, &reflection_scan)) {{
        write_status(
            "runtime-reflection-bootstrap-rejected", executable_sha256,
            &resolver, &reflection_scan, &empty_scan, NULL, NULL
        );
        return 4;
    }}
    if (!write_reflection_dispatch_manifest(&reflection_scan)) {{
        write_status(
            "runtime-reflection-dispatch-write-failed", executable_sha256,
            &resolver, &reflection_scan, &empty_scan, NULL, NULL
        );
        return 11;
    }}
    if (!write_inventory_dispatch_manifest(&reflection_scan)) {{
        write_status(
            "runtime-inventory-dispatch-write-failed", executable_sha256,
            &resolver, &reflection_scan, &empty_scan, NULL, NULL
        );
        return 12;
    }}
    if (!observe_managed_thread(&reflection_scan)) {{
        write_status(
            "managed-thread-rendezvous-rejected", executable_sha256,
            &resolver, &reflection_scan, &empty_scan, NULL, NULL
        );
        return 13;
    }}
    if (!capture_runtime_types(&reflection_scan)) {{
        release_captured_type_native_handles();
        write_status(
            "runtime-type-inventory-rejected", executable_sha256,
            &resolver, &reflection_scan, &empty_scan, NULL, NULL
        );
        return 14;
    }}
    if (!capture_runtime_members(&reflection_scan)) {{
        release_captured_type_native_handles();
        write_status(
            "runtime-member-inventory-rejected", executable_sha256,
            &resolver, &reflection_scan, &empty_scan, NULL, NULL
        );
        return 15;
    }}
    alpha_scan first, second;
    if (!scan_runtime(&first)) {{
        release_captured_type_native_handles();
        write_status(
            "first-scan-failed", executable_sha256, &resolver,
            &reflection_scan, &first, NULL, NULL
        );
        return 5;
    }}
    const alpha_candidate *first_candidate = unique_identity(&first);
    if (!first_candidate) {{
        release_captured_type_native_handles();
        write_status(
            "metadata-identity-not-unique", executable_sha256, &resolver,
            &reflection_scan, &first, NULL, NULL
        );
        return 6;
    }}
    Sleep(500);
    if (!scan_runtime(&second)) {{
        release_captured_type_native_handles();
        write_status(
            "second-scan-failed", executable_sha256, &resolver,
            &reflection_scan, &second, NULL, NULL
        );
        return 7;
    }}
    const alpha_candidate *second_candidate = unique_identity(&second);
    if (!second_candidate || first_candidate->extent != second_candidate->extent ||
        strcmp(first_candidate->sha256, second_candidate->sha256)) {{
        release_captured_type_native_handles();
        write_status(
            "metadata-not-stable", executable_sha256, &resolver,
            &reflection_scan, &second, NULL, NULL
        );
        return 8;
    }}
    if (!dump_memory(second_candidate)) {{
        release_captured_type_native_handles();
        write_status(
            "metadata-write-failed", executable_sha256, &resolver,
            &reflection_scan, &second, second_candidate, NULL
        );
        return 9;
    }}
    char output_sha256[65] = {{0}};
    if (!sha256_file(metadata_output, output_sha256) ||
        strcmp(output_sha256, second_candidate->sha256)) {{
        DeleteFileW(metadata_output);
        release_captured_type_native_handles();
        write_status(
            "metadata-write-verification-failed", executable_sha256,
            &resolver, &reflection_scan, &second, second_candidate,
            output_sha256
        );
        return 10;
    }}
    uintptr_t usage_image_base = 0;
    uint64_t usage_image_bytes = 0;
    uint64_t usage_count = 0;
    uint32_t usage_layout_matches = 0;
    uint32_t usage_array_matches = 0;
    alpha_metadata_usage_layout usage_layout;
    const uintptr_t *usage_slots = NULL;
    memset(&usage_layout, 0, sizeof(usage_layout));
    if (!current_image_bounds(&usage_image_base, &usage_image_bytes) ||
        !discover_metadata_usage_count(
            second_candidate, usage_image_bytes,
            reflection_scan.method_native_method_count, &usage_count,
            &usage_layout_matches, &usage_layout
        ) || !scan_metadata_usage_array(
            usage_count, &usage_slots, &usage_array_matches
        ) || !write_metadata_usage_observation(
            &reflection_scan, second_candidate, output_sha256,
            usage_image_base, usage_image_bytes, usage_slots, usage_count,
            usage_layout_matches, usage_array_matches
        )) {{
        reflection_scan.metadata_usage_count = usage_count;
        reflection_scan.metadata_usage_layout_match_count = usage_layout_matches;
        reflection_scan.metadata_usage_array_match_count = usage_array_matches;
        DeleteFileW(metadata_usage_observation_output);
        release_captured_type_native_handles();
        write_status(
            "metadata-usage-observation-rejected", executable_sha256,
            &resolver, &reflection_scan, &second, second_candidate,
            output_sha256
        );
        return 16;
    }}
    alpha_type_metadata_usage_entry *type_usage_entries = NULL;
    uint64_t type_usage_count = 0;
    uint32_t maximum_type_source = 0;
    const uintptr_t *type_registration_array = NULL;
    uint64_t type_registration_count = 0;
    uint32_t type_registration_matches = 0;
    if (!collect_type_metadata_usages(
            second_candidate, &usage_layout, usage_count,
            &type_usage_entries, &type_usage_count, &maximum_type_source
        ) || !scan_type_registration_array(
            type_usage_entries, type_usage_count, maximum_type_source,
            &type_registration_array, &type_registration_count,
            &type_registration_matches
        ) || !write_type_metadata_usage_observation(
            &reflection_scan, output_sha256, usage_image_base,
            usage_image_bytes, type_registration_array,
            type_registration_count, type_usage_entries, type_usage_count,
            type_registration_matches
        )) {{
        reflection_scan.type_metadata_usage_count = type_usage_count;
        reflection_scan.type_registration_count = type_registration_count;
        reflection_scan.type_registration_array_match_count =
            type_registration_matches;
        DeleteFileW(type_metadata_usage_observation_output);
        if (type_usage_entries)
            HeapFree(GetProcessHeap(), 0, type_usage_entries);
        release_captured_type_native_handles();
        write_status(
            "type-metadata-usage-observation-rejected", executable_sha256,
            &resolver, &reflection_scan, &second, second_candidate,
            output_sha256
        );
        return 17;
    }}
    HeapFree(GetProcessHeap(), 0, type_usage_entries);
    release_captured_type_native_handles();
    write_status("complete", executable_sha256, &resolver, &reflection_scan, &second, second_candidate, output_sha256);
    return 0;
}}

BOOL WINAPI DllMain(HINSTANCE instance, DWORD reason, LPVOID reserved) {{
    (void)reserved;
    if (reason == DLL_PROCESS_ATTACH) {{
        self_module = instance;
        DisableThreadLibraryCalls(instance);
        HANDLE thread = CreateThread(NULL, 0, worker, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }}
    return TRUE;
}}
'''


def runtime_injector_source() -> str:
    source = r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <tlhelp32.h>
#include <stdint.h>
#include <stdio.h>
#include <wchar.h>

static DWORD unique_process(const wchar_t *basename, int *matches) {
    *matches = 0;
    DWORD selected = 0;
    HANDLE snapshot = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (snapshot == INVALID_HANDLE_VALUE) return 0;
    PROCESSENTRY32W entry;
    entry.dwSize = sizeof(entry);
    if (Process32FirstW(snapshot, &entry)) {
        do {
            if (!_wcsicmp(entry.szExeFile, basename)) {
                selected = entry.th32ProcessID;
                (*matches)++;
            }
        } while (Process32NextW(snapshot, &entry));
    }
    CloseHandle(snapshot);
    return *matches == 1 ? selected : 0;
}

static int module_loaded(DWORD pid, const wchar_t *path) {
    const wchar_t *base = wcsrchr(path, L'\\');
    base = base ? base + 1 : path;
    HANDLE snapshot = CreateToolhelp32Snapshot(
        TH32CS_SNAPMODULE | TH32CS_SNAPMODULE32, pid
    );
    if (snapshot == INVALID_HANDLE_VALUE) return 0;
    MODULEENTRY32W entry;
    entry.dwSize = sizeof(entry);
    int found = 0;
    if (Module32FirstW(snapshot, &entry)) {
        do {
            if (!_wcsicmp(entry.szExePath, path) ||
                !_wcsicmp(entry.szModule, base)) {
                found = 1;
                break;
            }
        } while (Module32NextW(snapshot, &entry));
    }
    CloseHandle(snapshot);
    return found;
}

static int unique_module_copy(const wchar_t *source, wchar_t *target, size_t count) {
    size_t length = wcslen(source);
    if (length + 32 >= count) return 0;
    wcscpy(target, source);
    wchar_t *dot = wcsrchr(target, L'.');
    wchar_t *tail = wcsrchr(target, L'\\');
    size_t keep = length;
    if (dot != NULL && (tail == NULL || dot > tail)) keep = (size_t)(dot - target);
    if (swprintf(
            target + keep, count - keep, L".r%lu.%llu.dll",
            (unsigned long)GetCurrentProcessId(),
            (unsigned long long)GetTickCount64()
        ) < 0) {
        return 0;
    }
    return CopyFileW(source, target, FALSE) ? 1 : 0;
}

int wmain(int argc, wchar_t **argv) {
    if (argc != 3 || !argv[1][0] || !argv[2][0]) {
        fwprintf(stderr, L"usage: alpha-runtime-injector DLL PROCESS.EXE\n");
        return 2;
    }
    wchar_t dll[MAX_PATH * 16];
    DWORD length = GetFullPathNameW(
        argv[1], (DWORD)(sizeof(dll) / sizeof(dll[0])), dll, NULL
    );
    if (!length || length >= sizeof(dll) / sizeof(dll[0])) return 3;
    int matches = 0;
    DWORD pid = unique_process(argv[2], &matches);
    if (!pid) {
        fwprintf(stderr, L"target process selection is not unique: %d\n", matches);
        return 4;
    }
    if (module_loaded(pid, dll)) {


        wchar_t unique[MAX_PATH * 16];
        if (!unique_module_copy(dll, unique, sizeof(unique) / sizeof(unique[0]))) {
            fwprintf(
                stderr,
                L"collector module is already loaded and cannot be copied\n"
            );
            return 12;
        }
        wcscpy(dll, unique);
    }
    HANDLE process = OpenProcess(
        PROCESS_CREATE_THREAD | PROCESS_QUERY_INFORMATION |
        PROCESS_VM_OPERATION | PROCESS_VM_WRITE | PROCESS_VM_READ,
        FALSE, pid
    );
    if (!process) return 5;
    SIZE_T bytes = ((SIZE_T)wcslen(dll) + 1) * sizeof(wchar_t);
    void *remote = VirtualAllocEx(
        process, NULL, bytes, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE
    );
    int borrowed = 0;
    if (!remote) {
        DWORD allocate_error = GetLastError();
        /* Some launchers hook remote allocation.  Fall back to a zero-filled
           private read/write region that already exists in the target: we only
           borrow slack that reads as zeros, and we restore it afterwards, so a
           protected client can still be instrumented without allocating. */
        SYSTEM_INFO system;
        GetSystemInfo(&system);
        uintptr_t cursor = (uintptr_t)system.lpMinimumApplicationAddress;
        uintptr_t limit = (uintptr_t)system.lpMaximumApplicationAddress;
        while (cursor < limit) {
            MEMORY_BASIC_INFORMATION region;
            if (!VirtualQueryEx(process, (const void *)cursor, &region,
                                sizeof(region))) break;
            uintptr_t base = (uintptr_t)region.BaseAddress;
            SIZE_T size = region.RegionSize;
            if (!size || base + size <= base) break;
            if (region.State == MEM_COMMIT && region.Type == MEM_PRIVATE &&
                region.Protect == PAGE_READWRITE && size >= bytes + 64u) {
                unsigned char probe[64];
                SIZE_T got = 0;
                if (ReadProcessMemory(process, (const void *)base, probe,
                                      sizeof(probe), &got) && got == sizeof(probe)) {
                    int zero = 1;
                    for (SIZE_T index = 0; index < sizeof(probe); index++)
                        if (probe[index]) { zero = 0; break; }
                    if (zero) { remote = (void *)base; borrowed = 1; break; }
                }
            }
            cursor = base + size;
        }
        if (!remote) {
            fwprintf(
                stderr,
                L"remote allocation failed (VirtualAllocEx=%lu, borrowed region unavailable)\n",
                (unsigned long)allocate_error
            );
        }
    }
    if (!remote) { CloseHandle(process); return 6; }
    SIZE_T written = 0;
    if (!WriteProcessMemory(process, remote, dll, bytes, &written) || written != bytes) {
        if (!borrowed) VirtualFreeEx(process, remote, 0, MEM_RELEASE);
        CloseHandle(process);
        return 7;
    }
    HMODULE kernel = GetModuleHandleW(L"kernel32.dll");
    FARPROC load_library = kernel ? GetProcAddress(kernel, "LoadLibraryW") : NULL;
    if (!load_library) {
        if (!borrowed) VirtualFreeEx(process, remote, 0, MEM_RELEASE);
        CloseHandle(process);
        return 8;
    }
    HANDLE thread = CreateRemoteThread(
        process, NULL, 0, (LPTHREAD_START_ROUTINE)(uintptr_t)load_library,
        remote, 0, NULL
    );
    if (!thread) {
        if (!borrowed) VirtualFreeEx(process, remote, 0, MEM_RELEASE);
        CloseHandle(process);
        return 9;
    }
    DWORD wait = WaitForSingleObject(thread, 30000);
    DWORD result = 0;
    if (wait == WAIT_OBJECT_0) GetExitCodeThread(thread, &result);
    CloseHandle(thread);
    if (borrowed) {
        unsigned char zeros[64] = {0};
        SIZE_T restored = 0;
        WriteProcessMemory(process, remote, zeros,
                           bytes < sizeof(zeros) ? bytes : sizeof(zeros),
                           &restored);
    } else {
        VirtualFreeEx(process, remote, 0, MEM_RELEASE);
    }
    CloseHandle(process);
    if (wait != WAIT_OBJECT_0 || !result) return 10;
    wprintf(L"injected pid=%lu%s\n", (unsigned long)pid,
            borrowed ? L" via borrowed region" : L"");
    return 0;
}
'''
    from alpha.c01 import current_runtime_process_binding

    binding = current_runtime_process_binding()
    if binding is None:
        return source
    pid, creation, path = binding


    expected_literal = _wide_literal(_windows_z_path(Path(path)))
    guard = f'''
    FILETIME session_created, session_exited, session_kernel, session_user;
    wchar_t session_path[32768]; DWORD session_path_size = 32768;
    WIN32_FILE_ATTRIBUTE_DATA session_expected_attributes, session_observed_attributes;
    const wchar_t *session_expected_name = wcsrchr({expected_literal}, L'\\\\');
    const wchar_t *session_observed_name = NULL;
    int session_same_file = 0;
    if (pid != {pid}u ||
        !GetProcessTimes(process, &session_created, &session_exited,
                         &session_kernel, &session_user) ||
        (((uint64_t)session_created.dwHighDateTime << 32) |
         session_created.dwLowDateTime) != {creation}ull ||
        !QueryFullProcessImageNameW(process, 0, session_path, &session_path_size) ||
        (_wcsicmp(session_path, {expected_literal}) != 0 &&
         !(session_observed_name = wcsrchr(session_path, L'\\\\'),
           session_same_file = session_expected_name && session_observed_name &&
             _wcsicmp(session_expected_name + 1, session_observed_name + 1) == 0 &&
             GetFileAttributesExW({expected_literal}, GetFileExInfoStandard,
                                  &session_expected_attributes) &&
             GetFileAttributesExW(session_path, GetFileExInfoStandard,
                                  &session_observed_attributes) &&
             session_expected_attributes.nFileSizeHigh == session_observed_attributes.nFileSizeHigh &&
             session_expected_attributes.nFileSizeLow == session_observed_attributes.nFileSizeLow,
           session_same_file))) {{
        CloseHandle(process);
        fwprintf(stderr, L"current metadata process instance changed\\n");
        return 11;
    }}
'''
    return source.replace("    if (!process) return 5;\n", "    if (!process) return 5;\n" + guard)


def _reachable_heap_limit_bytes(limit_mib: int) -> int:

    if type(limit_mib) is not int or not 0 <= limit_mib <= ((1 << 64) - 1) // (1024 * 1024):
        raise AcquisitionError("reachable heap budget is invalid")
    return limit_mib * 1024 * 1024


def runtime_snapshot_source(
    *,
    expected_executable_sha256: str,
    snapshot_path: Path,
    status_path: Path,
    owner_roots_path: Path | None = None,
    pointer_index_path: Path | None = None,
    type_resolver_state_slot_rva: int = 0,
    type_resolver_helper_rva: int = 0,
    required_owner_pairs: tuple[tuple[str, str], ...] = (),
    reachable_heap_limit_mib: int = 0,
) -> str:
    reachable_heap_limit_bytes = _reachable_heap_limit_bytes(reachable_heap_limit_mib)
    if len(expected_executable_sha256) != 64:
        raise AcquisitionError("runtime snapshot requires an exact executable SHA-256")
    snapshot_literal = _wide_literal(_windows_z_path(snapshot_path))
    status_literal = _wide_literal(_windows_z_path(status_path))
    if owner_roots_path is None:
        owner_roots_path = status_path.with_name("runtime-owner-roots.private.json")
    owner_roots_literal = _wide_literal(_windows_z_path(owner_roots_path))
    if pointer_index_path is None:
        pointer_index_path = snapshot_path.with_name(
            "runtime-pointer-index.private.bin"
        )
    pointer_literal = _wide_literal(_windows_z_path(pointer_index_path))
    if (
        type_resolver_state_slot_rva < 0
        or type_resolver_helper_rva < 0
        or bool(type_resolver_state_slot_rva) != bool(type_resolver_helper_rva)
    ):
        raise AcquisitionError("runtime snapshot resolver binding is invalid")
    owner_rows = ",\n".join(
        f'    {{"{namespace}", "{type_name}"}}'
        for namespace, type_name in required_owner_pairs
    ) or "    {NULL, NULL}"
    return rf'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <bcrypt.h>
#include <io.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>

 #define ALPHA_CHUNK (1024u * 1024u)
 #define ALPHA_REACHABLE_CHUNK (64u * 1024u)
 #define ALPHA_WINDOW_CACHE_SLOTS 65536u
#define ALPHA_POINTER_GROUP_BYTES (32u * 1024u * 1024u)
#define ALPHA_POINTER_TABLE_BITS (1u << 23)
#define ALPHA_POINTER_TABLE_BYTES (ALPHA_POINTER_TABLE_BITS / 8u)
#define ALPHA_POINTER_MINIMUM 0x10000ull
#define ALPHA_POINTER_MAXIMUM (1ull << 48)
#define ALPHA_CAPTURE_TIME_BUDGET_MS 0u
#define ALPHA_REACHABLE_TOTAL_BUDGET {reachable_heap_limit_bytes}ull
static const char expected_executable_sha256[] = "{expected_executable_sha256.lower()}";
static const wchar_t snapshot_output[] = {snapshot_literal};
static const wchar_t status_output[] = {status_literal};
static const wchar_t owner_roots_output[] = {owner_roots_literal};
static const wchar_t pointer_output[] = {pointer_literal};
static const uint64_t derived_type_resolver_state_slot_rva =
    {type_resolver_state_slot_rva}ull;
static const uint64_t derived_type_resolver_helper_rva =
    {type_resolver_helper_rva}ull;

typedef struct {{
    const char *namespace_name;
    const char *type_name;
}} alpha_snapshot_required_owner;

static const alpha_snapshot_required_owner required_owner_roots[] = {{
{owner_rows}
}};
static const uint32_t required_owner_root_count =
    {len(required_owner_pairs)}u;

#pragma pack(push, 1)
typedef struct {{
    char magic[8];
    uint32_t version;
    uint32_t header_bytes;
    uint64_t image_base;
    uint64_t image_bytes;
    uint64_t record_count;
    uint64_t captured_bytes;
    uint64_t region_count;
    uint64_t reserved[3];
}} alpha_snapshot_header;

typedef struct {{
    uint64_t address;
    uint64_t bytes;
    uint32_t protect;
    uint32_t memory_type;
    uint32_t state;
    uint32_t reserved;
}} alpha_snapshot_record;

typedef struct {{
    char magic[8];
    uint32_t version;
    uint32_t stride;
    uint32_t table_bits;
    uint32_t shape;
    uint64_t group_bytes;
    uint64_t minimum;
    uint64_t maximum;
    uint64_t record_count;
    uint64_t group_count;
    uint64_t snapshot_bytes;
    uint64_t reserved[3];
}} alpha_pointer_index_header;
#pragma pack(pop)

typedef struct {{
    uintptr_t base;
    SIZE_T bytes;
    uintptr_t window_base;
    uintptr_t captured_base;
    uintptr_t captured_end;
    DWORD protect;
    DWORD memory_type;
    DWORD state;
    uint32_t depth;
    uint32_t structural_depth;
    uint64_t support;
    int structural_root;
    int selected;
    int scanned;
}} alpha_reachable_region;

typedef struct {{
    alpha_reachable_region *candidates;
    uint32_t *candidate_hash;
    uint32_t *window_cache;
    uint32_t candidate_capacity;
    uint32_t hash_slots;
    uint32_t candidate_count;
    uint32_t selected_count;
    uint64_t selected_bytes;
    uint64_t captured_bytes;
    SIZE_T window_bytes;
    uint32_t root_data_region_count;
    uint32_t structural_type_cache_site_count;
    uint32_t structural_initialized_class_count;
    uint32_t structural_root_window_count;
    uint32_t resolver_owner_root_count;
    int resolver_owner_roots_complete;
    int owner_root_manifest_written;
    uint64_t root_pointer_count;
    uint64_t observed_pointer_count;
    uint64_t window_cache_hit_count;
    uint64_t virtual_query_count;
    ULONGLONG deadline_tick;
    int time_budget_exhausted;
    uint64_t large_region_rejection_count;
    uint32_t maximum_depth;
    int overflow;
    int selection_complete;
    /* A window is captured at the moment it is accepted into the reachable
       set, so the bytes written to the snapshot and the selected-byte
       accounting cannot drift apart while the heap keeps mutating. */
    HANDLE capture_sink;
    alpha_snapshot_header *capture_header;
    unsigned char *capture_buffer;
    /* Capture-time pointer index: one Bloom-style table per fixed run of
       payload bytes, indexed by the same 64-bit mix the Python reader
       reproduces.  A window is indexed either way (snapshot write failure
       already fails the capture), so the index can never contradict the
       bytes in the snapshot; the Python side still binds it by the snapshot
       digest before trusting it. */
    HANDLE pointer_sink;
    unsigned char *pointer_table;
    uint64_t pointer_group_bytes;
    uint64_t pointer_group_count;
    int pointer_failed;
    uint64_t captured_window_count;
    uint64_t capture_rejected_window_count;
    uint64_t capture_shortfall_window_count;
    uint64_t capture_shortfall_bytes;
    int capture_failed;
    uint32_t capture_failure_stage;
    uintptr_t capture_failure_address;
    DWORD capture_failure_protect;
    DWORD capture_failure_state;
    DWORD capture_failure_type;
    DWORD capture_failure_error;
}} alpha_reachable_graph;

static int write_all(HANDLE output, const void *data, DWORD bytes);
static int begin_reachable_capture(
    alpha_reachable_graph *graph,
    alpha_reachable_region *candidate,
    uintptr_t base,
    uintptr_t end,
    uintptr_t required
);
static int extend_reachable_capture(
    alpha_reachable_graph *graph,
    alpha_reachable_region *candidate,
    uintptr_t base,
    uintptr_t end,
    uintptr_t required
);
static void pointer_index_window(
    alpha_reachable_graph *graph, const unsigned char *data, SIZE_T bytes
);
static int pointer_index_flush(alpha_reachable_graph *graph);

static void digest_hex(const unsigned char digest[32], char output[65]) {{
    static const char alphabet[] = "0123456789abcdef";
    for (int index = 0; index < 32; index++) {{
        output[index * 2] = alphabet[digest[index] >> 4];
        output[index * 2 + 1] = alphabet[digest[index] & 15];
    }}
    output[64] = 0;
}}

static int hash_begin(
    BCRYPT_ALG_HANDLE *algorithm,
    BCRYPT_HASH_HANDLE *hash,
    unsigned char **object
) {{
    DWORD object_size = 0, received = 0;
    if (BCryptOpenAlgorithmProvider(
            algorithm, BCRYPT_SHA256_ALGORITHM, NULL, 0
        ) < 0) return 0;
    if (BCryptGetProperty(
            *algorithm, BCRYPT_OBJECT_LENGTH,
            (PUCHAR)&object_size, sizeof(object_size), &received, 0
        ) < 0 || !object_size) {{
        BCryptCloseAlgorithmProvider(*algorithm, 0);
        return 0;
    }}
    *object = (unsigned char *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, object_size
    );
    if (!*object || BCryptCreateHash(
            *algorithm, hash, *object, object_size, NULL, 0, 0
        ) < 0) {{
        if (*object) HeapFree(GetProcessHeap(), 0, *object);
        BCryptCloseAlgorithmProvider(*algorithm, 0);
        return 0;
    }}
    return 1;
}}

static void hash_end(
    BCRYPT_ALG_HANDLE algorithm,
    BCRYPT_HASH_HANDLE hash,
    unsigned char *object
) {{
    if (hash) BCryptDestroyHash(hash);
    if (object) HeapFree(GetProcessHeap(), 0, object);
    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);
}}

static int sha256_file(const wchar_t *path, char output[65]) {{
    HANDLE input = CreateFileW(
        path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (input == INVALID_HANDLE_VALUE) return 0;
    BCRYPT_ALG_HANDLE algorithm = NULL;
    BCRYPT_HASH_HANDLE hash = NULL;
    unsigned char *object = NULL;
    unsigned char *buffer = NULL;
    unsigned char digest[32];
    int ok = hash_begin(&algorithm, &hash, &object);
    if (ok) buffer = (unsigned char *)HeapAlloc(GetProcessHeap(), 0, ALPHA_CHUNK);
    if (!buffer) ok = 0;
    while (ok) {{
        DWORD received = 0;
        if (!ReadFile(input, buffer, ALPHA_CHUNK, &received, NULL)) {{
            ok = 0;
            break;
        }}
        if (!received) break;
        if (BCryptHashData(hash, buffer, received, 0) < 0) ok = 0;
    }}
    if (ok && BCryptFinishHash(hash, digest, sizeof(digest), 0) >= 0) {{
        digest_hex(digest, output);
    }} else {{
        ok = 0;
    }}
    if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
    hash_end(algorithm, hash, object);
    CloseHandle(input);
    return ok;
}}

static int readable_committed(DWORD protect) {{
    DWORD base = protect & 0xffu;
    if ((protect & PAGE_GUARD) || base == PAGE_NOACCESS || base == 0) return 0;
    return base == PAGE_READONLY || base == PAGE_READWRITE || base == PAGE_WRITECOPY ||
           base == PAGE_EXECUTE_READ || base == PAGE_EXECUTE_READWRITE ||
           base == PAGE_EXECUTE_WRITECOPY;
}}

static int private_data_protection(DWORD protect) {{
    DWORD base = protect & 0xffu;
    return readable_committed(protect) &&
        (base == PAGE_READONLY || base == PAGE_READWRITE ||
         base == PAGE_WRITECOPY);
}}

static int writable_data_protection(DWORD protect) {{
    DWORD base = protect & 0xffu;
    return readable_committed(protect) &&
        (base == PAGE_READWRITE || base == PAGE_WRITECOPY);
}}

static int overlaps_main_image(
    uintptr_t base,
    SIZE_T bytes,
    uint64_t image_base,
    uint64_t image_bytes
) {{
    uintptr_t end = base + bytes;
    uintptr_t image_end = (uintptr_t)image_base + (uintptr_t)image_bytes;
    if (end <= base || image_end <= (uintptr_t)image_base) return 1;
    return base < image_end && end > (uintptr_t)image_base;
}}

static uint64_t reachable_hash(uintptr_t base, SIZE_T bytes) {{
    uint64_t hash = ((uint64_t)base >> 4) ^
        ((uint64_t)bytes * 0x9e3779b97f4a7c15ull);
    hash ^= hash >> 33;
    hash *= 0xff51afd7ed558ccdull;
    return hash ^ (hash >> 33);
}}

static int grow_reachable_candidates(alpha_reachable_graph *graph) {{
    if (graph->candidate_count < graph->candidate_capacity) return 1;
    uint32_t capacity = graph->candidate_capacity
        ? graph->candidate_capacity * 2u : 1024u;
    if (capacity <= graph->candidate_capacity) return 0;
    SIZE_T bytes = (SIZE_T)capacity * sizeof(alpha_reachable_region);
    void *next = graph->candidates
        ? HeapReAlloc(GetProcessHeap(), 0, graph->candidates, bytes)
        : HeapAlloc(GetProcessHeap(), 0, bytes);
    if (!next) return 0;
    graph->candidates = (alpha_reachable_region *)next;
    graph->candidate_capacity = capacity;
    return 1;
}}

static int grow_reachable_hash(alpha_reachable_graph *graph) {{
    if (graph->hash_slots &&
        (uint64_t)(graph->candidate_count + 1u) * 2u < graph->hash_slots)
        return 1;
    uint32_t slots = graph->hash_slots ? graph->hash_slots * 2u : 2048u;
    if (slots <= graph->hash_slots) return 0;
    uint32_t *next = (uint32_t *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, (SIZE_T)slots * sizeof(uint32_t)
    );
    if (!next) return 0;
    for (uint32_t index = 0; index < graph->candidate_count; index++) {{
        const alpha_reachable_region *candidate = &graph->candidates[index];
        uint32_t slot = (uint32_t)reachable_hash(
            candidate->window_base, graph->window_bytes
        ) & (slots - 1u);
        while (next[slot]) slot = (slot + 1u) & (slots - 1u);
        next[slot] = index + 1u;
    }}
    if (graph->candidate_hash)
        HeapFree(GetProcessHeap(), 0, graph->candidate_hash);
    graph->candidate_hash = next;
    graph->hash_slots = slots;
    return 1;
}}

static void free_reachable_graph(alpha_reachable_graph *graph) {{
    if (!graph) return;
    if (graph->capture_buffer)
        HeapFree(GetProcessHeap(), 0, graph->capture_buffer);
    if (graph->window_cache)
        HeapFree(GetProcessHeap(), 0, graph->window_cache);
    if (graph->candidate_hash)
        HeapFree(GetProcessHeap(), 0, graph->candidate_hash);
    if (graph->candidates)
        HeapFree(GetProcessHeap(), 0, graph->candidates);
    HeapFree(GetProcessHeap(), 0, graph);
}}

static int capture_time_available(alpha_reachable_graph *graph) {{
    if (!graph || !graph->deadline_tick ||
        GetTickCount64() < graph->deadline_tick) return 1;
    graph->time_budget_exhausted = 1;
    return 0;
}}

static uint32_t window_cache_slot(uintptr_t base) {{
    return (uint32_t)(((base >> 12) ^ (base >> 28)) &
        (ALPHA_WINDOW_CACHE_SLOTS - 1u));
}}

static int credit_reachable_candidate(
    alpha_reachable_graph *graph,
    alpha_reachable_region *candidate,
    uint32_t depth,
    int structural_path
) {{
    if (candidate->support == UINT64_MAX ||
        graph->observed_pointer_count == UINT64_MAX ||
        (depth == 1 && graph->root_pointer_count == UINT64_MAX)) {{
        graph->overflow = 1;
        return 0;
    }}
    graph->observed_pointer_count++;
    if (depth == 1) graph->root_pointer_count++;
    candidate->support++;
    if (depth < candidate->depth) candidate->depth = depth;
    if (structural_path && (!candidate->structural_depth ||
        depth < candidate->structural_depth))
        candidate->structural_depth = depth;
    if (structural_path && depth == 1 &&
        !candidate->structural_root) {{
        candidate->structural_root = 1;
        graph->structural_root_window_count++;
    }}
    return 1;
}}

static int observe_reachable_pointer(
    alpha_reachable_graph *graph,
    uintptr_t value,
    uint32_t depth,
    uint64_t image_base,
    uint64_t image_bytes,
    int structural_path
) {{
    MEMORY_BASIC_INFORMATION region;
    if (!graph || !value || (value & (sizeof(uintptr_t) - 1u)) ||
        depth < 1 || !graph->window_bytes) return 1;
    /* The image is captured separately; its addresses are never heap roots. */
    if ((uint64_t)value >= image_base &&
        (uint64_t)value - image_base < image_bytes) return 1;
    uintptr_t window_base = value &
        ~((uintptr_t)graph->window_bytes - 1u);
    uint32_t cache_slot = window_cache_slot(window_base);
    if (graph->window_cache) {{
        uint32_t encoded = graph->window_cache[cache_slot];
        if (encoded && encoded <= graph->candidate_count) {{
            alpha_reachable_region *cached =
                &graph->candidates[encoded - 1u];
            if (value >= cached->base &&
                value - cached->base < cached->bytes &&
                cached->window_base == window_base) {{
                graph->window_cache_hit_count++;
                return credit_reachable_candidate(
                    graph, cached, depth, structural_path
                );
            }}
        }}
    }}
    graph->virtual_query_count++;
    if (!VirtualQuery((const void *)value, &region, sizeof(region)) ||
        region.State != MEM_COMMIT || region.Type != MEM_PRIVATE ||
        !private_data_protection(region.Protect)) return 1;
    uintptr_t region_base = (uintptr_t)region.BaseAddress;
    SIZE_T region_bytes = region.RegionSize;
    if (!graph->window_bytes || !region_base || !region_bytes ||
        region_base + region_bytes <= region_base || value < region_base ||
        value >= region_base + region_bytes) return 1;
    uintptr_t window_end = window_base + graph->window_bytes;
    uintptr_t region_end = region_base + region_bytes;
    if (window_end <= window_base) return 1;
    uintptr_t base = window_base > region_base
        ? window_base : region_base;
    uintptr_t end = window_end < region_end
        ? window_end : region_end;
    if (end <= base) return 1;
    SIZE_T bytes = end - base;
    if (!base || base + bytes <= base || overlaps_main_image(
            base, bytes, image_base, image_bytes
        )) return 1;
    if (!grow_reachable_hash(graph)) {{
        graph->overflow = 1;
        return 0;
    }}
    uint32_t slot = (uint32_t)reachable_hash(
        window_base, graph->window_bytes
    ) &
        (graph->hash_slots - 1u);
    for (uint32_t probe = 0;
         probe < graph->hash_slots;
         probe++) {{
        uint32_t encoded = graph->candidate_hash[slot];
        if (!encoded) {{
            if (!grow_reachable_candidates(graph)) {{
                graph->overflow = 1;
                return 0;
            }}
            uint32_t index = graph->candidate_count++;
            alpha_reachable_region *candidate = &graph->candidates[index];
            memset(candidate, 0, sizeof(*candidate));
            candidate->window_base = window_base;
            candidate->base = base;
            candidate->bytes = bytes;
            candidate->protect = region.Protect;
            candidate->memory_type = region.Type;
            candidate->state = region.State;
            candidate->depth = depth;
            if (!credit_reachable_candidate(
                    graph, candidate, depth, structural_path
                )) return 0;
            graph->candidate_hash[slot] = index + 1u;
            if (graph->window_cache)
                graph->window_cache[cache_slot] = index + 1u;
            /* The window is validated as private committed data right here;
               reading it now keeps the snapshot bytes and the selection
               accounting atomic, so a live heap can never turn a complete
               traversal into a partial snapshot after the fact. */
            return begin_reachable_capture(
                graph, candidate, base, end, value
            );
        }}
        alpha_reachable_region *candidate =
            &graph->candidates[encoded - 1u];
        if (candidate->window_base == window_base) {{
            if (graph->window_cache)
                graph->window_cache[cache_slot] = encoded;
            if (!credit_reachable_candidate(
                    graph, candidate, depth, structural_path
                )) return 0;
            return extend_reachable_capture(
                graph, candidate, base, end, value
            );
        }}
        slot = (slot + 1u) & (graph->hash_slots - 1u);
    }}
    graph->overflow = 1;
    return 0;
}}

static int scan_reachable_pointers(
    alpha_reachable_graph *graph,
    uintptr_t address,
    SIZE_T bytes,
    uint32_t target_depth,
    uint64_t image_base,
    uint64_t image_bytes,
    unsigned char *buffer,
    int structural_path
) {{
    if (!graph || !address || !bytes || !buffer ||
        target_depth < 1)
        return 0;
    uintptr_t end = address + bytes;
    if (end <= address) return 0;
    for (uintptr_t position = address; position < end;) {{
        if (!capture_time_available(graph)) return 0;
        SIZE_T amount = end - position > ALPHA_REACHABLE_CHUNK
            ? ALPHA_REACHABLE_CHUNK : (SIZE_T)(end - position);
        SIZE_T received = 0;
        if (!ReadProcessMemory(
                GetCurrentProcess(), (const void *)position,
                buffer, amount, &received
            ) || received != amount) return 0;
        SIZE_T aligned = (SIZE_T)((sizeof(uintptr_t) -
            (position & (sizeof(uintptr_t) - 1u))) &
            (sizeof(uintptr_t) - 1u));
        for (SIZE_T offset = aligned;
             offset + sizeof(uintptr_t) <= amount;
             offset += sizeof(uintptr_t)) {{
            if (!(offset & 0x7fffu) &&
                !capture_time_available(graph)) return 0;
            uintptr_t value = 0;
            memcpy(&value, buffer + offset, sizeof(value));
            if (!observe_reachable_pointer(
                    graph, value, target_depth, image_base, image_bytes,
                    structural_path
                )) return 0;
        }}
        if (position + amount <= position) return 0;
        position += amount;
    }}
    return 1;
}}

static int scan_reachable_window(
    alpha_reachable_graph *graph,
    uintptr_t address,
    SIZE_T bytes,
    uint32_t target_depth,
    uint64_t image_base,
    uint64_t image_bytes,
    unsigned char *buffer
) {{
    if (!graph || !address || !bytes || address + bytes <= address)
        return 0;
    uintptr_t cursor = address;
    uintptr_t maximum = address + bytes;
    while (cursor < maximum) {{
        MEMORY_BASIC_INFORMATION region;
        if (!VirtualQuery((const void *)cursor, &region, sizeof(region)))
            return 0;
        uintptr_t region_base = (uintptr_t)region.BaseAddress;
        uintptr_t region_end = region_base + region.RegionSize;
        if (region_end <= region_base) return 0;
        uintptr_t base = region_base < cursor ? cursor : region_base;
        uintptr_t end = region_end > maximum ? maximum : region_end;
        if (region.State == MEM_COMMIT && region.Type == MEM_PRIVATE &&
            private_data_protection(region.Protect) && end > base &&
            !scan_reachable_pointers(
                graph, base, end - base, target_depth,
                image_base, image_bytes, buffer, 1
            )) return 0;
        cursor = region_end;
    }}
    return 1;
}}

/* Capture a candidate window in the same step that accepts it.  The window
   was validated when it was observed; re-validating and reading it here keeps
   the snapshot bytes and the selection accounting identical by construction,
   so a live heap that mutates after the traversal can no longer turn a
   complete selection into a partial snapshot behind our back. */
/* Read one half-open address range straight into the snapshot.  The range is
   re-validated against the live region map while it is read, and any gap or
   failed read fails closed: the caller must never publish a snapshot that is
   missing bytes it had already accepted. */
static int capture_reachable_range(
    alpha_reachable_graph *graph,
    uintptr_t base,
    uintptr_t end,
    uintptr_t required,
    uint64_t *captured_bytes_out
) {{
    if (!graph || !graph->capture_sink ||
        graph->capture_sink == INVALID_HANDLE_VALUE ||
        !graph->capture_header || !graph->capture_buffer ||
        !captured_bytes_out) return 0;
    if (!base || end <= base) return 0;
    *captured_bytes_out = 0;
    int required_captured = 0;
    uintptr_t cursor = base;
    while (cursor < end) {{
        MEMORY_BASIC_INFORMATION current;
        if (!VirtualQuery((const void *)cursor, &current, sizeof(current))) {{
            graph->capture_failure_stage = 1;
            graph->capture_failure_address = cursor;
            graph->capture_failure_error = GetLastError();
            return 0;
        }}
        uintptr_t region_base = (uintptr_t)current.BaseAddress;
        uintptr_t region_end = region_base + current.RegionSize;
        if (region_end <= region_base) {{
            graph->capture_failure_stage = 2;
            graph->capture_failure_address = cursor;
            graph->capture_failure_protect = current.Protect;
            graph->capture_failure_state = current.State;
            graph->capture_failure_type = current.Type;
            return 0;
        }}
        uintptr_t current_base = region_base < cursor ? cursor : region_base;
        uintptr_t current_end = region_end > end ? end : region_end;
        if (current_end <= current_base) {{
            graph->capture_failure_stage = 3;
            graph->capture_failure_address = cursor;
            graph->capture_failure_protect = current.Protect;
            graph->capture_failure_state = current.State;
            graph->capture_failure_type = current.Type;
            return 0;
        }}
        if (current.State != MEM_COMMIT || current.Type != MEM_PRIVATE ||
            !private_data_protection(current.Protect)) {{
            /* The heap released this part of the window after the pointer
               that reached it was observed.  Skip the gap and keep going:
               the snapshot keeps exactly the bytes that are still there, and
               the observed pointer is checked separately below. */
            graph->capture_shortfall_bytes +=
                (uint64_t)(current_end - current_base);
            cursor = region_end;
            continue;
        }}
        graph->capture_header->region_count++;
        for (uintptr_t position = current_base; position < current_end;) {{
            SIZE_T amount = current_end - position > ALPHA_REACHABLE_CHUNK
                ? ALPHA_REACHABLE_CHUNK : (SIZE_T)(current_end - position);
            SIZE_T received = 0;
            if (!ReadProcessMemory(
                    GetCurrentProcess(), (const void *)position,
                    graph->capture_buffer, amount, &received
                ) || received != amount) {{
                graph->capture_shortfall_bytes +=
                    (uint64_t)(current_end - position);
                if (required >= position && required < current_end) {{
                    graph->capture_failure_stage = 5;
                    graph->capture_failure_address = position;
                    graph->capture_failure_protect = current.Protect;
                    graph->capture_failure_state = current.State;
                    graph->capture_failure_type = current.Type;
                    graph->capture_failure_error = GetLastError();
                    return 0;
                }}
                break;
            }}
            alpha_snapshot_record record;
            record.address = (uint64_t)position;
            record.bytes = (uint64_t)received;
            record.protect = current.Protect;
            record.memory_type = current.Type;
            record.state = current.State;
            record.reserved = 0;
            /* The group boundary rule is lazy by contract: the running filter
               flushes only once the *previous* windows already cover the
               group, so the current window belongs to the current table even
               when the boundary fell inside it.  The reader tests both
               adjacent groups for such records, so the rule is exact. */
            if (graph->pointer_group_bytes >= ALPHA_POINTER_GROUP_BYTES) {{
                graph->pointer_group_bytes = 0;
                if (!pointer_index_flush(graph)) {{
                    graph->capture_failure_stage = 7;
                    graph->capture_failure_address = position;
                    return 0;
                }}
            }}
            pointer_index_window(graph, graph->capture_buffer, received);
            graph->pointer_group_bytes += received;
            if (!write_all(graph->capture_sink, &record, sizeof(record)) ||
                !write_all(graph->capture_sink, graph->capture_buffer,
                    (DWORD)received)) {{
                graph->capture_failure_stage = 6;
                graph->capture_failure_address = position;
                return 0;
            }}
            graph->capture_header->record_count++;
            graph->capture_header->captured_bytes += received;
            graph->captured_bytes += received;
            *captured_bytes_out += received;
            if (required >= position && required < position + amount)
                required_captured = 1;
            if (position + amount <= position) return 0;
            position += amount;
        }}
        cursor = region_end;
    }}
    if (required >= base && required < end && !required_captured) {{
        graph->capture_failure_stage = 4;
        graph->capture_failure_address = required;
        return 0;
    }}
    return 1;
}}

/* A window is captured the moment it is first accepted, and later
   observations of the same window only append the bytes that are not in the
   snapshot yet.  Records therefore never overlap and the captured bytes stay
   equal to the selected bytes even while the heap keeps changing. */
static int begin_reachable_capture(
    alpha_reachable_graph *graph,
    alpha_reachable_region *candidate,
    uintptr_t base,
    uintptr_t end,
    uintptr_t required
) {{
    if (!graph || !candidate || end <= base) return 0;
    uint64_t captured = 0;
    if (!capture_reachable_range(graph, base, end, required, &captured) ||
        !captured) {{
        graph->capture_rejected_window_count++;
        graph->capture_failed = 1;
        return 0;
    }}
    if (captured < (uint64_t)(end - base))
        graph->capture_shortfall_window_count++;
    candidate->captured_base = base;
    candidate->captured_end = end;
    candidate->base = base;
    candidate->bytes = (SIZE_T)captured;
    graph->captured_window_count++;
    return 1;
}}

static int extend_reachable_capture(
    alpha_reachable_graph *graph,
    alpha_reachable_region *candidate,
    uintptr_t base,
    uintptr_t end,
    uintptr_t required
) {{
    if (!graph || !candidate) return 0;
    uint64_t captured = 0;
    if (base < candidate->captured_base) {{
        if (!capture_reachable_range(
                graph, base, candidate->captured_base, required, &captured
            )) {{
            graph->capture_rejected_window_count++;
            graph->capture_failed = 1;
            return 0;
        }}
        if (captured < (uint64_t)(candidate->captured_base - base))
            graph->capture_shortfall_window_count++;
        candidate->bytes += (SIZE_T)captured;
        if (candidate->selected) graph->selected_bytes += captured;
        candidate->captured_base = base;
    }}
    if (end > candidate->captured_end) {{
        captured = 0;
        if (!capture_reachable_range(
                graph, candidate->captured_end, end, required, &captured
            )) {{
            graph->capture_rejected_window_count++;
            graph->capture_failed = 1;
            return 0;
        }}
        if (captured < (uint64_t)(end - candidate->captured_end))
            graph->capture_shortfall_window_count++;
        candidate->bytes += (SIZE_T)captured;
        if (candidate->selected) graph->selected_bytes += captured;
        candidate->captured_end = end;
    }}
    return 1;
}}

static int select_reachable_depth(
    alpha_reachable_graph *graph,
    uint32_t depth
) {{
    if (!graph || depth < 1) return 0;
    for (uint32_t index = 0; index < graph->candidate_count; index++) {{
        alpha_reachable_region *candidate = &graph->candidates[index];
        if (candidate->selected || candidate->depth != depth) continue;
        if (graph->selected_count == UINT32_MAX ||
            graph->selected_bytes > UINT64_MAX - (uint64_t)candidate->bytes ||
            (ALPHA_REACHABLE_TOTAL_BUDGET &&
             ((uint64_t)candidate->bytes > ALPHA_REACHABLE_TOTAL_BUDGET ||
              graph->selected_bytes > ALPHA_REACHABLE_TOTAL_BUDGET -
                  (uint64_t)candidate->bytes))) {{
            graph->overflow = 1;
            return 0;
        }}
        candidate->selected = 1;
        graph->selected_count++;
        graph->selected_bytes += (uint64_t)candidate->bytes;
    }}
    return 1;
}}

static uint64_t snapshot_section_extent(
    const IMAGE_SECTION_HEADER *section
) {{
    uint64_t virtual_bytes = section->Misc.VirtualSize;
    uint64_t raw_bytes = section->SizeOfRawData;
    return virtual_bytes > raw_bytes ? virtual_bytes : raw_bytes;
}}

static int snapshot_image_string(
    const unsigned char *image,
    uint64_t image_bytes,
    uintptr_t address,
    int allow_empty
) {{
    uintptr_t base = (uintptr_t)image;
    if (!image || !image_bytes || address < base ||
        address - base >= image_bytes) return 0;
    uint64_t offset = address - base;
    for (uint32_t index = 0; index < 256u && offset + index < image_bytes;
         index++) {{
        unsigned char value = image[offset + index];
        if (!value) return allow_empty || index > 0;
        if (value < 0x20 || value > 0x7e) return 0;
    }}
    return 0;
}}

static int scan_structural_type_cache_roots(
    alpha_reachable_graph *graph,
    uint64_t image_base,
    uint64_t image_bytes
) {{
    unsigned char *image = (unsigned char *)(uintptr_t)image_base;
    if (!graph || !image || image_bytes < sizeof(IMAGE_DOS_HEADER)) return 0;
    IMAGE_DOS_HEADER *dos = (IMAGE_DOS_HEADER *)image;
    if (dos->e_magic != IMAGE_DOS_SIGNATURE || dos->e_lfanew <= 0 ||
        (uint64_t)dos->e_lfanew + sizeof(IMAGE_NT_HEADERS64) > image_bytes)
        return 0;
    IMAGE_NT_HEADERS64 *nt =
        (IMAGE_NT_HEADERS64 *)(image + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE ||
        nt->OptionalHeader.Magic != IMAGE_NT_OPTIONAL_HDR64_MAGIC)
        return 0;
    IMAGE_SECTION_HEADER *sections = IMAGE_FIRST_SECTION(nt);
    WORD section_count = nt->FileHeader.NumberOfSections;
    for (WORD section_index = 0;
         section_index < section_count;
         section_index++) {{
        IMAGE_SECTION_HEADER *section = &sections[section_index];
        if (!(section->Characteristics & IMAGE_SCN_MEM_EXECUTE)) continue;
        uint64_t section_rva = section->VirtualAddress;
        uint64_t extent = snapshot_section_extent(section);
        if (!extent || section_rva + extent > image_bytes) continue;
        unsigned char *bytes = image + section_rva;
        for (uint64_t offset = 0; offset + 58u <= extent; offset++) {{
            unsigned char *site = bytes + offset;
            if (memcmp(site, "\x48\x8b\x0d", 3) ||
                memcmp(site + 7, "\x48\x8d\x15", 3) ||
                memcmp(site + 14, "\x4c\x8d\x05", 3)) continue;
            int32_t namespace_reference = 0, type_reference = 0;
            memcpy(&namespace_reference, site + 10, 4);
            memcpy(&type_reference, site + 17, 4);
            uintptr_t namespace_value =
                (uintptr_t)(site + 14) + (intptr_t)namespace_reference;
            uintptr_t type_value =
                (uintptr_t)(site + 21) + (intptr_t)type_reference;
            if (!snapshot_image_string(
                    image, image_bytes, namespace_value, 1
                ) || !snapshot_image_string(
                    image, image_bytes, type_value, 0
                )) continue;
            unsigned char *call = NULL;
            for (uint64_t delta = 21; delta <= 37 &&
                 offset + delta + 12 <= extent; delta++) {{
                unsigned char *candidate = site + delta;
                if (candidate[0] == 0xe8 && candidate[5] == 0x48 &&
                    candidate[6] == 0x89 &&
                    (candidate[7] & 0xc7u) == 0x05) {{
                    call = candidate;
                    break;
                }}
            }}
            if (!call) continue;
            int32_t result_reference = 0;
            memcpy(&result_reference, call + 8, 4);
            uintptr_t result_slot =
                (uintptr_t)(call + 12) + (intptr_t)result_reference;
            if (result_slot < image_base ||
                result_slot - image_base + sizeof(uintptr_t) > image_bytes)
                continue;
            MEMORY_BASIC_INFORMATION result_region;
            if (!VirtualQuery(
                    (const void *)result_slot,
                    &result_region,
                    sizeof(result_region)
                ) || result_region.State != MEM_COMMIT ||
                !writable_data_protection(result_region.Protect)) continue;
            graph->structural_type_cache_site_count++;
            uintptr_t class_pointer = 0;
            memcpy(
                &class_pointer,
                (const void *)result_slot,
                sizeof(class_pointer)
            );
            if (!class_pointer) continue;
            graph->structural_initialized_class_count++;
            if (!observe_reachable_pointer(
                    graph, class_pointer, 1,
                    image_base, image_bytes, 1
                )) return 0;
        }}
    }}
    return graph->structural_type_cache_site_count > 0 &&
        graph->structural_initialized_class_count > 0 &&
        graph->structural_root_window_count > 0;
}}

typedef uintptr_t (*alpha_snapshot_type_resolver)(
    uintptr_t state,
    const char *namespace_name,
    const char *type_name
);

static int executable_runtime_pointer(uintptr_t value) {{
    MEMORY_BASIC_INFORMATION region;
    if (!value || !VirtualQuery(
            (const void *)value, &region, sizeof(region)
        ) || region.State != MEM_COMMIT) return 0;
    DWORD protect = region.Protect & 0xffu;
    return protect == PAGE_EXECUTE || protect == PAGE_EXECUTE_READ ||
        protect == PAGE_EXECUTE_READWRITE ||
        protect == PAGE_EXECUTE_WRITECOPY;
}}

static int resolve_structural_owner_roots(
    alpha_reachable_graph *graph,
    uint64_t image_base,
    uint64_t image_bytes
) {{
    if (!graph || !image_base || !image_bytes) return 0;
    if (!required_owner_root_count) return 1;
    if (!derived_type_resolver_state_slot_rva ||
        !derived_type_resolver_helper_rva ||
        derived_type_resolver_state_slot_rva + sizeof(uintptr_t) >
            image_bytes ||
        derived_type_resolver_helper_rva >= image_bytes) return 0;
    uintptr_t state_slot = (uintptr_t)image_base +
        (uintptr_t)derived_type_resolver_state_slot_rva;
    uintptr_t helper = (uintptr_t)image_base +
        (uintptr_t)derived_type_resolver_helper_rva;
    MEMORY_BASIC_INFORMATION state_region;
    uintptr_t state = 0;
    if (!VirtualQuery(
            (const void *)state_slot,
            &state_region,
            sizeof(state_region)
        ) || state_region.State != MEM_COMMIT ||
        !writable_data_protection(state_region.Protect) ||
        !executable_runtime_pointer(helper)) return 0;
    memcpy(&state, (const void *)state_slot, sizeof(state));
    if (!state) return 0;
    uintptr_t *roots = (uintptr_t *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY,
        required_owner_root_count * sizeof(*roots)
    );
    if (!roots) return 0;
    alpha_snapshot_type_resolver resolve =
        (alpha_snapshot_type_resolver)helper;
    int ok = 1;
    for (uint32_t index = 0; index < required_owner_root_count; index++) {{
        roots[index] = resolve(
            state,
            required_owner_roots[index].namespace_name,
            required_owner_roots[index].type_name
        );
        MEMORY_BASIC_INFORMATION root_region;
        if (!roots[index] || !VirtualQuery(
                (const void *)roots[index],
                &root_region,
                sizeof(root_region)
            ) || root_region.State != MEM_COMMIT ||
            root_region.Type != MEM_PRIVATE ||
            !private_data_protection(root_region.Protect) ||
            !observe_reachable_pointer(
                graph, roots[index], 1, image_base, image_bytes, 1
            )) {{
            ok = 0;
            break;
        }}
        graph->resolver_owner_root_count++;
    }}
    FILE *output = NULL;
    if (ok) output = _wfopen(owner_roots_output, L"wb");
    if (!output) ok = 0;
    if (ok && fprintf(
            output,
            "{{\n"
            "  \"schema\": \"alpha.runtime-owner-roots/v1\",\n"
            "  \"executable_sha256\": \"%s\",\n"
            "  \"image_base\": %llu,\n"
            "  \"image_bytes\": %llu,\n"
            "  \"state_slot_rva\": %llu,\n"
            "  \"resolver_helper_rva\": %llu,\n"
            "  \"owner_count\": %u,\n"
            "  \"owners\": [\n",
            expected_executable_sha256,
            (unsigned long long)image_base,
            (unsigned long long)image_bytes,
            (unsigned long long)derived_type_resolver_state_slot_rva,
            (unsigned long long)derived_type_resolver_helper_rva,
            required_owner_root_count
        ) < 0) ok = 0;
    for (uint32_t index = 0; ok && index < required_owner_root_count;
         index++) {{
        if (fprintf(
                output,
                "    {{\"namespace\": \"%s\", "
                "\"type_name\": \"%s\", "
                "\"class_pointer\": %llu}}%s\n",
                required_owner_roots[index].namespace_name,
                required_owner_roots[index].type_name,
                (unsigned long long)roots[index],
                index + 1u == required_owner_root_count ? "" : ","
            ) < 0) ok = 0;
    }}
    if (ok && fprintf(output, "  ]\n}}\n") < 0) ok = 0;
    if (output) {{
        if (ok && fflush(output)) ok = 0;
        fclose(output);
    }}
    if (ok && _wchmod(owner_roots_output, 0600)) ok = 0;
    if (!ok) DeleteFileW(owner_roots_output);
    HeapFree(GetProcessHeap(), 0, roots);
    if (!ok || graph->resolver_owner_root_count !=
            required_owner_root_count) return 0;
    graph->resolver_owner_roots_complete = 1;
    graph->owner_root_manifest_written = 1;
    return 1;
}}

static int scan_image_data_roots(
    alpha_reachable_graph *graph,
    uint64_t image_base,
    uint64_t image_bytes,
    unsigned char *buffer
) {{
    if (!graph || !image_base || !image_bytes || !buffer ||
        image_base + image_bytes <= image_base) return 0;
    uintptr_t cursor = (uintptr_t)image_base;
    uintptr_t maximum = cursor + (uintptr_t)image_bytes;
    while (cursor < maximum) {{
        MEMORY_BASIC_INFORMATION region;
        if (!VirtualQuery((const void *)cursor, &region, sizeof(region)))
            return 0;
        uintptr_t region_base = (uintptr_t)region.BaseAddress;
        uintptr_t region_end = region_base + region.RegionSize;
        if (region_end <= region_base) return 0;
        uintptr_t base = region_base < cursor ? cursor : region_base;
        uintptr_t end = region_end > maximum ? maximum : region_end;
        if (region.State == MEM_COMMIT &&
            writable_data_protection(region.Protect) && end > base) {{
            graph->root_data_region_count++;
            if (!scan_reachable_pointers(
                    graph, base, end - base, 1,
                    image_base, image_bytes, buffer, 0
                )) return 0;
        }}
        cursor = region_end;
    }}
    return graph->root_data_region_count > 0;
}}

static int build_reachable_graph(
    alpha_reachable_graph *graph,
    uint64_t image_base,
    uint64_t image_bytes,
    unsigned char *buffer
) {{
    SYSTEM_INFO system;
    GetSystemInfo(&system);
    if (!graph || !image_base || !image_bytes || !buffer ||
        image_base + image_bytes <= image_base ||
        system.dwAllocationGranularity < 4096u ||
        (system.dwAllocationGranularity &
            (system.dwAllocationGranularity - 1u)) ||
        (graph->window_bytes = system.dwAllocationGranularity) == 0 ||
        !(graph->window_cache = (uint32_t *)HeapAlloc(
            GetProcessHeap(), HEAP_ZERO_MEMORY,
            ALPHA_WINDOW_CACHE_SLOTS * sizeof(uint32_t)
        )) ||
        !graph->capture_sink ||
        graph->capture_sink == INVALID_HANDLE_VALUE ||
        !graph->capture_header ||
        !(graph->capture_buffer = (unsigned char *)HeapAlloc(
            GetProcessHeap(), 0, ALPHA_REACHABLE_CHUNK
        )) ||
        !resolve_structural_owner_roots(
            graph, image_base, image_bytes
        ) ||
        !scan_structural_type_cache_roots(
            graph, image_base, image_bytes
        ) ||
        !scan_image_data_roots(
            graph, image_base, image_bytes, buffer
        ) || !select_reachable_depth(graph, 1)) return 0;
    for (uint32_t depth = 1;; depth++) {{
        if (!capture_time_available(graph)) return 0;
        uint32_t scan_limit = graph->candidate_count;
        for (uint32_t index = 0; index < scan_limit; index++) {{
            alpha_reachable_region *candidate = &graph->candidates[index];
            if (!candidate->selected || candidate->scanned ||
                candidate->depth != depth) continue;
            candidate->scanned = 1;
            uintptr_t base = candidate->base;
            SIZE_T bytes = candidate->bytes;
            if (depth == UINT32_MAX) return 0;
            if (!scan_reachable_window(
                    graph, base, bytes, depth + 1,
                    image_base, image_bytes, buffer
                )) return 0;
        }}
        graph->maximum_depth = depth;
        if (depth == UINT32_MAX) return 0;
        uint32_t selected_before = graph->selected_count;
        if (!select_reachable_depth(graph, depth + 1)) return 0;
        if (graph->selected_count == selected_before) break;
    }}
    if (graph->overflow || !graph->root_pointer_count ||
        !graph->selected_count || !graph->selected_bytes ||
        graph->candidate_count != graph->selected_count) return 0;
    graph->selection_complete = 1;
    return 1;
}}

static int write_all(HANDLE output, const void *data, DWORD bytes) {{
    DWORD written = 0;
    return WriteFile(output, data, bytes, &written, NULL) && written == bytes;
}}

/* Index one captured window into the running pointer filter.  Only 8-byte
   aligned qwords inside the fixed value window are indexed, and every value
   sets both of its slots, so a query whose slots read back unset proves the
   group cannot hold that value; the table's fullness only decides how often
   the exact scan runs. */
static void pointer_index_window(
    alpha_reachable_graph *graph, const unsigned char *data, SIZE_T bytes
) {{
    SIZE_T position;
    if (!graph || !graph->pointer_table) return;
    for (position = 0; position + 8 <= bytes; position += 8) {{
        uint64_t value;
        uint64_t mixed;
        uint32_t first;
        uint32_t second;
        memcpy(&value, data + position, sizeof(value));
        if (value < ALPHA_POINTER_MINIMUM || value >= ALPHA_POINTER_MAXIMUM)
            continue;
        mixed = value * 0x9E3779B97F4A7C15ull;
        mixed ^= mixed >> 29;
        mixed *= 0xBF58476D1CE4E5B9ull;
        mixed ^= mixed >> 32;
        first = (uint32_t)(mixed & (ALPHA_POINTER_TABLE_BITS - 1u));
        second = (uint32_t)((mixed >> 24) & (ALPHA_POINTER_TABLE_BITS - 1u));
        graph->pointer_table[first >> 3] |= (unsigned char)(1u << (first & 7u));
        graph->pointer_table[second >> 3] |= (unsigned char)(1u << (second & 7u));
    }}
}}

static int pointer_index_flush(alpha_reachable_graph *graph) {{
    if (!graph->pointer_sink || graph->pointer_sink == INVALID_HANDLE_VALUE ||
        !graph->pointer_table) {{
        graph->pointer_failed = 1;
        return 0;
    }}
    if (!write_all(
            graph->pointer_sink, graph->pointer_table,
            ALPHA_POINTER_TABLE_BYTES
        )) {{
        graph->pointer_failed = 1;
        return 0;
    }}
    memset(graph->pointer_table, 0, ALPHA_POINTER_TABLE_BYTES);
    graph->pointer_group_count++;
    return 1;
}}

static int executable_identity(char output[65]) {{
    wchar_t executable[MAX_PATH * 8];
    DWORD length = GetModuleFileNameW(
        NULL, executable, (DWORD)(sizeof(executable) / sizeof(executable[0]))
    );
    return length && length < sizeof(executable) / sizeof(executable[0]) &&
           sha256_file(executable, output);
}}

static int main_image(uint64_t *base, uint64_t *bytes) {{
    HMODULE module = GetModuleHandleW(NULL);
    if (!module) return 0;
    const unsigned char *image = (const unsigned char *)module;
    if (image[0] != 'M' || image[1] != 'Z') return 0;
    uint32_t pe_offset = *(const uint32_t *)(image + 0x3c);
    if (pe_offset > 0x100000 || memcmp(image + pe_offset, "PE\0\0", 4)) return 0;
    const unsigned char *optional = image + pe_offset + 24;
    if (*(const uint16_t *)optional != 0x20b) return 0;
    uint32_t image_size = *(const uint32_t *)(optional + 56);
    if (!image_size) return 0;
    *base = (uint64_t)(uintptr_t)module;
    *bytes = image_size;
    return 1;
}}

static void write_status(
    const char *status,
    const char *observed_hash,
    const char *snapshot_hash,
    const alpha_snapshot_header *header,
    const alpha_reachable_graph *graph
) {{
    static const uint64_t support_thresholds[5] = {{8, 16, 32, 64, 128}};
    uint32_t support_region_counts[5] = {{0}};
    uint64_t support_region_bytes[5] = {{0}};
    if (graph) {{
        for (uint32_t index = 0; index < graph->candidate_count; index++) {{
            const alpha_reachable_region *candidate =
                &graph->candidates[index];
            if (candidate->depth != 1) continue;
            for (uint32_t bucket = 0; bucket < 5; bucket++) {{
                if (candidate->support < support_thresholds[bucket]) continue;
                support_region_counts[bucket]++;
                support_region_bytes[bucket] += candidate->bytes;
            }}
        }}
    }}
    FILE *output = _wfopen(status_output, L"wb");
    if (!output) return;
    fprintf(output,
        "{{\n"
        "  \"schema\": \"alpha.runtime-memory-capture/v5\",\n"
        "  \"status\": \"%s\",\n"
        "  \"process_id\": %lu,\n"
        "  \"expected_executable_sha256\": \"%s\",\n"
        "  \"observed_executable_sha256\": \"%s\",\n"
        "  \"executable_hash_matches\": %s,\n"
        "  \"snapshot_sha256\": \"%s\",\n"
        "  \"record_count\": %llu,\n"
        "  \"region_count\": %llu,\n"
        "  \"captured_bytes\": %llu,\n"
        "  \"readable_committed_regions\": %s,\n"
        "  \"main_image_only\": false,\n"
        "  \"executable_regions_included\": %s,\n"
        "  \"reachable_heap_included\": %s,\n"
        "  \"reachable_heap_selection_complete\": %s,\n"
        "  \"reachable_all_candidates_selected\": %s,\n"
        "  \"reachable_root_data_region_count\": %u,\n"
        "  \"reachable_structural_type_cache_site_count\": %u,\n"
        "  \"reachable_structural_initialized_class_count\": %u,\n"
        "  \"reachable_structural_root_window_count\": %u,\n"
        "  \"reachable_resolver_owner_root_count\": %u,\n"
        "  \"reachable_resolver_owner_roots_complete\": %s,\n"
        "  \"reachable_owner_root_manifest_written\": %s,\n"
        "  \"reachable_root_pointer_count\": %llu,\n"
        "  \"reachable_observed_pointer_count\": %llu,\n"
        "  \"reachable_window_cache_hit_count\": %llu,\n"
        "  \"reachable_virtual_query_count\": %llu,\n"
        "  \"reachable_candidate_region_count\": %u,\n"
        "  \"reachable_heap_region_count\": %u,\n"
        "  \"reachable_heap_bytes\": %llu,\n"
        "  \"reachable_heap_captured_bytes\": %llu,\n"
        "  \"reachable_captured_window_count\": %llu,\n"
        "  \"reachable_capture_rejected_window_count\": %llu,\n"
        "  \"reachable_capture_shortfall_window_count\": %llu,\n"
        "  \"reachable_capture_shortfall_bytes\": %llu,\n"
        "  \"reachable_capture_failed\": %s,\n"
        "  \"reachable_capture_failure_stage\": %u,\n"
        "  \"reachable_capture_failure_address\": %llu,\n"
        "  \"reachable_capture_failure_protect\": %lu,\n"
        "  \"reachable_capture_failure_state\": %lu,\n"
        "  \"reachable_capture_failure_type\": %lu,\n"
        "  \"reachable_capture_failure_error\": %lu,\n"
        "  \"reachable_depth\": %u,\n"
        "  \"reachable_depth2_minimum_region_support\": %llu,\n"
        "  \"reachable_minimum_region_support\": %llu,\n"
        "  \"reachable_region_size_limit\": %llu,\n"
        "  \"reachable_window_bytes\": %llu,\n"
        "  \"reachable_total_size_limit\": %llu,\n"
        "  \"capture_time_budget_ms\": %u,\n"
        "  \"time_budget_exhausted\": %s,\n"
        "  \"reachable_large_region_rejection_count\": %llu,\n"
        "  \"reachable_root_support_region_counts\": {{"
            "\"8\": %u, \"16\": %u, \"32\": %u, "
            "\"64\": %u, \"128\": %u}},\n"
        "  \"reachable_root_support_region_bytes\": {{"
            "\"8\": %llu, \"16\": %llu, \"32\": %llu, "
            "\"64\": %llu, \"128\": %llu}},\n"
        "  \"reachable_selection_overflow\": %s,\n"
        "  \"reachable_bounds_enforced\": %s,\n"
        "  \"fixed_address_used\": false,\n"
        "  \"fixed_heap_range_used\": false,\n"
        "  \"network_used\": false,\n"
        "  \"external_runtime_plugin_used\": false\n"
        "}}\n",
        status,
        (unsigned long)GetCurrentProcessId(),
        expected_executable_sha256,
        observed_hash ? observed_hash : "",
        observed_hash && !strcmp(observed_hash, expected_executable_sha256)
            ? "true" : "false",
        snapshot_hash ? snapshot_hash : "",
        (unsigned long long)(header ? header->record_count : 0),
        (unsigned long long)(header ? header->region_count : 0),
        (unsigned long long)(header ? header->captured_bytes : 0),
        !strcmp(status, "complete") ? "true" : "false",
        !strcmp(status, "complete") ? "true" : "false",
        graph && !strcmp(status, "complete") &&
            graph->captured_bytes == graph->selected_bytes ? "true" : "false",
        graph && graph->selection_complete ? "true" : "false",
        graph && graph->selection_complete &&
            graph->candidate_count == graph->selected_count ? "true" : "false",
        graph ? graph->root_data_region_count : 0,
        graph ? graph->structural_type_cache_site_count : 0,
        graph ? graph->structural_initialized_class_count : 0,
        graph ? graph->structural_root_window_count : 0,
        graph ? graph->resolver_owner_root_count : 0,
        graph && graph->resolver_owner_roots_complete ? "true" : "false",
        graph && graph->owner_root_manifest_written ? "true" : "false",
        (unsigned long long)(graph ? graph->root_pointer_count : 0),
        (unsigned long long)(graph ? graph->observed_pointer_count : 0),
        (unsigned long long)(graph ? graph->window_cache_hit_count : 0),
        (unsigned long long)(graph ? graph->virtual_query_count : 0),
        graph ? graph->candidate_count : 0,
        graph ? graph->selected_count : 0,
        (unsigned long long)(graph ? graph->selected_bytes : 0),
        (unsigned long long)(graph ? graph->captured_bytes : 0),
        (unsigned long long)(graph ? graph->captured_window_count : 0),
        (unsigned long long)(graph ? graph->capture_rejected_window_count : 0),
        (unsigned long long)(graph ? graph->capture_shortfall_window_count : 0),
        (unsigned long long)(graph ? graph->capture_shortfall_bytes : 0),
        graph && graph->capture_failed ? "true" : "false",
        graph ? graph->capture_failure_stage : 0,
        (unsigned long long)(graph ? graph->capture_failure_address : 0),
        (unsigned long)(graph ? graph->capture_failure_protect : 0),
        (unsigned long)(graph ? graph->capture_failure_state : 0),
        (unsigned long)(graph ? graph->capture_failure_type : 0),
        (unsigned long)(graph ? graph->capture_failure_error : 0),
        graph ? graph->maximum_depth : 0,
        0ull,
        0ull,
        0ull,
        (unsigned long long)(graph ? graph->window_bytes : 0),
        (unsigned long long)ALPHA_REACHABLE_TOTAL_BUDGET,
        ALPHA_CAPTURE_TIME_BUDGET_MS,
        graph && graph->time_budget_exhausted ? "true" : "false",
        (unsigned long long)(graph ? graph->large_region_rejection_count : 0),
        support_region_counts[0], support_region_counts[1],
        support_region_counts[2], support_region_counts[3],
        support_region_counts[4],
        (unsigned long long)support_region_bytes[0],
        (unsigned long long)support_region_bytes[1],
        (unsigned long long)support_region_bytes[2],
        (unsigned long long)support_region_bytes[3],
        (unsigned long long)support_region_bytes[4],
        graph && graph->overflow ? "true" : "false",
        ALPHA_REACHABLE_TOTAL_BUDGET ? "true" : "false"
    );
    fclose(output);
    _wchmod(status_output, 0600);
}}

static DWORD WINAPI worker(void *unused) {{
    (void)unused;
    char observed_hash[65] = {{0}};
    alpha_snapshot_header header;
    alpha_reachable_graph *graph = NULL;
    unsigned char *buffer = NULL;
    memset(&header, 0, sizeof(header));
    memcpy(header.magic, "ALPHAMS5", 8);
    header.version = 5;
    header.header_bytes = sizeof(header);
    if (!executable_identity(observed_hash) ||
        strcmp(observed_hash, expected_executable_sha256)) {{
        write_status(
            "executable-binding-rejected", observed_hash, NULL, &header, NULL
        );
        return 2;
    }}
    if (!main_image(&header.image_base, &header.image_bytes)) {{
        write_status("main-image-invalid", observed_hash, NULL, &header, NULL);
        return 3;
    }}
    graph = (alpha_reachable_graph *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, sizeof(*graph)
    );
    if (graph && ALPHA_CAPTURE_TIME_BUDGET_MS) graph->deadline_tick =
        GetTickCount64() + ALPHA_CAPTURE_TIME_BUDGET_MS;
    buffer = (unsigned char *)HeapAlloc(
        GetProcessHeap(), 0, ALPHA_CHUNK
    );
    if (!graph || !buffer) {{
        write_status(
            "reachable-heap-selection-failed", observed_hash, NULL,
            &header, graph
        );
        if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
        free_reachable_graph(graph);
        return 4;
    }}
    HANDLE output = CreateFileW(
        snapshot_output, GENERIC_READ | GENERIC_WRITE, 0, NULL, CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (output == INVALID_HANDLE_VALUE) {{
        write_status(
            "snapshot-open-failed", observed_hash, NULL, &header, graph
        );
        HeapFree(GetProcessHeap(), 0, buffer);
        free_reachable_graph(graph);
        return 5;
    }}
    graph->capture_sink = output;
    graph->capture_header = &header;
    int ok = write_all(output, &header, sizeof(header));
    HANDLE pointer_output_handle = CreateFileW(
        pointer_output, GENERIC_READ | GENERIC_WRITE, 0, NULL, CREATE_ALWAYS,
        FILE_ATTRIBUTE_NORMAL, NULL
    );
    alpha_pointer_index_header pointer_header;
    if (pointer_output_handle == INVALID_HANDLE_VALUE) {{
        write_status(
            "pointer-index-open-failed", observed_hash, NULL, &header, graph
        );
        CloseHandle(output);
        DeleteFileW(snapshot_output);
        if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
        free_reachable_graph(graph);
        return 5;
    }}
    memset(&pointer_header, 0, sizeof(pointer_header));
    memcpy(pointer_header.magic, "ALPHAPI2", 8);
    pointer_header.version = 2;
    pointer_header.stride = 8;
    pointer_header.table_bits = ALPHA_POINTER_TABLE_BITS;
    pointer_header.shape = 2;
    pointer_header.group_bytes = ALPHA_POINTER_GROUP_BYTES;
    pointer_header.minimum = ALPHA_POINTER_MINIMUM;
    pointer_header.maximum = ALPHA_POINTER_MAXIMUM;
    graph->pointer_sink = pointer_output_handle;
    graph->pointer_table = (unsigned char *)HeapAlloc(
        GetProcessHeap(), HEAP_ZERO_MEMORY, ALPHA_POINTER_TABLE_BYTES
    );
    if (!graph->pointer_table ||
        !write_all(pointer_output_handle, &pointer_header, sizeof(pointer_header))) {{
        graph->pointer_failed = 1;
        ok = 0;
    }}
    if (ok && !build_reachable_graph(
            graph, header.image_base, header.image_bytes, buffer
        )) {{
        write_status(
            graph->capture_failed ? "reachable-heap-capture-failed"
                                  : "reachable-heap-selection-failed",
            observed_hash, NULL, &header, graph
        );
        CloseHandle(output);
        DeleteFileW(snapshot_output);
        if (buffer) HeapFree(GetProcessHeap(), 0, buffer);
        free_reachable_graph(graph);
        return 4;
    }}
    SYSTEM_INFO system_info;
    GetSystemInfo(&system_info);
    uintptr_t cursor = (uintptr_t)header.image_base;
    uintptr_t maximum = cursor + (uintptr_t)header.image_bytes;
    if (maximum <= cursor ||
        maximum > (uintptr_t)system_info.lpMaximumApplicationAddress)
        ok = 0;
    while (ok && cursor < maximum) {{
        if (!capture_time_available(graph)) {{ ok = 0; break; }}
        MEMORY_BASIC_INFORMATION region;
        SIZE_T queried = VirtualQuery((const void *)cursor, &region, sizeof(region));
        if (!queried) {{ ok = 0; break; }}
        uintptr_t region_base = (uintptr_t)region.BaseAddress;
        uintptr_t region_end = region_base + (uintptr_t)region.RegionSize;
        if (region_end <= region_base) {{ ok = 0; break; }}
        uintptr_t base = region_base < cursor ? cursor : region_base;
        uintptr_t end = region_end > maximum ? maximum : region_end;
        DWORD image_protect = region.Protect & 0xffu;
        if (region.State == MEM_COMMIT &&
            !readable_committed(region.Protect) &&
            (image_protect == PAGE_EXECUTE ||
             image_protect == PAGE_EXECUTE_READ ||
             image_protect == PAGE_EXECUTE_READWRITE ||
             image_protect == PAGE_EXECUTE_WRITECOPY)) {{
            ok = 0;
            break;
        }}
        if (region.State == MEM_COMMIT && readable_committed(region.Protect)) {{
            header.region_count++;
            uintptr_t position = base;
            while (position < end) {{
                if (!capture_time_available(graph)) {{ ok = 0; break; }}
                SIZE_T amount = end - position > ALPHA_CHUNK
                    ? ALPHA_CHUNK : (SIZE_T)(end - position);
                SIZE_T received = 0;
                if (ReadProcessMemory(
                        GetCurrentProcess(), (const void *)position,
                        buffer, amount, &received
                    ) && received == amount) {{
                    alpha_snapshot_record record;
                    record.address = (uint64_t)position;
                    record.bytes = (uint64_t)received;
                    record.protect = region.Protect;
                    record.memory_type = region.Type;
                    record.state = region.State;
                    record.reserved = 0;
                    /* Same lazy group rule as the heap path (see above): the
                       flush happens before the window is indexed, so a
                       boundary-straddling window always belongs to the fresh
                       table whichever side the reader probes. */
                    if (graph->pointer_group_bytes >= ALPHA_POINTER_GROUP_BYTES) {{
                        graph->pointer_group_bytes = 0;
                        if (!pointer_index_flush(graph)) {{
                            ok = 0;
                            break;
                        }}
                    }}
                    pointer_index_window(graph, buffer, received);
                    graph->pointer_group_bytes += received;
                    if (!write_all(output, &record, sizeof(record)) ||
                        !write_all(output, buffer, (DWORD)received)) {{
                        ok = 0;
                        break;
                    }}
                    header.record_count++;
                    header.captured_bytes += received;
                }} else {{
                    ok = 0;
                    break;
                }}
                if (position + amount <= position) {{ ok = 0; break; }}
                position += amount;
            }}
        }}
        cursor = region_end;
    }}
    /* Every selected window was written while it was accepted, so the heap
       portion of the snapshot is complete by construction.  A mismatch here
       means the capture or the traversal broke, not that the heap moved. */
    if (graph->capture_failed ||
        graph->captured_window_count != graph->selected_count ||
        graph->captured_bytes != graph->selected_bytes) ok = 0;
    if (graph->pointer_failed) ok = 0;
    if (ok && graph->pointer_group_bytes && !pointer_index_flush(graph)) ok = 0;
    graph->pointer_group_bytes = 0;
    graph->capture_sink = INVALID_HANDLE_VALUE;
    graph->capture_header = NULL;
    graph->pointer_sink = INVALID_HANDLE_VALUE;
    if (graph->pointer_table) {{
        HeapFree(GetProcessHeap(), 0, graph->pointer_table);
        graph->pointer_table = NULL;
    }}
    /* The index is written before the snapshot's own header is finalised, so
       its header records the totals the capture already proved: every record
       the snapshot will contain, every group flushed, and the exact byte size
       of the envelope the header describes.  The Python side re-derives all
       of them from the sealed files (and binds the snapshot digest), so a
       disagreement is a miss and the reader falls back. */
    if (pointer_output_handle != INVALID_HANDLE_VALUE) {{
        if (ok) {{
            pointer_header.record_count = header.record_count;
            pointer_header.group_count = graph->pointer_group_count;
            pointer_header.snapshot_bytes =
                (uint64_t)sizeof(alpha_snapshot_header) +
                (uint64_t)header.record_count *
                    (uint64_t)sizeof(alpha_snapshot_record) +
                header.captured_bytes;
            LARGE_INTEGER zero;
            zero.QuadPart = 0;
            if (!SetFilePointerEx(pointer_output_handle, zero, NULL, FILE_BEGIN) ||
                !write_all(
                    pointer_output_handle, &pointer_header,
                    sizeof(pointer_header)
                )) ok = 0;
        }}
        if (!FlushFileBuffers(pointer_output_handle)) ok = 0;
        if (!CloseHandle(pointer_output_handle)) ok = 0;
        if (ok && _wchmod(pointer_output, 0600)) ok = 0;
        if (!ok) DeleteFileW(pointer_output);
    }}
    HeapFree(GetProcessHeap(), 0, buffer);
    buffer = NULL;
    LARGE_INTEGER beginning;
    beginning.QuadPart = 0;
    if (ok && (!SetFilePointerEx(output, beginning, NULL, FILE_BEGIN) ||
        !write_all(output, &header, sizeof(header)))) ok = 0;
    if (ok && !FlushFileBuffers(output)) ok = 0;
    if (!CloseHandle(output)) ok = 0;
    if (ok && _wchmod(snapshot_output, 0600)) ok = 0;
    if (!ok) {{
        DeleteFileW(snapshot_output);
        write_status(
            "snapshot-write-failed", observed_hash, NULL, &header, graph
        );
        free_reachable_graph(graph);
        return 6;
    }}
    char snapshot_hash[65] = {{0}};
    if (!sha256_file(snapshot_output, snapshot_hash)) {{
        DeleteFileW(snapshot_output);
        write_status(
            "snapshot-hash-failed", observed_hash, NULL, &header, graph
        );
        free_reachable_graph(graph);
        return 7;
    }}
    write_status("complete", observed_hash, snapshot_hash, &header, graph);
    free_reachable_graph(graph);
    return 0;
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


def _compiler(explicit: Path | None) -> Path:
    if explicit is not None:
        candidate = Path(str(explicit)).expanduser().resolve()
        if not candidate.is_file():
            raise DependencyUnavailable(f"Windows compiler is unavailable: {candidate}")
        return candidate
    names = (
        ("x86_64-w64-mingw32-gcc", "gcc", "clang", "clang.exe")
        if os.name == "nt"
        else ("x86_64-w64-mingw32-gcc", "clang")
    )
    for name in names:
        candidate = shutil.which(name)
        if candidate:
            return Path(candidate).expanduser().resolve()
    raise DependencyUnavailable(
        "a 64-bit Windows GCC-compatible compiler is required; install MinGW-w64 or pass --compiler"
    )


def verify_windows_toolchain(explicit: Path | None) -> Path:
    compiler = _compiler(explicit)
    source = (
        "#define WIN32_LEAN_AND_MEAN\n"
        "#include <windows.h>\n"
        "#include <bcrypt.h>\n"
        "typedef char alpha_requires_64_bit_windows[(sizeof(void *) == 8) ? 1 : -1];\n"
        "int wmain(void) {\n"
        "    BCRYPT_ALG_HANDLE algorithm = NULL;\n"
        "    NTSTATUS status = BCryptOpenAlgorithmProvider(\n"
        "        &algorithm, BCRYPT_SHA256_ALGORITHM, NULL, 0\n"
        "    );\n"
        "    if (algorithm) BCryptCloseAlgorithmProvider(algorithm, 0);\n"
        "    return status < 0;\n"
        "}\n"
    )
    with tempfile.TemporaryDirectory(prefix="alpha-windows-toolchain-") as root:
        directory = Path(root)
        source_path = directory / "probe.c"
        program_path = directory / "probe.exe"
        source_path.write_text(source, encoding="utf-8")
        _build(
            [
                str(compiler), "-std=c11", "-O2", "-municode", "-Wall",
                "-Wextra", "-Werror", str(source_path), "-o",
                str(program_path), "-lbcrypt",
            ],
            label="64-bit Windows compiler preflight",
        )
        if not program_path.is_file() or program_path.stat().st_size < 1024:
            raise DependencyUnavailable(
                "Windows compiler preflight did not produce a usable executable"
            )
        with program_path.open("rb") as artifact:
            if artifact.read(2) != b"MZ":
                raise DependencyUnavailable(
                    "Windows compiler preflight did not produce a PE executable"
                )
    return compiler


def _build(command: list[str], *, label: str) -> dict[str, Any]:
    try:
        result = subprocess.run(
            command,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=300,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError(f"{label} build could not run") from error
    if result.returncode:
        raise AcquisitionError(
            f"{label} build failed ({result.returncode}): {result.stderr[-4000:]}"
        )
    return {"returncode": result.returncode, "stdout": result.stdout, "stderr": result.stderr}


_WINBUILD_MEMO_DIR: Path | None = None
_WINBUILD_MEMO_KEEP = 16


def set_windows_build_memo_dir(path: Path | None) -> None:
    global _WINBUILD_MEMO_DIR
    _WINBUILD_MEMO_DIR = (
        Path(path).expanduser().resolve() if path is not None else None
    )


def _windows_build_memo_key(
    command: list[str],
    *,
    source_path: Path,
    output_path: Path,
    suffix: str,
) -> str:
    digest = hashlib.sha256()
    digest.update(source_path.read_bytes())
    digest.update(b"\0")
    try:
        status = Path(command[0]).stat()
        digest.update(f"{status.st_size}:{status.st_mtime_ns}".encode("utf-8"))
    except OSError:
        digest.update(b"unknown-compiler")
    digest.update(b"\0")
    excluded = {str(source_path), str(output_path)}
    for element in command:
        if element in excluded:
            continue
        digest.update(element.encode("utf-8") + b"\x1f")
    digest.update(b"\0")
    digest.update(suffix.encode("utf-8"))
    return digest.hexdigest()


def cached_windows_build(
    command: list[str],
    *,
    label: str,
    source_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    memo_dir = _WINBUILD_MEMO_DIR
    cached: Path | None = None
    if memo_dir is not None:
        suffix = output_path.suffix or ".bin"
        cached = memo_dir / (
            "winbuild-"
            + _windows_build_memo_key(
                command, source_path=source_path, output_path=output_path, suffix=suffix
            )[:32]
            + suffix
        )
        try:
            if cached.is_file() and cached.stat().st_size > 0x1000:
                with cached.open("rb") as source:
                    header = source.read(2)
                if header == b"MZ":
                    output_path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
                    shutil.copyfile(cached, output_path)
                    output_path.chmod(0o600)
                    if output_path.is_file() and output_path.stat().st_size:
                        return {
                            "returncode": 0,
                            "stdout": "",
                            "stderr": "cached build reuse",
                        }
        except OSError:
            pass
    result = _build(command, label=label)
    if cached is None:
        return result
    try:
        data = output_path.read_bytes()
        if data[:2] == b"MZ" and len(data) > 0x1000:
            memo_dir.mkdir(parents=True, exist_ok=True, mode=0o700)
            descriptor, temporary = tempfile.mkstemp(
                prefix=f".{output_path.name}.", dir=memo_dir
            )
            try:
                os.fchmod(descriptor, 0o600)
                with os.fdopen(descriptor, "wb") as sink:
                    sink.write(data)
                    sink.flush()
                    os.fsync(sink.fileno())
                os.replace(temporary, cached)
                cached.chmod(0o600)
            except BaseException:
                Path(temporary).unlink(missing_ok=True)
                raise
    except OSError:
        pass
    try:
        records = []
        for stale in memo_dir.glob("winbuild-*"):
            if stale.is_file():
                records.append((stale.stat().st_mtime_ns, stale))
        for _, stale in sorted(records, reverse=True)[_WINBUILD_MEMO_KEEP:]:
            stale.unlink(missing_ok=True)
    except OSError:
        pass
    return result


def _inspect_snapshot(path: Path) -> dict[str, int]:

    path = path.expanduser().resolve()
    size = path.stat().st_size
    if size < SNAPSHOT_HEADER.size:
        raise AcquisitionError("runtime memory snapshot header is truncated")
    import mmap as _mmap

    with path.open("rb") as source:
        try:
            mapping = _mmap.mmap(
                source.fileno(), 0, access=_mmap.ACCESS_READ
            )
        except (OSError, ValueError) as error:
            raise AcquisitionError(
                "runtime memory snapshot header is truncated"
            ) from error
        try:
            if len(mapping) < SNAPSHOT_HEADER.size:
                raise AcquisitionError(
                    "runtime memory snapshot header is truncated"
                )
            (
                magic,
                version,
                header_bytes,
                image_base,
                image_bytes,
                expected_records,
                expected_captured,
                region_count,
                reserved0,
                reserved1,
                reserved2,
            ) = SNAPSHOT_HEADER.unpack_from(mapping, 0)
            if (
                (
                    (magic, version) not in SNAPSHOT_LEGACY_IDENTITIES
                    and (magic != SNAPSHOT_MAGIC or version != SNAPSHOT_VERSION)
                )
                or header_bytes != SNAPSHOT_HEADER.size
            ):
                raise AcquisitionError("runtime memory snapshot envelope is invalid")
            if not image_base or not image_bytes or image_base + image_bytes <= image_base:
                raise AcquisitionError("runtime memory snapshot main-image identity is invalid")
            if reserved0 or reserved1 or reserved2:
                raise AcquisitionError("runtime memory snapshot reserved header is nonzero")
            if expected_records > 10_000_000 or region_count > expected_records:
                raise AcquisitionError("runtime memory snapshot record bounds are invalid")
            records = 0
            captured = 0
            virtual_ranges: list[tuple[int, int]] = []
            cursor = SNAPSHOT_HEADER.size
            record_struct = SNAPSHOT_RECORD
            record_size = record_struct.size


            while records < expected_records:
                if cursor + record_size > size:
                    raise AcquisitionError("runtime memory snapshot record is truncated")
                address, byte_count, _protect, _memory_type, state, reserved = (
                    record_struct.unpack_from(mapping, cursor)
                )
                if (
                    not address
                    or not byte_count
                    or byte_count > 1024 * 1024
                    or address + byte_count <= address
                    or state != 0x1000
                    or reserved
                ):
                    raise AcquisitionError("runtime memory snapshot record is invalid")
                payload_end = cursor + record_size + byte_count
                if payload_end > size:
                    raise AcquisitionError("runtime memory snapshot payload is truncated")
                cursor = payload_end
                records += 1
                captured += byte_count
                virtual_ranges.append((address, address + byte_count))
            if cursor != size:
                raise AcquisitionError("runtime memory snapshot has an unaccounted trailer")
            if records != expected_records or captured != expected_captured:
                raise AcquisitionError("runtime memory snapshot counters are inconsistent")
            virtual_ranges.sort()
            if any(
                current[0] < previous[1]
                for previous, current in zip(virtual_ranges, virtual_ranges[1:])
            ):
                raise AcquisitionError("runtime memory snapshot virtual ranges overlap")
        finally:
            mapping.close()
    return {
        "bytes": size,
        "image_base": image_base,
        "image_bytes": image_bytes,
        "record_count": records,
        "captured_bytes": captured,
        "region_count": region_count,
    }


def recover_runtime_snapshot(*, incomplete: Path, output: Path) -> dict[str, Any]:

    incomplete = incomplete.expanduser().resolve()
    output = output.expanduser().resolve()
    if incomplete == output:
        raise AcquisitionError("runtime snapshot recovery requires a distinct output")
    if not incomplete.is_file() or incomplete.is_symlink():
        raise AcquisitionError("incomplete runtime snapshot is unavailable")
    _assert_owner_file(incomplete)
    _owner_directory(output.parent)
    if output.exists() or output.is_symlink():
        raise AcquisitionError("runtime snapshot recovery output already exists")
    size = incomplete.stat().st_size
    with incomplete.open("rb", buffering=0) as source:
        raw_header = source.read(SNAPSHOT_HEADER.size)
        if len(raw_header) != SNAPSHOT_HEADER.size:
            raise AcquisitionError("incomplete runtime snapshot header is truncated")
        header = list(SNAPSHOT_HEADER.unpack(raw_header))
        identity = (header[0], header[1])
        if identity not in SNAPSHOT_LEGACY_IDENTITIES and identity != (
            SNAPSHOT_MAGIC,
            SNAPSHOT_VERSION,
        ):
            raise AcquisitionError("incomplete runtime snapshot identity is invalid")
        if header[2] != SNAPSHOT_HEADER.size or not header[3] or not header[4]:
            raise AcquisitionError("incomplete runtime snapshot main image is invalid")
        if header[5] or header[6] or header[7]:
            raise AcquisitionError("runtime snapshot already has finalized counters")
        cursor = SNAPSHOT_HEADER.size
        record_count = 0
        captured_bytes = 0
        region_groups = 0
        main_image_captured = 0
        previous_end: int | None = None
        previous_attributes: tuple[int, int, int] | None = None
        image_end = header[3] + header[4]
        while cursor < size:
            if cursor + SNAPSHOT_RECORD.size > size:
                raise AcquisitionError("incomplete runtime snapshot ends in a record header")
            source.seek(cursor)
            raw_record = source.read(SNAPSHOT_RECORD.size)
            address, byte_count, protect, memory_type, state, reserved = (
                SNAPSHOT_RECORD.unpack(raw_record)
            )
            payload = cursor + SNAPSHOT_RECORD.size
            end = address + byte_count
            payload_end = payload + byte_count
            if (
                not address
                or not byte_count
                or byte_count > 1024 * 1024
                or end <= address
                or payload_end > size
                or state != 0x1000
                or reserved
                or (previous_end is not None and address < previous_end)
            ):
                raise AcquisitionError("incomplete runtime snapshot has a partial record")
            attributes = (protect, memory_type, state)
            if previous_end != address or previous_attributes != attributes:
                region_groups += 1
            overlap = max(0, min(end, image_end) - max(address, header[3]))
            main_image_captured += overlap
            previous_end = end
            previous_attributes = attributes
            captured_bytes += byte_count
            record_count += 1
            cursor = payload_end
        if cursor != size or not record_count:
            raise AcquisitionError("incomplete runtime snapshot recovery boundary is invalid")

    try:
        cloned = subprocess.run(
            ["cp", "-c", str(incomplete), str(output)],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=300,
        )
    except (OSError, subprocess.SubprocessError):
        cloned = None
    if cloned is None or cloned.returncode:
        shutil.copyfile(incomplete, output)
    output.chmod(0o600)
    _assert_owner_file(output)
    _private_bytes(
        output.with_name(output.name + ".original-header.private.bin"), raw_header
    )
    header[5] = record_count
    header[6] = captured_bytes
    header[7] = region_groups
    with output.open("r+b", buffering=0) as recovered:
        recovered.write(SNAPSHOT_HEADER.pack(*header))
        recovered.flush()
        os.fsync(recovered.fileno())
    output.chmod(0o600)
    _assert_owner_file(output)
    envelope = _inspect_snapshot(output)
    report = {
        "schema": "alpha.runtime-memory-recovery/v1",
        "status": "recovered",
        "source": {
            "bytes": size,
            "original_header_sha256": hashlib.sha256(raw_header).hexdigest(),
            "preserved_unchanged": True,
        },
        "output": file_identity(output),
        "envelope": envelope,
        "main_image_captured_bytes": main_image_captured,
        "main_image_declared_bytes": header[4],
        "record_boundary_complete": True,
        "region_count_is_derived_group_count": True,
        "official_runtime_attested": False,
        "owner_only": True,
    }
    _private_json(output.with_name(output.name + ".recovery.private.json"), report)
    return {
        "schema": report["schema"],
        "status": report["status"],
        "snapshot": {
            "bytes": envelope["bytes"],
            "sha256": report["output"]["sha256"],
            "record_count": envelope["record_count"],
            "captured_bytes": envelope["captured_bytes"],
            "main_image_captured_bytes": main_image_captured,
            "main_image_declared_bytes": header[4],
        },
        "record_boundary_complete": True,
        "official_runtime_attested": False,
        "owner_only": True,
    }


def prepare_runtime_dump(
    *,
    game_dir: Path,
    executable: Path | None,
    output_dir: Path,
    compiler: Path | None = None,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    context = CollectionContext(game_dir=game_dir, executable=executable)
    target, _client = collect_target(context)
    target_executable = Path(target.executable_path)
    metadata_candidates = [
        path.resolve()
        for path in (target_executable.parent / f"{target_executable.stem}_Data").rglob(
            "global-metadata.dat"
        )
        if path.is_file() and not path.is_symlink()
    ]
    metadata_identities: dict[str, list[Path]] = {}
    for path in metadata_candidates:
        metadata_identities.setdefault(sha256_file(path), []).append(path)
    if len(metadata_identities) != 1:
        raise AcquisitionError(
            f"current metadata identity must be unique, observed {len(metadata_identities)}"
        )
    encrypted_sha256, mirrors = next(iter(metadata_identities.items()))

    source_dir = _owner_directory(output_dir / "build")
    reflection = reflection_contract()
    inventory = runtime_inventory_contract()
    _private_json(output_dir / "reflection-contract.private.json", reflection)
    _private_json(output_dir / "runtime-inventory-contract.private.json", inventory)
    from alpha.p14 import discover_reflection_bootstrap
    from alpha.c04 import discover_runtime_resolver

    resolver_path = output_dir / "runtime-resolver.private.json"
    resolver = discover_runtime_resolver(binary=target_executable)
    _private_json(resolver_path, resolver)
    bootstrap_path = output_dir / "reflection-bootstrap.private.json"
    bootstrap = discover_reflection_bootstrap(
        binary=target_executable,
        resolver_model=resolver_path,
    )
    _private_json(bootstrap_path, bootstrap)
    metadata_path = output_dir / "global-metadata.dat"
    status_path = output_dir / "runtime-status.private.json"
    reflection_dispatch_path = output_dir / "reflection-dispatch.private.bin"
    inventory_dispatch_path = output_dir / "runtime-inventory-dispatch.private.bin"
    inventory_observation_path = (
        output_dir / "runtime-inventory-observation.private.bin"
    )
    member_observation_path = output_dir / "runtime-member-observation.private.bin"
    type_identity_observation_path = (
        output_dir / "runtime-type-identity-observation.private.bin"
    )
    member_detail_observation_path = (
        output_dir / "runtime-member-detail-observation.private.bin"
    )
    type_graph_observation_path = (
        output_dir / "runtime-type-graph-observation.private.bin"
    )
    method_native_observation_path = (
        output_dir / "runtime-method-native-observation.private.bin"
    )
    field_native_observation_path = (
        output_dir / "runtime-field-native-observation.private.bin"
    )
    metadata_usage_observation_path = (
        output_dir / "runtime-metadata-usage-observation.private.bin"
    )
    type_native_observation_path = (
        output_dir / "runtime-type-native-observation.private.bin"
    )
    type_metadata_usage_observation_path = (
        output_dir / "runtime-type-metadata-usage-observation.private.bin"
    )
    status_path.unlink(missing_ok=True)
    metadata_path.unlink(missing_ok=True)
    reflection_dispatch_path.unlink(missing_ok=True)
    inventory_dispatch_path.unlink(missing_ok=True)
    inventory_observation_path.unlink(missing_ok=True)
    member_observation_path.unlink(missing_ok=True)
    type_identity_observation_path.unlink(missing_ok=True)
    member_detail_observation_path.unlink(missing_ok=True)
    type_graph_observation_path.unlink(missing_ok=True)
    method_native_observation_path.unlink(missing_ok=True)
    field_native_observation_path.unlink(missing_ok=True)
    metadata_usage_observation_path.unlink(missing_ok=True)
    type_native_observation_path.unlink(missing_ok=True)
    type_metadata_usage_observation_path.unlink(missing_ok=True)
    collector_source = source_dir / "runtime-collector.c"
    injector_source = source_dir / "runtime-injector.c"
    collector_dll = source_dir / "alpha-runtime-collector.dll"
    injector_exe = source_dir / "alpha-runtime-injector.exe"
    _private_text(
        collector_source,
        runtime_collector_source(
            expected_executable_sha256=target.executable_sha256,
            metadata_path=metadata_path,
            status_path=status_path,
            reflection_dispatch_path=reflection_dispatch_path,
            inventory_dispatch_path=inventory_dispatch_path,
            inventory_observation_path=inventory_observation_path,
            member_observation_path=member_observation_path,
            type_identity_observation_path=type_identity_observation_path,
            member_detail_observation_path=member_detail_observation_path,
            type_graph_observation_path=type_graph_observation_path,
            method_native_observation_path=method_native_observation_path,
            field_native_observation_path=field_native_observation_path,
            metadata_usage_observation_path=metadata_usage_observation_path,
            type_native_observation_path=type_native_observation_path,
            type_metadata_usage_observation_path=(
                type_metadata_usage_observation_path
            ),
            expected_reflection_type_cache_count=len(bootstrap["type_caches"]),
            expected_reflection_state_slot_rva=bootstrap["state_slot_rva"],
            expected_reflection_cached_owners=tuple(
                (owner["namespace"], owner["type_name"])
                for owner in bootstrap["contract"][
                    "observed_concrete_owner_pairs"
                ]
            ),
        ),
    )
    _private_text(injector_source, runtime_injector_source())
    selected_compiler = _compiler(compiler)
    collector_command = [
        str(selected_compiler), "-O2", "-s", "-shared", "-Wall", "-Wextra",
        "-Wformat=2", "-Werror=format", str(collector_source), "-o",
        str(collector_dll), "-lbcrypt",
    ]
    injector_command = [
        str(selected_compiler), "-O2", "-s", "-municode", "-Wall", "-Wextra",
        "-Wformat=2", "-Werror=format", str(injector_source), "-o",
        str(injector_exe),
    ]
    _build(collector_command, label="runtime collector")
    _build(injector_command, label="runtime injector")
    for artifact in (collector_dll, injector_exe):
        if not artifact.is_file() or artifact.stat().st_size == 0:
            raise AcquisitionError(f"runtime build did not produce {artifact.name}")
        artifact.chmod(0o600)
    plan = {
        "schema": PLAN_SCHEMA,
        "status": "prepared",
        "target": target.public(),
        "encrypted_metadata": {
            "sha256": encrypted_sha256,
            "bytes": mirrors[0].stat().st_size,
            "mirror_count": len(mirrors),
        },
        "collector": file_identity(collector_dll),
        "injector": file_identity(injector_exe),
        "outputs": {
            "metadata": str(metadata_path),
            "status": str(status_path),
            "reflection_dispatch": str(reflection_dispatch_path),
            "runtime_inventory_dispatch": str(inventory_dispatch_path),
            "runtime_inventory_observation": str(inventory_observation_path),
            "runtime_member_observation": str(member_observation_path),
            "runtime_type_identity_observation": str(
                type_identity_observation_path
            ),
            "runtime_member_detail_observation": str(
                member_detail_observation_path
            ),
            "runtime_type_graph_observation": str(
                type_graph_observation_path
            ),
            "runtime_method_native_observation": str(
                method_native_observation_path
            ),
            "runtime_field_native_observation": str(
                field_native_observation_path
            ),
            "runtime_metadata_usage_observation": str(
                metadata_usage_observation_path
            ),
            "runtime_type_native_observation": str(
                type_native_observation_path
            ),
            "runtime_type_metadata_usage_observation": str(
                type_metadata_usage_observation_path
            ),
            "runtime_resolver_model": str(resolver_path),
            "reflection_bootstrap_model": str(bootstrap_path),
        },
        "policy": {
            "fresh_runtime_required": True,
            "current_executable_sha256_embedded": True,
            "fixed_address_used": False,
            "fixed_heap_range_used": False,
            "network_used": False,
            "external_runtime_plugin_used": False,
            "saved_dump_used_for_generation": False,
            "reflection_contract_id": reflection["contract_id"],
            "reflection_operation_count": reflection["operation_count"],
            "runtime_inventory_contract_id": inventory["contract_id"],
            "runtime_inventory_operation_count": inventory["operation_count"],
            "runtime_resolver_model_sha256": file_identity(resolver_path)["sha256"],
            "reflection_bootstrap_model_sha256": file_identity(bootstrap_path)[
                "sha256"
            ],
            "reflection_type_cache_count": len(bootstrap["type_caches"]),
            "reflection_state_slot_derived_for_current_target": True,
            "reflection_state_slot_rva": bootstrap["state_slot_rva"],
            "reflection_expected_owner_class_count": len(
                bootstrap["contract"]["observed_concrete_owner_pairs"]
            ),
            "reflection_contract_owner_class_count": len(
                {
                    operation["runtime_owner"]
                    for operation in reflection["operations"]
                }
                | {
                    owner
                    for operation in inventory["operations"]
                    for owner in operation["runtime_owners"]
                }
            ),
            "reflection_type_helper_candidate_count": len(
                bootstrap["type_helper_candidates"]
            ),
            "reflection_runtime_name_operation_keys": list(
                RUNTIME_NAME_OPERATION_KEYS
            ),
            "reflection_runtime_direct_object_operation_keys": list(
                RUNTIME_DIRECT_OBJECT_OPERATION_KEYS
            ),
            "reflection_runtime_parameter_flag_operation_keys": list(
                RUNTIME_PARAMETER_FLAG_OPERATION_KEYS
            ),
            "reflection_runtime_sentinel_field_operation_keys": list(
                RUNTIME_SENTINEL_FIELD_OPERATION_KEYS
            ),
            "reflection_runtime_direct_dword_operation_keys": list(
                RUNTIME_DIRECT_DWORD_OPERATION_KEYS
            ),
            "reflection_runtime_property_accessor_operation_keys": list(
                RUNTIME_PROPERTY_ACCESSOR_OPERATION_KEYS
            ),
            "reflection_runtime_semantic_operation_keys": list(
                RUNTIME_SEMANTIC_OPERATION_KEYS
            ),
            "reflection_runtime_operation_name_contract_count": reflection[
                "operation_count"
            ],
            "reflection_method_name_managed_thread_required": True,
            "reflection_method_name_probe_timeout_seconds": 15,
            "reflection_dispatch_manifest_required": True,
            "reflection_dispatch_manifest_owner_only": True,
            "runtime_inventory_dispatch_manifest_required": True,
            "runtime_inventory_dispatch_manifest_owner_only": True,
            "runtime_inventory_observation_required": True,
            "runtime_inventory_observation_owner_only": True,
            "runtime_member_observation_required": True,
            "runtime_member_observation_owner_only": True,
            "runtime_type_identity_observation_required": True,
            "runtime_type_identity_observation_owner_only": True,
            "runtime_member_detail_observation_required": True,
            "runtime_member_detail_observation_owner_only": True,
            "runtime_type_graph_observation_required": True,
            "runtime_type_graph_observation_owner_only": True,
            "runtime_method_native_observation_required": True,
            "runtime_method_native_observation_owner_only": True,
            "runtime_method_metadata_offset_seeded": False,
            "runtime_method_rva_seeded": False,
            "runtime_method_slot_offset_seeded": False,
            "runtime_field_native_observation_required": True,
            "runtime_field_native_observation_owner_only": True,
            "runtime_field_metadata_stride_seeded": False,
            "runtime_field_offset_seeded": False,
            "runtime_metadata_usage_observation_required": True,
            "runtime_metadata_usage_observation_owner_only": True,
            "runtime_metadata_usage_table_index_seeded": False,
            "runtime_metadata_usage_stride_seeded": False,
            "runtime_metadata_usage_count_seeded": False,
            "runtime_metadata_usage_address_seeded": False,
            "runtime_type_native_observation_required": True,
            "runtime_type_native_observation_owner_only": True,
            "runtime_type_handle_offset_seeded": False,
            "runtime_type_metadata_usage_observation_required": True,
            "runtime_type_metadata_usage_observation_owner_only": True,
            "runtime_type_registration_count_seeded": False,
            "runtime_type_registration_address_seeded": False,
            "managed_thread_rendezvous_required": inventory[
                "resolution_policy"
            ]["managed_thread_observation_required_before_invocation"],
            "managed_window_selection_fail_closed": True,
            "managed_probe_timeout_seconds": 15,
            "inventory_invocation_from_native_worker": False,
            "reflection_minimum_runtime_semantic_operation_count": len(
                RUNTIME_SEMANTIC_OPERATION_KEYS
            ),
            "semantic_operation_resolution_complete": bootstrap["contract"][
                "semantic_operation_resolution_complete"
            ],
        },
    }
    _private_json(output_dir / "capture-plan.private.json", plan)
    return plan


def capture_runtime_dump(
    *,
    game_dir: Path,
    executable: Path | None,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float = 900.0,
) -> dict[str, Any]:
    output_dir = _owner_directory(output_dir)
    plan = prepare_runtime_dump(
        game_dir=game_dir,
        executable=executable,
        output_dir=output_dir,
        compiler=compiler,
    )
    target_path = Path(plan["target"]["executable_path"])
    if sha256_file(target_path) != plan["target"]["executable_sha256"]:
        raise AcquisitionError("target executable changed after runtime dump preparation")
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise DependencyUnavailable("selected Wine binary or prefix is unavailable")
    build_dir = output_dir / "build"
    collector = build_dir / "alpha-runtime-collector.dll"
    injector = build_dir / "alpha-runtime-injector.exe"
    command = _host_run(str(wine), injector, collector, target_path.name)
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            command,
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError("ALPHA v2 runtime injector could not run") from error
    _private_text(
        output_dir / "injector.private.log",
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
        raise AcquisitionError(f"ALPHA v2 runtime injection failed ({injected.returncode})")
    status_path = output_dir / "runtime-status.private.json"
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
        raise AcquisitionError("ALPHA v2 runtime metadata capture timed out")
    metadata_path = output_dir / "global-metadata.dat"
    reflection_dispatch_path = output_dir / "reflection-dispatch.private.bin"
    inventory_dispatch_path = output_dir / "runtime-inventory-dispatch.private.bin"
    inventory_observation_path = (
        output_dir / "runtime-inventory-observation.private.bin"
    )
    member_observation_path = output_dir / "runtime-member-observation.private.bin"
    type_identity_observation_path = (
        output_dir / "runtime-type-identity-observation.private.bin"
    )
    member_detail_observation_path = (
        output_dir / "runtime-member-detail-observation.private.bin"
    )
    type_graph_observation_path = (
        output_dir / "runtime-type-graph-observation.private.bin"
    )
    method_native_observation_path = (
        output_dir / "runtime-method-native-observation.private.bin"
    )
    field_native_observation_path = (
        output_dir / "runtime-field-native-observation.private.bin"
    )
    metadata_usage_observation_path = (
        output_dir / "runtime-metadata-usage-observation.private.bin"
    )
    type_native_observation_path = (
        output_dir / "runtime-type-native-observation.private.bin"
    )
    type_metadata_usage_observation_path = (
        output_dir / "runtime-type-metadata-usage-observation.private.bin"
    )
    sealed_runtime_outputs = {
        path.name: _seal_runtime_output(path)
        for path in (
            status_path,
            metadata_path,
            reflection_dispatch_path,
            inventory_dispatch_path,
            inventory_observation_path,
            member_observation_path,
            type_identity_observation_path,
            member_detail_observation_path,
            type_graph_observation_path,
            method_native_observation_path,
            field_native_observation_path,
            metadata_usage_observation_path,
            type_native_observation_path,
            type_metadata_usage_observation_path,
        )
    }
    reflection_dispatch: dict[str, Any] | None = None
    inventory_dispatch: dict[str, Any] | None = None
    inventory_observation: dict[str, Any] | None = None
    member_observation: dict[str, Any] | None = None
    type_identity_observation: dict[str, Any] | None = None
    member_detail_observation: dict[str, Any] | None = None
    type_graph_observation: dict[str, Any] | None = None
    method_native_observation: dict[str, Any] | None = None
    field_native_observation: dict[str, Any] | None = None
    metadata_usage_observation: dict[str, Any] | None = None
    type_native_observation: dict[str, Any] | None = None
    type_metadata_usage_observation: dict[str, Any] | None = None
    if reflection_dispatch_path.is_file():
        try:
            reflection_dispatch = load_runtime_dispatch_manifest(
                reflection_dispatch_path,
                expected_executable_sha256=plan["target"]["executable_sha256"],
            )
        except AcquisitionError:
            reflection_dispatch = None
    if inventory_dispatch_path.is_file():
        try:
            inventory_dispatch = load_runtime_inventory_dispatch_manifest(
                inventory_dispatch_path,
                expected_executable_sha256=plan["target"]["executable_sha256"],
            )
        except AcquisitionError:
            inventory_dispatch = None
    if inventory_observation_path.is_file():
        try:
            inventory_observation = load_runtime_inventory_observation(
                inventory_observation_path,
                expected_executable_sha256=plan["target"]["executable_sha256"],
            )
        except AcquisitionError:
            inventory_observation = None
    if member_observation_path.is_file() and inventory_observation is not None:
        try:
            member_observation = load_runtime_member_observation(
                member_observation_path,
                type_observation_path=inventory_observation_path,
                expected_executable_sha256=plan["target"]["executable_sha256"],
            )
        except AcquisitionError:
            member_observation = None
    if type_identity_observation_path.is_file() and inventory_observation is not None:
        try:
            type_identity_observation = load_runtime_type_identity_observation(
                type_identity_observation_path,
                type_observation_path=inventory_observation_path,
                expected_executable_sha256=plan["target"]["executable_sha256"],
            )
        except AcquisitionError:
            type_identity_observation = None
    if (
        member_detail_observation_path.is_file()
        and inventory_observation is not None
        and member_observation is not None
        and type_identity_observation is not None
    ):
        try:
            member_detail_observation = load_runtime_member_detail_observation(
                member_detail_observation_path,
                type_observation_path=inventory_observation_path,
                member_observation_path=member_observation_path,
                type_identity_observation_path=type_identity_observation_path,
                expected_executable_sha256=plan["target"]["executable_sha256"],
            )
        except AcquisitionError:
            member_detail_observation = None
    if (
        type_graph_observation_path.is_file()
        and member_detail_observation is not None
    ):
        try:
            type_graph_observation = load_runtime_type_graph_observation(
                type_graph_observation_path,
                type_observation_path=inventory_observation_path,
                member_observation_path=member_observation_path,
                type_identity_observation_path=type_identity_observation_path,
                member_detail_observation_path=member_detail_observation_path,
                expected_executable_sha256=plan["target"]["executable_sha256"],
            )
        except AcquisitionError:
            type_graph_observation = None
    if (
        method_native_observation_path.is_file()
        and type_graph_observation is not None
    ):
        try:
            method_native_observation = load_runtime_method_native_observation(
                method_native_observation_path,
                type_observation_path=inventory_observation_path,
                member_observation_path=member_observation_path,
                type_identity_observation_path=type_identity_observation_path,
                member_detail_observation_path=member_detail_observation_path,
                type_graph_observation_path=type_graph_observation_path,
                expected_executable_sha256=plan["target"][
                    "executable_sha256"
                ],
            )
        except AcquisitionError:
            method_native_observation = None
    if (
        field_native_observation_path.is_file()
        and method_native_observation is not None
    ):
        try:
            field_native_observation = load_runtime_field_native_observation(
                field_native_observation_path,
                type_observation_path=inventory_observation_path,
                member_observation_path=member_observation_path,
                type_identity_observation_path=type_identity_observation_path,
                member_detail_observation_path=member_detail_observation_path,
                type_graph_observation_path=type_graph_observation_path,
                method_native_observation_path=method_native_observation_path,
                expected_executable_sha256=plan["target"][
                    "executable_sha256"
                ],
            )
        except AcquisitionError:
            field_native_observation = None
    if (
        type_native_observation_path.is_file()
        and type_graph_observation is not None
    ):
        try:
            type_native_observation = load_runtime_type_native_observation(
                type_native_observation_path,
                type_observation_path=inventory_observation_path,
                member_observation_path=member_observation_path,
                type_identity_observation_path=type_identity_observation_path,
                member_detail_observation_path=member_detail_observation_path,
                type_graph_observation_path=type_graph_observation_path,
                expected_executable_sha256=plan["target"][
                    "executable_sha256"
                ],
            )
        except AcquisitionError:
            type_native_observation = None
    if (
        metadata_usage_observation_path.is_file()
        and metadata_path.is_file()
        and member_detail_observation is not None
    ):
        try:
            metadata_usage_observation = load_runtime_metadata_usage_observation(
                metadata_usage_observation_path,
                metadata_path=metadata_path,
                type_observation_path=inventory_observation_path,
                member_observation_path=member_observation_path,
                type_identity_observation_path=type_identity_observation_path,
                member_detail_observation_path=member_detail_observation_path,
                expected_executable_sha256=plan["target"][
                    "executable_sha256"
                ],
            )
        except AcquisitionError:
            metadata_usage_observation = None
    if (
        type_metadata_usage_observation_path.is_file()
        and metadata_path.is_file()
        and metadata_usage_observation is not None
        and type_native_observation is not None
        and type_graph_observation is not None
    ):
        try:
            type_metadata_usage_observation = (
                load_runtime_type_metadata_usage_observation(
                    type_metadata_usage_observation_path,
                    metadata_path=metadata_path,
                    metadata_usage_observation_path=(
                        metadata_usage_observation_path
                    ),
                    type_native_observation_path=(
                        type_native_observation_path
                    ),
                    type_observation_path=inventory_observation_path,
                    member_observation_path=member_observation_path,
                    type_identity_observation_path=(
                        type_identity_observation_path
                    ),
                    member_detail_observation_path=(
                        member_detail_observation_path
                    ),
                    type_graph_observation_path=type_graph_observation_path,
                    expected_executable_sha256=plan["target"][
                        "executable_sha256"
                    ],
                )
            )
        except AcquisitionError:
            type_metadata_usage_observation = None
    runtime_outputs_owner_only = all(
        sealed or not (output_dir / name).exists()
        for name, sealed in sealed_runtime_outputs.items()
    )
    checks = {
        "schema": status.get("schema") == RUNTIME_SCHEMA,
        "runtime_outputs_owner_only": runtime_outputs_owner_only,
        "complete": status.get("status") == "complete",
        "executable_hash_matches": status.get("executable_hash_matches") is True,
        "expected_hash_matches_plan": status.get("expected_executable_sha256")
        == plan["target"]["executable_sha256"],
        "observed_hash_matches_plan": status.get("observed_executable_sha256")
        == plan["target"]["executable_sha256"],
        "fresh_runtime_observation": status.get("fresh_runtime_observation") is True,
        "runtime_resolver_unique": status.get("runtime_resolver_unique") is True,
        "reflection_state_initialized": status.get(
            "reflection_state_initialized"
        )
        is True,
        "reflection_bootstrap_wait_bounded": isinstance(
            status.get("reflection_bootstrap_attempt_count"), int
        )
        and status["reflection_bootstrap_attempt_count"] >= 1
        and isinstance(
            status.get("reflection_bootstrap_wait_milliseconds"), int
        )
        and 0 <= status["reflection_bootstrap_wait_milliseconds"] <= 65000,
        "reflection_type_resolver_helper_unique": status.get(
            "reflection_type_resolver_helper_unique"
        )
        is True,
        "reflection_type_cache_count_matches_preflight": status.get(
            "reflection_type_cache_count_matches_preflight"
        )
        is True,
        "reflection_type_cache_count_matches_plan": status.get(
            "reflection_type_cache_count"
        )
        == plan["policy"]["reflection_type_cache_count"],
        "reflection_initialized_type_caches_present": isinstance(
            status.get("reflection_initialized_type_cache_count"), int
        )
        and status["reflection_initialized_type_cache_count"] > 0,
        "reflection_expected_owner_class_count_matches_plan": status.get(
            "reflection_expected_owner_class_count"
        )
        == plan["policy"]["reflection_expected_owner_class_count"],
        "reflection_owner_classes_initialized": status.get(
            "reflection_initialized_owner_class_count"
        )
        == plan["policy"]["reflection_expected_owner_class_count"],
        "reflection_all_contract_owner_classes_available": status.get(
            "reflection_contract_owner_class_count"
        )
        == plan["policy"]["reflection_contract_owner_class_count"]
        and status.get("reflection_all_contract_owner_classes_available") is True
        and status.get("reflection_dynamically_resolved_owner_class_count")
        == plan["policy"]["reflection_contract_owner_class_count"]
        - plan["policy"]["reflection_expected_owner_class_count"],
        "reflection_vtable_boundary_derived": status.get(
            "reflection_vtable_boundary_derived"
        )
        is True,
        "reflection_method_layout_unique": status.get(
            "reflection_method_layout_unique"
        )
        is True,
        "reflection_methods_enumerated": isinstance(
            status.get("reflection_method_record_count"), int
        )
        and status["reflection_method_record_count"] > 0,
        "reflection_declaring_class_field_unique": status.get(
            "reflection_declaring_class_field_unique"
        )
        is True,
        "reflection_method_pointer_field_unique": status.get(
            "reflection_method_pointer_field_unique"
        )
        is True,
        "reflection_observed_class_layout_complete": status.get(
            "reflection_observed_class_layout_complete"
        )
        is True,
        "reflection_name_objects_present": isinstance(
            status.get("reflection_name_object_reference_counts"), dict
        )
        and set(status["reflection_name_object_reference_counts"])
        == set(plan["policy"]["reflection_runtime_name_operation_keys"])
        and all(
            isinstance(count, int) and count > 0
            for count in status["reflection_name_object_reference_counts"].values()
        ),
        "reflection_cached_name_fields_semantically_unique": status.get(
            "reflection_cached_name_field_unique_operation_count"
        )
        == len(plan["policy"]["reflection_runtime_name_operation_keys"]),
        "reflection_name_getters_unique": isinstance(
            status.get("reflection_name_getter_candidate_counts"), dict
        )
        and set(status["reflection_name_getter_candidate_counts"])
        == set(plan["policy"]["reflection_runtime_name_operation_keys"])
        and all(
            count == 1
            for count in status["reflection_name_getter_candidate_counts"].values()
        )
        and status.get("reflection_name_getter_unique_operation_count")
        == len(plan["policy"]["reflection_runtime_name_operation_keys"])
        and status.get("reflection_name_getters_semantically_unique") is True,
        "reflection_parameter_type_field_semantically_unique": isinstance(
            status.get("reflection_parameter_type_object_reference_count"), int
        )
        and status["reflection_parameter_type_object_reference_count"] > 0
        and status.get("reflection_parameter_type_field_semantically_unique")
        is True,
        "reflection_parameter_type_getter_unique": status.get(
            "reflection_parameter_type_getter_candidate_count"
        )
        == 1
        and status.get("reflection_parameter_type_getter_semantically_unique")
        is True,
        "reflection_parameter_flag_getters_unique": isinstance(
            status.get("reflection_parameter_flag_getter_candidate_counts"), dict
        )
        and set(status["reflection_parameter_flag_getter_candidate_counts"])
        == set(
            plan["policy"]["reflection_runtime_parameter_flag_operation_keys"]
        )
        and all(
            count == 1
            for count in status[
                "reflection_parameter_flag_getter_candidate_counts"
            ].values()
        )
        and isinstance(
            status.get("reflection_parameter_flag_object_reference_count"), int
        )
        and status["reflection_parameter_flag_object_reference_count"] >= 8
        and status.get("reflection_parameter_flag_field_semantically_unique")
        is True
        and status.get("reflection_parameter_flag_observation_complete") is True
        and status.get("reflection_parameter_flag_getters_semantically_unique")
        is True,
        "reflection_parameter_default_getter_unique": status.get(
            "reflection_parameter_default_field_semantically_unique"
        )
        is True
        and status.get("reflection_parameter_default_getter_candidate_count") == 1
        and status.get(
            "reflection_parameter_default_getter_semantically_unique"
        )
        is True,
        "reflection_field_attributes_getter_unique": isinstance(
            status.get("reflection_field_attributes_object_reference_count"), int
        )
        and status["reflection_field_attributes_object_reference_count"] >= 8
        and status.get("reflection_field_attributes_getter_candidate_count") == 1
        and status.get("reflection_field_attributes_getter_semantically_unique")
        is True
        and status.get("reflection_field_attributes_observation_complete") is True,
        "reflection_property_accessors_unique": isinstance(
            status.get("reflection_property_named_object_reference_count"), int
        )
        and status["reflection_property_named_object_reference_count"] >= 8
        and isinstance(
            status.get("reflection_property_accessor_field_support_counts"), dict
        )
        and set(status["reflection_property_accessor_field_support_counts"])
        == set(
            plan["policy"]["reflection_runtime_property_accessor_operation_keys"]
        )
        and all(
            isinstance(count, int) and count >= 8
            for count in status[
                "reflection_property_accessor_field_support_counts"
            ].values()
        )
        and isinstance(
            status.get("reflection_property_accessor_getter_candidate_counts"),
            dict,
        )
        and set(status["reflection_property_accessor_getter_candidate_counts"])
        == set(
            plan["policy"]["reflection_runtime_property_accessor_operation_keys"]
        )
        and all(
            count == 1
            for count in status[
                "reflection_property_accessor_getter_candidate_counts"
            ].values()
        )
        and status.get("reflection_property_accessors_semantically_unique") is True,
        "reflection_method_name_decoder_current_bound": status.get(
            "reflection_method_name_decoder_derived"
        )
        is True
        and status.get(
            "reflection_method_name_lazy_initializer_semantically_bound"
        )
        is True
        and status.get("reflection_runtime_operation_name_contract_count")
        == plan["policy"]["reflection_runtime_operation_name_contract_count"],
        "reflection_method_name_managed_thread_observed": plan["policy"].get(
            "reflection_method_name_managed_thread_required"
        )
        is True
        and status.get("reflection_method_name_window_candidate_count") == 1
        and status.get(
            "reflection_method_name_window_thread_matches_callback"
        )
        is True
        and status.get("reflection_method_name_managed_callback_complete") is True,
        "reflection_method_name_observation_complete": isinstance(
            status.get("reflection_method_name_decode_attempt_count"), int
        )
        and status["reflection_method_name_decode_attempt_count"]
        == status.get("reflection_method_record_count")
        and isinstance(
            status.get("reflection_method_name_decode_success_count"), int
        )
        and 0 < status["reflection_method_name_decode_success_count"]
        <= status["reflection_method_name_decode_attempt_count"]
        and isinstance(
            status.get("reflection_method_name_lazy_initialization_count"), int
        )
        and 0 <= status["reflection_method_name_lazy_initialization_count"]
        <= status["reflection_method_name_decode_attempt_count"],
        "reflection_method_parameter_count_field_unique": status.get(
            "reflection_method_parameter_count_field_candidate_count"
        )
        == 1
        and status.get(
            "reflection_method_parameter_count_field_semantically_unique"
        )
        is True
        and status.get(
            "reflection_method_parameter_count_observation_complete"
        )
        is True,
        "reflection_runtime_operation_names_present": isinstance(
            status.get("reflection_runtime_named_operation_match_count"), int
        )
        and status["reflection_runtime_named_operation_match_count"]
        >= plan["policy"][
            "reflection_minimum_runtime_semantic_operation_count"
        ]
        and isinstance(
            status.get("reflection_runtime_named_operation_unique_count"), int
        )
        and 0 <= status["reflection_runtime_named_operation_unique_count"]
        <= status["reflection_runtime_named_operation_match_count"],
        "reflection_runtime_operation_arities_unique": isinstance(
            status.get("reflection_runtime_arity_operation_match_count"), int
        )
        and isinstance(
            status.get("reflection_runtime_arity_operation_unique_count"), int
        )
        and status["reflection_runtime_arity_operation_unique_count"]
        >= plan["policy"][
            "reflection_minimum_runtime_semantic_operation_count"
        ]
        and status["reflection_runtime_arity_operation_unique_count"]
        <= status["reflection_runtime_arity_operation_match_count"]
        and status.get("reflection_semantic_operation_count")
        == status["reflection_runtime_arity_operation_unique_count"],
        "reflection_dispatch_contract_complete": status.get(
            "reflection_dispatch_contract_complete"
        )
        is True
        and status.get("reflection_dispatch_manifest_written") is True
        and reflection_dispatch is not None
        and reflection_dispatch["operation_count"]
        == plan["policy"]["reflection_operation_count"]
        and reflection_dispatch["contract_id"]
        == plan["policy"]["reflection_contract_id"],
        "runtime_inventory_dispatch_contract_complete": status.get(
            "inventory_dispatch_contract_complete"
        )
        is True
        and status.get("inventory_dispatch_manifest_written") is True
        and status.get("inventory_runtime_arity_operation_unique_count")
        == plan["policy"]["runtime_inventory_operation_count"]
        and inventory_dispatch is not None
        and inventory_dispatch["operation_count"]
        == plan["policy"]["runtime_inventory_operation_count"]
        and inventory_dispatch["contract_id"]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_inventory_managed_thread_observed": plan["policy"].get(
            "managed_thread_rendezvous_required"
        )
        is True
        and status.get("managed_window_candidate_count") == 1
        and status.get("managed_window_thread_matches_callback") is True
        and status.get("managed_thread_object_observed") is True
        and status.get("managed_thread_class_matches") is True
        and status.get("current_domain_object_observed") is True
        and status.get("current_domain_class_matches") is True
        and status.get("managed_thread_observation_complete") is True,
        "runtime_inventory_assembly_root_complete": status.get(
            "assembly_array_observed"
        )
        is True
        and status.get("assembly_array_layout_candidate_count") == 1
        and status.get("assembly_array_layout_unique") is True
        and isinstance(status.get("assembly_count"), int)
        and status["assembly_count"] > 0
        and status.get("all_assembly_objects_class_valid") is True
        and status.get("assembly_root_inventory_complete") is True,
        "runtime_inventory_type_roots_complete": inventory_observation is not None
        and status.get("type_inventory_observation_written") is True
        and status.get("type_inventory_observation_complete") is True
        and status.get("type_inventory_all_objects_class_valid") is True
        and status.get("type_inventory_globally_unique") is True
        and status.get("type_inventory_completed_slice_count")
        == status.get("assembly_count")
        and status.get("type_inventory_assembly_count")
        == inventory_observation["assembly_count"]
        == status.get("assembly_count")
        and status.get("type_inventory_type_count")
        == inventory_observation["type_count"]
        and inventory_observation["contract"]["contract_id"]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_inventory_member_roots_complete": member_observation is not None
        and status.get("member_inventory_observation_written") is True
        and status.get("member_inventory_observation_complete") is True
        and status.get("member_inventory_all_objects_class_valid") is True
        and status.get("member_inventory_globally_unique") is True
        and status.get("member_inventory_completed_slice_count")
        == status.get("type_inventory_type_count")
        == status.get("member_inventory_type_count")
        == member_observation["type_count"]
        and status.get("member_inventory_field_count")
        == member_observation["counts"]["fields"]
        and status.get("member_inventory_method_count")
        == member_observation["counts"]["methods"]
        and status.get("member_inventory_constructor_count")
        == member_observation["counts"]["constructors"]
        and status.get("member_inventory_property_count")
        == member_observation["counts"]["properties"]
        and status.get("member_inventory_event_count")
        == member_observation["counts"]["events"]
        and status.get("member_inventory_nested_type_count")
        == member_observation["counts"]["nested_types"]
        and member_observation["contract"]["contract_id"]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_type_identity_complete": type_identity_observation is not None
        and status.get("type_identity_observation_written") is True
        and status.get("type_identity_observation_complete") is True
        and status.get("type_identity_all_names_valid") is True
        and status.get("type_identity_references_valid") is True
        and status.get("type_identity_assembly_count")
        == type_identity_observation["assembly_count"]
        == status.get("assembly_count")
        and status.get("type_identity_type_count")
        == type_identity_observation["type_count"]
        == status.get("type_inventory_type_count")
        and status.get("type_identity_relation_count")
        == type_identity_observation["relation_count"]
        and type_identity_observation["contract"]["contract_id"]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_member_detail_complete": member_detail_observation is not None
        and status.get("member_detail_observation_written") is True
        and status.get("member_detail_observation_complete") is True
        and status.get("member_detail_type_count")
        == member_detail_observation["type_count"]
        == status.get("type_inventory_type_count")
        and isinstance(status.get("member_detail_observation_bytes"), int)
        and status["member_detail_observation_bytes"]
        == member_detail_observation_path.stat().st_size
        and member_detail_observation["counts"]
        == {
            category: member_observation["counts"][category]
            for category in member_detail_observation["counts"]
        }
        and member_detail_observation["contracts"][
            "reflection_contract_id"
        ]
        == plan["policy"]["reflection_contract_id"]
        and member_detail_observation["contracts"][
            "inventory_contract_id"
        ]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_type_graph_complete": type_graph_observation is not None
        and status.get("type_graph_observation_written") is True
        and status.get("type_graph_observation_complete") is True
        and status.get("type_graph_reference_closure_complete") is True
        and status.get("type_graph_root_count")
        == type_graph_observation["root_count"]
        == status.get("type_inventory_type_count")
        and status.get("type_graph_node_count")
        == type_graph_observation["node_count"]
        and isinstance(status.get("type_graph_observation_bytes"), int)
        and status["type_graph_observation_bytes"]
        == type_graph_observation_path.stat().st_size
        and type_graph_observation["reference_closure_complete"] is True
        and type_graph_observation["contract"]["inventory_contract_id"]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_type_native_complete": type_native_observation is not None
        and status.get("type_native_observation_written") is True
        and status.get("type_native_observation_complete") is True
        and status.get("type_native_roundtrip_complete") is True
        and status.get("type_native_node_count")
        == type_native_observation["node_count"]
        == type_graph_observation["node_count"]
        and status.get("type_native_unique_handle_count")
        == type_native_observation["unique_handle_count"]
        == type_graph_observation["node_count"]
        and isinstance(status.get("type_native_observation_bytes"), int)
        and status["type_native_observation_bytes"]
        == type_native_observation_path.stat().st_size
        and type_native_observation["contracts"][
            "reflection_contract_id"
        ]
        == plan["policy"]["reflection_contract_id"]
        and type_native_observation["contracts"][
            "inventory_contract_id"
        ]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_method_native_complete": method_native_observation is not None
        and status.get("method_native_observation_written") is True
        and status.get("method_native_observation_complete") is True
        and status.get("method_native_metadata_resolution_unique") is True
        and status.get("method_native_slot_layout_unique") is True
        and isinstance(status.get("method_native_slot_byte_offset"), int)
        and status["method_native_slot_byte_offset"] > 0
        and status.get("method_native_type_count")
        == method_native_observation["type_count"]
        == status.get("type_inventory_type_count")
        and status.get("method_native_method_count")
        == method_native_observation["method_count"]
        == member_detail_observation["counts"]["methods"]
        + member_detail_observation["counts"]["constructors"]
        and status.get("method_native_executable_count")
        == method_native_observation["executable_method_count"]
        and status.get("method_native_unique_metadata_count")
        == method_native_observation["method_count"]
        and isinstance(status.get("method_native_observation_bytes"), int)
        and status["method_native_observation_bytes"]
        == method_native_observation_path.stat().st_size
        and method_native_observation["contracts"][
            "reflection_contract_id"
        ]
        == plan["policy"]["reflection_contract_id"]
        and method_native_observation["contracts"][
            "inventory_contract_id"
        ]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_field_native_complete": field_native_observation is not None
        and status.get("field_native_observation_written") is True
        and status.get("field_native_observation_complete") is True
        and status.get("field_native_metadata_resolution_unique") is True
        and status.get("field_native_layout_derived") is True
        and status.get("field_native_type_count")
        == field_native_observation["type_count"]
        == status.get("type_inventory_type_count")
        and status.get("field_native_field_count")
        == field_native_observation["field_count"]
        == member_detail_observation["counts"]["fields"]
        and status.get("field_native_unique_metadata_count")
        == field_native_observation["field_count"]
        and status.get("field_native_metadata_stride")
        == field_native_observation["metadata_stride"]
        and status.get("field_native_offset_dword_index")
        == field_native_observation["offset_dword_index"]
        and status.get("field_native_token_dword_index")
        == field_native_observation["token_dword_index"]
        and isinstance(status.get("field_native_observation_bytes"), int)
        and status["field_native_observation_bytes"]
        == field_native_observation_path.stat().st_size
        and field_native_observation["contracts"][
            "reflection_contract_id"
        ]
        == plan["policy"]["reflection_contract_id"]
        and field_native_observation["contracts"][
            "inventory_contract_id"
        ]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_metadata_usage_complete": metadata_usage_observation is not None
        and status.get("metadata_usage_observation_written") is True
        and status.get("metadata_usage_observation_complete") is True
        and status.get("metadata_usage_layout_derived") is True
        and status.get("metadata_usage_slots_unique") is True
        and status.get("metadata_usage_layout_match_count") == 1
        and status.get("metadata_usage_array_match_count")
        == metadata_usage_observation["matching_array_count"]
        == 1
        and status.get("metadata_usage_count")
        == metadata_usage_observation["usage_count"]
        and isinstance(status.get("metadata_usage_observation_bytes"), int)
        and status["metadata_usage_observation_bytes"]
        == metadata_usage_observation_path.stat().st_size
        and metadata_usage_observation["contracts"]["metadata_sha256"]
        == status.get("metadata_sha256")
        and metadata_usage_observation["contracts"][
            "reflection_contract_id"
        ]
        == plan["policy"]["reflection_contract_id"]
        and metadata_usage_observation["contracts"][
            "inventory_contract_id"
        ]
        == plan["policy"]["runtime_inventory_contract_id"],
        "runtime_type_metadata_usage_complete": (
            type_metadata_usage_observation is not None
            and status.get("type_metadata_usage_observation_written") is True
            and status.get("type_metadata_usage_observation_complete") is True
            and status.get("type_metadata_usage_handles_unique") is True
            and status.get("type_registration_array_match_count")
            == type_metadata_usage_observation["matching_array_count"]
            == 1
            and status.get("type_registration_count")
            == type_metadata_usage_observation["type_count"]
            and status.get("type_metadata_usage_count")
            == type_metadata_usage_observation["type_usage_count"]
            == metadata_usage_observation["usage_kind_counts"].get("1")
            and isinstance(
                status.get("type_metadata_usage_observation_bytes"), int
            )
            and status["type_metadata_usage_observation_bytes"]
            == type_metadata_usage_observation_path.stat().st_size
            and type_metadata_usage_observation["contracts"][
                "metadata_sha256"
            ]
            == status.get("metadata_sha256")
            and type_metadata_usage_observation["contracts"][
                "reflection_contract_id"
            ]
            == plan["policy"]["reflection_contract_id"]
            and type_metadata_usage_observation["contracts"][
                "inventory_contract_id"
            ]
            == plan["policy"]["runtime_inventory_contract_id"]
            and type_metadata_usage_observation["contracts"][
                "type_native_observation_sha256"
            ]
            == sha256_file(type_native_observation_path)
            and type_metadata_usage_observation["contracts"][
                "metadata_usage_observation_sha256"
            ]
            == sha256_file(metadata_usage_observation_path)
        ),
        "reflection_minimum_semantic_operations_resolved": isinstance(
            status.get("reflection_semantic_operation_count"), int
        )
        and status["reflection_semantic_operation_count"]
        >= plan["policy"][
            "reflection_minimum_runtime_semantic_operation_count"
        ],
        "metadata_identity_unique": status.get("candidate_identity_count") == 1,
        "metadata_present": metadata_path.is_file(),
        "metadata_size_matches": metadata_path.is_file()
        and metadata_path.stat().st_size == status.get("metadata_bytes"),
        "metadata_hash_matches": metadata_path.is_file()
        and sha256_file(metadata_path) == status.get("metadata_sha256"),
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_heap_range_absent": status.get("fixed_heap_range_used") is False,
        "network_absent": status.get("network_used") is False,
        "external_runtime_plugin_absent": status.get("external_runtime_plugin_used") is False,
        "target_unchanged": sha256_file(target_path) == plan["target"]["executable_sha256"],
    }
    receipt = {
        "schema": "alpha.runtime-dump-receipt/v1",
        "status": "complete" if all(checks.values()) else "failed",
        "target": plan["target"],
        "checks": checks,
        "runtime": status,
        "outputs": {
            "metadata": file_identity(metadata_path) if metadata_path.is_file() else None,
            "reflection_dispatch": reflection_dispatch["identity"]
            if reflection_dispatch is not None
            else None,
            "runtime_inventory_dispatch": inventory_dispatch["identity"]
            if inventory_dispatch is not None
            else None,
            "runtime_inventory_observation": inventory_observation["identity"]
            if inventory_observation is not None
            else None,
            "runtime_member_observation": member_observation["identity"]
            if member_observation is not None
            else None,
            "runtime_type_identity_observation": type_identity_observation[
                "identity"
            ]
            if type_identity_observation is not None
            else None,
            "runtime_member_detail_observation": member_detail_observation[
                "identity"
            ]
            if member_detail_observation is not None
            else None,
            "runtime_type_graph_observation": type_graph_observation[
                "identity"
            ]
            if type_graph_observation is not None
            else None,
            "runtime_type_native_observation": type_native_observation[
                "identity"
            ]
            if type_native_observation is not None
            else None,
            "runtime_method_native_observation": method_native_observation[
                "identity"
            ]
            if method_native_observation is not None
            else None,
            "runtime_field_native_observation": field_native_observation[
                "identity"
            ]
            if field_native_observation is not None
            else None,
            "runtime_metadata_usage_observation": metadata_usage_observation[
                "identity"
            ]
            if metadata_usage_observation is not None
            else None,
            "runtime_type_metadata_usage_observation": (
                type_metadata_usage_observation["identity"]
                if type_metadata_usage_observation is not None
                else None
            ),
        },
        "raw_runtime_artifacts_owner_only": True,
        "external_runtime_plugin_used": False,
        "network_used": False,
    }
    _private_json(output_dir / "capture-receipt.private.json", receipt)
    public = {
        "schema": "alpha.runtime-dump/v1",
        "status": receipt["status"],
        "target": plan["target"],
        "checks": checks,
        "metadata": {
            "bytes": status.get("metadata_bytes"),
            "sha256": status.get("metadata_sha256"),
            "table_pairs": status.get("metadata_table_pairs"),
        },
        "candidate_count": status.get("candidate_count"),
        "candidate_identity_count": status.get("candidate_identity_count"),
        "reflection_dispatch": {
            "operation_count": reflection_dispatch["operation_count"],
            "method_record_count": reflection_dispatch["method_record_count"],
            "all_operations_uniquely_resolved": True,
        }
        if reflection_dispatch is not None
        else None,
        "runtime_inventory_dispatch": {
            "operation_count": inventory_dispatch["operation_count"],
            "method_record_count": inventory_dispatch["method_record_count"],
            "all_operations_uniquely_resolved": True,
        }
        if inventory_dispatch is not None
        else None,
        "runtime_inventory_observation": {
            "assembly_count": inventory_observation["assembly_count"],
            "type_count": inventory_observation["type_count"],
            "raw_runtime_type_objects_exposed": False,
        }
        if inventory_observation is not None
        else None,
        "runtime_member_observation": {
            "type_count": member_observation["type_count"],
            "counts": member_observation["counts"],
            "raw_runtime_member_objects_exposed": False,
        }
        if member_observation is not None
        else None,
        "runtime_type_identity_observation": {
            "assembly_count": type_identity_observation["assembly_count"],
            "type_count": type_identity_observation["type_count"],
            "relation_count": type_identity_observation["relation_count"],
            "assembly_full_names": [
                assembly["full_name"]
                for assembly in type_identity_observation["assemblies"]
            ],
            "raw_runtime_type_references_exposed": False,
        }
        if type_identity_observation is not None
        else None,
        "runtime_member_detail_observation": {
            "type_count": member_detail_observation["type_count"],
            "counts": member_detail_observation["counts"],
            "parameter_count": member_detail_observation["parameter_count"],
            "method_generic_argument_count": member_detail_observation[
                "method_generic_argument_count"
            ],
            "type_reference_count": member_detail_observation[
                "type_reference_count"
            ],
            "raw_runtime_objects_exposed": False,
        }
        if member_detail_observation is not None
        else None,
        "runtime_type_graph_observation": {
            "root_count": type_graph_observation["root_count"],
            "node_count": type_graph_observation["node_count"],
            "external_node_count": type_graph_observation[
                "external_node_count"
            ],
            "relation_count": type_graph_observation["relation_count"],
            "member_type_reference_count": type_graph_observation[
                "member_type_reference_count"
            ],
            "reference_closure_complete": True,
            "raw_runtime_type_objects_exposed": False,
        }
        if type_graph_observation is not None
        else None,
        "runtime_type_native_observation": {
            "node_count": type_native_observation["node_count"],
            "unique_handle_count": type_native_observation[
                "unique_handle_count"
            ],
            "raw_native_addresses_exposed": False,
        }
        if type_native_observation is not None
        else None,
        "runtime_method_native_observation": {
            "type_count": method_native_observation["type_count"],
            "method_count": method_native_observation["method_count"],
            "executable_method_count": method_native_observation[
                "executable_method_count"
            ],
            "unique_rva_count": method_native_observation[
                "unique_rva_count"
            ],
            "slotted_method_count": method_native_observation[
                "slotted_method_count"
            ],
            "raw_native_addresses_exposed": False,
        }
        if method_native_observation is not None
        else None,
        "runtime_field_native_observation": {
            "type_count": field_native_observation["type_count"],
            "field_count": field_native_observation["field_count"],
            "static_field_count": field_native_observation[
                "static_field_count"
            ],
            "literal_field_count": field_native_observation[
                "literal_field_count"
            ],
            "raw_native_addresses_exposed": False,
        }
        if field_native_observation is not None
        else None,
        "runtime_metadata_usage_observation": {
            "usage_count": metadata_usage_observation["usage_count"],
            "usage_kind_counts": metadata_usage_observation[
                "usage_kind_counts"
            ],
            "matching_array_count": metadata_usage_observation[
                "matching_array_count"
            ],
            "fixed_address_seed_used": False,
            "raw_native_addresses_exposed": False,
        }
        if metadata_usage_observation is not None
        else None,
        "runtime_type_metadata_usage_observation": {
            "type_count": type_metadata_usage_observation["type_count"],
            "type_usage_count": type_metadata_usage_observation[
                "type_usage_count"
            ],
            "matching_array_count": type_metadata_usage_observation[
                "matching_array_count"
            ],
            "fixed_address_seed_used": False,
            "fixed_type_count_seed_used": False,
            "raw_native_addresses_exposed": False,
        }
        if type_metadata_usage_observation is not None
        else None,
        "raw_runtime_artifacts_owner_only": True,
        "external_runtime_plugin_used": False,
        "network_used": False,
    }
    atomic_write_json(output_dir / "capture.json", public)
    return public


def _bind_pointer_index(
    *,
    snapshot_path: Path,
    snapshot_sha256: str | None,
    envelope: dict[str, int] | None,
    output_dir: Path,
) -> dict[str, Any] | None:
    from alpha.h04 import (
        POINTER_INDEX_BINDING_SCHEMA,
        POINTER_INDEX_GROUP_BYTES,
        POINTER_INDEX_HEADER,
        POINTER_INDEX_MAGIC,
        POINTER_INDEX_MAXIMUM,
        POINTER_INDEX_MINIMUM,
        POINTER_INDEX_TABLE_BITS,
        POINTER_INDEX_TABLE_SHAPE,
        POINTER_INDEX_VERSION,
    )

    index_path = output_dir / "runtime-pointer-index.private.bin"
    binding_path = output_dir / "runtime-pointer-index.private.json"
    if not index_path.exists():
        return None
    if not _seal_runtime_output(index_path):
        return None
    if envelope is None or snapshot_sha256 is None:
        raise AcquisitionError("pointer index exists without a valid snapshot")
    table_bytes = POINTER_INDEX_TABLE_BITS // 8
    with index_path.open("rb") as source:
        raw_header = source.read(POINTER_INDEX_HEADER.size)
    if len(raw_header) != POINTER_INDEX_HEADER.size:
        raise AcquisitionError("runtime pointer index header is truncated")
    (
        magic,
        version,
        stride,
        table_bits,
        shape,
        group_bytes,
        minimum,
        maximum,
        record_count,
        group_count,
        snapshot_bytes,
        reserved0,
        reserved1,
        reserved2,
    ) = POINTER_INDEX_HEADER.unpack_from(raw_header, 0)
    if (
        magic != POINTER_INDEX_MAGIC
        or version != POINTER_INDEX_VERSION
        or stride != 8
        or table_bits != POINTER_INDEX_TABLE_BITS
        or shape != POINTER_INDEX_TABLE_SHAPE
        or group_bytes != POINTER_INDEX_GROUP_BYTES
        or minimum != POINTER_INDEX_MINIMUM
        or maximum != POINTER_INDEX_MAXIMUM
        or reserved0
        or reserved1
        or reserved2
    ):
        raise AcquisitionError("runtime pointer index header is invalid")
    identity = file_identity(index_path)
    if (
        record_count != envelope["record_count"]
        or snapshot_bytes != envelope["bytes"]
        or identity["bytes"]
        != POINTER_INDEX_HEADER.size + group_count * table_bytes
    ):
        raise AcquisitionError("runtime pointer index does not describe the snapshot")
    binding = {
        "schema": POINTER_INDEX_BINDING_SCHEMA,
        "status": "complete",
        "snapshot": {"sha256": snapshot_sha256, "bytes": snapshot_bytes},
        "index": {"sha256": identity["sha256"], "bytes": identity["bytes"]},
        "geometry": {
            "stride": stride,
            "table_bits": table_bits,
            "table_shape": shape,
            "group_bytes": group_bytes,
            "minimum": minimum,
            "maximum": maximum,
            "record_count": record_count,
            "group_count": group_count,
        },
        "owner_only": True,
    }
    _private_json(binding_path, binding)
    return {
        "index": identity,
        "binding": file_identity(binding_path),
        "group_count": group_count,
        "record_count": record_count,
    }


def _read_official_runtime_attestation(
    path: Path | None,
    *,
    executable_sha256: str,
    process_id: int,
) -> tuple[dict[str, bool], dict[str, Any] | None]:
    checks = {
        "attestation_present": path is not None,
        "schema": False,
        "complete": False,
        "target_hash_matches": False,
        "process_id_matches": False,
        "fresh_process_observed": False,
        "official_runtime_observed": False,
        "local_route_absent": False,
        "official_traffic_unmodified": False,
    }
    if path is None:
        return checks, None
    path = path.expanduser().resolve()
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AcquisitionError("official runtime attestation is unreadable") from error
    if not isinstance(value, dict):
        raise AcquisitionError("official runtime attestation must be a JSON object")
    checks.update(
        {
            "schema": value.get("schema") == "alpha.official-runtime-attestation/v1",
            "complete": value.get("status") == "complete",
            "target_hash_matches": value.get("target_executable_sha256")
            == executable_sha256,
            "process_id_matches": value.get("process_id") == process_id,
            "fresh_process_observed": value.get("fresh_process_observed") is True,
            "official_runtime_observed": value.get("official_runtime_observed") is True,
            "local_route_absent": value.get("local_route_used") is False,
            "official_traffic_unmodified": value.get("official_traffic_unmodified") is True,
        }
    )
    return checks, value


def prepare_runtime_snapshot(
    *,
    game_dir: Path,
    executable: Path | None,
    output_dir: Path,
    compiler: Path | None = None,
    reachable_heap_limit_mib: int = 0,
) -> dict[str, Any]:

    reachable_heap_limit_bytes = _reachable_heap_limit_bytes(reachable_heap_limit_mib)
    output_dir = _owner_directory(output_dir)
    target, _client = collect_target(
        CollectionContext(game_dir=game_dir, executable=executable)
    )
    target_path = Path(target.executable_path)
    if sha256_file(target_path) != target.executable_sha256:
        raise AcquisitionError("target executable changed during snapshot preparation")

    from alpha.p14 import discover_reflection_bootstrap
    from alpha.c04 import discover_runtime_resolver

    resolver_path = output_dir / "memory-runtime-resolver.private.json"
    resolver = discover_runtime_resolver(binary=target_path)
    _private_json(resolver_path, resolver)
    bootstrap_path = output_dir / "memory-reflection-bootstrap.private.json"
    bootstrap = discover_reflection_bootstrap(
        binary=target_path,
        resolver_model=resolver_path,
    )
    _private_json(bootstrap_path, bootstrap)
    if (
        bootstrap["binary"]["sha256"] != target.executable_sha256
        or bootstrap["binary"]["size_of_image"] <= 0
        or bootstrap["state_slot_rva"] <= 0
        or bootstrap["type_resolver_helper_rva"] <= 0
    ):
        raise AcquisitionError("runtime snapshot resolver preflight is incomplete")
    required_owner_pairs = _required_runtime_owner_pairs()
    if not required_owner_pairs:
        raise AcquisitionError("runtime snapshot owner-root contract is empty")

    source_dir = _owner_directory(output_dir / "build-memory")
    snapshot_path = output_dir / "runtime-memory.private.bin"
    status_path = output_dir / "memory-status.private.json"
    owner_roots_path = output_dir / "runtime-owner-roots.private.json"
    pointer_index_path = output_dir / "runtime-pointer-index.private.bin"
    pointer_binding_path = output_dir / "runtime-pointer-index.private.json"
    source_path = source_dir / "runtime-snapshot.c"
    injector_source_path = source_dir / "runtime-snapshot-injector.c"
    injector_path = source_dir / "alpha-runtime-snapshot-injector.exe"
    for stale in (
        snapshot_path, status_path, owner_roots_path, pointer_index_path,
        pointer_binding_path,
    ):
        stale.unlink(missing_ok=True)
    _private_text(
        source_path,
        runtime_snapshot_source(
            expected_executable_sha256=target.executable_sha256,
            snapshot_path=snapshot_path,
            status_path=status_path,
            owner_roots_path=owner_roots_path,
            pointer_index_path=pointer_index_path,
            type_resolver_state_slot_rva=bootstrap["state_slot_rva"],
            type_resolver_helper_rva=bootstrap["type_resolver_helper_rva"],
            required_owner_pairs=required_owner_pairs,
            reachable_heap_limit_mib=reachable_heap_limit_mib,
        ),
    )
    _private_text(injector_source_path, runtime_injector_source())
    source_sha256 = file_identity(source_path)["sha256"]
    collector_path = source_dir / (
        f"alpha-runtime-snapshot-{source_sha256[:16]}.dll"
    )
    selected_compiler = _compiler(compiler)
    _build(
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
            str(collector_path),
            "-lbcrypt",
        ],
        label="runtime memory collector",
    )
    _build(
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
        label="runtime memory injector",
    )
    for artifact in (collector_path, injector_path):
        if not artifact.is_file() or not artifact.stat().st_size:
            raise AcquisitionError(f"runtime memory build did not produce {artifact.name}")
        artifact.chmod(0o600)
    plan = {
        "schema": SNAPSHOT_PLAN_SCHEMA,
        "status": "prepared",
        "target": target.public(),
        "collector": file_identity(collector_path),
        "injector": file_identity(injector_path),
        "outputs": {
            "snapshot": str(snapshot_path),
            "status": str(status_path),
            "owner_roots": str(owner_roots_path),
            "pointer_index": str(pointer_index_path),
            "pointer_index_binding": str(pointer_binding_path),
            "runtime_resolver_model": str(resolver_path),
            "reflection_bootstrap_model": str(bootstrap_path),
        },
        "resolver_binding": {
            "state_slot_rva": bootstrap["state_slot_rva"],
            "type_resolver_helper_rva": bootstrap["type_resolver_helper_rva"],
            "runtime_resolver_model_sha256": file_identity(resolver_path)["sha256"],
            "reflection_bootstrap_model_sha256": file_identity(bootstrap_path)[
                "sha256"
            ],
        },
        "policy": {
            "fresh_runtime_required": True,
            "official_runtime_required_for_acceptance": True,
            "local_route_forbidden_for_acceptance": True,
            "current_executable_sha256_embedded": True,
            "readable_committed_regions": True,
            "main_image_only": False,
            "executable_regions_included": True,
            "reachable_heap_required": True,
            "capture_scope": "main-image-and-private-heap-fixed-point-from-observed-roots",
            "reachable_heap_followup_required": False,
            "reachable_heap_depth": "fixed-point",
            "reachable_depth2_minimum_region_support": 0,
            "reachable_minimum_region_support": 0,
            "metadata_arena_lossless_structural_depth": True,
            "collector_basename_bound_to_generated_source": True,
            "reachable_structural_type_cache_roots_required": True,
            "reachable_resolver_owner_roots_required": True,
            "reachable_owner_root_count": len(required_owner_pairs),
            "owner_root_manifest_required": True,
            "resolver_binding_derived_from_current_executable": True,
            "reachable_region_size_limit": 0,
            "reachable_total_size_limit": reachable_heap_limit_bytes,
            "reachable_bounds_enforced": bool(reachable_heap_limit_bytes),
            "reachable_overflow_rejected": True,
            "fixed_address_used": False,
            "fixed_rva_used": False,
            "fixed_heap_range_used": False,
            "network_used": False,
            "external_runtime_plugin_used": False,
            "saved_dump_used_for_generation": False,
            "raw_snapshot_owner_only": True,
        },
    }
    _private_json(output_dir / "memory-plan.private.json", plan)
    return {
        "schema": SNAPSHOT_PLAN_SCHEMA,
        "status": "prepared",
        "target": target.public(),
        "policy": plan["policy"],
    }


def capture_runtime_snapshot(
    *,
    game_dir: Path,
    executable: Path | None,
    output_dir: Path,
    wine: Path,
    wineprefix: Path,
    compiler: Path | None = None,
    timeout: float | None = None,
    official_runtime_attestation: Path | None = None,
    reachable_heap_limit_mib: int = 0,
    process_check: Callable[[], None] | None = None,
) -> dict[str, Any]:

    output_dir = _owner_directory(output_dir)
    prepare_runtime_snapshot(
        game_dir=game_dir,
        executable=executable,
        output_dir=output_dir,
        compiler=compiler,
        reachable_heap_limit_mib=reachable_heap_limit_mib,
    )
    plan_path = output_dir / "memory-plan.private.json"
    plan = json.loads(plan_path.read_text(encoding="utf-8"))
    target_path = Path(plan["target"]["executable_path"])
    if sha256_file(target_path) != plan["target"]["executable_sha256"]:
        raise AcquisitionError("target executable changed after snapshot preparation")
    wine = wine.expanduser().resolve()
    wineprefix = wineprefix.expanduser().resolve()
    if not wine.is_file() or not wineprefix.is_dir():
        raise DependencyUnavailable("selected Wine binary or prefix is unavailable")
    collector = Path(plan["collector"]["path"]).expanduser().resolve()
    injector = Path(plan["injector"]["path"]).expanduser().resolve()
    expected_build_root = (output_dir / "build-memory").resolve()
    if (
        collector.parent != expected_build_root
        or injector.parent != expected_build_root
        or not collector.name.startswith("alpha-runtime-snapshot-")
        or collector.suffix.casefold() != ".dll"
        or injector.name != "alpha-runtime-snapshot-injector.exe"
    ):
        raise AcquisitionError("runtime memory build artifact boundary is invalid")
    environment = os.environ.copy()
    environment["WINEPREFIX"] = str(wineprefix)
    environment["WINEDEBUG"] = "-all"
    try:
        injected = subprocess.run(
            _host_run(str(wine), injector, collector, target_path.name),
            env=environment,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="replace",
            timeout=90,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError("ALPHA v2 runtime memory injector could not run") from error
    _private_text(
        output_dir / "memory-injector.private.log",
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
            f"ALPHA v2 runtime memory injection failed ({injected.returncode})"
        )
    status_path = output_dir / "memory-status.private.json"
    deadline = None if timeout is None else time.monotonic() + max(1.0, timeout)
    status: dict[str, Any] | None = None
    next_process_check = time.monotonic()
    while deadline is None or time.monotonic() < deadline:
        if status_path.is_file():
            try:
                value = json.loads(status_path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                value = None
            if isinstance(value, dict):
                status = value
                break
        if process_check is not None and time.monotonic() >= next_process_check:
            process_check()
            next_process_check = time.monotonic() + 30.0
        time.sleep(0.25)
    if status is None:
        raise AcquisitionError("ALPHA v2 runtime memory capture timed out")
    _seal_runtime_output(status_path)


    _seal_runtime_output(output_dir / "runtime-owner-roots.private.json")
    if status.get("status") != "complete":
        raise AcquisitionError(
            "ALPHA v2 runtime memory capture failed "
            f"(status={status.get('status')}, "
            f"reachable_selection_overflow={status.get('reachable_selection_overflow')}, "
            f"time_budget_exhausted={status.get('time_budget_exhausted')}, "
            f"reachable_total_size_limit={status.get('reachable_total_size_limit')})"
        )

    snapshot_path = output_dir / "runtime-memory.private.bin"
    envelope = _inspect_snapshot(snapshot_path) if snapshot_path.is_file() else None
    _seal_runtime_output(snapshot_path)
    snapshot_sha256 = sha256_file(snapshot_path) if snapshot_path.is_file() else None
    pointer_index = _bind_pointer_index(
        snapshot_path=snapshot_path,
        snapshot_sha256=snapshot_sha256,
        envelope=envelope,
        output_dir=output_dir,
    )
    owner_roots_path = output_dir / "runtime-owner-roots.private.json"
    owner_roots = None
    if _seal_runtime_output(owner_roots_path):
        if envelope is None:
            raise AcquisitionError(
                "runtime owner-root manifest exists without a valid snapshot"
            )
        owner_roots = load_runtime_owner_roots(
            owner_roots_path,
            executable_sha256=plan["target"]["executable_sha256"],
            image_base=envelope["image_base"],
            image_bytes=envelope["image_bytes"],
            required_owner_pairs=_required_runtime_owner_pairs(),
            state_slot_rva=plan["resolver_binding"]["state_slot_rva"],
            resolver_helper_rva=plan["resolver_binding"][
                "type_resolver_helper_rva"
            ],
        )
    process_id = status.get("process_id")
    attestation_checks, attestation = _read_official_runtime_attestation(
        official_runtime_attestation,
        executable_sha256=plan["target"]["executable_sha256"],
        process_id=process_id if isinstance(process_id, int) else -1,
    )
    capture_checks = {
        "schema": status.get("schema") == SNAPSHOT_SCHEMA,
        "complete": status.get("status") == "complete",
        "executable_hash_matches": status.get("executable_hash_matches") is True,
        "expected_hash_matches_plan": status.get("expected_executable_sha256")
        == plan["target"]["executable_sha256"],
        "observed_hash_matches_plan": status.get("observed_executable_sha256")
        == plan["target"]["executable_sha256"],
        "snapshot_present": envelope is not None,
        "snapshot_hash_matches": snapshot_sha256 == status.get("snapshot_sha256"),
        "record_count_matches": envelope is not None
        and envelope["record_count"] == status.get("record_count"),
        "region_count_matches": envelope is not None
        and envelope["region_count"] == status.get("region_count"),
        "captured_bytes_match": envelope is not None
        and envelope["captured_bytes"] == status.get("captured_bytes"),
        "readable_committed_regions": status.get("readable_committed_regions") is True,
        "reachable_capture_window_atomic": (
            status.get("reachable_capture_failed") is False
            and status.get("reachable_capture_rejected_window_count") == 0
            and status.get("reachable_captured_window_count")
            == status.get("reachable_candidate_region_count")
        ),
        "main_image_plus_reachable_heap": status.get("main_image_only") is False
        and status.get("reachable_heap_included") is True
        and status.get("reachable_heap_selection_complete") is True
        and status.get("reachable_all_candidates_selected") is True
        and status.get("reachable_heap_captured_bytes")
        == status.get("reachable_heap_bytes")
        and isinstance(status.get("reachable_root_data_region_count"), int)
        and status["reachable_root_data_region_count"] > 0
        and isinstance(
            status.get("reachable_structural_type_cache_site_count"), int
        )
        and status["reachable_structural_type_cache_site_count"] > 0
        and isinstance(
            status.get("reachable_structural_initialized_class_count"), int
        )
        and status["reachable_structural_initialized_class_count"] > 0
        and isinstance(
            status.get("reachable_structural_root_window_count"), int
        )
        and status["reachable_structural_root_window_count"] > 0
        and isinstance(status.get("reachable_root_pointer_count"), int)
        and status["reachable_root_pointer_count"] > 0
        and isinstance(status.get("reachable_candidate_region_count"), int)
        and status["reachable_candidate_region_count"]
        == status.get("reachable_heap_region_count", 0)
        and isinstance(status.get("reachable_heap_region_count"), int)
        and status["reachable_heap_region_count"] > 0
        and isinstance(status.get("reachable_heap_bytes"), int)
        and status["reachable_heap_bytes"] > 0
        and (not plan["policy"]["reachable_total_size_limit"]
             or status["reachable_heap_bytes"]
             <= plan["policy"]["reachable_total_size_limit"])
        and isinstance(status.get("reachable_depth"), int)
        and status["reachable_depth"] >= 1
        and status.get("reachable_depth2_minimum_region_support")
        == plan["policy"]["reachable_depth2_minimum_region_support"]
        and status.get("reachable_minimum_region_support")
        == plan["policy"]["reachable_minimum_region_support"]
        and status.get("reachable_region_size_limit")
        == plan["policy"]["reachable_region_size_limit"]
        and isinstance(status.get("reachable_window_bytes"), int)
        and status["reachable_window_bytes"] >= 4096
        and status["reachable_window_bytes"] & (status["reachable_window_bytes"] - 1) == 0
        and status.get("reachable_total_size_limit")
        == plan["policy"]["reachable_total_size_limit"]
        and status.get("reachable_selection_overflow") is False
        and status.get("reachable_bounds_enforced")
        is plan["policy"]["reachable_bounds_enforced"],
        "resolver_owner_roots_complete": owner_roots is not None
        and owner_roots["owner_count"]
        == plan["policy"]["reachable_owner_root_count"]
        and status.get("reachable_resolver_owner_root_count")
        == plan["policy"]["reachable_owner_root_count"]
        and status.get("reachable_resolver_owner_roots_complete") is True
        and status.get("reachable_owner_root_manifest_written") is True,
        "executable_regions_included": status.get("executable_regions_included") is True,
        "fixed_address_absent": status.get("fixed_address_used") is False,
        "fixed_rva_seed_absent": plan["policy"].get("fixed_rva_used") is False,
        "fixed_heap_range_absent": status.get("fixed_heap_range_used") is False,
        "network_absent": status.get("network_used") is False,
        "external_runtime_plugin_absent": status.get("external_runtime_plugin_used")
        is False,
        "target_unchanged": sha256_file(target_path)
        == plan["target"]["executable_sha256"],
    }
    capture_valid = all(capture_checks.values())
    official_valid = all(attestation_checks.values())
    result_status = (
        "complete"
        if capture_valid and official_valid
        else "captured-unattested"
        if capture_valid
        else "failed"
    )
    receipt = {
        "schema": "alpha.runtime-memory-receipt/v1",
        "status": result_status,
        "scope": plan["policy"]["capture_scope"],
        "target": plan["target"],
        "capture_checks": capture_checks,
        "official_runtime_checks": attestation_checks,
        "runtime": status,
        "envelope": envelope,
        "official_runtime_attestation": attestation,
        "snapshot": file_identity(snapshot_path) if snapshot_path.is_file() else None,
        "pointer_index": pointer_index,
        "owner_roots": {
            "identity": owner_roots["identity"],
            "owner_count": owner_roots["owner_count"],
            "checks": owner_roots["checks"],
        }
        if owner_roots is not None
        else None,
        "raw_runtime_artifacts_owner_only": True,
    }
    _private_json(output_dir / "memory-receipt.private.json", receipt)
    public = {
        "schema": "alpha.runtime-memory/v1",
        "status": result_status,
        "scope": plan["policy"]["capture_scope"],
        "target": plan["target"],
        "capture_checks": capture_checks,
        "official_runtime_checks": attestation_checks,
        "snapshot": {
            "bytes": envelope["bytes"] if envelope else None,
            "captured_bytes": envelope["captured_bytes"] if envelope else None,
            "record_count": envelope["record_count"] if envelope else None,
            "region_count": envelope["region_count"] if envelope else None,
            "sha256": snapshot_sha256,
        },
        "owner_roots": {
            "owner_count": owner_roots["owner_count"] if owner_roots else 0,
            "complete": owner_roots is not None,
            "raw_pointers_exposed": False,
        },
        "raw_runtime_artifacts_owner_only": True,
        "external_runtime_plugin_used": False,
        "network_used": False,
    }
    atomic_write_json(output_dir / "memory-capture.json", public)
    return public
