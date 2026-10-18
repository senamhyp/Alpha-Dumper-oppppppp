import hashlib
import json
import os
import shutil
import struct
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError
from alpha.h02 import atomic_write_json, file_identity


METADATA_MAGIC = 0xFAB11BAF
COMPLETE_METADATA_SCHEMA = "alpha.complete-global-metadata/v1"


_V24_2_TABLES = (
    "string_literals",
    "string_literal_data",
    "metadata_strings",
    "events",
    "properties",
    "methods",
    "parameter_default_values",
    "field_default_values",
    "field_and_parameter_default_value_data",
    "field_marshaled_sizes",
    "parameters",
    "fields",
    "generic_parameters",
    "generic_parameter_constraints",
    "generic_containers",
    "nested_types",
    "interfaces",
    "vtable_methods",
    "interface_offsets",
    "type_definitions",
    "images",
    "assemblies",
    "metadata_usage_lists",
    "metadata_usage_pairs",
    "field_refs",
    "referenced_assemblies",
    "custom_attribute_type_ranges",
    "custom_attribute_types",
    "unresolved_virtual_call_parameter_types",
    "unresolved_virtual_call_parameter_ranges",
    "windows_runtime_type_names",
    "exported_type_definitions",
)

_V29_TABLES = (
    "string_literals",
    "string_literal_data",
    "metadata_strings",
    "events",
    "properties",
    "methods",
    "parameter_default_values",
    "field_default_values",
    "field_and_parameter_default_value_data",
    "field_marshaled_sizes",
    "parameters",
    "fields",
    "generic_parameters",
    "generic_parameter_constraints",
    "generic_containers",
    "nested_types",
    "interfaces",
    "vtable_methods",
    "interface_offsets",
    "type_definitions",
    "images",
    "assemblies",
    "field_refs",
    "referenced_assemblies",
    "custom_attribute_data",
    "custom_attribute_data_ranges",
    "unresolved_virtual_call_parameter_types",
    "unresolved_virtual_call_parameter_ranges",
    "windows_runtime_type_names",
    "windows_runtime_strings",
    "exported_type_definitions",
)


@dataclass(frozen=True)
class MetadataTable:
    index: int
    name: str
    offset: int
    size: int

    @property
    def end(self) -> int:
        return self.offset + self.size


@dataclass(frozen=True)
class MetadataDirectory:
    version: int
    layout: str
    header_size: int
    tables: tuple[MetadataTable, ...]
    data: bytes

    def table(self, name: str) -> MetadataTable:
        matches = [table for table in self.tables if table.name == name]
        if len(matches) != 1:
            raise AcquisitionError(f"global metadata table is unavailable: {name}")
        return matches[0]

    def bytes_for(self, name: str) -> bytes:
        table = self.table(name)
        return self.data[table.offset : table.end]


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _table_names(version: int, pair_count: int, header_size: int) -> tuple[str, ...]:
    if version == 24 and pair_count == len(_V24_2_TABLES) and header_size == 264:
        return _V24_2_TABLES
    if version >= 29 and pair_count == len(_V29_TABLES):
        return _V29_TABLES
    return tuple(f"unknown_table_{index:02d}" for index in range(pair_count))


def parse_global_metadata(data: bytes, *, require_structured_layout: bool = True) -> MetadataDirectory:
    if len(data) < 16:
        raise AcquisitionError("global metadata is truncated")
    magic, version, first_table_offset = struct.unpack_from("<III", data, 0)
    if magic != METADATA_MAGIC:
        raise AcquisitionError("global metadata magic is invalid")
    if not 16 <= version <= 1000:
        raise AcquisitionError("global metadata version is invalid")
    if (
        first_table_offset < 16
        or first_table_offset > min(len(data), 0x4000)
        or (first_table_offset - 8) % 8
    ):
        raise AcquisitionError("global metadata header size is invalid")
    pair_count = (first_table_offset - 8) // 8
    names = _table_names(version, pair_count, first_table_offset)
    structured = not names[0].startswith("unknown_table_")
    if require_structured_layout and not structured:
        raise AcquisitionError(
            "global metadata header layout is not structurally supported "
            f"(version={version}, header={first_table_offset}, pairs={pair_count})"
        )
    tables: list[MetadataTable] = []
    occupied: list[tuple[int, int, str]] = []
    for index, name in enumerate(names):
        offset, size = struct.unpack_from("<II", data, 8 + index * 8)
        if size:
            if (
                offset < first_table_offset
                or offset & 3
                or offset > len(data)
                or size > len(data) - offset
            ):
                raise AcquisitionError(f"global metadata table is out of bounds: {name}")
            occupied.append((offset, offset + size, name))
        elif offset > len(data):
            raise AcquisitionError(f"empty global metadata table offset is invalid: {name}")
        tables.append(MetadataTable(index, name, offset, size))
    occupied.sort()
    for previous, current in zip(occupied, occupied[1:]):
        if current[0] < previous[1]:
            raise AcquisitionError(
                "global metadata tables overlap: " f"{previous[2]} and {current[2]}"
            )
    return MetadataDirectory(
        version=version,
        layout=(
            "il2cpp-v24.2-plus-264-byte-header"
            if names == _V24_2_TABLES
            else "il2cpp-v29-plus-attribute-data-header"
            if names == _V29_TABLES
            else "unknown-self-describing-layout"
        ),
        header_size=first_table_offset,
        tables=tuple(tables),
        data=data,
    )


def _records(data: bytes, record: struct.Struct, label: str) -> list[tuple[int, ...]]:
    if len(data) % record.size:
        raise AcquisitionError(f"{label} table has a partial record")
    return [record.unpack_from(data, offset) for offset in range(0, len(data), record.size)]


def _write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    try:
        with temporary.open("wb") as output:
            output.write(data)
            output.flush()
            os.fsync(output.fileno())
        temporary.chmod(0o600)
        os.replace(temporary, path)
        path.chmod(0o600)
    finally:
        temporary.unlink(missing_ok=True)


def _copy_raw(source: Path, destination: Path) -> None:
    if source == destination:
        destination.chmod(0o600)
        return
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_name(f".{destination.name}.{os.getpid()}.tmp")
    try:
        with source.open("rb") as input_file, temporary.open("wb") as output_file:
            shutil.copyfileobj(input_file, output_file, length=1024 * 1024)
            output_file.flush()
            os.fsync(output_file.fileno())
        temporary.chmod(0o600)
        os.replace(temporary, destination)
        destination.chmod(0o600)
    finally:
        temporary.unlink(missing_ok=True)


def _range_accounting(directory: MetadataDirectory) -> dict[str, Any]:
    occupied = sorted(
        (table.offset, table.end, table.name)
        for table in directory.tables
        if table.size
    )
    cursor = directory.header_size
    gaps: list[dict[str, Any]] = []
    for start, end, _name in occupied:
        if start > cursor:
            value = directory.data[cursor:start]
            gaps.append(
                {
                    "offset": cursor,
                    "size": len(value),
                    "sha256": _sha256(value),
                    "nonzero_byte_count": sum(byte != 0 for byte in value),
                }
            )
        cursor = max(cursor, end)
    if cursor < len(directory.data):
        value = directory.data[cursor:]
        gaps.append(
            {
                "offset": cursor,
                "size": len(value),
                "sha256": _sha256(value),
                "nonzero_byte_count": sum(byte != 0 for byte in value),
            }
        )
    return {
        "header_bytes": directory.header_size,
        "table_bytes": sum(table.size for table in directory.tables),
        "unassigned_bytes": sum(gap["size"] for gap in gaps),
        "unassigned_ranges": gaps,
        "raw_file_bytes_accounted": (
            directory.header_size
            + sum(table.size for table in directory.tables)
            + sum(gap["size"] for gap in gaps)
            == len(directory.data)
        ),
    }


def write_complete_metadata_artifacts(
    *, metadata: Path, output_dir: Path, executable_sha256: str | None = None
) -> dict[str, Any]:
    metadata = metadata.expanduser().resolve()
    output_dir = output_dir.expanduser().resolve()
    if not metadata.is_file() or metadata.is_symlink():
        raise AcquisitionError("captured global metadata is unavailable")
    output_dir.mkdir(parents=True, mode=0o700, exist_ok=True)
    output_dir.chmod(0o700)
    data = metadata.read_bytes()
    directory = parse_global_metadata(data)

    raw_output = output_dir / "global-metadata.dat"
    _copy_raw(metadata, raw_output)
    if raw_output.read_bytes() != data:
        raise AcquisitionError("published global metadata is not byte-for-byte identical")

    default_record = struct.Struct("<iii")
    parameter_defaults = _records(
        directory.bytes_for("parameter_default_values"),
        default_record,
        "parameter default",
    )
    field_defaults = _records(
        directory.bytes_for("field_default_values"), default_record, "field default"
    )
    default_data = directory.bytes_for("field_and_parameter_default_value_data")
    default_data_path = output_dir / "field-and-parameter-default-value-data.bin"
    _write_bytes(default_data_path, default_data)
    parameter_payload = {
        "schema": "alpha.parameter-default-values/v1",
        "encoding": "Il2CppParameterDefaultValue[index,type_index,data_index]",
        "record_size": default_record.size,
        "record_count": len(parameter_defaults),
        "records": [
            {"parameter_index": index, "type_index": type_index, "data_index": data_index}
            for index, type_index, data_index in parameter_defaults
        ],
        "shared_data": file_identity(default_data_path),
        "all_table_bytes_projected": True,
    }
    field_payload = {
        "schema": "alpha.field-default-values/v1",
        "encoding": "Il2CppFieldDefaultValue[index,type_index,data_index]",
        "record_size": default_record.size,
        "record_count": len(field_defaults),
        "records": [
            {"field_index": index, "type_index": type_index, "data_index": data_index}
            for index, type_index, data_index in field_defaults
        ],
        "shared_data": file_identity(default_data_path),
        "all_table_bytes_projected": True,
    }
    parameter_path = output_dir / "parameterdefaults.json"
    field_path = output_dir / "fielddefaults.json"
    atomic_write_json(parameter_path, parameter_payload)
    atomic_write_json(field_path, field_payload)

    if directory.version == 24:
        range_record = struct.Struct("<Iii")
        ranges = _records(
            directory.bytes_for("custom_attribute_type_ranges"),
            range_record,
            "custom attribute type range",
        )
        type_bytes = directory.bytes_for("custom_attribute_types")
        type_values = _records(type_bytes, struct.Struct("<i"), "custom attribute type")
        attribute_binary = output_dir / "custom-attribute-types.bin"
        _write_bytes(attribute_binary, type_bytes)
        attributes: dict[str, Any] = {
            "schema": "alpha.custom-attributes/v1",
            "metadata_encoding": "v21-v27.2-type-ranges",
            "serialized_attribute_blob_present_in_this_metadata_version": False,
            "range_record_size": range_record.size,
            "range_count": len(ranges),
            "type_index_count": len(type_values),
            "ranges": [
                {"token": token, "start": start, "count": count}
                for token, start, count in ranges
            ],
            "type_indices": [value[0] for value in type_values],
            "raw_type_index_table": file_identity(attribute_binary),
            "all_version_applicable_attribute_bytes_projected": True,
        }
    else:
        range_record = struct.Struct("<II")
        ranges = _records(
            directory.bytes_for("custom_attribute_data_ranges"),
            range_record,
            "custom attribute data range",
        )
        attribute_data = directory.bytes_for("custom_attribute_data")
        attribute_binary = output_dir / "custom-attribute-data.bin"
        _write_bytes(attribute_binary, attribute_data)
        attributes = {
            "schema": "alpha.custom-attributes/v1",
            "metadata_encoding": "v29-plus-serialized-data",
            "serialized_attribute_blob_present_in_this_metadata_version": True,
            "range_record_size": range_record.size,
            "range_count": len(ranges),
            "ranges": [
                {"token": token, "start_offset": start}
                for token, start in ranges
            ],
            "raw_attribute_data": file_identity(attribute_binary),
            "all_version_applicable_attribute_bytes_projected": True,
        }
    attributes_path = output_dir / "customattributes.json"
    atomic_write_json(attributes_path, attributes)

    accounting = _range_accounting(directory)
    manifest = {
        "schema": COMPLETE_METADATA_SCHEMA,
        "status": "complete",
        "target": {"executable_sha256": executable_sha256},
        "metadata": {
            "version": directory.version,
            "layout": directory.layout,
            "header_size": directory.header_size,
            "pair_count": len(directory.tables),
            "raw": file_identity(raw_output),
            "source_sha256": _sha256(data),
            "byte_for_byte_source_preserved": _sha256(data)
            == file_identity(raw_output)["sha256"],
        },
        "tables": [
            {
                "index": table.index,
                "name": table.name,
                "offset": table.offset,
                "size": table.size,
                "sha256": _sha256(directory.data[table.offset : table.end]),
            }
            for table in directory.tables
        ],
        "accounting": accounting,
        "artifacts": {
            "parameter_defaults": file_identity(parameter_path),
            "field_defaults": file_identity(field_path),
            "default_value_data": file_identity(default_data_path),
            "custom_attributes": file_identity(attributes_path),
            "custom_attribute_binary": file_identity(attribute_binary),
        },
        "checks": {
            "unity_magic_valid": True,
            "header_shape_understood": True,
            "all_tables_in_bounds": True,
            "all_tables_non_overlapping": True,
            "all_raw_file_bytes_accounted": accounting["raw_file_bytes_accounted"],
            "raw_metadata_byte_for_byte_preserved": _sha256(data)
            == file_identity(raw_output)["sha256"],
            "all_parameter_default_records_projected": True,
            "all_field_default_records_projected": True,
            "all_version_applicable_custom_attribute_bytes_projected": True,
        },
    }
    if not all(manifest["checks"].values()):
        raise AcquisitionError("complete global metadata checks did not all pass")
    manifest_path = output_dir / "global-metadata.manifest.json"
    atomic_write_json(manifest_path, manifest)
    return {**manifest, "manifest": file_identity(manifest_path)}
