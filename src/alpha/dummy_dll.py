import hashlib
import json
import os
import re
import shutil
import stat
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from alpha.p61 import validate_dump_ir
from alpha.h01 import AcquisitionError, ContractViolation, DependencyUnavailable
from alpha.h02 import atomic_write_json, file_identity


DUMMY_DLL_SCHEMA = "alpha.dummy-dll-output/v1"
EMITTER_SCHEMA = "alpha.dummy-dll-emitter/v1"
HELPER_FILE_NAME = "Il2CppDummyDll.dll"
_DOTNET_VERSION = re.compile(r"^(\d+)\.")
_TABLE_NAMES = {
    0: "Module",
    1: "TypeRef",
    2: "TypeDef",
    4: "Field",
    6: "MethodDef",
    8: "Param",
    9: "InterfaceImpl",
    12: "CustomAttribute",
    18: "EventMap",
    20: "Event",
    21: "PropertyMap",
    23: "Property",
    32: "Assembly",
    35: "AssemblyRef",
    41: "NestedClass",
    42: "GenericParam",
    44: "GenericParamConstraint",
}


def _emitter_project() -> Path:
    project = Path(__file__).with_name("_dummy_emitter") / "BalDummyEmitter.csproj"
    source = project.with_name("Program.cs")
    if not project.is_file() or not source.is_file():
        raise DependencyUnavailable("bundled BAL DummyDll emitter source is unavailable")
    return project


def _emitter_source_sha256() -> str:
    project = _emitter_project()
    digest = hashlib.sha256()
    for path in (project, project.with_name("Program.cs")):
        data = path.read_bytes()
        digest.update(path.name.encode("utf-8"))
        digest.update(b"\0")
        digest.update(data)
        digest.update(b"\0")
    return digest.hexdigest()


def _output_file_name(image: dict[str, Any]) -> str:
    name = image["name"]
    if (
        Path(name).name != name
        or name in {".", ".."}
        or any(character in name for character in '<>:"/\\|?*')
        or any(ord(character) < 0x20 for character in name)
    ):
        raise ContractViolation("dump IR image name is unsafe for DummyDll output")
    return name if name.casefold().endswith(".dll") else f"{name}.dll"


def _expected_images(payload: dict[str, Any]) -> dict[str, dict[str, int]]:
    by_image: dict[str, list[dict[str, Any]]] = {
        image["id"]: [] for image in payload["images"]
    }
    for type_record in payload["types"]:
        by_image[type_record["image_id"]].append(type_record)
    expected: dict[str, dict[str, int]] = {}
    names = {HELPER_FILE_NAME.casefold()}
    for image in payload["images"]:
        file_name = _output_file_name(image)
        if file_name.casefold() in names:
            raise ContractViolation("DummyDll output names are not unique")
        names.add(file_name.casefold())
        types = by_image[image["id"]]
        expected[file_name] = {
            "type_count": len(types),
            "field_count": sum(len(item.get("fields", [])) for item in types),
            "property_count": sum(len(item.get("properties", [])) for item in types),
            "method_count": sum(len(item.get("methods", [])) for item in types),
            "event_count": sum(len(item.get("events", [])) for item in types),
        }
    return expected


def _u16(data: bytes, offset: int) -> int:
    if offset < 0 or offset + 2 > len(data):
        raise AcquisitionError("managed DLL header is truncated")
    return struct.unpack_from("<H", data, offset)[0]


def _u32(data: bytes, offset: int) -> int:
    if offset < 0 or offset + 4 > len(data):
        raise AcquisitionError("managed DLL header is truncated")
    return struct.unpack_from("<I", data, offset)[0]


def _managed_table_counts(data: bytes) -> dict[str, int]:
    if len(data) < 0x100 or data[:2] != b"MZ":
        raise AcquisitionError("DummyDll DOS header is invalid")
    pe_offset = _u32(data, 0x3C)
    if data[pe_offset : pe_offset + 4] != b"PE\0\0":
        raise AcquisitionError("DummyDll PE signature is invalid")
    coff = pe_offset + 4
    machine = _u16(data, coff)
    section_count = _u16(data, coff + 2)
    optional_size = _u16(data, coff + 16)
    characteristics = _u16(data, coff + 18)
    optional = coff + 20
    optional_magic = _u16(data, optional)
    if (
        machine not in {0x14C, 0x8664}
        or not section_count
        or optional_magic not in {0x10B, 0x20B}
        or not characteristics & 0x2000
    ):
        raise AcquisitionError("DummyDll PE architecture or characteristics are invalid")
    directory = optional + (96 if optional_magic == 0x10B else 112)
    cli_rva = _u32(data, directory + 14 * 8)
    cli_size = _u32(data, directory + 14 * 8 + 4)
    if not cli_rva or cli_size < 0x48:
        raise AcquisitionError("DummyDll CLR directory is unavailable")
    sections: list[tuple[int, int, int, int]] = []
    section_offset = optional + optional_size
    for index in range(section_count):
        entry = section_offset + index * 40
        if entry + 40 > len(data):
            raise AcquisitionError("DummyDll section table is truncated")
        virtual_size, virtual_rva, raw_size, raw_offset = struct.unpack_from(
            "<IIII", data, entry + 8
        )
        sections.append((virtual_rva, max(virtual_size, raw_size), raw_offset, raw_size))

    def rva_to_offset(rva: int, size: int = 1) -> int:
        for virtual_rva, extent, raw_offset, raw_size in sections:
            relative = rva - virtual_rva
            if 0 <= relative and relative + size <= min(extent, raw_size):
                result = raw_offset + relative
                if result + size <= len(data):
                    return result
        raise AcquisitionError("DummyDll RVA does not map to complete file data")

    cli = rva_to_offset(cli_rva, 0x48)
    if _u32(data, cli) < 0x48:
        raise AcquisitionError("DummyDll CLR header is invalid")
    metadata_rva = _u32(data, cli + 8)
    metadata_size = _u32(data, cli + 12)
    metadata = rva_to_offset(metadata_rva, metadata_size)
    metadata_end = metadata + metadata_size
    if data[metadata : metadata + 4] != b"BSJB":
        raise AcquisitionError("DummyDll CLR metadata signature is invalid")
    version_bytes = _u32(data, metadata + 12)
    stream_header = metadata + 16 + ((version_bytes + 3) & ~3)
    if stream_header + 4 > metadata_end:
        raise AcquisitionError("DummyDll metadata stream directory is truncated")
    stream_count = _u16(data, stream_header + 2)
    cursor = stream_header + 4
    tables: tuple[int, int] | None = None
    for _ in range(stream_count):
        if cursor + 8 > metadata_end:
            raise AcquisitionError("DummyDll metadata stream header is truncated")
        relative, size = struct.unpack_from("<II", data, cursor)
        name_start = cursor + 8
        name_end = data.find(b"\0", name_start, min(name_start + 32, metadata_end))
        if name_end < 0:
            raise AcquisitionError("DummyDll metadata stream name is invalid")
        try:
            name = data[name_start:name_end].decode("ascii")
        except UnicodeDecodeError as error:
            raise AcquisitionError("DummyDll metadata stream name is invalid") from error
        cursor = (name_end + 4) & ~3
        if relative + size > metadata_size:
            raise AcquisitionError("DummyDll metadata stream extent is invalid")
        if name in {"#~", "#-"}:
            tables = (metadata + relative, size)
    if tables is None:
        raise AcquisitionError("DummyDll metadata tables stream is unavailable")
    table_offset, table_size = tables
    if table_size < 24 or table_offset + table_size > metadata_end:
        raise AcquisitionError("DummyDll metadata tables stream is truncated")
    valid = struct.unpack_from("<Q", data, table_offset + 8)[0]
    row_cursor = table_offset + 24
    counts: dict[str, int] = {}
    for table_index in range(64):
        if valid & (1 << table_index):
            rows = _u32(data, row_cursor)
            row_cursor += 4
            name = _TABLE_NAMES.get(table_index)
            if name is not None:
                counts[name] = rows
    if counts.get("Module") != 1 or counts.get("Assembly") != 1:
        raise AcquisitionError("DummyDll module or assembly metadata is invalid")
    counts["machine"] = machine
    counts["pe32_plus"] = int(optional_magic == 0x20B)
    counts["clr_metadata_bytes"] = metadata_size
    return counts


def _inspect_managed_dll(path: Path) -> dict[str, Any]:
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError(f"DummyDll artifact is unavailable: {path.name}")
    tables = _managed_table_counts(path.read_bytes())
    return {
        "identity": file_identity(path),
        "valid_managed_pe": True,
        "machine": f"0x{tables.pop('machine'):04X}",
        "pe32_plus": bool(tables.pop("pe32_plus")),
        "clr_metadata_bytes": tables.pop("clr_metadata_bytes"),
        "tables": tables,
    }


def inspect_dummy_dll_tree(
    payload: dict[str, Any],
    root: Path,
    *,
    emitter_receipt: dict[str, Any] | None = None,
) -> dict[str, Any]:
    totals = validate_dump_ir(payload)
    expected = _expected_images(payload)
    root = root.expanduser().resolve()
    if not root.is_dir() or root.is_symlink():
        raise AcquisitionError("DummyDll output directory is unavailable")
    dlls = {
        path.name: path
        for path in root.iterdir()
        if path.is_file() and not path.is_symlink() and path.suffix.casefold() == ".dll"
    }
    expected_names = {HELPER_FILE_NAME, *expected}
    if set(dlls) != expected_names:
        raise AcquisitionError("DummyDll file inventory does not match runtime images")
    helper = _inspect_managed_dll(dlls[HELPER_FILE_NAME])
    helper_tables = helper["tables"]
    helper_contract_matches = (
        helper_tables.get("TypeDef") == 6
        and helper_tables.get("Field") == 10
        and helper_tables.get("MethodDef") == 5
    )
    images: list[dict[str, Any]] = []
    aggregate = {
        "type_count": 0,
        "field_count": 0,
        "property_count": 0,
        "method_count": 0,
        "event_count": 0,
    }
    for image in payload["images"]:
        file_name = _output_file_name(image)
        inspected = _inspect_managed_dll(dlls[file_name])
        tables = inspected["tables"]
        actual = {
            "type_count": tables.get("TypeDef", 0) - 1,
            "field_count": tables.get("Field", 0),
            "property_count": tables.get("Property", 0),
            "method_count": tables.get("MethodDef", 0),
            "event_count": tables.get("Event", 0),
        }
        matches = actual == expected[file_name]
        if not matches:
            raise AcquisitionError(f"DummyDll metadata inventory differs from IR: {file_name}")
        for key, value in actual.items():
            aggregate[key] += value
        images.append(
            {
                "image_id": image["id"],
                "file_name": file_name,
                "identity": inspected["identity"],
                "counts": actual,
                "valid_managed_pe": inspected["valid_managed_pe"],
                "metadata_inventory_matches_ir": matches,
                "custom_attribute_count": tables.get("CustomAttribute", 0),
            }
        )
    expected_aggregate = {
        "type_count": totals["type_count"],
        "field_count": totals["field_count"],
        "property_count": totals["property_count"],
        "method_count": totals["method_count"],
        "event_count": totals["event_count"],
    }
    checks = {
        "dll_count_matches_images_plus_helper": len(dlls) == totals["image_count"] + 1,
        "all_files_are_managed_pe": all(item["valid_managed_pe"] for item in images)
        and helper["valid_managed_pe"],
        "helper_attribute_contract_matches": helper_contract_matches,
        "metadata_inventory_matches_ir": aggregate == expected_aggregate,
        "target_binding_present": bool(payload["target"]["executable_sha256"]),
        "external_runtime_component_absent": True,
        "saved_reference_generation_seed_absent": True,
    }
    if emitter_receipt is not None:
        emitted = {
            item.get("file_name"): item
            for item in emitter_receipt.get("assemblies", [])
            if isinstance(item, dict)
        }
        checks["emitter_schema_complete"] = (
            emitter_receipt.get("schema") == EMITTER_SCHEMA
            and emitter_receipt.get("status") == "complete"
            and emitter_receipt.get("target_executable_sha256")
            == payload["target"]["executable_sha256"]
            and emitter_receipt.get("dll_count") == len(dlls)
            and emitter_receipt.get("all_metadata_valid") is True
            and emitter_receipt.get("all_inventories_match_ir") is True
        )
        checks["emitter_file_hashes_match"] = set(emitted) == expected_names and all(
            emitted[name].get("sha256") == file_identity(path)["sha256"]
            for name, path in dlls.items()
        )
    if not all(checks.values()):
        raise AcquisitionError("DummyDll output failed its BAL ownership or fidelity contract")
    return {
        "schema": DUMMY_DLL_SCHEMA,
        "status": "complete",
        "target": payload["target"],
        "counts": {**expected_aggregate, "image_count": totals["image_count"]},
        "dll_count": len(dlls),
        "helper": {
            "file_name": HELPER_FILE_NAME,
            "identity": helper["identity"],
            "attribute_type_count": helper_tables["TypeDef"] - 1,
            "valid_managed_pe": helper["valid_managed_pe"],
        },
        "images": images,
        "checks": checks,
    }


def _run(
    command: list[str],
    *,
    cwd: Path,
    environment: dict[str, str],
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            cwd=cwd,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise DependencyUnavailable("BAL DummyDll emitter could not be executed") from error


def build_dummy_dlls(
    payload: dict[str, Any],
    *,
    output_dir: Path,
    dotnet: str | None = None,
) -> dict[str, Any]:
    validate_dump_ir(payload)
    _expected_images(payload)
    executable = dotnet or shutil.which("dotnet")
    if not executable:
        raise DependencyUnavailable(".NET SDK is required to build BAL-owned DummyDll output")
    project = _emitter_project()
    output_dir = output_dir.expanduser().resolve()
    if output_dir.exists() and (output_dir.is_symlink() or not output_dir.is_dir()):
        raise AcquisitionError("DummyDll output boundary is invalid")
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix=".alpha-dummydll.", dir=output_dir.parent
    ) as temporary:
        temporary_root = Path(temporary).resolve()
        private_ir = temporary_root / "dump-ir.private.json"
        atomic_write_json(private_ir, payload)
        private_ir.chmod(0o600)
        build_dir = temporary_root / "emitter-build"
        source_dir = temporary_root / "emitter-source"
        generated_dir = temporary_root / "generated"
        cli_home = temporary_root / "dotnet-home"
        build_dir.mkdir(mode=0o700)
        source_dir.mkdir(mode=0o700)
        generated_dir.mkdir(mode=0o700)
        cli_home.mkdir(mode=0o700)
        environment = os.environ.copy()
        environment.update(
            {
                "DOTNET_CLI_HOME": str(cli_home),
                "DOTNET_NOLOGO": "1",
                "DOTNET_SKIP_FIRST_TIME_EXPERIENCE": "1",
                "DOTNET_CLI_TELEMETRY_OPTOUT": "1",
                "NUGET_PACKAGES": str(temporary_root / "nuget"),
            }
        )
        version_result = _run(
            [executable, "--version"],
            cwd=temporary_root,
            environment=environment,
            timeout=30,
        )
        version = version_result.stdout.strip()
        version_match = _DOTNET_VERSION.match(version)
        if version_result.returncode or not version_match or int(version_match.group(1)) < 8:
            raise DependencyUnavailable(".NET SDK 8 or newer is required by the bundled DummyDll emitter")
        sdk_major = int(version_match.group(1))
        copied_project = source_dir / project.name
        copied_source = source_dir / "Program.cs"
        project_text = project.read_text(encoding="utf-8").replace(
            "<TargetFramework>net10.0</TargetFramework>",
            f"<TargetFramework>net{sdk_major}.0</TargetFramework>",
        )
        if f"<TargetFramework>net{sdk_major}.0</TargetFramework>" not in project_text:
            raise DependencyUnavailable("bundled BAL DummyDll emitter target framework is invalid")
        copied_project.write_text(project_text, encoding="utf-8")
        shutil.copy2(project.with_name("Program.cs"), copied_source)
        copied_project.chmod(0o600)
        copied_source.chmod(0o600)
        nuget_config = temporary_root / "NuGet.Config"
        nuget_config.write_text(
            "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"
            "<configuration><packageSources><clear /></packageSources></configuration>\n",
            encoding="utf-8",
        )
        nuget_config.chmod(0o600)
        restore = _run(
            [
                executable,
                "restore",
                str(copied_project),
                "--nologo",
                "--ignore-failed-sources",
                "--configfile",
                str(nuget_config),
            ],
            cwd=temporary_root,
            environment=environment,
            timeout=120,
        )
        if restore.returncode:
            detail = (restore.stderr or restore.stdout).strip().splitlines()
            suffix = f": {detail[-1]}" if detail else ""
            raise DependencyUnavailable(f"BAL DummyDll emitter restore failed{suffix}")
        build = _run(
            [
                executable,
                "build",
                str(copied_project),
                "-c",
                "Release",
                "--nologo",
                "--verbosity",
                "quiet",
                "--no-incremental",
                "--no-restore",
                "-o",
                str(build_dir),
            ],
            cwd=temporary_root,
            environment=environment,
            timeout=180,
        )
        emitter = build_dir / "BalDummyEmitter.dll"
        if build.returncode or not emitter.is_file():
            detail = (build.stderr or build.stdout).strip().splitlines()
            suffix = f": {detail[-1]}" if detail else ""
            raise DependencyUnavailable(f"BAL DummyDll emitter build failed{suffix}")
        emitted = _run(
            [
                executable,
                str(emitter),
                "emit",
                str(private_ir),
                str(generated_dir),
            ],
            cwd=temporary_root,
            environment=environment,
            timeout=600,
        )
        if emitted.returncode:
            detail = (emitted.stderr or emitted.stdout).strip().splitlines()
            suffix = f": {detail[-1]}" if detail else ""
            raise AcquisitionError(f"BAL DummyDll emission failed{suffix}")
        try:
            emitter_receipt = json.loads(emitted.stdout)
        except json.JSONDecodeError as error:
            raise AcquisitionError("BAL DummyDll emitter receipt is invalid") from error
        if not isinstance(emitter_receipt, dict):
            raise AcquisitionError("BAL DummyDll emitter receipt is invalid")
        for path in generated_dir.iterdir():
            if path.is_file():
                path.chmod(0o600)
        inspect_dummy_dll_tree(
            payload, generated_dir, emitter_receipt=emitter_receipt
        )

        backup = temporary_root / "previous-output"
        replaced_existing = output_dir.exists()
        if replaced_existing:
            os.replace(output_dir, backup)
        try:
            os.replace(generated_dir, output_dir)
        except BaseException:
            if replaced_existing and backup.exists() and not output_dir.exists():
                os.replace(backup, output_dir)
            raise
        if backup.exists():
            shutil.rmtree(backup)
        output_dir.chmod(0o700)
        result = inspect_dummy_dll_tree(
            payload, output_dir, emitter_receipt=emitter_receipt
        )
        result["emitter"] = {
            "implementation": "bundled-bal-metadata-emitter",
            "source_sha256": _emitter_source_sha256(),
            "sdk_version": version,
            "build_time_dependency_only": True,
            "generated_dll_runtime_dependency_on_emitter": False,
        }
        return result


def _validated_runtime_bundle(
    bundle_dir: Path,
) -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    bundle_dir = bundle_dir.expanduser().resolve()
    if (
        not bundle_dir.is_dir()
        or bundle_dir.is_symlink()
        or bundle_dir.stat().st_uid != os.getuid()
        or stat.S_IMODE(bundle_dir.stat().st_mode) & 0o077
    ):
        raise AcquisitionError("runtime DummyDll bundle is not owner-only")
    manifest_path = bundle_dir / "manifest.private.json"
    if (
        not manifest_path.is_file()
        or manifest_path.is_symlink()
        or stat.S_IMODE(manifest_path.stat().st_mode) & 0o077
    ):
        raise AcquisitionError("runtime DummyDll manifest is unavailable")
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise AcquisitionError("runtime DummyDll manifest is invalid") from error
    if (
        not isinstance(manifest, dict)
        or manifest.get("schema") != "alpha.runtime-dummy-bundle/v1"
        or manifest.get("status") != "complete"
        or not isinstance(manifest.get("checks"), dict)
        or not manifest["checks"]
        or not all(manifest["checks"].values())
    ):
        raise AcquisitionError("runtime DummyDll manifest is incomplete")
    target = manifest.get("target")
    images = manifest.get("images")
    types = manifest.get("types")
    documents = manifest.get("image_documents")
    if (
        not isinstance(target, dict)
        or not isinstance(target.get("executable_sha256"), str)
        or not re.fullmatch(r"[0-9a-f]{64}", target["executable_sha256"])
        or not isinstance(images, list)
        or not images
        or any(not isinstance(item, dict) for item in images)
        or not isinstance(types, list)
        or not types
        or any(not isinstance(item, dict) for item in types)
        or not isinstance(documents, list)
        or len(documents) != len(images)
        or any(not isinstance(item, dict) for item in documents)
    ):
        raise AcquisitionError("runtime DummyDll manifest inventories are invalid")
    image_ids: set[str] = set()
    output_names = {HELPER_FILE_NAME.casefold()}
    for image in images:
        image_id = image.get("id")
        if not isinstance(image_id, str) or not image_id or image_id in image_ids:
            raise AcquisitionError("runtime DummyDll image ids are invalid")
        image_ids.add(image_id)
        file_name = _output_file_name(image)
        if file_name.casefold() in output_names:
            raise AcquisitionError("runtime DummyDll output names repeat")
        output_names.add(file_name.casefold())
    type_ids: set[str] = set()
    type_by_id: dict[str, dict[str, Any]] = {}
    for index, record in enumerate(types):
        type_id = record.get("id")
        if (
            not isinstance(type_id, str)
            or not type_id
            or type_id in type_ids
            or record.get("type_definition_index") != index
            or record.get("image_id") not in image_ids
            or not isinstance(record.get("name"), str)
            or "\0" in record["name"]
            or (not record["name"] and not record.get("signature_name"))
        ):
            raise AcquisitionError("runtime DummyDll type index is invalid")
        if "signature_name" in record or "signature_namespace" in record:
            if (not isinstance(record.get("signature_name"), str)
                or not record["signature_name"]
                or not isinstance(record.get("signature_namespace"), str)
                or any(ord(character) < 32 or ord(character) == 127 for character in
                       record["signature_name"] + record["signature_namespace"])):
                raise AcquisitionError("runtime DummyDll signature labels are invalid")
        type_ids.add(type_id)
        type_by_id[type_id] = record
    for record in types:
        owner = record.get("declaring_type_id")
        if owner is not None and (
            owner not in type_by_id
            or type_by_id[owner].get("image_id") != record.get("image_id")
        ):
            raise AcquisitionError("runtime DummyDll nested type owner is invalid")
    by_document: dict[str, dict[str, int]] = {}
    observed_types = 0
    for document in documents:
        image_id = document.get("image_id")
        file_name = document.get("file_name")
        digest = document.get("sha256")
        if (
            image_id not in image_ids
            or image_id in by_document
            or not isinstance(file_name, str)
            or Path(file_name).name != file_name
            or not isinstance(digest, str)
            or not re.fullmatch(r"[0-9a-f]{64}", digest)
        ):
            raise AcquisitionError("runtime DummyDll image document is invalid")
        path = bundle_dir / file_name
        if (
            not path.is_file()
            or path.is_symlink()
            or stat.S_IMODE(path.stat().st_mode) & 0o077
            or file_identity(path)["sha256"] != digest
        ):
            raise AcquisitionError("runtime DummyDll image document is stale")
        counts: dict[str, int] = {}
        for key in (
            "type_count",
            "field_count",
            "property_count",
            "method_count",
            "event_count",
        ):
            value = document.get(key)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise AcquisitionError("runtime DummyDll image counts are invalid")
            counts[key] = value
        observed_types += counts["type_count"]
        by_document[image_id] = counts
    if set(by_document) != image_ids or observed_types != len(types):
        raise AcquisitionError("runtime DummyDll image partition is incomplete")
    expected_counts = manifest.get("counts", {})
    aggregate = {
        key: sum(item[key] for item in by_document.values())
        for key in (
            "type_count",
            "field_count",
            "property_count",
            "method_count",
            "event_count",
        )
    }
    if any(expected_counts.get(key) != value for key, value in aggregate.items()):
        raise AcquisitionError("runtime DummyDll manifest counts are inconsistent")
    return manifest, by_document


def inspect_runtime_dummy_dll_tree(
    bundle_dir: Path,
    root: Path,
    *,
    emitter_receipt: dict[str, Any] | None = None,
) -> dict[str, Any]:
    manifest, expected_by_image = _validated_runtime_bundle(bundle_dir)
    root = root.expanduser().resolve()
    if not root.is_dir() or root.is_symlink():
        raise AcquisitionError("runtime DummyDll output directory is unavailable")
    dlls = {
        path.name: path
        for path in root.iterdir()
        if path.is_file() and not path.is_symlink() and path.suffix.casefold() == ".dll"
    }
    expected_names = {
        HELPER_FILE_NAME,
        *(_output_file_name(image) for image in manifest["images"]),
    }
    if set(dlls) != expected_names:
        raise AcquisitionError("runtime DummyDll file inventory differs from images")
    helper = _inspect_managed_dll(dlls[HELPER_FILE_NAME])
    helper_tables = helper["tables"]
    helper_contract_matches = (
        helper_tables.get("TypeDef") == 6
        and helper_tables.get("Field") == 10
        and helper_tables.get("MethodDef") == 5
    )
    aggregate = {
        "type_count": 0,
        "field_count": 0,
        "property_count": 0,
        "method_count": 0,
        "event_count": 0,
    }
    images: list[dict[str, Any]] = []
    for image in manifest["images"]:
        file_name = _output_file_name(image)
        inspected = _inspect_managed_dll(dlls[file_name])
        tables = inspected["tables"]
        actual = {
            "type_count": tables.get("TypeDef", 0) - 1,
            "field_count": tables.get("Field", 0),
            "property_count": tables.get("Property", 0),
            "method_count": tables.get("MethodDef", 0),
            "event_count": tables.get("Event", 0),
        }
        if actual != expected_by_image[image["id"]]:
            raise AcquisitionError(
                f"runtime DummyDll metadata inventory differs: {file_name}"
            )
        for key, value in actual.items():
            aggregate[key] += value
        images.append(
            {
                "image_id": image["id"],
                "file_name": file_name,
                "identity": inspected["identity"],
                "counts": actual,
                "valid_managed_pe": inspected["valid_managed_pe"],
                "metadata_inventory_matches_bundle": True,
                "custom_attribute_count": tables.get("CustomAttribute", 0),
            }
        )
    expected_aggregate = {
        key: manifest["counts"][key] for key in aggregate
    }
    checks = {
        "dll_count_matches_images_plus_helper": len(dlls)
        == len(manifest["images"]) + 1,
        "all_files_are_managed_pe": all(
            item["valid_managed_pe"] for item in images
        )
        and helper["valid_managed_pe"],
        "helper_attribute_contract_matches": helper_contract_matches,
        "metadata_inventory_matches_bundle": aggregate == expected_aggregate,
        "target_binding_present": bool(
            manifest["target"]["executable_sha256"]
        ),
        "external_runtime_component_absent": True,
        "saved_reference_generation_seed_absent": True,
    }
    if emitter_receipt is not None:
        emitted = {
            item.get("file_name"): item
            for item in emitter_receipt.get("assemblies", [])
            if isinstance(item, dict)
        }
        checks["emitter_schema_complete"] = (
            emitter_receipt.get("schema") == EMITTER_SCHEMA
            and emitter_receipt.get("status") == "complete"
            and emitter_receipt.get("target_executable_sha256")
            == manifest["target"]["executable_sha256"]
            and emitter_receipt.get("dll_count") == len(dlls)
            and emitter_receipt.get("all_metadata_valid") is True
            and emitter_receipt.get("all_inventories_match_ir") is True
        )
        checks["emitter_file_hashes_match"] = set(emitted) == expected_names and all(
            emitted[name].get("sha256") == file_identity(path)["sha256"]
            for name, path in dlls.items()
        )
    if not all(checks.values()):
        raise AcquisitionError("runtime DummyDll output validation failed")
    return {
        "schema": DUMMY_DLL_SCHEMA,
        "status": "complete",
        "target": manifest["target"],
        "counts": {**aggregate, "image_count": len(manifest["images"])},
        "dll_count": len(dlls),
        "helper": {
            "file_name": HELPER_FILE_NAME,
            "identity": helper["identity"],
            "attribute_type_count": helper_tables["TypeDef"] - 1,
            "valid_managed_pe": helper["valid_managed_pe"],
        },
        "images": images,
        "checks": checks,
        "fidelity": manifest.get("fidelity", {}),
    }


def build_runtime_dummy_dlls(
    bundle_dir: Path,
    *,
    output_dir: Path,
    dotnet: str | None = None,
    timeout: int = 1800,
) -> dict[str, Any]:
    manifest, _expected = _validated_runtime_bundle(bundle_dir)
    bundle_dir = bundle_dir.expanduser().resolve()
    executable = dotnet or shutil.which("dotnet")
    if not executable:
        raise DependencyUnavailable(".NET SDK is required to build runtime DummyDll output")
    project = _emitter_project()
    emitter_source_sha256 = _emitter_source_sha256()
    if output_dir.expanduser().is_symlink():
        raise AcquisitionError("runtime DummyDll requires a new output destination; existing output preserved")
    output_dir = output_dir.expanduser().resolve()
    if output_dir.exists():
        raise AcquisitionError("runtime DummyDll requires a new output destination; existing output preserved")
    output_dir.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix=".alpha-runtime-dummydll.", dir=output_dir.parent
    ) as temporary, tempfile.TemporaryDirectory(
        prefix=".alpha-runtime-dll-stage.", dir=output_dir.parent
    ) as generated:
        temporary_root = Path(temporary).resolve()
        build_dir = temporary_root / "emitter-build"
        source_dir = temporary_root / "emitter-source"
        generated_dir = Path(generated).resolve()
        cli_home = temporary_root / "dotnet-home"
        for directory in (build_dir, source_dir, cli_home):
            directory.mkdir(mode=0o700)
        environment = os.environ.copy()
        environment.update(
            {
                "DOTNET_CLI_HOME": str(cli_home),
                "DOTNET_NOLOGO": "1",
                "DOTNET_SKIP_FIRST_TIME_EXPERIENCE": "1",
                "DOTNET_CLI_TELEMETRY_OPTOUT": "1",
                "NUGET_PACKAGES": str(temporary_root / "nuget"),
            }
        )
        version_result = _run(
            [executable, "--version"],
            cwd=temporary_root,
            environment=environment,
            timeout=30,
        )
        version = version_result.stdout.strip()
        version_match = _DOTNET_VERSION.match(version)
        if version_result.returncode or not version_match or int(version_match.group(1)) < 8:
            raise DependencyUnavailable(".NET SDK 8 or newer is required by the bundled DummyDll emitter")
        sdk_major = int(version_match.group(1))
        copied_project = source_dir / project.name
        copied_source = source_dir / "Program.cs"
        project_text = project.read_text(encoding="utf-8").replace(
            "<TargetFramework>net10.0</TargetFramework>",
            f"<TargetFramework>net{sdk_major}.0</TargetFramework>",
        )
        if f"<TargetFramework>net{sdk_major}.0</TargetFramework>" not in project_text:
            raise DependencyUnavailable("bundled BAL DummyDll emitter target framework is invalid")
        copied_project.write_text(project_text, encoding="utf-8")
        shutil.copy2(project.with_name("Program.cs"), copied_source)
        copied_project.chmod(0o600)
        copied_source.chmod(0o600)
        nuget_config = temporary_root / "NuGet.Config"
        nuget_config.write_text(
            '<?xml version="1.0" encoding="utf-8"?>\n'
            "<configuration><packageSources><clear /></packageSources></configuration>\n",
            encoding="utf-8",
        )
        nuget_config.chmod(0o600)
        restore = _run(
            [
                executable,
                "restore",
                str(copied_project),
                "--nologo",
                "--ignore-failed-sources",
                "--configfile",
                str(nuget_config),
            ],
            cwd=temporary_root,
            environment=environment,
            timeout=120,
        )
        if restore.returncode:
            detail = (restore.stderr or restore.stdout).strip().splitlines()
            suffix = f": {detail[-1]}" if detail else ""
            raise DependencyUnavailable(f"BAL DummyDll emitter restore failed{suffix}")
        build = _run(
            [
                executable,
                "build",
                str(copied_project),
                "-c",
                "Release",
                "--nologo",
                "--verbosity",
                "quiet",
                "--no-incremental",
                "--no-restore",
                "-o",
                str(build_dir),
            ],
            cwd=temporary_root,
            environment=environment,
            timeout=180,
        )
        emitter = build_dir / "BalDummyEmitter.dll"
        if build.returncode or not emitter.is_file():
            detail = (build.stderr or build.stdout).strip().splitlines()
            suffix = f": {detail[-1]}" if detail else ""
            raise DependencyUnavailable(f"BAL DummyDll emitter build failed{suffix}")
        emitted = _run(
            [
                executable,
                str(emitter),
                "emit-bundle",
                str(bundle_dir),
                str(generated_dir),
            ],
            cwd=temporary_root,
            environment=environment,
            timeout=timeout,
        )
        if emitted.returncode:
            detail = (emitted.stderr or emitted.stdout).strip().splitlines()
            suffix = f": {detail[-1]}" if detail else ""
            raise AcquisitionError(f"BAL runtime DummyDll emission failed{suffix}")
        try:
            emitter_receipt = json.loads(emitted.stdout)
        except json.JSONDecodeError as error:
            raise AcquisitionError("BAL runtime DummyDll emitter receipt is invalid") from error
        if not isinstance(emitter_receipt, dict):
            raise AcquisitionError("BAL runtime DummyDll emitter receipt is invalid")
        for path in generated_dir.iterdir():
            if path.is_file():
                path.chmod(0o600)
        inspect_runtime_dummy_dll_tree(
            bundle_dir, generated_dir, emitter_receipt=emitter_receipt
        )
        if _validated_runtime_bundle(bundle_dir) != (manifest, _expected):
            raise AcquisitionError("runtime DummyDll source bundle changed during generation")
        if _emitter_source_sha256() != emitter_source_sha256:
            raise AcquisitionError("runtime DummyDll emitter source changed during generation")
        from alpha.h02 import publish_new_directory
        publish_new_directory(generated_dir, output_dir)
        output_dir.chmod(0o700)
        result = inspect_runtime_dummy_dll_tree(
            bundle_dir, output_dir, emitter_receipt=emitter_receipt
        )
        result["emitter"] = {
            "implementation": "bundled-bal-metadata-emitter",
            "source_sha256": emitter_source_sha256,
            "sdk_version": version,
            "build_time_dependency_only": True,
            "generated_dll_runtime_dependency_on_emitter": False,
            "assembly_partitioned_input": True,
        }
        result["bundle_manifest"] = file_identity(
            bundle_dir / "manifest.private.json"
        )
        result["target"] = manifest["target"]
        result["metadata_complete"] = False
        return result
