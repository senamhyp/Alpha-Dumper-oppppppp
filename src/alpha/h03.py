import hashlib
import json
import re
import struct
from pathlib import Path
from typing import Any, Iterable

from alpha.h01 import AcquisitionError
from alpha.h02 import atomic_write_json, file_identity, sha256_file


ORACLE_SCHEMA = "alpha.dump-quality-oracle/v1"
EXPECTED_PROTO_BANNER = "// Dumped by sena with alpha"
_MESSAGE = re.compile(r"^\s*message\s+([A-Za-z_]\w*)\s*\{")
_ENUM = re.compile(r"^\s*enum\s+([A-Za-z_]\w*)\s*\{")
_FIELD = re.compile(
    r"^\s*(?:(?:repeated|optional|required)\s+)?"
    r"(?:map\s*<[^>]+>|[A-Za-z_][\w.]*)\s+"
    r"([A-Za-z_]\w*)\s*=\s*(\d+)\b"
)
_SCRIPT_SECTION = re.compile(r'^  "([A-Za-z]+)": \[$')


def _artifact_identity(path: Path) -> dict[str, Any]:
    identity = file_identity(path)
    return {"bytes": identity["bytes"], "sha256": identity["sha256"]}


def _required_file(root: Path, relative: str) -> Path:
    path = (root / relative).resolve()
    if path.parent != root and root not in path.parents:
        raise AcquisitionError(f"reference path escaped its root: {relative}")
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError(f"required reference artifact is unavailable: {relative}")
    return path


def _load_json(path: Path, *, maximum_bytes: int = 64 * 1024 * 1024) -> Any:
    if path.stat().st_size > maximum_bytes:
        raise AcquisitionError(f"reference JSON exceeds the safety limit: {path.name}")
    try:
        with path.open("r", encoding="utf-8") as source:
            return json.load(source)
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AcquisitionError(f"invalid reference JSON: {path.name}") from error


def inspect_metadata_header(path: Path) -> dict[str, Any]:
    size = path.stat().st_size
    if size < 16:
        raise AcquisitionError("metadata is smaller than its fixed header")
    with path.open("rb") as source:
        fixed = source.read(16)
        magic, version, first_offset, _first_size = struct.unpack("<IIII", fixed)
        if magic != 0xFAB11BAF:
            raise AcquisitionError("metadata magic is invalid")
        if first_offset < 0x80 or first_offset > 0x4000 or (first_offset - 8) % 8:
            raise AcquisitionError("metadata directory extent is invalid")
        source.seek(0)
        header = source.read(first_offset)
    pair_count = (first_offset - 8) // 8
    pairs: list[dict[str, int]] = []
    previous_end = first_offset
    contiguous = True
    for index in range(pair_count):
        offset, table_bytes = struct.unpack_from("<II", header, 8 + index * 8)
        if offset == 0 and table_bytes == 0:
            continue
        end = offset + table_bytes
        if offset != previous_end or end < offset or end > size:
            contiguous = False
        previous_end = end
        pairs.append({"index": index, "offset": offset, "bytes": table_bytes})
    exact_extent = bool(pairs) and previous_end == size
    if len(pairs) < 16 or not contiguous or not exact_extent:
        raise AcquisitionError("metadata table directory is not contiguous and exact")
    return {
        "magic": f"0x{magic:08X}",
        "version": version,
        "header_bytes": first_offset,
        "table_pair_count": pair_count,
        "nonempty_table_count": len(pairs),
        "tables_contiguous": contiguous,
        "final_extent_matches_file": exact_extent,
    }


def inspect_proto(path: Path) -> dict[str, Any]:
    messages: dict[str, list[tuple[str, int]]] = {}
    enum_count = 0
    contexts: list[tuple[str, str, int]] = []
    depth = 0
    first_nonempty = ""
    try:
        with path.open("r", encoding="utf-8") as source:
            for raw_line in source:
                line = raw_line.rstrip("\r\n")
                if not first_nonempty and line.strip():
                    first_nonempty = line.strip()
                opening = line.count("{")
                closing = line.count("}")
                message_match = _MESSAGE.match(line)
                enum_match = _ENUM.match(line)
                if message_match:
                    name = message_match.group(1)
                    if name in messages:
                        raise AcquisitionError(f"duplicate proto message: {name}")
                    messages[name] = []
                    contexts.append(("message", name, depth + max(1, opening)))
                elif enum_match:
                    enum_count += 1
                    contexts.append(("enum", enum_match.group(1), depth + max(1, opening)))
                else:
                    field_match = _FIELD.match(line)
                    active_message = next(
                        (name for kind, name, _level in reversed(contexts) if kind == "message"),
                        None,
                    )
                    if field_match and active_message is not None:
                        messages[active_message].append(
                            (field_match.group(1), int(field_match.group(2)))
                        )
                depth += opening - closing
                while contexts and depth < contexts[-1][2]:
                    contexts.pop()
    except (OSError, UnicodeDecodeError) as error:
        raise AcquisitionError("proto could not be read as UTF-8") from error
    duplicate_field_name_messages = 0
    duplicate_field_number_messages = 0
    for fields in messages.values():
        names = [name for name, _number in fields]
        numbers = [number for _name, number in fields]
        duplicate_field_name_messages += len(names) != len(set(names))
        duplicate_field_number_messages += len(numbers) != len(set(numbers))
    return {
        "identity": _artifact_identity(path),
        "banner_matches_required": first_nonempty == EXPECTED_PROTO_BANNER,
        "required_alpha_banner": EXPECTED_PROTO_BANNER,
        "message_count": len(messages),
        "enum_count": enum_count,
        "field_count": sum(len(fields) for fields in messages.values()),
        "duplicate_field_name_message_count": duplicate_field_name_messages,
        "duplicate_field_number_message_count": duplicate_field_number_messages,
        "_messages": messages,
    }


def _tree_identity(files: Iterable[tuple[str, Path]]) -> dict[str, Any]:
    digest = hashlib.sha256()
    count = 0
    total_bytes = 0
    for relative, path in sorted(files):
        item = file_identity(path)
        encoded = json.dumps(
            [relative.replace("\\", "/"), item["bytes"], item["sha256"]],
            ensure_ascii=False,
            separators=(",", ":"),
        ).encode("utf-8")
        digest.update(encoded)
        digest.update(b"\n")
        count += 1
        total_bytes += item["bytes"]
    return {"file_count": count, "bytes": total_bytes, "tree_sha256": digest.hexdigest()}


def inspect_excel_tree(root: Path) -> dict[str, Any]:
    if not root.is_dir() or root.is_symlink():
        raise AcquisitionError("Excel resource output directory is unavailable")
    files = [(path.relative_to(root).as_posix(), path) for path in root.rglob("*.json")]
    valid = 0
    for _relative, path in files:
        try:
            with path.open("r", encoding="utf-8") as source:
                json.load(source)
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
            raise AcquisitionError(f"invalid Excel resource JSON: {path.name}") from error
        valid += 1
    result = _tree_identity(files)
    result["json_valid_count"] = valid
    result["all_json_valid"] = valid == len(files) and valid > 0
    return result


def inspect_standard_output(root: Path) -> dict[str, Any]:
    root = root.expanduser().resolve()
    dump_cs = _required_file(root, "dump.cs")
    script = _required_file(root, "script.json")
    header = _required_file(root, "il2cpp.h")
    strings = _required_file(root, "stringliteral.json")
    script_counts: dict[str, int] = {}
    active: str | None = None
    with script.open("r", encoding="utf-8") as source:
        for line in source:
            section = _SCRIPT_SECTION.match(line.rstrip("\r\n"))
            if section:
                active = section.group(1)
                script_counts[active] = 0
            elif active and line.startswith("  ]"):
                active = None
            elif active == "Addresses" and re.match(r"^    \d+,?\s*$", line):
                script_counts[active] += 1
            elif active and line.rstrip("\r\n") == "    {":
                script_counts[active] += 1
    dump_counts = {
        "image_count": 0,
        "type_definition_count": 0,
        "field_section_count": 0,
        "property_section_count": 0,
        "method_section_count": 0,
        "method_rva_count": 0,
    }
    with dump_cs.open("r", encoding="utf-8", errors="replace") as source:
        for line in source:
            stripped = line.strip()
            if line.startswith("// Image "):
                dump_counts["image_count"] += 1
            if "// TypeDefIndex:" in line:
                dump_counts["type_definition_count"] += 1
            if stripped == "// Fields":
                dump_counts["field_section_count"] += 1
            elif stripped == "// Properties":
                dump_counts["property_section_count"] += 1
            elif stripped == "// Methods":
                dump_counts["method_section_count"] += 1
            elif stripped.startswith("// RVA: 0x"):
                dump_counts["method_rva_count"] += 1
    dummy_files = [
        path for path in (root / "DummyDll").rglob("*.dll") if path.is_file() and not path.is_symlink()
    ]
    all_files = [
        (path.relative_to(root).as_posix(), path)
        for path in root.rglob("*")
        if path.is_file() and not path.is_symlink()
    ]
    return {
        "required_files": {
            "dump.cs": _artifact_identity(dump_cs),
            "script.json": _artifact_identity(script),
            "il2cpp.h": _artifact_identity(header),
            "stringliteral.json": _artifact_identity(strings),
        },
        "script_counts": script_counts,
        "dump_counts": dump_counts,
        "dummy_dll_count": len(dummy_files),
        "tree": _tree_identity(all_files),
    }


def build_reference_oracle(
    *, reference_package: Path, standard_output: Path | None = None
) -> dict[str, Any]:
    root = reference_package.expanduser().resolve()
    if not root.is_dir() or root.is_symlink():
        raise AcquisitionError("reference package directory is unavailable")
    assembly = _required_file(root, "GameAssembly.dll")
    metadata = _required_file(root, "global-metadata.dat")
    proto_path = _required_file(root, "Genshin.proto")
    sorted_proto = _required_file(root, "Genshin_sorted.proto")
    class_path = _required_file(root, "classList.json")
    packet_path = _required_file(root, "packetIds.json")
    proto = inspect_proto(proto_path)
    messages = proto.pop("_messages")
    classes = _load_json(class_path)
    packets = _load_json(packet_path)
    if not isinstance(classes, list) or not isinstance(packets, dict):
        raise AcquisitionError("class or packet reference shape is invalid")
    class_fields: dict[str, list[tuple[str, int]]] = {}
    class_packets: dict[str, int] = {}
    field_count = 0
    for item in classes:
        if not isinstance(item, dict) or not isinstance(item.get("name"), str):
            raise AcquisitionError("class reference record is invalid")
        name = item["name"]
        fields = item.get("fields")
        if name in class_fields or not isinstance(fields, list):
            raise AcquisitionError("class reference names or fields are invalid")
        normalized: list[tuple[str, int]] = []
        for field in fields:
            if not isinstance(field, dict) or not isinstance(field.get("name"), str):
                raise AcquisitionError("class field reference record is invalid")
            number = field.get("number")
            if not isinstance(number, int):
                raise AcquisitionError("class field number is invalid")
            normalized.append((field["name"], number))
        class_fields[name] = normalized
        field_count += len(normalized)
        if isinstance(item.get("cmd_id"), int):
            class_packets[name] = item["cmd_id"]
    normalized_packets = {
        name: value for name, value in packets.items() if isinstance(name, str) and isinstance(value, int)
    }
    class_field_sets_are_proto_subsets = all(
        set(fields).issubset(set(messages[name]))
        for name, fields in class_fields.items()
        if name in messages
    )
    consistency = {
        "proto_and_class_message_sets_match": set(messages) == set(class_fields),
        "class_fields_are_proto_subsets": class_field_sets_are_proto_subsets,
        "packet_map_entries_match_classes": all(
            class_packets.get(name) == value for name, value in normalized_packets.items()
        ),
        "packet_map_covers_every_unique_class_cmd_id": set(normalized_packets.values())
        == set(class_packets.values()),
        "packet_ids_unique": len(set(normalized_packets.values())) == len(normalized_packets),
        "proto_has_no_duplicate_field_names": proto["duplicate_field_name_message_count"] == 0,
        "proto_has_no_duplicate_field_numbers": proto["duplicate_field_number_message_count"] == 0,
    }
    if not all(consistency.values()):
        failed = ", ".join(name for name, value in consistency.items() if not value)
        raise AcquisitionError(f"reference package is internally inconsistent: {failed}")
    oracle: dict[str, Any] = {
        "schema": ORACLE_SCHEMA,
        "status": "measured",
        "source_role": "read-only-quality-reference",
        "generation_seed_allowed": False,
        "primary": {
            "GameAssembly.dll": _artifact_identity(assembly),
            "global-metadata.dat": {
                **_artifact_identity(metadata),
                "header": inspect_metadata_header(metadata),
            },
            "Genshin.proto": proto,
            "Genshin_sorted.proto": _artifact_identity(sorted_proto),
            "classList.json": {
                **_artifact_identity(class_path),
                "class_count": len(classes),
                "field_count": field_count,
                "fieldless_class_count": sum(not fields for fields in class_fields.values()),
                "class_with_cmd_id_count": len(class_packets),
                "duplicate_cmd_id_class_count": len(class_packets)
                - len(set(class_packets.values())),
            },
            "packetIds.json": {
                **_artifact_identity(packet_path),
                "packet_id_count": len(normalized_packets),
            },
            "ExcelBinOutput": inspect_excel_tree(root / "ExcelBinOutput"),
        },
        "consistency": consistency,
        "required_output_banner": EXPECTED_PROTO_BANNER,
        "reference_banner_copied": False,
    }
    if standard_output is not None:
        oracle["standard_il2cpp_output"] = inspect_standard_output(standard_output)
    return oracle


def write_reference_oracle(
    *, reference_package: Path, standard_output: Path | None, output: Path
) -> dict[str, Any]:
    oracle = build_reference_oracle(
        reference_package=reference_package,
        standard_output=standard_output,
    )
    atomic_write_json(output, oracle)
    output.expanduser().resolve().chmod(0o600)
    return oracle


import importlib.metadata
import hashlib
import json
import os
import re
import subprocess
import shlex
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Protocol

from alpha.h01 import AcquisitionError, ContractViolation
from alpha.p01 import EVIDENCE_KINDS, Evidence, TargetIdentity
from alpha.h02 import inspect_pe
from alpha.h02 import public_identities_in_binary, public_identity
from alpha.h02 import bundle_version
from alpha.h02 import file_identity, generation_id, read_json, sha256_file


SEMVER = re.compile(r"(?<![0-9])([0-9]+\.[0-9]+\.[0-9]+)(?![0-9])")


@dataclass(frozen=True)
class CollectionContext:
    game_dir: Path
    executable: Path | None = None
    evidence_roots: tuple[Path, ...] = ()
    proto_roots: tuple[Path, ...] = ()
    rsa_roots: tuple[Path, ...] = ()


class AcquisitionProvider(Protocol):
    name: str

    def collect(
        self, context: CollectionContext, target: TargetIdentity
    ) -> Iterable[Evidence]: ...


def _select_executable(game_dir: Path, explicit: Path | None) -> Path:
    game_dir = game_dir.expanduser().resolve()
    if explicit is not None:
        candidate = explicit.expanduser().resolve()


        candidate_parent = candidate.parent
        if candidate_parent != game_dir and not (
            (game_dir / f"{candidate.stem}_Data").is_dir()
            or (candidate_parent / f"{candidate.stem}_Data").is_dir()
        ):
            raise AcquisitionError("explicit executable is outside the game directory")


        candidates = [explicit.expanduser().absolute()]
    else:
        candidates = [
            path.resolve()
            for path in game_dir.iterdir()
            if path.is_file()
            and not path.is_symlink()
            and path.suffix.casefold() == ".exe"
            and (game_dir / f"{path.stem}_Data").is_dir()
        ]
    if len(candidates) != 1:
        raise AcquisitionError(
            f"client executable selection must be unique, observed {len(candidates)}"
        )
    return candidates[0]


def collect_target(context: CollectionContext) -> tuple[TargetIdentity, Evidence]:
    executable = _select_executable(context.game_dir, context.executable)
    data_dir = executable.parent / f"{executable.stem}_Data"
    global_managers = data_dir / "globalgamemanagers"
    if not global_managers.is_file() or global_managers.is_symlink():
        raise AcquisitionError("Unity globalgamemanagers is missing")
    unity_version = bundle_version(global_managers)
    version = unity_version["version"]
    pe = inspect_pe(executable)
    version_resources = pe.get("version_resources") or []
    fixed_versions = sorted(
        {
            str(entry.get("file_version"))
            for entry in version_resources
            if isinstance(entry, dict) and entry.get("file_version")
        }
    )
    client_build = unity_version["build"]
    executable_ref = file_identity(executable)
    target = TargetIdentity(
        client_version=version,
        client_build=client_build,
        executable_path=str(executable),
        executable_sha256=executable_ref["sha256"],
        executable_bytes=executable_ref["bytes"],
    )
    evidence = Evidence(
        kind="client",
        target_version=version,
        target_executable_sha256=target.executable_sha256,
        source={
            "executable": executable_ref,
            "unity_global_managers": file_identity(global_managers),
        },
        facts={
            "client_build": client_build,
            "pe": pe,
            "version_authority": unity_version["authority"],
            "version_signal_count": 1,
            "pe_fixed_file_versions": fixed_versions,
        },
        provider="alpha.builtin.client",
    )
    return target, evidence


def _manifest_records(path: Path) -> list[dict[str, Any]]:
    if path.stat().st_size > 64 * 1024 * 1024 or path.stat().st_size == 0:
        return []
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return []
    stripped = text.lstrip()
    if not stripped or stripped[0] not in "[{":
        return []
    payloads: list[Any]
    try:
        root = json.loads(text)
        payloads = root if isinstance(root, list) else [root]
    except json.JSONDecodeError:
        payloads = []
        for line in text.splitlines():
            if not line.strip():
                continue
            try:
                payloads.append(json.loads(line))
            except json.JSONDecodeError:
                return []
    records: list[dict[str, Any]] = []
    for payload in payloads:
        if not isinstance(payload, dict):
            return []
        name = next(
            (
                payload.get(key)
                for key in ("remoteName", "relativePath", "path", "name")
                if isinstance(payload.get(key), str) and payload.get(key)
            ),
            None,
        )
        digest_name = next(
            (
                key
                for key in ("sha256", "md5", "hash", "digest")
                if isinstance(payload.get(key), str) and payload.get(key)
            ),
            None,
        )
        digest = payload.get(digest_name) if digest_name else None
        size = next(
            (
                payload.get(key)
                for key in ("fileSize", "size", "bytes")
                if isinstance(payload.get(key), int)
                and not isinstance(payload.get(key), bool)
                and payload.get(key) >= 0
            ),
            None,
        )
        if name is None or digest is None or size is None:
            return []
        normalized = str(name).replace("\\", "/")
        relative = Path(normalized)
        if relative.is_absolute() or ".." in relative.parts:
            return []
        records.append(
            {
                "path": normalized,
                "digest": digest.lower(),
                "digest_algorithm": digest_name,
                "bytes": size,
            }
        )
    if len({record["path"].casefold() for record in records}) != len(records):
        return []
    return records


def _digest(path: Path, algorithm: str) -> str:
    if algorithm == "sha256":
        return sha256_file(path)
    if algorithm != "md5":
        raise AcquisitionError(f"unsupported package anchor digest: {algorithm}")
    value = hashlib.md5(usedforsecurity=False)
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def collect_package(
    context: CollectionContext, target: TargetIdentity, client: Evidence
) -> tuple[Evidence, Evidence]:
    candidates: list[tuple[Path, list[dict[str, Any]]]] = []
    for path in context.game_dir.expanduser().resolve().iterdir():
        if path.is_file() and not path.is_symlink():
            records = _manifest_records(path)
            if len(records) >= 2:
                candidates.append((path.resolve(), records))
    if len(candidates) != 1:
        raise AcquisitionError(
            f"package manifest selection must be unique, observed {len(candidates)}"
        )
    manifest, records = candidates[0]
    canonical_records = sorted(records, key=lambda item: item["path"].casefold())
    executable = Path(target.executable_path)
    data_dir = executable.parent / f"{executable.stem}_Data"
    anchors = {
        executable.relative_to(context.game_dir.resolve()).as_posix(): executable,
        (data_dir / "globalgamemanagers").relative_to(context.game_dir.resolve()).as_posix(): (
            data_dir / "globalgamemanagers"
        ),
    }
    by_path = {record["path"].casefold(): record for record in canonical_records}
    verified_anchors: list[dict[str, Any]] = []
    for relative, path in anchors.items():
        record = by_path.get(relative.casefold())
        if record is None or record["bytes"] != path.stat().st_size:
            raise AcquisitionError(f"package manifest does not bind current anchor: {relative}")
        algorithm = record["digest_algorithm"]
        if algorithm not in {"sha256", "md5"} or _digest(path, algorithm) != record["digest"]:
            raise AcquisitionError(f"package anchor digest mismatch: {relative}")
        verified_anchors.append(
            {
                "path": relative,
                "bytes": record["bytes"],
                "digest_algorithm": algorithm,
                "digest": record["digest"],
            }
        )
    package_content_id = generation_id("package-content", canonical_records)
    runtime = _active_runtime_identity(Path(target.executable_path))
    package = Evidence(
        kind="package_runtime",
        target_version=target.client_version,
        target_executable_sha256=target.executable_sha256,
        source={"manifest": file_identity(manifest), "client_generation": client.id},
        facts={
            "package_content_id": package_content_id,
            "manifest_entry_count": len(canonical_records),
            "verified_package_anchors": verified_anchors,
            "verified_package_anchor_count": len(verified_anchors),
            "runtime": runtime,
            "runtime_observed": bool(runtime["executables"]),
        },
        references={"client": client.id},
        provider="alpha.builtin.package-runtime",
    )
    resource_records = [
        record
        for record in canonical_records
        if any(part.casefold() == "streamingassets" for part in Path(record["path"]).parts)
    ]
    if not resource_records:
        raise AcquisitionError("package manifest has no resource/cache identity records")
    resources = Evidence(
        kind="resource_cache_identity",
        target_version=target.client_version,
        target_executable_sha256=target.executable_sha256,
        source={"manifest": file_identity(manifest)},
        facts={
            "resource_content_id": generation_id("resource-content", resource_records),
            "resource_entry_count": len(resource_records),
            "package_content_id": package_content_id,
        },
        references={"package_runtime": package.id},
        provider="alpha.builtin.resource-cache",
    )
    return package, resources


def _active_runtime_identity(executable: Path) -> dict[str, Any]:
    try:
        process = subprocess.run(
            ["ps", "-axo", "pid=,command="],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            text=True, encoding="utf-8", errors="replace",
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise AcquisitionError("cannot inspect active runtime") from error
    binaries: dict[str, dict[str, Any]] = {}
    process_count = 0
    for row in process.stdout.splitlines():
        command = row.strip().partition(" ")[2]
        if not process_command_is_target_runtime(command, executable):
            continue
        process_count += 1


        target_identity = file_identity(executable)
        binaries[target_identity["sha256"]] = target_identity
        token = command.split(maxsplit=1)[0] if command else ""
        candidate = Path(token)
        if candidate.is_absolute() and candidate.is_file() and not candidate.is_symlink():
            identity = file_identity(candidate)
            binaries[identity["sha256"]] = identity
    return {
        "process_count": process_count,
        "executables": sorted(binaries.values(), key=lambda item: item["sha256"]),
    }


def process_command_is_target_runtime(command: str, executable: Path) -> bool:

    exact = str(executable.expanduser().resolve())
    try:
        tokens = shlex.split(command)
    except ValueError:
        tokens = []
    if tokens and tokens[0] == exact:
        return True

    collapsed = re.sub(r"\\+", r"\\", command.strip())
    windows_suffix = exact.replace("/", "\\")
    target = rf"[A-Za-z]:{re.escape(windows_suffix)}(?:\s|$)"
    if re.match(rf"^{target}", collapsed, re.IGNORECASE):
        return True
    return bool(
        re.match(
            rf"^[A-Za-z]:\\windows\\system32\\steam\.exe\s+{target}",
            collapsed,
            re.IGNORECASE,
        )
    )


def _semantic_versions(path: Path, content_prefix: str = "") -> set[str]:
    values = set(SEMVER.findall(str(path)))
    values.update(SEMVER.findall(content_prefix))
    return values


def _json_shape(path: Path) -> str | None:
    try:
        payload = read_json(path, maximum_bytes=128 * 1024 * 1024)
    except AcquisitionError:
        return None
    if isinstance(payload, dict) and len(payload) >= 32:
        if all(isinstance(key, str) for key in payload) and sum(
            isinstance(value, int) and not isinstance(value, bool)
            for value in payload.values()
        ) >= len(payload) * 0.8:
            return "packet_ids"
    if isinstance(payload, (dict, list)):
        sample = json.dumps(payload if isinstance(payload, list) else list(payload)[:32])
        if any(marker in sample.casefold() for marker in ("field", "class", "method")):
            return "class_metadata"
    return None


def _current_il2cpp_proto_source(
    target: TargetIdentity, *, unmatched_proto_bundle_count: int | None = None
) -> Evidence:

    executable = Path(target.executable_path)
    data_dir = executable.parent / f"{executable.stem}_Data"
    metadata = [
        path.resolve()
        for path in data_dir.rglob("global-metadata.dat")
        if path.is_file() and not path.is_symlink()
    ]
    metadata_groups: dict[str, list[Path]] = {}
    for path in metadata:
        metadata_groups.setdefault(sha256_file(path), []).append(path)
    if len(metadata_groups) != 1:
        raise AcquisitionError(
            f"IL2CPP metadata content must be unique, observed {len(metadata_groups)} identities"
        )
    metadata_sha256, mirrors = next(iter(metadata_groups.items()))
    metadata_identity = {
        "sha256": metadata_sha256,
        "bytes": mirrors[0].stat().st_size,
        "mirror_paths": sorted(str(path) for path in mirrors),
        "mirror_count": len(mirrors),
    }
    facts: dict[str, Any] = {
        "source_version": target.client_version,
        "source_kind": "current-client-il2cpp-pair",
        "extracted_proto_available": False,


        "opcode_and_field_single_generation": False,
        "compatibility_fallback_used": False,
        "derived_protocol_must_reference_this_generation": True,
    }
    if unmatched_proto_bundle_count is not None:
        facts["exact_proto_bundle_candidate_count"] = unmatched_proto_bundle_count
    return Evidence(
        kind="proto",
        target_version=target.client_version,
        target_executable_sha256=target.executable_sha256,
        source={
            "il2cpp_executable": file_identity(executable),
            "il2cpp_metadata": metadata_identity,
        },
        facts=facts,
        provider="alpha.builtin.il2cpp-proto-source",
    )


def collect_proto(context: CollectionContext, target: TargetIdentity) -> Evidence | None:
    if not context.proto_roots:
        return _current_il2cpp_proto_source(target)
    protos: list[Path] = []
    jsons: list[tuple[Path, str]] = []
    for root in context.proto_roots:
        root = root.expanduser().resolve()
        if not root.is_dir():
            raise AcquisitionError(f"proto discovery root is not a directory: {root}")
        for path in root.rglob("*"):
            if path.is_symlink() or not path.is_file():
                continue
            if path.suffix.casefold() == ".proto" and path.stat().st_size <= 128 * 1024 * 1024:
                protos.append(path.resolve())
            elif path.suffix.casefold() == ".json":
                shape = _json_shape(path)
                if shape:
                    jsons.append((path.resolve(), shape))
    bundles: list[tuple[Path, Path, Path]] = []
    for proto in protos:
        prefix = proto.read_text(encoding="utf-8", errors="ignore")[:2 * 1024 * 1024]
        versions = _semantic_versions(proto, prefix)
        if versions != {target.client_version}:
            continue
        packet_ids = [
            path for path, shape in jsons
            if shape == "packet_ids" and _semantic_versions(path) in ({target.client_version}, set())
        ]
        class_metadata = [
            path for path, shape in jsons
            if shape == "class_metadata" and _semantic_versions(path) in ({target.client_version}, set())
        ]
        if len(packet_ids) == 1 and len(class_metadata) == 1:
            bundles.append((proto, packet_ids[0], class_metadata[0]))
    if not bundles:
        return _current_il2cpp_proto_source(
            target, unmatched_proto_bundle_count=len(bundles)
        )
    if len(bundles) != 1:
        raise AcquisitionError(
            f"exact-version proto bundle must be unique, observed {len(bundles)}"
        )
    proto, packet_ids, class_metadata = bundles[0]
    members = {
        "proto": file_identity(proto),
        "packet_ids": file_identity(packet_ids),
        "class_metadata": file_identity(class_metadata),
    }
    return Evidence(
        kind="proto",
        target_version=target.client_version,
        target_executable_sha256=target.executable_sha256,
        source=members,
        facts={
            "source_version": target.client_version,
            "source_kind": "exact-version-proto-bundle",
            "extracted_proto_available": True,
            "bundle_member_count": 3,
            "opcode_and_field_single_generation": True,
            "compatibility_fallback_used": False,
        },
        provider="alpha.builtin.proto-bundle",
    )


def collect_rsa(context: CollectionContext, target: TargetIdentity) -> Evidence | None:
    if not context.rsa_roots:
        executable = Path(target.executable_path)
        identities = public_identities_in_binary(executable)
        return Evidence(
            kind="rsa",
            target_version=target.client_version,
            target_executable_sha256=target.executable_sha256,
            source={"client_executable": file_identity(executable)},
            facts={
                "embedded_public_identity_count": len(identities),
                "embedded_public_identities": identities,
                "roles_bound_by_runtime_observation": False,
                "raw_key_material_withheld": True,
            },
            provider="alpha.builtin.rsa-embedded-source",
        )
    groups: dict[str, dict[str, Any]] = {}
    for root in context.rsa_roots:
        root = root.expanduser().resolve()
        if not root.is_dir():
            raise AcquisitionError(f"RSA discovery root is not a directory: {root}")
        for path in root.rglob("*"):
            if (
                path.is_symlink()
                or not path.is_file()
                or path.stat().st_size > 64 * 1024
                or path.suffix.casefold() not in {".pem", ".der", ".key", ".rsa"}
            ):
                continue
            try:
                parsed = public_identity(path)
            except AcquisitionError:
                continue
            public_sha256, private = parsed
            group = groups.setdefault(
                public_sha256,
                {"public_key_sha256": public_sha256, "private_count": 0, "artifact_count": 0},
            )
            group["artifact_count"] += 1
            group["private_count"] += int(private)
    paired = [group for group in groups.values() if group["private_count"] == 1]
    if len(paired) != 1:
        raise AcquisitionError(
            f"runtime-selected RSA generation must be unique, observed {len(paired)}"
        )
    return Evidence(
        kind="rsa",
        target_version=target.client_version,
        target_executable_sha256=target.executable_sha256,
        source={"discovery_root_count": len(context.rsa_roots)},
        facts={
            "key_pairs": paired,
            "roles_bound_by_runtime_observation": False,
            "raw_key_material_withheld": True,
        },
        provider="alpha.builtin.rsa-structural",
    )


def load_receipts(context: CollectionContext, target: TargetIdentity) -> list[Evidence]:
    evidence: list[Evidence] = []
    for root in context.evidence_roots:
        root = root.expanduser().resolve()
        if not root.is_dir():
            raise AcquisitionError(f"evidence root is not a directory: {root}")
        for path in root.rglob("*.json"):
            if path.is_symlink() or not path.is_file() or path.stat().st_size > 16 * 1024 * 1024:
                continue
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                continue
            if not isinstance(payload, dict) or payload.get("schema") != "alpha.evidence/v1":
                continue
            item = Evidence.from_dict(payload)
            if (
                item.target_version == target.client_version
                and item.target_executable_sha256 == target.executable_sha256
            ):
                evidence.append(item)
    return evidence


def load_foundation_receipts(
    context: CollectionContext, target: TargetIdentity
) -> list[Evidence]:

    foundation_kinds = {
        "client",
        "package_runtime",
        "resource_cache_identity",
        "redirect_profile",
    }
    evidence: list[Evidence] = []
    for root in context.evidence_roots:
        root = root.expanduser().resolve()
        if not root.is_dir() or root.is_symlink():
            raise AcquisitionError(f"foundation evidence root is not a directory: {root}")
        for kind in sorted(foundation_kinds):
            path = root / f"{kind}.json"
            if not path.is_file() or path.is_symlink() or path.stat().st_size > 16 * 1024 * 1024:
                continue
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError, json.JSONDecodeError):
                continue
            if not isinstance(payload, dict) or payload.get("schema") != "alpha.evidence/v1":
                continue
            item = Evidence.from_dict(payload)
            if (
                item.kind == kind
                and item.target_version == target.client_version
                and item.target_executable_sha256 == target.executable_sha256
            ):
                evidence.append(item)
    return evidence


def load_plugin_evidence(
    context: CollectionContext, target: TargetIdentity
) -> list[Evidence]:
    result: list[Evidence] = []
    for entry in importlib.metadata.entry_points(group="alpha.providers"):
        provider = entry.load()()
        for evidence in provider.collect(context, target):
            if not isinstance(evidence, Evidence):
                raise ContractViolation(f"provider {entry.name} returned a non-Evidence value")
            result.append(evidence)
    return result


def make_redirect_profile(
    target: TargetIdentity, client: Evidence, package: Evidence
) -> Evidence:
    routing_identity = {
        "target_executable_sha256": target.executable_sha256,
        "package_generation": package.id,
        "path_binding": str(Path(target.executable_path).resolve()),
        "selection_policy": "exact-executable-content-addressed",
    }
    return Evidence(
        kind="redirect_profile",
        target_version=target.client_version,
        target_executable_sha256=target.executable_sha256,
        source={"generated_from": [client.id, package.id]},
        facts={
            "routing_identity": routing_identity,
            "legacy_profile_used": False,
            "version_only_selection": False,
            "fresh_route_observed": False,
            "official_route_unmodified": False,
            "route_selector_applied": False,
            "route_redirection_applied": False,
            "token_or_rsa_actions_started": False,
            "raw_values_withheld": True,
        },
        references={"client": client.id, "package_runtime": package.id},
        provider="alpha.builtin.redirect-profile",
    )


def collect(context: CollectionContext) -> tuple[TargetIdentity, list[Evidence]]:
    target, client = collect_target(context)
    package, resources = collect_package(context, target, client)
    evidence: list[Evidence] = [client, package, resources]
    supplied = load_receipts(context, target) + load_plugin_evidence(context, target)
    supplied_kinds = {item.kind for item in supplied}
    proto = None if "proto" in supplied_kinds else collect_proto(context, target)
    if proto is not None and "proto" not in supplied_kinds:
        evidence.append(proto)
    rsa = None if "rsa" in supplied_kinds else collect_rsa(context, target)
    if rsa is not None:
        evidence.append(rsa)
    evidence.extend(supplied)
    if "redirect_profile" not in supplied_kinds:
        evidence.append(make_redirect_profile(target, client, package))
    return target, evidence


def collect_foundation(context: CollectionContext) -> tuple[TargetIdentity, list[Evidence]]:

    target, client = collect_target(context)
    supplied = load_foundation_receipts(context, target)
    if supplied:
        expected_kinds = {
            "client",
            "package_runtime",
            "resource_cache_identity",
            "redirect_profile",
        }
        grouped: dict[str, dict[str, Evidence]] = {kind: {} for kind in expected_kinds}
        for item in supplied:
            grouped[item.kind][item.id] = item
        missing = sorted(kind for kind, values in grouped.items() if not values)
        ambiguous = sorted(kind for kind, values in grouped.items() if len(values) > 1)
        if missing or ambiguous:
            details = []
            if missing:
                details.append("missing=" + ",".join(missing))
            if ambiguous:
                details.append("ambiguous=" + ",".join(ambiguous))
            raise AcquisitionError("foundation receipts are incomplete: " + "; ".join(details))
        selected = {kind: next(iter(values.values())) for kind, values in grouped.items()}
        return target, [selected[kind] for kind in sorted(selected)]
    package, resources = collect_package(context, target, client)
    redirect = make_redirect_profile(target, client, package)
    return target, [client, package, resources, redirect]
