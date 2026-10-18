import os
from pathlib import Path

from alpha.h01 import AcquisitionError


def _windows_path(
    path: Path,
    *,
    native_windows: bool | None = None,
    resolve: bool = True,
) -> str:
    if native_windows is None:
        native_windows = os.name == "nt"
    path = path.expanduser()


    path = path.resolve() if resolve else path.absolute()
    if not path.is_absolute():
        raise AcquisitionError("runtime artifact path must be absolute")
    if native_windows:
        return str(path)
    return "Z:" + str(path).replace("/", "\\")


def windows_run(
    wine,
    *arguments,
    _native_windows: bool | None = None,
    _resolve_paths: bool = True,
) -> list[str]:
    if _native_windows is None:
        _native_windows = os.name == "nt"
    converted: list[str] = []
    for item in arguments:
        text = str(item)
        if os.path.isabs(text) or "/" in text or "\\" in text:
            path = Path(text)
            converted.append(
                _windows_path(
                    path,
                    native_windows=_native_windows,
                    resolve=_resolve_paths,
                )
            )
        else:
            converted.append(text)
    if _native_windows:
        return converted
    return [str(Path(wine).expanduser().resolve()), *converted]


import datetime as dt
import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError


def _u16(data: bytes, offset: int) -> int:
    return struct.unpack_from("<H", data, offset)[0]


def _u32(data: bytes, offset: int) -> int:
    return struct.unpack_from("<I", data, offset)[0]


def inspect_pe(path: Path) -> dict[str, Any]:

    path = path.expanduser().resolve()
    try:
        data = path.read_bytes()
    except OSError as error:
        raise AcquisitionError(f"cannot read executable: {path}") from error
    if len(data) < 0x100 or data[:2] != b"MZ":
        raise AcquisitionError("selected executable is not PE/MZ")
    pe_offset = _u32(data, 0x3C)
    if pe_offset + 24 >= len(data) or data[pe_offset : pe_offset + 4] != b"PE\0\0":
        raise AcquisitionError("invalid PE header")
    coff = pe_offset + 4
    machine = _u16(data, coff)
    section_count = _u16(data, coff + 2)
    timestamp = _u32(data, coff + 4)
    optional_size = _u16(data, coff + 16)
    optional = coff + 20
    magic = _u16(data, optional)
    if magic not in {0x10B, 0x20B}:
        raise AcquisitionError("unsupported PE optional header")
    data_directories = optional + (112 if magic == 0x20B else 96)
    resource_rva = _u32(data, data_directories + 16)
    resource_size = _u32(data, data_directories + 20)
    section_table = optional + optional_size
    sections: list[tuple[int, int, int]] = []
    for index in range(section_count):
        offset = section_table + index * 40
        if offset + 40 > len(data):
            raise AcquisitionError("truncated PE section table")
        virtual_size = _u32(data, offset + 8)
        virtual_address = _u32(data, offset + 12)
        raw_size = _u32(data, offset + 16)
        raw_pointer = _u32(data, offset + 20)
        sections.append((virtual_address, max(virtual_size, raw_size), raw_pointer))

    def rva_to_raw(rva: int) -> int:
        for virtual_address, size, raw_pointer in sections:
            if virtual_address <= rva < virtual_address + size:
                return raw_pointer + (rva - virtual_address)
        raise AcquisitionError(f"unmapped PE RVA: {rva:#x}")

    versions: list[dict[str, Any]] = []
    if resource_rva and resource_size:
        base = rva_to_raw(resource_rva)

        def directory_entries(relative: int) -> list[tuple[int, bool, int, bool]]:
            offset = base + relative
            if offset + 16 > len(data):
                raise AcquisitionError("truncated PE resource directory")
            named = _u16(data, offset + 12)
            identified = _u16(data, offset + 14)
            result: list[tuple[int, bool, int, bool]] = []
            for index in range(named + identified):
                entry = offset + 16 + index * 8
                name = _u32(data, entry)
                target = _u32(data, entry + 4)
                result.append(
                    (
                        name & 0xFFFF,
                        bool(name & 0x80000000),
                        target & 0x7FFFFFFF,
                        bool(target & 0x80000000),
                    )
                )
            return result

        roots = [
            entry
            for entry in directory_entries(0)
            if not entry[1] and entry[0] == 16 and entry[3]
        ]
        for root in roots:
            for name in directory_entries(root[2]):
                if not name[3]:
                    continue
                for language in directory_entries(name[2]):
                    if language[3]:
                        continue
                    entry = base + language[2]
                    if entry + 16 > len(data):
                        raise AcquisitionError("truncated PE resource data entry")
                    value_rva, value_size = struct.unpack_from("<II", data, entry)
                    raw = rva_to_raw(value_rva)
                    blob = data[raw : raw + value_size]
                    signature = blob.find(struct.pack("<I", 0xFEEF04BD))
                    if signature < 0 or signature + 52 > len(blob):
                        continue
                    fixed = struct.unpack_from("<13I", blob, signature)

                    def version(ms: int, ls: int) -> str:
                        return f"{ms >> 16}.{ms & 0xFFFF}.{ls >> 16}.{ls & 0xFFFF}"

                    versions.append(
                        {
                            "resource_id": name[0],
                            "language_id": language[0],
                            "file_version": version(fixed[2], fixed[3]),
                            "product_version": version(fixed[4], fixed[5]),
                        }
                    )
    return {
        "machine": f"0x{machine:04x}",
        "pe_format": "PE32+" if magic == 0x20B else "PE32",
        "coff_timestamp": timestamp,
        "coff_timestamp_utc": dt.datetime.fromtimestamp(
            timestamp, tz=dt.timezone.utc
        ).isoformat(),
        "version_resources": versions,
    }


import base64
import hashlib
import mmap
import re
from dataclasses import dataclass
from pathlib import Path

from alpha.h01 import AcquisitionError


PEM = re.compile(
    rb"-----BEGIN ([A-Z0-9 ]+)-----\s+([A-Za-z0-9+/=\r\n]+?)\s+-----END \1-----",
    re.DOTALL,
)


@dataclass(frozen=True)
class Tlv:
    tag: int
    value: bytes
    encoded: bytes


def _read_tlv(data: bytes, offset: int = 0) -> tuple[Tlv, int]:
    if offset >= len(data):
        raise AcquisitionError("truncated DER tag")
    start = offset
    tag = data[offset]
    offset += 1
    if offset >= len(data):
        raise AcquisitionError("truncated DER length")
    first = data[offset]
    offset += 1
    if first < 0x80:
        length = first
    else:
        count = first & 0x7F
        if not 1 <= count <= 4 or offset + count > len(data):
            raise AcquisitionError("unsupported DER length")
        length = int.from_bytes(data[offset : offset + count], "big")
        offset += count
    end = offset + length
    if end > len(data):
        raise AcquisitionError("truncated DER value")
    return Tlv(tag, data[offset:end], data[start:end]), end


def _children(sequence: bytes) -> list[Tlv]:
    result: list[Tlv] = []
    offset = 0
    while offset < len(sequence):
        item, offset = _read_tlv(sequence, offset)
        result.append(item)
    return result


def _integer(item: Tlv) -> int:
    if item.tag != 0x02 or not item.value:
        raise AcquisitionError("RSA component is not an INTEGER")
    return int.from_bytes(item.value, "big", signed=False)


def _pem_or_der(path: Path) -> tuple[bytes, str]:
    data = path.read_bytes()
    match = PEM.search(data)
    if not match:
        return data, "DER"
    try:
        return base64.b64decode(re.sub(rb"\s+", b"", match.group(2)), validate=True), match.group(1).decode("ascii")
    except (ValueError, UnicodeDecodeError) as error:
        raise AcquisitionError(f"invalid PEM: {path}") from error


def _rsa_components(der: bytes) -> tuple[int, int, bool]:
    outer, end = _read_tlv(der)
    if end != len(der) or outer.tag != 0x30:
        raise AcquisitionError("RSA artifact is not one DER SEQUENCE")
    items = _children(outer.value)


    if len(items) >= 9 and items[0].tag == items[1].tag == items[2].tag == 0x02:
        return _integer(items[1]), _integer(items[2]), True


    if len(items) == 2 and items[0].tag == items[1].tag == 0x02:
        return _integer(items[0]), _integer(items[1]), False


    if len(items) >= 3 and items[0].tag == 0x02 and items[1].tag == 0x30 and items[2].tag == 0x04:
        modulus, exponent, _ = _rsa_components(items[2].value)
        return modulus, exponent, True


    if len(items) == 2 and items[0].tag == 0x30 and items[1].tag == 0x03 and items[1].value[:1] == b"\0":
        modulus, exponent, _ = _rsa_components(items[1].value[1:])
        return modulus, exponent, False
    raise AcquisitionError("unrecognized RSA DER container")


def public_identity(path: Path) -> tuple[str, bool]:

    der, _ = _pem_or_der(path)
    modulus, exponent, private = _rsa_components(der)
    if modulus.bit_length() < 1024 or exponent < 3 or exponent % 2 == 0:
        raise AcquisitionError("invalid RSA public components")
    modulus_bytes = modulus.to_bytes((modulus.bit_length() + 7) // 8, "big")
    exponent_bytes = exponent.to_bytes((exponent.bit_length() + 7) // 8, "big")
    material = (
        len(modulus_bytes).to_bytes(4, "big")
        + modulus_bytes
        + len(exponent_bytes).to_bytes(4, "big")
        + exponent_bytes
    )
    return hashlib.sha256(material).hexdigest(), private


def public_identities_in_binary(path: Path, *, maximum_der_bytes: int = 8192) -> list[str]:

    identities: set[str] = set()
    with path.open("rb") as source, mmap.mmap(source.fileno(), 0, access=mmap.ACCESS_READ) as data:
        offset = 0
        while True:
            offset = data.find(b"\x30\x82", offset)
            if offset < 0:
                break
            if offset + 4 <= len(data):
                length = int.from_bytes(data[offset + 2 : offset + 4], "big") + 4
                if 16 <= length <= maximum_der_bytes and offset + length <= len(data):
                    candidate = bytes(data[offset : offset + length])
                    try:
                        modulus, exponent, private = _rsa_components(candidate)
                        if not private and modulus.bit_length() >= 1024 and exponent >= 3 and exponent % 2:
                            modulus_bytes = modulus.to_bytes((modulus.bit_length() + 7) // 8, "big")
                            exponent_bytes = exponent.to_bytes((exponent.bit_length() + 7) // 8, "big")
                            material = (
                                len(modulus_bytes).to_bytes(4, "big")
                                + modulus_bytes
                                + len(exponent_bytes).to_bytes(4, "big")
                                + exponent_bytes
                            )
                            identities.add(hashlib.sha256(material).hexdigest())
                    except AcquisitionError:
                        pass
            offset += 2
    return sorted(identities)


import ctypes
import os
from pathlib import Path
import sys
import tempfile
import json

from alpha.h01 import AcquisitionError


def _publish_new_path(source: Path, destination: Path, *, directory: bool) -> None:

    if not (source.is_dir() if directory else source.is_file()):
        kind = "directory" if directory else "regular file"
        raise AcquisitionError(f"runtime staging source must be a {kind} beside its destination")
    try:
        if sys.platform == "darwin":
            library = ctypes.CDLL(None, use_errno=True)
            rename = library.renamex_np
            rename.argtypes = (ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint)
            rename.restype = ctypes.c_int
            if rename(os.fsencode(source), os.fsencode(destination), 0x00000004):
                error = ctypes.get_errno()
                raise OSError(error, os.strerror(error), str(destination))
        elif os.name == "nt":

            os.rename(source, destination)
        elif not directory:
            os.link(source, destination)
        else:
            raise AcquisitionError("filesystem has no supported exclusive directory publication primitive")
    except FileExistsError as error:
        raise AcquisitionError("runtime output appeared during staging; existing file preserved") from error
    except (OSError, AttributeError) as error:
        raise AcquisitionError("filesystem cannot publish this new artifact atomically without replacement") from error


def publish_new_file(source: Path, destination: Path) -> None:
    _publish_new_path(source, destination, directory=False)


def publish_new_directory(source: Path, destination: Path) -> None:

    _publish_new_path(source, destination, directory=True)


def write_new_bytes(path: Path, value: bytes) -> None:
    path.parent.mkdir(mode=0o700, parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(descriptor, "wb") as output:
            output.write(value)
            output.flush()
            os.fsync(output.fileno())
        publish_new_file(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def write_new_json(path: Path, value) -> None:
    write_new_bytes(path, (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2, allow_nan=False) + "\n").encode("utf-8"))


def write_new_text(path: Path, value: str) -> None:
    write_new_bytes(path, value.encode("utf-8"))


import re
from pathlib import Path

from alpha.h01 import AcquisitionError


BUILD_MARKER = re.compile(
    rb"(?<![0-9])([0-9]+\.[0-9]+\.[0-9]+(?:_[0-9]+)+)(?![0-9])"
)


def bundle_version(global_managers: Path) -> dict[str, str]:

    try:
        data = global_managers.read_bytes()
    except OSError as error:
        raise AcquisitionError(f"cannot read Unity metadata: {global_managers}") from error
    markers = {match.group(1).decode("ascii") for match in BUILD_MARKER.finditer(data)}
    versions = {marker.partition("_")[0] for marker in markers}
    if len(markers) == 1 and len(versions) == 1:
        return {
            "version": versions.pop(),
            "build": markers.pop(),
            "authority": "unique-globalgamemanagers-build-marker",
        }

    try:
        import UnityPy
    except ImportError as error:
        raise AcquisitionError(
            "current Unity metadata has no unique dependency-free build marker"
        ) from error
    typed_error: Exception | None = None
    try:
        environment = UnityPy.load(str(global_managers))
        values: set[str] = set()
        for item in environment.objects:
            if item.type.name != "PlayerSettings":
                continue
            tree = item.read_typetree()
            for name in ("bundleVersion", "m_BundleVersion"):
                value = tree.get(name)
                if isinstance(value, str) and value.strip():
                    values.add(value.strip())
        if len(values) == 1:
            value = values.pop()
            return {"version": value, "build": value, "authority": "typed-player-settings"}
        typed_error = AcquisitionError(
            f"Unity bundleVersion must be unique, observed {len(values)} values"
        )
    except Exception as error:
        typed_error = error

    raise AcquisitionError(
        "cannot acquire a unique Unity client version/build from current metadata"
    ) from typed_error


import hashlib
import json
import os
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import Any, Iterable

from alpha.h01 import AcquisitionError


_FILE_HASH_CACHE: dict[str, tuple[tuple[int, int, int, int, int], str]] = {}
_FILE_HASH_LOCK = threading.Lock()
_FILE_HASH_INFLIGHT: dict[str, threading.Event] = {}
_FILE_HASH_MEMO_DIR: Path | None = None
_FILE_HASH_MEMO_READS_DISABLED = False
_FILE_HASH_MEMO_SCHEMA = "alpha.file-hash-memo/v1"
_FILE_HASH_MEMO_KEEP = 64
_FILE_HASH_MEMO_MINIMUM_BYTES = 1 << 20


def set_file_hash_memo_dir(path: Path | None) -> None:
    global _FILE_HASH_MEMO_DIR
    _FILE_HASH_MEMO_DIR = (
        Path(path).expanduser().resolve() if path is not None else None
    )


def _file_hash_memo_path(key: str) -> Path | None:
    if _FILE_HASH_MEMO_DIR is None:
        return None
    digest = hashlib.sha256(key.encode("utf-8")).hexdigest()[:32]
    return _FILE_HASH_MEMO_DIR / f"filehash-{digest}.meta.json"


def _load_file_hash_memo_entry(
    key: str, fingerprint: tuple[int, int, int, int, int]
) -> str | None:
    path = _file_hash_memo_path(key)
    if path is None:
        return None
    try:
        meta = read_json(path, maximum_bytes=1 << 16)
        if (
            meta.get("schema") != _FILE_HASH_MEMO_SCHEMA
            or meta.get("path") != key
            or meta.get("fingerprint") != list(fingerprint)
            or type(meta.get("sha256")) is not str
            or len(meta["sha256"]) != 64
        ):
            return None
        return meta["sha256"]
    except (AcquisitionError, OSError, ValueError, TypeError, KeyError):

        return None


def _store_file_hash_memo_entry(
    key: str,
    fingerprint: tuple[int, int, int, int, int],
    digest: str,
) -> None:
    path = _file_hash_memo_path(key)
    if path is None:
        return
    try:
        path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        descriptor, temporary = tempfile.mkstemp(
            prefix=f".{path.name}.", dir=path.parent
        )
        try:
            os.fchmod(descriptor, 0o600)
            with os.fdopen(descriptor, "w", encoding="utf-8") as sink:
                json.dump(
                    {
                        "schema": _FILE_HASH_MEMO_SCHEMA,
                        "path": key,
                        "fingerprint": list(fingerprint),
                        "sha256": digest,
                    },
                    sink,
                    sort_keys=True,
                )
                sink.flush()
                os.fsync(sink.fileno())
            os.replace(temporary, path)
            path.chmod(0o600)
        except BaseException:
            Path(temporary).unlink(missing_ok=True)
            raise
    except OSError:
        return
    try:
        records = []
        for stale in _FILE_HASH_MEMO_DIR.glob("filehash-*.meta.json"):
            if stale.is_file():
                records.append((stale.stat().st_mtime_ns, stale))
        for _, stale in sorted(records, reverse=True)[_FILE_HASH_MEMO_KEEP:]:
            stale.unlink(missing_ok=True)
    except OSError:
        return


def _file_fingerprint(path: Path) -> tuple[int, int, int, int, int]:
    try:
        status = path.stat()
    except OSError as error:
        raise AcquisitionError(f"unreadable file: {path}") from error
    return (
        status.st_dev, status.st_ino, status.st_size,
        status.st_mtime_ns, status.st_ctime_ns,
    )


def clear_file_hash_cache() -> None:
    global _FILE_HASH_MEMO_READS_DISABLED
    with _FILE_HASH_LOCK:
        _FILE_HASH_CACHE.clear()
        _FILE_HASH_INFLIGHT.clear()


    _FILE_HASH_MEMO_READS_DISABLED = True


_HASH_BLOCK_BYTES = 8 * 1024 * 1024
_HASH_PREFETCH_MINIMUM_BYTES = 256 * 1024 * 1024
_HASH_PREFETCH_WORKERS = 4


def _hash_file_sequential(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(_HASH_BLOCK_BYTES), b""):
            digest.update(block)
    return digest.hexdigest()


def _read_full(fd: int, offset: int, length: int) -> bytes:
    block = os.pread(fd, length, offset)
    if len(block) == length:
        return block
    chunks = [block]
    cursor = offset + len(block)
    while True:
        piece = os.pread(fd, offset + length - cursor, cursor)
        if not piece:
            break
        chunks.append(piece)
        cursor += len(piece)
    return b"".join(chunks)


def _hash_file_prefetched(path: Path, size: int) -> str:
    workers = _HASH_PREFETCH_WORKERS
    pread = getattr(os, "pread", None)
    if workers < 2 or not callable(pread):
        return _hash_file_sequential(path)
    offsets = list(range(0, size, _HASH_BLOCK_BYTES))

    def read_at(offset: int) -> bytes:
        descriptor = os.open(path, os.O_RDONLY)
        try:
            return _read_full(descriptor, offset, min(_HASH_BLOCK_BYTES, size - offset))
        finally:
            os.close(descriptor)

    digest = hashlib.sha256()


    window = 2 * workers
    with ThreadPoolExecutor(max_workers=workers) as executor:
        pending = [executor.submit(read_at, offset) for offset in offsets[:window]]
        cursor = window
        for index, offset in enumerate(offsets):
            slot = index % window
            digest.update(pending[slot].result())
            if cursor < len(offsets):
                pending[slot] = executor.submit(read_at, offsets[cursor])
                cursor += 1
    return digest.hexdigest()


def _hash_file(path: Path, size: int) -> str:
    if (
        size >= _HASH_PREFETCH_MINIMUM_BYTES
        and _HASH_PREFETCH_WORKERS > 1
        and hasattr(os, "pread")
    ):
        return _hash_file_prefetched(path, size)
    return _hash_file_sequential(path)


def sha256_file(path: Path, *, maximum_bytes: int | None = None) -> str:
    path = path.expanduser().resolve()
    try:
        size = path.stat().st_size
    except OSError as error:
        raise AcquisitionError(f"unreadable file: {path}") from error
    if not path.is_file() or path.is_symlink():
        raise AcquisitionError(f"not a regular file: {path}")
    if maximum_bytes is not None and size > maximum_bytes:
        raise AcquisitionError(f"file exceeds acquisition limit: {path}")
    key = str(path)
    try:
        fingerprint = _file_fingerprint(path)
    except AcquisitionError:
        raise
    with _FILE_HASH_LOCK:
        cached = _FILE_HASH_CACHE.get(key)
        if cached is not None and cached[0] == fingerprint:
            return cached[1]
        inflight = _FILE_HASH_INFLIGHT.get(key)
        if inflight is None:
            inflight = threading.Event()
            _FILE_HASH_INFLIGHT[key] = inflight
            owner = True
        else:
            owner = False
    if not owner:


        inflight.wait()
        with _FILE_HASH_LOCK:
            cached = _FILE_HASH_CACHE.get(key)
            if cached is not None and cached[0] == _file_fingerprint(path):
                return cached[1]


        return sha256_file(path, maximum_bytes=maximum_bytes)
    try:
        if (
            maximum_bytes is None
            and size >= _FILE_HASH_MEMO_MINIMUM_BYTES
            and not _FILE_HASH_MEMO_READS_DISABLED
        ):
            memo_digest = _load_file_hash_memo_entry(key, fingerprint)
            if memo_digest is not None:
                settled = _file_fingerprint(path)
                if settled == fingerprint:
                    with _FILE_HASH_LOCK:
                        _FILE_HASH_CACHE[key] = (fingerprint, memo_digest)
                        _FILE_HASH_INFLIGHT.pop(key, None)
                    inflight.set()
                    return memo_digest


        result = _hash_file(path, size)
    finally:
        with _FILE_HASH_LOCK:
            _FILE_HASH_INFLIGHT.pop(key, None)
            inflight.set()


    try:
        settled = _file_fingerprint(path)
    except AcquisitionError:
        raise
    with _FILE_HASH_LOCK:
        if settled == fingerprint:
            _FILE_HASH_CACHE[key] = (settled, result)
    if settled == fingerprint and maximum_bytes is None and size >= _FILE_HASH_MEMO_MINIMUM_BYTES:
        _store_file_hash_memo_entry(key, fingerprint, result)
    return result


def canonical_json_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def generation_id(kind: str, value: Any) -> str:
    digest = hashlib.sha256(canonical_json_bytes(value)).hexdigest()
    return f"{kind}:sha256:{digest}"


def file_identity(path: Path, *, maximum_bytes: int | None = None) -> dict[str, Any]:
    path = path.expanduser().resolve()
    digest = sha256_file(path, maximum_bytes=maximum_bytes)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": digest}


def stable_common_root(paths: Iterable[Path]) -> Path:
    normalized = [path.expanduser().resolve() for path in paths]
    if not normalized:
        raise AcquisitionError("no discovery roots supplied")
    return Path(os.path.commonpath([str(path) for path in normalized]))


def read_json(path: Path, *, maximum_bytes: int | None = 16 * 1024 * 1024) -> Any:
    sha256_file(path, maximum_bytes=maximum_bytes)
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AcquisitionError(f"invalid JSON: {path}") from error


PRIVATE_MODEL_MAXIMUM_BYTES = 256 * 1024 * 1024


def read_private_model(path: Path) -> Any:
    return read_json(path, maximum_bytes=PRIVATE_MODEL_MAXIMUM_BYTES)


def atomic_write_json(path: Path, payload: Any) -> None:
    path = path.expanduser().resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    data = json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as sink:
            sink.write(data)
            sink.flush()
            os.fsync(sink.fileno())
        os.replace(temporary_path, path)
    finally:
        temporary_path.unlink(missing_ok=True)
