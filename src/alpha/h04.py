import array
import bisect
import mmap
import os
import struct
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator

from alpha.p12 import SNAPSHOT_HEADER, SNAPSHOT_LEGACY_IDENTITIES, SNAPSHOT_MAGIC, SNAPSHOT_RECORD, SNAPSHOT_VERSION
from alpha.h01 import AcquisitionError
from alpha.h02 import _file_fingerprint, atomic_write_json, file_identity, read_json, sha256_file


MEMORY_MODEL_SCHEMA = "alpha.il2cpp-memory-model/v1"
POINTER_INDEX_SCHEMA = "alpha.runtime-pointer-index/v2"
POINTER_INDEX_BINDING_SCHEMA = "alpha.runtime-pointer-index-binding/v2"
POINTER_INDEX_MAGIC = b"ALPHAPI2"
POINTER_INDEX_VERSION = 2


POINTER_INDEX_GROUP_BYTES = 32 * 1024 * 1024
POINTER_INDEX_TABLE_BITS = 1 << 23
POINTER_INDEX_TABLE_SHAPE = 2
POINTER_INDEX_ADDRESS_STRIDE = 8


POINTER_INDEX_MINIMUM = 0x10000
POINTER_INDEX_MAXIMUM = 1 << 48


POINTER_INDEX_HEADER = struct.Struct("<8sIIIIQQQQQQ3Q")


def pointer_index_slots(
    value: int,
    *,
    table_bits: int = POINTER_INDEX_TABLE_BITS,
) -> tuple[int, int]:
    mixed = (value * 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
    mixed ^= mixed >> 29
    mixed = (mixed * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    mixed ^= mixed >> 32
    mask = table_bits - 1
    return mixed & mask, (mixed >> 24) & mask


def pointer_index_tables(
    windows: Iterable[bytes],
    *,
    minimum: int = POINTER_INDEX_MINIMUM,
    maximum: int = POINTER_INDEX_MAXIMUM,
    table_bits: int = POINTER_INDEX_TABLE_BITS,
) -> bytes:
    if table_bits < 256 or table_bits & (table_bits - 1):
        raise AcquisitionError("runtime pointer index table width is invalid")
    table = bytearray(table_bits // 8)
    for window in windows:
        count = len(window) // 8
        for index, value in enumerate(struct.unpack_from(f"<{count}Q", window)):
            if not minimum <= value < maximum:
                continue
            first, second = pointer_index_slots(value, table_bits=table_bits)
            table[first >> 3] |= 1 << (first & 7)
            table[second >> 3] |= 1 << (second & 7)
    return bytes(table)


_PREAD = getattr(os, "pread", None)


def _reference_needle_groups(
    needles: Iterable[bytes],
) -> list[tuple[bytes, frozenset[int], int]]:
    ordered = sorted(needles, key=lambda needle: needle[::-1])
    groups: list[tuple[bytes, frozenset[int], int]] = []
    index = 0
    total = len(ordered)
    while index < total:
        needle = ordered[index]
        index += 1
        members = [needle]
        suffix = needle
        while index < total:
            candidate = ordered[index]
            reversed_group = suffix[::-1]
            reversed_candidate = candidate[::-1]
            shared = 0
            limit = len(reversed_group)
            while (
                shared < limit
                and shared < len(reversed_candidate)
                and reversed_group[shared] == reversed_candidate[shared]
            ):
                shared += 1
            if shared < 4:
                break
            suffix = candidate[len(candidate) - shared :]
            members.append(candidate)
            index += 1
        groups.append(
            (
                suffix,
                frozenset(member[0] for member in members),
                len(needle) - len(suffix),
            )
        )
    return groups


_QWORD_STRUCT_CACHE: dict[int, struct.Struct] = {}


def _qword_struct(count: int) -> struct.Struct | None:
    if count < 0 or count > 1024:
        return None
    cached = _QWORD_STRUCT_CACHE.get(count)
    if cached is None:
        try:
            cached = struct.Struct(f"<{count}Q")
        except struct.error:
            return None


        if len(_QWORD_STRUCT_CACHE) < 32:
            _QWORD_STRUCT_CACHE[count] = cached
    return cached


@dataclass(frozen=True)
class SnapshotRecord:
    address: int
    byte_count: int
    payload_offset: int
    protect: int
    memory_type: int
    state: int

    @property
    def end(self) -> int:
        return self.address + self.byte_count


class MemorySnapshot:


    _index_cache: tuple[str, tuple[int, int, int, int, int], str, tuple[Any, ...]] | None = None


    _build_fingerprint: tuple[int, int, int, int, int] | None = None


    _SEARCH_WINDOW_BYTES = 1 * 1024 * 1024


    _REFERENCE_WINDOW_BYTES = 1 * 1024 * 1024


    _INDEX_WINDOW_BYTES = 8 * 1024 * 1024

    def __init__(self, path: Path):
        self.path = path.expanduser().resolve()
        if not self.path.is_file() or self.path.is_symlink():
            raise AcquisitionError("runtime memory snapshot is unavailable")
        self._source = self.path.open("rb", buffering=0)
        self._mapping = None


        self._reference_hits: dict[int, tuple[int, ...]] = {}


        self._pointer_index: (
            tuple[list[bytes], dict[SnapshotRecord, tuple[int, int]], int, int]
            | None
        ) = None
        self._pointer_index_loaded = False


        try:
            try:
                self._mapping = mmap.mmap(self._source.fileno(), 0, access=mmap.ACCESS_READ)
            except (OSError, ValueError) as error:


                raise AcquisitionError(
                    "runtime memory snapshot header is truncated"
                ) from error
            if not self._adopt_cached_index():
                self._initialize_from_source()
            self._prefetch_mapping(self._mapping)
            self._publish_index_cache()
        except BaseException:
            self.close()
            raise


        try:
            self._snapshot_digest = sha256_file(self.path)
        except AcquisitionError:
            self._snapshot_digest = ""

    @staticmethod
    def _prefetch_mapping(mapping: mmap.mmap) -> None:


        advise = getattr(mmap, "MADV_SEQUENTIAL", None)
        if advise is None:
            return
        try:
            mapping.madvise(advise)
        except (OSError, ValueError, AttributeError):
            pass

    def _adopt_cached_index(self) -> bool:


        cached = type(self)._index_cache
        if cached is None or cached[0] != str(self.path):
            return False
        try:
            fingerprint = _file_fingerprint(self.path)
        except AcquisitionError:
            return False
        if fingerprint != cached[1]:
            return False
        try:
            digest = sha256_file(self.path)
        except AcquisitionError:
            return False
        if digest != cached[2]:
            return False
        (
            self.image_base, self.image_bytes, self.expected_record_count,
            self.captured_bytes, self.region_count, self.records,
            self._starts, self._protects,
        ) = cached[3]


        return True

    def _publish_index_cache(self) -> None:


        build = self._build_fingerprint
        if build is None:
            return
        try:
            fingerprint = _file_fingerprint(self.path)
        except AcquisitionError:
            return
        if fingerprint != build:
            return
        try:
            digest = sha256_file(self.path)
        except AcquisitionError:
            return
        type(self)._index_cache = (
            str(self.path), fingerprint, digest,
            (
                self.image_base, self.image_bytes, self.expected_record_count,
                self.captured_bytes, self.region_count, self.records,
                self._starts, self._protects,
            ),
        )

    def _initialize_from_source(self) -> None:


        try:
            fingerprint = _file_fingerprint(self.path)
        except AcquisitionError as error:
            raise AcquisitionError("runtime memory snapshot is unavailable") from error
        self._build_fingerprint = fingerprint
        source = self._source
        try:
            position = source.seek(0)
        except OSError as error:
            raise AcquisitionError("runtime memory snapshot is unavailable") from error
        if position != 0:
            raise AcquisitionError("runtime memory snapshot is unavailable")


        try:
            body = source.read(SNAPSHOT_HEADER.size)
        except OSError as error:
            raise AcquisitionError("runtime memory snapshot header is truncated") from error
        if len(body) != SNAPSHOT_HEADER.size:
            raise AcquisitionError("runtime memory snapshot header is truncated")
        header = SNAPSHOT_HEADER.unpack(body)
        magic, version, header_bytes = header[0], header[1], header[2]
        image_base, image_bytes = header[3], header[4]
        expected_records, captured_bytes, region_count = header[5], header[6], header[7]
        reserved0, reserved1, reserved2 = header[8], header[9], header[10]
        if (magic, version) not in SNAPSHOT_LEGACY_IDENTITIES and (
            magic != SNAPSHOT_MAGIC or version != SNAPSHOT_VERSION
        ):
            raise AcquisitionError("runtime memory snapshot magic is invalid")
        if header_bytes != SNAPSHOT_HEADER.size:
            raise AcquisitionError("runtime memory snapshot envelope is invalid")
        if not image_base or not image_bytes or image_base + image_bytes <= image_base:
            raise AcquisitionError("runtime memory snapshot main-image identity is invalid")
        if reserved0 or reserved1 or reserved2:
            raise AcquisitionError("runtime memory snapshot reserved header is nonzero")
        if expected_records > 10_000_000 or region_count > expected_records:
            raise AcquisitionError("runtime memory snapshot record bounds are invalid")
        self.image_base = image_base
        self.image_bytes = image_bytes
        self.expected_record_count = expected_records
        self.captured_bytes = captured_bytes
        self.region_count = region_count
        mapping_len = fingerprint[2]
        records: list[SnapshotRecord] = []
        append = records.append
        unpack = SNAPSHOT_RECORD.unpack_from
        record_size = SNAPSHOT_RECORD.size
        cursor = SNAPSHOT_HEADER.size
        observed_bytes = 0

        record_cls = SnapshotRecord
        window_size = type(self)._INDEX_WINDOW_BYTES
        window = b""
        window_start = 0
        for _index in range(expected_records):
            offset = cursor - window_start
            if offset < 0 or offset + record_size > len(window):
                try:
                    source.seek(cursor)
                    window = source.read(window_size)
                except OSError as error:
                    raise AcquisitionError(
                        "runtime memory snapshot record is truncated"
                    ) from error
                window_start = cursor
                offset = 0
                if len(window) < record_size:
                    raise AcquisitionError("runtime memory snapshot record is truncated")
            address, byte_count, protect, memory_type, state, reserved = unpack(
                window, offset
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
            payload = cursor + record_size
            if payload + byte_count > mapping_len:
                raise AcquisitionError("runtime memory snapshot payload is truncated")
            append(
                record_cls(
                    address,
                    byte_count,
                    payload,
                    protect,
                    memory_type,
                    state,
                )
            )
            cursor = payload + byte_count
            observed_bytes += byte_count
        if cursor != mapping_len or observed_bytes != captured_bytes:
            raise AcquisitionError("runtime memory snapshot envelope does not close exactly")
        try:
            position = source.seek(0, 2)
        except OSError as error:
            raise AcquisitionError(
                "runtime memory snapshot envelope does not close exactly"
            ) from error
        if position != mapping_len:


            raise AcquisitionError("runtime memory snapshot envelope does not close exactly")
        records.sort(key=lambda item: item.address)
        for previous, current in zip(records, records[1:]):
            if current.address < previous.end:
                raise AcquisitionError("runtime memory snapshot virtual ranges overlap")
        self.records = tuple(records)
        self._starts = tuple(record.address for record in records)


        self._protects = tuple(record.protect & 0xFF for record in records)

    def close(self) -> None:
        mapping = getattr(self, "_mapping", None)
        source = getattr(self, "_source", None)
        if mapping is not None:
            mapping.close()
            self._mapping = None
        if source is not None:
            source.close()
            self._source = None

    def __enter__(self) -> MemorySnapshot:
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    @property
    def image_range(self) -> tuple[int, int]:
        return self.image_base, self.image_base + self.image_bytes

    def _record_index(self, address: int) -> int | None:
        index = bisect.bisect_right(self._starts, address) - 1
        if index < 0 or address >= self.records[index].end:
            return None
        return index

    def protect_of(self, address: int) -> int | None:


        index = bisect.bisect_right(self._starts, address) - 1
        if index < 0:
            return None
        record = self.records[index]
        if address >= record.end:
            return None
        return self._protects[index]

    def contains(self, address: int, byte_count: int = 1) -> bool:
        if byte_count < 0 or address + byte_count < address:
            return False
        remaining = byte_count
        cursor = address
        index = self._record_index(cursor)
        if index is None:
            return False
        records = self.records
        while remaining:
            record = records[index]
            amount = min(remaining, record.end - cursor)
            cursor += amount
            remaining -= amount
            if not remaining:
                return True
            index += 1
            if index >= len(records) or records[index].address != cursor:
                return False
        return True

    def read(self, address: int, byte_count: int) -> bytes | None:


        if byte_count < 0 or address + byte_count < address:
            return None
        records = self.records
        index = bisect.bisect_right(self._starts, address) - 1
        if index < 0 or address >= records[index].end:
            return None
        record = records[index]
        available = record.end - address
        if byte_count <= available:


            file_offset = record.payload_offset + address - record.address
            return bytes(self._mapping[file_offset : file_offset + byte_count])
        output = bytearray()
        remaining = byte_count
        cursor = address
        mapping = self._mapping
        while remaining:
            record = records[index]
            amount = min(remaining, record.end - cursor)
            file_offset = record.payload_offset + cursor - record.address
            output.extend(mapping[file_offset : file_offset + amount])
            cursor += amount
            remaining -= amount
            if not remaining:
                return bytes(output)
            index += 1
            if index >= len(records) or records[index].address != cursor:
                return None
        return bytes(output)

    def qwords(self, address: int, count: int) -> tuple[int, ...] | None:
        if count < 0 or count > 1_000_000:
            return None


        needed = count * 8
        if needed < 0 or address + needed < address:
            return None
        records = self.records
        index = bisect.bisect_right(self._starts, address) - 1
        if index < 0 or address >= records[index].end:
            return None
        record = records[index]
        if needed <= record.end - address:
            cached = _qword_struct(count)
            if cached is not None:
                try:
                    return cached.unpack_from(
                        self._mapping,
                        record.payload_offset + address - record.address,
                    )
                except (struct.error, ValueError, TypeError):
                    return None
        data = self.read(address, needed)
        if data is None:
            return None
        cached = _qword_struct(count)
        if cached is not None:
            try:
                return cached.unpack(data)
            except struct.error:
                return None
        return struct.unpack(f"<{count}Q", data)

    def c_string(self, address: int, *, maximum: int = 512) -> str | None:
        if maximum < 1:
            return None


        chunk = 256 if maximum > 256 else maximum
        index = bisect.bisect_right(self._starts, address) - 1
        records = self.records
        if index < 0 or address >= records[index].end:
            return None
        initial_available = records[index].end - address
        if maximum > initial_available:


            remaining_probe = maximum - initial_available
            probe_cursor = records[index].end
            probe_index = index + 1
            contiguous = True
            while remaining_probe > 0:
                if (
                    probe_index >= len(records)
                    or records[probe_index].address != probe_cursor
                ):
                    contiguous = False
                    break
                span = records[probe_index].end - probe_cursor
                if remaining_probe <= span:
                    break
                remaining_probe -= span
                probe_cursor = records[probe_index].end
                probe_index += 1
            if not contiguous:
                maximum = initial_available
        collected = bytearray()
        remaining = maximum
        cursor = address
        record_end = records[index].end
        mapping = self._mapping
        while remaining:
            amount = min(chunk, remaining, record_end - cursor)
            record = records[index]
            file_offset = record.payload_offset + cursor - record.address
            collected.extend(mapping[file_offset : file_offset + amount])
            cursor += amount
            remaining -= amount
            end = collected.find(b"\0")
            if end >= 0:
                try:
                    return bytes(collected[:end]).decode("utf-8")
                except UnicodeDecodeError:
                    return None
            if not remaining:
                break
            following = index + 1
            if (
                following >= len(records)
                or records[following].address != cursor
            ):
                break
            index = following
            record_end = records[index].end
        if collected.find(b"\0") < 0:
            return None


        cursor = address + len(collected)
        remaining = maximum - len(collected)
        tail = self.read(cursor, remaining) if remaining > 0 else b""
        if tail is None:
            return None
        raw = bytes(collected) + bytes(tail)
        end = raw.find(b"\0")
        if end < 0:
            return None
        try:
            return raw[:end].decode("utf-8")
        except UnicodeDecodeError:
            return None

    def iter_records(
        self, within: tuple[int, int] | None = None
    ) -> Iterator[SnapshotRecord]:
        lower, upper = within if within is not None else (0, 1 << 64)
        for record in self.records:
            if record.end <= lower:
                continue
            if record.address >= upper:
                break
            yield record

    def _load_pointer_index(
        self,
    ) -> (
        tuple[list[bytes], dict[SnapshotRecord, tuple[int, int]], int, int]
        | None
    ):
        if self._pointer_index_loaded:
            return self._pointer_index
        self._pointer_index_loaded = True
        index_path = self.path.with_name(
            self.path.name.replace("runtime-memory.private.bin", "")
            + "runtime-pointer-index.private.bin"
        )
        binding_path = self.path.with_name(
            self.path.name.replace("runtime-memory.private.bin", "")
            + "runtime-pointer-index.private.json"
        )
        try:
            if (
                not index_path.is_file()
                or index_path.is_symlink()
                or not binding_path.is_file()
                or binding_path.is_symlink()
            ):
                return None
            binding = read_json(binding_path)
            if (
                not isinstance(binding, dict)
                or binding.get("schema") != POINTER_INDEX_BINDING_SCHEMA
                or binding.get("status") != "complete"
            ):
                return None
            snapshot_record = binding.get("snapshot")
            index_record = binding.get("index")
            geometry = binding.get("geometry")
            if (
                not isinstance(snapshot_record, dict)
                or not isinstance(index_record, dict)
                or not isinstance(geometry, dict)
                or snapshot_record.get("sha256") != self._snapshot_digest
                or geometry.get("stride") != POINTER_INDEX_ADDRESS_STRIDE
                or geometry.get("table_bits") != POINTER_INDEX_TABLE_BITS
                or geometry.get("table_shape") != POINTER_INDEX_TABLE_SHAPE
                or geometry.get("group_bytes") != POINTER_INDEX_GROUP_BYTES
                or geometry.get("minimum") != POINTER_INDEX_MINIMUM
                or geometry.get("maximum") != POINTER_INDEX_MAXIMUM
                or geometry.get("record_count") != len(self.records)
            ):
                return None
            index_identity = file_identity(index_path)
            if (
                index_identity["sha256"] != index_record.get("sha256")
                or index_identity["bytes"] != index_record.get("bytes")
            ):
                return None
            raw = index_path.read_bytes()
        except (AcquisitionError, OSError, ValueError, TypeError, KeyError):
            return None
        if len(raw) < POINTER_INDEX_HEADER.size:
            return None
        try:
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
            ) = POINTER_INDEX_HEADER.unpack_from(raw, 0)
        except struct.error:
            return None
        table_bytes = table_bits // 8
        if (
            magic != POINTER_INDEX_MAGIC
            or version != POINTER_INDEX_VERSION
            or stride != POINTER_INDEX_ADDRESS_STRIDE
            or table_bits != POINTER_INDEX_TABLE_BITS
            or shape != POINTER_INDEX_TABLE_SHAPE
            or group_bytes != POINTER_INDEX_GROUP_BYTES
            or minimum != POINTER_INDEX_MINIMUM
            or maximum != POINTER_INDEX_MAXIMUM
            or reserved0
            or reserved1
            or reserved2
            or record_count != len(self.records)
            or group_count != geometry.get("group_count")
            or snapshot_bytes != snapshot_record.get("bytes")
            or self.path.stat().st_size != snapshot_record.get("bytes")
            or len(raw) != POINTER_INDEX_HEADER.size + group_count * table_bytes
        ):
            return None
        groups: list[bytes] = []
        offset = POINTER_INDEX_HEADER.size
        for _ in range(group_count):
            groups.append(raw[offset : offset + table_bytes])
            offset += table_bytes


        file_order = sorted(
            self.records, key=lambda record: record.payload_offset
        )
        by_record: dict[SnapshotRecord, tuple[int, int]] = {}
        cumulative = 0
        for record in file_order:
            if record.address % stride or record.end % stride:
                return None
            first = cumulative // group_bytes
            cumulative += record.byte_count
            last = (cumulative - 1) // group_bytes
            if last >= group_count:
                return None
            by_record[record] = (first, last)
        self._pointer_index = (groups, by_record, minimum, maximum)
        return self._pointer_index

    def _payload_read(self, offset: int, length: int) -> bytes:

        source = self._source
        if source is None or _PREAD is None:
            raise ValueError("runtime memory snapshot is closed")
        if length <= 0:
            return b""
        descriptor = source.fileno()
        chunks: list[bytes] = []
        remaining = length
        cursor = offset
        try:
            while remaining > 0:
                block = _PREAD(descriptor, remaining, cursor)
                if not block:
                    break
                chunks.append(block)
                remaining -= len(block)
                cursor += len(block)
        except (OSError, ValueError) as error:
            raise AcquisitionError(
                "runtime memory snapshot payload read failed"
            ) from error
        if remaining:
            raise AcquisitionError(
                "runtime memory snapshot payload read is truncated"
            )
        if len(chunks) == 1:
            return chunks[0]
        return b"".join(chunks)

    def find_bytes(
        self, needle: bytes, *, within: tuple[int, int] | None = None
    ) -> Iterator[int]:
        if not needle:
            return
        lower, upper = within if within is not None else (0, 1 << 64)
        overlap = max(0, len(needle) - 1)
        mapping = self._mapping
        window_bytes = type(self)._SEARCH_WINDOW_BYTES
        streamed = _PREAD is not None
        for record in self.iter_records(within):
            record_end = record.end
            virtual_start = max(record.address, lower)
            virtual_end = min(record_end, upper)
            file_start = record.payload_offset + virtual_start - record.address
            file_end = record.payload_offset + virtual_end - record.address
            if streamed:


                span = file_end - file_start
                carry = b""
                processed = 0
                while processed < span:
                    amount = min(window_bytes, span - processed)


                    data = self._payload_read(file_start + processed, amount)
                    window = carry + data if carry else data
                    limit = len(window)
                    found = window.find(needle)
                    while found >= 0:
                        address = virtual_start + processed - len(carry) + found
                        if lower <= address and address + len(needle) <= upper:
                            yield address
                        found = window.find(needle, found + 1)
                    carry = window[-overlap:] if overlap else b""
                    processed += len(data)
            else:
                cursor = file_start
                while cursor < file_end:
                    found = mapping.find(needle, cursor, file_end)
                    if found < 0:
                        break
                    address = virtual_start + found - file_start
                    if lower <= address and address + len(needle) <= upper:
                        yield address
                    cursor = found + 1
            if overlap and virtual_end == record_end:


                tail_length = min(overlap, record.byte_count)
                if (
                    tail_length
                    and needle[0] in mapping[file_end - tail_length : file_end]
                ):
                    next_index = bisect.bisect_right(self._starts, record.address)
                    if (
                        next_index < len(self.records)
                        and self.records[next_index].address == record_end
                    ):
                        boundary_start = max(virtual_start, record_end - overlap)
                        joined = self.read(boundary_start, overlap * 2)
                        if joined is not None:
                            boundary_found = joined.find(needle)
                            while boundary_found >= 0:
                                address = boundary_start + boundary_found
                                if (
                                    address < record_end < address + len(needle)
                                    and lower <= address
                                    and address + len(needle) <= upper
                                ):
                                    yield address
                                boundary_found = joined.find(needle, boundary_found + 1)

    def find_bytes_many(
        self, needles: Iterable[bytes]
    ) -> dict[bytes, tuple[int, ...]]:
        unique: list[bytes] = []
        seen: set[bytes] = set()
        for needle in needles:
            if not needle or needle in seen:
                continue
            seen.add(needle)
            unique.append(needle)
        hits: dict[bytes, list[int]] = {needle: [] for needle in unique}
        if not unique:
            return {needle: () for needle in hits}


        overlap = max(len(needle) for needle in unique) - 1
        search_lengths = {needle: len(needle) for needle in unique}
        first_bytes = {needle[0] for needle in unique}
        records = self.records


        adjacent_sources = {
            previous.address
            for previous, following in zip(records, records[1:])
            if following.address == previous.end
        }
        source = self._source
        if source is None:
            raise ValueError("runtime memory snapshot is closed")
        try:
            fingerprint = _file_fingerprint(self.path)
        except AcquisitionError:
            fingerprint = None
        window_size = max(type(self)._REFERENCE_WINDOW_BYTES, 1 << 20)
        window = b""
        window_start = 0
        file_order = sorted(
            (record for record in records if record.byte_count),
            key=lambda record: record.payload_offset,
        )
        for record in file_order:
            byte_count = record.byte_count
            start = record.payload_offset
            if not (
                window_start <= start
                and start + byte_count <= window_start + len(window)
            ):
                try:
                    source.seek(start)
                    window = source.read(window_size)
                except OSError as error:
                    raise AcquisitionError(
                        "runtime memory snapshot payload read failed"
                    ) from error
                window_start = start
                if len(window) < byte_count:
                    raise AcquisitionError(
                        "runtime memory snapshot payload read is truncated"
                    )
            offset = start - window_start
            data = window[offset : offset + byte_count]
            for needle in unique:
                found = data.find(needle)
                while found >= 0:
                    hits[needle].append(record.address + found)
                    found = data.find(needle, found + 1)
            tail_length = min(overlap, byte_count)
            if first_bytes.isdisjoint(data[byte_count - tail_length :]):
                continue
            if record.address not in adjacent_sources:
                continue
            boundary_start = max(record.address, record.end - overlap)
            joined = self.read(boundary_start, overlap * 2)
            if joined is None:
                continue
            record_end = record.end
            for needle in unique:
                needle_length = search_lengths[needle]
                boundary_found = joined.find(needle)
                while boundary_found >= 0:
                    address = boundary_start + boundary_found
                    if address < record_end < address + needle_length:
                        hits[needle].append(address)
                    boundary_found = joined.find(needle, boundary_found + 1)
        if fingerprint is not None:
            try:
                if _file_fingerprint(self.path) != fingerprint:
                    raise AcquisitionError(
                        "runtime memory snapshot changed during the batched scan"
                    )
            except AcquisitionError as error:


                raise AcquisitionError(
                    "runtime memory snapshot changed during the batched scan"
                ) from error
        return {needle: tuple(sorted(hits[needle])) for needle in unique}

    def capture_reference_hits(
        self, targets, *, within: tuple[int, int] | None = None
    ) -> dict[int, tuple[int, ...]]:
        unique = sorted(set(targets))
        needles = {target: struct.pack("<Q", target) for target in unique}
        if within is not None or not unique:
            return {
                target: tuple(
                    address
                    for address in self.find_bytes(
                        needles[target], within=within
                    )
                )
                for target in unique
            }
        fingerprint = _file_fingerprint(self.path)
        overlap = 7
        first_bytes = {needle[0] for needle in needles.values()}
        hits: dict[int, list[int]] = {target: [] for target in unique}
        records = self.records


        adjacent_sources = {
            previous.address
            for previous, following in zip(records, records[1:])
            if following.address == previous.end
        }


        groups = _reference_needle_groups(needles.values())
        by_needle = {needle: target for target, needle in needles.items()}
        source = self._source
        window_size = max(type(self)._REFERENCE_WINDOW_BYTES, 1 << 20)
        window = b""
        window_start = 0
        file_order = sorted(
            (record for record in records if record.byte_count),
            key=lambda record: record.payload_offset,
        )
        for record in file_order:
            byte_count = record.byte_count
            start = record.payload_offset
            if not (
                window_start <= start
                and start + byte_count <= window_start + len(window)
            ):
                try:
                    source.seek(start)
                    window = source.read(window_size)
                except OSError as error:
                    raise AcquisitionError(
                        "runtime memory snapshot reference scan is truncated"
                    ) from error
                window_start = start
                if len(window) < byte_count:
                    raise AcquisitionError(
                        "runtime memory snapshot reference scan is truncated"
                    )
            offset = start - window_start
            payload_end = offset + byte_count


            find = window.find
            seen: set[int] = set()
            for group_suffix, group_first_bytes, pad in groups:
                position = find(group_suffix, offset, payload_end)
                while position >= 0:
                    candidate = position - pad
                    if (
                        candidate >= offset
                        and candidate + 8 <= payload_end
                        and window[candidate] in group_first_bytes
                        and candidate not in seen
                    ):
                        target = by_needle.get(window[candidate : candidate + 8])
                        if target is not None:
                            seen.add(candidate)
                            hits[target].append(
                                record.address + candidate - offset
                            )
                    position = find(group_suffix, position + 1, payload_end)
            tail_length = min(overlap, byte_count)
            if (
                record.address in adjacent_sources
                and not first_bytes.isdisjoint(
                    window[payload_end - tail_length : payload_end]
                )
            ):
                boundary_start = max(record.address, record.end - overlap)
                joined = self.read(boundary_start, overlap * 2)
                if joined is not None:
                    for target in unique:
                        needle = needles[target]
                        boundary_found = joined.find(needle)
                        while boundary_found >= 0:
                            address = boundary_start + boundary_found
                            if (
                                address < record.end < address + 8
                                and 0 <= address
                                and address + 8 <= 1 << 64
                            ):
                                hits[target].append(address)
                            boundary_found = joined.find(
                                needle, boundary_found + 1
                            )
        if _file_fingerprint(self.path) != fingerprint:
            raise AcquisitionError(
                "runtime memory snapshot changed during the reference scan"
            )
        frozen = {
            target: tuple(sorted(hits[target]))
            for target in unique
        }
        self._reference_hits.update(frozen)
        return frozen

    def _indexed_candidates(
        self, target: int
    ) -> Iterator[SnapshotRecord] | None:
        layout = self._load_pointer_index()
        if layout is None:
            return None
        groups, by_record, minimum, maximum = layout
        if not minimum <= target < maximum:
            return None
        first, second = pointer_index_slots(target)
        mask = 1 << (first & 7)
        second_mask = 1 << (second & 7)

        def admitted(record: SnapshotRecord) -> bool:
            for group in {*by_record[record]}:
                table = groups[group]
                if not table[first >> 3] & mask:
                    return False
                if not table[second >> 3] & second_mask:
                    return False
            return True

        return (record for record in self.records if admitted(record))

    def references(
        self, target: int, *, within: tuple[int, int] | None = None
    ) -> Iterator[int]:
        if within is None:
            cached = self._reference_hits.get(target)
            if cached is not None:
                for address in cached:
                    if address % 8 == 0:
                        yield address
                return
            candidates = self._indexed_candidates(target)
            if candidates is not None:
                needle = struct.pack("<Q", target)
                for record in candidates:
                    payload = self._payload_read(
                        record.payload_offset, record.byte_count
                    )
                    found = payload.find(needle)
                    while found >= 0:
                        address = record.address + found
                        if address % 8 == 0:
                            yield address
                        found = payload.find(needle, found + 1)
                return
        for address in self.find_bytes(struct.pack("<Q", target), within=within):
            if address % 8 == 0:
                yield address

    def qword_items(
        self, *, within: tuple[int, int] | None = None
    ) -> Iterator[tuple[int, int]]:
        lower, upper = within if within is not None else (0, 1 << 64)
        for record in self.iter_records(within):
            virtual_start = max(record.address, lower)
            virtual_end = min(record.end, upper)
            aligned_start = virtual_start + (-virtual_start % 8)
            aligned_end = virtual_end - (virtual_end - aligned_start) % 8
            if aligned_end <= aligned_start:
                continue
            file_start = record.payload_offset + aligned_start - record.address
            file_end = file_start + aligned_end - aligned_start
            values = array.array("Q")
            values.frombytes(self._mapping[file_start:file_end])
            if values.itemsize != 8:
                raise AcquisitionError("host qword width is unsupported")
            if sys.byteorder != "little":
                values.byteswap()
            address = aligned_start
            for value in values:
                yield address, value
                address += 8


def _dll_strings(snapshot: MemorySnapshot) -> dict[int, str]:
    output: dict[int, str] = {}
    lower, upper = snapshot.image_range
    for dot_address in snapshot.find_bytes(b".dll\0", within=(lower, upper)):
        start = max(lower, dot_address - 240)
        raw = snapshot.read(start, dot_address - start + 4)
        if raw is None:
            continue
        previous = raw.rfind(b"\0", 0, len(raw) - 4)
        name_raw = raw[previous + 1 :]
        if not (5 <= len(name_raw) <= 244):
            continue
        if any(value < 0x20 or value > 0x7E for value in name_raw):
            continue
        try:
            name = name_raw.decode("ascii")
        except UnicodeDecodeError:
            continue
        if name.casefold().endswith(".dll"):
            output[dot_address - len(name_raw) + 4] = name
    return output


def _module_candidates(
    snapshot: MemorySnapshot, dll_strings: dict[int, str]
) -> dict[int, dict[str, Any]]:
    output: dict[int, dict[str, Any]] = {}
    captured_limit = max(1, snapshot.captured_bytes // 8)
    for address, value in snapshot.qword_items(within=snapshot.image_range):
        name = dll_strings.get(value)
        if name is None:
            continue
        values = snapshot.qwords(address, 3)
        if not values or values[0] != value or values[1] > captured_limit:
            continue
        if values[1] and (not values[2] or values[2] % 8):
            continue
        output[address] = {
            "address": address,
            "name": name,
            "method_pointer_count_candidate": values[1],
            "method_pointers_candidate": values[2],
        }
    return output


def _module_arrays(
    snapshot: MemorySnapshot, modules: dict[int, dict[str, Any]]
) -> list[dict[str, Any]]:
    module_addresses = set(modules)
    runs: list[tuple[int, list[int]]] = []
    run_start: int | None = None
    run_values: list[int] = []
    previous_address: int | None = None
    for address, value in snapshot.qword_items(within=snapshot.image_range):
        if value in module_addresses:
            if previous_address is None or address != previous_address + 8:
                if run_start is not None and len(run_values) >= 4:
                    runs.append((run_start, run_values))
                run_start = address
                run_values = []
            run_values.append(value)
            previous_address = address
        else:
            if run_start is not None and len(run_values) >= 4:
                runs.append((run_start, run_values))
            run_start = None
            run_values = []
            previous_address = None
    if run_start is not None and len(run_values) >= 4:
        runs.append((run_start, run_values))

    candidates: list[dict[str, Any]] = []
    seen: set[tuple[int, tuple[int, ...]]] = set()
    for address, pointers in runs:
        names = [modules[pointer]["name"] for pointer in pointers]
        identity = (address, tuple(pointers))
        if identity in seen or len(set(names)) != len(names):
            continue
        seen.add(identity)
        candidates.append(
            {
                "address": address,
                "module_count": len(pointers),
                "module_pointers": pointers,
                "module_names": names,
            }
        )
    candidates.sort(key=lambda item: (-item["module_count"], item["address"]))
    return candidates


def _registration_candidates(
    snapshot: MemorySnapshot, module_array: dict[str, Any]
) -> list[dict[str, Any]]:
    output: list[dict[str, Any]] = []
    count = module_array["module_count"]
    maximum_count = max(1, snapshot.captured_bytes // 8)
    for pointer_field in snapshot.references(
        module_array["address"], within=snapshot.image_range
    ):
        previous = snapshot.qwords(pointer_field - 8, 1)
        if not previous or previous[0] != count:
            continue
        pairs: list[dict[str, int]] = []
        cursor = pointer_field - 8
        while len(pairs) < 32:
            pair = snapshot.qwords(cursor, 2)
            if not pair:
                break
            pair_count, pair_pointer = pair
            if pair_count > maximum_count:
                break
            if pair_count and (not pair_pointer or pair_pointer % 8):
                break
            if pair_count and not snapshot.contains(pair_pointer):
                break
            pairs.append({"count": pair_count, "pointer": pair_pointer})
            cursor -= 16
        if not pairs or pairs[0]["count"] != count:
            continue
        pairs.reverse()
        output.append(
            {
                "module_count_field": pointer_field - 8,
                "module_array_field": pointer_field,
                "backward_pair_window_start": pointer_field
                - (len(pairs) * 16 - 8),
                "backward_pair_window_count": len(pairs),
                "module_count": count,
                "module_array": module_array["address"],
                "pairs": pairs,
            }
        )
    return output


def discover_snapshot_model(snapshot_path: Path) -> dict[str, Any]:
    identity = file_identity(snapshot_path)
    with MemorySnapshot(snapshot_path) as snapshot:
        strings = _dll_strings(snapshot)
        modules = _module_candidates(snapshot, strings)
        arrays = _module_arrays(snapshot, modules)
        if not arrays:
            raise AcquisitionError("runtime module array could not be derived from snapshot")
        maximum = arrays[0]["module_count"]
        strongest = [item for item in arrays if item["module_count"] == maximum]
        if len(strongest) != 1:
            raise AcquisitionError(
                f"runtime module array identity is not unique ({len(strongest)})"
            )
        selected = strongest[0]
        registrations = _registration_candidates(snapshot, selected)
        if len(registrations) != 1:
            raise AcquisitionError(
                "runtime code registration identity is not unique "
                f"({len(registrations)})"
            )
        selected_modules = [modules[pointer] for pointer in selected["module_pointers"]]
        return {
            "schema": MEMORY_MODEL_SCHEMA,
            "status": "discovered",
            "snapshot": {
                "bytes": identity["bytes"],
                "sha256": identity["sha256"],
                "record_count": snapshot.expected_record_count,
                "region_count": snapshot.region_count,
                "captured_bytes": snapshot.captured_bytes,
                "image_base": snapshot.image_base,
                "image_bytes": snapshot.image_bytes,
            },
            "discovery": {
                "dll_string_count": len(strings),
                "module_structure_candidate_count": len(modules),
                "module_array_candidate_count": len(arrays),
            },
            "module_array": selected,
            "modules": selected_modules,
            "code_registration_tail": registrations[0],
            "checks": {
                "snapshot_envelope_valid": True,
                "module_array_unique_by_maximal_structural_run": True,
                "module_names_unique": True,
                "code_registration_module_tail_unique": True,
                "code_registration_start_resolved": False,
                "fixed_address_used": False,
                "fixed_rva_used": False,
                "fixed_version_used": False,
                "saved_module_list_used": False,
                "saved_registration_used": False,
            },
        }


def inspect_snapshot_model(*, snapshot: Path, output: Path) -> dict[str, Any]:
    model = discover_snapshot_model(snapshot)
    output = output.expanduser().resolve()
    atomic_write_json(output, model)
    output.chmod(0o600)
    return {
        "schema": MEMORY_MODEL_SCHEMA,
        "status": model["status"],
        "snapshot": {
            "bytes": model["snapshot"]["bytes"],
            "sha256": model["snapshot"]["sha256"],
            "record_count": model["snapshot"]["record_count"],
            "captured_bytes": model["snapshot"]["captured_bytes"],
        },
        "discovery": model["discovery"],
        "module_count": model["module_array"]["module_count"],
        "registration_backward_pair_window_count": model["code_registration_tail"][
            "backward_pair_window_count"
        ],
        "checks": model["checks"],
        "raw_addresses_owner_only": True,
        "output": str(output),
    }
