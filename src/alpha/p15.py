import struct
from collections import Counter
from pathlib import Path
from typing import Any

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError
from alpha.h04 import MemorySnapshot
from alpha.p01 import reflection_contract
from alpha.p14 import REFLECTION_BOOTSTRAP_SCHEMA
from alpha.p02 import runtime_inventory_contract
from alpha.c01 import load_runtime_owner_roots
from alpha.h02 import file_identity, read_json


RUNTIME_CLASS_SCHEMA = "alpha.runtime-class-model/v2"
EXECUTABLE_PROTECTIONS = {0x10, 0x20, 0x40, 0x80}
SEMANTIC_INHERITANCE_PAIRS = (
    ("System.RuntimeType", "System.Type"),
    ("System.Reflection.MonoMethod", "System.Reflection.MethodInfo"),
    ("System.Reflection.MonoField", "System.Reflection.FieldInfo"),
    ("System.Reflection.MonoProperty", "System.Reflection.PropertyInfo"),
    ("System.Reflection.MonoEvent", "System.Reflection.EventInfo"),
    ("System.Reflection.MonoParameterInfo", "System.Reflection.ParameterInfo"),
)


def _select_semantic_member_layout(
    *,
    candidates: list[dict[str, Any]],
    required_counts: dict[str, int],
    owner_count: int,
) -> dict[str, Any]:
    eligible = [
        candidate
        for candidate in candidates
        if candidate["valid_owner_count"] == owner_count
        and all(
            candidate["counts_by_owner"].get(owner, 0) >= count
            for owner, count in required_counts.items()
        )
    ]
    if len(eligible) != 1:
        raise AcquisitionError(
            "runtime class method layout is not unique "
            f"(candidates={len(eligible)})"
        )
    return eligible[0]


def _record_for(snapshot: MemorySnapshot, value: int):


    index = snapshot._record_index(value)
    return snapshot.records[index] if index is not None else None


def _is_executable_pointer(snapshot: MemorySnapshot, value: int) -> bool:
    if not value:
        return False
    protect = snapshot.protect_of(value)
    return protect is not None and protect in EXECUTABLE_PROTECTIONS


def _is_metadata_pointer(snapshot: MemorySnapshot, value: int) -> bool:
    if not value:
        return False
    protect = snapshot.protect_of(value)
    return protect is not None and protect not in EXECUTABLE_PROTECTIONS


def _discover_vtable_start(
    snapshot: MemorySnapshot, class_headers: dict[str, tuple[int, ...]]
) -> int:
    candidates: list[int] = []
    for index in range(min(len(values) for values in class_headers.values()) - 8):
        if not all(
            _is_executable_pointer(snapshot, values[index])
            for values in class_headers.values()
        ):
            continue
        if all(
            sum(
                _is_executable_pointer(snapshot, value)
                for value in values[index : index + 8]
            )
            >= 3
            for values in class_headers.values()
        ):


            candidates.append(index)
    if not candidates:
        raise AcquisitionError("runtime class vtable boundary is unavailable")
    return min(candidates)


def _discover_parent_class_field(
    *,
    snapshot: MemorySnapshot,
    class_addresses: dict[str, int],
    scan_qwords: int = 64,
) -> dict[str, Any]:
    pairs = [
        (class_addresses[child], class_addresses[parent])
        for child, parent in SEMANTIC_INHERITANCE_PAIRS
        if child in class_addresses and parent in class_addresses
    ]
    if len(pairs) < 4:
        raise AcquisitionError("runtime class inheritance evidence is incomplete")


    hierarchy_scores: dict[int, int] = {}


    child_windows: dict[int, tuple[int, ...] | None] = {}
    for child, _ancestor in pairs:
        if child not in child_windows:
            child_windows[child] = snapshot.qwords(child, scan_qwords)
    hierarchy_cache: dict[int, tuple[int, ...] | None] = {}
    metadata_cache: dict[int, bool] = {}

    def _cached_is_metadata(value: int) -> bool:
        cached = metadata_cache.get(value)
        if cached is None:
            cached = _is_metadata_pointer(snapshot, value)
            metadata_cache[value] = cached
        return cached

    for field in range(scan_qwords):
        support = 0
        for child, ancestor in pairs:
            window = child_windows.get(child)
            if window is not None:
                hierarchy_pointer = window[field]
            else:
                pointer_values = snapshot.qwords(child, field + 1)
                hierarchy_pointer = pointer_values[-1] if pointer_values else 0
            if hierarchy_pointer in hierarchy_cache:
                hierarchy = hierarchy_cache[hierarchy_pointer]
            else:
                hierarchy = (
                    snapshot.qwords(hierarchy_pointer, 32)
                    if hierarchy_pointer
                    else None
                )
                hierarchy_cache[hierarchy_pointer] = hierarchy
            if not hierarchy or child not in hierarchy or ancestor not in hierarchy:
                continue
            child_index = hierarchy.index(child)
            ancestor_index = hierarchy.index(ancestor)
            prefix = hierarchy[: child_index + 1]
            if (
                ancestor_index < child_index
                and len(prefix) == len(set(prefix))
                and all(_cached_is_metadata(value) for value in prefix)
            ):
                support += 1
        hierarchy_scores[field] = support
    minimum_support = max(4, (len(pairs) * 2 + 2) // 3)
    hierarchy_support = max(hierarchy_scores.values(), default=0)
    hierarchy_candidates = [
        field
        for field, support in hierarchy_scores.items()
        if support == hierarchy_support and support >= minimum_support
    ]
    if len(hierarchy_candidates) == 1:
        field = hierarchy_candidates[0]
        return {
            "encoding": "hierarchy-pointer",
            "byte_offset": field * 8,
            "qword": field,
            "support": hierarchy_support,
            "pair_count": len(pairs),
        }
    def decoded_parent(
        current: int, *, byte_offset: int, encoding: str
    ) -> int:
        if encoding == "native-pointer":
            values = snapshot.qwords(current, byte_offset // 8 + 1)
            return values[-1] if values else 0
        raw = snapshot.read(current + byte_offset, 4)
        if raw is None or len(raw) != 4:
            return 0
        low = struct.unpack("<I", raw)[0]
        return (current & 0xFFFFFFFF00000000) | low if low else 0

    def reaches_ancestor(
        child: int, ancestor: int, *, byte_offset: int, encoding: str
    ) -> bool:
        current = child
        visited = {child}
        while True:
            parent = decoded_parent(
                current, byte_offset=byte_offset, encoding=encoding
            )
            if parent == ancestor:
                return True
            if (
                not parent
                or parent in visited
                or not _is_metadata_pointer(snapshot, parent)
            ):
                return False
            visited.add(parent)
            current = parent

    families = (
        ("native-pointer", range(0, scan_qwords * 8, 8)),
        ("same-region-low32", range(0, scan_qwords * 8, 4)),
    )
    best_observed_support = 0
    for encoding, offsets in families:
        scores = {
            byte_offset: sum(
                reaches_ancestor(
                    child,
                    parent,
                    byte_offset=byte_offset,
                    encoding=encoding,
                )
                for child, parent in pairs
            )
            for byte_offset in offsets
        }
        best_support = max(scores.values(), default=0)
        best_observed_support = max(best_observed_support, best_support)
        candidates = [
            byte_offset
            for byte_offset, support in scores.items()
            if support == best_support and support >= minimum_support
        ]


        if len(candidates) == 1:
            byte_offset = candidates[0]
            return {
                "encoding": encoding,
                "byte_offset": byte_offset,
                "qword": byte_offset // 8,
                "support": best_support,
                "pair_count": len(pairs),
            }
    raise AcquisitionError(
        "runtime parent-class field is not unique "
        f"(support={best_observed_support}/{len(pairs)})"
    )


def _parent_class_pointer(
    *, snapshot: MemorySnapshot, class_pointer: int, layout: dict[str, Any]
) -> int:
    byte_offset = layout["byte_offset"]
    if layout["encoding"] == "hierarchy-pointer":
        values = snapshot.qwords(class_pointer, byte_offset // 8 + 1)
        hierarchy_pointer = values[-1] if values else 0
        hierarchy = (
            snapshot.qwords(hierarchy_pointer, 32)
            if hierarchy_pointer
            else None
        )
        if not hierarchy or class_pointer not in hierarchy:
            return 0
        index = hierarchy.index(class_pointer)
        return hierarchy[index - 1] if index else 0
    if layout["encoding"] == "native-pointer":
        values = snapshot.qwords(class_pointer, byte_offset // 8 + 1)
        return values[-1] if values else 0
    raw = snapshot.read(class_pointer + byte_offset, 4)
    if raw is None or len(raw) != 4:
        return 0
    low = struct.unpack("<I", raw)[0]
    return (class_pointer & 0xFFFFFFFF00000000) | low if low else 0


def _member_layout_candidates(
    *,
    snapshot: MemorySnapshot,
    class_addresses: dict[str, int],
    vtable_start_qword: int,
) -> list[dict[str, Any]]:
    header_bytes = vtable_start_qword * 8
    headers = {
        owner: snapshot.read(address, header_bytes)
        for owner, address in class_addresses.items()
    }
    if any(value is None for value in headers.values()):
        raise AcquisitionError("runtime class header is not fully captured")
    pointer_fields = [
        index
        for index in range(vtable_start_qword)
        if all(
            _is_metadata_pointer(
                snapshot, struct.unpack_from("<Q", header, index * 8)[0]
            )
            for header in headers.values()
        )
    ]
    candidates: list[dict[str, Any]] = []
    qwords_cache: dict[tuple[int, int], tuple[int, ...] | None] = {}
    metadata_cache: dict[int, bool] = {}

    def _cached_qwords(pointer: int, count: int) -> tuple[int, ...] | None:
        key = (pointer, count)
        if key not in qwords_cache:
            qwords_cache[key] = snapshot.qwords(pointer, count)
        return qwords_cache[key]

    def _cached_is_metadata(value: int) -> bool:


        cached = metadata_cache.get(value)
        if cached is None:
            cached = _is_metadata_pointer(snapshot, value)


            metadata_cache[value] = cached
        return cached

    for pointer_qword in pointer_fields:
        for count_offset in range(0, header_bytes, 2):
            valid = 0
            counts: dict[str, int] = {}
            mean_sum = 0.0
            mean_count = 0
            for owner, header in headers.items():
                pointer = struct.unpack_from("<Q", header, pointer_qword * 8)[0]
                count = struct.unpack_from("<H", header, count_offset)[0]
                counts[owner] = count
                if not 0 < count <= 4096:
                    continue
                entries = _cached_qwords(pointer, count)
                if not entries:
                    continue


                hits = 0
                for entry in entries:
                    if _cached_is_metadata(entry):
                        hits += 1
                ratio = hits / len(entries)
                mean_sum += ratio
                mean_count += 1
                if ratio >= 0.9:
                    valid += 1
            if valid:
                candidates.append(
                    {
                        "pointer_qword": pointer_qword,
                        "count_byte_offset": count_offset,
                        "valid_owner_count": valid,
                        "mean_metadata_pointer_ratio": (
                            mean_sum / mean_count if mean_count else 0.0
                        ),
                        "counts_by_owner": counts,
                    }
                )
    return candidates


def _declaring_class_field(
    *,
    snapshot: MemorySnapshot,
    method_records: list[dict[str, Any]],
    scan_qwords: int = 32,
) -> int:


    windows: list[tuple[int, ...] | None] = [
        snapshot.qwords(record["metadata_pointer"], scan_qwords)
        for record in method_records
    ]
    candidates: list[int] = []
    for field in range(scan_qwords):
        matched = True
        for record, window in zip(method_records, windows):
            if window is not None:
                value = window[field]
            else:
                value = (
                    snapshot.qwords(record["metadata_pointer"], field + 1) or (0,)
                )[-1]
            if value != record["class_pointer"]:
                matched = False
                break
        if matched:
            candidates.append(field)
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime method declaring-class field is not unique "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def _method_record_qword_limit(
    *,
    snapshot: MemorySnapshot,
    method_records: list[dict[str, Any]],
    maximum_qwords: int = 64,
) -> int:
    by_region: dict[int, list[int]] = {}
    pointers = [record["metadata_pointer"] for record in method_records]
    if len(pointers) != len(set(pointers)):
        raise AcquisitionError("runtime method metadata pointers are duplicated")
    for pointer in pointers:
        region = snapshot._record_index(pointer)
        if region is None or pointer % 8:
            raise AcquisitionError("runtime method metadata pointer is invalid")
        by_region.setdefault(region, []).append(pointer)

    gaps: Counter[int] = Counter()
    for addresses in by_region.values():
        ordered = sorted(addresses)
        for left, right in zip(ordered, ordered[1:]):
            gap = right - left
            if gap % 8:
                raise AcquisitionError("runtime method record spacing is unaligned")
            if 0 < gap <= maximum_qwords * 8:
                gaps[gap // 8] += 1
    if not gaps:
        raise AcquisitionError("runtime method record stride is unavailable")
    support = max(gaps.values())
    candidates = [size for size, count in gaps.items() if count == support]
    if (
        len(candidates) != 1
        or not 2 <= candidates[0] <= maximum_qwords
        or support < 8
        or support * 4 < sum(gaps.values()) * 3
        or min(gaps) < candidates[0]
    ):
        raise AcquisitionError(
            "runtime method record stride is not unique "
            f"(candidates={len(candidates)}, support={support})"
        )
    return candidates[0]


def _method_pointer_field(
    *,
    snapshot: MemorySnapshot,
    method_records: list[dict[str, Any]],
    declaring_class_qword: int,
    scan_qwords: int,
) -> int:
    if not 0 <= declaring_class_qword < scan_qwords:
        raise AcquisitionError("runtime method declaring-class field is outside record")
    rows = [
        snapshot.qwords(record["metadata_pointer"], scan_qwords)
        for record in method_records
    ]
    if any(row is None for row in rows):
        raise AcquisitionError("runtime method record is not fully captured")
    candidates: list[int] = []
    for field in range(scan_qwords):
        if field == declaring_class_qword:
            continue
        values = [row[field] for row in rows if row is not None]
        executable = [value for value in values if _is_executable_pointer(snapshot, value)]
        zero = sum(value == 0 for value in values)


        if (
            len(executable) + zero == len(values)
            and len(executable) * 5 >= len(values) * 4
            and len(set(executable)) * 4 >= len(executable) * 3
        ):
            candidates.append(field)
    if len(candidates) != 1:
        raise AcquisitionError(
            "runtime method pointer field is not unique "
            f"(candidates={len(candidates)})"
        )
    return candidates[0]


def discover_runtime_class_model(
    *,
    snapshot_path: Path,
    bootstrap_model: Path,
    owner_roots_path: Path | None = None,
) -> dict[str, Any]:
    bootstrap = read_json(bootstrap_model)
    if (
        not isinstance(bootstrap, dict)
        or bootstrap.get("schema") != REFLECTION_BOOTSTRAP_SCHEMA
    ):
        raise AcquisitionError("runtime class bootstrap model is invalid")
    contract = reflection_contract()
    inventory = runtime_inventory_contract()
    required_all = Counter(
        operation["runtime_owner"] for operation in contract["operations"]
    )
    required_all.update(
        owner
        for operation in inventory["operations"]
        for owner in operation["runtime_owners"]
    )
    required_all.update(inventory["additional_required_runtime_owners"])
    layout_required_all = Counter(
        operation["runtime_owner"] for operation in contract["operations"]
    )
    layout_required_all.update(
        owner
        for operation in inventory["operations"]
        if operation["stage"] != "execution"
        for owner in operation["runtime_owners"]
    )
    layout_required_all.update(
        inventory["additional_required_runtime_owners"]
    )
    all_type_caches = {
        f"{cache['namespace']}.{cache['type_name']}": cache
        for cache in bootstrap["type_caches"]
    }
    cache_by_owner = {
        owner: cache
        for owner, cache in all_type_caches.items()
        if owner in required_all
    }
    if not cache_by_owner:
        raise AcquisitionError("runtime class contract owners are unavailable")
    with MemorySnapshot(snapshot_path) as snapshot:
        if snapshot.image_bytes != bootstrap["binary"]["size_of_image"]:
            raise AcquisitionError("runtime class snapshot image binding is stale")
        required_owner_pairs = tuple(
            sorted(tuple(owner.rsplit(".", 1)) for owner in required_all)
        )
        owner_roots = (
            load_runtime_owner_roots(
                owner_roots_path,
                executable_sha256=bootstrap["binary"]["sha256"],
                image_base=snapshot.image_base,
                image_bytes=snapshot.image_bytes,
                required_owner_pairs=required_owner_pairs,
                state_slot_rva=bootstrap["state_slot_rva"],
                resolver_helper_rva=bootstrap["type_resolver_helper_rva"],
            )
            if owner_roots_path is not None
            else None
        )
        available_addresses: dict[str, int] = (
            dict(owner_roots["roots"]) if owner_roots is not None else {}
        )
        if any(
            not _is_metadata_pointer(snapshot, class_pointer)
            for class_pointer in available_addresses.values()
        ):
            raise AcquisitionError(
                "runtime owner-root class object is absent from the snapshot"
            )
        needed_for_inheritance = {
            owner for pair in SEMANTIC_INHERITANCE_PAIRS for owner in pair
        }
        for owner, cache in all_type_caches.items():
            if owner not in required_all and owner not in needed_for_inheritance:
                continue
            values = snapshot.qwords(
                snapshot.image_base + cache["result_slot_rva"], 1
            )
            class_pointer = values[0] if values else 0
            if not class_pointer or not _is_metadata_pointer(snapshot, class_pointer):
                raise AcquisitionError(
                    f"runtime class object is unavailable for contract owner: {owner}"
                )
            resolved_pointer = available_addresses.get(owner)
            if resolved_pointer is not None and resolved_pointer != class_pointer:
                raise AcquisitionError(
                    f"runtime owner-root cache binding is stale: {owner}"
                )
            available_addresses[owner] = class_pointer
        parent_layout: dict[str, Any] | None = None
        base_classes_derived = owner_roots is not None and {
            "System.Reflection.MemberInfo",
            "System.Reflection.MethodBase",
        }.issubset(available_addresses)
        try:
            parent_layout = _discover_parent_class_field(
                snapshot=snapshot, class_addresses=available_addresses
            )
        except AcquisitionError:
            parent_layout = None
        if parent_layout is not None:
            method_info = available_addresses.get("System.Reflection.MethodInfo")
            type_class = available_addresses.get("System.Type")
            method_base = _parent_class_pointer(
                snapshot=snapshot,
                class_pointer=method_info or 0,
                layout=parent_layout,
            ) if method_info else 0
            member_from_type = _parent_class_pointer(
                snapshot=snapshot,
                class_pointer=type_class or 0,
                layout=parent_layout,
            ) if type_class else 0
            member_from_method = _parent_class_pointer(
                snapshot=snapshot,
                class_pointer=method_base,
                layout=parent_layout,
            ) if method_base else 0
            if (
                _is_metadata_pointer(snapshot, method_base)
                and _is_metadata_pointer(snapshot, member_from_type)
                and member_from_type == member_from_method
            ):
                if owner_roots is not None and (
                    available_addresses["System.Reflection.MethodBase"]
                    != method_base
                    or available_addresses["System.Reflection.MemberInfo"]
                    != member_from_type
                ):
                    raise AcquisitionError(
                        "runtime owner-root inheritance binding is stale"
                    )
                available_addresses["System.Reflection.MethodBase"] = method_base
                available_addresses["System.Reflection.MemberInfo"] = member_from_type
                if owner_roots is None:
                    base_classes_derived = True
        class_addresses = {
            owner: available_addresses[owner]
            for owner in required_all
            if owner in available_addresses
        }
        layout_class_addresses = {
            owner: class_pointer
            for owner, class_pointer in class_addresses.items()
            if owner in layout_required_all
        }
        required_observed = {
            owner: count
            for owner, count in layout_required_all.items()
            if owner in layout_class_addresses
        }
        class_headers = {
            owner: snapshot.qwords(address, 64) or ()
            for owner, address in layout_class_addresses.items()
        }
        if any(len(values) != 64 for values in class_headers.values()):
            raise AcquisitionError("runtime class header sample is incomplete")
        vtable_start = _discover_vtable_start(snapshot, class_headers)
        candidates = _member_layout_candidates(
            snapshot=snapshot,
            class_addresses=layout_class_addresses,
            vtable_start_qword=vtable_start,
        )
        layout = _select_semantic_member_layout(
            candidates=candidates,
            required_counts=required_observed,
            owner_count=len(layout_class_addresses),
        )
        method_records: list[dict[str, Any]] = []
        observed_method_counts: dict[str, int] = {}
        for owner, class_pointer in class_addresses.items():
            header = snapshot.read(class_pointer, vtable_start * 8)
            if header is None:
                raise AcquisitionError("runtime class header became unavailable")
            array_pointer = struct.unpack_from(
                "<Q", header, layout["pointer_qword"] * 8
            )[0]
            count = struct.unpack_from(
                "<H", header, layout["count_byte_offset"]
            )[0]
            entries = snapshot.qwords(array_pointer, count)
            if not entries:
                raise AcquisitionError("runtime class method array is unavailable")
            observed_method_counts[owner] = count
            method_records.extend(
                {
                    "runtime_owner": owner,
                    "method_index": index,
                    "metadata_pointer": pointer,
                    "class_pointer": class_pointer,
                }
                for index, pointer in enumerate(entries)
            )
        method_record_qwords = _method_record_qword_limit(
            snapshot=snapshot, method_records=method_records
        )
        declaring_field = _declaring_class_field(
            snapshot=snapshot, method_records=method_records,
            scan_qwords=method_record_qwords,
        )
        method_pointer_field = _method_pointer_field(
            snapshot=snapshot,
            method_records=method_records,
            declaring_class_qword=declaring_field,
            scan_qwords=method_record_qwords,
        )
        for record in method_records:
            values = snapshot.qwords(
                record["metadata_pointer"], method_pointer_field + 1
            )
            record["method_pointer"] = values[-1] if values else 0

        missing_owners = sorted(set(required_all) - set(class_addresses))
        snapshot_identity = file_identity(snapshot_path)
        return {
            "schema": RUNTIME_CLASS_SCHEMA,
            "status": "discovered",
            "scope": "runtime-reflection-bootstrap-contract",
            "snapshot": {
                "bytes": snapshot_identity["bytes"],
                "sha256": snapshot_identity["sha256"],
                "image_bytes": snapshot.image_bytes,
            },
            "bootstrap_model_sha256": file_identity(bootstrap_model)["sha256"],
            "owner_root_manifest": {
                "sha256": owner_roots["identity"]["sha256"],
                "bytes": owner_roots["identity"]["bytes"],
                "owner_count": owner_roots["owner_count"],
            }
            if owner_roots is not None
            else None,
            "layout": {
                "vtable_start_qword": vtable_start,
                "parent_class_qword": (
                    parent_layout["qword"] if parent_layout is not None else None
                ),
                "parent_class_byte_offset": (
                    parent_layout["byte_offset"]
                    if parent_layout is not None
                    else None
                ),
                "parent_class_pointer_encoding": (
                    parent_layout["encoding"]
                    if parent_layout is not None
                    else None
                ),
                "method_array_pointer_qword": layout["pointer_qword"],
                "method_count_byte_offset": layout["count_byte_offset"],
                "method_record_qwords": method_record_qwords,
                "declaring_class_qword": declaring_field,
                "method_pointer_qword": method_pointer_field,
            },
            "classes": [
                {
                    "runtime_owner": owner,
                    "class_pointer": class_pointer,
                    "method_count": observed_method_counts[owner],
                }
                for owner, class_pointer in sorted(class_addresses.items())
            ],
            "methods": method_records,
            "contract": {
                "contract_id": contract["contract_id"],
                "operation_count": contract["operation_count"],
                "runtime_inventory_contract_id": inventory["contract_id"],
                "runtime_inventory_operation_count": inventory["operation_count"],
                "missing_runtime_owner_classes": missing_owners,
                "semantic_operation_resolution_complete": False,
                "all_game_classes_claimed": False,
            },
            "checks": {
                "snapshot_image_binding_matches": True,
                "vtable_boundary_derived": True,
                "method_layout_semantically_unique": True,
                "method_record_stride_derived": True,
                "declaring_class_field_unique": True,
                "method_pointer_field_unique": True,
                "all_observed_contract_owners_enumerated": True,
                "all_contract_owner_classes_present": not missing_owners,
                "owner_root_manifest_bound": owner_roots is not None,
                "owner_root_contract_exact": owner_roots is not None,
                "owner_root_raw_pointers_owner_only": True,
                "parent_class_field_unique": parent_layout is not None,
                "base_reflection_classes_derived": base_classes_derived,
                "semantic_operation_resolution_complete": False,
                "official_runtime_attested": False,
                "acceptance_eligible": False,
                "fixed_address_used": False,
                "fixed_offset_used": False,
                "fixed_version_used": False,
                "saved_reference_values_used": False,
                "external_runtime_component_used": False,
            },
        }


def inspect_runtime_class_model(
    *,
    snapshot: Path,
    bootstrap_model: Path,
    output: Path,
    owner_roots: Path | None = None,
) -> dict[str, Any]:
    model = discover_runtime_class_model(
        snapshot_path=snapshot,
        bootstrap_model=bootstrap_model,
        owner_roots_path=owner_roots,
    )
    output = output.expanduser().resolve()
    _private_json(output, model)
    return {
        "schema": RUNTIME_CLASS_SCHEMA,
        "status": model["status"],
        "scope": model["scope"],
        "snapshot": model["snapshot"],
        "class_count": len(model["classes"]),
        "method_count": len(model["methods"]),
        "missing_runtime_owner_class_count": len(
            model["contract"]["missing_runtime_owner_classes"]
        ),
        "semantic_operation_resolution_complete": model["contract"][
            "semantic_operation_resolution_complete"
        ],
        "checks": model["checks"],
        "raw_addresses_offsets_and_method_pointers_owner_only": True,
        "output": str(output),
    }


from alpha.h01 import AcquisitionError
from alpha.c01 import direct_reference_getter
from alpha.p14 import RuntimeRangeView, _requests
from operator import itemgetter as _itemgetter

_RANGE_ADDRESS_KEY = _itemgetter(0)


def merged_ranges(ranges):

    result = []
    append = result.append
    last_begin = last_end = 0


    for address, size in sorted(ranges, key=_RANGE_ADDRESS_KEY):
        if type(address) is not int or type(size) is not int or address <= 0 or size <= 0:
            raise AcquisitionError("Module owner observation range is invalid")
        if result and address <= last_end:
            if address + size > last_end:
                last_end = address + size
                result[-1] = (last_begin, last_end - last_begin)
        else:
            append((address, size))
            last_begin, last_end = address, address + size
    return _requests(result)


def owner_memory_requests(model, modules):
    edges = model.get("direct_edges")
    if not isinstance(edges, list) or not edges or not modules or len(set(modules)) != len(modules):
        raise AcquisitionError("Module owner candidate or owner domain is absent")
    ranges, width = [], 8
    for edge in edges:
        try:
            code = bytes.fromhex(edge["code_hex"])
            getter = direct_reference_getter(code)
        except (KeyError, ValueError, TypeError) as error:
            raise AcquisitionError("Module owner getter encoding is invalid") from error
        if any(type(edge.get(key)) is not type(value) or edge[key] != value for key, value in getter.items()):
            raise AcquisitionError("Module owner field displacement differs from code")
        if type(edge.get("method_pointer")) is not int or edge["method_pointer"] <= 0:
            raise AcquisitionError("Module owner candidate method pointer is absent")
        width = max(width, getter["byte_offset"] + 8)
        ranges.append((edge["method_pointer"], len(code)))
    for module in modules:
        if type(module) is not int or module <= 0 or module & 7:
            raise AcquisitionError("Module owner pointer is invalid")
        ranges.append((module, width))
    return merged_ranges(ranges)


def replay_owner_fields(*, model, modules, identity_rows, ancestry_rows, observation, expected=None):
    owner_memory_requests(model, modules)
    view = RuntimeRangeView(observation)
    identities = {row[0]: row for row in identity_rows}
    classes = {row[3]: row[0] for row in identity_rows}
    if len(identities) != len(identity_rows) or len(classes) != len(identity_rows):
        raise AcquisitionError("Module owner identity domain repeats")
    parents = {}
    for row in ancestry_rows:
        if row[0] not in identities or row[0] in parents or identities[row[0]][3] != row[2]:
            raise AcquisitionError("Module owner ancestry source differs")
        parents[row[0]] = None if not row[3] else classes.get(row[3], "unresolved")
    if set(parents) != set(identities):
        raise AcquisitionError("Module owner ancestry domain is incomplete")
    def chain(klass):
        if klass not in classes:
            raise AcquisitionError("Module owner observed class is outside current TypeDef domain")
        result, current = [], classes[klass]
        while current is not None:
            if current == "unresolved" or current in result:
                raise AcquisitionError("Module owner lineage is unresolved or cyclic")
            result.append(current); current = parents[current]
        return result
    def pointer(address):
        raw = view.read(address, 8)
        if raw is None:
            raise AcquisitionError("Module owner pointer observation is missing")
        value = int.from_bytes(raw, "little")
        if not value or value & 7:
            raise AcquisitionError("Module owner field is not a nonnull aligned reference")
        return value
    rows = []
    for module in modules:
        klass = pointer(module)
        lineage = chain(klass)
        if model["module_type_index"] not in lineage:
            raise AcquisitionError("Module owner observed receiver is not a Module descendant")
        edges = [edge for edge in model["direct_edges"] if edge["declaring_type_index"] in lineage]
        if len(edges) != 1:
            raise AcquisitionError("Module owner field operation is not unique for the actual class")
        edge = edges[0]
        target = identities.get(edge["return_type_index"])
        if (target is None or target[3] != edge["return_class_pointer"] or target[2] != edge["return_descriptor"]
                or target[1] & 64 or identities[edge["declaring_type_index"]][3] != edge["declaring_class_pointer"]):
            raise AcquisitionError("Module owner return is not a closed reference-type descriptor")
        code = bytes.fromhex(edge["code_hex"])
        if view.read(edge["method_pointer"], len(code)) != code:
            raise AcquisitionError("Module owner live getter code differs from current executable")
        owner = pointer(module + edge["byte_offset"])
        row = {"module_pointer": module, "module_class": klass, "owner_pointer": owner,
            "method_pointer": edge["method_pointer"], "metadata_pointer": edge["metadata_pointer"],
            "byte_offset": edge["byte_offset"], "return_type_index": edge["return_type_index"]}
        if expected is not None:
            owner_class = pointer(owner)
            if edge["return_type_index"] not in chain(owner_class):
                raise AcquisitionError("Module owner observed object class contradicts the declared return type")
            row["owner_class"] = owner_class
        rows.append(row)
    if expected is not None and [{key: value for key, value in row.items() if key != "owner_class"} for row in rows] != expected:
        raise AcquisitionError("Module owner fields or live code changed between observations")
    return rows


from dataclasses import dataclass

from alpha.h01 import AcquisitionError
from alpha.c03 import evaluate
from alpha.p14 import RuntimeRangeView, _requests


def coalesce_ranges(ranges, *, max_gap=0):


    if type(max_gap) is not int or not 0 <= max_gap <= 65536:
        raise AcquisitionError("native read graph batching gap is invalid")
    output = []
    for address, size in sorted(ranges):
        if type(address) is not int or type(size) is not int or address <= 0 or size <= 0 or address + size > 1 << 64:
            raise AcquisitionError("native read graph range bounds are invalid")
        if output and address <= output[-1][0] + output[-1][1] + max_gap:
            start, length = output[-1]
            output[-1] = start, max(start + length, address + size) - start
        else:
            output.append((address, size))
    return _requests(output)


def _checked_capture(ranges, capture):
    observed = capture(ranges)
    if not isinstance(observed, dict) or any(not isinstance(value, bytes) for value in observed.values()):
        raise AcquisitionError("native read graph capture has invalid payloads")
    if sorted((address, len(value)) for address, value in observed.items()) != ranges:
        raise AcquisitionError("native read graph capture returned different ranges")
    RuntimeRangeView(observed)
    return observed


def _merge(old, new):
    merged = []
    for address, payload in sorted([*old.items(), *new.items()], key=lambda item: item[0]):
        if merged and address <= merged[-1][0] + len(merged[-1][1]):
            start, current = merged[-1]
            offset = address - start
            overlap = min(len(current) - offset, len(payload))
            if current[offset:offset + overlap] != payload[:overlap]:
                raise AcquisitionError("native read graph dependency changed between observations")
            current.extend(payload[overlap:])
        else:
            merged.append((address, bytearray(payload)))
    return {address: bytes(payload) for address, payload in merged}


def _loads(expr):
    for child in expr[1:]:
        if isinstance(child, tuple):
            yield from _loads(child)
    if expr[0] == "load":
        yield expr


class _NeedRead(Exception):
    pass


@dataclass(frozen=True)
class NativeReadGraph:
    observed: dict[int, bytes]
    discovery_waves: int

    def view(self):
        return RuntimeRangeView(self.observed)


def resolve_native_read_graph(cases, *, capture, max_waves=8, initial=None):

    if type(max_waves) is not int or not 1 <= max_waves <= 32:
        raise AcquisitionError("native read graph wave bound is invalid")
    cases = tuple(cases)
    if not cases:
        raise AcquisitionError("native read graph has no cases")
    load_cache = {}
    prepared = []
    for expr, values in cases:
        if expr not in load_cache:
            load_cache[expr] = tuple(_loads(expr))
        prepared.append((load_cache[expr], values))
    observed = dict(initial.observed) if initial is not None else {}
    waves = initial.discovery_waves if initial is not None else 0
    while True:
        requests = set()
        view = RuntimeRangeView(observed) if observed else None
        class Reader:
            def read(self, address, width):
                value = view.read(address, width) if view is not None else None
                if value is None:
                    requests.add((address, width))
                    raise _NeedRead
                return value
        reader = Reader()
        for loads, values in prepared:
            for node in loads:
                try:
                    evaluate(node, values, reader)
                except _NeedRead:
                    pass
        if not requests:

            for expr, values in cases:
                evaluate(expr, values, reader)
            return NativeReadGraph(observed, waves)
        if waves >= max_waves:
            raise AcquisitionError("native read graph exceeded bounded discovery waves")
        ranges = coalesce_ranges(requests)
        fresh = _checked_capture(ranges, capture)
        observed = _merge(observed, fresh)
        waves += 1


def reobserve_native_read_graph(graph: NativeReadGraph, *, extra_ranges, capture, max_gap=0):

    ranges = coalesce_ranges([*((address, len(data)) for address, data in graph.observed.items()), *extra_ranges], max_gap=max_gap)
    fresh = _checked_capture(ranges, capture)
    view = RuntimeRangeView(fresh)
    for address, value in graph.observed.items():
        if view.read(address, len(value)) != value:
            raise AcquisitionError("native read graph changed before final observation")
    return view


def specialize_expression(expr, values, reader):

    from alpha.c03 import variables
    if variables(expr) <= values.keys():
        return ("constant", evaluate(expr, values, reader))
    return tuple(specialize_expression(child, values, reader) if isinstance(child, tuple) else child for child in expr)


from alpha.p12 import _wide_literal, _windows_z_path
from alpha.h01 import AcquisitionError
from alpha.p14 import _READER
from alpha.c04 import native_string_reader_source
from alpha.c05 import SCOPE, capture_binding, transport_digest


def attach_reference_names(source, *, binding, seed_identity, raw_path, io_path):
    contract = binding["string_layout_contract"]
    digest = transport_digest(capture_binding(
        dict(binding["binary"], executable_sha256=binding["binary"]["sha256"],
             process_id=binding["process_id"], creation_filetime=binding["creation_filetime"]),
        dict(binding, seed=seed_identity)))
    reader = native_string_reader_source(contract=contract, output_path=io_path,
        include_utf8_reader=False, sample_scope=SCOPE)

    reader += _READER[:_READER.index("static int managed_utf8(")]
    begin = source.index("static int managed_utf8(")
    end = source.index("static int append_text(", begin)
    source = source[:begin] + "#define ALPHA_MAX_MANAGED_TEXT ALPHA_MAX_TEXT\n" + reader + (
        "static const wchar_t reference_raw_path[]=" + _wide_literal(_windows_z_path(raw_path)) + ";\n"
        "static const unsigned char reference_raw_binding[32]={" + ",".join(map(str, digest)) + "};\n"
    ) + NATIVE + source[end:]
    old = "if(!managed_utf8(get_name(object,name_metadata),1,&name,&name_bytes)||!managed_utf8(get_namespace(object,namespace_metadata),1,&space,&space_bytes))"
    new = "if(!capture_reference_names(target->descriptor,get_name(object,name_metadata),get_namespace(object,namespace_metadata),&name,&name_bytes,&space,&space_bytes))"
    if source.count(old) != 1:
        raise AcquisitionError("raw TypeRef name capture seam differs")
    source = source.replace(old, new, 1)
    old = '"EmptyTypeRef_%llX",(unsigned long long)target->descriptor'
    if source.count(old) != 1:
        raise AcquisitionError("TypeRef display alias seam differs")
    source = source.replace(old, '"EmptyTypeRef_%llX",(unsigned long long)capture_index', 1)
    old = "int ok=reference_instance_current()&&write_output();"
    if source.count(old) != 1:
        raise AcquisitionError("raw TypeRef output seam differs")
    return source.replace(old, "int ok=reference_instance_current()&&write_reference_raw()&&write_string_io_probe()&&write_output();", 1)


NATIVE = r'''
static FILE *reference_private_output(const wchar_t *path);
static int reference_instance_current(void);
struct reference_raw_header {
    char magic[8]; uint32_t version, header_bytes, row_bytes, reserved;
    uint64_t count, bytes; unsigned char binding[32];
};
struct reference_raw_row {
    uint64_t descriptor, index; uint32_t null_name, null_space, name_bytes, space_bytes;
    uint64_t name_offset, space_offset;
};
_Static_assert(sizeof(struct reference_raw_header)==72,"ALPHATN1 header");
_Static_assert(sizeof(struct reference_raw_row)==48,"ALPHATN1 row");
static struct reference_raw_row *reference_raw_rows;
static unsigned char *reference_raw_pool;
static uint64_t reference_raw_count, reference_raw_capacity, reference_raw_bytes, reference_raw_pool_capacity;
static int reference_raw_written;
static int append_reference_raw(uint64_t descriptor, int null_name, int null_space,
        const char *name, uint32_t n, const char *space, uint32_t s) {
    if (reference_raw_written || !descriptor || descriptor%8 ||
        reference_raw_count>=ALPHA_MAX_NODES || null_name<0 || null_name>1 || null_space<0 || null_space>1 ||
        (null_name&&n) || (null_space&&s) || (!name&&n) || (!space&&s) ||
        n>65536u || s>65536u || (uint64_t)n+s>268435456ull-reference_raw_bytes) return 0;
    if (reference_raw_count==reference_raw_capacity) {
        uint64_t next=reference_raw_capacity?reference_raw_capacity*2u:64u;
        if(next>ALPHA_MAX_NODES)next=ALPHA_MAX_NODES;
        struct reference_raw_row *grown=realloc(reference_raw_rows,(size_t)next*sizeof(*grown));
        if(!grown)return 0;reference_raw_rows=grown;reference_raw_capacity=next;
    }
    uint64_t required=reference_raw_bytes+n+s;
    if(required>reference_raw_pool_capacity) {
        uint64_t next=reference_raw_pool_capacity?reference_raw_pool_capacity:1024u;
        while(next<required)next*=2u;
        unsigned char *grown=realloc(reference_raw_pool,(size_t)next);
        if(!grown)return 0;reference_raw_pool=grown;reference_raw_pool_capacity=next;
    }
    reference_raw_rows[reference_raw_count]=(struct reference_raw_row){descriptor,reference_raw_count,
        (uint32_t)null_name,(uint32_t)null_space,n,s,reference_raw_bytes,reference_raw_bytes+n};
    if(n)memcpy(reference_raw_pool+reference_raw_bytes,name,n);
    if(s)memcpy(reference_raw_pool+reference_raw_bytes+n,space,s);
    reference_raw_bytes=required;reference_raw_count++;return 1;
}
static int capture_reference_names(uint64_t descriptor, uintptr_t name_object, uintptr_t space_object,
        char **name, uint32_t *n, char **space, uint32_t *s) {
    *name=NULL;*space=NULL;*n=*s=0;
    if ((name_object&&!event_string_utf8(name_object,1,name,n)) ||
        (space_object&&!event_string_utf8(space_object,1,space,s))) return 0;
    return append_reference_raw(descriptor,!name_object,!space_object,*name,*n,*space,*s);
}
static int write_reference_raw(void) {
    if(reference_raw_written || !reference_instance_current() || !node_count ||
       reference_raw_count!=node_count || completed_nodes!=node_count)return 0;
    for(uint64_t i=0;i<node_count;i++)if(reference_raw_rows[i].descriptor!=records[i].descriptor)return 0;
    struct reference_raw_header header={0};memcpy(header.magic,"ALPHATN1",8);
    header.version=1;header.header_bytes=sizeof(header);header.row_bytes=sizeof(*reference_raw_rows);
    header.count=reference_raw_count;header.bytes=reference_raw_bytes;memcpy(header.binding,reference_raw_binding,32);
    FILE *out=reference_private_output(reference_raw_path);if(!out)return 0;
    int ok=fwrite(&header,1,sizeof(header),out)==sizeof(header)&&
        fwrite(reference_raw_rows,sizeof(*reference_raw_rows),reference_raw_count,out)==reference_raw_count&&
        (!reference_raw_bytes||fwrite(reference_raw_pool,1,reference_raw_bytes,out)==reference_raw_bytes)&&
        reference_instance_current();
    if(fclose(out))ok=0;
    if(!ok)_wremove(reference_raw_path);else reference_raw_written=1;
    return ok;
}
'''
