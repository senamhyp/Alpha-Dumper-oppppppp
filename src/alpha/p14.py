import re
import struct
from collections import Counter
from pathlib import Path
from typing import Any

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError, same_executable_path
from alpha.p01 import reflection_contract
from alpha.c04 import MappedPE, RESOLVER_SCHEMA
from alpha.h02 import file_identity, read_json


REFLECTION_BOOTSTRAP_SCHEMA = "alpha.runtime-reflection-bootstrap/v1"

_STATE_DERIVATION = re.compile(
    rb"(?:[\x48-\x4f][\xb8-\xbf].{8})?"
    rb"[\x48-\x4f]\x8b(?:"
    rb"[\x40\x48\x50\x58\x60\x68\x70\x78].|"
    rb"[\x80\x88\x90\x98\xa0\xa8\xb0\xb8].{4}|"
    rb"[\x00\x08\x10\x18\x20\x28\x30\x38])"
    rb"[\x48-\x4f](?:\x01|\x03)."
    rb"[\x40-\x4f]\x89[\x05\x0d\x15\x1d\x25\x2d\x35\x3d](.{4})",
    re.DOTALL,
)


_RIP_RELATIVE_STATE_STORE = re.compile(
    rb"[\x40-\x4f]\x89[\x05\x0d\x15\x1d\x25\x2d\x35\x3d](.{4})",
    re.DOTALL,
)
_TYPE_CACHE = re.compile(
    rb"\x48\x8b\x0d(.{4})"
    rb"\x48\x8d\x15(.{4})"
    rb"\x4c\x8d\x05(.{4})"
    rb".{0,16}?\xe8(.{4})"
    rb"\x48\x89\x05(.{4})",
    re.DOTALL,
)
_TYPE_HELPER_USE = re.compile(
    rb"\x48\x8b\x0d(.{4})"
    rb"\xba(.{4})"
    rb"\x45[\x31\x33]\xc0"
    rb"\xe8(.{4})"
    rb"\x48(?:\x89\xc1|\x8b\xc8)"
    rb"\xe8(.{4})",
    re.DOTALL,
)
_SEMANTIC_TEXT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.`+<>-]{0,159}$")


def _signed(value: bytes) -> int:
    return struct.unpack("<i", value)[0]


def _derived_state_slot_from_window(*, window: bytes, after_call_rva: int) -> int:
    matches = list(_STATE_DERIVATION.finditer(window))
    if len(matches) == 1:
        match = matches[0]
        displacement_start = match.start(1)
        store_rva = after_call_rva + displacement_start - 3
        return store_rva + 7 + _signed(match.group(1))
    candidates = _derived_state_slots_from_window(
        window=window, after_call_rva=after_call_rva
    )
    if len(candidates) == 1:
        return candidates[0]
    raise AcquisitionError(
        "runtime reflection state derivation is not unique "
        f"(candidates={len(candidates)})"
    )


def _derived_state_slots_from_window(
    *, window: bytes, after_call_rva: int
) -> list[int]:


    return sorted(
        {
            after_call_rva + match.start() + 7 + _signed(match.group(1))
            for match in _RIP_RELATIVE_STATE_STORE.finditer(window)
        }
    )


def _semantic_string(image: MappedPE, rva: int) -> str | None:
    offset = image.rva_to_offset(rva)
    if offset is None:
        return None
    end = image._mapping.find(b"\0", offset, min(len(image._mapping), offset + 161))
    if end < 0:
        return None
    try:
        value = bytes(image._mapping[offset:end]).decode("ascii")
    except UnicodeDecodeError:
        return None
    return value if _SEMANTIC_TEXT.fullmatch(value) else None


def _type_caches(image: MappedPE, state_slot_rva: int) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for section in image.executable_sections:
        for match in _TYPE_CACHE.finditer(
            image._mapping, section.raw_offset, section.raw_end
        ):
            site_rva = image.offset_to_rva(section, match.start())
            observed_state = site_rva + 7 + _signed(match.group(1))
            if observed_state != state_slot_rva:
                continue
            namespace = _semantic_string(
                image, site_rva + match.start(2) - match.start() + 4 + _signed(match.group(2))
            )
            type_name = _semantic_string(
                image, site_rva + match.start(3) - match.start() + 4 + _signed(match.group(3))
            )
            if namespace is None or type_name is None:
                continue
            call_rva = site_rva + match.start(4) - match.start() - 1
            helper_rva = call_rva + 5 + _signed(match.group(4))
            store_rva = site_rva + match.start(5) - match.start() - 3
            result_slot_rva = store_rva + 7 + _signed(match.group(5))
            if not image.executable_rva(helper_rva) or image.executable_rva(result_slot_rva):
                continue
            records.append(
                {
                    "namespace": namespace,
                    "type_name": type_name,
                    "site_rva": site_rva,
                    "resolver_helper_rva": helper_rva,
                    "result_slot_rva": result_slot_rva,
                }
            )
    return records


def _type_helper_candidates(
    image: MappedPE, type_caches: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    by_slot: dict[int, list[dict[str, Any]]] = {}
    for cache in type_caches:
        by_slot.setdefault(cache["result_slot_rva"], []).append(cache)
    records: list[dict[str, Any]] = []
    for section in image.executable_sections:
        for match in _TYPE_HELPER_USE.finditer(
            image._mapping, section.raw_offset, section.raw_end
        ):
            site_rva = image.offset_to_rva(section, match.start())
            type_slot_rva = site_rva + 7 + _signed(match.group(1))
            caches = by_slot.get(type_slot_rva, [])
            if len(caches) != 1:
                continue
            selector_call_rva = site_rva + match.start(3) - match.start() - 1
            selector_rva = selector_call_rva + 5 + _signed(match.group(3))
            unwrap_call_rva = site_rva + match.start(4) - match.start() - 1
            unwrap_rva = unwrap_call_rva + 5 + _signed(match.group(4))
            if not image.executable_rva(selector_rva) or not image.executable_rva(unwrap_rva):
                continue
            cache = caches[0]
            records.append(
                {
                    "namespace": cache["namespace"],
                    "type_name": cache["type_name"],
                    "site_rva": site_rva,
                    "selector_argument": struct.unpack("<I", match.group(2))[0],
                    "first_helper_rva": selector_rva,
                    "second_helper_rva": unwrap_rva,
                    "semantic_identity": None,
                }
            )
    return records


def discover_reflection_bootstrap(
    *, binary: Path, resolver_model: Path
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    resolver = read_json(resolver_model)
    if not isinstance(resolver, dict) or resolver.get("schema") != RESOLVER_SCHEMA:
        raise AcquisitionError("runtime reflection resolver model is invalid")
    identity = file_identity(binary)
    resolver_binary = resolver.get("binary")
    if (
        not isinstance(resolver_binary, dict)
        or resolver_binary.get("sha256") != identity["sha256"]
        or resolver_binary.get("bytes") != identity["bytes"]
    ):
        raise AcquisitionError("runtime reflection resolver target binding is stale")
    selected = resolver.get("selected")
    if not isinstance(selected, dict) or not isinstance(selected.get("call_rva"), int):
        raise AcquisitionError("runtime reflection resolver selection is unavailable")

    with MappedPE(binary) as image:
        call_offset = image.rva_to_offset(selected["call_rva"])
        if call_offset is None:
            raise AcquisitionError("runtime reflection selected call is outside the target")
        after_call_rva = selected["call_rva"] + 5
        state_slot_candidates = _derived_state_slots_from_window(
            window=bytes(image._mapping[call_offset + 5 : call_offset + 69]),
            after_call_rva=after_call_rva,
        )
        state_graphs: list[dict[str, Any]] = []
        for state_slot_candidate in state_slot_candidates:
            if image.executable_rva(state_slot_candidate):
                continue
            candidate_type_caches = _type_caches(image, state_slot_candidate)
            if not candidate_type_caches:
                continue
            candidate_helper_counts = Counter(
                cache["resolver_helper_rva"] for cache in candidate_type_caches
            )
            if len(candidate_helper_counts) != 1:
                continue
            candidate_helper_rows = _type_helper_candidates(
                image, candidate_type_caches
            )
            if not candidate_helper_rows:
                continue
            candidate_first_count = len(
                {record["first_helper_rva"] for record in candidate_helper_rows}
            )
            candidate_second_count = len(
                {record["second_helper_rva"] for record in candidate_helper_rows}
            )
            if candidate_first_count != 1 or candidate_second_count != 1:
                continue
            state_graphs.append(
                {
                    "state_slot_rva": state_slot_candidate,
                    "type_caches": candidate_type_caches,
                    "helper_counts": candidate_helper_counts,
                    "helper_candidates": candidate_helper_rows,
                }
            )
        if len(state_graphs) != 1:
            raise AcquisitionError(
                "runtime reflection state graph is not unique "
                f"(stores={len(state_slot_candidates)}, "
                f"complete_graphs={len(state_graphs)})"
            )
        state_graph = state_graphs[0]
        state_slot_rva = state_graph["state_slot_rva"]
        type_caches = state_graph["type_caches"]
        helper_counts = state_graph["helper_counts"]
        helper_candidates = state_graph["helper_candidates"]

        contract = reflection_contract()
        pair_counts = Counter(
            (cache["namespace"], cache["type_name"]) for cache in type_caches
        )
        concrete_owner_pairs = {
            tuple(operation["runtime_owner"].rsplit(".", 1))
            for operation in contract["operations"]
        }
        observed_contract_owner_pairs = sorted(
            pair for pair in concrete_owner_pairs if pair_counts[pair] == 1
        )
        return {
            "schema": REFLECTION_BOOTSTRAP_SCHEMA,
            "status": "discovered",
            "binary": {
                "bytes": identity["bytes"],
                "sha256": identity["sha256"],
                "size_of_image": image.size_of_image,
            },
            "resolver_model_sha256": file_identity(resolver_model)["sha256"],
            "state_slot_rva": state_slot_rva,
            "type_caches": type_caches,
            "type_resolver_helper_rva": next(iter(helper_counts)),
            "type_helper_candidates": helper_candidates,
            "contract": {
                "contract_id": contract["contract_id"],
                "operation_count": contract["operation_count"],
                "observed_concrete_owner_pairs": [
                    {"namespace": pair[0], "type_name": pair[1]}
                    for pair in observed_contract_owner_pairs
                ],
                "semantic_operation_resolution_complete": False,
            },
            "checks": {
                "target_identity_bound": True,
                "resolver_model_identity_bound": True,
                "derived_state_slot_unique": True,
                "derived_state_slot_non_executable": True,
                "type_resolver_helper_unique": True,
                "first_type_helper_unique": True,
                "second_type_helper_unique": True,
                "helper_semantics_resolved": False,
                "semantic_operation_resolution_complete": False,
                "fixed_address_used": False,
                "fixed_rva_used": False,
                "fixed_ordinal_used": False,
                "fixed_version_used": False,
                "saved_runtime_output_used": False,
                "external_runtime_component_used": False,
            },
        }


def inspect_reflection_bootstrap(
    *, binary: Path, resolver_model: Path, output: Path
) -> dict[str, Any]:
    model = discover_reflection_bootstrap(
        binary=binary, resolver_model=resolver_model
    )
    output = output.expanduser().resolve()
    _private_json(output, model)
    return {
        "schema": REFLECTION_BOOTSTRAP_SCHEMA,
        "status": model["status"],
        "binary": model["binary"],
        "type_cache_count": len(model["type_caches"]),
        "type_helper_candidate_count": len(model["type_helper_candidates"]),
        "observed_contract_owner_pair_count": len(
            model["contract"]["observed_concrete_owner_pairs"]
        ),
        "reflection_operation_count": model["contract"]["operation_count"],
        "semantic_operation_resolution_complete": model["contract"][
            "semantic_operation_resolution_complete"
        ],
        "checks": model["checks"],
        "raw_addresses_and_helper_arguments_owner_only": True,
        "output": str(output),
    }


from alpha.c04 import native_string_reader_source, validate_string_layout_io


SAMPLE_SCOPE = "event-module-raw-names"


def event_string_reader_source(*, contract, output_path):
    return (native_string_reader_source(contract=contract, output_path=output_path,
            include_utf8_reader=False, sample_scope=SAMPLE_SCOPE) + _READER)


def validate_event_string_io(*, observation, names, expected_process_id, contract):
    from alpha.h01 import AcquisitionError
    if {name.domain for name in names} - {"event", "module"}:
        raise AcquisitionError("Event/Module String I/O contains a foreign name domain")
    return validate_string_layout_io(observation=observation, names=names,
        expected_process_id=expected_process_id, contract=contract, expected_scope=SAMPLE_SCOPE)


_READER = r'''


static int event_string_utf8(uintptr_t object, int record_io, char **output, uint32_t *bytes) {
    *output = NULL; *bytes = 0;
    if (object > UINTPTR_MAX - observed_string_data_offset -
            (uintptr_t)ALPHA_MAX_MANAGED_TEXT * sizeof(uint16_t) ||
        !string_io_code_unchanged() || !object_class(object, observed_string_class) ||
        !readable(object + observed_string_length_offset, sizeof(int32_t))) return 0;
    int32_t length = 0;
    memcpy(&length, (const void *)(object + observed_string_length_offset), sizeof(length));
    if (length < 0 || (uint32_t)length > ALPHA_MAX_MANAGED_TEXT ||
        (length && !readable(object + observed_string_data_offset, (SIZE_T)length * sizeof(uint16_t)))) return 0;
    int32_t (*length_fn)(uintptr_t, uintptr_t) = (void *)observed_string_length_pointer;
    uint16_t (*indexer_fn)(uintptr_t, int32_t, uintptr_t) = (void *)observed_string_indexer_pointer;
    if (length_fn(object, observed_string_length_metadata) != length) return 0;
    SIZE_T extent = (SIZE_T)length * sizeof(uint16_t);
    uint16_t *snapshot = malloc(extent ? extent : sizeof(uint16_t));
    if (!snapshot) return 0;
    if (extent) memcpy(snapshot, (const void *)(object + observed_string_data_offset), extent);
    for (int32_t i = 0; i < length; i++) {
        if (indexer_fn(object, i, observed_string_indexer_metadata) != snapshot[i]) { free(snapshot); return 0; }
    }
    int32_t final_length = 0;
    memcpy(&final_length, (const void *)(object + observed_string_length_offset), sizeof(final_length));
    if (final_length != length || length_fn(object, observed_string_length_metadata) != length ||
        !string_io_code_unchanged() || (record_io && !probe_observed_string_io(object)) ||
        (extent && memcmp(snapshot, (const void *)(object + observed_string_data_offset), extent))) {
        free(snapshot); return 0;
    }
    if (!length) { free(snapshot); return 1; }
    int required = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, (const wchar_t *)snapshot,
        length, NULL, 0, NULL, NULL);
    if (required <= 0 || required > 4 * (int)ALPHA_MAX_MANAGED_TEXT) { free(snapshot); return 0; }
    char *value = malloc((SIZE_T)required);
    if (!value || WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, (const wchar_t *)snapshot,
        length, value, required, NULL, NULL) != required) { free(snapshot); free(value); return 0; }
    free(snapshot);


    *output = value; *bytes = (uint32_t)required; return 1;
}
static int managed_utf8(uintptr_t object, char **output, uint32_t *bytes) {
    return event_string_utf8(object, 0, output, bytes);
}
static int managed_utf8_recorded(uintptr_t object, char **output, uint32_t *bytes) {
    return event_string_utf8(object, 1, output, bytes);
}
'''


from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.p01 import project_fields
from alpha.c04 import _verify_files
from alpha.h02 import file_identity, read_json


def require_reference_extension(base_nodes, selected_nodes):

    if not base_nodes or any(selected_nodes.get(key) != row for key, row in base_nodes.items()):
        raise AcquisitionError("constructed field output TypeRef extension changes its base graph")


def render_observed_field(renderer, fields, *, owner, ordinal, pointer, definition):
    row = fields.get((owner, ordinal))
    if (row is None or row["field_metadata_pointer"] != pointer
            or row["definition_index"] != definition):
        raise AcquisitionError("constructed field output native observation is absent or mismatched")
    return renderer.render(row["descriptor"]), row["attributes"]


def bind_output_constructed_fields(*, field_capture, reference_model, reference_inventory,
                                  constructed_model, constructed_inventory,
                                  member_inventory, identity_inventory, executable_sha256,
                                  runtime):

    from alpha.p28 import load_extension_source
    from alpha.p27 import RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_HEADER as H, RUNTIME_CONSTRUCTED_GENERIC_LAYOUT_RECORD as R
    from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_HEADER as MH, RUNTIME_NATIVE_MEMBER_DETAIL_FIELD as MF
    from alpha.p25 import _reference_snapshot, _reference_snapshot_file, RUNTIME_TYPE_REFERENCE_HEADER as TH, RUNTIME_TYPE_REFERENCE_RECORD as TR
    if field_capture is None:
        raise AcquisitionError("constructed field output requires explicit native field type observations")
    selected = {
        "constructed_field_capture": file_identity(field_capture),
        "constructed_field_reference_model": file_identity(reference_model),
        "constructed_field_reference_inventory": reference_inventory,
        "constructed_field_layout_model": file_identity(constructed_model),
        "constructed_field_layout_inventory": file_identity(constructed_inventory),
        "constructed_field_member_inventory": member_inventory,
        "constructed_field_identity_inventory": identity_inventory,
    }
    _verify_files(selected)
    field = read_json(field_capture, maximum_bytes=256 * 1024 * 1024)
    refs = read_json(reference_model)
    target = refs.get("target", {})
    identity = field.get("identity", {})
    if (target.get("executable_sha256") != executable_sha256
            or refs.get("schema") != "alpha.runtime-type-reference-inventory/v1"
            or refs.get("status") != "runtime-validated"
            or refs.get("inventory") != reference_inventory
            or not refs.get("checks") or any(value is not True for value in refs["checks"].values())
            or any(identity.get("image_base" if key == "image_base_owner_only" else key) != value
                   for key, value in target.items())
            or not all(key in target for key in ("process_id", "creation_filetime", "executable_path",
                                                "executable_sha256", "image_base_owner_only", "image_bytes"))):
        raise AcquisitionError("constructed field output current process/reference identity differs")
    source = load_extension_source(field_capture, expected_identity=identity, allow_empty=True)
    expected = {"constructed_model": selected["constructed_field_layout_model"],
                "constructed_inventory": selected["constructed_field_layout_inventory"],
                "member_detail_inventory": member_inventory,
                "type_identity_inventory": identity_inventory}
    if any(source["source_inputs"].get(key) != value for key, value in expected.items()):
        raise AcquisitionError("constructed field output selected native sources differ")
    selected.update({"constructed_field_source_" + key: value
                     for key, value in source["source_inputs"].items()})
    _verify_files(selected)
    if (runtime.references != Path(reference_inventory["path"]).read_bytes()
            or runtime.native != Path(member_inventory["path"]).read_bytes()):
        raise AcquisitionError("constructed field output runtime bytes differ from selected sources")
    _, _, base = _reference_snapshot_file(Path(source["base_type_reference_inventory"]["path"]), label="field output base")
    _, _, nodes = _reference_snapshot(runtime.references, label="field output selected")
    require_reference_extension(base, nodes)
    raw = Path(constructed_inventory).read_bytes()
    h = H.unpack_from(raw)
    owners = {row[2]: (row[3], row[8]) for row in R.iter_unpack(raw[H.size:H.size + h[5] * R.size])}
    if len(owners) != h[5]:
        raise AcquisitionError("constructed field output owner domain repeats")
    mh = MH.unpack_from(runtime.native)
    templates = list(MF.iter_unpack(runtime.native[MH.size:MH.size + mh[5] * MF.size]))
    rh = TH.unpack_from(runtime.references)
    references = {row[0]: row for row in TR.iter_unpack(runtime.references[TH.size:TH.size + rh[5] * TR.size])}


    projection = project_fields(observed_fields=field["constructed_fields"],
        prefixes=source["expected_current_bytes"], references=references, owners=owners,
        template_fields=templates, attribute_layout=field["derivation"]["attributes"])
    _verify_files(selected)
    return {"fields": {(row["generic_index"], row["field_ordinal"]): row for row in projection["fields"]},
            "inputs": selected, "base_type_reference_inventory": source["base_type_reference_inventory"],
            "field_count": projection["field_count"], "observed_field_types_bound": True,
            "template_substitution_used_as_observation": False,
            "constructed_class_reference_closure_proven": False,
            "native_layout_complete": False}


import json
import os
from pathlib import Path
import stat

from alpha.h01 import AcquisitionError, owner_uid
from alpha.p13 import _safe_path


def read_runtime_progress(path: Path):

    path = _safe_path(path)
    try:
        fd = os.open(
            path,
            os.O_RDONLY
            | getattr(os, "O_NOFOLLOW", 0)
            | getattr(os, "O_NONBLOCK", 0),
        )
    except FileNotFoundError:
        return None
    except OSError as error:
        raise AcquisitionError("runtime progress file could not be opened") from error
    with os.fdopen(fd, "rb") as source:
        info = os.fstat(source.fileno())
        if not stat.S_ISREG(info.st_mode) or False:
            raise AcquisitionError("runtime progress is not a regular owner file")
        raw = source.read(512 * 1024 + 1)
    if len(raw) > 512 * 1024:
        raise AcquisitionError("runtime progress file exceeds bounded JSON size")
    try:
        return json.loads(raw.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None


from alpha.h02 import windows_run as _host_run

import os
import bisect
import hashlib
import json
import struct
import subprocess
from pathlib import Path

from alpha.p12 import _compiler, _owner_directory, _private_json, _private_text, _wide_literal, cached_windows_build
from alpha.h01 import AcquisitionError
from alpha.c01 import current_runtime_process_binding
from alpha.p13 import _safe_path, _file_record
from alpha.h02 import file_identity


_HEADER = struct.Struct("<8sIIQQ")
_RECORD = struct.Struct("<QQ")
_MAGIC = b"BALV2RR1"
_MAX_BYTES = 64 * 1024 * 1024


_MAX_RANGES = 1 << 20


_READ_FAILURE_DIAGNOSTIC = r'''
static void report_read_failure(HANDLE process,unsigned pass,SIZE_T index,
                                uint64_t address,uint64_t requested,SIZE_T transferred,
                                BOOL read_ok,DWORD read_error){
    DWORD wait_status=WaitForSingleObject(process,0);
    DWORD wait_error=wait_status==WAIT_FAILED?GetLastError():0;
    DWORD exit_code=0;BOOL exit_known=GetExitCodeProcess(process,&exit_code);
    DWORD exit_error=exit_known?0:GetLastError();
    MEMORY_BASIC_INFORMATION region={0};
    SIZE_T query_bytes=VirtualQueryEx(process,(const void*)(uintptr_t)address,&region,sizeof(region));
    DWORD query_error=query_bytes?0:GetLastError();
    fprintf(stderr,"range_read_failed index=%llu error=%lu pass=%u address=%llu requested=%llu transferred=%llu read_ok=%u\n",
        (unsigned long long)index,(unsigned long)read_error,pass,
        (unsigned long long)address,(unsigned long long)requested,
        (unsigned long long)transferred,(unsigned)!!read_ok);
    fprintf(stderr,"range_read_diagnostic wait_status=%lu wait_error=%lu exit_known=%u exit_code=%lu exit_error=%lu query_bytes=%llu query_error=%lu region_base=%llu region_bytes=%llu region_state=%lu region_protect=%lu region_type=%lu\n",
        (unsigned long)wait_status,(unsigned long)wait_error,(unsigned)!!exit_known,
        (unsigned long)exit_code,(unsigned long)exit_error,(unsigned long long)query_bytes,
        (unsigned long)query_error,(unsigned long long)(uintptr_t)region.BaseAddress,
        (unsigned long long)region.RegionSize,(unsigned long)region.State,
        (unsigned long)region.Protect,(unsigned long)region.Type);
}
'''


def _requests(ranges):
    if not isinstance(ranges, (list, tuple)) or not 1 <= len(ranges) <= _MAX_RANGES:
        raise AcquisitionError("read-only range count is invalid")
    ordered = []
    append = ordered.append
    for item in ranges:
        if not isinstance(item, (tuple, list)) or len(item) != 2:
            raise AcquisitionError("read-only range is invalid")
        address, size = item
        if (type(address) is not int or type(size) is not int or address <= 0 or size <= 0
            or size > _MAX_BYTES or address + size > 1 << 64):
            raise AcquisitionError("read-only range bounds are invalid")
        append((address, size))
    ordered.sort()


    total = 0
    previous_end = 0
    for address, size in ordered:
        total += size
        if address < previous_end:
            raise AcquisitionError("read-only ranges overlap")
        previous_end = address + size
    if total > _MAX_BYTES:
        raise AcquisitionError("read-only range total exceeds bounded storage")
    return ordered


class RuntimeRangeView:

    def __init__(self, observed: dict[int, bytes]):
        if not isinstance(observed, dict) or any(not isinstance(value, bytes) for value in observed.values()):
            raise AcquisitionError("runtime range payloads are invalid")
        ordered = _requests([(address, len(value)) for address, value in observed.items()])
        self.starts = tuple(address for address, _ in ordered)
        self.payloads = tuple(observed[address] for address in self.starts)

    def read(self, address: int, width: int) -> bytes | None:
        if type(address) is not int or type(width) is not int or address <= 0 or width <= 0 or address + width > 1 << 64:
            return None
        index = bisect.bisect_right(self.starts, address) - 1
        if index < 0:
            return None


        start = self.starts[index]
        offset = address - start
        payload = self.payloads[index]
        if offset + width <= len(payload):
            return payload[offset:offset + width]
        result = bytearray()
        cursor, remaining = address, width
        while remaining and index < len(self.starts):
            start, payload = self.starts[index], self.payloads[index]
            if not start <= cursor < start + len(payload):
                return None
            part = payload[cursor - start:cursor - start + remaining]
            result.extend(part)
            remaining -= len(part)
            cursor += len(part)
            index += 1
        return bytes(result) if not remaining else None


def _parse_output(raw, requests, binding):
    total = sum(size for _, size in requests)
    cursor = _HEADER.size + len(requests) * _RECORD.size
    if len(raw) != cursor + total or _HEADER.unpack_from(raw) != (_MAGIC, len(requests), binding[0], binding[1], total):
        raise AcquisitionError("read-only range output binding is invalid")
    observed = {}
    for index, (address, size) in enumerate(requests):
        if _RECORD.unpack_from(raw, _HEADER.size + index * _RECORD.size) != (address, size):
            raise AcquisitionError("read-only range output ordering differs")
        observed[address] = raw[cursor:cursor + size]
        cursor += size
    return observed


def _same_executable_spelling(recorded: object, expected: object) -> bool:


    if recorded == expected:
        return True
    return (
        isinstance(recorded, str) and isinstance(expected, str)
        and same_executable_path(recorded, expected)
    )


def load_runtime_range_observation(receipt_path: Path, *, expected_identity: dict) -> RuntimeRangeView:

    receipt_path = _safe_path(receipt_path)
    receipt_identity = _file_record(receipt_path)
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    if not isinstance(receipt, dict):
        raise AcquisitionError("read-only range receipt is malformed")
    target = receipt.get("target", {})
    if (receipt.get("schema") != "alpha.runtime-readonly-ranges/v1" or receipt.get("status") != "observed"
        or receipt.get("process_id") != expected_identity["process_id"]
        or receipt.get("creation_filetime") != expected_identity["creation_filetime"]
        or target.get("sha256") != expected_identity["executable_sha256"]
        or not _same_executable_spelling(target.get("path"), expected_identity["executable_path"])
        or target.get("bytes") != expected_identity["executable_bytes"]
        or receipt.get("checks") != {"opened_process_instance_bound": True, "two_complete_passes_match": True,
                                    "target_unchanged": True, "process_memory_write_absent": True, "code_injection_absent": True}):
        raise AcquisitionError("read-only range receipt identity/checks differ")
    paths = {}
    for key in ("plan", "source", "observer", "inventory"):
        record = receipt.get(key)
        if not isinstance(record, dict) or not isinstance(record.get("path"), str):
            raise AcquisitionError("read-only range receipt artifact is absent")
        path = _safe_path(Path(record["path"]))
        _file_record(path)
        if file_identity(path) != record:
            raise AcquisitionError("read-only range receipt artifact changed")
        paths[key] = path
    plan = json.loads(paths["plan"].read_text(encoding="utf-8"))
    if (plan.get("target") != target or plan.get("process_id") != receipt["process_id"]
        or plan.get("creation_filetime") != receipt["creation_filetime"]):
        raise AcquisitionError("read-only range plan identity differs")
    requests = _requests(plan.get("ranges"))
    raw = paths["inventory"].read_bytes()
    if hashlib.sha256(raw).hexdigest() != receipt["inventory"]["sha256"]:
        raise AcquisitionError("read-only range data changed while reading")
    if receipt.get("range_count") != len(requests) or receipt.get("byte_count") != sum(size for _, size in requests):
        raise AcquisitionError("read-only range receipt counts differ")
    observed = _parse_output(raw, requests, (receipt["process_id"], receipt["creation_filetime"]))
    if _file_record(receipt_path) != receipt_identity or any(file_identity(path) != receipt[key] for key, path in paths.items()):
        raise AcquisitionError("read-only range evidence changed during load")
    return RuntimeRangeView(observed)


def _source(binding, binary, requests):


    def wine_path(candidate: Path) -> str:
        expanded = candidate.expanduser()
        if not expanded.is_absolute():
            raise AcquisitionError("read-only range path is not absolute")
        return "Z:" + str(expanded).replace("/", "\\")

    accepted: list[str] = []
    for candidate in (
        Path(binding[2]),
        binary,
        Path(binding[2]).resolve(),
        Path(binary).resolve(),
    ):
        literal = _wide_literal(wine_path(candidate))
        if literal not in accepted:
            accepted.append(literal)
    path_table = ",".join(accepted)
    rows = ",".join(f"{{{address}ull,{size}ull}}" for address, size in requests)


    magic_initializer = "{" + ",".join(f"0x{byte:02x}" for byte in _MAGIC) + "}"
    return r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
typedef struct { uint64_t address,bytes; } range;
typedef struct { char magic[8]; uint32_t count,pid; uint64_t created,bytes; } header;
_Static_assert(sizeof(header)==32,"range header");
_Static_assert(sizeof(range)==16,"range row");
''' + _READ_FAILURE_DIAGNOSTIC + f'''
static const range ranges[] = {{{rows}}};
static const wchar_t* accepted_paths[]={{{path_table}}};
/* The live process reports the path it was started from, which can be a
   launcher symlink whose spelling is absent from accepted_paths.  Both paths
   still name the same executable, so fall back to the file identity that
   matters here: the executable file name and its byte size. */
static int same_executable_file(const wchar_t *left, const wchar_t *right){{
    const wchar_t *left_name = wcsrchr(left, L'\\\\');
    const wchar_t *right_name = wcsrchr(right, L'\\\\');
    left_name = left_name ? left_name + 1 : left;
    right_name = right_name ? right_name + 1 : right;
    if (!left_name[0] || _wcsicmp(left_name, right_name) != 0) return 0;
    HANDLE left_file = CreateFileW(left, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (left_file == INVALID_HANDLE_VALUE) return 0;
    HANDLE right_file = CreateFileW(right, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (right_file == INVALID_HANDLE_VALUE) {{
        CloseHandle(left_file); return 0;
    }}
    LARGE_INTEGER left_size, right_size;
    BOOL left_ok = GetFileSizeEx(left_file, &left_size);
    BOOL right_ok = GetFileSizeEx(right_file, &right_size);
    CloseHandle(left_file); CloseHandle(right_file);
    return left_ok && right_ok && left_size.QuadPart > 0 &&
        left_size.QuadPart == right_size.QuadPart;
}}
static int path_accepted(const wchar_t* path){{
    for(unsigned i=0;i<sizeof(accepted_paths)/sizeof(accepted_paths[0]);i++)
        if(!_wcsicmp(path,accepted_paths[i])||same_executable_file(path,accepted_paths[i]))return 1;
    return 0;
}}
static int identity(HANDLE process){{
    FILETIME created,exited,kernel,user;wchar_t path[32768];DWORD size=32768;
    return GetProcessTimes(process,&created,&exited,&kernel,&user)&&
        (((uint64_t)created.dwHighDateTime<<32)|created.dwLowDateTime)=={binding[1]}ull&&
        QueryFullProcessImageNameW(process,0,path,&size)&&path_accepted(path)&&
        WaitForSingleObject(process,0)==WAIT_TIMEOUT;
}}
static int write_all(HANDLE file,const void*data,DWORD size){{
    DWORD written=0;return WriteFile(file,data,size,&written,NULL)&&written==size;
}}
int main(int argc, char *argv[]){{
    wchar_t destination[32768];
    if(argc!=2||!argv[1]||!argv[1][0]||
       !MultiByteToWideChar(CP_UTF8,0,argv[1],-1,destination,32768))return 8;
    HANDLE process=OpenProcess(PROCESS_QUERY_INFORMATION|PROCESS_VM_READ|SYNCHRONIZE,FALSE,{binding[0]}u);
    if(!process)return 2;
    int result=3;unsigned char*first=NULL,*second=NULL;HANDLE output=INVALID_HANDLE_VALUE;
    if(!identity(process))goto done;
    uint64_t total=0;for(SIZE_T i=0;i<sizeof(ranges)/sizeof(ranges[0]);i++)total+=ranges[i].bytes;
    if(!total||total>{_MAX_BYTES}ull)goto done;
    first=malloc((SIZE_T)total);second=malloc((SIZE_T)total);
    if(!first||!second)goto done;
    for(unsigned pass=0;pass<2;pass++){{
        SIZE_T cursor=0;
        for(SIZE_T i=0;i<sizeof(ranges)/sizeof(ranges[0]);i++){{
            SIZE_T count=0;unsigned char*target=(pass?second:first)+cursor;
            BOOL read_ok=ReadProcessMemory(process,(const void*)(uintptr_t)ranges[i].address,target,(SIZE_T)ranges[i].bytes,&count);
            DWORD read_error=read_ok?0:GetLastError();
            if(!read_ok||count!=ranges[i].bytes){{
                report_read_failure(process,pass,i,ranges[i].address,ranges[i].bytes,count,read_ok,read_error);
                result=4;goto done;
            }}
            cursor+=(SIZE_T)ranges[i].bytes;
        }}
        if(!identity(process))goto done;
    }}
    if(memcmp(first,second,(SIZE_T)total)){{result=5;goto done;}}
    output=CreateFileW(destination,GENERIC_WRITE,0,NULL,CREATE_NEW,FILE_ATTRIBUTE_NORMAL,NULL);
    if(output==INVALID_HANDLE_VALUE){{result=6;goto done;}}
    header h={{{magic_initializer},(uint32_t)(sizeof(ranges)/sizeof(ranges[0])),{binding[0]}u,{binding[1]}ull,total}};
    if(!write_all(output,&h,sizeof(h))||!write_all(output,ranges,sizeof(ranges))||
       !write_all(output,first,(DWORD)total)||!FlushFileBuffers(output)){{result=7;goto done;}}
    if(!identity(process))goto done;
    result=0;printf("captured ranges=%u passes=2\\n",h.count);
done:
    if(output!=INVALID_HANDLE_VALUE)CloseHandle(output);
    free(first);free(second);CloseHandle(process);return result;
}}
'''


def prepare_range_observation(*, binary: Path, ranges, output_dir: Path, binding,
                              compiler: Path | None = None):
    binary = binary.expanduser().resolve()
    if binding is None or Path(binding[2]).resolve() != binary:
        raise AcquisitionError("read-only ranges require an explicit current-process binding")
    requests = _requests(ranges)
    output_dir = _owner_directory(output_dir)
    paths = {key: output_dir / name for key, name in (
        ("source", "range-observer.c"), ("program", "range-observer.exe"),
        ("output", "runtime-ranges.private.bin"), ("plan", "runtime-ranges-plan.private.json"),
        ("log", "range-observer.private.log"), ("receipt", "runtime-ranges.private.json"))}
    if any(path.exists() or path.is_symlink() for path in paths.values()):
        raise AcquisitionError("read-only range observation output already exists")
    target = file_identity(binary)
    _private_json(paths["plan"], {"target": target, "process_id": binding[0],
        "creation_filetime": binding[1], "ranges": requests,
        "destination": str(paths["output"])})
    _private_text(paths["source"], _source(binding, binary, requests))
    cached_windows_build([str(_compiler(compiler)), "-O2", "-Wall", "-Wextra", "-Werror",
            str(paths["source"]), "-o", str(paths["program"])], label="read-only range observer",
        source_path=paths["source"], output_path=paths["program"])
    paths["program"].chmod(0o600)
    return {"binding": binding, "binary": binary, "requests": requests, "paths": paths,
        "target": target, "source_identity": file_identity(paths["source"]),
        "program_identity": file_identity(paths["program"])}


def read_current_runtime_ranges(*, binary: Path, ranges, output_dir: Path,
                                wine: Path, wineprefix: Path, compiler: Path | None = None,
                                prepared: dict | None = None):
    if prepared is None:
        prepared = prepare_range_observation(binary=binary, ranges=ranges,
            output_dir=output_dir, binding=current_runtime_process_binding(),
            compiler=compiler)
    binding = prepared["binding"]
    paths = prepared["paths"]
    requests = prepared["requests"]
    target = prepared["target"]
    binary = prepared["binary"]
    if (current_runtime_process_binding() != binding
            or Path(binary).expanduser().resolve() != prepared["binary"]
            or _requests(ranges) != requests):
        raise AcquisitionError("read-only ranges require an explicit current-process binding")
    result = subprocess.run(_host_run(str(wine.resolve()), paths['program'], paths["output"]),
        env=dict(os.environ, WINEPREFIX=str(wineprefix.resolve()), WINEDEBUG="-all"),
        capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60, check=False)
    _private_json(paths["log"], {"returncode": result.returncode, "stdout": result.stdout, "stderr": result.stderr})
    if paths["output"].is_file() and not paths["output"].is_symlink():
        paths["output"].chmod(0o600)
    if (result.returncode or result.stdout != f"captured ranges={len(requests)} passes=2\n"
        or file_identity(binary) != target or file_identity(paths["source"]) != prepared["source_identity"]
        or file_identity(paths["program"]) != prepared["program_identity"]):
        raise AcquisitionError("read-only range observation failed or changed identity")
    if not paths["output"].is_file() or paths["output"].is_symlink():
        raise AcquisitionError("read-only range output is unavailable")
    raw = paths["output"].read_bytes()
    total = sum(size for _, size in requests)
    observed = _parse_output(raw, requests, binding)
    _private_json(paths["receipt"], {
        "schema": "alpha.runtime-readonly-ranges/v1", "status": "observed",
        "target": target, "process_id": binding[0], "creation_filetime": binding[1],
        "plan": file_identity(paths["plan"]), "source": prepared["source_identity"], "observer": prepared["program_identity"],
        "inventory": file_identity(paths["output"]), "range_count": len(requests), "byte_count": total,
        "checks": {"opened_process_instance_bound": True, "two_complete_passes_match": True,
                   "target_unchanged": True, "process_memory_write_absent": True, "code_injection_absent": True},
        "metadata_complete": False,
    })
    return observed


from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.p04 import prove, rewrite_reference_byref
from alpha.c04 import _verify_files
from alpha.c04 import MappedPE
from alpha.p04 import bounded_current_body
from alpha.h02 import read_json


def derive_current_contract(binding):
    records = {key: binding[key] for key in ("binary", "semantics")}
    _verify_files(records)
    semantics = read_json(Path(records["semantics"]["path"]))
    operations = [r for r in semantics.get("operations", []) if r.get("key") == "type.is_byref"]
    evidence = [r for r in semantics.get("native_type_flag_evidence", []) if r.get("operation_key") == "type.is_byref"]
    if (semantics.get("status") != "resolved" or semantics.get("binary") != records["binary"]
            or len(operations) != 1 or len(evidence) != 1
            or operations[0].get("semantic_identity_resolved") is not True):
        raise AcquisitionError("reference ByRef semantic evidence is absent or ambiguous")
    operation, prior = operations[0], evidence[0]
    if any(type(prior.get(k)) is not int or prior[k] < minimum for k, minimum in (("set_count", 2), ("clear_count", 8))):
        raise AcquisitionError("reference ByRef semantic support is insufficient")
    selected = binding["operations"]["type.is_byref"]
    if selected != dict(pointer=operation.get("method_pointer"), metadata=operation.get("metadata_pointer")):
        raise AcquisitionError("reference ByRef selected operation differs")
    with MappedPE(Path(records["binary"]["path"])) as image:
        pointer, code, thunks = bounded_current_body(image, selected["pointer"], image_base=binding["image_base"])
    if thunks or pointer != selected["pointer"]:
        raise AcquisitionError("reference ByRef getter is not a bounded direct body")
    proof = prove(code)
    expected = {"derived_descriptor_field_qword": binding["handle_qword"],
        "derived_flag_byte_offset": proof["descriptor_flag_byte_offset"],
        "derived_flag_mask": proof["descriptor_flag_mask"]}
    if any(type(prior.get(k)) is not int or prior[k] != value for k, value in expected.items()):
        raise AcquisitionError("reference ByRef semantic and code derivations disagree")
    result = dict(operation_key="type.is_byref", operation=dict(selected), code_hex=code.hex(), proof=proof,
        semantic_set_count=prior["set_count"], semantic_clear_count=prior["clear_count"],
        live_code_comparison_required=True, metadata_complete=False)
    validate_contract(result, binding)
    _verify_files(records)
    return result


def validate_contract(contract, binding):
    if not isinstance(contract, dict) or contract.get("operation_key") != "type.is_byref":
        raise AcquisitionError("reference ByRef derived contract is absent")
    try:
        code = bytes.fromhex(contract["code_hex"])
    except (KeyError, ValueError, TypeError) as error:
        raise AcquisitionError("reference ByRef code is invalid") from error
    pointer = contract.get("operation", {}).get("pointer")
    if (contract.get("operation") != binding["operations"]["type.is_byref"]
            or type(pointer) is not int or not binding["image_base"] <= pointer
            or pointer + len(code) > binding["image_base"] + binding["image_bytes"]
            or not code or contract.get("live_code_comparison_required") is not True):
        raise AcquisitionError("reference ByRef current operation/code extent differs")
    proof = prove(code)
    if (proof != contract.get("proof") or type(binding["handle_qword"]) is not int
            or proof["receiver_descriptor_offset"] != binding["handle_qword"] * 8):
        raise AcquisitionError("reference ByRef descriptor proof does not rederive")
    return code


def attach_reference_byref(source, *, binding):
    contract = binding.get("descriptor_byref_contract")
    code = validate_contract(contract, binding)
    source = rewrite_reference_byref(source, code=code, handle_qword=binding["handle_qword"])
    marker = "static int reference_instance_current(void) {"
    if source.count(marker) != 1:
        raise AcquisitionError("reference ByRef current-instance guard seam differs")
    guard = ("static const unsigned char reference_byref_code[]={" + ",".join(map(str, code)) + "};\n"
        "static int reference_byref_code_current(void){return readable(byref_pointer,sizeof(reference_byref_code))&&"
        "!memcmp((const void*)byref_pointer,reference_byref_code,sizeof(reference_byref_code));}\n")


    source = source.replace(marker, guard + marker + "\n    if(!reference_byref_code_current())return 0;", 1)
    old = r'\"fixed_offset_used\": true'
    args = 'written?"true":"false");fclose(out);}'
    if source.count(old) != 1 or source.count(args) != 1:
        raise AcquisitionError("reference ByRef status reporting seam differs")
    source = source.replace(old, old + r',\n  \"descriptor_byref_live_code_matches\": %s', 1)
    return source.replace(args, 'written?"true":"false",written&&reference_byref_code_current()?"true":"false");fclose(out);}', 1)


def verify_plan_contract(plan):
    contract = plan.get("contract", {}).get("descriptor_byref")
    if not isinstance(contract, dict):
        raise AcquisitionError("reference ByRef plan proof is absent")
    offset = contract.get("proof", {}).get("receiver_descriptor_offset")
    if type(offset) is not int or offset < 0 or offset % 8:
        raise AcquisitionError("reference ByRef plan descriptor field is invalid")
    from alpha.h02 import file_identity
    binary = file_identity(Path(plan["target"]["executable_path"]))
    if binary["sha256"] != plan["target"]["executable_sha256"]:
        raise AcquisitionError("reference ByRef plan executable changed")
    binding = dict(binary=binary, semantics=plan["inputs"]["semantics"],
        operations={"type.is_byref": contract.get("operation")}, handle_qword=offset // 8,
        image_base=plan["target"]["image_base_owner_only"], image_bytes=plan["target"]["image_bytes"])
    if derive_current_contract(binding) != contract:
        raise AcquisitionError("reference ByRef plan does not rederive from current inputs")
    return True


from contextvars import ContextVar
from functools import wraps
import inspect
from pathlib import Path
import tempfile

from alpha.h01 import AcquisitionError
from alpha.c01 import bind_runtime_process, current_runtime_process_binding
from alpha.c04 import RuntimeProcessLifetimeGuard
from alpha.h02 import file_identity


_ACTIVE = ContextVar("metadata_capture_lifetime", default=None)


def assert_current_capture_alive():
    lifetime = _ACTIVE.get()
    if lifetime is None:
        raise AcquisitionError("runtime capture is outside an opened process lifetime scope")
    lifetime.assert_alive()


def current_capture_scope(function):

    signature = inspect.signature(function)
    @wraps(function)
    def capture(*args, **kwargs):
        arguments = signature.bind(*args, **kwargs)
        arguments.apply_defaults()
        values = arguments.arguments
        binary = Path(values["binary"]).expanduser().resolve()
        before = file_identity(binary)
        with tempfile.TemporaryDirectory(prefix="alpha-capture-scope-") as temporary:
            root = Path(temporary).resolve()
            current = current_runtime_process_binding()
            probe = None
            if current is None:
                from alpha.p13 import RuntimeProcessProbe
                probe = RuntimeProcessProbe(binary=binary, wine=values["wine"], wineprefix=values["wineprefix"],
                    compiler=values.get("compiler"), build_dir=root / "probe")
                identity = probe()
                if identity.get("executable_sha256") != before["sha256"]:
                    raise AcquisitionError("runtime capture probe executable differs from selected file")
            else:
                identity = {"process_id": current[0], "creation_filetime": current[1], "executable_path": current[2]}
            if not same_executable_path(
                identity.get("executable_path"), binary
            ):
                raise AcquisitionError("runtime capture current process path differs from selected file")
            with bind_runtime_process(identity), RuntimeProcessLifetimeGuard(identity=identity,
                wine=values["wine"], wineprefix=values["wineprefix"], compiler=values.get("compiler"),
                build_dir=root / "lifetime") as lifetime:
                token = _ACTIVE.set(lifetime)
                try:
                    lifetime.assert_alive()
                    result = function(*args, **kwargs)
                    lifetime.assert_alive()
                    if file_identity(binary) != before:
                        raise AcquisitionError("runtime capture executable changed during acquisition")
                    if probe is not None and probe() != identity:
                        raise AcquisitionError("runtime capture process changed during acquisition")
                    return result
                finally:
                    _ACTIVE.reset(token)
    return capture
