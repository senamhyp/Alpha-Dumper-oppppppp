from alpha.h01 import owner_only_mode_ok, owner_uid

import hashlib
import os
from pathlib import Path

from alpha.p12 import _wide_literal, _windows_z_path
from alpha.h01 import AcquisitionError
from alpha.c02 import native_raw_name_writer_source
from alpha.c01 import decode_raw_metadata_names
from alpha.c01 import encode_raw_metadata_names
from alpha.c04 import _verify_files
from alpha.p13 import _safe_path, _file_record
from alpha.p24 import RUNTIME_EVENT_MODULE_HEADER as EH, RUNTIME_EVENT_MODULE_MODULE as EM, RUNTIME_EVENT_MODULE_EVENT as EE
from alpha.p19 import _IDENTITY_HEADER as IH, _IDENTITY_RECORD as IR
from alpha.p17 import _NATIVE_MEMBER_HEADER as MH, _NATIVE_MEMBER_RECORD as MR


ROLES = ("native_inventory", "native_member_inventory", "type_identity_inventory",
         "native_semantics", "reflection_semantics")
SOURCE_ROLES = set(ROLES) | {"event_module_inventory", "raw_event_module_observation"}
CHECKS = {
    "raw_event_module_domains_closed": True, "display_projection_exact": True,
    "module_owners_replayed_from_typedefs": True, "event_owners_replayed_from_native_members": True,
    "pool_ranges_closed_without_aliases": True, "byte_roundtrip": True, "semantic_roundtrip": True,
    "source_files_unchanged": True,
}
PROOF_LIMITS = {"module_name_role_proven": False, "event_flags_proven": False,
    "raise_accessor_captured": False, "all_name_domains_closed": False, "live_capture_attested": False}


_DISPLAY_CONTROL_BYTES = bytes(byte if byte >= 32 else 95 for byte in range(256))


def replay_owners(*, identity_inventory, native_member_inventory, expected_binding,
                  type_count, event_count, image_base, image_bytes):

    if (type(type_count) is not int or not 0 < type_count <= 16_000_000 or
        type(event_count) is not int or not 0 <= event_count <= 16_000_000 or
        set(expected_binding["inputs"]) != set(ROLES)):
        raise AcquisitionError("raw event/module source roles or domain bounds differ")
    for role, raw in (("type_identity_inventory", identity_inventory),
                      ("native_member_inventory", native_member_inventory)):
        if not isinstance(raw, bytes) or hashlib.sha256(raw).hexdigest() != expected_binding["inputs"][role]:
            raise AcquisitionError("raw event/module source digest differs")
    if len(identity_inventory) < IH.size or len(native_member_inventory) < MH.size:
        raise AcquisitionError("raw event/module owner source is truncated")
    ih, mh = IH.unpack_from(identity_inventory), MH.unpack_from(native_member_inventory)
    cursor = IH.size + type_count * IR.size
    if (ih[:8] != (b"ALPHATI1", 1, IH.size, IR.size, 0, type_count, image_base, image_bytes) or
        ih[9:] != tuple(value.encode("ascii") for value in (
            expected_binding["executable_sha256"], expected_binding["inputs"]["native_inventory"],
            expected_binding["inputs"]["reflection_semantics"])) or cursor + ih[8] != len(identity_inventory) or
        mh[:5] != (b"ALPHANM1", 1, MR.size, type_count, 0) or mh[7] != event_count or
        mh[8:10] != (image_bytes, expected_binding["executable_sha256"].encode("ascii")) or
        MH.size + sum(mh[5:8]) * MR.size != len(native_member_inventory)):
        raise AcquisitionError("raw event/module owner header differs")
    modules, module_seen = [], set()


    identity_region = memoryview(identity_inventory)[IH.size:IH.size + type_count * IR.size]
    try:
        identity_iterator = IR.iter_unpack(identity_region)
        for index in range(type_count):
            row = next(identity_iterator)
            if (row[0] != index or not row[4] or row[11] != cursor or
                row[12] != cursor + row[8] or row[8] + row[9] > len(identity_inventory) - cursor):
                raise AcquisitionError("raw event/module TypeDef order, module or name range differs")
            cursor += row[8] + row[9]
            if row[4] not in module_seen:
                module_seen.add(row[4]); modules.append(row[4])
    finally:
        del identity_iterator
        identity_region.release()
    if cursor != len(identity_inventory):
        raise AcquisitionError("raw event/module TypeDef pool does not close")
    owners, pointer_seen = [], set()
    member_region = memoryview(native_member_inventory)[MH.size:]
    try:
        member_iterator = MR.iter_unpack(member_region)
        for kind, count in enumerate(mh[5:8]):
            previous_owner = -1
            next_local = 0


            expected_stride = mh[14 + kind * 3]
            zero_tail = b"" if expected_stride >= 48 else bytes(48 - expected_stride)
            for _ in range(count):
                row = next(member_iterator)
                owner, local, pointer, observed_kind, stride, payload = row
                if owner != previous_owner:
                    next_local = 0
                if (owner < previous_owner or owner >= type_count or local != next_local or
                    not pointer or pointer in pointer_seen or observed_kind != kind or
                    not 0 < stride <= len(payload) or stride != expected_stride or stride % 8 or payload[stride:] != zero_tail):
                    raise AcquisitionError("raw event/module native member owner/order differs")
                pointer_seen.add(pointer); previous_owner = owner; next_local += 1
                if kind == 2:
                    owners.append((owner, local, pointer))
    finally:
        del member_iterator
        member_region.release()
    return tuple(modules), tuple(owners)


def project_raw_event_module_names(*, raw_observation, event_module_inventory,
        identity_inventory, native_member_inventory, expected_binding,
        expected_counts, type_count, image_base, image_bytes, rid_base):
    if (set(expected_counts) != {"event", "module"} or type(rid_base) is not int or rid_base not in (0, 1)):
        raise AcquisitionError("raw event/module domains or RID base differ")
    names = decode_raw_metadata_names(raw_observation, expected_binding=expected_binding,
                                     expected_counts=expected_counts)
    modules, owners = replay_owners(identity_inventory=identity_inventory,
        native_member_inventory=native_member_inventory, expected_binding=expected_binding,
        type_count=type_count, event_count=expected_counts["event"], image_base=image_base, image_bytes=image_bytes)
    if len(modules) != expected_counts["module"]:
        raise AcquisitionError("raw module domain differs from current TypeDef ownership")
    raw = event_module_inventory
    if not isinstance(raw, bytes) or len(raw) < EH.size:
        raise AcquisitionError("raw event/module display header is truncated")
    h = EH.unpack_from(raw)
    event_start = EH.size + len(modules) * EM.size
    pool_start = event_start + len(owners) * EE.size
    if (h[:7] != (b"ALPHAEM1", 1, EH.size, EM.size, EE.size, len(modules), len(owners)) or
        h[8:12] != (image_base, image_bytes, type_count, 0) or
        h[12:] != tuple(value.encode("ascii") for value in (expected_binding["executable_sha256"],
            *(expected_binding["inputs"][role] for role in
              ("type_identity_inventory", "native_member_inventory", "native_semantics")))) or
        pool_start + h[7] != len(raw)):
        raise AcquisitionError("raw event/module display header or binding differs")
    counts = dict(expected_counts, empty_event_names=0, null_event_names=0,
                  empty_module_names=0, null_module_names=0, event_token_rid_gap_count=0)


    module_region = memoryview(raw)[EH.size:EH.size + len(modules) * EM.size]
    try:
        module_rows = list(EM.iter_unpack(module_region))
    finally:
        module_region.release()
    event_region = memoryview(raw)[event_start:event_start + len(owners) * EE.size]
    try:
        event_rows = list(EE.iter_unpack(event_region))
    finally:
        event_region.release()
    ranges, previous_rid = [], None
    for name in names:
        value = name.value


        if value is None:
            raise AcquisitionError("raw event/module observation is outside capture contract")
        try:
            value.decode("utf-8", errors="strict")
        except UnicodeDecodeError as error:
            raise AcquisitionError("raw managed name is not strict UTF-8") from error
        if name.domain == "module":
            pointer, length, reserved, offset = module_rows[name.index]
            if pointer != modules[name.index] or reserved:
                raise AcquisitionError("raw module owner differs from TypeDef source")
            counts["empty_module_names"] += value == b""
            display = value.translate(_DISPLAY_CONTROL_BYTES) or f"EmptyModule_{name.index:X}".encode("ascii")
        else:
            row = event_rows[name.index]
            token, length, flags, reserved, offset = row[6:]
            rid = token & 0xffffff
            if (row[:3] != owners[name.index] or not all(row[3:6]) or flags > 0xffff or reserved or
                token >> 24 != 0x14 or rid < rid_base or
                previous_rid is None and rid != rid_base or previous_rid is not None and rid <= previous_rid):
                raise AcquisitionError("raw event owner, token or structural fields differ")
            if previous_rid is not None:
                counts["event_token_rid_gap_count"] += rid - previous_rid - 1
            previous_rid = rid
            counts["empty_event_names"] += value == b""
            display = value or f"EmptyEvent_{token:X}".encode("ascii")
        if (not length or length != len(display) or offset < pool_start or
            length > len(raw) - offset or raw[offset:offset + length] != display):
            raise AcquisitionError("raw event/module name display projection differs")
        ranges.append((offset, length))


    cursor = pool_start
    for offset, length in sorted(ranges):
        if offset != cursor:
            raise AcquisitionError("raw event/module name pool overlaps or has a gap")
        cursor += length
    if cursor != len(raw):
        raise AcquisitionError("raw event/module name pool does not close")
    return names, counts


def _project_files(*, records, identity, counts, type_count, rid_base):
    if set(records) != SOURCE_ROLES:
        raise AcquisitionError("raw event/module explicit source records differ")
    _verify_files(records)
    buffers = {role: Path(records[role]["path"]).read_bytes() for role in
        ("type_identity_inventory", "native_member_inventory", "event_module_inventory", "raw_event_module_observation")}
    if any(hashlib.sha256(raw).hexdigest() != records[role]["sha256"] for role, raw in buffers.items()):
        raise AcquisitionError("raw event/module source changed during read")
    binding = {key: identity[key] for key in ("executable_sha256", "process_id", "creation_filetime")}
    binding["inputs"] = {role: records[role]["sha256"] for role in ROLES}
    buffers["identity_inventory"] = buffers.pop("type_identity_inventory")
    names, observed = project_raw_event_module_names(
        raw_observation=buffers.pop("raw_event_module_observation"), **buffers,
        expected_binding=binding, expected_counts=counts, type_count=type_count,
        image_base=identity["image_base"], image_bytes=identity["image_bytes"], rid_base=rid_base)
    _verify_files(records)
    binding["inputs"] = {role: record["sha256"] for role, record in records.items()}
    return names, observed, binding


def normalize_raw_event_module_names(*, records, identity, counts, type_count, rid_base, output_path):

    output_path = _safe_path(Path(output_path))
    parent = output_path.parent.stat()
    capture_parent = _safe_path(Path(records["raw_event_module_observation"]["path"])).parent
    if False and (False or not owner_only_mode_ok(parent, 0o700) or
        output_path.parent != capture_parent or
        _safe_path(Path(records["event_module_inventory"]["path"])).parent != capture_parent):
        raise AcquisitionError("raw event/module output must share its private capture directory")
    names, observed, binding = _project_files(records=records, identity=identity,
        counts=counts, type_count=type_count, rid_base=rid_base)
    encoded = encode_raw_metadata_names(names, binding=binding, expected_counts=counts)
    if decode_raw_metadata_names(encoded, expected_binding=binding, expected_counts=counts) != names:
        raise AcquisitionError("raw event/module semantic roundtrip differs")
    try:
        fd = os.open(
            output_path,
            os.O_WRONLY
            | os.O_CREAT
            | os.O_EXCL
            | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
    except OSError as error:
        raise AcquisitionError("raw event/module normalization cannot overwrite existing output") from error
    with os.fdopen(fd, "wb") as output:
        output.write(encoded); output.flush(); os.fsync(output.fileno())
    if output_path.read_bytes() != encoded:
        raise AcquisitionError("raw event/module byte roundtrip differs")
    _verify_files(records)
    return {"schema": "alpha.raw-event-module-names/v1", "inputs": records,
        "binding": binding, "inventory": dict(_file_record(output_path), path=str(output_path)),
        "counts": observed, "domain_counts": counts, "checks": dict(CHECKS),
        "proof_limits": dict(PROOF_LIMITS), "metadata_complete": False}


def load_raw_event_module_names(*, model, inventory_path, expected_identity, expected_inputs,
                               expected_counts, type_count, rid_base):
    if (not isinstance(model, dict) or model.get("schema") != "alpha.raw-event-module-names/v1" or
        model.get("metadata_complete") is not False or model.get("inputs") != expected_inputs or
        model.get("domain_counts") != expected_counts or model.get("checks") != CHECKS or
        model.get("proof_limits") != PROOF_LIMITS or
        any(value is not True for value in model["checks"].values()) or
        any(value is not False for value in model["proof_limits"].values())):
        raise AcquisitionError("raw event/module model, explicit sources or proof scope differ")
    inventory_path = _safe_path(Path(inventory_path))
    if model.get("inventory", {}).get("path") != str(inventory_path):
        raise AcquisitionError("raw event/module normalized inventory path differs")
    files = dict(expected_inputs, normalized_inventory=model["inventory"])
    _verify_files(files)
    names, counts, binding = _project_files(records=expected_inputs, identity=expected_identity,
        counts=expected_counts, type_count=type_count, rid_base=rid_base)
    raw = inventory_path.read_bytes()
    if (hashlib.sha256(raw).hexdigest() != model["inventory"]["sha256"] or
        model.get("binding") != binding or model.get("counts") != counts or
        decode_raw_metadata_names(raw, expected_binding=binding, expected_counts=expected_counts) != names or
        encode_raw_metadata_names(names, binding=binding, expected_counts=expected_counts) != raw):
        raise AcquisitionError("raw event/module original source replay differs")
    _verify_files(files)
    return names, counts


def attach_raw_event_module_names(source, *, binding, creation_filetime, module_count, output_path):

    if "static struct alpha_raw_row *alpha_raw_rows;" in source:
        raise AcquisitionError("raw event/module writer already composed")
    raw_binding = {"executable_sha256": binding["binary"]["sha256"], "process_id": binding["process_id"],
        "creation_filetime": creation_filetime,
        "inputs": {role: binding["semantics" if role == "reflection_semantics" else role]["sha256"]
                   for role in ROLES}}
    counts = {"event": binding["event_count"], "module": module_count}
    writer = native_raw_name_writer_source(binding=raw_binding, counts=counts)

    def replace_once(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise AcquisitionError("raw event/module composition seam differs")
        source = source.replace(old, new, 1)

    seam = "static int capture_modules(void) {"
    replace_once(seam, "#include <io.h>\n#include <fcntl.h>\n#include <sys/stat.h>\n" + writer +
        "\nstatic const wchar_t alpha_raw_output[] = " + _wide_literal(_windows_z_path(Path(output_path))) + r''';
static int write_raw_event_module_names(void) {
    int fd = _wopen(alpha_raw_output, _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY, _S_IREAD | _S_IWRITE);
    if (fd < 0) return 0;
    FILE *out = _fdopen(fd, "wb");
    if (!out) { _close(fd); _wremove(alpha_raw_output); return 0; }
    int ok = alpha_raw_write(out);
    if (fclose(out)) ok = 0;
    if (!ok) _wremove(alpha_raw_output);
    return ok;
}
''' + seam)
    replace_once("if(!append_text(v,n,&modules[i].name_offset))",
        "if(!alpha_raw_append(10u,(uint32_t)i,0,v,n)||!append_text(v,n,&modules[i].name_offset))")
    replace_once("            if(!bytes){char synthetic[40];", """            if(!alpha_raw_append(6u,(uint32_t)index,!name,value,bytes)) {
                free(value);failure_kind=1201;failure_index=index+1;return 0;
            }
            if(!bytes){char synthetic[40];""")
    replace_once("if(GetCurrentProcessId()!=expected_pid||", "if(!alpha_raw_identity()||GetCurrentProcessId()!=expected_pid||")
    replace_once("if(!capture_modules()){", "if(!alpha_raw_initialize()||!capture_modules()){")
    replace_once("int ok=write_string_io_probe()&&write_output();write_status(",
                 "int ok=write_raw_event_module_names()&&write_string_io_probe()&&write_output();write_status(")
    return source, raw_binding, counts
