from pathlib import Path

from alpha.h01 import AcquisitionError
from alpha.p22 import RUNTIME_METHOD_DETAIL_HEADER as MH, RUNTIME_METHOD_DETAIL_METHOD as MR, RUNTIME_METHOD_DETAIL_PARAMETER as PR
from alpha.c01 import derive_operations
from alpha.c04 import _verify_files
from alpha.c04 import MappedPE
from alpha.p18 import _ANCESTRY_HEADER as AH, _ANCESTRY_RECORD as AR
from alpha.p19 import _IDENTITY_HEADER as IH, _IDENTITY_RECORD as IR
from alpha.h02 import file_identity, read_json


def load_bound_method_ancestry(*, native, binary, method_detail_model, method_detail_inventory, ancestry_inventory,
                              process_identity):

    if any(path is None for path in (method_detail_model, method_detail_inventory, ancestry_inventory)):
        raise AcquisitionError("logical Module capture requires explicit method model/inventory and ancestry inventory")
    inputs = {"method_detail_model": file_identity(method_detail_model),
              "method_detail_inventory": file_identity(method_detail_inventory),
              "ancestry_inventory": file_identity(ancestry_inventory)}
    sources = dict(inputs, type_identity_inventory=native["type_identity_inventory"],
        native_inventory=native["native_inventory"], native_semantics=native["native_semantics"],
        semantics=native["semantics"])
    _verify_files(sources)
    model = read_json(method_detail_model)
    if (not isinstance(process_identity, dict) or any(type(process_identity.get(key)) is not int
            or process_identity[key] <= 0 for key in ("process_id", "creation_filetime"))):
        raise AcquisitionError("Module operation needs explicit current process lifetime identity")
    if (model.get("schema") != "alpha.runtime-method-detail-inventory/v1" or model.get("status") != "runtime-validated"
            or model.get("inventory") != inputs["method_detail_inventory"]
            or model.get("target", {}).get("executable_sha256") != native["binary"]["sha256"]
            or any(type(model.get("target", {}).get(key)) is not int
                   or model["target"][key] != process_identity[key] for key in ("process_id", "creation_filetime"))
            or not model.get("checks") or any(value is not True for value in model["checks"].values())
            or any(model.get("inputs", {}).get("type_identity_inventory", {}).get(key) != native["type_identity_inventory"].get(key) for key in ("path", "bytes", "sha256"))
            or model.get("inputs", {}).get("reflection_semantics") != native["semantics"]
            or any(model.get("inputs", {}).get("native_inventory", {}).get(key) != native["native_inventory"].get(key) for key in ("path", "bytes", "sha256"))):
        raise AcquisitionError("Module operation method model is not bound to the selected current TypeDef domain")
    name_source = model.get("inputs", {}).get("method_name_observation")
    if not isinstance(name_source, dict):
        raise AcquisitionError("Module operation method-name source binding is absent")
    inputs["method_name_observation"] = name_source
    sources["method_name_observation"] = name_source
    _verify_files(sources)
    iraw = Path(native["type_identity_inventory"]["path"]).read_bytes()
    mraw, araw = Path(method_detail_inventory).read_bytes(), Path(ancestry_inventory).read_bytes()
    if len(iraw) < IH.size or len(mraw) < MH.size or len(araw) < AH.size:
        raise AcquisitionError("Module operation source header is truncated")
    ih, mh, ah = IH.unpack_from(iraw), MH.unpack_from(mraw), AH.unpack_from(araw)
    if (ih[:5] != (b"ALPHATI1", 1, IH.size, IR.size, 0)
            or ih[5] != native["type_count"] or IH.size + ih[5] * IR.size + ih[8] != len(iraw)
            or ih[6:8] != (native["image_base"], native["image_bytes"])
            or ih[9:12] != tuple(native[key]["sha256"].encode() for key in ("binary", "native_inventory", "semantics"))
            or mh[:5] != (b"ALPHADM1", 1, MH.size, MR.size, PR.size) or mh[11]
            or mh[8:10] != (native["image_base"], native["image_bytes"])
            or mh[12:15] != tuple(native[key]["sha256"].encode() for key in ("binary", "native_inventory", "type_identity_inventory"))
            or mh[15] != name_source["sha256"].encode()
            or MH.size + mh[5] * MR.size + mh[6] * PR.size + mh[7] != len(mraw)
            or ah[:5] != (b"ALPHAAN1", 1, AR.size, 0, ih[5])
            or ah[5:7] != (native["image_base"], native["image_bytes"])
            or ah[7:10] != tuple(native[key]["sha256"].encode() for key in ("binary", "native_inventory", "native_semantics"))
            or AH.size + ah[4] * AR.size != len(araw)):
        raise AcquisitionError("Module operation inventory source/header/extent binding differs")
    identity_region = memoryview(iraw)[IH.size:IH.size + ih[5] * IR.size]
    try:
        identity_rows = list(IR.iter_unpack(identity_region))
    finally:
        identity_region.release()
    method_region = memoryview(mraw)[MH.size:MH.size + mh[5] * MR.size]
    try:
        method_rows = list(MR.iter_unpack(method_region))
    finally:
        method_region.release()
    ancestry_region = memoryview(araw)[AH.size:AH.size + ah[4] * AR.size]
    try:
        ancestry_rows = list(AR.iter_unpack(ancestry_region))
    finally:
        ancestry_region.release()
    rows = (identity_rows, method_rows, ancestry_rows)
    _verify_files(sources)
    if file_identity(binary) != native["binary"]:
        raise AcquisitionError("method/ancestry executable changed during source replay")
    return rows, inputs


def derive_bound_operations(*, native, binary, method_detail_model, method_detail_inventory, ancestry_inventory,
                            process_identity):
    (identities, methods, ancestry), inputs = load_bound_method_ancestry(native=native, binary=binary,
        method_detail_model=method_detail_model, method_detail_inventory=method_detail_inventory,
        ancestry_inventory=ancestry_inventory, process_identity=process_identity)
    sources = dict(inputs, **{key: native[key] for key in
        ("type_identity_inventory", "native_inventory", "native_semantics", "semantics")})
    semantics = read_json(Path(native["semantics"]["path"]))
    operation = [row for row in semantics.get("operations", []) if row.get("key") == "type.module"]
    if len(operation) != 1 or operation[0].get("semantic_identity_resolved") is not True:
        raise AcquisitionError("Module operation requires a uniquely resolved current type.module semantic")
    with MappedPE(binary) as image:
        if image.size_of_image != native["image_bytes"]:
            raise AcquisitionError("Module operation current executable image extent differs")
        def read_code(pointer):
            offset = image.rva_to_offset(pointer - native["image_base"])
            if offset is None or not any(section.raw_offset <= offset and offset + 8 <= section.raw_end
                                         for section in image.executable_sections):
                raise AcquisitionError("Module string override code is outside current executable sections")
            return bytes(image._mapping[offset:offset + 8])
        result = derive_operations(
            identity_rows=identities, method_rows=methods, ancestry_rows=ancestry,
            module_operation=operation[0], string_class=native["string_class"], read_code=read_code)
    _verify_files(sources)
    if file_identity(binary) != native["binary"]:
        raise AcquisitionError("Module operation executable changed during code derivation")
    modules = tuple(dict.fromkeys(row[4] for row in identities))
    return result, inputs, modules
