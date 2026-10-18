from string import Template

from alpha.p12 import _wide_literal, _windows_z_path
from alpha.h01 import AcquisitionError


def validate_diagnostic(value, *, identity, inputs, modules):

    if (not isinstance(value, dict) or value.get("schema") != "alpha.module-name-candidate-diagnostic/v1"
            or value.get("module_name_role_proven") is not False or value.get("metadata_complete") is not False
            or value.get("truncated") is not False or value.get("all_candidate_reads_succeeded") is not True):
        raise AcquisitionError("module candidate diagnostic is incomplete or claims a semantic role")
    for key in ("process_id", "creation_filetime", "executable_sha256"):
        if type(value.get(key)) is not type(identity[key]) or value[key] != identity[key]:
            raise AcquisitionError("module candidate diagnostic process identity differs")
    for label, role in (("identity", "type_identity_inventory"), ("native", "native_inventory"),
                        ("member", "native_member_inventory")):
        if value.get(label + "_sha256") != inputs[role]["sha256"]:
            raise AcquisitionError("module candidate diagnostic source identity differs")
    count = len(modules)
    support = value.get("support")
    if (not count or len(set(modules)) != count or type(value.get("module_count")) is not int
            or value["module_count"] != count or not isinstance(support, list) or len(support) != 16
            or any(type(n) is not int or not 0 <= n <= count for n in support)):
        raise AcquisitionError("module candidate diagnostic support domain differs")
    candidates = [q for q in range(2, 16) if support[q] == count]
    if len(candidates) < 2 or type(value.get("candidate_count")) is not int or value["candidate_count"] != len(candidates):
        raise AcquisitionError("module candidate ambiguity is not independently counted")
    rows = value.get("rows_owner_only")
    if not isinstance(rows, list) or len(rows) != count:
        raise AcquisitionError("module candidate owner domain does not close")
    classes, equal_values = {}, 0
    for index, row in enumerate(rows):
        if (not isinstance(row, dict) or type(row.get("index")) is not int or row["index"] != index
                or type(row.get("module_pointer")) is not int or row["module_pointer"] != modules[index]
                or type(row.get("class_pointer")) is not int or not 0 < row["class_pointer"] < 1 << 64
                or row["class_pointer"] & 7):
            raise AcquisitionError("module candidate owner order or class differs")
        fields = row.get("fields")
        if not isinstance(fields, list) or len(fields) != len(candidates):
            raise AcquisitionError("module candidate field domain differs")
        names = []
        for qword, field in zip(candidates, fields):
            if (not isinstance(field, dict) or type(field.get("qword")) is not int or field["qword"] != qword
                    or field.get("readable") is not True or type(field.get("string_pointer")) is not int
                    or not 0 < field["string_pointer"] < 1 << 64 or field["string_pointer"] & 7
                    or not isinstance(field.get("utf8_hex"), str) or len(field["utf8_hex"]) > 131072):
                raise AcquisitionError("module candidate field extent or observation differs")
            try:
                raw = bytes.fromhex(field["utf8_hex"])
                raw.decode("utf-8", errors="strict")
            except (ValueError, UnicodeError) as error:
                raise AcquisitionError("module candidate name encoding differs") from error
            if raw.hex() != field["utf8_hex"] or not raw.endswith((b".dll", b".exe")):
                raise AcquisitionError("module candidate does not match the recorded suffix predicate")
            names.append(raw)
        equal_values += len(set(names)) == 1
        classes[row["class_pointer"]] = classes.get(row["class_pointer"], 0) + 1
    return {"module_count": count, "candidate_count": len(candidates), "candidate_qwords_owner_only": candidates,
            "class_counts_owner_only": classes, "modules_with_equal_candidate_values": equal_values,
            "transport_and_owner_binding_verified": True, "module_name_role_proven": False, "metadata_complete": False}


def diagnostic_source(output_path):
    return Template(r'''
static FILE *open_private_output(const wchar_t *path);
static void write_module_candidate_diagnostic(const uint32_t support[16], uint32_t candidates) {
    FILETIME creation, exit_time, kernel, user;
    if (!GetProcessTimes(GetCurrentProcess(), &creation, &exit_time, &kernel, &user)) return;
    FILE *out = open_private_output($output_path);
    if (!out) return;
    uint64_t born = ((uint64_t)creation.dwHighDateTime << 32) | creation.dwLowDateTime;
    uint64_t limit = module_count < 4096u ? module_count : 4096u;
    fprintf(out, "{\"schema\":\"alpha.module-name-candidate-diagnostic/v1\","
        "\"process_id\":%lu,\"creation_filetime\":%llu,\"executable_sha256\":\"%s\","
        "\"identity_sha256\":\"%s\",\"native_sha256\":\"%s\",\"member_sha256\":\"%s\","
        "\"module_count\":%llu,\"candidate_count\":%u,\"support\":[",
        (unsigned long)GetCurrentProcessId(), (unsigned long long)born, executable_sha256,
        identity_sha256, native_sha256, member_sha256, (unsigned long long)module_count, candidates);
    for (uint32_t q = 0; q < 16u; q++) fprintf(out, "%s%u", q ? "," : "", support[q]);
    fprintf(out, "],\"rows_owner_only\":[");
    int all_readable = 1;
    for (uint64_t i = 0; i < limit; i++) {
        uintptr_t pointer = modules[i].module_pointer, klass = 0;
        if (readable(pointer, sizeof(klass))) memcpy(&klass, (const void *)pointer, sizeof(klass));
        else all_readable = 0;
        fprintf(out, "%s{\"index\":%llu,\"module_pointer\":%llu,\"class_pointer\":%llu,\"fields\":[",
            i ? "," : "", (unsigned long long)i, (unsigned long long)pointer, (unsigned long long)klass);
        uint32_t emitted = 0;
        for (uint32_t q = 2; q < 16u; q++) if (support[q] == module_count) {
            uintptr_t object = 0, address = pointer + (uintptr_t)q * 8u;
            char *value = NULL; uint32_t bytes = 0;
            int valid = readable(address, sizeof(object));
            if (valid) memcpy(&object, (const void *)address, sizeof(object));
            valid = valid && managed_utf8(object, &value, &bytes);
            if (!valid) all_readable = 0;
            fprintf(out, "%s{\"qword\":%u,\"string_pointer\":%llu,\"readable\":%s,\"utf8_hex\":\"",
                emitted++ ? "," : "", q, (unsigned long long)object, valid ? "true" : "false");
            if (valid) for (uint32_t b = 0; b < bytes; b++) fprintf(out, "%02x", (unsigned char)value[b]);
            fprintf(out, "\"}"); free(value);
        }
        fprintf(out, "]}");
    }
    fprintf(out, "],\"all_candidate_reads_succeeded\":%s,\"truncated\":%s,"
        "\"module_name_role_proven\":false,\"metadata_complete\":false}\n",
        all_readable ? "true" : "false", limit == module_count ? "false" : "true");
    fclose(out);
}
''').substitute(output_path=_wide_literal(_windows_z_path(output_path)))


from pathlib import Path

from alpha.p12 import _wide_literal, _windows_z_path
from alpha.h01 import AcquisitionError
from alpha.c02 import native_getter_support


def compose_module_capture(source, *, model, modules, binding, observation_path):
    start, end = "static int capture_modules(void) {", "static int validate_event_token_order(void);"
    if ("module_name_capture_worker" in source or source.count(start) != 1 or source.count(end) != 1 or "static int alpha_raw_identity(" not in source
            or "static struct alpha_raw_row *alpha_raw_rows;" not in source
            or source.index(end) < source.index(start)):
        raise AcquisitionError("logical Module capture requires a guarded raw-name collector")
    hook = r'''
        if (!alpha_raw_append(10u, (uint32_t)i, 0, name, bytes)) { free(name); failure = 11; break; }
        char alias[48]; char *display = NULL; uint32_t display_bytes = bytes;
        if (!bytes) {
            int n = snprintf(alias, sizeof(alias), "EmptyModule_%llX", (unsigned long long)i);
            if (n <= 0 || (size_t)n >= sizeof(alias)) { free(name); failure = 12; break; }
            display = alias; display_bytes = (uint32_t)n;
        } else {
            display = malloc(bytes);
            if (!display) { free(name); failure = 12; break; }
            for (uint32_t b = 0; b < bytes; b++) display[b] = (unsigned char)name[b] < 32 ? '_' : name[b];
        }
        int appended = append_text(display, display_bytes, &modules[i].name_offset);
        if (bytes) free(display);
        if (!appended) { free(name); failure = 13; break; }
        modules[i].module_pointer = object; modules[i].name_bytes = display_bytes;
'''
    support = "static const wchar_t module_getter_observation_path[] = " + _wide_literal(_windows_z_path(Path(observation_path))) + ";\n"
    support += native_getter_support(model=model, modules=modules, binding=binding,
        entrypoint="module_name_capture_worker", destination="module_getter_observation_path",
        after_read=hook, finish_string_io=False)
    wrapper = r'''
static int capture_modules(void) {
    const uint64_t count = sizeof(observed_modules) / sizeof(observed_modules[0]);
    if (!count || count != expected_module_count) { failure_kind = 1085; return 0; }
    modules = calloc(count, sizeof(*modules));
    if (!modules) { failure_kind = 1081; return 0; }


    for (uint64_t i = 0; i < expected_type_count; i++) {
        uintptr_t pointer = types[i].module_pointer;
        uint64_t found = 0;
        while (found < module_count && modules[found].module_pointer != pointer) found++;
        if (found == module_count) {
            if (module_count >= count || observed_modules[module_count] != pointer) { failure_kind = 1086; return 0; }
            modules[module_count++].module_pointer = pointer;
        }
    }
    if (module_count != count) { failure_kind = 1087; return 0; }
    DWORD result = module_name_capture_worker(NULL);
    if (result) { failure_kind = 10900u + result; return 0; }
    return 1;
}
'''
    return source[:source.index(start)] + support + wrapper + source[source.index(end):]


from alpha.h02 import windows_run as _host_run

import json
import os
import subprocess
from pathlib import Path

from alpha.p12 import _build, _compiler, _owner_directory, _private_json, _private_text, _wide_literal, _windows_z_path, cached_windows_build
from alpha.h01 import AcquisitionError
from alpha.c01 import current_runtime_process_binding
from alpha.h02 import file_identity


def observe_missing_native_names(*, binary: Path, requests: list[dict], output_dir: Path,
                                 wine: Path, wineprefix: Path, compiler: Path | None = None) -> dict[int, str]:
    binding = current_runtime_process_binding()
    if binding is None or Path(binding[2]).resolve() != binary.resolve():
        raise AcquisitionError("native-name observation requires a current-process session binding")
    if not requests or len(requests) > 4096:
        raise AcquisitionError("native-name observation request count is invalid")
    output_dir = _owner_directory(output_dir)
    target = file_identity(binary)
    arrays, rows, observed = [], [], {}
    total = 0
    for index, request in enumerate(requests):
        name = request["name"]
        encoded = name.encode("utf-8") + b"\0"
        if b"\0" in encoded[:-1] or not 1 <= len(encoded) <= 16385:
            raise AcquisitionError("native-name observation expected text is invalid")
        values = [request[key] for key in ("member_pointer", "slot", "encoded_value", "name_pointer")]
        if any(type(value) is not int or value < 0 for value in values) or not values[0] or not values[3]:
            raise AcquisitionError("native-name observation pointer binding is invalid")
        member, slot, word, address = values
        if slot >= 64 or max(member + slot * 8, address + len(encoded), word) > 0xFFFFFFFFFFFFFFFF:
            raise AcquisitionError("native-name observation range is invalid")
        total += len(encoded)
        if total > 16 * 1024 * 1024:
            raise AcquisitionError("native-name observation exceeds bounded storage")
        arrays.append(f"static const unsigned char expected_{index}[] = {{" + ",".join(map(str, encoded)) + "};")
        rows.append(f"{{{member + slot * 8}ull,{word}ull,{address}ull,sizeof(expected_{index}),expected_{index}}}")
        if address in observed and observed[address] != name:
            raise AcquisitionError("native-name observation has conflicting expectations")
        observed[address] = name


    def wine_path(path: Path) -> str:
        expanded = path.expanduser()
        if not expanded.is_absolute():
            raise AcquisitionError("native-name observation path is not absolute")
        return "Z:" + str(expanded).replace("/", "\\")

    accepted_paths: list[str] = []
    for candidate in (
        Path(binding[2]),
        binary,
        Path(binding[2]).resolve(),
        Path(binary).resolve(),
    ):
        literal = _wide_literal(wine_path(candidate))
        if literal not in accepted_paths:
            accepted_paths.append(literal)
    path_literals = ",".join(accepted_paths)
    source = r'''#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <wchar.h>
typedef struct {uint64_t word_address,word,name_address;SIZE_T bytes;const unsigned char*expected;} request;
''' + "\n".join(arrays) + "\nstatic const request requests[]={" + ",".join(rows) + "};\n" + f'''
static const wchar_t* accepted_paths[]={{{path_literals}}};
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
    if(!GetProcessTimes(process,&created,&exited,&kernel,&user)||
       (((uint64_t)created.dwHighDateTime<<32)|created.dwLowDateTime)!={binding[1]}ull||
       !QueryFullProcessImageNameW(process,0,path,&size)||!path_accepted(path))return 0;
    return WaitForSingleObject(process,0)==WAIT_TIMEOUT;
}}
int main(void){{
    HANDLE process=OpenProcess(PROCESS_QUERY_INFORMATION|PROCESS_VM_READ|SYNCHRONIZE,FALSE,{binding[0]}u);
    if(!process)return 2;
    if(!identity(process)){{CloseHandle(process);return 3;}}
    unsigned char buffer[16385];
    for(unsigned pass=0;pass<2;pass++)for(unsigned i=0;i<sizeof(requests)/sizeof(requests[0]);i++){{
        const request*r=&requests[i];uint64_t word=0;SIZE_T read=0;
        if(!ReadProcessMemory(process,(const void*)(uintptr_t)r->word_address,&word,8,&read)||read!=8||word!=r->word||
           !ReadProcessMemory(process,(const void*)(uintptr_t)r->name_address,buffer,r->bytes,&read)||read!=r->bytes||
           memcmp(buffer,r->expected,r->bytes)){{CloseHandle(process);return 4;}}
    }}
    if(!identity(process)){{CloseHandle(process);return 5;}}
    CloseHandle(process);
    printf("verified requests=%u passes=2\\n",(unsigned)(sizeof(requests)/sizeof(requests[0])));
    return 0;
}}
'''
    source_path = output_dir / "native-name-observer.c"
    program = output_dir / "native-name-observer.exe"
    receipt = output_dir / "native-name-observation.private.json"
    if any(path.exists() for path in (source_path, program, receipt)):
        raise AcquisitionError("native-name observation output already exists")
    _private_text(source_path, source)
    plan_path = output_dir / "native-name-observation-plan.private.json"
    _private_json(plan_path, {
        "target": target, "process_id": binding[0], "creation_filetime": binding[1], "requests": requests})
    _build([str(_compiler(compiler)), "-O2", "-Wall", "-Wextra", "-Werror", str(source_path), "-o", str(program)],
           label="read-only native-name observer")
    program.chmod(0o600)
    environment = dict(os.environ, WINEPREFIX=str(wineprefix.resolve()), WINEDEBUG="-all")
    result = subprocess.run(_host_run(str(wine.resolve()), program), env=environment,
                            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60, check=False)
    _private_json(output_dir / "native-name-observer.private.log", {
        "returncode": result.returncode, "stdout": result.stdout, "stderr": result.stderr})
    expected_output = f"verified requests={len(requests)} passes=2\n"
    if result.returncode or result.stdout != expected_output or file_identity(binary) != target:
        raise AcquisitionError("current native-name bytes or process identity did not verify")
    _private_json(receipt, {"schema": "alpha.runtime-native-name-observation/v1", "status": "verified",
        "target": target, "process_id": binding[0], "creation_filetime": binding[1],
        "observer": file_identity(program), "source": file_identity(source_path),
        "plan": file_identity(plan_path),
        "request_count": len(requests), "read_pass_count": 2,
        "checks": {"opened_process_instance_bound": True, "encoded_member_words_match": True,
                   "native_bytes_equal_independent_managed_names": True, "target_unchanged": True,
                   "process_memory_write_absent": True, "code_injection_absent": True}})
    return observed


from alpha.h01 import owner_uid, owner_only_mode_ok

from pathlib import Path

from alpha.p12 import _wide_literal, _windows_z_path
from alpha.h01 import AcquisitionError
from alpha.c01 import decode_raw_metadata_names
from alpha.c02 import native_raw_name_writer_source


ROLES = ("native_inventory", "native_member_inventory", "type_identity_inventory", "native_semantics")


def attach_raw_member_names(source, *, binding, creation_filetime, output_path):
    raw_binding = {"executable_sha256": binding["binary"]["sha256"],
                   "process_id": binding["process_id"], "creation_filetime": creation_filetime,
                   "inputs": {role: binding[role]["sha256"] for role in ROLES}}
    counts = {"field": binding["field_count"], "property": binding["property_count"]}
    native = native_raw_name_writer_source(binding=raw_binding, counts=counts)

    def replace_once(old, new):
        nonlocal source
        if source.count(old) != 1:
            raise AcquisitionError("raw member-name template integration seam differs")
        source = source.replace(old, new, 1)

    declaration = "static volatile LONG callback_complete;"
    replace_once(declaration, declaration + "\n#include <io.h>\n#include <fcntl.h>\n#include <sys/stat.h>\n" +
        native + "\nstatic const wchar_t alpha_raw_output[] = " +
        _wide_literal(_windows_z_path(Path(output_path))) + r''';
static int write_raw_member_names(void) {
    int fd = _wopen(alpha_raw_output, _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY,
                   _S_IREAD | _S_IWRITE);
    if (fd < 0) return 0;
    FILE *output = _fdopen(fd, "wb");
    if (!output) { _close(fd); _wremove(alpha_raw_output); return 0; }
    int ok = alpha_raw_write(output);
    if (fclose(output)) ok = 0;
    if (!ok) _wremove(alpha_raw_output);
    return ok;
}
''')
    condition = "    if (GetCurrentProcessId() != expected_process_id ||"
    replace_once(condition, condition + "\n        !alpha_raw_identity() ||")
    allocation = "    if (!fields || !properties || !method_metadata)"
    replace_once(allocation, "    if (!fields || !properties || !method_metadata || !alpha_raw_initialize())")
    signature = "static int append_native_name(\n    uintptr_t pointer, uint32_t token, const char *prefix,"
    replace_once(signature, "static int append_native_name(\n    uintptr_t pointer, uint32_t domain, uint32_t index, uint32_t token, const char *prefix,")
    count = "    uint32_t count = text_bytes(pointer);\n    if (count == UINT32_MAX) return 0;"
    replace_once(count, count + "\n    if (!alpha_raw_append(domain, index, !pointer, (const void *)pointer, count)) return 0;")
    for prefix, domain, index in (("EmptyField_", 4, "field_index"), ("EmptyProperty_", 5, "index")):
        call = f'append_native_name(name_pointer, target->metadata_token,\n                "{prefix}"'
        replacement = (f'append_native_name(name_pointer, {domain}u, (uint32_t){index}, '
                       f'target->metadata_token,\n                "{prefix}"')
        replace_once(call, replacement)
    replace_once("    ok = write_output(); write_status(",
                 "    ok = write_raw_member_names() && write_output(); write_status(")
    return source, raw_binding, counts


def project_raw_member_names(*, raw_observation, detail_inventory, expected_binding,
                             expected_counts, image_base, image_bytes, type_count, rid_base):

    from alpha.p23 import RUNTIME_NATIVE_MEMBER_DETAIL_HEADER as header_type, RUNTIME_NATIVE_MEMBER_DETAIL_FIELD as field_type, RUNTIME_NATIVE_MEMBER_DETAIL_PROPERTY as property_type
    if (set(expected_counts) != {"field", "property"} or
        set(expected_binding["inputs"]) != set(ROLES) or type(rid_base) is not int or rid_base not in (0, 1)):
        raise AcquisitionError("raw member-name source roles, domains or RID base differ")
    names = decode_raw_metadata_names(raw_observation, expected_binding=expected_binding,
                                     expected_counts=expected_counts)
    if not isinstance(detail_inventory, bytes) or len(detail_inventory) < header_type.size:
        raise AcquisitionError("member detail inventory is truncated")
    header = header_type.unpack_from(detail_inventory)
    field_count, property_count = expected_counts["field"], expected_counts["property"]
    property_start = header_type.size + field_count * field_type.size
    cursor = property_start + property_count * property_type.size
    if (header[:7] != (b"ALPHAND1", 1, header_type.size, field_type.size, property_type.size,
                       field_count, property_count) or
        header[8:12] != (image_base, image_bytes, type_count, 0) or
        header[12:] != tuple(value.encode("ascii") for value in (
            expected_binding["executable_sha256"], expected_binding["inputs"]["native_member_inventory"],
            expected_binding["inputs"]["type_identity_inventory"], expected_binding["inputs"]["native_semantics"])) or
        cursor + header[7] != len(detail_inventory)):
        raise AcquisitionError("raw member-name detail header or source binding differs")
    counts = dict(expected_counts, empty_field_names=0, null_field_names=0,
                  empty_property_names=0, null_property_names=0)


    field_rows = field_type.iter_unpack(
        memoryview(detail_inventory)[header_type.size:property_start])
    property_rows = property_type.iter_unpack(
        memoryview(detail_inventory)[property_start:cursor])
    for name, row in zip(names, chain(field_rows, property_rows)):
        is_field = name.domain == "field"
        token, length, offset = (row[6], row[7], row[9]) if is_field else (row[5], row[6], row[9])
        kind = 0x04 if is_field else 0x17
        if row[0] >= type_count or token != (kind << 24) | (name.index + rid_base):
            raise AcquisitionError("raw member-name owner or definition token differs")
        value = name.value
        if value is None:
            counts[f"null_{name.domain}_names"] += 1
        elif not value:
            counts[f"empty_{name.domain}_names"] += 1
        if value and b"\0" in value:
            raise AcquisitionError("native NUL-terminated member name contains embedded NUL")
        display = value or (("EmptyField_" if is_field else "EmptyProperty_") + f"{token:X}").encode("ascii")
        if offset != cursor or length != len(display) or detail_inventory[offset:offset + length] != display:
            raise AcquisitionError("raw member-name bytes do not project to the exact display inventory")
        cursor += length
    if cursor != len(detail_inventory):
        raise AcquisitionError("raw member-name string pool does not close")
    return names, counts


def _verify_files(records):
    from alpha.p13 import _safe_path, _file_record
    from alpha.c01 import group_source_records
    from alpha.c01 import verify_source
    for source_path, expected in group_source_records(records).items():
        path = _safe_path(Path(source_path))
        if str(path) != source_path:
            raise AcquisitionError("raw member-name source file changed")
        verify_source(path, expected, _file_record)


def _project_files(*, records, identity, counts, type_count, rid_base):
    import hashlib
    _verify_files(records)
    buffers = {role: Path(records[role]["path"]).read_bytes()
               for role in ("raw_member_observation", "member_detail_inventory")}
    if any(hashlib.sha256(data).hexdigest() != records[role]["sha256"] for role, data in buffers.items()):
        raise AcquisitionError("raw member-name source changed during read")
    binding = {key: identity[key] for key in ("executable_sha256", "process_id", "creation_filetime")}
    binding["inputs"] = {role: records[role]["sha256"] for role in ROLES}
    names, observed_counts = project_raw_member_names(
        raw_observation=buffers["raw_member_observation"],
        detail_inventory=buffers["member_detail_inventory"], expected_binding=binding,
        expected_counts=counts, image_base=identity["image_base"], image_bytes=identity["image_bytes"],
        type_count=type_count, rid_base=rid_base)
    _verify_files(records)
    binding["inputs"] = {role: record["sha256"] for role, record in records.items()}
    return names, observed_counts, binding


def finalize_raw_member_names(*, plan, output_path):
    import os
    import stat
    from alpha.p13 import _safe_path
    from alpha.c01 import encode_raw_metadata_names
    from alpha.h02 import file_identity

    if not isinstance(plan, dict) or plan.get("contract", {}).get("lossless_raw_names_required") is not True:
        raise AcquisitionError("member capture has no lossless raw-name contract")
    detail_path = _safe_path(Path(plan["output_path"]))
    raw_path = _safe_path(Path(plan["raw_member_names_path"]))
    output_path = _safe_path(Path(output_path))
    parent = output_path.parent.stat()
    if (raw_path.parent != detail_path.parent or output_path.parent != detail_path.parent or
        False or not owner_only_mode_ok(parent, 0o700)):
        raise AcquisitionError("raw member-name output must share its private capture directory")
    records = {role: dict(plan["inputs"][role]) for role in ROLES}
    records.update(member_detail_inventory=file_identity(detail_path),
                   raw_member_observation=file_identity(raw_path))
    counts = {domain: plan["contract"][domain + "_count"] for domain in ("field", "property")}
    identity = dict(plan["target"], image_base=plan["target"]["image_base_owner_only"])
    names, observed_counts, binding = _project_files(records=records, identity=identity, counts=counts,
        type_count=plan["contract"]["type_count"], rid_base=plan["contract"]["metadata_token_rid_base"])
    encoded = encode_raw_metadata_names(names, binding=binding, expected_counts=counts)
    if decode_raw_metadata_names(encoded, expected_binding=binding, expected_counts=counts) != names:
        raise AcquisitionError("raw member-name semantic roundtrip differs")
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
        raise AcquisitionError("raw member-name output must not overwrite an existing artifact") from error
    with os.fdopen(fd, "wb") as output:
        output.write(encoded); output.flush(); os.fsync(output.fileno())
    if output_path.read_bytes() != encoded:
        raise AcquisitionError("raw member-name byte roundtrip differs")
    _verify_files(records)
    return {"schema": "alpha.raw-field-property-names/v1", "binding": binding, "inputs": records,
        "inventory": file_identity(output_path), "counts": observed_counts, "domain_counts": counts,
        "checks": {"raw_field_property_domains_closed": True, "raw_member_display_projection_exact": True,
                   "raw_member_null_and_empty_distinct": True, "raw_member_byte_roundtrip": True,
                   "raw_member_semantic_roundtrip": True, "raw_member_sources_unchanged": True},
        "metadata_complete": False}


def load_raw_member_names(*, model, inventory_path, expected_identity, expected_inputs,
                          expected_counts, expected_type_count, expected_rid_base):

    import hashlib
    from alpha.p13 import _safe_path
    from alpha.c01 import encode_raw_metadata_names
    roles = set(ROLES) | {"member_detail_inventory", "raw_member_observation"}
    if (not isinstance(model, dict) or model.get("schema") != "alpha.raw-field-property-names/v1" or
        model.get("metadata_complete") is not False or set(expected_inputs) != roles or
        model.get("inputs") != expected_inputs or model.get("domain_counts") != expected_counts):
        raise AcquisitionError("raw member-name model or explicit source records differ")
    inventory_path = _safe_path(Path(inventory_path))
    if model.get("inventory", {}).get("path") != str(inventory_path):
        raise AcquisitionError("raw member-name inventory path differs")
    all_records = dict(expected_inputs, normalized_inventory=model["inventory"])
    _verify_files(all_records)
    names, counts, binding = _project_files(records=expected_inputs, identity=expected_identity,
        counts=expected_counts, type_count=expected_type_count, rid_base=expected_rid_base)
    raw = inventory_path.read_bytes()
    if (hashlib.sha256(raw).hexdigest() != model["inventory"]["sha256"] or
        model.get("binding") != binding or model.get("counts") != counts or
        decode_raw_metadata_names(raw, expected_binding=binding, expected_counts=expected_counts) != names or
        encode_raw_metadata_names(names, binding=binding, expected_counts=expected_counts) != raw):
        raise AcquisitionError("raw member-name original source replay or roundtrip differs")
    _verify_files(all_records)
    return names, counts


import bisect
import mmap
import re
import struct
from array import array
from dataclasses import dataclass
from itertools import chain
from operator import attrgetter, itemgetter
from pathlib import Path
from typing import Any, Iterable, Iterator

from alpha.p12 import _private_json
from alpha.h01 import AcquisitionError
from alpha.h02 import file_identity


RESOLVER_SCHEMA = "alpha.runtime-resolver-model/v1"
IMAGE_SCN_MEM_EXECUTE = 0x20000000
IMAGE_SCN_MEM_READ = 0x40000000
EXCEPTION_DIRECTORY_INDEX = 3
MINIMUM_STRONG_SCORE = 13

_DLL_STRING = re.compile(
    rb"([A-Za-z0-9_.-]{1,128}\.[Dd][Ll][Ll])\x00"
)
_RIP_RELATIVE = re.compile(
    rb"[\x40-\x4f][\x8b\x8d][\x05\x0d\x15\x1d\x25\x2d\x35\x3d][\x00-\xff]{4}"
)
_DLL_NAME_CHARSET = frozenset(
    b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789_.-"
)
_DLL_TAILS = tuple(
    bytes((0x2E, d, l1, l2, 0x00))
    for d in (0x44, 0x64)
    for l1 in (0x4C, 0x6C)
    for l2 in (0x4C, 0x6C)
)


def _bucket_byte_values(
    low: int, high: int, *, circle_bits: int = 32, bucket_bits: int = 24
) -> tuple[int, ...]:
    circle = 1 << circle_bits
    bucket_size = 1 << bucket_bits
    bucket_count = 1 << (circle_bits - bucket_bits)
    span = (high - low) % circle
    if span >= circle - 1:
        return tuple(range(bucket_count))
    values: list[int] = []
    bucket_reach = bucket_size - 1


    bucket = (low >> bucket_bits) & (bucket_count - 1)
    steps = min(bucket_count, span // bucket_size + 2)
    for _ in range(steps):
        start = bucket << bucket_bits
        if (
            (start - low) % circle <= span
            or (low - start) % circle <= bucket_reach
        ):
            values.append(bucket)
        bucket = (bucket + 1) & (bucket_count - 1)
    return tuple(values)


@dataclass(frozen=True)
class PESection:
    name: str
    virtual_address: int
    virtual_size: int
    raw_offset: int
    raw_size: int
    characteristics: int

    @property
    def raw_end(self) -> int:
        return self.raw_offset + self.raw_size

    @property
    def virtual_end(self) -> int:
        return self.virtual_address + max(self.virtual_size, self.raw_size)

    @property
    def executable(self) -> bool:
        return bool(self.characteristics & IMAGE_SCN_MEM_EXECUTE)

    @property
    def readable(self) -> bool:
        return bool(self.characteristics & IMAGE_SCN_MEM_READ)


@dataclass(frozen=True)
class RuntimeFunction:
    begin_rva: int
    end_rva: int
    unwind_rva: int


@dataclass(frozen=True)
class Anchor:
    name: str
    rva: int


class MappedPE:


    _PE_PARSE_CACHE: dict[tuple[str, int, int, bool], dict[str, object]] = {}
    _PARSED_ATTRIBUTES = (
        "image_base", "size_of_image", "size_of_headers", "sections",
        "runtime_functions", "_runtime_function_starts",
        "_runtime_overlap_intervals", "_runtime_function_prefix_max_end",
    )

    def __init__(
        self, path: Path, *, require_runtime_functions: bool = True
    ):
        self.path = path.expanduser().resolve()
        if not self.path.is_file() or self.path.is_symlink():
            raise AcquisitionError("runtime resolver binary is unavailable")
        file_stat = self.path.stat()
        key = (
            str(self.path), file_stat.st_size, file_stat.st_mtime_ns,
            bool(require_runtime_functions),
        )
        cached = self._PE_PARSE_CACHE.get(key)
        self._source = self.path.open("rb", buffering=0)


        self._containing_cache: dict[int, RuntimeFunction | None] = {}
        try:
            self._mapping = mmap.mmap(self._source.fileno(), 0, access=mmap.ACCESS_READ)
            if cached is not None:
                for name in self._PARSED_ATTRIBUTES:
                    setattr(self, name, cached[name])
                return
            self._parse_headers(require_runtime_functions=require_runtime_functions)
        except Exception:
            self.close()
            raise
        if len(self._PE_PARSE_CACHE) >= 8:
            self._PE_PARSE_CACHE.clear()
        self._PE_PARSE_CACHE[key] = {
            name: getattr(self, name) for name in self._PARSED_ATTRIBUTES
        }

    def close(self) -> None:
        mapping = getattr(self, "_mapping", None)
        source = getattr(self, "_source", None)
        if mapping is not None:
            mapping.close()
            self._mapping = None
        if source is not None:
            source.close()
            self._source = None

    def __enter__(self) -> MappedPE:
        return self

    def __exit__(self, *_args: object) -> None:
        self.close()

    def _parse_headers(self, *, require_runtime_functions: bool) -> None:
        data = self._mapping
        if len(data) < 0x100 or data[:2] != b"MZ":
            raise AcquisitionError("runtime resolver binary is not a PE image")
        pe_offset = struct.unpack_from("<I", data, 0x3C)[0]
        if pe_offset + 24 > len(data) or data[pe_offset : pe_offset + 4] != b"PE\0\0":
            raise AcquisitionError("runtime resolver PE header is invalid")
        section_count = struct.unpack_from("<H", data, pe_offset + 6)[0]
        optional_size = struct.unpack_from("<H", data, pe_offset + 20)[0]
        optional = pe_offset + 24
        if optional + optional_size > len(data):
            raise AcquisitionError("runtime resolver optional header is truncated")
        if struct.unpack_from("<H", data, optional)[0] != 0x20B:
            raise AcquisitionError("runtime resolver requires a PE32+ image")
        if optional_size < 112:
            raise AcquisitionError("runtime resolver optional header lacks directories")
        self.image_base = struct.unpack_from("<Q", data, optional + 24)[0]
        self.size_of_image = struct.unpack_from("<I", data, optional + 56)[0]
        self.size_of_headers = struct.unpack_from("<I", data, optional + 60)[0]
        directory_count = struct.unpack_from("<I", data, optional + 108)[0]
        exception_rva = 0
        exception_size = 0
        directory_offset = optional + 112 + EXCEPTION_DIRECTORY_INDEX * 8
        if directory_count > EXCEPTION_DIRECTORY_INDEX and directory_offset + 8 <= optional + optional_size:
            exception_rva, exception_size = struct.unpack_from("<II", data, directory_offset)

        section_table = optional + optional_size
        if section_table + section_count * 40 > len(data):
            raise AcquisitionError("runtime resolver section table is truncated")
        sections: list[PESection] = []
        for index in range(section_count):
            offset = section_table + index * 40
            raw_name = data[offset : offset + 8].split(b"\0", 1)[0]
            name = raw_name.decode("ascii", errors="replace")
            virtual_size, virtual_address, raw_size, raw_offset = struct.unpack_from(
                "<IIII", data, offset + 8
            )
            characteristics = struct.unpack_from("<I", data, offset + 36)[0]
            if raw_size and raw_offset + raw_size > len(data):
                raise AcquisitionError(f"runtime resolver section is truncated: {name}")
            sections.append(
                PESection(
                    name=name,
                    virtual_address=virtual_address,
                    virtual_size=virtual_size,
                    raw_offset=raw_offset,
                    raw_size=raw_size,
                    characteristics=characteristics,
                )
            )
        self.sections = tuple(sections)
        self.runtime_functions = (
            self._parse_runtime_functions(exception_rva, exception_size)
            if require_runtime_functions
            else ()
        )


        starts: list[int] = []
        overlap_intervals: list[tuple[int, int]] = []
        furthest_end = 0
        prefix_max_end = array("I")
        append_start = starts.append
        append_prefix = prefix_max_end.append
        append_overlap = overlap_intervals.append
        for begin, end, _unwind in self.runtime_functions:
            append_start(begin)
            if begin < furthest_end:
                append_overlap((begin, min(end, furthest_end)))
            if end > furthest_end:
                furthest_end = end
            append_prefix(furthest_end)
        self._runtime_function_starts = tuple(starts)
        self._runtime_overlap_intervals = tuple(overlap_intervals)
        self._runtime_function_prefix_max_end = prefix_max_end

    @property
    def executable_sections(self) -> tuple[PESection, ...]:
        return tuple(
            section for section in self.sections if section.executable and section.raw_size
        )

    @property
    def readonly_sections(self) -> tuple[PESection, ...]:
        return tuple(
            section
            for section in self.sections
            if section.readable and not section.executable and section.raw_size
        )

    def section_for_rva(self, rva: int) -> PESection | None:
        for section in self.sections:
            if section.virtual_address <= rva < section.virtual_end:
                return section
        return None

    def rva_to_offset(self, rva: int) -> int | None:
        if 0 <= rva < self.size_of_headers and rva < len(self._mapping):
            return rva
        section = self.section_for_rva(rva)
        if section is None:
            return None
        delta = rva - section.virtual_address
        if delta >= section.raw_size:
            return None
        return section.raw_offset + delta

    def offset_to_rva(self, section: PESection, offset: int) -> int:
        return section.virtual_address + offset - section.raw_offset

    def executable_rva(self, rva: int) -> bool:
        section = self.section_for_rva(rva)
        return section is not None and section.executable

    def _parse_runtime_functions(
        self, exception_rva: int, exception_size: int
    ) -> tuple[RuntimeFunction, ...]:
        if not exception_rva or exception_size < 12 or exception_size % 12:
            raise AcquisitionError("runtime resolver exception directory is unavailable")
        offset = self.rva_to_offset(exception_rva)
        if offset is None or offset + exception_size > len(self._mapping):
            raise AcquisitionError("runtime resolver exception directory is truncated")
        functions: list[tuple[int, int, int]] = []
        extend = functions.append


        for row in struct.iter_unpack(
            "<III", self._mapping[offset : offset + exception_size]
        ):
            begin, end, unwind = row
            if not (0 < begin < end <= self.size_of_image):
                raise AcquisitionError("runtime resolver exception record is invalid")
            extend(row)
        functions.sort(key=itemgetter(0))
        return tuple(functions)

    def containing_function(self, rva: int) -> RuntimeFunction | None:
        cache = getattr(self, "_containing_cache", None)
        if cache is not None and rva in cache:
            return cache[rva]
        if any(start <= rva < end for start, end in self._runtime_overlap_intervals):
            raise AcquisitionError("runtime resolver function boundary is ambiguous")
        index = bisect.bisect_right(self._runtime_function_starts, rva) - 1
        result: RuntimeFunction | None = None
        while index >= 0:
            begin, end, unwind = self.runtime_functions[index]
            if begin <= rva < end:
                result = RuntimeFunction(begin, end, unwind)
                break
            index -= 1
            if index < 0 or self._runtime_function_prefix_max_end[index] <= rva:
                result = None
                break
        else:
            result = None
        if cache is not None:


            if len(cache) < 131072:
                cache[rva] = result
        return result

    def find_anchors(self, names: Iterable[str] | None = None) -> tuple[Anchor, ...]:
        requested = None
        if names is not None:
            requested = {name.casefold() for name in names if name}
            if not requested:
                raise AcquisitionError("runtime resolver anchor list is empty")
        anchors: dict[tuple[str, int], Anchor] = {}
        mapping = self._mapping
        charset = _DLL_NAME_CHARSET
        for section in self.readonly_sections:


            sites: list[int] = []
            end = section.raw_end
            for tail in _DLL_TAILS:
                cursor = section.raw_offset
                while cursor <= end - 5:
                    found = mapping.find(tail, cursor, end)
                    if found < 0:
                        break
                    sites.append(found)
                    cursor = found + 1
            last_end = -1
            for found in sorted(sites):
                if found < last_end:
                    continue
                start = found
                limit = found - 128
                floor = section.raw_offset
                while start > limit and start > floor and mapping[start - 1] in charset:
                    start -= 1
                if start == found:
                    continue
                last_end = found + 5
                name = mapping[start : found + 4].decode("ascii")
                if requested is not None and name.casefold() not in requested:
                    continue
                rva = self.offset_to_rva(section, start)
                anchors[(name.casefold(), rva)] = Anchor(name=name, rva=rva)
        if requested is not None:
            found = {anchor.name.casefold() for anchor in anchors.values()}
            missing = sorted(requested - found)
            if missing:
                raise AcquisitionError(
                    "runtime resolver anchors are absent from this exact target: "
                    + ", ".join(missing)
                )
        if not anchors:
            raise AcquisitionError("runtime resolver found no assembly-name anchors")
        if len(anchors) > 100_000:
            raise AcquisitionError("runtime resolver anchor set exceeds structural bound")
        return tuple(sorted(anchors.values(), key=lambda item: (item.rva, item.name.casefold())))

    def iter_anchor_references(
        self, anchors: Iterable[Anchor]
    ) -> Iterator[tuple[Anchor, int, int, int]]:
        by_rva: dict[int, Anchor] = {anchor.rva: anchor for anchor in anchors}
        if not by_rva:
            return
        mapping = self._mapping
        unpack = struct.unpack_from
        for section in self.executable_sections:
            rva_delta = section.virtual_address - section.raw_offset


            for match in _RIP_RELATIVE.finditer(
                mapping, section.raw_offset, section.raw_end
            ):
                start = match.start()
                displacement = unpack("<i", mapping, start + 3)[0]
                anchor = by_rva.get(start + rva_delta + 7 + displacement)
                if anchor is None:
                    continue
                rex = mapping[start]
                opcode = mapping[start + 1]
                modrm = mapping[start + 2]
                destination_register = ((modrm >> 3) & 7) | (8 if rex & 4 else 0)
                yield anchor, start + rva_delta, opcode, destination_register

    def direct_callers(self, target_rva: int) -> tuple[int, ...]:
        mapping = self._mapping
        unpack = struct.unpack_from
        callers: list[int] = []
        for section in self.executable_sections:
            rva_delta = section.virtual_address - section.raw_offset
            floor = section.raw_offset
            ceiling = section.raw_end - 5
            if ceiling < floor:
                continue


            block = 1 << 18
            for start in range(floor, section.raw_end, block):
                stop = min(start + block, section.raw_end)
                block_ceiling = min(ceiling, stop - 1)
                low = (target_rva - 5 - (rva_delta + block_ceiling)) % (1 << 32)
                high = (target_rva - 5 - (rva_delta + start)) % (1 << 32)
                pairs = b"|".join(
                    re.escape(bytes((value & 0xFF, value >> 8)))
                    for value in _bucket_byte_values(low, high, bucket_bits=16)
                )
                pattern = re.compile(rb"\xe8[\x00-\xff]{2}(?:" + pairs + b")")
                for match in pattern.finditer(
                    mapping, start, min(stop + 4, section.raw_end)
                ):
                    found = match.start()
                    if found >= stop:
                        continue
                    displacement = unpack("<i", mapping, found + 1)[0]
                    call_rva = found + rva_delta
                    if call_rva + 5 + displacement == target_rva:
                        callers.append(call_rva)


                    for k in range(1, 5):
                        nested = found + k
                        if nested >= stop or mapping[nested] != 0xE8:
                            continue
                        if nested > ceiling:
                            continue
                        displacement = unpack("<i", mapping, nested + 1)[0]
                        call_rva = nested + rva_delta
                        if call_rva + 5 + displacement == target_rva:
                            callers.append(call_rva)
        return tuple(callers)

    def bounded_code(self, begin_rva: int, end_rva: int) -> tuple[int, int] | None:
        begin = self.rva_to_offset(begin_rva)
        if begin is None:
            return None
        section = self.section_for_rva(begin_rva)
        if section is None:
            return None
        end = self.rva_to_offset(end_rva)
        if end is None:
            end = min(section.raw_end, begin + max(0, end_rva - begin_rva))
        return begin, min(end, section.raw_end)


def _has_rax_dereference(data: mmap.mmap, start: int, end: int) -> bool:
    for cursor in range(start, max(start, end - 2)):
        rex, opcode, modrm = data[cursor : cursor + 3]
        if (
            0x48 <= rex <= 0x4F
            and not rex & 1
            and opcode == 0x8B
            and (modrm & 0xC7) in {0x00, 0x40, 0x80}
        ):
            return True
    return False


def _has_rip_relative_store(data: mmap.mmap, start: int, end: int) -> bool:
    for cursor in range(start, max(start, end - 2)):
        rex, opcode, modrm = data[cursor : cursor + 3]
        if 0x40 <= rex <= 0x4F and opcode == 0x89 and (modrm & 0xC7) == 0x05:
            return True
    return False


def _candidate_records(image: MappedPE, anchors: tuple[Anchor, ...]) -> list[dict[str, Any]]:
    candidates: list[dict[str, Any]] = []
    argument_registers = {1, 2, 8, 9}
    for anchor, reference_rva, opcode, destination_register in image.iter_anchor_references(
        anchors
    ):
        function = image.containing_function(reference_rva)
        if function is None:
            continue
        code_bounds = image.bounded_code(reference_rva + 7, function.end_rva)
        if code_bounds is None:
            continue
        scan_start, function_end = code_bounds
        call_limit = min(function_end, scan_start + 40)
        for call_offset in range(scan_start, max(scan_start, call_limit - 4)):
            if image._mapping[call_offset] != 0xE8:
                continue
            call_rva = reference_rva + 7 + call_offset - scan_start
            displacement = struct.unpack_from("<i", image._mapping, call_offset + 1)[0]
            call_target_rva = call_rva + 5 + displacement
            if not image.executable_rva(call_target_rva):
                continue
            after_call = call_offset + 5
            return_window_end = min(function_end, after_call + 40)
            store_window_end = min(function_end, after_call + 64)
            argument_load = opcode == 0x8D and destination_register in argument_registers
            return_dereference = _has_rax_dereference(
                image._mapping, after_call, return_window_end
            )
            global_store = _has_rip_relative_store(
                image._mapping, after_call, store_window_end
            )
            call_distance = call_offset - scan_start
            score = 0
            score += 3 if argument_load else 0
            score += 2
            score += 2
            score += 2 if call_distance <= 16 else 1
            score += 4 if return_dereference else 0
            score += 2 if global_store else 0
            candidates.append(
                {
                    "anchor_name": anchor.name,
                    "anchor_rva": anchor.rva,
                    "reference_rva": reference_rva,
                    "reference_kind": "lea" if opcode == 0x8D else "mov",
                    "argument_register": destination_register,
                    "function_begin_rva": function.begin_rva,
                    "function_end_rva": function.end_rva,
                    "call_rva": call_rva,
                    "call_target_rva": call_target_rva,
                    "call_distance": call_distance,
                    "return_dereference": return_dereference,
                    "rip_relative_store": global_store,
                    "score": score,
                }
            )
    return candidates


def discover_runtime_resolver(
    *, binary: Path, anchor_names: Iterable[str] | None = None
) -> dict[str, Any]:
    binary = binary.expanduser().resolve()
    identity = file_identity(binary)
    with MappedPE(binary) as image:
        anchors = image.find_anchors(anchor_names)
        candidates = _candidate_records(image, anchors)
        strong = [
            candidate
            for candidate in candidates
            if candidate["score"] >= MINIMUM_STRONG_SCORE
            and candidate["return_dereference"]
            and candidate["rip_relative_store"]
        ]
        unique: dict[tuple[int, int, int], dict[str, Any]] = {}
        for candidate in strong:
            key = (
                candidate["function_begin_rva"],
                candidate["call_rva"],
                candidate["call_target_rva"],
            )
            previous = unique.get(key)
            if previous is None or candidate["score"] > previous["score"]:
                unique[key] = candidate
        if len(unique) != 1:
            raise AcquisitionError(
                "runtime resolver behavioral identity is not unique "
                f"(anchors={len(anchors)}, candidates={len(candidates)}, strong={len(unique)})"
            )
        selected = next(iter(unique.values()))
        direct_callers = image.direct_callers(selected["call_target_rva"])
        if len(direct_callers) < 2:
            raise AcquisitionError(
                "runtime resolver selected target is not independently reused "
                f"(direct_callers={len(direct_callers)})"
            )
        return {
            "schema": RESOLVER_SCHEMA,
            "status": "discovered",
            "binary": {
                "bytes": identity["bytes"],
                "sha256": identity["sha256"],
                "image_base": image.image_base,
                "size_of_image": image.size_of_image,
            },
            "anchors": [
                {"name": anchor.name, "rva": anchor.rva} for anchor in anchors
            ],
            "runtime_function_count": len(image.runtime_functions),
            "candidates": candidates,
            "selected": selected,
            "selected_target_direct_callers": list(direct_callers),
            "checks": {
                "target_identity_bound": True,
                "assembly_names_discovered_from_target": True,
                "rip_relative_reference_validated": True,
                "exception_boundary_resolved": True,
                "direct_call_target_executable": True,
                "return_value_behavior_validated": True,
                "behavioral_candidate_unique": True,
                "selected_target_reused": True,
                "fixed_address_used": False,
                "fixed_rva_used": False,
                "fixed_version_used": False,
                "saved_symbol_used": False,
                "external_runtime_component_used": False,
            },
        }


def inspect_runtime_resolver(
    *, binary: Path, output: Path, anchor_names: Iterable[str] | None = None
) -> dict[str, Any]:
    model = discover_runtime_resolver(binary=binary, anchor_names=anchor_names)
    output = output.expanduser().resolve()
    _private_json(output, model)
    return {
        "schema": RESOLVER_SCHEMA,
        "status": model["status"],
        "binary": {
            "bytes": model["binary"]["bytes"],
            "sha256": model["binary"]["sha256"],
        },
        "anchor_count": len(model["anchors"]),
        "candidate_count": len(model["candidates"]),
        "selected_target_direct_caller_count": len(
            model["selected_target_direct_callers"]
        ),
        "checks": model["checks"],
        "raw_addresses_owner_only": True,
        "output": str(output),
    }


from pathlib import Path
from string import Template
import struct
import re

from alpha.p12 import _wide_literal, _windows_z_path
from alpha.h01 import AcquisitionError


def native_string_reader_source(*, contract, output_path, include_utf8_reader=True, sample_scope=None):
    if (type(include_utf8_reader) is not bool or sample_scope is not None and
        (not isinstance(sample_scope, str) or re.fullmatch(r"[a-z][a-z0-9-]{1,63}", sample_scope) is None)):
        raise AcquisitionError("String reader output scope is invalid")
    required = {"class_pointer", "length_pointer", "length_metadata", "indexer_pointer", "indexer_metadata",
                "length_offset", "data_offset", "length_code", "indexer_code"}
    if not isinstance(contract, dict) or set(contract) != required or any(type(contract[key]) is not int or not 0 < contract[key] < 1 << 64
        for key in required - {"length_code", "indexer_code", "length_offset", "data_offset"}):
        raise AcquisitionError("String reader candidate contract is incomplete")
    if (type(contract["length_offset"]) is not int or not 0 <= contract["length_offset"] < 1 << 32 or
        type(contract["data_offset"]) is not int or not contract["length_offset"] + 4 <= contract["data_offset"] < 1 << 32 or
        any(not isinstance(contract[key], bytes) or not 1 <= len(contract[key]) <= 4096
            for key in ("length_code", "indexer_code"))):
        raise AcquisitionError("String reader candidate code or ranges are invalid")
    values = {key: value for key, value in contract.items() if not isinstance(value, bytes)}
    values.update({key: ",".join(str(byte) for byte in contract[key]) for key in ("length_code", "indexer_code")})
    values["output_path"] = _wide_literal(_windows_z_path(Path(output_path)))
    values["io_schema"] = "alpha.string-layout-native-io/v2" if sample_scope else "alpha.string-layout-native-io/v1"
    values["scope_fields"] = (r'\"sample_scope\":\"' + sample_scope + r'\",\"all_selected_names_included\":true,'
                              if sample_scope else r'\"all_nonnull_namespaces_included\":true,')
    return ("#include <io.h>\n#include <fcntl.h>\n#include <sys/stat.h>\n" + _SOURCE.substitute(values)
            + (_READER if include_utf8_reader else ""))


_UNIT_ZERO = bytes(1 if value == 0 else 0 for value in range(256))
_UNIT_ASCII = bytes(1 if value < 0x80 else 0 for value in range(256))
_UNIT_SURROGATE = bytes(1 if 0xD8 <= value <= 0xDF else 0 for value in range(256))


def _count_true_bytewise(left: bytes, right: bytes) -> int:
    if not left:
        return 0
    both = int.from_bytes(left, "little") & int.from_bytes(right, "little")
    return both.to_bytes(len(left), "little").count(1)


_STRING_IO_REPLAY_CACHE: dict[bytes, tuple[int, int, int]] = {}
_STRING_IO_REPLAY_CACHE_LIMIT = 1 << 19


def _string_io_replay_stats(value: bytes) -> tuple[int, int, int]:
    try:
        utf16 = value.decode("utf-8").encode("utf-16-le")
    except UnicodeError as error:
        raise AcquisitionError("String I/O replay name is not valid Unicode") from error
    if not utf16:
        return (0, 0, 0)
    low, high = utf16[0::2], utf16[1::2]
    ascii_units = _count_true_bytewise(
        low.translate(_UNIT_ASCII), high.translate(_UNIT_ZERO)
    )
    return (len(utf16) // 2, len(high) - ascii_units,
            high.translate(_UNIT_SURROGATE).count(1))


def validate_string_layout_io(*, observation, names, expected_process_id, contract, expected_scope=None):
    schema = "alpha.string-layout-native-io/v2" if expected_scope else "alpha.string-layout-native-io/v1"
    if (not isinstance(observation, dict) or observation.get("schema") != schema or
        observation.get("metadata_complete") is not False or observation.get("process_id") != expected_process_id or
        observation.get("class_pointer_owner_only") != contract["class_pointer"] or
        observation.get("length_offset") != contract["length_offset"] or
        observation.get("data_offset") != contract["data_offset"]):
        raise AcquisitionError("String native I/O identity or derived layout differs")
    if expected_scope is not None and observation.get("sample_scope") != expected_scope:
        raise AcquisitionError("String native I/O sample scope differs")
    if any(type(observation.get(key)) is not int for key in
           ("process_id", "class_pointer_owner_only", "length_offset", "data_offset")):
        raise AcquisitionError("String native I/O identity fields must be integers")
    scope_check = "all_selected_names_included" if expected_scope else "all_nonnull_namespaces_included"
    for key in ("all_observed_units_match_live_indexer", "length_before_after_equal", "code_before_after_unchanged",
                scope_check, "candidate_role_derived_without_names"):
        if observation.get(key) is not True:
            raise AcquisitionError("String native I/O proof is incomplete")
    lengths, units, nonascii, surrogates = [], 0, 0, 0
    replay_cache = _STRING_IO_REPLAY_CACHE
    for name in names:
        value = name.value
        if value is None:
            continue


        stats = replay_cache.get(value)
        if stats is None:
            stats = _string_io_replay_stats(value)
            if len(replay_cache) >= _STRING_IO_REPLAY_CACHE_LIMIT:
                replay_cache.clear()
            replay_cache[value] = stats
        length, value_nonascii, value_surrogates = stats
        lengths.append(length); units += length
        nonascii += value_nonascii; surrogates += value_surrogates
    if len(lengths) < 16 or len(set(lengths)) < 4:
        raise AcquisitionError("String native I/O sample support is insufficient")
    expected = {"samples": len(lengths), "empty_samples": lengths.count(0), "utf16_units": units,
        "non_ascii_units": nonascii, "surrogate_units": surrogates, "minimum_length": min(lengths),
        "maximum_length": max(lengths), "distinct_lengths": len(set(lengths))}
    if any(type(observation.get(key)) is not int or observation[key] != value for key, value in expected.items()):
        raise AcquisitionError("String native I/O differs from original-name UTF-16 replay")
    return {"counts": expected, "checks": {"string_getters_current_code_bound": True,
        "string_getter_units_match_observed_memory": True, "string_length_before_after_equal": True,
        "string_io_matches_independent_utf16_replay": True, "string_io_support_sufficient": True}}


_SOURCE = Template(r'''
static const uintptr_t observed_string_class = ${class_pointer}ull;
static const uintptr_t observed_string_length_pointer = ${length_pointer}ull;
static const uintptr_t observed_string_length_metadata = ${length_metadata}ull;
static const uintptr_t observed_string_indexer_pointer = ${indexer_pointer}ull;
static const uintptr_t observed_string_indexer_metadata = ${indexer_metadata}ull;
static const uint32_t observed_string_length_offset = ${length_offset}u;
static const uint32_t observed_string_data_offset = ${data_offset}u;
static const unsigned char observed_string_length_code[] = {${length_code}};
static const unsigned char observed_string_indexer_code[] = {${indexer_code}};
static const wchar_t string_io_output[] = ${output_path};
static uint64_t string_io_samples, string_io_empty, string_io_units, string_io_nonascii, string_io_surrogates;
static uint32_t string_io_min = UINT32_MAX, string_io_max, string_io_distinct;
static unsigned char string_io_lengths[ALPHA_MAX_MANAGED_TEXT + 1u];
static int string_io_code_unchanged(void) {
    return readable(observed_string_length_pointer, sizeof(observed_string_length_code)) &&
        readable(observed_string_indexer_pointer, sizeof(observed_string_indexer_code)) &&
        !memcmp((const void *)observed_string_length_pointer, observed_string_length_code,
                sizeof(observed_string_length_code)) &&
        !memcmp((const void *)observed_string_indexer_pointer, observed_string_indexer_code,
                sizeof(observed_string_indexer_code));
}
static int probe_observed_string_io(uintptr_t object) {
    if (object > UINTPTR_MAX - observed_string_data_offset -
            (uintptr_t)ALPHA_MAX_MANAGED_TEXT * sizeof(uint16_t)) return 0;
    if (!string_io_code_unchanged() || !object_class(object, observed_string_class) ||
        !readable(object + observed_string_length_offset, sizeof(int32_t))) return 0;
    int32_t memory_length = 0;
    memcpy(&memory_length, (const void *)(object + observed_string_length_offset), sizeof(memory_length));
    if (memory_length < 0 || (uint32_t)memory_length > ALPHA_MAX_MANAGED_TEXT ||
        (memory_length && !readable(object + observed_string_data_offset, (SIZE_T)memory_length * sizeof(uint16_t))))
        return 0;
    int32_t (*length_fn)(uintptr_t, uintptr_t) = (void *)observed_string_length_pointer;
    uint16_t (*indexer_fn)(uintptr_t, int32_t, uintptr_t) = (void *)observed_string_indexer_pointer;
    if (length_fn(object, observed_string_length_metadata) != memory_length) return 0;
    for (int32_t index = 0; index < memory_length; index++) {
        uint16_t expected = 0;
        memcpy(&expected, (const void *)(object + observed_string_data_offset +
                                        (uintptr_t)index * sizeof(uint16_t)), sizeof(expected));
        if (indexer_fn(object, index, observed_string_indexer_metadata) != expected) return 0;
        string_io_units++; string_io_nonascii += expected > 0x7fu;
        string_io_surrogates += expected >= 0xd800u && expected <= 0xdfffu;
    }
    if (length_fn(object, observed_string_length_metadata) != memory_length || !string_io_code_unchanged()) return 0;
    string_io_samples++; string_io_empty += !memory_length;
    if ((uint32_t)memory_length < string_io_min) string_io_min = (uint32_t)memory_length;
    if ((uint32_t)memory_length > string_io_max) string_io_max = (uint32_t)memory_length;
    if (!string_io_lengths[memory_length]) { string_io_lengths[memory_length] = 1; string_io_distinct++; }
    return 1;
}
static int write_string_io_probe(void) {
    if (!string_io_code_unchanged() || string_io_samples < 16u || string_io_distinct < 4u) return 0;
    int fd = _wopen(string_io_output, _O_WRONLY | _O_CREAT | _O_EXCL | _O_BINARY, _S_IREAD | _S_IWRITE);
    if (fd < 0) return 0;
    FILE *output = _fdopen(fd, "wb");
    if (!output) { _close(fd); _wremove(string_io_output); return 0; }
    int result = fprintf(output,
        "{\"schema\":\"$io_schema\",\"process_id\":%lu,"
        "\"samples\":%llu,\"empty_samples\":%llu,\"utf16_units\":%llu,"
        "\"non_ascii_units\":%llu,\"surrogate_units\":%llu,"
        "\"minimum_length\":%u,\"maximum_length\":%u,\"distinct_lengths\":%u,"
        "\"class_pointer_owner_only\":%llu,\"length_offset\":%u,\"data_offset\":%u,"
        "\"all_observed_units_match_live_indexer\":true,\"length_before_after_equal\":true,"
        "\"code_before_after_unchanged\":true,"
        "$scope_fields"
        "\"candidate_role_derived_without_names\":true,\"metadata_complete\":false}\n",
        (unsigned long)GetCurrentProcessId(), (unsigned long long)string_io_samples,
        (unsigned long long)string_io_empty, (unsigned long long)string_io_units,
        (unsigned long long)string_io_nonascii, (unsigned long long)string_io_surrogates,
        string_io_min, string_io_max, string_io_distinct, (unsigned long long)observed_string_class,
        observed_string_length_offset, observed_string_data_offset);
    int ok = result > 0 && !ferror(output);
    if (fclose(output)) ok = 0;
    if (!ok) _wremove(string_io_output);
    return ok;
}
''')

_READER = r'''
static int managed_utf8(
    uintptr_t object, int allow_null, char **output, uint32_t *bytes
) {
    *output = NULL;
    *bytes = 0;
    if (!object) return allow_null;
    if (!probe_observed_string_io(object)) return 0;
    if (!object_class(object, observed_string_class) ||
        !readable(object + observed_string_length_offset, sizeof(int32_t))) return 0;
    int32_t length = 0;
    memcpy(&length, (const void *)(object + observed_string_length_offset), sizeof(length));
    if (length < 0 || (uint32_t)length > ALPHA_MAX_MANAGED_TEXT ||
        (length && !readable(
            object + observed_string_data_offset, (SIZE_T)length * sizeof(wchar_t)))) return 0;
    if (!length) return 1;
    int required = WideCharToMultiByte(
        CP_UTF8, WC_ERR_INVALID_CHARS, (const wchar_t *)(object + observed_string_data_offset),
        length, NULL, 0, NULL, NULL);
    if (required <= 0 || required > 4 * (int)ALPHA_MAX_MANAGED_TEXT) return 0;
    char *value = (char *)malloc((SIZE_T)required);
    if (!value || WideCharToMultiByte(
            CP_UTF8, WC_ERR_INVALID_CHARS,
            (const wchar_t *)(object + observed_string_data_offset), length,
            value, required, NULL, NULL) != required) {
        free(value);
        return 0;
    }
    if (memchr(value, 0, (SIZE_T)required)) {
        free(value);
        return 0;
    }
    *output = value;
    *bytes = (uint32_t)required;
    return 1;
}

'''


import json
import math
import os
from pathlib import Path
import queue
import threading
import subprocess
import time

from alpha.p12 import _build, _compiler, _private_text, _windows_z_path
from alpha.h01 import AcquisitionError
from alpha.p13 import _safe_path, _file_record
from alpha.c01 import bind_runtime_process


LIFETIME_SOURCE = r'''
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <wchar.h>

static int positive_u64(const wchar_t *text, uint64_t *value) {
    uint64_t result = 0;
    if (!text || !*text) return 0;
    for (; *text; text++) {
        if (*text < L'0' || *text > L'9') return 0;
        uint64_t digit = (uint64_t)(*text - L'0');
        if (result > (UINT64_MAX - digit) / 10u) return 0;
        result = result * 10u + digit;
    }
    *value = result; return result != 0;
}

/* The live client can report the launcher symlink it was started from while
   the recorded candidates hold the resolved target (or the reverse), and
   GetFullPathNameW does not resolve that link.  Both paths still name the
   same executable, so fall back to the file identity that matters here: the
   executable file name and its byte size. */
static int same_executable_file(const wchar_t *left, const wchar_t *right) {
    const wchar_t *left_name = wcsrchr(left, L'\\');
    const wchar_t *right_name = wcsrchr(right, L'\\');
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
    if (right_file == INVALID_HANDLE_VALUE) {
        CloseHandle(left_file); return 0;
    }
    LARGE_INTEGER left_size, right_size;
    BOOL left_ok = GetFileSizeEx(left_file, &left_size);
    BOOL right_ok = GetFileSizeEx(right_file, &right_size);
    CloseHandle(left_file); CloseHandle(right_file);
    return left_ok && right_ok && left_size.QuadPart > 0 &&
        left_size.QuadPart == right_size.QuadPart;
}

int wmain(int argc, wchar_t **argv) {
    uint64_t pid = 0, creation = 0;
    if (argc < 4 || !positive_u64(argv[1], &pid) || pid > UINT32_MAX ||
        !positive_u64(argv[2], &creation)) return 2;
    wchar_t actual[32768];
    HANDLE target = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION | SYNCHRONIZE,
                                FALSE, (DWORD)pid);
    if (!target) return 4;
    FILETIME c, e, k, u; DWORD capacity = 32768;
    if (!QueryFullProcessImageNameW(target, 0, actual, &capacity) ||
        !GetProcessTimes(target, &c, &e, &k, &u) ||
        (((uint64_t)c.dwHighDateTime << 32) | c.dwLowDateTime) != creation) {
        CloseHandle(target); return 5;
    }
    int path_match = 0;
    for (int index = 3; index < argc && !path_match; index++) {
        wchar_t expected[32768];
        DWORD n = GetFullPathNameW(argv[index], 32768, expected, NULL);
        if (n && n < 32768 && (!_wcsicmp(actual, expected) ||
            same_executable_file(actual, expected))) path_match = 1;
    }
    if (!path_match) { CloseHandle(target); return 5; }
    if (WaitForSingleObject(target, 0) != WAIT_TIMEOUT) {
        CloseHandle(target); return 6;
    }
    printf("{\"schema\":\"alpha.runtime-process-lifetime/v1\",\"status\":\"watching\","
           "\"process_id\":%lu,\"creation_filetime\":%llu}\n",
           (unsigned long)pid, (unsigned long long)creation);
    if (fflush(stdout)) { CloseHandle(target); return 7; }
    DWORD result = WaitForSingleObject(target, INFINITE);
    CloseHandle(target);
    if (result == WAIT_OBJECT_0) {
        fprintf(stderr, "target process instance exited\n"); return 10;
    }
    fprintf(stderr, "target lifetime wait failed\n"); return 11;
}
'''


class RuntimeProcessLifetimeGuard:
    def __init__(self, *, identity, wine: Path, wineprefix: Path,
                 build_dir: Path, compiler: Path | None = None, startup_timeout=30.0):


        with bind_runtime_process(identity):
            pass
        if (type(startup_timeout) not in (int, float) or not math.isfinite(startup_timeout) or
            not 0 < startup_timeout <= 30):
            raise AcquisitionError("runtime lifetime guard startup timeout is invalid")
        self.identity = dict(identity)
        self.wine = wine.expanduser().resolve()
        self.wineprefix = wineprefix.expanduser().resolve()
        self.directory = _safe_path(build_dir)
        self.compiler = compiler
        self.startup_timeout = startup_timeout
        self.process = None
        self.log = None

    def __enter__(self):
        self.directory.mkdir(mode=0o700, parents=True, exist_ok=False)
        source = self.directory / "runtime-process-lifetime.c"
        program = self.directory / "runtime-process-lifetime.exe"
        _private_text(source, LIFETIME_SOURCE)


        cached_windows_build(
            [str(_compiler(self.compiler)), "-O2", "-municode", "-Wall", "-Wextra",
             "-Werror", str(source), "-o", str(program)],
            label="runtime process lifetime guard",
            source_path=source,
            output_path=program,
        )
        program.chmod(0o600)
        record = _file_record(program)
        fd = os.open(
            self.directory / "runtime-process-lifetime.private.log",
            os.O_WRONLY
            | os.O_CREAT
            | os.O_EXCL
            | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        self.log = os.fdopen(fd, "wb")
        try:
            if _file_record(program) != record:
                raise AcquisitionError("runtime lifetime guard changed before execution")
            bindings = current_runtime_process_binding()
            path_candidates: list[str] = []
            for value in (
                self.identity.get("executable_path"),
                bindings[2] if bindings is not None else None,
            ):
                if not isinstance(value, str) or not value:
                    continue
                for spelling in (
                    Path(value).expanduser(),
                    Path(value).expanduser().absolute().resolve(),
                ):
                    text = str(spelling)
                    if text not in path_candidates:
                        path_candidates.append(text)
            if not path_candidates:
                raise AcquisitionError(
                    "runtime lifetime guard executable binding is absent"
                )
            arguments = _host_run(
                str(self.wine),
                program,
                str(self.identity["process_id"]),
                str(self.identity["creation_filetime"]),


                *path_candidates,
                _resolve_paths=False,
            )
            environment = dict(os.environ, WINEPREFIX=str(self.wineprefix), WINEDEBUG="-all")


            last_error: AcquisitionError | None = None
            for attempt in range(3):
                if attempt:
                    self.log.write(b"--- lifetime guard startup retry ---\n")
                    self.log.flush()
                    time.sleep(5.0)
                self.process = subprocess.Popen(
                    arguments, env=environment,
                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=self.log,
                )
                try:
                    self._await_ready()
                except AcquisitionError as error:
                    last_error = error
                    if not any(
                        marker in str(error)
                        for marker in (
                            "did not confirm the target instance",
                            "runtime lifetime guard startup timed out",
                        )
                    ):
                        raise
                    self._abandon_attempt()
                    continue
                break
            else:
                assert last_error is not None
                raise last_error
            self.assert_alive()
            return self
        except BaseException:
            self.close()
            raise

    def _abandon_attempt(self) -> None:
        process, self.process = self.process, None
        if process is not None:
            try:
                if process.poll() is None:
                    process.terminate()
                try:
                    process.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait(timeout=3)
            finally:
                if process.stdout is not None:
                    process.stdout.close()

    def _await_ready(self):
        deadline = time.monotonic() + self.startup_timeout
        data = bytearray()
        descriptor = self.process.stdout.fileno()
        stream: queue.Queue = queue.Queue()

        def forward():
            try:
                while True:
                    part = os.read(descriptor, 4096)
                    if not part:
                        break
                    stream.put(part)
                    if b"\n" in part:
                        break
            except OSError:
                pass
            finally:
                stream.put(b"")

        threading.Thread(target=forward, daemon=True).start()
        while b"\n" not in data:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise AcquisitionError("runtime lifetime guard startup timed out")
            try:
                part = stream.get(timeout=remaining)
            except queue.Empty:
                raise AcquisitionError("runtime lifetime guard startup timed out") from None
            if not part or len(data) + len(part) > 4096:
                raise AcquisitionError("runtime lifetime guard did not confirm the target instance")
            data.extend(part)
        try:
            ready = json.loads(data)
        except (ValueError, UnicodeError) as error:
            raise AcquisitionError("runtime lifetime guard response is malformed") from error
        expected = {"schema": "alpha.runtime-process-lifetime/v1", "status": "watching",
                    "process_id": self.identity["process_id"],
                    "creation_filetime": self.identity["creation_filetime"]}
        if ready != expected:
            raise AcquisitionError("runtime lifetime guard confirmed a different process instance")

    def assert_alive(self):
        if self.process is None:
            raise AcquisitionError("runtime lifetime guard is not active")
        code = self.process.poll()
        if code == 10:
            raise AcquisitionError("target process exited during runtime capture")
        if code is not None:
            raise AcquisitionError(f"runtime lifetime guard failed during capture ({code})")

    def close(self):


        process, self.process = self.process, None
        try:
            if process is not None:
                try:
                    if process.poll() is None:
                        process.terminate()
                    try:
                        process.wait(timeout=3)
                    except subprocess.TimeoutExpired:
                        process.kill()
                        process.wait(timeout=3)
                finally:
                    if process.stdout is not None:
                        process.stdout.close()
        finally:
            if self.log is not None:
                self.log.close()
                self.log = None

    def __exit__(self, *_):
        self.close()
