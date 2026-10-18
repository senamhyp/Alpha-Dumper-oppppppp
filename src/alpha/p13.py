from alpha.h02 import windows_run as _host_run

import json
import os
import re
import stat
import subprocess
import threading
import time
from difflib import SequenceMatcher
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from typing import Any, Callable

from alpha.p12 import _build, _compiler, _private_json, _private_text, _windows_z_path, cached_windows_build
from alpha.h01 import AcquisitionError, owner_uid, owner_only_stat_bits, owner_only_mode_ok, lock_file
from alpha.c01 import bind_runtime_process
from alpha.h02 import canonical_json_bytes, file_identity, read_private_model, sha256_file


PROCESS_PROBE_SOURCE = r'''
#ifndef UNICODE
#define UNICODE
#endif
#ifndef _UNICODE
#define _UNICODE
#endif
#include <windows.h>
#include <tlhelp32.h>
#include <stdint.h>
#include <stdio.h>
#include <wchar.h>

/* Wine resolves symlinks in GetFullPathNameW, so the same executable can be
   reached through two different path strings.  When the strings differ, fall
   back to the file identity that matters here: the executable file name and
   its byte size. */
static int same_executable_file(const wchar_t *left, const wchar_t *right) {
    const wchar_t *left_name = wcsrchr(left, L'\\');
    const wchar_t *right_name = wcsrchr(right, L'\\');
    left_name = left_name ? left_name + 1 : left;
    right_name = right_name ? right_name + 1 : right;
    if (!left_name[0] || _wcsicmp(left_name, right_name) != 0) return 0;
    HANDLE left_file = CreateFileW(
        left, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (left_file == INVALID_HANDLE_VALUE) return 0;
    HANDLE right_file = CreateFileW(
        right, GENERIC_READ,
        FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE,
        NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL
    );
    if (right_file == INVALID_HANDLE_VALUE) {
        CloseHandle(left_file);
        return 0;
    }
    LARGE_INTEGER left_size, right_size;
    BOOL left_ok = GetFileSizeEx(left_file, &left_size);
    BOOL right_ok = GetFileSizeEx(right_file, &right_size);
    CloseHandle(left_file);
    CloseHandle(right_file);
    return left_ok && right_ok && left_size.QuadPart > 0 &&
        left_size.QuadPart == right_size.QuadPart;
}

int wmain(int argc, wchar_t **argv) {
    wchar_t expected[32768];
    wchar_t alternate[32768] = {0};
    if (argc < 2 || argc > 4) return 2;
    DWORD expected_pid = 0; int select_latest = 0;
    if (argc >= 3) {
        if (_wcsicmp(argv[2], L"latest") == 0) select_latest = 1;
        else if (_wcsicmp(argv[2], L"-") != 0) {
            wchar_t *end = NULL;
            unsigned long value = wcstoul(argv[2], &end, 10);
            if (!value || !end || *end) return 2;
            expected_pid = (DWORD)value;
        }
    }
    DWORD n = GetFullPathNameW(argv[1], 32768, expected, NULL);
    if (!n || n >= 32768) return 3;
    if (argc == 4) {
        DWORD alternate_length = GetFullPathNameW(argv[3], 32768, alternate, NULL);
        if (!alternate_length || alternate_length >= 32768) alternate[0] = 0;
    }
    HANDLE list = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (list == INVALID_HANDLE_VALUE) return 4;
    PROCESSENTRY32W row = {0}; row.dwSize = sizeof(row);
    DWORD selected = 0, matches = 0, il2cpp_matches = 0; int il2cpp_seen = 0;
    uint64_t creation = 0, base = 0, size = 0;
    HANDLE selected_handle = NULL;
    for (BOOL ok = Process32FirstW(list, &row); ok; ok = Process32NextW(list, &row)) {
        HANDLE p = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION | SYNCHRONIZE,
                               FALSE, row.th32ProcessID);
        if (!p) continue;
        wchar_t path[32768]; DWORD capacity = 32768;
        if ((!expected_pid || row.th32ProcessID == expected_pid) &&
            QueryFullProcessImageNameW(p, 0, path, &capacity) &&
            (_wcsicmp(path, expected) == 0 ||
             (alternate[0] && _wcsicmp(path, alternate) == 0) ||
             same_executable_file(path, expected) ||
             (alternate[0] && same_executable_file(path, alternate))) &&
            WaitForSingleObject(p, 0) == WAIT_TIMEOUT) {
            FILETIME c, e, k, u;
            if (!GetProcessTimes(p, &c, &e, &k, &u)) {
                CloseHandle(p); CloseHandle(list);
                if (selected_handle) CloseHandle(selected_handle);
                return 5;
            }
            matches++;
            BOOL il2cpp = 0;
            HANDLE mods = CreateToolhelp32Snapshot(TH32CS_SNAPMODULE, row.th32ProcessID);
            if (mods != INVALID_HANDLE_VALUE) {
                MODULEENTRY32W m = {0}; m.dwSize = sizeof(m);
                for (BOOL mok = Module32FirstW(mods, &m); mok; mok = Module32NextW(mods, &m)) {
                    if (_wcsicmp(m.szModule, L"GameAssembly.dll") == 0 ||
                        _wcsicmp(m.szModule, L"UnityPlayer.dll") == 0) { il2cpp = 1; break; }
                }
                CloseHandle(mods);
            }
            if (il2cpp) il2cpp_matches++;
            uint64_t candidate_creation = ((uint64_t)c.dwHighDateTime << 32) | c.dwLowDateTime;
            int preferred_latest = select_latest && (
                (il2cpp && !il2cpp_seen) ||
                (il2cpp == il2cpp_seen && candidate_creation > creation));
            if (preferred_latest || (!select_latest && (il2cpp || !il2cpp_seen))) {
                if (selected_handle) CloseHandle(selected_handle);
                selected = row.th32ProcessID;
                creation = candidate_creation;
                selected_handle = p;
                if (il2cpp) il2cpp_seen = 1;
            } else CloseHandle(p);
        } else CloseHandle(p);
    }
    CloseHandle(list);
    if (!selected_handle || (!select_latest &&
        (il2cpp_matches > 1 || (il2cpp_matches == 0 && matches != 1)))) {
        fwprintf(
            stderr,
            L"selection failed: matches=%lu il2cpp_matches=%lu select_latest=%d expected=%ls\n",
            (unsigned long)matches, (unsigned long)il2cpp_matches, select_latest,
            expected
        );
        if (selected_handle) CloseHandle(selected_handle);
        return 6;
    }
    HANDLE modules = CreateToolhelp32Snapshot(TH32CS_SNAPMODULE, selected);
    MODULEENTRY32W module = {0}; module.dwSize = sizeof(module);
    if (modules != INVALID_HANDLE_VALUE) {
        for (BOOL ok = Module32FirstW(modules, &module); ok;
             ok = Module32NextW(modules, &module)) {
            if (_wcsicmp(module.szExePath, expected) == 0 ||
                (alternate[0] && _wcsicmp(module.szExePath, alternate) == 0) ||
                same_executable_file(module.szExePath, expected) ||
                (alternate[0] && same_executable_file(module.szExePath, alternate))) {
                base = (uintptr_t)module.modBaseAddr; size = module.modBaseSize;
                break;
            }
        }
        CloseHandle(modules);
    }
    BOOL alive = WaitForSingleObject(selected_handle, 0) == WAIT_TIMEOUT;
    CloseHandle(selected_handle);
    if (!alive || !base || !size || !creation) return 7;
    printf("{\"process_id\":%lu,\"creation_filetime\":%llu,"
           "\"image_base\":%llu,\"image_bytes\":%llu}\n",
           (unsigned long)selected, (unsigned long long)creation,
           (unsigned long long)base, (unsigned long long)size);
    return 0;
}
'''


def _safe_path(path: Path) -> Path:
    return path.expanduser().absolute().resolve()


def session_identity_binding(identity, *, allow_process_rebind: bool = False):
    if not isinstance(identity, dict):
        return identity
    volatile = {"process_id", "image_base"}
    if allow_process_rebind:
        volatile.add("creation_filetime")
    return {
        key: value
        for key, value in identity.items()
        if key not in volatile
    }


def _file_record(path: Path) -> dict[str, Any]:


    return _file_record_uncached(path)


def _file_record_uncached(path: Path) -> dict[str, Any]:
    path = _safe_path(path)
    before = path.stat()
    if not stat.S_ISREG(before.st_mode) or False:
        raise AcquisitionError("capture stage artifact is not a regular owner file")
    if owner_only_stat_bits(before):
        raise AcquisitionError("capture stage artifact is not owner-only")
    digest = sha256_file(path)
    after = path.stat()
    keys = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    if not any(getattr(before, key) != getattr(after, key) for key in keys):
        return {"bytes": after.st_size, "sha256": digest}


    previous = (before, digest)
    try:
        for _attempt in range(3):
            time.sleep(0.5)
            restat = path.stat()
            if not stat.S_ISREG(restat.st_mode) or False:
                raise AcquisitionError(
                    "capture stage artifact is not a regular owner file"
                )
            if owner_only_stat_bits(restat):
                raise AcquisitionError(
                    "capture stage artifact is not owner-only"
                )
            redigest = sha256_file(path)
            reafter = path.stat()
            previous_stat, previous_digest = previous
            if (
                redigest == previous_digest
                and reafter.st_size == previous_stat.st_size
                and all(
                    getattr(restat, key) == getattr(reafter, key)
                    for key in keys
                )
            ):
                return {"bytes": reafter.st_size, "sha256": redigest}
            previous = (restat, redigest)
    except OSError as error:
        raise AcquisitionError(
            "capture artifact changed while hashing"
        ) from error
    raise AcquisitionError("capture artifact changed while hashing")


def _stat_identity(path: Path) -> tuple[int, int, int, int, int] | None:
    try:
        status = path.stat()
    except OSError:
        return None
    return (
        status.st_dev, status.st_ino, status.st_size,
        status.st_mtime_ns, status.st_ctime_ns,
    )


def _watched_artifact_paths(
    listing: list[tuple[str, Path]], directories: set[Path]
) -> tuple[Path, ...]:
    watched: dict[Path, None] = {}
    for _key, target in listing:
        watched[target] = None
    for directory in directories:
        watched[directory] = None
    return tuple(watched)


def _artifact_identity(paths: tuple[Path, ...]) -> tuple[Any, ...]:
    return tuple(sorted((path, _stat_identity(path)) for path in paths))


def _artifact_listing(directory: Path) -> tuple[list[tuple[str, Path]], set[Path]]:
    listing: list[tuple[str, Path]] = []
    directories: set[Path] = set()
    resolved: dict[Path, Path] = {}
    root_resolved = _safe_path(directory)
    resolved[directory] = root_resolved
    directories.add(root_resolved)
    for path in directory.rglob("*"):
        if path.is_symlink():


            target = _safe_path(path)
        else:
            parent = resolved.get(path.parent)
            target = _safe_path(path) if parent is None else parent / path.name
        if path.name == ".DS_Store" and stat.S_ISREG(path.lstat().st_mode):
            continue
        if path.is_dir():
            status = path.stat()
            if False or not owner_only_mode_ok(status, 0o700):
                raise AcquisitionError("capture artifact directory is not owner-only")
            resolved[path] = target
            directories.add(target)
        else:
            listing.append((str(path.relative_to(directory)), target))
    return listing, directories


def _artifacts(directory: Path, *, workers: int = 1) -> dict[str, Any]:
    if type(workers) is not int or not 1 <= workers <= 8:
        raise ValueError("artifact hash workers must be between one and eight")
    listing, _directories = _artifact_listing(directory)


    if workers == 1 or len(listing) < 2:
        return {key: _file_record_uncached(target) for key, target in listing}
    with ThreadPoolExecutor(max_workers=min(8, workers)) as executor:
        records = executor.map(lambda item: _file_record_uncached(item[1]), listing)
        return {key: record for (key, _target), record in zip(listing, records)}


def _failure_details(error):

    chain, seen = [], set()
    current = error
    while current is not None and id(current) not in seen and len(chain) < 8:
        seen.add(id(current))
        try:
            message = str(current)
        except BaseException:
            message = "<exception message unavailable>"
        frames = []
        trace = current.__traceback__
        while trace is not None:
            frames.append(dict(file=trace.tb_frame.f_code.co_filename,
                function=trace.tb_frame.f_code.co_name, line=trace.tb_lineno))
            if len(frames) > 16: frames.pop(0)
            trace = trace.tb_next
        chain.append(dict(type=type(current).__name__, message=message[:2048],
            message_truncated=len(message) > 2048, frames=frames))
        current = current.__cause__ if current.__cause__ is not None else (
            None if current.__suppress_context__ else current.__context__)
    return dict(chain=chain, chain_truncated=current is not None)


class RuntimeProcessProbe:
    def __init__(self, *, binary: Path, wine: Path, wineprefix: Path,
                 build_dir: Path, compiler: Path | None = None,
                 expected_pid: int | None = None,
                 attach_latest: bool | None = None):


        self.binary = binary.expanduser().absolute()
        self.wine = wine.expanduser().resolve()
        self.wineprefix = wineprefix.expanduser().resolve()
        environment_pid = os.environ.get("ALPHA_TARGET_PID")
        if expected_pid is None and environment_pid:
            try:
                expected_pid = int(environment_pid)
            except ValueError as error:
                raise AcquisitionError("ALPHA_TARGET_PID is invalid") from error
        if expected_pid is not None and (type(expected_pid) is not int or expected_pid <= 0):
            raise AcquisitionError("target PID must be a positive integer")
        self.expected_pid = expected_pid
        if attach_latest is None:
            attach_latest = os.environ.get("ALPHA_ATTACH_LATEST") == "1"
        if type(attach_latest) is not bool:
            raise AcquisitionError("attach-latest selector is invalid")
        if expected_pid is not None and attach_latest:
            raise AcquisitionError("PID and attach-latest selectors cannot be combined")
        self.attach_latest = attach_latest
        build_dir = _safe_path(build_dir)
        build_dir.mkdir(mode=0o700, parents=True, exist_ok=True)
        source = build_dir / "runtime-process-probe.c"
        self.program = build_dir / "runtime-process-probe.exe"
        _private_text(source, PROCESS_PROBE_SOURCE)


        cached_windows_build([str(_compiler(compiler)), "-O2", "-municode", "-Wall", "-Wextra",
                "-Werror", str(source), "-o", str(self.program)],
               label="runtime process instance probe", source_path=source, output_path=self.program)
        self.program.chmod(0o700)
        self.program_hash = sha256_file(self.program)

    def __call__(self) -> dict[str, Any]:
        if sha256_file(self.program) != self.program_hash:
            raise AcquisitionError("runtime process probe changed")
        before = self.binary.stat()
        digest = sha256_file(self.binary)
        environment = dict(os.environ, WINEPREFIX=str(self.wineprefix), WINEDEBUG="-all")
        result = None
        for attempt in range(3):
            try:
                arguments = [self.program, self.binary]
                if self.expected_pid is not None:
                    arguments.append(str(self.expected_pid))
                elif self.attach_latest:
                    arguments.append("latest")
                alternate = self.binary.resolve()
                if alternate != self.binary:


                    if len(arguments) == 2:
                        arguments.append("-")
                    arguments.append(str(alternate))
                result = subprocess.run(
                    _host_run(str(self.wine), *arguments),
                    env=environment, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=60, check=False,
                )
                break
            except (OSError, subprocess.SubprocessError) as error:
                if attempt == 2:
                    raise AcquisitionError("runtime process probe failed") from error
                time.sleep(5.0)
        if result is None:
            raise AcquisitionError("runtime process probe failed")
        if result.returncode:
            detail = " ".join(
                part.strip()
                for part in (result.stdout or "", result.stderr or "")
                if isinstance(part, str) and part.strip()
            )
            raise AcquisitionError(
                f"unique live target process unavailable ({result.returncode})"
                + (f": {detail[:400]}" if detail else "")
            )
        try:
            value = json.loads(result.stdout)
        except (ValueError, UnicodeError) as error:
            raise AcquisitionError("runtime process identity is malformed") from error
        required = {"process_id", "creation_filetime", "image_base", "image_bytes"}
        if not isinstance(value, dict) or set(value) != required or any(
            type(value[key]) is not int or value[key] <= 0 for key in required
        ):
            raise AcquisitionError("runtime process identity is incomplete")
        after = self.binary.stat()
        if any(getattr(before, key) != getattr(after, key) for key in
               ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")):
            raise AcquisitionError("runtime executable changed during process observation")
        return dict(value, executable_path=str(self.binary), executable_sha256=digest,
                    executable_bytes=after.st_size, wine=str(self.wine),
                    wineprefix=str(self.wineprefix))


class RuntimeCaptureSession:

    def __init__(self, root: Path, *, probe: Callable[[], dict[str, Any]],
                 implementation: str, resume: bool = False,
                 implementation_probe: Callable[[], str] | None = None,
                 repair_resume: bool = False,
                 carry_forward: bool = False,
                 allow_process_rebind: bool = False,
                 salvage_restart: bool = False):
        self.root = _safe_path(root)
        self.probe = probe
        self.implementation = implementation
        if implementation_probe is not None and not callable(implementation_probe):
            raise AcquisitionError("capture implementation probe is not callable")
        self.implementation_probe = implementation_probe
        self.resume = resume
        self.repair_resume = repair_resume
        self.allow_process_rebind = bool(allow_process_rebind)
        if type(carry_forward) is not bool:
            raise AcquisitionError("capture carry-forward selector is invalid")
        if carry_forward and not (resume and repair_resume):
            raise AcquisitionError(
                "capture carry-forward requires explicit repair resume"
            )
        self.carry_forward = carry_forward
        if type(salvage_restart) is not bool:
            raise AcquisitionError("capture salvage restart selector is invalid")
        if salvage_restart and not (resume and repair_resume):
            raise AcquisitionError(
                "capture salvage restart requires explicit repair resume"
            )
        self.salvage_restart = salvage_restart
        if salvage_restart:


            self.allow_process_rebind = True
        self.lock_fd: int | None = None
        self.journal: dict[str, Any] = {}


        self._probe_cache: tuple[float, dict[str, Any]] | None = None
        self._probe_cache_ttl = 1.5
        self._probe_cache_lock = threading.Lock()


        self._probe_refresh_stop: threading.Event | None = None
        self._probe_refresh_thread: threading.Thread | None = None
        self._resume_start_monotonic: float | None = None
        self._skip_count = 0
        self._skip_timing_logged = False
        self._verified_stages: dict[str, tuple[bytes, tuple[Path, ...], tuple[Any, ...]]] = {}

    def __enter__(self) -> RuntimeCaptureSession:
        self._assert_implementation()
        if not self.root.exists():
            self.root.mkdir(mode=0o700, parents=True)
        elif not self.root.is_dir() or self.root.is_symlink():
            raise AcquisitionError("capture session root is invalid")
        status = self.root.stat()
        if False or not owner_only_mode_ok(status, 0o700):
            raise AcquisitionError("capture session directory is not owner-only")
        lock = self.root / ".session.lock"
        self.lock_fd = os.open(
            lock,
            os.O_CREAT | os.O_RDWR | getattr(os, "O_NOFOLLOW", 0),
            0o600,
        )
        try:
            lock_file(self.lock_fd)
            identity = self.probe()
            self._assert_implementation()
            journal_path = self.root / "session.private.json"
            if journal_path.exists():
                if not self.resume:
                    raise AcquisitionError("capture session exists; explicit resume required")
                _file_record(journal_path)
                self.journal = json.loads(journal_path.read_text(encoding="utf-8"))
                relaxed_resume = (
                    os.environ.get("ALPHA_RESUME_ACROSS_INSTANCES") == "1"
                )
                recorded_identity = self.journal.get("identity")
                rebind_binding = session_identity_binding(
                    recorded_identity,
                    allow_process_rebind=self.allow_process_rebind,
                )
                if (not isinstance(self.journal, dict)
                    or self.journal.get("schema") != "alpha.runtime-capture-session/v1"
                    or type(self.journal.get("metadata_complete")) is not bool
                    or type(self.journal.get("published")) is not bool
                    or (
                        rebind_binding
                        != session_identity_binding(
                            identity,
                            allow_process_rebind=self.allow_process_rebind,
                        )
                        and not relaxed_resume
                    )):
                    raise AcquisitionError("stale process, mixed executable, or changed implementation")
                if (
                    self.allow_process_rebind
                    and isinstance(recorded_identity, dict)
                    and recorded_identity != identity
                    and session_identity_binding(
                        recorded_identity,
                        allow_process_rebind=True,
                    )
                    == session_identity_binding(
                        identity, allow_process_rebind=True
                    )
                ):


                    rebinds = self.journal.setdefault("process_rebinds", [])
                    if not isinstance(rebinds, list):
                        raise AcquisitionError(
                            "capture journal process rebind record is invalid"
                        )
                    rebound_ns = time.time_ns()
                    rebinds.append(
                        {
                            "explicit": True,
                            "previous_process_id": recorded_identity.get(
                                "process_id"
                            ),
                            "previous_creation_filetime": recorded_identity.get(
                                "creation_filetime"
                            ),
                            "process_id": identity.get("process_id"),
                            "creation_filetime": identity.get(
                                "creation_filetime"
                            ),
                            "executable_sha256": identity.get(
                                "executable_sha256"
                            ),
                            "rebound_ns": rebound_ns,
                        }
                    )


                    if self.salvage_restart:
                        self._salvage_rebind(identity)
                    else:
                        self._invalidate_rebound_stages()
                    self.journal["identity"] = identity
                    self._save()
                if self.allow_process_rebind and not self.salvage_restart:


                    self._invalidate_rebound_stages()
                elif self.salvage_restart:
                    self._salvage_rebind(identity)
                stages = self.journal.get("stages")
                if not isinstance(stages, dict) or any(
                    not re.fullmatch(r"[a-z][a-z0-9-]*", name)
                    or not isinstance(stage, dict)
                    or not isinstance(stage.get("dependencies"), list)
                    or any(dep not in stages or dep == name for dep in stage["dependencies"])
                    for name, stage in stages.items()
                ):
                    raise AcquisitionError("capture journal stage graph is invalid")
                implementation_changed = (
                    not relaxed_resume and self._implementation_changed()
                )
                incomplete = [
                    name for name, stage in stages.items()
                    if stage.get("status") != "complete"
                ]
                if implementation_changed or incomplete:
                    if not self.repair_resume:
                        if implementation_changed:
                            raise AcquisitionError(
                                "stale process, mixed executable, or changed implementation"
                            )
                        raise AcquisitionError(
                            "incomplete capture stage preserved; use repair resume or a new session"
                        )
                    if implementation_changed and not self.carry_forward:


                        self._repair_implementation_swap()
                    elif incomplete:
                        if self.carry_forward:
                            for name, stage in stages.items():
                                if stage.get("status") == "complete":
                                    self._verify_stage_contract(name)
                        if (
                            self.allow_process_rebind
                            and all(
                                stages[name].get("status")
                                in (
                                    "rebound-recapture-required",
                                    "failed",
                                    "running",
                                )
                                for name in incomplete
                            )
                            and self.journal.get("published") is False
                            and self.journal.get("metadata_complete") is False
                        ):


                            self._repair_rebind_recapture(incomplete)
                        else:
                            self._repair_resume(incomplete)
                    else:
                        self._adopt_implementation_carry_forward()
                self._verify_completed_stages()
            else:
                if self.carry_forward:
                    raise AcquisitionError(
                        "carry-forward requires the original session journal"
                    )


                if any(p.name not in (".session.lock", ".memo-cache")
                       for p in self.root.iterdir()):
                    raise AcquisitionError("new capture session directory is not empty")
                self.journal = {"schema": "alpha.runtime-capture-session/v1",
                                "identity": identity, "implementation": self.implementation,
                                "implementation_revalidation_required": self.implementation_probe is not None,
                                "created_ns": time.time_ns(), "stages": {},
                                "metadata_complete": False, "published": False}
                self._save()
            self._assert_implementation()
            return self
        except BaseException:
            self.__exit__(None, None, None)
            raise

    def __exit__(self, *_: object) -> None:
        self._stop_probe_refresh()
        if self.lock_fd is not None:
            os.close(self.lock_fd)
            self.lock_fd = None

    def _save(self) -> None:
        _private_json(self.root / "session.private.json", self.journal)

    def _invalidate_rebound_stages(self) -> list[str]:
        stages = self.journal.get("stages") or {}
        rebinds = [
            record.get("rebound_ns")
            for record in self.journal.get("process_rebinds", [])
            if isinstance(record, dict)
            and isinstance(record.get("rebound_ns"), int)
        ]
        if not rebinds:
            return []
        last_rebound = max(rebinds)


        invalidated: list[str] = sorted(
            name
            for name, stage in stages.items()
            if isinstance(stage, dict)
            and stage.get("status") == "rebound-recapture-required"
        )
        changed = True
        while changed:
            changed = False
            for name, stage in sorted(stages.items()):
                if not isinstance(stage, dict) or stage.get("status") != "complete":
                    continue
                finished = stage.get("finished_ns")
                captured_before = (
                    isinstance(finished, int) and finished < last_rebound
                )
                dependent = any(
                    dependency in invalidated
                    for dependency in (stage.get("dependencies") or [])
                )
                if captured_before or dependent:
                    stage["status"] = "rebound-recapture-required"
                    invalidated.append(name)
                    changed = True
        if invalidated:
            record = self.journal.setdefault("rebind_invalidations", [])
            if not isinstance(record, list):
                raise AcquisitionError(
                    "capture journal rebind invalidation record is invalid"
                )
            record.append(
                {
                    "rebound_ns": last_rebound,
                    "stages": sorted(invalidated),
                    "replayed": True,
                }
            )
            self._save()
        return sorted(invalidated)

    def _implementation_changed(self) -> bool:


        return (
            self.journal.get("implementation") != self.implementation
            or self.journal.get("implementation_revalidation_required", False)
            is not (self.implementation_probe is not None)
        )

    def _salvage_keep_set(
        self, stages: dict[str, Any], rebound_ns: int,
        force_recapture: frozenset = frozenset(),
    ) -> tuple[set[str], dict[str, str]]:
        from alpha.stage_catalog import salvage_eligible_stages
        eligible = salvage_eligible_stages()

        def prebound(name: str, stage: Any) -> bool:
            return (
                isinstance(stage, dict)
                and stage.get("status") == "complete"
                and isinstance(stage.get("finished_ns"), int)
                and stage["finished_ns"] < rebound_ns
            )

        def target_free(stage: dict[str, Any]) -> bool:
            target = (stage.get("result") or {}).get("target")
            if not isinstance(target, dict):
                return True
            return not any(
                key in ("process_id", "creation_filetime")
                or "image_base" in key
                for key in target.keys()
            )

        def eligible_reason(name: str, stage: dict[str, Any]) -> str | None:
            if name not in eligible:
                from alpha.stage_catalog import salvage_recapture_reason
                return salvage_recapture_reason(name)
            if not target_free(stage):
                return "sealed result target binds the old process lifetime"
            return None

        blocked: dict[str, str] = {}
        for name, stage in sorted(stages.items()):
            if not prebound(name, stage):
                continue
            if name in force_recapture:
                blocked[name] = (
                    "sealed evidence revalidation failed under the new lifetime"
                )
                continue
            reason = eligible_reason(name, stage)
            if reason is not None:
                blocked[name] = reason


        changed = True
        while changed:
            changed = False
            for name, stage in sorted(stages.items()):
                if not prebound(name, stage) or name in blocked:
                    continue
                for dependency in stage.get("dependencies") or []:
                    if dependency in blocked:
                        blocked[name] = (
                            "dependency is recaptured under the new "
                            f"lifetime: {dependency}"
                        )
                        changed = True
                        break
        keep = {
            name
            for name, stage in stages.items()
            if prebound(name, stage) and name not in blocked
        }
        reasons = {
            name: (
                "carried: audited restart-invariant, lifetime-free target, "
                "carried-or-fresh dependencies"
                if name in keep else blocked[name]
            )
            for name, stage in sorted(stages.items())
            if prebound(name, stage)
        }
        return keep, reasons

    def _salvage_rebind(self, identity: dict[str, Any]) -> None:
        if self._implementation_changed():
            raise AcquisitionError(
                "salvage restart requires unchanged implementation "
                f"(journal ver {self.journal.get('implementation')!r} "
                f"!= current ver {self.implementation!r}); refusing to mix "
                "code versions across a restart -- re-run with "
                "--carry-forward to adopt a changed implementation "
                "deliberately"
            )
        rebinds = [
            record.get("rebound_ns")
            for record in self.journal.get("process_rebinds", [])
            if isinstance(record, dict)
            and isinstance(record.get("rebound_ns"), int)
        ]
        if not rebinds:
            return
        last_rebound = max(rebinds)
        for entry in self.journal.get("salvage_resumes", []):
            if isinstance(entry, dict) and entry.get("rebound_ns") == last_rebound:
                return
        stages = self.journal.get("stages") or {}


        forced: set[str] = set()
        reasons: dict[str, str] = {}
        demotion_reasons: dict[str, str] = {}
        while True:
            keep, reasons = self._salvage_keep_set(
                stages, last_rebound, force_recapture=frozenset(forced),
            )
            demoted: dict[str, str] = {}
            for name in sorted(keep):
                try:
                    self._verify_stage(name)
                    self._verify_stage_contract(name)
                except AcquisitionError as error:
                    demoted[name] = (
                        "sealed evidence revalidation failed under the new "
                        f"lifetime: {error}"
                    )
            if not demoted:
                break
            forced.update(demoted)
            demotion_reasons.update(demoted)
        reasons.update(demotion_reasons)
        for name in sorted(keep):
            stage = stages[name]
            stage["salvaged_from_rebound_ns"] = last_rebound
            stage["salvaged_previous_finished_ns"] = stage.get("finished_ns")
            stage["finished_ns"] = last_rebound
        self._invalidate_rebound_stages()
        for name in sorted(keep):
            if stages[name].get("status") != "complete":
                raise AcquisitionError(
                    f"salvage keep-set inconsistent after invalidation: {name}"
                )
        record = self.journal.setdefault("salvage_resumes", [])
        if not isinstance(record, list):
            raise AcquisitionError(
                "capture journal salvage resume record is invalid"
            )
        record.append(
            {
                "salvaged_ns": time.time_ns(),
                "rebound_ns": last_rebound,
                "recovery_kind": "explicit-salvage-restart",
                "implementation": self.implementation,
                "executable_sha256": identity.get("executable_sha256"),
                "previous_image_base": (
                    self.journal.get("identity") or {}
                ).get("image_base"),
                "image_base": identity.get("image_base"),
                "previous_process_id": (
                    self.journal.get("identity") or {}
                ).get("process_id"),
                "process_id": identity.get("process_id"),
                "kept_stages": sorted(keep),
                "reasons": reasons,
                "replayed": True,
            }
        )
        self._save()

    def _repair_rebind_recapture(self, incomplete: list[str]) -> None:
        stages = self.journal["stages"]
        archive_root = _safe_path(self.root / "failed-stages")
        archive_root.mkdir(mode=0o700, exist_ok=True)
        archives: list[str] = []
        for name in sorted(incomplete):
            directory = _safe_path(self.root / name)
            if directory.is_dir():
                archive = archive_root / f"{name}-{time.time_ns()}"
                os.replace(directory, archive)
                archives.append(str(archive))
            stages.pop(name, None)
            self._forget_planned_stage(name)
        recaptures = self.journal.setdefault("rebind_recaptures", [])
        if not isinstance(recaptures, list):
            raise AcquisitionError(
                "capture journal rebind recapture record is invalid"
            )
        recaptures.append(
            {
                "recaptured_ns": time.time_ns(),
                "stages": sorted(incomplete),
                "archives": archives,
                "recovery_kind": "explicit-process-rebind-recapture",
            }
        )
        self._save()

    def set_stage_plan(self, group: str, names: tuple[str, ...]) -> None:
        if not re.fullmatch(r"[a-z][a-z0-9-]*", group):
            raise AcquisitionError("invalid capture stage plan group")
        if (not isinstance(names, tuple) or not names
                or any(not isinstance(name, str)
                       or not re.fullmatch(r"[a-z][a-z0-9-]*", name)
                       for name in names)
                or len(set(names)) != len(names)):
            raise AcquisitionError("capture stage plan is invalid")
        plans = self.journal.get("stage_plan")
        if plans is None:
            plans = {}
            self.journal["stage_plan"] = plans
        if not isinstance(plans, dict):
            raise AcquisitionError("capture stage plan journal is invalid")
        current = plans.get(group)
        if current is not None and current != list(names):


            if self.journal.get("stages"):
                raise AcquisitionError("capture stage plan changed")
        plans[group] = list(names)
        self._save()

    def register_planned_stage(self, group: str, name: str) -> None:
        if (not re.fullmatch(r"[a-z][a-z0-9-]*", group)
                or not re.fullmatch(r"[a-z][a-z0-9-]*", name)):
            raise AcquisitionError("invalid capture stage plan entry")
        plans = self.journal.setdefault("stage_discoveries", {})
        if not isinstance(plans, dict):
            raise AcquisitionError("capture stage plan journal is invalid")
        names = plans.setdefault(group, [])
        if not isinstance(names, list) or any(not isinstance(item, str) for item in names):
            raise AcquisitionError("capture stage plan journal is invalid")
        planned = self.journal.get("stage_plan", {})
        planned_names = planned.get(group, []) if isinstance(planned, dict) else []
        if name not in names and name not in planned_names:
            names.append(name)
            self._save()

    def _forget_planned_stage(self, name: str) -> None:
        plans = self.journal.get("stage_discoveries")
        if not isinstance(plans, dict):
            return
        changed = False
        for group in list(plans):
            names = plans.get(group)
            if isinstance(names, list) and name in names:
                plans[group] = [item for item in names if item != name]
                changed = True
        if changed:
            self._save()

    def finalize(self, *, terminal_stage: str, published: bool) -> None:
        if type(published) is not bool:
            raise AcquisitionError("capture publication state is invalid")
        if terminal_stage not in self.journal.get("stages", {}):
            raise AcquisitionError("capture terminal stage is unavailable")


        try:
            from alpha.h02 import clear_file_hash_cache
        except ImportError:
            clear_file_hash_cache = None
        if clear_file_hash_cache is not None:
            clear_file_hash_cache()
        self._stop_probe_refresh()
        self._probe_cache = None
        try:
            self._verified_stages.clear()
        except AttributeError:
            self._verified_stages = {}
        self.assert_current()


        self._read_stage_artifacts([
            name for name, stage in self.journal["stages"].items()
            if stage.get("status") == "complete"
        ])
        for name in self.journal["stages"]:
            self._verify_stage(name)
        terminal = self.journal["stages"][terminal_stage]
        if terminal.get("status") != "complete":
            raise AcquisitionError("capture terminal stage is incomplete")
        result = terminal.get("result")
        if not isinstance(result, dict) or result.get("status") != "complete":
            raise AcquisitionError("capture terminal stage result is incomplete")
        self.assert_current()
        self.journal["metadata_complete"] = True
        self.journal["published"] = published
        self.journal["terminal_stage"] = terminal_stage
        self.journal["completed_ns"] = time.time_ns()
        self._save()

    def _repair_resume(self, incomplete: list[str]) -> None:

        stages = self.journal["stages"]
        repairable_statuses = {"failed", "running"}
        if (
            len(incomplete) != 1
            or stages[incomplete[0]].get("status") not in repairable_statuses
            or self.journal.get("published") is not False
            or self.journal.get("metadata_complete") is not False
        ):
            raise AcquisitionError(
                "repair resume requires one failed or interrupted unpublished stage"
            )
        failed = incomplete[0]
        if any(
            failed in stage.get("dependencies", [])
            for name, stage in stages.items()
            if name != failed and stage.get("status") == "complete"
        ):
            raise AcquisitionError("repair resume failed stage has completed consumers")
        for name, stage in stages.items():
            if name != failed:
                if stage.get("status") != "complete":
                    raise AcquisitionError("repair resume stage graph is not a single failed leaf")
                self._verify_stage(name)
        failed_dir = _safe_path(self.root / failed)
        if not failed_dir.is_dir():
            raise AcquisitionError("repair resume failed stage directory is unavailable")
        archive_root = _safe_path(self.root / "failed-stages")
        archive_root.mkdir(mode=0o700, exist_ok=True)
        if False or not owner_only_mode_ok(
            archive_root.stat(), 0o700
        ):
            raise AcquisitionError("repair resume archive is not owner-only")
        archive_name = f"{failed}-{time.time_ns()}"
        archive = archive_root / archive_name
        os.replace(failed_dir, archive)
        previous_implementation = self.journal.get("implementation")
        failure = stages.pop(failed)
        self._forget_planned_stage(failed)
        if self.carry_forward:
            self.journal.setdefault("carry_forward_resumes", []).append({
                "adopted_ns": time.time_ns(),
                "recovery_kind": "explicit-implementation-carry-forward",
                "previous_implementation": previous_implementation,
                "replacement_implementation": self.implementation,
                "interrupted_stage": failed,
                "completed_stage_count": len(stages),
                "completed_stage_implementations": {
                    name: stage.get("implementation")
                    for name, stage in stages.items()
                    if stage.get("status") == "complete"
                },
                "completed_artifacts_rehashed": True,
                "completed_stage_results_revalidated": True,
                "same_process_identity_required": True,
            })
        self.journal.setdefault("repair_resumes", []).append({
            "repaired_ns": time.time_ns(),
            "failed_stage": failed,
            "failed_stage_archive": str(archive),
            "failure": failure,
            "recovery_kind": (
                "interrupted-running-stage"
                if failure.get("status") == "running"
                else "failed-stage"
            ),
            "previous_implementation": previous_implementation,
            "replacement_implementation": self.implementation,
            "completed_artifacts_rehashed": True,
            "implementation_carry_forward": self.carry_forward,
            "completed_stage_results_revalidated": self.carry_forward,
            "same_process_identity_required": True,
        })
        self.journal["implementation"] = self.implementation
        self.journal["implementation_revalidation_required"] = (
            self.implementation_probe is not None
        )
        self._save()

    def _archive_failed_attempt(
        self, name: str, error: AcquisitionError
    ) -> None:
        stages = self.journal["stages"]
        stage = stages.get(name)
        if not isinstance(stage, dict) or stage.get("status") != "failed":
            return
        if any(
            name in candidate.get("dependencies", [])
            and candidate.get("status") == "complete"
            for candidate_name, candidate in stages.items()
            if candidate_name != name
        ):
            raise AcquisitionError(
                f"cannot retry failed stage with completed consumers: {name}"
            )
        directory = _safe_path(self.root / name)
        archive_root = _safe_path(self.root / "failed-stages")
        archive_root.mkdir(mode=0o700, exist_ok=True)
        if False or not owner_only_mode_ok(archive_root.stat(), 0o700):
            raise AcquisitionError("stage retry archive is not owner-only")
        archive = archive_root / f"{name}-attempt-{time.time_ns()}"
        if directory.exists() or directory.is_symlink():
            if directory.is_symlink() or not directory.is_dir():
                raise AcquisitionError(
                    f"stage retry archive source is invalid: {name}"
                )
            os.replace(directory, archive)
        failure = dict(stage)
        stages.pop(name, None)
        self._forget_planned_stage(name)
        self.journal.setdefault("stage_attempts", []).append({
            "attempted_ns": time.time_ns(),
            "stage": name,
            "archive": str(archive),
            "failure": failure,
            "retry_reason": str(error)[:2048],
        })
        self._save()

    def _verify_stage_contract(self, name: str) -> None:
        stage = self.journal["stages"].get(name)
        result = stage.get("result") if isinstance(stage, dict) else None
        if not isinstance(result, dict) or not isinstance(result.get("status"), str):
            raise AcquisitionError(f"capture stage result is invalid: {name}")
        target = result.get("target")
        if isinstance(target, dict):
            executable_sha256 = target.get("executable_sha256")
            if (
                executable_sha256 is not None
                and executable_sha256
                != self.journal["identity"].get("executable_sha256")
            ):
                raise AcquisitionError(
                    f"capture stage executable binding is stale: {name}"
                )
        checks = result.get("checks")
        if result["status"] in {"runtime-validated", "validated", "resolved"}:
            if isinstance(checks, dict) and checks and all(
                value is True for value in checks.values()
            ):
                return


            model_identity = result.get("model")
            if not isinstance(model_identity, dict):
                self._verify_stage_verification_receipt(name, result)
                return
            model_path = Path(str(model_identity.get("path", "")))
            if (not model_path.is_file()
                    or file_identity(model_path) != model_identity):
                raise AcquisitionError(f"capture stage model identity differs: {name}")
            model = read_private_model(model_path)
            counts = model.get("counts")
            if (
                model.get("schema") != result.get("schema")
                or model.get("status") != result["status"]
                or model.get("target") != result.get("target")
                or counts != result.get("counts")
                or not isinstance(counts, dict)
            ):
                raise AcquisitionError(f"capture stage model contract differs: {name}")
            if (
                isinstance(checks, dict)
                and checks
                and model.get("checks") == checks
                and counts.get("required") is None
            ):


                return
            if (
                type(counts.get("required")) is not int
                or counts.get("required") <= 0
                or counts.get("verified") != counts["required"]
                or counts.get("failed", 0) != 0
            ):
                raise AcquisitionError(f"capture stage model contract differs: {name}")
            shards = model.get("shards_owner_only")
            if not isinstance(shards, list) or not shards:
                raise AcquisitionError(f"capture stage shard evidence is absent: {name}")
            for shard in shards:
                if not isinstance(shard, dict):
                    raise AcquisitionError(f"capture stage shard evidence is invalid: {name}")
                shard_path = Path(str(shard.get("path", "")))
                if (not shard_path.is_file()
                        or file_identity(shard_path) != shard):
                    raise AcquisitionError(f"capture stage shard evidence differs: {name}")

    def _verify_stage_verification_receipt(
        self, name: str, result: dict[str, Any]
    ) -> None:
        receipt_identity = result.get("verification")
        if not isinstance(receipt_identity, dict):
            raise AcquisitionError(
                f"capture stage validation checks are not current: {name}"
            )
        receipt_path = Path(str(receipt_identity.get("path", "")))
        if (not receipt_path.is_file()
                or file_identity(receipt_path) != receipt_identity):
            raise AcquisitionError(
                f"capture stage verification receipt changed: {name}"
            )
        receipt = read_private_model(receipt_path)
        if not isinstance(receipt, dict) or receipt.get("status") != result["status"]:
            raise AcquisitionError(
                f"capture stage verification receipt differs: {name}"
            )
        for key, value in result.items():
            if key == "verification" or key not in receipt:
                continue
            if receipt.get(key) != value:
                raise AcquisitionError(
                    "capture stage verification receipt attests a different "
                    f"result: {name}"
                )
        inputs = receipt.get("inputs")
        if not isinstance(inputs, dict) or not inputs:
            raise AcquisitionError(
                f"capture stage verification inputs are absent: {name}"
            )
        for role, record in inputs.items():
            if not isinstance(record, dict) or not isinstance(record.get("path"), str):
                raise AcquisitionError(
                    f"capture stage verification input is invalid: {name}"
                )
            input_path = _safe_path(Path(record["path"]))
            if file_identity(input_path) != record:
                raise AcquisitionError(
                    f"capture stage verification input changed: {name}"
                )

    def _adopt_implementation_carry_forward(self) -> None:
        stages = self.journal["stages"]
        for name in stages:
            self._verify_stage(name)
            self._verify_stage_contract(name)
        previous_implementation = self.journal.get("implementation")
        self.journal.setdefault("carry_forward_resumes", []).append({
            "adopted_ns": time.time_ns(),
            "recovery_kind": "explicit-implementation-carry-forward",
            "previous_implementation": previous_implementation,
            "replacement_implementation": self.implementation,
            "completed_stage_count": len(stages),
            "completed_stage_implementations": {
                name: stage.get("implementation")
                for name, stage in stages.items()
            },
            "completed_artifacts_rehashed": True,
            "completed_stage_results_revalidated": True,
            "same_process_identity_required": True,
        })
        self.journal["implementation"] = self.implementation
        self.journal["implementation_revalidation_required"] = (
            self.implementation_probe is not None
        )
        self._save()

    def _repair_implementation_swap(self) -> None:
        stages = self.journal["stages"]
        for name, stage in stages.items():
            if stage.get("status") == "complete":
                self._verify_stage(name)
        archive_root = _safe_path(self.root / "superseded-stages")
        archive_root.mkdir(mode=0o700, exist_ok=True)
        if False or not owner_only_mode_ok(archive_root.stat(), 0o700):
            raise AcquisitionError(
                "implementation-swap stage archive is not owner-only"
            )
        archive = archive_root / str(time.time_ns())
        archive.mkdir(mode=0o700)
        archived_stages = {}
        for name in sorted(stages):
            source = _safe_path(self.root / name)
            if source.exists() and not source.is_dir():
                raise AcquisitionError(
                    f"implementation-swap stage directory is unavailable: {name}"
                )
            was_directory = source.is_dir()
            if was_directory:
                os.replace(source, archive / name)
            archived_stages[name] = {
                "status": stages[name].get("status"),
                "archived": was_directory,
            }
        previous_implementation = self.journal.get("implementation")
        self.journal.setdefault("repair_resumes", []).append({
            "repaired_ns": time.time_ns(),
            "failed_stage": None,
            "failure": None,
            "recovery_kind": "implementation-swap-full-rebuild",
            "superseded_stage_archive": str(archive),
            "superseded_stage_count": len(stages),
            "superseded_stages": archived_stages,
            "previous_implementation": previous_implementation,
            "replacement_implementation": self.implementation,
            "completed_artifacts_rehashed": True,
            "same_process_identity_required": True,
        })
        self.journal["stages"] = {}
        self.journal["stage_discoveries"] = {}
        self.journal["metadata_complete"] = False
        self.journal["published"] = False
        self.journal["implementation"] = self.implementation
        self.journal["implementation_revalidation_required"] = (
            self.implementation_probe is not None
        )
        self._save()

    def _assert_implementation(self) -> None:
        if self.implementation_probe is not None:
            current = self.implementation_probe()
            if not isinstance(current, str) or current != self.implementation:
                raise AcquisitionError("runtime capture implementation changed during capture")

    def assert_current(self) -> None:
        self._assert_implementation()
        now = time.monotonic()
        with self._probe_cache_lock:
            cached = self._probe_cache
        if (
            cached is not None
            and (now - cached[0]) < self._probe_cache_ttl
            and cached[1] == self.journal.get("identity")
        ):
            self._assert_implementation()
            return
        current = self.probe()
        if current != self.journal["identity"]:
            raise AcquisitionError("runtime process or executable changed during capture")
        with self._probe_cache_lock:
            self._probe_cache = (now, current)
        self._assert_implementation()

    def _keep_probe_warm(self) -> None:
        if self._probe_refresh_thread is not None:
            return
        ttl = self._probe_cache_ttl
        if not isinstance(ttl, (int, float)) or ttl <= 0:
            return
        interval = max(0.05, ttl / 2.0)
        stop = threading.Event()

        def refresh() -> None:
            while not stop.wait(interval):
                try:
                    observed = self.probe()
                except BaseException:


                    continue
                with self._probe_cache_lock:
                    self._probe_cache = (time.monotonic(), observed)

        thread = threading.Thread(
            target=refresh, name="alpha-probe-refresh", daemon=True
        )
        self._probe_refresh_stop = stop
        self._probe_refresh_thread = thread
        thread.start()

    def _stop_probe_refresh(self) -> None:
        stop = getattr(self, "_probe_refresh_stop", None)
        thread = getattr(self, "_probe_refresh_thread", None)
        self._probe_refresh_stop = None
        self._probe_refresh_thread = None
        if stop is not None:
            stop.set()
        if thread is not None and thread is not threading.current_thread():
            thread.join(timeout=float(self._probe_cache_ttl) + 30.0)


    _VERIFY_HASH_WORKERS = min(4, max(1, (os.cpu_count() or 4)))

    def _read_stage_artifacts(
        self, names: list[str]
    ) -> tuple[dict[str, list[tuple[str, Path]]], dict[str, Exception],
               dict[str, tuple[tuple[Path, ...], tuple[Any, ...]]],
               dict[Path, Any]]:
        listing: dict[str, list[tuple[str, Path]]] = {}
        failures: dict[str, Exception] = {}
        identities: dict[str, tuple[tuple[Path, ...], tuple[Any, ...]]] = {}
        sizes: dict[Path, int] = {}
        for name in names:
            try:
                entries, directories = _artifact_listing(self.root / name)
            except Exception as error:
                failures[name] = error
                continue
            listing[name] = entries


            watched = _watched_artifact_paths(entries, directories)
            identity = _artifact_identity(watched)
            identities[name] = (watched, identity)


            measured = dict(identity)
            for _key, target in entries:
                if target in sizes:
                    continue
                fingerprint = measured.get(target)
                sizes[target] = -1 if fingerprint is None else fingerprint[2]
        outcomes: dict[Path, Any] = {}
        if sizes:
            ordered = [
                path for path, _size in sorted(
                    sizes.items(), key=lambda item: item[1], reverse=True
                )
            ]

            def read(target: Path) -> Any:
                try:
                    return _file_record(target)
                except Exception as error:
                    return error

            with ThreadPoolExecutor(
                max_workers=min(self._VERIFY_HASH_WORKERS, len(ordered))
            ) as executor:
                for target, outcome in zip(ordered, executor.map(read, ordered)):
                    outcomes[target] = outcome
        return listing, failures, identities, outcomes

    def _stage_verification_still_valid(self, name: str) -> bool:
        try:
            entry = self._verified_stages.get(name)
        except AttributeError:
            return False
        if not isinstance(entry, tuple) or len(entry) != 3:


            return False
        stage = self.journal["stages"].get(name)
        if not stage or not stage.get("artifacts"):
            return False
        journal_bytes, watched, identity = entry
        if journal_bytes != canonical_json_bytes(stage):
            return False
        return _artifact_identity(watched) == identity

    def _remember_stage_verification(
        self, name: str, stage: dict[str, Any],
        watched: tuple[Path, ...], identity: tuple[Any, ...],
    ) -> None:
        try:
            verified = self._verified_stages
        except AttributeError:
            verified = self._verified_stages = {}
        verified[name] = (canonical_json_bytes(stage), watched, identity)

    def _verify_completed_stages(self) -> None:
        stages = self.journal["stages"]
        try:
            self._verified_stages
        except AttributeError:
            self._verified_stages = {}
        pending = [
            name for name, stage in stages.items()
            if stage.get("status") == "complete"
            and not self._stage_verification_still_valid(name)
        ]
        if not pending:
            return
        listing, failures, identities, outcomes = self._read_stage_artifacts(pending)
        for name in pending:
            failure = failures.get(name)
            if failure is not None:
                raise failure
            stage = stages.get(name)
            if not stage or stage.get("status") != "complete" or not stage.get("artifacts"):
                raise AcquisitionError(f"capture dependency incomplete: {name}")
            records = {}
            for key, target in listing[name]:
                outcome = outcomes.get(target, None)
                if isinstance(outcome, Exception):
                    raise outcome
                records[key] = outcome
            if records != stage["artifacts"]:
                raise AcquisitionError(f"capture stage artifact changed: {name}")
            watched, identity = identities[name]
            self._remember_stage_verification(name, stage, watched, identity)

    def _verify_stage(self, name: str) -> None:


        if self._stage_verification_still_valid(name):
            return
        self._verify_stage_uncached(name)

    def _verify_stage_uncached(self, name: str) -> None:
        stage = self.journal["stages"].get(name)
        if not stage or stage.get("status") != "complete" or not stage.get("artifacts"):
            raise AcquisitionError(f"capture dependency incomplete: {name}")
        directory = self.root / name
        listing, directories = _artifact_listing(directory)


        watched = _watched_artifact_paths(listing, directories)
        identity = _artifact_identity(watched)
        actual = {key: _file_record(target) for key, target in listing}
        if actual != stage["artifacts"]:
            raise AcquisitionError(f"capture stage artifact changed: {name}")
        self._remember_stage_verification(name, stage, watched, identity)

    def _repair_changed_dependencies(self, name: str, dependencies: tuple[str, ...]) -> None:
        if not (self.resume and self.repair_resume and self.carry_forward):
            raise AcquisitionError("capture dependency graph changed")
        stages = self.journal["stages"]
        affected = {name}
        while True:
            consumers = {
                candidate_name for candidate_name, candidate in stages.items()
                if candidate_name not in affected
                and any(dep in affected for dep in candidate.get("dependencies", []))
            }
            if not consumers:
                break
            affected.update(consumers)
        for candidate_name in affected:
            if stages[candidate_name].get("status") != "complete":
                raise AcquisitionError(
                    f"cannot repair changed dependencies with incomplete consumer: {candidate_name}"
                )
            self._verify_stage(candidate_name)
        archive_root = _safe_path(self.root / "superseded-stages")
        archive_root.mkdir(mode=0o700, exist_ok=True)
        if False or not owner_only_mode_ok(archive_root.stat(), 0o700):
            raise AcquisitionError("dependency repair archive is not owner-only")
        archive = archive_root / str(time.time_ns())
        archive.mkdir(mode=0o700)
        previous = {}
        for candidate_name in sorted(affected):
            source = _safe_path(self.root / candidate_name)
            os.replace(source, archive / candidate_name)
            previous[candidate_name] = stages.pop(candidate_name)
            self._forget_planned_stage(candidate_name)
        self.journal.setdefault("repair_resumes", []).append({
            "repaired_ns": time.time_ns(),
            "recovery_kind": "changed-dependencies-carry-forward",
            "changed_stage": name,
            "previous_dependencies": previous[name]["dependencies"],
            "replacement_dependencies": list(dependencies),
            "superseded_stage_archive": str(archive),
            "superseded_stages": sorted(affected),
            "completed_artifacts_rehashed": True,
            "same_process_identity_required": True,
        })
        self.journal["metadata_complete"] = False
        self.journal["published"] = False
        self._save()

    def run(self, name: str, callback: Callable[[Path], dict[str, Any]], *,
            dependencies: tuple[str, ...] = (),
            accepted_statuses: tuple[str, ...] = ("complete", "validated", "discovered"),
            validate: Callable[[dict[str, Any]], bool] | None = None) -> dict[str, Any]:
        for attempt in range(2):
            try:
                return self._run_once(
                    name, callback, dependencies=dependencies,
                    accepted_statuses=accepted_statuses, validate=validate,
                )
            except (AcquisitionError, subprocess.TimeoutExpired) as error:
                if isinstance(error, subprocess.TimeoutExpired):


                    error = AcquisitionError(f"stage child timed out: {error}")
                    transient = True
                else:
                    text = str(error)
                    transient = any(
                        marker in text
                        for marker in (
                            "timed out", "capture failed", "probe failed",
                            "did not confirm the target instance",


                            "validation failed",
                        )
                    )
                if attempt or not transient:
                    raise error
                self._archive_failed_attempt(name, error)
                time.sleep(5.0)
        raise AcquisitionError("capture stage retry exhausted")

    def _run_once(self, name: str, callback: Callable[[Path], dict[str, Any]], *,
            dependencies: tuple[str, ...] = (),
            accepted_statuses: tuple[str, ...] = ("complete", "validated", "discovered"),
            validate: Callable[[dict[str, Any]], bool] | None = None) -> dict[str, Any]:
        if not re.fullmatch(r"[a-z][a-z0-9-]*", name) or name in dependencies:
            raise AcquisitionError("invalid capture stage name or self dependency")
        self.assert_current()
        for dependency in dependencies:
            self._verify_stage(dependency)
        if name in self.journal["stages"]:
            stage = self.journal["stages"][name]
            if stage.get("dependencies") != list(dependencies):
                self._repair_changed_dependencies(name, dependencies)
            else:


                self._keep_probe_warm()
                self._verify_stage(name)
                result = stage["result"]
                if result.get("status") not in accepted_statuses or (validate and not validate(result)):
                    raise AcquisitionError("resumed stage no longer satisfies its contract")
                self.assert_current()
                return result
        directory = self.root / name
        if directory.exists():
            raise AcquisitionError("uncommitted stage directory preserved; use a new session")
        directory.mkdir(mode=0o700)


        self._stop_probe_refresh()
        started = time.time_ns()
        stage = {"status": "running", "started_ns": started,
                 "dependencies": list(dependencies)}
        self.journal["stages"][name] = stage
        self._save()
        try:
            with bind_runtime_process(self.journal["identity"]):
                result = callback(directory)
            self.assert_current()
            for dependency in dependencies:
                self._verify_stage(dependency)
            if (not isinstance(result, dict) or result.get("status") not in accepted_statuses
                or (validate is not None and not validate(result))):
                raise AcquisitionError(f"capture stage contract rejected: {name}")


            for path in directory.rglob("*"):
                _safe_path(path)
                if path.is_file() and path.stat().st_uid == owner_uid():
                    path.chmod(0o600)
            artifacts = _artifacts(directory)
            if not artifacts:
                raise AcquisitionError("capture stage produced no artifacts")
            self._assert_implementation()
            stage.update(status="complete", finished_ns=time.time_ns(),
                         artifacts=artifacts, result=result,
                         implementation=self.implementation)
            self._save()
            return result
        except BaseException as error:
            stage.update(status="failed", error_type=type(error).__name__,
                         error_diagnostic=_failure_details(error), finished_ns=time.time_ns())
            self._save()
            raise


import struct
from pathlib import Path
from typing import Any

from alpha.h01 import AcquisitionError
from alpha.h04 import MemorySnapshot
from alpha.h02 import file_identity


def _operation(semantics: dict[str, Any], key: str) -> dict[str, Any]:
    rows = [
        row
        for row in semantics.get("operations", [])
        if isinstance(row, dict)
        and row.get("key") == key
        and row.get("semantic_identity_resolved") is True
        and isinstance(row.get("method_pointer"), int)
        and row["method_pointer"] > 0
        and isinstance(row.get("metadata_pointer"), int)
        and row["metadata_pointer"] > 0
    ]
    if len(rows) != 1:
        raise AcquisitionError(
            f"runtime concrete method semantic is unavailable: {key}"
        )
    return rows[0]


def _method_rows(
    class_model: dict[str, Any], runtime_owner: str
) -> list[dict[str, Any]]:
    rows = [
        row
        for row in class_model.get("methods", [])
        if isinstance(row, dict)
        and row.get("runtime_owner") == runtime_owner
        and isinstance(row.get("method_pointer"), int)
        and isinstance(row.get("metadata_pointer"), int)
        and isinstance(row.get("method_index"), int)
    ]
    if not rows:
        raise AcquisitionError(
            "runtime concrete method owner is unavailable: " + runtime_owner
        )
    return rows


def _normalized_direct_body(
    snapshot: MemorySnapshot,
    pointer: int,
    *,
    byte_count: int,
) -> bytes:
    if not 0 < byte_count <= 1_048_576:
        raise AcquisitionError("runtime concrete method body exceeds analysis bounds")
    raw = snapshot.read(pointer, byte_count)
    if raw is None:
        raise AcquisitionError("runtime concrete method body is unavailable")
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
    except ImportError as error:
        raise AcquisitionError(
            "runtime concrete method normalization requires capstone"
        ) from error
    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    body = bytearray(raw)
    for instruction in decoder.disasm(raw, 0):
        if instruction.size == 5 and instruction.bytes[:1] in (b"\xe8", b"\xe9"):
            cursor = instruction.address
            body[cursor + 1 : cursor + 5] = b"\0\0\0\0"
    return bytes(body)


def _word_zero_extend_count(body: bytes) -> int:
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_MEM, X86_OP_REG
    except ImportError as error:
        raise AcquisitionError(
            "runtime concrete method classification requires capstone"
        ) from error
    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    decoder.detail = True
    return sum(
        instruction.mnemonic == "movzx"
        and len(instruction.operands) == 2
        and instruction.operands[0].type == X86_OP_REG
        and instruction.operands[1].type == X86_OP_MEM
        and instruction.operands[1].size == 2
        for instruction in decoder.disasm(body, 0)
    )


def _layout(
    snapshot: MemorySnapshot,
    row: dict[str, Any],
    arity_offset: int,
) -> dict[str, int]:


    if arity_offset < 6:
        raise AcquisitionError("runtime concrete method arity offset is invalid")
    raw = snapshot.read(row["metadata_pointer"] + arity_offset - 6, 7)
    if raw is None:
        raise AcquisitionError("runtime concrete method layout is unavailable")
    slot, impl_attributes, attributes, arity = struct.unpack("<HHHB", raw)
    return {
        "slot": slot,
        "impl_attributes": impl_attributes,
        "attributes": attributes,
        "arity": arity,
    }


def _method_code_shape(
    snapshot: MemorySnapshot, image: Any, pointer: int
) -> tuple[tuple[Any, ...], ...] | None:
    rva = pointer - snapshot.image_base
    if not 0 <= rva < image.size_of_image or not image.executable_rva(rva):
        return None
    function = image.containing_function(rva)
    byte_count = (
        function.end_rva - rva
        if function is not None
        else min(512, image.size_of_image - rva)
    )
    if not 0 < byte_count <= 1_048_576:
        return None
    raw = snapshot.read(pointer, byte_count)
    if raw is None and function is None:
        for smaller in (256, 128, 64, 32, 16):
            if smaller < byte_count:
                raw = snapshot.read(pointer, smaller)
                if raw is not None:
                    break
    if raw is None:
        return None
    try:
        from capstone import Cs, CS_ARCH_X86, CS_MODE_64
        from capstone.x86 import X86_OP_IMM, X86_OP_MEM
    except ImportError as error:
        raise AcquisitionError(
            "runtime concrete method matching requires capstone"
        ) from error
    decoder = Cs(CS_ARCH_X86, CS_MODE_64)
    decoder.detail = True
    shape: list[tuple[Any, ...]] = []
    terminated = False
    for instruction in decoder.disasm(raw, pointer):
        operands = []
        for operand in instruction.operands:
            value = None
            if operand.type == X86_OP_MEM:
                base = decoder.reg_name(operand.mem.base)
                if base not in ("rip", "eip"):
                    value = operand.mem.disp
            elif operand.type == X86_OP_IMM and not (
                instruction.mnemonic == "call"
                or instruction.mnemonic.startswith("j")
            ):
                if -4096 <= operand.imm <= 4096:
                    value = operand.imm
            operands.append((operand.type, operand.size, value))
        shape.append((instruction.mnemonic, tuple(operands)))
        if function is None and instruction.mnemonic in ("ret", "int3", "ud2"):
            terminated = True
            break
    if not shape or (function is None and not terminated):
        return None
    return tuple(shape)


def derive_concrete_method_operations(
    *,
    semantics: dict[str, Any],
    class_model: dict[str, Any],
    snapshot_path: Path,
    arity_offset: int,
    expected_executable_sha256: str,
    binary: Path,
) -> dict[str, Any]:


    class_checks = class_model.get("checks", {})
    required_class_checks = (
        "all_contract_owner_classes_present",
        "all_observed_contract_owners_enumerated",
        "declaring_class_field_unique",
        "method_layout_semantically_unique",
        "method_pointer_field_unique",
        "owner_root_contract_exact",
        "snapshot_image_binding_matches",
        "vtable_boundary_derived",
    )
    if class_model.get("status") != "discovered" or any(
        class_checks.get(key) is not True for key in required_class_checks
    ):
        raise AcquisitionError("runtime concrete method class model is stale")
    snapshot_record = class_model.get("snapshot")
    snapshot_path = snapshot_path.expanduser().resolve()
    if (
        not isinstance(snapshot_record, dict)
        or snapshot_record.get("sha256") != file_identity(snapshot_path)["sha256"]
    ):
        raise AcquisitionError("runtime concrete method snapshot binding differs")
    if semantics.get("binary", {}).get("sha256") != expected_executable_sha256:
        raise AcquisitionError("runtime concrete method target binding differs")
    binary = binary.expanduser().resolve()
    if file_identity(binary)["sha256"] != expected_executable_sha256:
        raise AcquisitionError("runtime concrete method binary binding differs")

    method_parameters = _operation(semantics, "method.parameters")
    method_attributes = _operation(semantics, "method.attributes")
    mono_methods = _method_rows(class_model, "System.Reflection.MonoMethod")
    constructors = _method_rows(class_model, "System.Reflection.MonoCMethod")
    all_pointers = sorted(
        {
            int(row["method_pointer"])
            for row in class_model.get("methods", [])
            if isinstance(row, dict) and int(row.get("method_pointer", 0)) > 0
        }
    )

    from alpha.c04 import MappedPE

    with MemorySnapshot(snapshot_path) as snapshot, MappedPE(binary) as image:
        method_layout = {
            row["metadata_pointer"]: _layout(snapshot, row, arity_offset)
            for row in mono_methods
        }
        constructor_layout = {
            row["metadata_pointer"]: _layout(snapshot, row, arity_offset)
            for row in constructors
        }
        counterpart_evidence: dict[str, dict[str, Any]] = {}

        def counterpart(source: dict[str, Any], *, key: str) -> dict[str, Any]:
            source_layout = method_layout[source["metadata_pointer"]]
            matches = [
                row
                for row in constructors
                if row["method_pointer"] > 0
                and constructor_layout[row["metadata_pointer"]]["slot"]
                == source_layout["slot"]
                and constructor_layout[row["metadata_pointer"]]["arity"]
                == source_layout["arity"]
            ]
            if not matches:
                raise AcquisitionError(
                    f"runtime concrete method sibling is unavailable: {key}"
                )
            if len(matches) == 1:
                chosen = matches[0]
                counterpart_evidence[key] = {
                    "candidate_count": 1,
                    "selection": "unique-current-slot-and-arity",
                    "selected_method_index_owner_only": chosen["method_index"],
                }
                return chosen
            source_shape = _method_code_shape(
                snapshot, image, source["method_pointer"]
            )
            candidate_shapes = [
                _method_code_shape(snapshot, image, row["method_pointer"])
                for row in matches
            ]
            if source_shape is None or any(
                shape is None for shape in candidate_shapes
            ):
                raise AcquisitionError(
                    f"runtime concrete method sibling code evidence is unavailable: {key}"
                )
            ranked = [
                (
                    SequenceMatcher(
                        None, source_shape, shape, autojunk=False
                    ).ratio(),
                    row,
                )
                for row, shape in zip(matches, candidate_shapes)
                if shape is not None
            ]
            ranked.sort(key=lambda item: item[0], reverse=True)
            best_score, chosen = ranked[0]
            next_score = ranked[1][0]
            if best_score < 0.3 or best_score - next_score < 0.05:
                raise AcquisitionError(
                    f"runtime concrete method sibling is ambiguous after code matching: {key}"
                )
            counterpart_evidence[key] = {
                "candidate_count": len(matches),
                "selection": "current-runtime-instruction-shape",
                "selected_method_index_owner_only": chosen["method_index"],
                "shape_similarity": round(best_score, 6),
                "runner_up_similarity": round(next_score, 6),
            }
            return chosen

        constructor_parameters = counterpart(
            method_parameters, key="constructor.parameters"
        )
        constructor_attributes = counterpart(
            method_attributes, key="constructor.attributes"
        )

        attribute_slot = method_layout[
            method_attributes["metadata_pointer"]
        ]["slot"]
        parameter_slot = method_layout[
            method_parameters["metadata_pointer"]
        ]["slot"]
        impl_pairs: list[tuple[dict[str, Any], dict[str, Any], bytes]] = []
        constructors_by_slot: dict[int, list[dict[str, Any]]] = {}
        for row in constructors:
            if (
                row["method_pointer"] > 0
                and constructor_layout[row["metadata_pointer"]]["arity"] == 0
            ):
                slot = constructor_layout[row["metadata_pointer"]]["slot"]
                constructors_by_slot.setdefault(slot, []).append(row)
        for row in mono_methods:
            if row["method_pointer"] <= 0:
                continue
            layout = method_layout[row["metadata_pointer"]]
            if (
                layout["arity"] != 0
                or layout["slot"] == 0xFFFF
                or row["metadata_pointer"] in (
                    method_attributes["metadata_pointer"],
                    method_parameters["metadata_pointer"],
                )
            ):
                continue
            for sibling in constructors_by_slot.get(layout["slot"], ()):
                left_boundary = next(
                    (value for value in all_pointers if value > row["method_pointer"]),
                    None,
                )
                right_boundary = next(
                    (value for value in all_pointers if value > sibling["method_pointer"]),
                    None,
                )
                left_rva = row["method_pointer"] - snapshot.image_base
                right_rva = sibling["method_pointer"] - snapshot.image_base
                if (
                    not 0 <= left_rva < image.size_of_image
                    or not 0 <= right_rva < image.size_of_image
                    or not image.executable_rva(left_rva)
                    or not image.executable_rva(right_rva)
                ):
                    raise AcquisitionError("runtime concrete method is outside image code")
                left_function = image.containing_function(left_rva)
                right_function = image.containing_function(right_rva)
                if left_function is None or right_function is None:
                    continue
                if (
                    left_boundary is not None
                    and left_boundary < snapshot.image_base + left_function.end_rva
                ) or (
                    right_boundary is not None
                    and right_boundary < snapshot.image_base + right_function.end_rva
                ):
                    continue
                left_length = left_function.end_rva - left_rva
                right_length = right_function.end_rva - right_rva
                if left_length != right_length:
                    continue
                left = _normalized_direct_body(
                    snapshot, row["method_pointer"],
                    byte_count=left_length,
                )
                right = _normalized_direct_body(
                    snapshot, sibling["method_pointer"],
                    byte_count=right_length,
                )
                if left == right and _word_zero_extend_count(left) == 1:
                    impl_pairs.append((row, sibling, left))
        if len(impl_pairs) != 1:
            raise AcquisitionError(
                "runtime method implementation-flags sibling is ambiguous "
                f"({len(impl_pairs)} candidates)"
            )
        method_impl, constructor_impl, impl_body = impl_pairs[0]

    class_row_by_metadata = {
        row["metadata_pointer"]: row
        for row in (*mono_methods, *constructors)
    }

    def result(row: dict[str, Any], key: str) -> dict[str, Any]:
        class_row = class_row_by_metadata.get(row["metadata_pointer"], row)
        return {
            "key": key,
            "class_pointer": class_row["class_pointer"],
            "metadata_pointer": row["metadata_pointer"],
            "method_pointer": row["method_pointer"],
            "method_index_owner_only": class_row["method_index"],
            "parameter_count": 0,
            "semantic_identity_resolved": True,
            "derivation": "current-runtime-virtual-slot-and-code-shape",
        }

    operations = {
        "method.parameters": result(method_parameters, "method.parameters"),
        "method.attributes": result(method_attributes, "method.attributes"),
        "method.impl_attributes": result(
            method_impl, "method.impl_attributes"
        ),
        "constructor.parameters": result(
            constructor_parameters, "constructor.parameters"
        ),
        "constructor.attributes": result(
            constructor_attributes, "constructor.attributes"
        ),
        "constructor.impl_attributes": result(
            constructor_impl, "constructor.impl_attributes"
        ),
    }
    return {
        "status": "resolved",
        "operations": operations,
        "evidence": {
            "method_parameter_slot_owner_only": method_layout[
                method_parameters["metadata_pointer"]
            ]["slot"],
            "method_attribute_slot_owner_only": attribute_slot,
            "method_impl_attribute_slot_owner_only": method_layout[
                method_impl["metadata_pointer"]
            ]["slot"],
            "constructor_counterpart_selection": counterpart_evidence,
            "implementation_pair_candidate_count": 1,
            "implementation_body_bytes": len(impl_body),
            "implementation_boundary_source": "pe_exception_directory",
            "implementation_word_load_count": 1,
            "saved_method_name_used": False,
            "saved_method_ordinal_used": False,
            "fixed_rva_used": False,
            "fixed_offset_used": False,
        },
    }
