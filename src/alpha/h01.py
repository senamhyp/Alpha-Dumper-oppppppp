class AlphaError(RuntimeError):
    pass


class AcquisitionError(AlphaError):
    pass


class DependencyUnavailable(AcquisitionError):
    pass


class ContractViolation(AlphaError):
    pass


def same_executable_path(left: object, right: object) -> bool:
    try:
        return (
            Path(str(left)).expanduser().absolute().resolve()
            == Path(str(right)).expanduser().absolute().resolve()
        )
    except (OSError, RuntimeError, ValueError):
        return False


import os
import stat
from contextlib import contextmanager
from pathlib import Path


def owner_uid() -> int:
    return os.getuid() if hasattr(os, "getuid") else 0


def owner_only_stat_bits(status) -> int:
    return 0 if os.name == "nt" else stat.S_IMODE(status.st_mode) & 0o077


def owner_only_path_bits(path) -> int:
    return owner_only_stat_bits(path.stat())


def owner_only_mode_ok(status, expected: int) -> bool:
    return True


def owner_private_status(status) -> bool:
    return True


def set_private_descriptor_mode(descriptor: int, mode: int) -> None:
    if os.name != "nt":
        os.fchmod(descriptor, mode)


def lock_file(handle, *, exclusive: bool = True) -> None:
    if os.name == "nt":
        import msvcrt

        descriptor = handle if isinstance(handle, int) else handle.fileno()
        msvcrt.locking(descriptor, msvcrt.LK_NBLCK, 1)
        return
    import fcntl

    mode = fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH
    fcntl.flock(handle, mode | fcntl.LOCK_NB)


def launcher_lock_path(work_dir: Path) -> Path:
    work_dir = work_dir.expanduser().absolute()
    return work_dir.with_name(work_dir.name + ".launch.lock")


@contextmanager
def launch_lock(work_dir: Path):
    lock_path = launcher_lock_path(work_dir)
    descriptor = os.open(
        lock_path,
        os.O_CREAT | os.O_RDWR | getattr(os, "O_NOFOLLOW", 0),
        0o600,
    )
    try:
        try:
            os.fchmod(descriptor, 0o600)
        except (AttributeError, OSError):
            pass
        try:
            lock_file(descriptor)
        except (OSError, BlockingIOError) as error:
            raise AcquisitionError(
                "another Alpha-Dumper launcher already owns this work directory"
            ) from error
        yield lock_path
    finally:
        os.close(descriptor)


import json
import os
import shutil
from pathlib import Path
from typing import Iterable


CLIENT_NAMES = ("GenshinImpact.exe", "YuanShen.exe")
WINE_NAMES = ("wine", "wine64", "wine-stable")


def home() -> Path:
    override = os.environ.get("ALPHA_HOME")
    if override:
        return Path(override).expanduser()
    return Path.home() / "alpha"


def config_path() -> Path:
    override = os.environ.get("ALPHA_CONFIG")
    if override:
        return Path(override).expanduser()
    for candidate in (
        Path.cwd() / "alpha.json",
        Path(__file__).resolve().parents[2] / "alpha.json",
        home() / "alpha.json",
    ):
        if candidate.is_file():
            return candidate
    return home() / "alpha.json"


def load_config() -> dict:
    path = config_path()
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return value if isinstance(value, dict) else {}


def _setting(name: str) -> Path | None:
    env = os.environ.get("ALPHA_" + name.upper())
    if env:
        return Path(env).expanduser()
    value = load_config().get(name)
    if isinstance(value, str) and value.strip():
        return Path(value).expanduser()
    return None


def dump_root() -> Path:
    return _setting("dump_root") or home() / "dump"


def completion_root() -> Path:
    return _setting("completion_root") or home() / "completion"


def client_search_roots() -> list[Path]:
    roots: list[Path] = []
    extra = os.environ.get("ALPHA_CLIENT_DIRS")
    if extra:
        roots.extend(Path(item).expanduser() for item in extra.split(os.pathsep) if item)
    seen: list[Path] = []
    for root in roots:
        if root not in seen:
            seen.append(root)
    return seen


def _executables_under(root: Path, depth: int = 4) -> Iterable[Path]:
    if not root.is_dir():
        return
    yield from _walk_for_names(root, CLIENT_NAMES, depth)


def _walk_for_names(root: Path, names: tuple[str, ...], depth: int) -> Iterable[Path]:
    stack = [(root, 0)]
    lowered = {name.casefold() for name in names}
    while stack:
        directory, level = stack.pop()
        try:
            entries = list(os.scandir(directory))
        except OSError:
            continue
        for entry in entries:
            if entry.name.startswith("."):
                continue
            try:
                is_dir = entry.is_dir(follow_symlinks=False)
            except OSError:
                continue
            if is_dir:
                if level + 1 <= depth:
                    stack.append((Path(entry.path), level + 1))
                continue
            if entry.name.casefold() in lowered:
                yield Path(entry.path)


def find_clients() -> list[Path]:

    found: list[Path] = []
    configured = _setting("client")
    if configured is not None:
        if configured.is_file():
            found.append(configured)
        elif configured.is_dir():
            for name in CLIENT_NAMES:
                candidate = configured / name
                if candidate.is_file():
                    found.append(candidate)
    for root in client_search_roots():
        for path in _executables_under(root):
            if path not in found:
                found.append(path)
    return found


def find_wine() -> Path | None:
    configured = _setting("wine")
    if configured is not None and configured.is_file():
        return configured
    candidates = [
        Path.home() / "Library/Application Support/Yaagl OS/wine/bin/wine",
        Path.home() / "Library/Application Support/Yaagl/wine/bin/wine",
    ]
    for name in WINE_NAMES:
        located = shutil.which(name)
        if located:
            candidates.append(Path(located))
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    return None


def find_wineprefix() -> Path | None:
    configured = _setting("wineprefix")
    if configured is not None and configured.is_dir():
        return configured
    environment = os.environ.get("WINEPREFIX")
    if environment and Path(environment).expanduser().is_dir():
        return Path(environment).expanduser()
    candidates = [
        Path.home() / "Library/Application Support/Yaagl OS/wineprefix",
        Path.home() / "Library/Application Support/Yaagl/wineprefix",
        Path.home() / ".wine",
    ]
    for candidate in candidates:
        if candidate.is_dir():
            return candidate
    return None


def find_compiler() -> Path | None:
    configured = _setting("compiler")
    if configured is not None and configured.is_file():
        return configured
    names = [os.environ.get("CC")]
    if os.name == "nt":
        names.extend([
            "x86_64-w64-mingw32-gcc.exe",
            "x86_64-w64-mingw32-gcc",
            "gcc.exe",
            "gcc",
            "clang.exe",
            "clang",
        ])
    else:
        names.extend([
            "x86_64-w64-mingw32-gcc",
            "x86_64-w64-mingw32-clang",
            "clang",
        ])
    for name in names:
        if not name:
            continue
        if not name:
            continue
        located = shutil.which(name)
        if located:
            return Path(located)
    return None


def default_config_template() -> dict:
    return {
        "client": "",
        "wine": "",
        "wineprefix": "",
        "compiler": "",
        "dump_root": "",
        "completion_root": "",
    }
