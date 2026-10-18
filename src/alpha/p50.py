
from collections import Counter
from dataclasses import dataclass
from itertools import product
import hashlib
from functools import lru_cache
import json
import os
from pathlib import Path
import tempfile
import time
from typing import Any, Iterable, Mapping, Protocol, Sequence

from alpha.h01 import AcquisitionError


FIELD_ENCRYPTION_SCHEMA = "alpha.runtime-proto-field-encryption/v6"
FIELD_ENCRYPTION_JSON_NAME = "field-encrypt.json"
MAX_SUPPORTED_OPS = 4
MAX_SOLVER_SECONDS = 30.0
MAX_ADAPTIVE_ROUNDS = 64
ADAPTIVE_SAMPLE_COUNT = 32


def _nonnegative_count(value: Any) -> bool:
    return type(value) is int and value >= 0


_OPS = ("add", "xor")
FIELD_ENCRYPTION_EXCLUDED_CATEGORIES = (
    "bool", "string", "bytes", "message", "group",
)


@dataclass(frozen=True)
class RuntimeModule:
    name: str
    path: str
    image_base: int | None = None
    image_bytes: int | None = None


@dataclass(frozen=True)
class ProcessCandidate:
    pid: int
    executable_path: str
    process_name: str
    creation_time: int
    architecture: str
    modules: tuple[RuntimeModule, ...]

    def as_dict(self) -> dict:
        return {
            "pid": self.pid,
            "executable_path": self.executable_path,
            "process_name": self.process_name,
            "creation_time": self.creation_time,
            "architecture": self.architecture,
            "modules": [module.__dict__ for module in self.modules],
        }


class ProcessLocator(Protocol):

    def enumerate(self) -> Sequence[ProcessCandidate]: ...


class ProcessMemoryReader(Protocol):

    def read(self, pid: int, address: int, size: int) -> bytes: ...


class ModuleEnumerator(Protocol):
    def modules(self, pid: int) -> Sequence[RuntimeModule]: ...


class RuntimeDetector(Protocol):
    def detect(self, candidate: ProcessCandidate) -> dict: ...


def detect_runtime(candidate: ProcessCandidate) -> dict:
    names = {module.name.casefold() for module in candidate.modules}
    paths = {Path(module.path).name.casefold() for module in candidate.modules}
    names.update(paths)
    evidence: list[str] = []
    families: list[str] = []
    if "gameassembly.dll" in names:
        families.append("il2cpp")
        evidence.append("loaded module GameAssembly.dll")
    if any(name in names for name in ("mono-2.0-bdwgc.dll", "mono.dll", "libmono.so")):
        families.append("mono")
        evidence.append("loaded Mono runtime module")
    protobuf = "unknown"
    if any("protobuf-lite" in name or "libprotobuf-lite" in name for name in names):
        protobuf = "lite"
        evidence.append("loaded protobuf lite module")
    elif any("protobuf" in name for name in names):
        protobuf = "full"
        evidence.append("loaded protobuf module")
    if not families:
        families.append("native_cpp_or_custom")
    return {
        "runtime_families": families,
        "protobuf_runtime": protobuf,
        "descriptor_availability": "unresolved",
        "registration_mode": "unresolved",
        "evidence": evidence,
    }


def _same_executable(candidate: ProcessCandidate, expected: str) -> bool:
    left = candidate.executable_path.replace("\\", "/").casefold()
    right = str(expected).replace("\\", "/").casefold()
    return left == right or Path(left).name == Path(right).name


def select_process(
    candidates: Iterable[ProcessCandidate], *, pid: int | None = None,
    process_name: str | None = None, executable: str | Path | None = None,
    attach_latest: bool = False,
) -> ProcessCandidate:
    if pid is not None and (type(pid) is not int or pid <= 0):
        raise AcquisitionError("target PID must be a positive integer")
    if not any((pid is not None, process_name, executable, attach_latest)):
        raise AcquisitionError("one process selector is required")
    rows = list(candidates)
    if pid is not None:
        rows = [row for row in rows if row.pid == pid]
    if process_name:
        wanted = process_name.casefold()
        rows = [
            row for row in rows
            if row.process_name.casefold() == wanted
            or Path(row.process_name).stem.casefold() == Path(wanted).stem.casefold()
        ]
    if executable is not None:
        rows = [row for row in rows if _same_executable(row, str(executable))]
    if attach_latest and rows:
        newest = max(row.creation_time for row in rows)
        rows = [row for row in rows if row.creation_time == newest]
    if len(rows) == 1:
        return rows[0]
    details = [row.as_dict() for row in sorted(rows, key=lambda row: (row.creation_time, row.pid))]
    if not rows:
        raise AcquisitionError("no live process matches the requested selectors")
    raise AcquisitionError(
        "target process is ambiguous; refine --pid, --process-name, or --executable; "
        f"candidates={details}"
    )


def apply_ops(value: int, ops: Sequence[Sequence[Any]], width: int) -> int:
    mask = _width_mask(width)
    if type(value) is not int or not 0 <= value <= mask:
        raise AcquisitionError("field-encryption input is outside its bit width")
    result = value
    for entry in ops:
        if (
            not isinstance(entry, Sequence)
            or isinstance(entry, (str, bytes))
            or len(entry) != 2
        ):
            raise AcquisitionError("field-encryption operation is malformed")
        operation, constant = entry
        if operation not in {"add", "sub", "xor"}:
            raise AcquisitionError("field-encryption operation is unsupported")
        if type(constant) is not int or not 0 <= constant <= mask:
            raise AcquisitionError("field-encryption constant is outside its bit width")
        if operation == "add":
            result = (result + constant) & mask
        elif operation == "sub":
            result = (result - constant) & mask
        else:
            result ^= constant
    return result


def invert_ops(ops: Sequence[Sequence[Any]], width: int) -> list[list[Any]]:
    mask = _width_mask(width)
    inverse: list[list[Any]] = []
    for operation, constant in reversed(ops):
        if type(constant) is not int or not 0 <= constant <= mask:
            raise AcquisitionError("field-encryption constant is outside its bit width")
        if operation == "add":
            inverse.append(["sub", constant])
        elif operation == "sub":
            inverse.append(["add", constant])
        elif operation == "xor":
            inverse.append(["xor", constant])
        else:
            raise AcquisitionError("field-encryption operation is unsupported")
    return _canonicalize(inverse, width)


def _width_mask(width: int) -> int:
    if type(width) is not int or width not in (32, 64):
        raise AcquisitionError("field-encryption width must be 32 or 64")
    return (1 << width) - 1


def _valid_operation_rows(value: Any, width: int, *, allow_sub: bool = True) -> bool:
    if not isinstance(value, list):
        return False
    allowed = {"add", "xor", "sub"} if allow_sub else {"add", "xor"}
    try:
        mask = _width_mask(width)
    except AcquisitionError:
        return False
    return all(
        isinstance(operation, Sequence)
        and not isinstance(operation, (str, bytes))
        and len(operation) == 2
        and operation[0] in allowed
        and type(operation[1]) is int
        and 0 <= operation[1] <= mask
        for operation in value
    )


def _mask_for_bits(width: int) -> int:
    if type(width) is not int or not 1 <= width <= 64:
        raise AcquisitionError("field-encryption internal bit width is invalid")
    return (1 << width) - 1


def _canonicalize(ops: Iterable[Sequence[Any]], width: int) -> list[list[int | str]]:
    mask = _mask_for_bits(width)
    output: list[list[int | str]] = []
    for operation, constant in ops:
        if operation == "sub":
            operation, constant = "add", (-int(constant)) & mask
        if operation not in _OPS or type(constant) is not int:
            raise AcquisitionError("field-encryption operation cannot be normalized")
        constant &= mask
        if not constant:
            continue
        if output and output[-1][0] == operation:
            previous = int(output[-1][1])
            output[-1][1] = (
                previous ^ constant if operation == "xor"
                else (previous + constant) & mask
            )
            if output[-1][1] == 0:
                output.pop()
        else:
            output.append([operation, constant])
    return output


def _operation_shapes(max_ops: int) -> Iterable[tuple[str, ...]]:
    yield ()
    for length in range(1, max_ops + 1):
        for shape in product(_OPS, repeat=length):

            if any(shape[index] == shape[index - 1] for index in range(1, length)):
                continue
            yield shape


def _step_bits(
    value_bit: int, state: tuple[int, ...], ops: Sequence[Sequence[Any]], bit: int,
) -> tuple[int, tuple[int, ...]]:
    next_state: list[int] = []
    for index, (operation, constant) in enumerate(ops):
        key_bit = (int(constant) >> bit) & 1
        carry = state[index]
        if operation == "add":
            total = value_bit + key_bit + carry
            value_bit = total & 1
            next_state.append(total >> 1)
        elif operation == "xor":
            value_bit ^= key_bit
            next_state.append(0)
        else:
            raise AcquisitionError("field-encryption equivalence op is invalid")
    return value_bit, tuple(next_state)


def _equivalent_ops(
    left: Sequence[Sequence[Any]], right: Sequence[Sequence[Any]], width: int,
) -> bool:
    _mask_for_bits(width)
    states: set[tuple[tuple[int, ...], tuple[int, ...]]] = {
        ((0,) * len(left), (0,) * len(right))
    }
    for bit in range(width):
        next_states: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
        for left_state, right_state in states:
            for input_bit in (0, 1):
                left_bit, next_left = _step_bits(input_bit, left_state, left, bit)
                right_bit, next_right = _step_bits(input_bit, right_state, right, bit)
                if left_bit != right_bit:
                    return False
                next_states.add((next_left, next_right))
        states = next_states
    return True


def _z3_module():
    try:
        import z3
    except ImportError as error:
        raise AcquisitionError(
            "field-encryption proof requires the declared z3-solver dependency"
        ) from error
    return z3


def _symbolic_ops(value: Any, constants: Sequence[Any], shape: Sequence[str], width: int):
    z3 = _z3_module()
    result = value
    for operation, constant in zip(shape, constants):
        if operation == "add":
            result = result + constant
        elif operation == "xor":
            result = result ^ constant
        else:
            raise AcquisitionError("field-encryption solver op is invalid")
    return z3.simplify(result)


def _shape_solver(
    samples: Sequence[tuple[int, int]], width: int, shape: tuple[str, ...],
    *, distinguish_from: Sequence[Sequence[Any]] | None = None,
    timeout_ms: int = 15000,
):
    z3 = _z3_module()
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    constants = [z3.BitVec(f"k_{index}", width) for index in range(len(shape))]
    for sample_index, (source, target) in enumerate(samples):
        source_bits = z3.BitVecVal(source, width)
        target_bits = z3.BitVecVal(target, width)
        solver.add(
            _symbolic_ops(source_bits, constants, shape, width) == target_bits
        )
    challenge = None
    if distinguish_from is not None:
        challenge = z3.BitVec("challenge", width)
        candidate_bits = challenge
        for operation, constant in distinguish_from:
            key = z3.BitVecVal(int(constant), width)
            candidate_bits = (
                candidate_bits + key if operation == "add"
                else candidate_bits ^ key if operation == "xor"
                else candidate_bits - key if operation == "sub"
                else None
            )
            if candidate_bits is None:
                raise AcquisitionError("field-encryption candidate op is invalid")
        solver.add(
            _symbolic_ops(challenge, constants, shape, width) != candidate_bits
        )
    return solver, constants, challenge


def _model_shape_ops(model: Any, constants: Sequence[Any], shape: Sequence[str], width: int):
    values = [model.eval(item, model_completion=True).as_long() for item in constants]
    return _canonicalize(zip(shape, values), width)


def infer_restoring_candidates(
    samples: Sequence[tuple[int, int]], width: int, *, max_ops: int = MAX_SUPPORTED_OPS,
) -> list[list[list[int | str]]]:
    mask = _width_mask(width)
    if type(max_ops) is not int or not 0 <= max_ops <= MAX_SUPPORTED_OPS:
        raise AcquisitionError("field-encryption operation bound is invalid")
    normalized: list[tuple[int, int]] = []
    for row in samples:
        if (
            not isinstance(row, Sequence)
            or isinstance(row, (str, bytes))
            or len(row) != 2
            or type(row[0]) is not int
            or type(row[1]) is not int
            or not 0 <= row[0] <= mask
            or not 0 <= row[1] <= mask
        ):
            raise AcquisitionError("field-encryption observation is malformed")
        normalized.append((row[0], row[1]))
    if len(normalized) < max(8, width // 8) or len({row[0] for row in normalized}) != len(normalized):
        raise AcquisitionError("field-encryption observations are insufficient")
    cache_key = tuple(normalized)
    return [
        [list(operation) for operation in candidate]
        for candidate in _infer_restoring_candidates_cached(
            cache_key, width, max_ops
        )
    ]


@lru_cache(maxsize=256)
def _infer_restoring_candidates_cached(
    normalized: tuple[tuple[int, int], ...], width: int, max_ops: int,
) -> tuple[tuple[tuple[int | str, int], ...], ...]:
    z3 = _z3_module()
    shapes = list(_operation_shapes(max_ops))
    deadline = time.monotonic() + MAX_SOLVER_SECONDS
    candidate: list[list[int | str]] | None = None
    for shape in shapes:
        remaining_ms = int(max(0.0, deadline - time.monotonic()) * 1000)
        if remaining_ms <= 0:
            raise AcquisitionError("field-encryption candidate proof exceeded its time bound")
        solver, constants, _challenge = _shape_solver(
            normalized, width, shape, timeout_ms=min(15000, remaining_ms)
        )
        result = solver.check()
        if result == z3.unknown:
            raise AcquisitionError(
                "field-encryption solver could not close a candidate shape: "
                + solver.reason_unknown()
            )
        if result == z3.sat:
            candidate = _model_shape_ops(solver.model(), constants, shape, width)
            break
    if candidate is None:
        raise AcquisitionError(
            "runtime field transform is outside the supported add/xor operation language"
        )

    candidates: list[list[list[int | str]]] = [candidate]
    for shape in shapes:
        remaining_ms = int(max(0.0, deadline - time.monotonic()) * 1000)
        if remaining_ms <= 0:
            raise AcquisitionError("field-encryption uniqueness proof exceeded its time bound")
        solver, constants, _challenge = _shape_solver(
            normalized, width, shape, distinguish_from=candidate,
            timeout_ms=min(15000, remaining_ms),
        )
        result = solver.check()
        if result == z3.unknown:
            raise AcquisitionError(
                "field-encryption uniqueness proof did not complete: "
                + solver.reason_unknown()
            )
        if result != z3.sat:
            continue
        alternative = _model_shape_ops(solver.model(), constants, shape, width)
        if not any(
            _equivalent_ops(alternative, existing, width)
            for existing in candidates
        ):
            candidates.append(alternative)
    return tuple(tuple(tuple(operation) for operation in candidate)
                 for candidate in candidates)


def infer_restoring_ops(
    samples: Sequence[tuple[int, int]], width: int, *, max_ops: int = MAX_SUPPORTED_OPS,
) -> list[list[int | str]]:
    if (
        not isinstance(samples, Sequence)
        or isinstance(samples, (str, bytes))
        or any(
            not isinstance(row, Sequence)
            or isinstance(row, (str, bytes))
            or len(row) != 2
            or type(row[0]) is not int
            or type(row[1]) is not int
            for row in samples
        )
    ):
        candidates = infer_restoring_candidates(samples, width, max_ops=max_ops)
        if len(candidates) != 1:
            raise AcquisitionError(
                "field-encryption operation sequence is not structurally unique "
                f"(candidates={len(candidates)})"
            )
        return candidates[0]
    normalized = tuple((row[0], row[1]) for row in samples)
    return [list(row) for row in _infer_restoring_ops_cached(normalized, width, max_ops)]


@lru_cache(maxsize=256)
def _infer_restoring_ops_cached(
    samples: tuple[tuple[int, int], ...], width: int, max_ops: int,
) -> tuple[tuple[int | str, ...], ...]:
    candidates = infer_restoring_candidates(samples, width, max_ops=max_ops)
    if len(candidates) != 1:
        raise AcquisitionError(
            "field-encryption operation sequence is not structurally unique "
            f"(candidates={len(candidates)})"
        )
    return tuple(tuple(item) for item in candidates[0])


def initial_runtime_probe_values(width: int) -> list[int]:
    mask = _width_mask(width)
    half = 1 << (width - 1)
    values = [
        0,
        1,
        2,
        3,
        17,
        123,
        0x5555555555555555 & mask,
        0xAAAAAAAAAAAAAAAA & mask,
        half - 1,
        half,
        mask - 1,
        mask,
    ]
    if len(values) != len(set(values)):
        raise AcquisitionError("field-encryption initial probe values collide")
    return values


def _ieee_negative_zero_probe(width: int) -> int:
    return 1 << (width - 1)


def next_runtime_probe_value(
    samples: Sequence[tuple[int, int]], width: int,
    *, candidates: Sequence[Sequence[Sequence[Any]]] | None = None,
) -> int | None:
    observed_serialized = {serialized for serialized, _runtime in samples}
    candidates = (
        infer_restoring_candidates(samples, width)
        if candidates is None else [
            [list(operation) for operation in candidate]
            for candidate in candidates
        ]
    )
    if len(candidates) == 1:
        return None
    mask = _width_mask(width)
    probes = set(initial_runtime_probe_values(width))
    probes.update(range(256))
    seed = hashlib.sha256(
        b"alpha-field-encryption-probe-v1\0"
        + b"".join(
            int(source).to_bytes(width // 8, "little")
            + int(target).to_bytes(width // 8, "little")
            for source, target in samples
        )
    ).digest()
    for counter in range(256):
        probes.add(
            int.from_bytes(
                hashlib.sha256(seed + counter.to_bytes(4, "little")).digest()[:width // 8],
                "little",
            ) & mask
        )
    for first_index, first in enumerate(candidates):
        for other in candidates[first_index + 1:]:
            ciphertext = _distinguishing_input(first, other, width)
            if ciphertext is not None:
                probes.add(ciphertext)
    probes.discard(_ieee_negative_zero_probe(width))
    best: tuple[int, int, bytes] | None = None
    for serialized in sorted(probes - observed_serialized):
        outputs = [apply_ops(serialized, decoder, width) for decoder in candidates]
        partition_sizes: dict[int, int] = {}
        for output in outputs:
            partition_sizes[output] = partition_sizes.get(output, 0) + 1
        tie_break = hashlib.sha256(
            seed + b"field-transform-probe-tie\0"
            + serialized.to_bytes(width // 8, "little")
        ).digest()
        score = (
            len(partition_sizes),
            -max(partition_sizes.values()),
            tie_break,
        )
        if best is None or score > best:
            best = score
            selected = serialized
    if best is None or best[0] < 2:
        raise AcquisitionError(
            "field-encryption candidates cannot be separated by a fresh runtime input"
        )
    return selected


def next_runtime_probe_values(
    samples: Sequence[tuple[int, int]], width: int,
    *, candidates: Sequence[Sequence[Sequence[Any]]],
    count: int = ADAPTIVE_SAMPLE_COUNT,
) -> list[int]:
    mask = _width_mask(width)
    if type(count) is not int or count < 2 or count % 2:
        raise AcquisitionError("field-encryption adaptive batch size is invalid")
    if len(candidates) < 2:
        raise AcquisitionError("field-encryption candidates are not ambiguous")
    observed = {source for source, _target in samples}
    selected: list[int] = []

    def add(value: int | None) -> None:
        if (
            value is not None and type(value) is int
            and 0 <= value <= mask
            and value != _ieee_negative_zero_probe(width)
            and value not in observed
            and value not in selected and len(selected) < count
        ):
            selected.append(value)

    add(next_runtime_probe_value(samples, width, candidates=candidates))
    first = candidates[0]
    for alternative in candidates[1:]:
        add(_distinguishing_input(first, alternative, width))

    seed = hashlib.sha256(
        b"alpha-field-encryption-batch-v1\0"
        + width.to_bytes(2, "little")
        + b"".join(
            int(source).to_bytes(width // 8, "little")
            + int(target).to_bytes(width // 8, "little")
            for source, target in samples
        )
    ).digest()
    counter = 0
    while len(selected) < count:
        value = int.from_bytes(
            hashlib.sha256(seed + counter.to_bytes(8, "little")).digest()[:width // 8],
            "little",
        ) & mask
        add(value)
        counter += 1
        if counter > count * 128:
            raise AcquisitionError(
                "field-encryption adaptive batch could not create fresh values"
            )
    return selected


def unresolved_field_transform_roles(
    runtime_probe: Mapping[str, Any],
    *, identities: Iterable[tuple[int, int, str, str]] | None = None,
) -> dict[tuple[int, int, str, str], dict[str, Any]]:
    rows = runtime_probe.get("observations")
    if not isinstance(rows, list):
        raise AcquisitionError("field-transform probe observations are absent")
    selected = None if identities is None else set(identities)
    unresolved: dict[tuple[int, int, str, str], dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, Mapping) or not isinstance(row.get("identity"), Mapping):
            raise AcquisitionError("field-transform probe row is malformed")
        identity = row["identity"]
        key = tuple(identity.get(name) for name in (
            "type_index_owner_only", "number", "container", "role"
        ))
        if (
            len(key) != 4 or type(key[0]) is not int or type(key[1]) is not int
            or not isinstance(key[2], str) or not isinstance(key[3], str)
        ):
            raise AcquisitionError("field-transform probe identity is invalid")
        if selected is not None and key not in selected:
            continue
        width = identity.get("width")
        samples = row.get("samples_owner_only")
        if width not in (32, 64) or not isinstance(samples, list):
            raise AcquisitionError("field-transform probe sample inventory is invalid")
        pairs = []
        for sample in samples:
            if not isinstance(sample, Mapping):
                raise AcquisitionError("field-transform sample row is malformed")
            pairs.append((sample.get("serialized_value"), sample.get("runtime_value")))
        candidates = infer_restoring_candidates(pairs, width)
        if len(candidates) > 1:
            unresolved[key] = {
                "identity": dict(identity),
                "width": width,
                "samples": pairs,
                "candidates": candidates,
            }
    return unresolved


def validate_combined_field_transform_probe(
    runtime_probe: Mapping[str, Any],
) -> None:
    from alpha.h02 import file_identity, read_private_model
    from alpha.p43 import FIELD_TRANSFORM_RESULT_SCHEMA

    if (
        not isinstance(runtime_probe, Mapping)
        or runtime_probe.get("schema") != FIELD_TRANSFORM_RESULT_SCHEMA
        or runtime_probe.get("status") != "runtime-validated"
    ):
        raise AcquisitionError("combined field-transform probe schema is invalid")
    initial_ref = runtime_probe.get("initial_capture_model")
    if not isinstance(initial_ref, Mapping) or not isinstance(initial_ref.get("path"), str):
        raise AcquisitionError("combined field-transform probe has no source capture")
    initial_path = Path(initial_ref["path"]).expanduser().resolve()
    if file_identity(initial_path) != dict(initial_ref):
        raise AcquisitionError("initial field-transform capture identity differs")
    initial = read_private_model(initial_path)
    if file_identity(initial_path) != dict(initial_ref):
        raise AcquisitionError("initial field-transform capture changed while reading")
    if (
        initial.get("schema") != runtime_probe.get("schema")
        or initial.get("status") != "runtime-validated"
        or initial.get("target") != runtime_probe.get("target")
        or initial.get("policy") != runtime_probe.get("policy")
    ):
        raise AcquisitionError("initial field-transform capture binding differs")
    for identity_name in ("inventory", "status_receipt"):
        identity = initial.get(identity_name)
        if (
            not isinstance(identity, Mapping)
            or not isinstance(identity.get("path"), str)
            or file_identity(Path(identity["path"]).expanduser().resolve()) != dict(identity)
        ):
            raise AcquisitionError(
                f"initial field-transform {identity_name} identity differs"
            )
    initial_counts = initial.get("counts")
    initial_rows = initial.get("observations")
    if (
        not isinstance(initial_counts, Mapping)
        or not _nonnegative_count(initial_counts.get("required"))
        or not _nonnegative_count(initial_counts.get("verified"))
        or not _nonnegative_count(initial_counts.get("failed"))
        or initial_counts.get("required") != initial_counts.get("verified")
        or initial_counts.get("failed") != 0
        or not isinstance(initial_rows, list)
    ):
        raise AcquisitionError("initial field-transform capture is incomplete")
    combined = json.loads(json.dumps(initial_rows, ensure_ascii=False, allow_nan=False))
    combined_by_key: dict[tuple[int, int, str, str], dict[str, Any]] = {}
    for row in combined:
        if not isinstance(row, dict) or not isinstance(row.get("identity"), Mapping):
            raise AcquisitionError("initial field-transform observation is malformed")
        key = tuple(row["identity"].get(name) for name in (
            "type_index_owner_only", "number", "container", "role"
        ))
        if key in combined_by_key:
            raise AcquisitionError("initial field-transform role is duplicated")
        combined_by_key[key] = row
    rounds_by_key: dict[tuple[int, int, str, str], int] = {}
    adaptive = runtime_probe.get("adaptive_captures_owner_only", [])
    if not isinstance(adaptive, list):
        raise AcquisitionError("adaptive field-transform capture list is invalid")
    for record in adaptive:
        if not isinstance(record, Mapping):
            raise AcquisitionError("adaptive field-transform capture record is invalid")
        identity = record.get("identity")
        capture = record.get("capture")
        round_number = record.get("round")
        if (
            not isinstance(identity, Mapping)
            or type(round_number) is not int
            or not 0 < round_number <= MAX_ADAPTIVE_ROUNDS
            or not isinstance(capture, Mapping)
        ):
            raise AcquisitionError("adaptive field-transform capture identity is invalid")
        key = tuple(identity.get(name) for name in (
            "type_index_owner_only", "number", "container", "role"
        ))
        if key not in combined_by_key or identity != combined_by_key[key]["identity"]:
            raise AcquisitionError("adaptive field-transform capture targets another role")
        if round_number != rounds_by_key.get(key, 0) + 1:
            raise AcquisitionError("adaptive field-transform rounds are out of order")
        rounds_by_key[key] = round_number
        model_ref = capture.get("model")
        if not isinstance(model_ref, Mapping) or not isinstance(model_ref.get("path"), str):
            raise AcquisitionError("adaptive field-transform model identity is absent")
        model_path = Path(model_ref["path"]).expanduser().resolve()
        if file_identity(model_path) != dict(model_ref):
            raise AcquisitionError("adaptive field-transform model identity differs")
        extra_model = read_private_model(model_path)
        if file_identity(model_path) != dict(model_ref):
            raise AcquisitionError("adaptive field-transform model changed while reading")
        extra_rows = extra_model.get("observations")
        extra_counts = extra_model.get("counts")
        if (
            extra_model.get("schema") != runtime_probe.get("schema")
            or extra_model.get("status") != "runtime-validated"
            or extra_model.get("target") != runtime_probe.get("target")
            or not isinstance(extra_rows, list) or len(extra_rows) != 1
            or not isinstance(extra_counts, Mapping)
            or not _nonnegative_count(extra_counts.get("required"))
            or not _nonnegative_count(extra_counts.get("verified"))
            or not _nonnegative_count(extra_counts.get("failed"))
            or extra_counts.get("required") != 1
            or extra_counts.get("verified") != 1
            or extra_counts.get("failed") != 0
        ):
            raise AcquisitionError("adaptive field-transform capture is incomplete")
        for identity_name in ("inventory", "status_receipt"):
            identity_value = extra_model.get(identity_name)
            if (
                not isinstance(identity_value, Mapping)
                or not isinstance(identity_value.get("path"), str)
                or file_identity(
                    Path(identity_value["path"]).expanduser().resolve()
                ) != dict(identity_value)
            ):
                raise AcquisitionError(
                    f"adaptive field-transform {identity_name} identity differs"
                )
        extra = extra_rows[0]
        base = combined_by_key[key]
        if (
            extra.get("identity") != identity
            or any(extra.get(name) != base.get(name) for name in (
                "encoding", "context", "field_index_owner_only"
            ))
        ):
            raise AcquisitionError("adaptive field-transform role schema changed")
        extra_samples = extra.get("samples_owner_only")
        probe_values = record.get("probe_values_owner_only")
        base_samples = base.get("samples_owner_only")
        width = identity.get("width")
        if (
            not isinstance(extra_samples, list)
            or not isinstance(probe_values, list)
            or len(probe_values) != ADAPTIVE_SAMPLE_COUNT
            or len(probe_values) % 2
            or type(width) is not int or width not in (32, 64)
            or any(type(value) is not int or not 0 <= value < (1 << width)
                   for value in probe_values)
            or len(set(probe_values)) != len(probe_values)
            or len(extra_samples) != len(probe_values)
            or not _nonnegative_count(extra_counts.get("sample_count_per_role"))
            or extra_counts.get("sample_count_per_role") != len(probe_values)
            or not isinstance(base_samples, list)
        ):
            raise AcquisitionError("adaptive field-transform sample batch is invalid")
        observed_inputs = {
            sample.get("serialized_value") for sample in base_samples
            if isinstance(sample, Mapping)
        }
        if any(
            not isinstance(sample, Mapping)
            or sample.get("serialized_value") in observed_inputs
            for sample in extra_samples
        ) or [sample.get("serialized_value") for sample in extra_samples] != probe_values:
            raise AcquisitionError("adaptive field-transform samples are duplicated")
        base_samples.extend(json.loads(json.dumps(
            extra_samples, ensure_ascii=False, allow_nan=False
        )))
    if combined != runtime_probe.get("observations"):
        raise AcquisitionError("combined field-transform rows differ from live source captures")
    expected_keys = set(combined_by_key)
    if len(expected_keys) != len(combined_by_key):
        raise AcquisitionError("combined field-transform role inventory is duplicated")
    final_counts = runtime_probe.get("counts")
    lengths = [len(row.get("samples_owner_only", [])) for row in combined]
    if (
        not isinstance(final_counts, Mapping)
        or not _nonnegative_count(final_counts.get("required"))
        or not _nonnegative_count(final_counts.get("verified"))
        or not _nonnegative_count(final_counts.get("failed"))
        or not _nonnegative_count(final_counts.get("sample_count_min"))
        or not _nonnegative_count(final_counts.get("sample_count_max"))
        or final_counts.get("required") != len(combined)
        or final_counts.get("verified") != len(combined)
        or final_counts.get("failed") != 0
        or final_counts.get("sample_count_min") != min(lengths, default=0)
        or final_counts.get("sample_count_max") != max(lengths, default=0)
    ):
        raise AcquisitionError("combined field-transform counts do not close")


def classify_runtime_field_samples(
    samples: Sequence[tuple[int, int]], width: int,
) -> dict[str, Any]:
    ops = infer_restoring_ops(samples, width)
    sample_rows = [
        {"serialized_value": serialized, "runtime_value": runtime_value}
        for serialized, runtime_value in samples
    ]
    return {
        "width": width,
        "disposition": "identity" if not ops else "encrypted",
        **({"ops": ops} if ops else {}),
        "samples_owner_only": sample_rows,
    }


def distinguishing_runtime_input(
    candidates: Sequence[Sequence[Sequence[Any]]], width: int,
    *, already_observed: Iterable[int] = (),
) -> int:
    _width_mask(width)
    if len(candidates) < 2:
        raise AcquisitionError("field-encryption candidates are not ambiguous")
    observed = set(already_observed)
    first = candidates[0]
    for other in candidates[1:]:
        ciphertext = _distinguishing_input(first, other, width)
        if ciphertext is None:
            continue
        if ciphertext not in observed:
            return ciphertext
    raise AcquisitionError(
        "field-encryption candidates cannot be separated by a fresh runtime input"
    )


def _distinguishing_input(
    left: Sequence[Sequence[Any]], right: Sequence[Sequence[Any]], width: int,
) -> int | None:
    _width_mask(width)
    states: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {
        ((0,) * len(left), (0,) * len(right)): 0
    }
    for bit in range(width):
        next_states: dict[tuple[tuple[int, ...], tuple[int, ...]], int] = {}
        for (left_state, right_state), prefix in states.items():
            for input_bit in (0, 1):
                left_bit, next_left = _step_bits(input_bit, left_state, left, bit)
                right_bit, next_right = _step_bits(input_bit, right_state, right, bit)
                value = prefix | (input_bit << bit)
                if left_bit != right_bit:
                    return value
                next_states.setdefault((next_left, next_right), value)
        states = next_states
    return None


def validate_observation_inventory(
    value: Mapping[str, Any], *, executable_sha256: str,
    expected_target: Mapping[str, Any],
) -> dict[tuple[int, int, str, str], dict[str, Any]]:
    target = value.get("target") if isinstance(value, Mapping) else None
    policy = value.get("policy") if isinstance(value, Mapping) else None
    inputs = value.get("inputs") if isinstance(value, Mapping) else None
    probe_model_identity = (
        inputs.get("runtime_probe_model") if isinstance(inputs, Mapping) else None
    )
    if (
        not isinstance(value, Mapping)
        or value.get("schema") != FIELD_ENCRYPTION_SCHEMA
        or value.get("status") != "runtime-validated"
        or not isinstance(target, Mapping)
        or target.get("executable_sha256") != executable_sha256
        or not isinstance(expected_target, Mapping)
        or dict(target) != dict(expected_target)
        or expected_target.get("executable_sha256") != executable_sha256
        or not isinstance(policy, Mapping)
        or policy.get("reference_proto_values_used") is not False
        or policy.get("fresh_runtime_observations_used") is not True
        or policy.get("current_runtime_only") is not True
        or policy.get("all_numeric_proto_roles_required") is not True
        or policy.get("excluded_field_categories")
        != list(FIELD_ENCRYPTION_EXCLUDED_CATEGORIES)
        or policy.get("decoder_selection")
        != "shortest-candidate-unique-within-supported-add-xor-model"
        or policy.get("decoder_maximum_operations") != MAX_SUPPORTED_OPS
        or policy.get("adaptive_samples_per_round") != ADAPTIVE_SAMPLE_COUNT
        or policy.get("maximum_adaptive_rounds") != MAX_ADAPTIVE_ROUNDS
        or policy.get("full_runtime_transform_implementation_proven") is not False
        or policy.get("parser_body_evidence_scope")
        != "message-parser-post-call-standard-reader-store"
        or not isinstance(probe_model_identity, Mapping)
        or not isinstance(probe_model_identity.get("path"), str)
        or type(probe_model_identity.get("bytes")) is not int
        or probe_model_identity.get("bytes", -1) < 0
        or not isinstance(probe_model_identity.get("sha256"), str)
        or len(probe_model_identity.get("sha256", "")) != 64
        or any(
            char not in "0123456789abcdef"
            for char in probe_model_identity.get("sha256", "")
        )
    ):
        raise AcquisitionError("field-encryption runtime model is stale or unbound")
    checks = value.get("checks")
    rows = value.get("field_observations_owner_only")
    coverage = value.get("coverage")
    if (
        not isinstance(checks, Mapping)
        or not checks
        or any(item is not True for item in checks.values())
        or not isinstance(rows, list)
        or not isinstance(coverage, Mapping)
        or coverage.get("complete") is not True
        or checks.get("reference_proto_data_excluded") is not True
        or checks.get("fallback_sample_models_unique") is not True
        or checks.get("parser_body_evidence_inventory_closed") is not True
        or checks.get("runtime_role_inventory_matches_proto_model") is not True
        or checks.get("non_numeric_field_categories_excluded") is not True
    ):
        raise AcquisitionError("field-encryption runtime model is incomplete")
    output: dict[tuple[int, int, str, str], dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, Mapping):
            raise AcquisitionError("field-encryption observation row is invalid")
        type_index = row.get("message_type_index_owner_only")
        field_index = row.get("field_index_owner_only")
        number = row.get("field_number")
        container = row.get("container")
        role = row.get("role")
        width = row.get("width")
        disposition = row.get("disposition")
        if (
            type(type_index) is not int or type_index < 0
            or type(field_index) is not int or field_index < 0
            or type(number) is not int or not 0 < number <= 0x1FFFFFFF
            or not isinstance(container, str) or not (
                container == "field" or container.startswith("oneof:")
                and len(container) > len("oneof:")
            )
            or role not in {"type", "key_type", "value_type"}
            or width not in (32, 64)
            or disposition not in {"identity", "encrypted"}
        ):
            raise AcquisitionError("field-encryption observation identity is invalid")
        key = (type_index, number, container, role)
        if key in output:
            raise AcquisitionError("field-encryption observation identity is duplicated")
        record = dict(row)
        retained_samples = record.get("samples_owner_only")
        if not isinstance(retained_samples, list):
            raise AcquisitionError("field-encryption runtime samples are absent")
        for sample in retained_samples:
            if not isinstance(sample, Mapping):
                raise AcquisitionError("field-encryption runtime sample is malformed")
            input_hex = sample.get("input_hex")
            input_fnv64 = sample.get("input_fnv64")
            try:
                payload = bytes.fromhex(input_hex) if isinstance(input_hex, str) else b""
            except ValueError as error:
                raise AcquisitionError("field-encryption input payload is malformed") from error
            if (
                not payload or payload.hex() != input_hex
                or type(input_fnv64) is not int
                or not 0 <= input_fnv64 < (1 << 64)
                or _fnv64(payload) != input_fnv64
            ):
                raise AcquisitionError("field-encryption input payload hash differs")
        if disposition == "encrypted":
            ops = record.get("ops")
            if not isinstance(ops, list) or not ops or any(
                not isinstance(item, Sequence)
                or isinstance(item, (str, bytes))
                or len(item) != 2 for item in ops
            ):
                raise AcquisitionError("encrypted field has no operation evidence")
            for operation, constant in ops:
                if (
                    operation not in {"add", "sub", "xor"}
                    or type(constant) is not int
                    or not 0 <= constant < (1 << width)
                ):
                    raise AcquisitionError("encrypted field operation is invalid")
            samples = record.get("samples_owner_only")
            if not isinstance(samples, list) or len(samples) < max(8, width // 8):
                raise AcquisitionError("encrypted field sample domain is incomplete")
            restoring = [
                (sample.get("serialized_value"), sample.get("runtime_value"))
                for sample in samples
                if isinstance(sample, Mapping)
            ]
            if (
                len(restoring) != len(samples)
                or any(
                    type(source) is not int
                    or type(target) is not int
                    or not 0 <= source < (1 << width)
                    or not 0 <= target < (1 << width)
                    for source, target in restoring
                )
                or len({source for source, _target in restoring}) != len(samples)
                or len({target for _source, target in restoring}) != len(samples)
            ):
                raise AcquisitionError("encrypted field runtime samples are invalid")
            body_candidate = record.get("parser_body_evidence_owner_only")
            if (
                isinstance(body_candidate, Mapping)
                and body_candidate.get("status") == "post-call-chain-matches-probes"
            ):
                body_candidate_ops = body_candidate.get("ops")
                if not _valid_operation_rows(body_candidate_ops, width, allow_sub=False):
                    raise AcquisitionError("field-encryption parser-body operations are invalid")
                if not _equivalent_ops(body_candidate_ops, ops, width):
                    raise AcquisitionError(
                        "field-encryption ops differ from proven parser-body chain"
                    )
            elif not _equivalent_ops(
                infer_restoring_ops(restoring, width), ops, width
            ):
                raise AcquisitionError("field-encryption ops differ from observed values")
        else:
            if "ops" in record:
                raise AcquisitionError("identity field must not publish encryption ops")
            samples = record.get("samples_owner_only")
            if not isinstance(samples, list) or len(samples) < max(8, width // 8):
                raise AcquisitionError("identity field sample domain is incomplete")
            values = [
                (sample.get("serialized_value"), sample.get("runtime_value"))
                for sample in samples
                if isinstance(sample, Mapping)
            ]
            if (
                len(values) != len(samples)
                or any(
                    type(source) is not int
                    or type(target) is not int
                    or not 0 <= source < (1 << width)
                    or not 0 <= target < (1 << width)
                    for source, target in values
                )
                or len({source for source, _target in values}) != len(samples)
                or len({target for _source, target in values}) != len(samples)
                or any(
                    source != target
                    for source, target in values
                )
            ):
                raise AcquisitionError("identity field is not proven by runtime samples")
        body_evidence = record.get("parser_body_evidence_owner_only")
        if not isinstance(body_evidence, Mapping):
            raise AcquisitionError("field-encryption parser-body evidence is absent")
        body_status = body_evidence.get("status")
        if body_status not in {"unresolved", "post-call-chain-matches-probes"}:
            raise AcquisitionError("field-encryption parser-body evidence status is invalid")
        cases = body_evidence.get("cases")
        if not isinstance(cases, list):
            raise AcquisitionError("field-encryption parser-body case inventory is invalid")
        if body_status == "post-call-chain-matches-probes":
            body_ops = body_evidence.get("ops")
            cardinality = row.get("cardinality", "singular")
            scope = {
                "singular": "message-parser-post-call-standard-reader-store",
                "repeated": "message-parser-post-call-collection-element-store",
                "map": ("message-parser-post-call-map-key-store" if role == "key_type"
                        else "message-parser-post-call-map-value-store"),
            }.get(cardinality)
            expected_wire = {
                "int32": 0, "sint32": 0, "uint32": 0,
                "int64": 0, "sint64": 0, "uint64": 0,
                "fixed32": 5, "sfixed32": 5, "float": 5,
                "fixed64": 1, "sfixed64": 1, "double": 1,
            }.get(record.get("encoding"))
            if (
                body_evidence.get("scope")
                != scope
                or scope is None
                or expected_wire is None
                or not _valid_operation_rows(body_ops, width, allow_sub=False)
                or len(cases) == 0
            ):
                raise AcquisitionError("field-encryption parser-body proof is malformed")
            replayed = _parser_body_probe_evidence(
                field={**record, "parser_body_transfers_owner_only": cases},
                container=container, encoding=str(record.get("encoding")), width=width,
                samples=[(sample["serialized_value"], sample["runtime_value"])
                         for sample in retained_samples],
                inferred_ops=body_ops,
            )
            if replayed != body_evidence:
                raise AcquisitionError("field-encryption parser-body proof differs from replay")
            for case in cases:
                if not isinstance(case, Mapping):
                    raise AcquisitionError("field-encryption parser-body case is malformed")
                transfer = case.get("transfer")
                if (
                    type(case.get("field_number")) is not int
                    or case.get("field_number") != number
                    or type(case.get("wire")) is not int
                    or (case.get("wire") != expected_wire and not (
                        cardinality in {"repeated", "map"}
                        and isinstance(transfer, Mapping)
                        and transfer.get("store_kind") == "call-argument"))
                    or type(case.get("code_offset")) is not int
                    or case.get("code_offset") < 0
                    or not isinstance(transfer, Mapping)
                    or transfer.get("status") != "proven"
                    or transfer.get("proof") != "bounded-parser-body-path-analysis"
                    or transfer.get("width") != width
                    or type(transfer.get("source_call_offset")) is not int
                    or transfer.get("source_call_offset") < 0
                    or type(transfer.get("store_offset")) is not int
                    or transfer.get("store_offset") != case.get("code_offset")
                    or transfer.get("source_call_offset") >= transfer.get("store_offset")
                    or not _reader_call_binding_matches(transfer)
                    or not _valid_operation_rows(
                        transfer.get("ops"), width, allow_sub=False
                    )
                    or not _equivalent_ops(transfer["ops"], body_ops, width)
                ):
                    raise AcquisitionError("field-encryption parser-body case binding differs")
                reader_method = transfer.get("reader_method_owner_only")
                reader_resolution = transfer.get("reader_method_resolution")
                if isinstance(reader_method, Mapping):
                    if (
                        type(reader_method.get("method_index_owner_only")) is not int
                        or reader_method.get("method_index_owner_only") < 0
                        or type(reader_method.get("owner_type_index_owner_only")) is not int
                        or reader_method.get("owner_type_index_owner_only") < 0
                        or type(reader_method.get("call_target_owner_only")) is not int
                        or reader_method.get("call_target_owner_only") <= 0
                        or reader_method.get("call_target_owner_only")
                        != reader_method.get("code_pointer_owner_only")
                        or not _standard_reader_identity(
                            reader_method,
                            encoding=str(record.get("encoding")),
                            width=width,
                        )
                        or type(reader_method.get("parameter_count_owner_only")) is not int
                        or reader_method.get("parameter_count_owner_only") < 0
                        or reader_resolution is not None
                    ):
                        raise AcquisitionError("field-encryption reader method binding is invalid")
                elif (
                    not isinstance(reader_resolution, Mapping)
                    or reader_resolution.get("status") != "unresolved"
                    or not (
                        isinstance(reader_resolution.get("reason"), str)
                        or type(reader_resolution.get("candidate_count")) is int
                        and reader_resolution.get("candidate_count") >= 0
                    )
                ):
                    raise AcquisitionError("field-encryption reader method resolution is unexplained")
            for sample in record["samples_owner_only"]:
                if apply_ops(
                    int(sample["serialized_value"]), body_ops, width
                ) != int(sample["runtime_value"]):
                    raise AcquisitionError(
                        "field-encryption parser-body operations disagree with runtime probes"
                    )
        elif not isinstance(body_evidence.get("reason"), str):
            raise AcquisitionError("unresolved field-encryption parser-body reason is absent")
        recovery_method = record.get("recovery_method")
        if recovery_method not in {"bounded-parser-body", "bounded-sample-model"}:
            raise AcquisitionError("field-encryption recovery method is invalid")
        if recovery_method == "bounded-parser-body":
            if body_status != "post-call-chain-matches-probes":
                raise AcquisitionError("field-encryption parser-body recovery lacks proof")
            recovered_ops = record.get("ops", []) if disposition == "encrypted" else []
            if not _equivalent_ops(body_evidence.get("ops", []), recovered_ops, width):
                raise AcquisitionError("field-encryption recovery differs from parser body")
        elif body_status == "post-call-chain-matches-probes":
            recovered_ops = record.get("ops", []) if disposition == "encrypted" else []
            if not _equivalent_ops(body_evidence.get("ops", []), recovered_ops, width):
                raise AcquisitionError("field-encryption sample recovery conflicts with parser body")
        output[key] = record
    coverage = value.get("coverage")
    if not isinstance(coverage, Mapping):
        raise AcquisitionError("field-encryption coverage record is invalid")
    if (
        any(
            type(coverage.get(name)) is not int or coverage.get(name) < 0
            for name in (
                "observed_role_count",
                "encrypted_field_count",
                "identity_field_count",
                "unresolved_field_count",
            )
        )
        or coverage.get("observed_role_count") != len(output)
        or coverage.get("encrypted_field_count") != sum(
            row["disposition"] == "encrypted" for row in output.values()
        )
        or coverage.get("identity_field_count") != sum(
            row["disposition"] == "identity" for row in output.values()
        )
        or coverage.get("unresolved_field_count") != 0
    ):
        raise AcquisitionError("field-encryption coverage counts do not close")
    implementation_coverage = value.get("implementation_evidence_coverage")
    if (
        not isinstance(implementation_coverage, Mapping)
        or type(implementation_coverage.get("numeric_role_count")) is not int
        or implementation_coverage.get("numeric_role_count") < 0
        or implementation_coverage.get("numeric_role_count") != len(output)
        or type(implementation_coverage.get("post_call_chain_matches_probe_count")) is not int
        or implementation_coverage.get("post_call_chain_matches_probe_count") < 0
        or type(implementation_coverage.get("unresolved_count")) is not int
        or implementation_coverage.get("unresolved_count") < 0
        or implementation_coverage.get("post_call_chain_matches_probe_count")
        + implementation_coverage.get("unresolved_count") != len(output)
        or implementation_coverage.get("end_to_end_function_proven") is not False
    ):
        raise AcquisitionError("field-encryption implementation evidence coverage is invalid")
    if implementation_coverage["post_call_chain_matches_probe_count"] != sum(
        row["parser_body_evidence_owner_only"]["status"]
        == "post-call-chain-matches-probes"
        for row in output.values()
    ):
        raise AcquisitionError("field-encryption implementation evidence counts differ")
    return output


def _enum_type_names(rows: Sequence[Any]) -> set[str]:
    names: set[str] = set()
    for row in rows:
        if not isinstance(row, Mapping) or not isinstance(row.get("name"), str):
            raise AcquisitionError("field-encryption enum type inventory is malformed")
        names.add(str(row["name"]))
        declaring_path = row.get("declaring_path")
        if declaring_path is not None:
            if not isinstance(declaring_path, str) or not declaring_path:
                raise AcquisitionError("field-encryption enum declaring path is malformed")
            names.add(declaring_path)
    return names


def _numeric_role(type_name: Any, enum_names: set[str]) -> tuple[str, int] | None:
    scalar_widths = {
        "int32": 32, "uint32": 32, "sint32": 32,
        "fixed32": 32, "sfixed32": 32, "float": 32,
        "int64": 64, "uint64": 64, "sint64": 64,
        "fixed64": 64, "sfixed64": 64, "double": 64,
    }
    if isinstance(type_name, str) and type_name in scalar_widths:
        return type_name, scalar_widths[type_name]
    if isinstance(type_name, str) and type_name in enum_names:
        return "int32", 32
    return None


def _standard_reader_identity(
    value: Mapping[str, Any], *, encoding: str, width: int
) -> bool:
    reader_contracts = {
        "int32": ("ReadInt32", "System.Int32", 32),
        "sint32": ("ReadSInt32", "System.Int32", 32),
        "uint32": ("ReadUInt32", "System.UInt32", 32),
        "fixed32": ("ReadFixed32", "System.UInt32", 32),
        "sfixed32": ("ReadSFixed32", "System.Int32", 32),
        "float": ("ReadFloat", "System.Single", 32),
        "int64": ("ReadInt64", "System.Int64", 64),
        "sint64": ("ReadSInt64", "System.Int64", 64),
        "uint64": ("ReadUInt64", "System.UInt64", 64),
        "fixed64": ("ReadFixed64", "System.UInt64", 64),
        "sfixed64": ("ReadSFixed64", "System.Int64", 64),
        "double": ("ReadDouble", "System.Double", 64),
    }
    expected = reader_contracts.get(encoding)
    return bool(
        expected is not None
        and expected[2] == width
        and value.get("name_owner_only") == expected[0]
        and value.get("return_type_owner_only") == expected[1]
        and value.get("parameter_count_owner_only") == 0
    )


def _reader_call_binding_matches(transfer: Mapping[str, Any]) -> bool:
    if transfer.get("indirect_reader_call_owner_only") is True:
        return False
    parser_pointer = transfer.get("parser_method_code_pointer_owner_only")
    if type(parser_pointer) is not int or parser_pointer <= 0:
        return False
    readers = transfer.get("reader_methods_owner_only")
    if not isinstance(readers, list) or not readers:
        readers = [transfer.get("reader_method_owner_only")]
    offsets = transfer.get("reader_call_offsets_owner_only")
    if isinstance(offsets, list) and offsets:
        if any(type(value) is not int for value in offsets):
            return False
    elif type(transfer.get("source_call_target_offset")) is not int:
        return False
    else:
        offsets = [transfer["source_call_target_offset"]]
    if len(offsets) != len(readers):
        return False
    store_method = transfer.get("store_method_owner_only")
    if store_method is not None:
        if (
            not isinstance(store_method, Mapping)
            or type(store_method.get("parser_code_pointer_owner_only")) is not int
            or type(store_method.get("call_site_offset_owner_only")) is not int
            or type(store_method.get("code_pointer_owner_only")) is not int
            or store_method.get("parser_code_pointer_owner_only")
            + store_method.get("call_site_offset_owner_only")
            != store_method.get("code_pointer_owner_only")
        ):
            return False
    for offset, reader in zip(offsets, readers):
        if not isinstance(reader, Mapping):
            return False
        return_type = reader.get("return_type_owner_only")
        expected_return_bank = {
            "System.Int32": "rax", "System.UInt32": "rax",
            "System.Int64": "rax", "System.UInt64": "rax",
            "System.Single": "xmm0", "System.Double": "xmm0",
        }.get(return_type)
        resolved_target = parser_pointer + offset
        if not (
            expected_return_bank is not None
            and transfer.get("source_call_return_bank") == expected_return_bank
            and resolved_target > 0
            and type(reader.get("call_target_owner_only")) is int
            and type(reader.get("code_pointer_owner_only")) is int
            and reader.get("call_target_owner_only") == resolved_target
            and reader.get("code_pointer_owner_only") == resolved_target
        ):
            return False
    return True


def _parser_body_probe_evidence(
    *, field: Mapping[str, Any], container: str, encoding: str, width: int,
    samples: Sequence[tuple[int, int]],
    inferred_ops: Sequence[Sequence[Any]] | None,
) -> dict[str, Any]:
    raw_cases = field.get("parser_body_transfers_owner_only")
    if not isinstance(raw_cases, list):
        return {"status": "unresolved", "reason": "parser-body-evidence-absent", "cases": []}
    cardinality = field.get("cardinality", "singular")
    if cardinality not in {"singular", "repeated", "map"}:
        return {
            "status": "unresolved",
            "reason": "cardinality-handler-not-analyzed",
            "cases": copy_json_value(raw_cases),
        }


    role = str(field.get("role") or "type")
    if cardinality == "singular":
        expected_store_argument = None
    elif cardinality == "repeated":
        expected_store_argument = 0
    elif role == "key_type":
        expected_store_argument = 0
    else:
        expected_store_argument = 1
    scalar_wires = {
        "int32": 0, "sint32": 0, "uint32": 0,
        "int64": 0, "sint64": 0, "uint64": 0,
        "fixed32": 5, "sfixed32": 5, "float": 5,
        "fixed64": 1, "sfixed64": 1, "double": 1,
    }
    expected_wire = scalar_wires.get(encoding)
    if expected_wire is None:
        return {
            "status": "unresolved",
            "reason": "wire-encoding-has-no-scalar-parser-case",
            "cases": copy_json_value(raw_cases),
        }
    cases = [
        item for item in raw_cases
        if isinstance(item, Mapping)
        and (
            item.get("wire") == expected_wire
            or (
                isinstance(item.get("transfer"), Mapping)
                and item["transfer"].get("store_kind") == "call-argument"
            )
        )
    ]
    if not cases:
        return {
            "status": "unresolved",
            "reason": "expected-scalar-parser-case-absent",
            "cases": [],
        }
    transfers = [item.get("transfer") for item in cases]
    if any(
        not isinstance(transfer, Mapping)
        or transfer.get("status") != "proven"
        or transfer.get("proof") != "bounded-parser-body-path-analysis"
        or transfer.get("width") != width
        or not _reader_call_binding_matches(transfer)
        or not _valid_operation_rows(transfer.get("ops"), width, allow_sub=False)
        for transfer in transfers
    ):
        return {
            "status": "unresolved",
            "reason": "one-or-more-parser-cases-lack-exact-post-call-dataflow",
            "cases": copy_json_value(cases),
        }
    if expected_store_argument is not None:
        store_bindings = [transfer.get("store_method_owner_only") for transfer in transfers]
        if any(
            not isinstance(binding, Mapping)
            or binding.get("argument_index_owner_only") != expected_store_argument
            or not isinstance(binding.get("owner_type_name_owner_only"), str)
            or not isinstance(binding.get("field_type_name_owner_only"), str)
            or "<" not in binding["owner_type_name_owner_only"]
            or "<" not in binding["field_type_name_owner_only"]
            or binding["owner_type_name_owner_only"].split("<", 1)[0]
            != binding["field_type_name_owner_only"].split("<", 1)[0]
            for binding in store_bindings
        ):
            return {
                "status": "unresolved",
                "reason": "collection-element-store-binding-absent",
                "cases": copy_json_value(cases),
            }
    reader_methods: list[Mapping[str, Any]] = []
    for transfer in transfers:
        rows = transfer.get("reader_methods_owner_only")
        if isinstance(rows, list) and rows:
            reader_methods.extend(rows)
        else:
            reader_methods.append(transfer.get("reader_method_owner_only"))
    if any(
        not isinstance(reader, Mapping)
        or not _standard_reader_identity(reader, encoding=encoding, width=width)
        for reader in reader_methods
    ):
        return {
            "status": "unresolved",
            "reason": "reader-method-identity-does-not-match-protobuf-scalar-contract",
            "cases": copy_json_value(cases),
        }
    if len({
        (
            reader.get("method_index_owner_only"),
            reader.get("owner_type_index_owner_only"),
            reader.get("call_target_owner_only"),
            reader.get("code_pointer_owner_only"),
        )
        for reader in reader_methods
        if isinstance(reader, Mapping)
    }) != 1:
        return {
            "status": "unresolved",
            "reason": "parser-cases-call-different-scalar-readers",
            "cases": copy_json_value(cases),
        }
    first_ops = transfers[0]["ops"]
    if any(
        not _equivalent_ops(first_ops, transfer["ops"], width)
        for transfer in transfers[1:]
    ):
        return {
            "status": "unresolved",
            "reason": "parser-cases-have-different-post-call-transforms",
            "cases": copy_json_value(cases),
        }
    if (
        any(apply_ops(source, first_ops, width) != target for source, target in samples)
        or inferred_ops is not None
        and not _equivalent_ops(first_ops, inferred_ops, width)
    ):
        return {
            "status": "unresolved",
            "reason": "post-call-chain-does-not-account-for-runtime-probes",
            "cases": copy_json_value(cases),
        }
    scope = "message-parser-post-call-standard-reader-store"
    if cardinality == "repeated":
        scope = "message-parser-post-call-collection-element-store"
    elif cardinality == "map":
        scope = (
            "message-parser-post-call-map-key-store"
            if role == "key_type"
            else "message-parser-post-call-map-value-store"
        )
    return {
        "status": "post-call-chain-matches-probes",
        "scope": scope,
        "ops": copy_json_value(first_ops),
        "cases": copy_json_value(cases),
        **(
            {"store_argument_index_owner_only": expected_store_argument}
            if expected_store_argument is not None
            else {}
        ),
    }


def _fnv64(payload: bytes) -> int:
    value = 1469598103934665603
    for byte in payload:
        value = ((value ^ byte) * 1099511628211) & ((1 << 64) - 1)
    return value


def build_field_encryption_observation_model(
    *, proto_model: Mapping[str, Any], runtime_probe: Mapping[str, Any],
    runtime_probe_model_identity: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    from alpha.p43 import FIELD_TRANSFORM_RESULT_SCHEMA, _field_transform_role_inventory

    target = proto_model.get("target")
    probe_target = runtime_probe.get("target")
    probe_policy = runtime_probe.get("policy")
    if (
        proto_model.get("status") != "complete"
        or proto_model.get("full_semantic_verification_complete") is not True
        or not isinstance(target, Mapping)
        or probe_target != target
        or runtime_probe.get("schema") != FIELD_TRANSFORM_RESULT_SCHEMA
        or runtime_probe.get("status") != "runtime-validated"
        or not isinstance(probe_policy, Mapping)
        or probe_policy.get("fresh_runtime_observations_used") is not True
        or probe_policy.get("reference_proto_values_used") is not False
        or not isinstance(runtime_probe_model_identity, Mapping)
        or not isinstance(runtime_probe_model_identity.get("path"), str)
        or type(runtime_probe_model_identity.get("bytes")) is not int
        or not isinstance(runtime_probe_model_identity.get("sha256"), str)
        or len(runtime_probe_model_identity.get("sha256", "")) != 64
    ):
        raise AcquisitionError("field-encryption probe is incomplete or bound to another runtime")
    executable_sha256 = target.get("executable_sha256")
    if (
        not isinstance(executable_sha256, str) or len(executable_sha256) != 64
        or any(char not in "0123456789abcdef" for char in executable_sha256)
    ):
        raise AcquisitionError("field-encryption target executable identity is invalid")
    messages = proto_model.get("messages_owner_only")
    enums = proto_model.get("enums_owner_only")
    probe_rows = runtime_probe.get("observations")
    probe_counts = runtime_probe.get("counts")
    if (
        not isinstance(messages, list) or not isinstance(enums, list)
        or not isinstance(probe_rows, list) or not isinstance(probe_counts, Mapping)
    ):
        raise AcquisitionError("field-encryption current-runtime inventory is incomplete")
    enum_names = _enum_type_names(enums)
    expected = _field_transform_role_inventory(proto_model)
    if (
        not _nonnegative_count(probe_counts.get("required"))
        or not _nonnegative_count(probe_counts.get("verified"))
        or not _nonnegative_count(probe_counts.get("failed"))
        or probe_counts.get("required") != len(expected)
        or probe_counts.get("verified") != len(expected)
        or probe_counts.get("failed") != 0
    ):
        raise AcquisitionError("field-encryption runtime probe counts do not close")
    messages_by_index = {
        message["type_index_owner_only"]: message for message in messages
        if isinstance(message, Mapping)
        and type(message.get("type_index_owner_only")) is int
    }
    normalized_expected: dict[tuple[int, int, str, str], dict[str, Any]] = {}
    for identity in expected:
        key = tuple(identity[name] for name in (
            "type_index_owner_only", "number", "container", "role"
        ))
        owner = identity["type_index_owner_only"]
        message = messages_by_index.get(owner)
        if message is None:
            raise AcquisitionError("field-encryption message identity is absent")
        container = identity["container"]
        if container == "field":
            fields = message.get("fields")
            field_index = None
        else:
            oneof = next((row for row in message.get("oneofs", [])
                          if container == "oneof:" + str(row.get("name"))), None)
            if not isinstance(oneof, Mapping):
                raise AcquisitionError("field-encryption oneof identity is absent")
            fields = oneof.get("cases")
            field_index = oneof.get("storage_field_index_owner_only")
        if not isinstance(fields, list):
            raise AcquisitionError("field-encryption field inventory is invalid")
        matches = [field for field in fields if isinstance(field, Mapping)
                   and field.get("number") == identity["number"]]
        if len(matches) != 1:
            raise AcquisitionError("field-encryption field identity is ambiguous")
        field = matches[0]
        if field_index is None:
            field_index = field.get("field_index_owner_only")
        actual = _numeric_role(field.get(identity["role"]), enum_names)
        if (
            type(field_index) is not int or field_index < 0
            or actual != (identity["encoding"], identity["width"])
            or not isinstance(message.get("name"), str)
            or not isinstance(field.get("name"), str)
        ):
            raise AcquisitionError("field-encryption current proto role differs from runtime schema")
        normalized_expected[key] = {
            **identity,
            "message_type_index_owner_only": owner,
            "field_index_owner_only": field_index,
            "message_name": message.get("name"),
            "field_name": field.get("name"),
            "parser_body_transfers_owner_only": (
                copy_json_value(field.get("parser_body_transfers_owner_only"))
                if isinstance(field.get("parser_body_transfers_owner_only"), list)
                else None
            ),
        }
    observed: dict[tuple[int, int, str, str], Mapping[str, Any]] = {}
    for row in probe_rows:
        if not isinstance(row, Mapping) or not isinstance(row.get("identity"), Mapping):
            raise AcquisitionError("field-encryption runtime probe row is malformed")
        identity = row["identity"]
        key = tuple(identity.get(name) for name in (
            "type_index_owner_only", "number", "container", "role"
        ))
        if key in observed or key not in normalized_expected:
            raise AcquisitionError("field-encryption runtime probe role domain differs")
        expected_row = normalized_expected[key]
        if (
            identity != {name: expected_row[name] for name in (
                "type_index_owner_only", "number", "container", "role",
                "cardinality", "width",
            )}
            or row.get("encoding") != expected_row["encoding"]
            or row.get("field_index_owner_only") != expected_row["field_index_owner_only"]
        ):
            raise AcquisitionError("field-encryption runtime probe identity does not match current proto")
        observed[key] = row
    if set(observed) != set(normalized_expected):
        raise AcquisitionError(
            f"field-encryption runtime probe is incomplete "
            f"({len(observed)}/{len(normalized_expected)} numeric roles)"
        )
    field_rows = []
    for key, source in normalized_expected.items():
        probe = observed[key]
        samples = probe.get("samples_owner_only")
        if not isinstance(samples, list):
            raise AcquisitionError("field-encryption runtime samples are absent")
        pairs = []
        retained_samples = []
        for sample in samples:
            if not isinstance(sample, Mapping):
                raise AcquisitionError("field-encryption runtime sample is malformed")
            serialized = sample.get("serialized_value")
            restored = sample.get("runtime_value")
            input_hex = sample.get("input_hex")
            input_fnv64 = sample.get("input_fnv64")
            try:
                payload = bytes.fromhex(input_hex) if isinstance(input_hex, str) else b""
            except ValueError as error:
                raise AcquisitionError("field-encryption input payload is malformed") from error
            if not payload or type(input_fnv64) is not int or _fnv64(payload) != input_fnv64:
                raise AcquisitionError("field-encryption input payload hash differs")
            retained_samples.append({
                "serialized_value": serialized,
                "runtime_value": restored,
                "input_hex": input_hex,
                "input_fnv64": input_fnv64,
            })
            pairs.append((serialized, restored))
        parser_body_evidence = _parser_body_probe_evidence(
            field=source,
            container=str(source["container"]),
            encoding=str(source["encoding"]),
            width=int(source["width"]),
            samples=pairs,
            inferred_ops=None,
        )
        if parser_body_evidence["status"] == "post-call-chain-matches-probes":
            body_ops = parser_body_evidence["ops"]
            classified = (
                {"disposition": "identity"}
                if _equivalent_ops(body_ops, [], int(source["width"]))
                else {"disposition": "encrypted", "ops": body_ops}
            )
            recovery_method = "bounded-parser-body"
        else:
            classified = classify_runtime_field_samples(pairs, int(source["width"]))
            inferred_ops = classified.get("ops", [])
            parser_body_evidence = _parser_body_probe_evidence(
                field=source,
                container=str(source["container"]),
                encoding=str(source["encoding"]),
                width=int(source["width"]),
                samples=pairs,
                inferred_ops=inferred_ops,
            )
            recovery_method = "bounded-sample-model"
        field_rows.append({
            "message_type_index_owner_only": source["message_type_index_owner_only"],
            "field_index_owner_only": source["field_index_owner_only"],
            "field_number": source["number"],
            "container": source["container"],
            "role": source["role"],
            "message_name": source["message_name"],
            "field_name": source["field_name"],
            "encoding": source["encoding"],
            "cardinality": source["cardinality"],
            "width": source["width"],
            **classified,
            "recovery_method": recovery_method,
            "parser_body_evidence_owner_only": parser_body_evidence,
            "samples_owner_only": retained_samples,
        })
    encrypted = sum(row["disposition"] == "encrypted" for row in field_rows)
    parser_body_matches = sum(
        row["parser_body_evidence_owner_only"]["status"]
        == "post-call-chain-matches-probes"
        for row in field_rows
    )
    model = {
        "schema": FIELD_ENCRYPTION_SCHEMA,
        "status": "runtime-validated",
        "target": dict(target),
        "field_observations_owner_only": field_rows,
        "coverage": {
            "complete": True,
            "observed_role_count": len(field_rows),
            "encrypted_field_count": encrypted,
            "identity_field_count": len(field_rows) - encrypted,
            "unresolved_field_count": 0,
        },
        "implementation_evidence_coverage": {
            "numeric_role_count": len(field_rows),
            "post_call_chain_matches_probe_count": parser_body_matches,
            "unresolved_count": len(field_rows) - parser_body_matches,
            "end_to_end_function_proven": False,
        },
        "inputs": {
            "runtime_probe": copy_json_value(runtime_probe.get("inventory")),
            "runtime_probe_model": copy_json_value(runtime_probe_model_identity),
            "probe_status": copy_json_value(runtime_probe.get("status_receipt")),
        },
        "checks": {
            "current_executable_bound": True,
            "runtime_sample_domain_closed": True,
            "all_numeric_proto_roles_classified": True,
            "fallback_sample_models_unique": True,
            "parser_body_evidence_inventory_closed": all(
                isinstance(row.get("parser_body_evidence_owner_only"), Mapping)
                and row["parser_body_evidence_owner_only"].get("status")
                in {"unresolved", "post-call-chain-matches-probes"}
                for row in field_rows
            ),
            "reference_proto_data_excluded": True,
            "runtime_role_inventory_matches_proto_model": True,
            "non_numeric_field_categories_excluded": True,
        },
        "policy": {
            "current_runtime_only": True,
            "reference_proto_values_used": False,
            "fresh_runtime_observations_used": True,
            "all_numeric_proto_roles_required": True,
            "decoder_selection": (
                "shortest-candidate-unique-within-supported-add-xor-model"
            ),
            "decoder_maximum_operations": MAX_SUPPORTED_OPS,
            "adaptive_samples_per_round": ADAPTIVE_SAMPLE_COUNT,
            "maximum_adaptive_rounds": MAX_ADAPTIVE_ROUNDS,
            "excluded_field_categories": list(FIELD_ENCRYPTION_EXCLUDED_CATEGORIES),
            "full_runtime_transform_implementation_proven": False,
            "parser_body_evidence_scope": "message-parser-post-call-standard-reader-store",
        },
        "owner_only": True,
    }
    validate_observation_inventory(
        model,
        executable_sha256=executable_sha256,
        expected_target=target,
    )
    return model


def copy_json_value(value: Any) -> Any:
    if value is None:
        return None
    return json.loads(json.dumps(value, ensure_ascii=False, allow_nan=False))


def require_publishable_field_encryption_model(
    observation_model: Mapping[str, Any],
    observations: Mapping[tuple[int, int, str, str], Mapping[str, Any]],
    *,
    allow_partial: bool = False,
) -> dict[str, Any]:
    evidence = observation_model.get("implementation_evidence_coverage")
    if not isinstance(evidence, Mapping):
        raise AcquisitionError("field-encryption implementation evidence is absent")
    expected_count = len(observations)
    def proven(row: Mapping[str, Any]) -> bool:
        return bool(
            row.get("recovery_method") == "bounded-parser-body"
            and isinstance(row.get("parser_body_evidence_owner_only"), Mapping)
            and row["parser_body_evidence_owner_only"].get("status")
            == "post-call-chain-matches-probes"
        )

    proven_count = sum(proven(row) for row in observations.values())
    deferred_rows = [
        row for row in observations.values() if not proven(row)
    ]
    deferred = [
        {
            "message_type_index_owner_only": row.get(
                "message_type_index_owner_only"
            ),
            "field_number": row.get("field_number"),
            "container": row.get("container"),
            "role": row.get("role"),
            "reason": (
                row.get("parser_body_evidence_owner_only", {}).get("reason")
                if isinstance(
                    row.get("parser_body_evidence_owner_only"), Mapping
                )
                else "parser-body-evidence-absent"
            ),
        }
        for row in deferred_rows
    ]
    summary = {
        "numeric_role_count": expected_count,
        "bounded_parser_body_proven_role_count": proven_count,
        "deferred_role_count": len(deferred),
        "deferred_reason_counts": dict(sorted(Counter(
            str(row["reason"]) for row in deferred
        ).items())),
        "deferred_roles_owner_only": deferred,
    }
    if any(type(evidence.get(name)) is not int or evidence.get(name) != expected
           for name, expected in (
               ("numeric_role_count", expected_count),
               ("post_call_chain_matches_probe_count", proven_count),
               ("unresolved_count", expected_count - proven_count))):
        raise AcquisitionError("field-encryption implementation evidence counts differ")
    if not deferred:
        return summary
    if allow_partial:


        published = [
            row for row in observations.values()
            if row.get("disposition") == "encrypted"
        ]
        if any(not proven(row) for row in published):
            raise AcquisitionError(
                "field-encryption partial output would publish an unproven "
                "encrypted role"
            )
        return summary
    if (
        type(evidence.get("numeric_role_count")) is not int
        or evidence.get("numeric_role_count") != expected_count
        or evidence.get("post_call_chain_matches_probe_count") != proven_count
        or evidence.get("unresolved_count") != expected_count - proven_count
        or proven_count != expected_count
    ):
        unresolved = deferred
        raise AcquisitionError(
            "field-encryption output is withheld because parser implementation "
            "evidence is incomplete for " + str(len(unresolved))
            + " numeric role(s); sample-only candidates are diagnostic, not "
            "publishable. First 20 unresolved roles: "
            + json.dumps(unresolved[:20], sort_keys=True)
            + ". Remaining role details are retained in the private observation model."
        )
    return summary


def render_field_encrypt_document(
    *, proto_messages: Sequence[Mapping[str, Any]],
    observations: Mapping[tuple[int, int, str, str], Mapping[str, Any]],
    enum_type_names: Iterable[str] = (),
) -> dict[str, dict[str, dict[str, Any]]]:
    enum_names = set(enum_type_names)
    message_by_type = {
        int(message["type_index_owner_only"]): message
        for message in proto_messages
        if isinstance(message, Mapping)
        and type(message.get("type_index_owner_only")) is int
    }
    name_owner: dict[str, set[int]] = {}
    expected: dict[
        tuple[int, int, str, str],
        tuple[Mapping[str, Any], Mapping[str, Any], int, str, str, int, str],
    ] = {}

    def add_role(type_index, message, field, container, field_index, role):
        numeric = _numeric_role(field.get(role), enum_names)
        if numeric is None:
            return
        encoding, width = numeric
        key = (type_index, field.get("number"), container, role)
        if (
            type(field_index) is not int or field_index < 0
            or type(field.get("number")) is not int or key in expected
            or not isinstance(field.get("name"), str)
        ):
            raise AcquisitionError("numeric field has no unique current-runtime identity")
        expected[key] = (
            message, field, width, encoding,
            str(field.get("cardinality", "singular")), field_index, role,
        )

    for type_index, message in message_by_type.items():
        message_name = message.get("name")
        if not isinstance(message_name, str) or not message_name:
            raise AcquisitionError("field-encryption message name is invalid")
        name_owner.setdefault(message_name, set()).add(type_index)
        fields = message.get("fields")
        oneofs = message.get("oneofs")
        if not isinstance(fields, list) or not isinstance(oneofs, list):
            raise AcquisitionError("field-encryption proto message members are invalid")
        for field in fields:
            if not isinstance(field, Mapping):
                raise AcquisitionError("field-encryption proto field is invalid")
            cardinality = field.get("cardinality", "singular")
            field_index = field.get("field_index_owner_only")
            roles = ("key_type", "value_type") if cardinality == "map" else ("type",)
            for role in roles:
                add_role(type_index, message, field, "field", field_index, role)
        for oneof in oneofs:
            if not isinstance(oneof, Mapping) or not isinstance(oneof.get("cases"), list):
                raise AcquisitionError("field-encryption proto oneof is invalid")
            container = "oneof:" + str(oneof.get("name"))
            field_index = oneof.get("storage_field_index_owner_only")
            for case in oneof["cases"]:
                if not isinstance(case, Mapping):
                    raise AcquisitionError("field-encryption oneof case is invalid")
                add_role(type_index, message, case, container, field_index, "type")
    if set(observations) != set(expected):
        raise AcquisitionError(
            "field-encryption runtime observation domain differs from numeric proto fields"
        )
    for message_name, type_indexes in name_owner.items():
        if len(type_indexes) <= 1:
            continue
        if any(
            observations[key].get("disposition") == "encrypted"
            for key in expected
            if key[0] in type_indexes
        ):
            raise AcquisitionError(
                "field-encryption format cannot distinguish duplicate current message names"
            )
    document: dict[str, dict[str, dict[str, Any]]] = {}
    seen: set[tuple[int, int, str, str]] = set()
    field_name_rows: dict[
        tuple[int, str], list[tuple[tuple[int, int, str, str], str]]
    ] = {}
    for key, (
        _message, field, _width, _encoding, _cardinality, _field_index, _role,
    ) in expected.items():
        type_index, _number, _container, _role = key
        owner_key = (type_index, str(field.get("name")))
        field_name_rows.setdefault(owner_key, []).append((key, _cardinality))
    for rows in field_name_rows.values():
        distinct_fields = {
            (key[1], key[2]) for key, cardinality in rows
            if cardinality != "map"
        }
        if len(distinct_fields) <= 1:
            continue
        if any(
            observations[key].get("disposition") == "encrypted"
            for key, cardinality in rows if cardinality != "map"
        ):
            raise AcquisitionError(
                "field-encryption format cannot distinguish duplicate current field names"
            )
    for key, row in observations.items():
        if key not in expected or not isinstance(row, Mapping):
            raise AcquisitionError("field-encryption field is outside proto model")
        (
            message, field, expected_width, expected_encoding, cardinality,
            expected_field_index, expected_role,
        ) = expected[key]
        type_index, field_number, container, role = key
        if (
            row.get("message_type_index_owner_only") != type_index
            or row.get("field_index_owner_only") != expected_field_index
            or row.get("field_number") != field_number
            or row.get("container") != container
            or row.get("role") != expected_role
            or row.get("message_name") != message.get("name")
            or row.get("field_name") != field.get("name")
            or row.get("encoding") != expected_encoding
            or row.get("cardinality", "singular") != cardinality
        ):
            raise AcquisitionError(
                "field-encryption observation identity differs from current proto role"
            )
        if row.get("disposition") == "identity":
            continue
        if row.get("disposition") != "encrypted":
            raise AcquisitionError("field-encryption disposition is invalid")
        width = row.get("width")
        ops = row.get("ops")
        if width != expected_width or not isinstance(ops, list):
            raise AcquisitionError("field-encryption output row is invalid")
        if cardinality == "map":
            raise AcquisitionError(
                "the compatible field-encrypt format cannot express separate map key/value transforms"
            )
        name = str(message["name"])
        field_name = str(field["name"])
        message_entry = document.setdefault(name, {})
        if field_name in message_entry:
            raise AcquisitionError("field-encryption output contains duplicate field")
        if row.get("width") != expected_width:
            raise AcquisitionError("field-encryption runtime width differs from proto field")
        message_entry[field_name] = {
            "ops": [
                [operation, str(constant) if width == 64 else constant]
                for operation, constant in ops
            ],
            "w": width,
        }
        seen.add(key)
    encrypted_expected = {
        key for key, row in observations.items()
        if row.get("disposition") == "encrypted"
    }
    if set(observations) != set(expected) or seen != encrypted_expected:
        raise AcquisitionError("field-encryption output field domain differs")
    return {name: fields for name, fields in sorted(document.items())}


def write_field_encrypt_artifact(
    *,
    proto_model: Mapping[str, Any],
    runtime_observation_model: Mapping[str, Any],
    output_path: Path,
    allow_partial: bool = False,
) -> dict[str, Any]:
    target = proto_model.get("target")
    executable_sha256 = (
        target.get("executable_sha256") if isinstance(target, Mapping) else None
    )
    if (
        not isinstance(executable_sha256, str)
        or len(executable_sha256) != 64
        or any(char not in "0123456789abcdef" for char in executable_sha256)
    ):
        raise AcquisitionError("field-encryption proto target is not SHA-256 bound")
    messages = proto_model.get("messages_owner_only")
    enums = proto_model.get("enums_owner_only")
    if not isinstance(messages, list) or not isinstance(enums, list):
        raise AcquisitionError("field-encryption proto model is incomplete")
    from alpha.p02 import validate_runtime_proto_static_model_for_publication

    validate_runtime_proto_static_model_for_publication(proto_model)
    observations = validate_observation_inventory(
        runtime_observation_model,
        executable_sha256=executable_sha256,
        expected_target=target,
    )
    coverage = require_publishable_field_encryption_model(
        runtime_observation_model, observations, allow_partial=allow_partial,
    )
    if any(
        not isinstance(item, Mapping) or not isinstance(item.get("name"), str)
        for item in enums
    ):
        raise AcquisitionError("field-encryption enum type domain is invalid")
    enum_names = _enum_type_names(enums)
    document = render_field_encrypt_document(
        proto_messages=messages,
        observations=observations,
        enum_type_names=enum_names,
    )
    encoded = json.dumps(
        document, ensure_ascii=False, indent=2, sort_keys=True, allow_nan=False
    ) + "\n"
    destination = output_path.expanduser().absolute()
    if destination.exists() or destination.is_symlink():
        raise AcquisitionError("field-encryption artifact destination already exists")
    if not destination.parent.is_dir() or destination.parent.is_symlink():
        raise AcquisitionError("field-encryption artifact directory is unavailable")
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=".field-encrypt-", suffix=".tmp", dir=destination.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
        if destination.exists() or destination.is_symlink():
            raise AcquisitionError("field-encryption artifact destination raced")
        os.replace(temporary, destination)
        saved = json.loads(destination.read_text(encoding="utf-8"))
        if saved != document:
            destination.unlink(missing_ok=True)
            raise AcquisitionError("field-encryption artifact read-back differs")
    finally:
        temporary.unlink(missing_ok=True)
    from alpha.h02 import file_identity

    deferred_role_count = int(coverage.get("deferred_role_count") or 0)
    status = "partial" if deferred_role_count else "complete"
    return {
        "schema": "alpha.runtime-field-encrypt-artifact/v2",
        "status": status,
        "artifact": file_identity(destination),
        "implementation_evidence_coverage": {
            "numeric_role_count": len(observations),
            "bounded_parser_body_proven_role_count": (
                coverage.get("bounded_parser_body_proven_role_count")
            ),
            "unresolved_role_count": deferred_role_count,
            "deferred_role_count": deferred_role_count,
            "deferred_reason_counts": dict(
                coverage.get("deferred_reason_counts") or {}
            ),
            "deferred_roles_owner_only": list(
                coverage.get("deferred_roles_owner_only") or []
            ),
            "end_to_end_function_proven": False,
        },
        "counts": {
            "numeric_field_count": len({
                (row["message_type_index_owner_only"], row["field_number"], row["container"])
                for row in observations.values()
            }),
            "numeric_role_count": len(observations),
            "encrypted_field_count": len({
                (row["message_type_index_owner_only"], row["field_number"], row["container"])
                for row in observations.values() if row.get("disposition") == "encrypted"
            }),
            "encrypted_role_count": sum(
                row.get("disposition") == "encrypted" for row in observations.values()
            ),
            "identity_role_count": sum(
                row.get("disposition") == "identity" for row in observations.values()
            ),
        },
        "checks": {
            "current_executable_bound": True,
            "runtime_sample_domain_closed": True,
            "all_numeric_proto_roles_classified": True,
            "fallback_sample_models_unique": True,

            "all_published_encrypted_roles_proven": True,
            "deferred_roles_recorded_owner_only": (
                deferred_role_count
                == len(coverage.get("deferred_roles_owner_only") or [])
            ),
            "non_numeric_field_categories_excluded": True,
            "reference_proto_names_or_values_excluded": True,
            "output_matches_validated_document": True,
        },
        "excluded_field_categories": list(FIELD_ENCRYPTION_EXCLUDED_CATEGORIES),
        "proof_scope": "bounded-parser-body-crosschecked-by-fresh-runtime-probes",
        "full_runtime_transform_implementation_proven": False,
    }
