"""End-to-end pipeline helpers: source -> IR -> Lean, plus oracle calls."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable, Iterable, Sequence

from .emit import emit_module
from .frontend import Translated, translate
from .interp import (
    Interpreter,
    Outcome,
    Returned,
    DEFAULT_FUEL,
    rat_string,
    run_exact,
    run_float,
    to_option,
)


@dataclass
class Artifacts:
    translated: Translated
    lean_source: str
    ir_json: str

    @property
    def fn(self):
        return self.translated.fn


def compile_source(
    source: str,
    *,
    filename: str = "<string>",
    function: str | None = None,
    namespace: str = "Pontifex.Generated",
    fuel: int = 64,
    conformance: Sequence[tuple[Sequence[Fraction], Sequence[Fraction]]] = (),
    generator: str = "python -m pontifex compile",
) -> Artifacts:
    translated = translate(source, filename=filename, function=function)
    lean = emit_module(
        translated,
        namespace=namespace,
        fuel=fuel,
        conformance=conformance,
        generator=generator,
    )
    return Artifacts(translated=translated, lean_source=lean, ir_json=translated.fn.to_json_text())


def compile_file(
    path: str | Path,
    *,
    function: str | None = None,
    namespace: str | None = None,
    fuel: int = 64,
    conformance: Sequence[tuple[Sequence[Fraction], Sequence[Fraction]]] = (),
) -> Artifacts:
    path = Path(path)
    source = path.read_text()
    ns = namespace or default_namespace(path.stem)
    return compile_source(
        source,
        filename=str(path),
        function=function,
        namespace=ns,
        fuel=fuel,
        conformance=conformance,
        generator=f"python -m pontifex compile {path}" + (f" --function {function}" if function else ""),
    )


def default_namespace(stem: str) -> str:
    parts = "".join(p.capitalize() for p in stem.replace("-", "_").split("_"))
    return f"Pontifex.Generated.{parts}"


# ---------------------------------------------------------------------------
# The Python source as an oracle
# ---------------------------------------------------------------------------


def load_python_function(source: str, name: str, filename: str = "<string>") -> Callable[..., Any]:
    """Execute the *original* module and return the requested function object.

    Used as the ground truth in differential testing: the translated IR must
    agree with what Python actually computes.
    """
    namespace: dict[str, Any] = {"__name__": "pontifex_oracle", "__file__": filename}
    exec(compile(source, filename, "exec"), namespace)  # noqa: S102 - deliberate
    return namespace[name]


def observe_python(fn: Callable[..., Any], args: Sequence[Any]) -> Outcome:
    """Map supported CPython outcomes to the same observable language results."""
    from .interp import Failed
    try:
        value = fn(*args)
        return Returned(value if isinstance(value, tuple) else (value,))
    except ZeroDivisionError:
        return Failed("divisionByZero")
    except OverflowError:
        return Failed("overflow")
    except IndexError:
        return Failed("indexOutOfBounds")
    except TypeError as exc:
        # The only subscript site in the subset is ``xs[i]``; CPython raises
        # TypeError for a non-integer index, which the IR maps to the same
        # defined bounds failure.
        if "index" in str(exc) or "indices" in str(exc):
            return Failed("indexOutOfBounds")
        raise


def run_python_source(
    source: str,
    name: str,
    args: Sequence[Any],
    *,
    filename: str = "<string>",
) -> Any:
    fn = load_python_function(source, name, filename)
    return fn(*args)


# ---------------------------------------------------------------------------
# Lean oracle
# ---------------------------------------------------------------------------


def find_lean_exe(root: Path | None = None) -> Path | None:
    """Locate the built conformance runner."""
    candidates: list[Path] = []
    if root is not None:
        candidates.append(root / ".lake" / "build" / "bin" / "pontifex")
    env = os.environ.get("PONTIFEX_EXE")
    if env:
        candidates.insert(0, Path(env))
    here = Path(__file__).resolve().parent.parent
    candidates.append(here / ".lake" / "build" / "bin" / "pontifex")
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return None


def _wire_rats(args: Sequence[Any]) -> list[str]:
    out = []
    for a in args:
        f = Fraction(a)
        out.append(rat_string(f))
    return out


def run_lean(
    exe: Path,
    ir_json_text: str,
    inputs: Sequence[Sequence[Any]],
    *,
    mode: str = "rat",
    fuel: int = DEFAULT_FUEL,
) -> list[Outcome]:
    """Run the Lean reference semantics through the ``pontifex`` executable."""
    with tempfile.TemporaryDirectory(prefix="pontifex-") as tmp:
        ir_path = Path(tmp) / "ir.json"
        inputs_path = Path(tmp) / "inputs.json"
        ir_path.write_text(ir_json_text)
        if mode == "float":
            from .interp import float_bits
            wire = [[float_bits(float(v)) for v in row] for row in inputs]
        elif mode == "rat":
            wire = [_wire_rats(v) for v in inputs]
        else:
            raise ValueError(f"unknown numeric mode {mode!r}")
        inputs_path.write_text(json.dumps(wire))
        proc = subprocess.run(
            [str(exe), mode, str(ir_path), str(inputs_path), str(fuel)],
            capture_output=True,
            text=True,
            check=False,
        )
    if proc.returncode != 0:
        raise RuntimeError(f"pontifex exe failed ({proc.returncode}): {proc.stderr}")
    payload = json.loads(proc.stdout)
    return [_decode_outcome(item) for item in payload]


def _decode_outcome(item: dict[str, Any]) -> Outcome:
    from .interp import FellThrough, OutOfFuel, Failed, Stuck

    kind = item["kind"]
    if kind == "failed":
        return Failed(item["error"])
    if kind == "stuck":
        return Stuck()
    if kind == "outOfFuel":
        return OutOfFuel()
    if kind == "fellThrough":
        return FellThrough({
            i: _decode_value(value)
            for i, value in enumerate(item["slots"]) if value is not None
        })
    return Returned(tuple(_decode_value(v) for v in item["vals"]))


def _decode_value(value: Any) -> Any:
    """One wire value: scalar text or a nested array of scalar texts."""
    if isinstance(value, list):
        return [_decode_value(v) for v in value]
    if isinstance(value, str) and value.startswith("0x"):
        return _bits_to_float(value)
    return _parse_rat_string(value)


def _parse_rat_string(text: str) -> Fraction:
    if "/" in text:
        num, den = text.split("/")
        return Fraction(int(num), int(den))
    return Fraction(int(text))


def _bits_to_float(text: str) -> float:
    import struct

    bits = int(text, 16)
    (value,) = struct.unpack("<d", struct.pack("<Q", bits))
    return value


def _compare_values(a: Any, b: Any) -> str | None:
    """Compare one scalar or array value; bit-level for floats."""
    if isinstance(a, (list, tuple)) or isinstance(b, (list, tuple)):
        if type(a) is not type(b):
            return f"value kind mismatch: {a!r} vs {b!r}"
        if len(a) != len(b):
            return f"array length mismatch: {len(a)} vs {len(b)}"
        for i, (x, y) in enumerate(zip(a, b)):
            difference = _compare_values(x, y)
            if difference is not None:
                return f"element {i}: {difference}"
        return None
    if isinstance(a, float) or isinstance(b, float):
        import struct as _s

        if _s.pack("<d", float(a)) != _s.pack("<d", float(b)):
            return f"value {a!r} vs {b!r} (bit-level)"
        return None
    if Fraction(a) != Fraction(b):
        return f"value {a!r} vs {b!r}"
    return None


def compare_outcomes(
    left: Outcome, right: Outcome
) -> str | None:
    """Return ``None`` when two outcomes agree, else a short explanation."""
    lv, rv = to_option(left), to_option(right)
    if lv is None or rv is None:
        from .interp import Failed, FellThrough
        if type(left) is type(right):
            if isinstance(left, Failed) and left.error != right.error:
                return f"failure mismatch: {left.error} vs {right.error}"
            if isinstance(left, FellThrough):
                if left.env.keys() != right.env.keys():
                    return "environment slot mismatch"
                for slot in sorted(left.env):
                    difference = _compare_values(left.env[slot], right.env[slot])
                    if difference is not None:
                        return f"slot {slot}: {difference}"
            return None
        return f"termination mismatch: {type(left).__name__} vs {type(right).__name__}"
    if len(lv) != len(rv):
        return f"arity mismatch: {lv} vs {rv}"
    for i, (a, b) in enumerate(zip(lv, rv)):
        difference = _compare_values(a, b)
        if difference is not None:
            return f"value {i}: {difference}"
    return None


# ---------------------------------------------------------------------------
# Conformance samples
# ---------------------------------------------------------------------------


def default_samples(fn) -> list[tuple[Fraction, ...]]:
    """A small deterministic set of exact rational inputs for conformance checks."""
    base = [Fraction(0), Fraction(1), Fraction(-1), Fraction(1, 2), Fraction(3, 7)]
    samples: list[tuple[Fraction, ...]] = []
    for k in range(min(3, max(1, fn.arity))):
        args = []
        for i in range(fn.arity):
            args.append(base[(i + k) % len(base)])
        samples.append(tuple(args))
    return samples


def conformance_pairs(artifacts: Artifacts, samples: Iterable[Sequence[Fraction]] | None = None):
    """Compute expected outputs with the exact IR interpreter."""
    fn = artifacts.fn
    inputs = list(samples) if samples is not None else default_samples(fn)
    pairs = []
    for args in inputs:
        out = run_exact(fn, args)
        if isinstance(out, Returned):
            pairs.append((tuple(args), out.values))
    return pairs
