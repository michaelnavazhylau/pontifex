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
    namespace: str = "PyVerif.Generated",
    fuel: int = 64,
    conformance: Sequence[tuple[Sequence[Fraction], Sequence[Fraction]]] = (),
    generator: str = "python -m pyverif compile",
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
        generator=f"python -m pyverif compile {path}",
    )


def default_namespace(stem: str) -> str:
    parts = "".join(p.capitalize() for p in stem.replace("-", "_").split("_"))
    return f"PyVerif.Generated.{parts}"


# ---------------------------------------------------------------------------
# The Python source as an oracle
# ---------------------------------------------------------------------------


def load_python_function(source: str, name: str, filename: str = "<string>") -> Callable[..., Any]:
    """Execute the *original* module and return the requested function object.

    Used as the ground truth in differential testing: the translated IR must
    agree with what Python actually computes.
    """
    namespace: dict[str, Any] = {"__name__": "pyverif_oracle", "__file__": filename}
    exec(compile(source, filename, "exec"), namespace)  # noqa: S102 - deliberate
    return namespace[name]


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
        candidates.append(root / ".lake" / "build" / "bin" / "pyverif")
    env = os.environ.get("PYVERIF_EXE")
    if env:
        candidates.insert(0, Path(env))
    here = Path(__file__).resolve().parent.parent
    candidates.append(here / ".lake" / "build" / "bin" / "pyverif")
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
    """Run the Lean reference semantics through the ``pyverif`` executable."""
    with tempfile.TemporaryDirectory(prefix="pyverif-") as tmp:
        ir_path = Path(tmp) / "ir.json"
        inputs_path = Path(tmp) / "inputs.json"
        ir_path.write_text(ir_json_text)
        inputs_path.write_text(json.dumps([_wire_rats(v) for v in inputs]))
        proc = subprocess.run(
            [str(exe), mode, str(ir_path), str(inputs_path), str(fuel)],
            capture_output=True,
            text=True,
            check=False,
        )
    if proc.returncode != 0:
        raise RuntimeError(f"pyverif exe failed ({proc.returncode}): {proc.stderr}")
    payload = json.loads(proc.stdout)
    return [_decode_outcome(item) for item in payload]


def _decode_outcome(item: dict[str, Any]) -> Outcome:
    from .interp import FellThrough, OutOfFuel

    kind = item["kind"]
    if kind == "outOfFuel":
        return OutOfFuel()
    if kind == "fellThrough":
        return FellThrough({})
    values = item["vals"]
    if values and isinstance(values[0], str) and values[0].startswith("0x"):
        return Returned(tuple(_bits_to_float(v) for v in values))
    return Returned(tuple(_parse_rat_string(v) for v in values))


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


def compare_outcomes(
    left: Outcome, right: Outcome
) -> str | None:
    """Return ``None`` when two outcomes agree, else a short explanation."""
    lv, rv = to_option(left), to_option(right)
    if lv is None or rv is None:
        if type(left) is type(right):
            return None
        return f"termination mismatch: {type(left).__name__} vs {type(right).__name__}"
    if len(lv) != len(rv):
        return f"arity mismatch: {lv} vs {rv}"
    for i, (a, b) in enumerate(zip(lv, rv)):
        if isinstance(a, float) or isinstance(b, float):
            import struct as _s

            if _s.pack("<d", float(a)) != _s.pack("<d", float(b)):
                return f"value {i}: {a!r} vs {b!r} (bit-level)"
        elif Fraction(a) != Fraction(b):
            return f"value {i}: {a!r} vs {b!r}"
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
