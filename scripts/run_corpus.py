#!/usr/bin/env python3
"""Differential corpus runner (P0/T4).

Each program in ``corpus/manifest.json`` is compiled once, then compared across
three implementations on deterministic sampled inputs:

* the original Python function (CPython),
* the reference interpreter over the emitted IR (exact and binary64),
* the Lean reference semantics through ``lake exe pontifex``.

Exact runs use ``Fraction``; float runs compare IEEE-754 bit patterns.  A known
boundary mismatch must be explicitly allowlisted in ``corpus/allowlist.json``
with a reason; nothing is skipped silently.

    python scripts/run_corpus.py --samples 32
    python scripts/run_corpus.py --samples 8 --verbose
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from dataclasses import dataclass, field
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))

from pontifex.errors import InterpreterError, PontifexError  # noqa: E402
from pontifex.interp import (  # noqa: E402
    run_exact,
    run_float,
    to_option,
)
from pontifex.pipeline import (  # noqa: E402
    compile_file,
    compare_outcomes,
    find_lean_exe,
    run_lean,
    load_python_function,
    observe_python,
)

CORPUS = ROOT / "corpus"


@dataclass
class Failure:
    program: str
    mode: str
    detail: str


@dataclass
class Stats:
    programs: int = 0
    samples: int = 0
    comparisons: int = 0
    allowlisted: int = 0
    failures: list[Failure] = field(default_factory=list)


def load_manifest() -> list[dict]:
    return json.loads((CORPUS / "manifest.json").read_text())["programs"]


def load_allowlist() -> dict[tuple[str, str], str]:
    payload = json.loads((CORPUS / "allowlist.json").read_text())
    return {(item["program"], item["mode"]): item["reason"] for item in payload["allow"]}


def sample_value(spec: dict, rng: random.Random) -> Fraction:
    kind = spec.get("kind", "rat")
    if kind == "nat":
        return Fraction(rng.randint(0, int(spec.get("max", 10))))
    low = int(spec.get("min", -8))
    high = int(spec.get("max", 8))
    denominator = rng.choice(spec.get("dens", [1, 2, 4]))
    if kind in {"positive", "nonnegative"}:
        value = Fraction(abs(rng.randint(low, high)), denominator)
        if kind == "positive" and value == 0:
            value = Fraction(1, denominator)
        return value
    return Fraction(rng.randint(low, high), denominator)


def sample_vectors(entry: dict, count: int) -> list[list[Fraction]]:
    rng = random.Random(entry["file"])
    return [
        [sample_value(spec, rng) for spec in entry["params"]]
        for _ in range(count)
    ]


def _values(outcome):
    values = to_option(outcome)
    return None if values is None else tuple(values)



def run(samples: int, exe: Path, verbose: bool) -> Stats:
    stats = Stats()
    allow = load_allowlist()
    used_allow: set[tuple[str, str]] = set()

    for entry in load_manifest():
        name = entry["file"]
        program = name.removesuffix(".py")
        path = CORPUS / "programs" / name
        fuel = int(entry.get("fuel", 128))
        artifacts = compile_file(path, function=entry["function"], fuel=fuel)
        fn = artifacts.fn
        if fn.arity != len(entry["params"]):
            raise SystemExit(
                f"{name}: manifest has {len(entry['params'])} params, function has {fn.arity}"
            )
        vectors = sample_vectors(entry, samples)
        stats.programs += 1
        stats.samples += len(vectors)

        source = path.read_text()
        source_fn = load_python_function(source, fn.name, str(path))
        source_results = [observe_python(source_fn, args) for args in vectors]
        source_float_results = [
            observe_python(source_fn, [float(a) for a in args]) for args in vectors
        ]

        exact_ir = [run_exact(fn, args, fuel=fuel) for args in vectors]
        float_ir = [run_float(fn, args, fuel=fuel) for args in vectors]
        lean_rat = run_lean(exe, artifacts.ir_json, vectors, mode="rat", fuel=fuel)
        lean_float = run_lean(exe, artifacts.ir_json, vectors, mode="float", fuel=fuel)

        checks: dict[str, list[str]] = {"exact": [], "float": [], "rat": []}
        for i, args in enumerate(vectors):
            exact_values = _values(exact_ir[i])
            if compare_outcomes(source_results[i], exact_ir[i]) is not None:
                checks["exact"].append(
                    f"sample {i} args={args}: python={source_results[i]} ir={exact_values}"
                )
            difference = compare_outcomes(exact_ir[i], lean_rat[i])
            if difference is not None:
                checks["rat"].append(f"sample {i} args={args}: {difference}")
            float_values = _values(float_ir[i])
            if compare_outcomes(source_float_results[i], float_ir[i]) is not None:
                checks["float"].append(
                    f"sample {i} args={args}: python={source_float_results[i]} ir={float_values}"
                )
            difference = compare_outcomes(float_ir[i], lean_float[i])
            if difference is not None:
                checks["float"].append(f"sample {i} args={args}: {difference}")

        line = f"{program:<26} {len(vectors):>3} samples"
        for mode in ("exact", "rat", "float"):
            stats.comparisons += len(vectors) * (2 if mode == "float" else 1)
            failures = checks[mode]
            if failures and (program, mode) in allow:
                stats.allowlisted += len(failures)
                used_allow.add((program, mode))
                line += f"  {mode}: allowlisted"
            elif failures:
                stats.failures.append(Failure(program, mode, failures[0]))
                line += f"  {mode}: FAIL"
            else:
                line += f"  {mode}: ok"
        print(line)

    stale_allow = sorted(set(allow) - used_allow)
    print(
        f"\nSUMMARY: {stats.programs} programs, {stats.samples} samples, "
        f"{stats.comparisons} comparisons, {len(stats.failures)} mismatches, "
        f"{stats.allowlisted} allowlisted"
    )
    for failure in stats.failures:
        print(f"  FAIL {failure.program} [{failure.mode}]: {failure.detail}")
    for program, mode in stale_allow:
        print(f"  note: allowlist entry for {program} [{mode}] was not exercised")
    return stats


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=32, help="input vectors per program")
    parser.add_argument("--exe", type=Path, default=None, help="Lean runner path")
    parser.add_argument("--verbose", action="store_true", help="print allowlist reasons")
    args = parser.parse_args(argv)

    exe = args.exe or find_lean_exe(ROOT)
    if exe is None or not Path(exe).exists():
        print("error: Lean runner not built (run `lake build pontifex`)", file=sys.stderr)
        return 2
    try:
        stats = run(args.samples, Path(exe), args.verbose)
    except (InterpreterError, PontifexError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0 if not stats.failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
