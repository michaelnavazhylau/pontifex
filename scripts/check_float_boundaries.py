#!/usr/bin/env python3
"""Bit-exact CPython ↔ Python IR ↔ Lean boundary corpus.

Default: 100,000 deterministic random binary64 patterns plus explicit edge
patterns. All identity transport must preserve bits (including NaN payloads).
Arithmetic has one narrowly defined, reported allowlist: computed NaN payloads.
No finite mismatch or mismatched failure can be allowlisted.

    uv run python scripts/check_float_boundaries.py
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import random
import struct
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))

from pontifex.frontend import translate
from pontifex.interp import Returned, float_bits, run_float
from pontifex.pipeline import (
    compare_outcomes,
    find_lean_exe,
    load_python_function,
    observe_python,
    run_lean,
)

EDGE_BITS = [
    0x0000000000000000,
    0x8000000000000000,  # both zero signs
    0x0000000000000001,
    0x8000000000000001,  # smallest subnormals
    0x000FFFFFFFFFFFFF,
    0x800FFFFFFFFFFFFF,  # largest subnormals
    0x0010000000000000,
    0x8010000000000000,  # smallest normals
    0x7FEFFFFFFFFFFFFF,
    0xFFEFFFFFFFFFFFFF,  # largest finite
    0x3FF0000000000000,
    0xBFF0000000000000,  # +/-1
    0x3FF0000000000001,
    0x3FEFFFFFFFFFFFFF,  # neighbors of 1
    0x7FF0000000000000,
    0xFFF0000000000000,  # infinities
    0x7FF8000000000000,
    0xFFF8000000000001,  # quiet NaN payload/sign
    0x7FF0000000000001,
    0xFFF0000000000042,  # signaling NaNs
]


# These operations select/transport existing operands; even NaN payload/sign
# differences are bugs, not computed-NaN arithmetic exemptions.
BIT_EXACT_PROGRAMS = frozenset({"identity", "literal", "abs_neg", "min", "max", "select"})


def from_bits(bits):
    return struct.unpack(">d", struct.pack(">Q", bits))[0]


def permitted_nan_difference(expected, actual, *, transport, allow_nan):
    if transport or not allow_nan:
        return False
    if not isinstance(expected, Returned) or not isinstance(actual, Returned):
        return False
    if len(expected.values) != len(actual.values):
        return False
    return all(
        float_bits(a) == float_bits(b) or (math.isnan(a) and math.isnan(b))
        for a, b in zip(expected.values, actual.values)
    )


def check(samples=100000, arithmetic=4096, exe=None):
    exe = exe or find_lean_exe(ROOT)
    if exe is None:
        raise RuntimeError("build the Lean runner with `lake build` first")
    rng = random.Random(0x50595645524946)
    values = [from_bits(b) for b in EDGE_BITS]
    values.extend(from_bits(rng.getrandbits(64)) for _ in range(samples))
    edge_pairs = [[from_bits(x), from_bits(y)] for x in EDGE_BITS for y in EDGE_BITS]
    pairs = edge_pairs + [[rng.choice(values), rng.choice(values)] for _ in range(arithmetic)]
    unary = [[v] for v in values[: arithmetic + len(EDGE_BITS)]]
    programs = [
        ("identity", "def f(x):\n    return x\n", [[v] for v in values]),
        ("add", "def f(x, y):\n    return x + y\n", pairs),
        ("sub", "def f(x, y):\n    return x - y\n", pairs),
        ("mul", "def f(x, y):\n    return x * y\n", pairs),
        ("div", "def f(x, y):\n    return x / y\n", pairs),
        ("min", "def f(x, y):\n    return min(x, y)\n", pairs),
        ("max", "def f(x, y):\n    return max(x, y)\n", pairs),
        ("select", "def f(x, y):\n    return x if x < y else y\n", pairs),
        ("power", "def f(x):\n    return x ** 3\n", unary),
        ("power_zero", "def f(x):\n    return x ** 0\n", unary),
        ("abs_neg", "def f(x):\n    return abs(x), -x\n", unary),
        (
            "comparisons",
            "def f(x, y):\n    r = 0\n    if x == y:\n        r = 1\n    if x != y:\n        r = 2\n    if x < y:\n        r = 3\n    if x <= y:\n        r = 4\n    if x > y:\n        r = 5\n    if x >= y:\n        r = 6\n    return r\n",
            pairs,
        ),
    ]
    # Test decimal spelling -> AST -> exact rational + original bits -> Lean.
    for bits in EDGE_BITS:
        value = from_bits(bits)
        if math.isfinite(value):
            programs.append(("literal", f"def f():\n    return {value!r}\n", [[]]))
    allowlist = json.loads((ROOT / "corpus" / "float_allowlist.json").read_text())["allow"]
    rules = {item["rule"]: item["reason"] for item in allowlist}
    unknown = set(rules) - {"computed_nan_payload"}
    if unknown:
        raise ValueError(f"unknown Float allowlist rules: {unknown}")
    mismatches = []
    mismatch_count = 0
    allowed = 0
    count = 0
    for name, source, vectors in programs:
        fn = translate(source).fn
        python_fn = load_python_function(source, fn.name)
        lean_results = run_lean(exe, fn.to_json_text(), vectors, mode="float", fuel=128)
        if len(lean_results) != len(vectors):
            raise AssertionError("Lean returned the wrong number of observations")
        for index, (args, lean) in enumerate(zip(vectors, lean_results)):
            python = observe_python(python_fn, args)
            ir = run_float(fn, args, fuel=128)
            for label, actual in [("IR", ir), ("Lean", lean)]:
                count += 1
                diff = compare_outcomes(python, actual)
                if diff is None:
                    continue
                if permitted_nan_difference(
                    python,
                    actual,
                    transport=name in BIT_EXACT_PROGRAMS,
                    allow_nan="computed_nan_payload" in rules,
                ):
                    allowed += 1
                else:
                    mismatch_count += 1
                    if len(mismatches) < 20:
                        mismatches.append(
                            f"{name}[{index}] {label}, args bits={[float_bits(a) for a in args]}: {diff}"
                        )
        if name != "literal":
            print(f"{name}: {len(vectors)} vectors")
    print(
        f"Float boundaries: {count} comparisons; {mismatch_count} mismatches; {allowed} allowlisted"
    )
    for rule, reason in rules.items():
        print(f"  allowlist {rule}: {reason}")
    for mismatch in mismatches:
        print("  FAIL " + mismatch)
    return mismatch_count == 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=100000)
    parser.add_argument("--arithmetic", type=int, default=4096)
    args = parser.parse_args(argv)
    if args.samples < 0 or args.arithmetic < 0:
        parser.error("sample counts must be nonnegative")
    return 0 if check(args.samples, args.arithmetic) else 1


if __name__ == "__main__":
    raise SystemExit(main())
