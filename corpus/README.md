# Differential corpus

Each program is a self-contained module with a selected entry point in the
verified Python subset (and optionally bounded scalar helpers). The runner compiles it once and compares, on deterministic sampled inputs:

1. CPython execution of the source,
2. the exact / binary64 reference interpreters over the emitted IR, and
3. the Lean reference semantics via `lake exe pontifex`.

Exact runs use `Fraction`; binary64 runs compare bit patterns.

```bash
python scripts/run_corpus.py --samples 32
python scripts/run_corpus.py --samples 8 --verbose
```

## Adding a program

Create `programs/<name>.py` with an entry-point function, then add an entry to
`manifest.json` naming that function. Bounded white-box scalar helpers may share
the module (`call_step.py`, `call_loop.py`, `call_failure.py`); see
[`docs/CALLS.md`](../docs/CALLS.md). No test code is required: the pytest suite iterates the
manifest.

```json
{
  "file": "my_step.py",
  "function": "step",
  "fuel": 64,
  "params": [
    {"kind": "rat", "min": -8, "max": 8},
    {"kind": "positive", "min": 1, "max": 4, "dens": [1, 2, 4, 8]}
  ]
}
```

Parameter kinds:

| kind | meaning |
| --- | --- |
| `rat` | numerator in `[min, max]`, denominator from `dens` (default `[1, 2, 4]`) |
| `positive` | same, forced non-zero (use for divisors and time steps) |
| `nonnegative` | same, absolute value (use for end times) |
| `nat` | integer in `[0, max]` (use for loop counters) |

Constraints must guarantee termination and stay within the structured fuel
budget. Division by zero is now an explicit compared outcome, not an excluded
input. Source exceptions map to the same `Failed` constructors as both IR
interpreters. Use `positive` when a program needs a nonzero divisor for its
algorithm rather than to hide failures.

Array programs are welcome. Keep index expressions integer-valued in CPython
(loop counters and literals, not `float`/`Fraction` parameters): Python rejects
non-integer list indices with `TypeError` while the IR reads an integral scalar
as an index, so a parameter-driven fractional index would compare a Python type
error against an IR bounds failure. Out-of-range integer indices are fine and
are compared as the shared `indexOutOfBounds` failure (`vector_step.py`,
`array_read_bounds.py`, `array_store_bounds.py`).

Scalar-selection programs (`limited_step.py`, `safe_ratio.py`,
`selection_loop.py`) cover eager two-argument `min`/`max` and lazy conditional
expressions, including protected division and selection within control flow.
See [`docs/SELECTION.md`](../docs/SELECTION.md). NaN/signed-zero/tie selection
is covered separately by the bit-exact boundary corpus below.

## Binary64 boundary corpus

`make float-boundaries` runs 100,000 fixed-seed random bit patterns and explicit
IEEE edge cases through CPython, Python IR, and Lean. Raw wire transport,
literals, sign operations, and `min`/`max`/conditional operand selection are
bit-exact, including NaN payloads. Arithmetic
may canonicalize computed NaNs: `float_allowlist.json` permits payload/sign
differences only when both results are NaN; finite differences and failures are
never exempt. See `docs/FLOAT_POLICY.md` for the precise tested/proved policy.

## Allowlist

A known boundary mismatch is allowed only via `allowlist.json`, which records
the program, mode (`exact`, `rat`, or `float`), and a reason. The runner reports
allowlist entries that were not exercised, so stale exemptions are visible.
