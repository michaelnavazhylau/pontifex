# Differential corpus

Each program is a self-contained function in the verified Python subset. The
runner compiles it once and compares, on deterministic sampled inputs:

1. CPython execution of the source,
2. the exact / binary64 reference interpreters over the emitted IR, and
3. the Lean reference semantics via `lake exe pyverif`.

Exact runs use `Fraction`; binary64 runs compare bit patterns.

```bash
python scripts/run_corpus.py --samples 32
python scripts/run_corpus.py --samples 8 --verbose
```

## Adding a program

Create `programs/<name>.py` with exactly one function, then add an entry to
`manifest.json`. No test code is required: the pytest suite iterates the
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

Constraints must guarantee termination, avoid division by zero, and keep loop
iterations below `fuel` (loops consume one unit per iteration).

## Allowlist

A known boundary mismatch is allowed only via `allowlist.json`, which records
the program, mode (`exact`, `rat`, or `float`), and a reason. The runner reports
allowlist entries that were not exercised, so stale exemptions are visible.
