# Rejection snapshots

Each `cases/*.py` must be rejected with the exact class, message, and location
committed in `expected/*.error`. Regenerate with `make rejections` after
reviewing a diagnostic change; `make check` checks freshness.

`functions.json` optionally selects an entry point (the CLI's `--function`)
for a multi-function case. Cases not listed still use the default single-function
selection rule, including the `multiple_functions.py` rejection. This lets
call tests reach the actual call diagnostic rather than fail entry selection.
