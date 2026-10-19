"""Schema and artifact versioning.

Bump `IR_VERSION` here *and* `irSchemaVersion` in
`PyVerif/Core/Config.lean` together.  Generated modules stamp the version and
`#guard` it against the Lean schema; the Lean JSON decoder rejects a mismatched
wire format, and `scripts/generate.py --check` reports stale artifacts.
"""

from __future__ import annotations

IR_VERSION = 1

FUEL_POLICY_LITERAL = "literal"
FUEL_POLICY_ALL_FUEL = "allFuel"

NUMERIC_MODE_EXACT_RAT = "exactRat"
NUMERIC_MODE_BINARY64 = "binary64"
