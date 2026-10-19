#!/usr/bin/env python3
"""Regenerate the expected diagnostics for the rejection corpus.

    python scripts/update_rejections.py           # rewrite snapshots
    python scripts/update_rejections.py --check   # fail if any snapshot is stale

Each case under ``tests/rejections/cases/*.py`` must be rejected by the
frontend.  The snapshot records the exception class and the exact located
message.  A case that stops being rejected is an error, not a silent update.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "python"))

from pontifex.errors import FrontendError  # noqa: E402
from pontifex.frontend import translate  # noqa: E402

CASES = ROOT / "tests" / "rejections" / "cases"
EXPECTED = ROOT / "tests" / "rejections" / "expected"
FUNCTIONS = json.loads((CASES.parent / "functions.json").read_text())


def diagnose(path: Path) -> str:
    relative = path.relative_to(ROOT).as_posix()
    try:
        translate(path.read_text(), filename=relative, function=FUNCTIONS.get(path.name))
    except FrontendError as exc:
        return f"{type(exc).__name__}\n{exc}\n"
    except Exception as exc:  # noqa: BLE001 - report, do not hide
        raise SystemExit(f"{relative}: unexpected {type(exc).__name__}: {exc}") from exc
    raise SystemExit(f"{relative}: expected a rejection, but the frontend accepted it")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="verify snapshots without writing")
    args = parser.parse_args(argv)

    EXPECTED.mkdir(parents=True, exist_ok=True)
    unknown = set(FUNCTIONS) - {path.name for path in CASES.glob("*.py")}
    if unknown:
        raise SystemExit(f"unknown rejection cases in functions.json: {sorted(unknown)}")
    stale: list[str] = []
    for case in sorted(CASES.glob("*.py")):
        snapshot = EXPECTED / f"{case.stem}.error"
        text = diagnose(case)
        if args.check:
            if not snapshot.exists() or snapshot.read_text() != text:
                stale.append(str(snapshot.relative_to(ROOT)))
            continue
        snapshot.write_text(text)
    if stale:
        print("stale rejection snapshots:", *stale, sep="\n  ")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
