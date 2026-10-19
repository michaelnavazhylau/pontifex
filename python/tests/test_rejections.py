"""P0/T3: the rejection corpus and its committed diagnostics."""
from __future__ import annotations

import subprocess
import sys

import pytest

from pontifex.errors import FrontendError
from pontifex.frontend import translate

from conftest import ROOT

CASES = ROOT / "tests" / "rejections" / "cases"
EXPECTED = ROOT / "tests" / "rejections" / "expected"
CASE_PATHS = sorted(CASES.glob("*.py"))


def _diagnose(path):
    relative = path.relative_to(ROOT).as_posix()
    with pytest.raises(FrontendError) as info:
        translate(path.read_text(), filename=relative)
    return f"{type(info.value).__name__}\n{info.value}\n"


def test_corpus_is_not_empty():
    assert len(CASE_PATHS) >= 40


@pytest.mark.parametrize("path", CASE_PATHS, ids=lambda p: p.stem)
def test_rejection_matches_committed_snapshot(path):
    snapshot = EXPECTED / f"{path.stem}.error"
    assert snapshot.exists(), f"missing snapshot; run python scripts/update_rejections.py"
    assert _diagnose(path) == snapshot.read_text(), (
        f"diagnostic changed for {path.name}; review it, then run "
        "`python scripts/update_rejections.py`"
    )


@pytest.mark.parametrize("path", CASE_PATHS, ids=lambda p: p.stem)
def test_diagnostics_are_deterministic(path):
    assert _diagnose(path) == _diagnose(path)


def test_no_orphan_snapshots():
    expected = {p.stem for p in CASE_PATHS}
    snapshots = {p.stem for p in EXPECTED.glob("*.error")}
    assert snapshots <= expected, snapshots - expected


def test_snapshot_checker_detects_drift(tmp_path):
    case = CASE_PATHS[0]
    snapshot = EXPECTED / f"{case.stem}.error"
    original = snapshot.read_text()
    try:
        snapshot.write_text(original + "stale\n")
        proc = subprocess.run(
            [sys.executable, str(ROOT / "scripts" / "update_rejections.py"), "--check"],
            capture_output=True,
            text=True,
            timeout=120,
        )
        assert proc.returncode != 0
        assert "stale rejection snapshots" in proc.stdout
    finally:
        snapshot.write_text(original)
