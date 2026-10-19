"""P0/T4: the differential corpus and its manifest."""
from __future__ import annotations

import json
import subprocess
import sys

import pytest

from pyverif.pipeline import compile_file

from conftest import ROOT

CORPUS = ROOT / "corpus"
MODES = {"exact", "rat", "float"}


def _manifest():
    return json.loads((CORPUS / "manifest.json").read_text())["programs"]


def _allowlist():
    return json.loads((CORPUS / "allowlist.json").read_text())["allow"]


def test_every_program_is_declared_exactly_once():
    declared = {entry["file"] for entry in _manifest()}
    present = {path.name for path in (CORPUS / "programs").glob("*.py")}
    assert declared == present


@pytest.mark.parametrize("entry", _manifest(), ids=lambda e: e["file"])
def test_manifest_entry_is_a_well_formed_subset_program(entry):
    artifacts = compile_file(CORPUS / "programs" / entry["file"], function=entry["function"])
    assert artifacts.fn.arity == len(entry["params"])
    assert entry.get("fuel", 0) > 0
    for spec in entry["params"]:
        assert spec["kind"] in {"rat", "positive", "nonnegative", "nat"}


def test_allowlist_is_well_formed():
    declared = {entry["file"].removesuffix(".py") for entry in _manifest()}
    for item in _allowlist():
        assert item["program"] in declared
        assert item["mode"] in MODES
        assert item["reason"].strip()


def test_corpus_is_large_enough():
    assert len(_manifest()) >= 15


@pytest.mark.slow
def test_corpus_differential_passes(lean_exe):
    proc = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts" / "run_corpus.py"),
            "--samples",
            "6",
            "--exe",
            str(lean_exe),
        ],
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr
    assert "0 mismatches" in proc.stdout
