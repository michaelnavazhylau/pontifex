"""Emitter output and integration with the Lean build."""

from __future__ import annotations

import subprocess
import sys

import pytest

from pyverif.emit import option_type, rat_literal, tuple_type
from pyverif.pipeline import compile_file

from conftest import EXAMPLES, ROOT


def test_rat_literal():
    from fractions import Fraction

    assert rat_literal(Fraction(3)) == "(3 : Rat)"
    assert rat_literal(Fraction(-1, 2)) == "((-1 : Rat) / 2)"


def test_tuple_and_option_types():
    assert tuple_type(0) == "Unit"
    assert tuple_type(1) == "Rat"
    assert tuple_type(3) == "Rat × Rat × Rat"
    assert option_type(0) == "Option Unit"
    assert option_type(1) == "Option Rat"
    assert option_type(2) == "Option (Rat × Rat)"


def test_straight_line_link_is_emitted():
    artifacts = compile_file(EXAMPLES / "free_fall.py")
    text = artifacts.lean_source
    assert "def stepIR : Fn :=" in text
    assert "def step (_fuel : Nat)" in text
    assert "theorem step_link" in text
    assert ":=\n  rfl" in text
    assert "namespace PyVerif.Generated.FreeFall" in text


def test_control_flow_emits_all_fuel_certificates():
    artifacts = compile_file(EXAMPLES / "free_fall_loop.py", fuel=64)
    text = artifacts.lean_source
    assert "induction fuel generalizing env" in text
    assert "theorem simulate_compiled_link (ops : Ops α)" in text
    assert "theorem simulate_link (fuel : Nat)" in text
    assert "sorry" not in text
    assert "native_decide" not in text  # no samples requested
    assert "missing linkage" not in text


def test_json_ir_matches_lean_literal_slots():
    artifacts = compile_file(EXAMPLES / "clamped_step.py")
    fn = artifacts.fn
    for name in fn.slot_names:
        assert name.replace('"', '\\"') in artifacts.lean_source


def test_generated_files_are_up_to_date():
    proc = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "generate.py"), "--check"],
        capture_output=True,
        text=True,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


@pytest.mark.slow
def test_lean_build_succeeds():
    proc = subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    assert proc.returncode == 0, proc.stdout[-4000:] + proc.stderr[-4000:]


@pytest.mark.slow
def test_lean_runner_builds_and_runs(lean_exe):
    proc = subprocess.run([str(lean_exe)], capture_output=True, text=True)
    assert proc.returncode == 2
    assert "usage" in proc.stderr
