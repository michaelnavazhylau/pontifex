"""Emitter output and integration with the Lean build."""

from __future__ import annotations

import importlib.util
import shutil
import subprocess
import sys
from fractions import Fraction

import pytest
from conftest import EXAMPLES, ROOT
from lean_helpers import check_lean
from pontifex.emit import emit_native_samples, option_type, rat_literal, tuple_type
from pontifex.pipeline import compile_file, compile_source


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
    assert "namespace Pontifex.Generated.FreeFall" in text


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
        check=False,
    )
    assert proc.returncode == 0, proc.stdout + proc.stderr


@pytest.mark.slow
def test_lean_build_succeeds():
    proc = subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True, check=False)
    assert proc.returncode == 0, proc.stdout[-4000:] + proc.stderr[-4000:]


@pytest.mark.slow
def test_lean_runner_builds_and_runs(lean_exe):
    proc = subprocess.run([str(lean_exe)], capture_output=True, text=True, check=False)
    assert proc.returncode == 2
    assert "usage" in proc.stderr


@pytest.mark.slow
@pytest.mark.parametrize("expected,success", [(2, True), (3, False)])
def test_separate_native_samples_reject_corrupt_expectations(tmp_path, expected, success):
    artifacts = compile_source("def f(x):\n    return x + 1\n", namespace="SampleCheck")
    assert "native_decide" not in artifacts.lean_source
    samples = emit_native_samples(
        artifacts.fn,
        namespace="SampleCheck",
        conformance=[([Fraction(1)], [Fraction(expected)])],
    )
    result = check_lean(tmp_path, artifacts.lean_source + samples)
    assert (result.returncode == 0) == success, result.stdout + result.stderr


def test_pipeline_samples_are_not_part_of_the_certificate():
    pairs = [([Fraction(1)], [Fraction(2)])]
    artifacts = compile_source(
        "def f(x):\n    return x + 1\n", namespace="SampleAPI", conformance=pairs
    )
    assert "native_decide" not in artifacts.lean_source
    assert "f_sample_0" not in artifacts.lean_source
    assert artifacts.native_samples_source.startswith(artifacts.lean_source)
    assert "native_decide" in artifacts.native_samples_source
    assert (
        "native_decide"
        in compile_file(
            EXAMPLES / "free_fall.py", conformance=[([0, 0, 0, 0], [0, 0])]
        ).native_samples_source
    )


@pytest.mark.slow
def test_cli_samples_are_separate_and_standalone(tmp_path, capsys):
    from pontifex.cli import main

    source = tmp_path / "add.py"
    source.write_text("def f(x):\n    return x + 1\n")
    output = tmp_path / "Add.lean"
    assert main(["compile", str(source), "--out", str(output), "--with-samples"]) == 0
    samples = tmp_path / "Add.samples.lean"
    assert str(samples) in capsys.readouterr().out
    assert "native_decide" not in output.read_text()
    assert "native_decide" in samples.read_text()
    result = check_lean(tmp_path, samples.read_text(), name="StandaloneSamples.lean")
    assert result.returncode == 0, result.stdout + result.stderr


def test_native_samples_freshness_is_checked(tmp_path, monkeypatch, capsys):
    spec = importlib.util.spec_from_file_location("sample_generator", ROOT / "scripts/generate.py")
    generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generator)
    monkeypatch.setattr(generator, "ROOT", tmp_path)
    shutil.copytree(EXAMPLES, tmp_path / "examples")
    config = tmp_path / "Pontifex/Core/Config.lean"
    config.parent.mkdir(parents=True)
    shutil.copyfile(ROOT / "Pontifex/Core/Config.lean", config)
    assert generator.main([]) == 0
    assert generator.main(["--check"]) == 0
    native = tmp_path / "NativeTests.lean"
    native.write_text(native.read_text() + "-- stale\n")
    assert generator.main(["--check"]) == 1
    assert str(native) in capsys.readouterr().out
