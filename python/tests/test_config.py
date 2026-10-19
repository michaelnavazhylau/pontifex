"""Artifact configuration stamping and schema guards (P0/T1)."""
from __future__ import annotations

import json
import subprocess

import pytest

from pontifex.frontend import translate
from pontifex.ir import fn_of_json
from pontifex.pipeline import compile_file
from pontifex.version import IR_VERSION

from conftest import EXAMPLES, ROOT


def _generated_example() -> str:
    return (ROOT / "Pontifex" / "Generated" / "FreeFallLoop.lean").read_text()


def test_generated_artifacts_stamp_configuration():
    text = _generated_example()
    assert "def pontifexConfig : Config :=" in text
    assert f"irVersion := {IR_VERSION}" in text
    assert "fuelPolicy := .allFuel" in text
    assert "numericMode := .exactRat" in text
    assert "#guard pontifexConfig.schemaMatches" in text


def test_straight_line_artifacts_declare_literal_fuel():
    text = (ROOT / "Pontifex" / "Generated" / "FreeFall.lean").read_text()
    assert "fuelPolicy := .literal" in text


def test_json_artifacts_record_schema_version():
    artifacts = compile_file(EXAMPLES / "free_fall.py")
    payload = json.loads(artifacts.ir_json)
    assert payload["irVersion"] == IR_VERSION
    assert fn_of_json(payload).name == "step"


def test_python_decoder_rejects_wrong_schema_version():
    payload = json.loads(compile_file(EXAMPLES / "free_fall.py").ir_json)
    payload["irVersion"] = IR_VERSION + 1
    with pytest.raises(ValueError, match="IR version mismatch"):
        fn_of_json(payload)


@pytest.mark.parametrize("field", ["schema", "fuel", "numeric"])
def test_stale_schema_version_breaks_the_build(tmp_path, field):
    """`#guard` must turn a version drift into a compile error."""
    text = _generated_example()
    if field == "schema":
        corrupted = text.replace(f"irVersion := {IR_VERSION}", f"irVersion := {IR_VERSION + 1}", 1)
    elif field == "fuel":
        corrupted = text.replace("fuelPolicy := .allFuel", "fuelPolicy := .literal", 1)
    else:
        corrupted = text.replace("numericMode := .exactRat", "numericMode := .binary64", 1)
    assert corrupted != text
    path = tmp_path / "Stale.lean"
    path.write_text(corrupted)
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True, timeout=120
    )
    assert proc.returncode != 0
    output = (proc.stdout + proc.stderr).lower()
    assert "did not evaluate" in output


def test_lean_runner_rejects_stale_ir_json(tmp_path, lean_exe):
    artifacts = compile_file(EXAMPLES / "free_fall.py")
    payload = json.loads(artifacts.ir_json)
    payload["irVersion"] = IR_VERSION + 1
    ir_path = tmp_path / "stale.json"
    ir_path.write_text(json.dumps(payload))
    inputs = tmp_path / "inputs.json"
    inputs.write_text('[["1", "2", "3", "4"]]')
    proc = subprocess.run(
        [str(lean_exe), "rat", str(ir_path), str(inputs)],
        capture_output=True,
        text=True,
        timeout=60,
    )
    assert proc.returncode != 0
    assert "version mismatch" in proc.stderr.lower()


def test_generate_refuses_to_run_on_schema_drift(tmp_path):
    import importlib.util

    spec = importlib.util.spec_from_file_location("pontifex_generate", ROOT / "scripts" / "generate.py")
    generate = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generate)
    config = tmp_path / "Config.lean"
    config.write_text("def irSchemaVersion : Nat := 999\n")
    with pytest.raises(SystemExit, match="schema version mismatch"):
        generate.check_schema_alignment(config, expected=IR_VERSION)
