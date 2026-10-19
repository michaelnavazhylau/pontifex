"""Proof certificates must generalize, and reject a corrupted executable.

These tests invoke Lean's kernel on newly translated programs, not just the
checked-in physics examples. No sample/native_decide proofs are requested.
"""
from __future__ import annotations

import re
import subprocess
import textwrap

import pytest

from pyverif.pipeline import compile_source
from conftest import ROOT, example_source

PROGRAMS = {
    "binder_hygiene": """
        def f(fuel, env, ops, input0):
            if fuel > 0:
                env = ops + input0
            return env
    """,
    "nested_if": """
        def f(x, y):
            if x > y:
                if y != 0:
                    x = x / y
                else:
                    x = -x
            else:
                y = abs(x - y)
            return x, y
    """,
    "no_phis": """
        def f(x):
            if x > 0:
                pass
            return x
    """,
    "loop_then_continuation": """
        def f(x):
            while x < 3:
                x = x + 1
            x = x * 2
            return x, x + 1
    """,
    "nested_loop": """
        def f(x, n):
            j = 0
            while x < n:
                j = 0
                while j < 2:
                    if x < 0:
                        x = x + 2
                    else:
                        x = x + 1
                    j = j + 1
            return x, j
    """,
    "sequential_loops": """
        def f(x, y):
            while x < 2:
                x = x + 1
            while y < x:
                y = y + 1
            return x, y
    """,
    "divergence": """
        def f(x):
            while True:
                pass
            return x
    """,
    "constant_false": """
        def f():
            while False:
                pass
            return 0.1 + 0.2
    """,
    "conditions": """
        def f(x, y):
            while x < 4 and not (x == y):
                if x <= y or x >= 1:
                    x = x + 1
                else:
                    x = x + 2
            return x
    """,
}


def check_lean(tmp_path, source: str):
    path = tmp_path / "Certificate.lean"
    path.write_text(source)
    return subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT,
        capture_output=True, text=True, timeout=90,
    )


@pytest.mark.slow
@pytest.mark.parametrize("name", PROGRAMS)
def test_new_program_certificates_are_kernel_checked(name, tmp_path):
    artifacts = compile_source(textwrap.dedent(PROGRAMS[name]), namespace="Certificate")
    text = artifacts.lean_source
    assert "native_decide" not in text
    assert "sorry" not in text
    # Generated executable blocks must be independent of the reference evaluator.
    for declaration in re.findall(r"(?ms)^def .*?(?=^theorem |\Z)", text):
        assert not re.search(r"\b(exec|evalE|evalC|mergePhis|applyBackEdges)\b", declaration)
    text += (
        "\n#print axioms Certificate.f_lowering"
        "\n#print axioms Certificate.f_compiled_link"
        "\n#print axioms Certificate.f_link\n"
    )
    result = check_lean(tmp_path, text)
    assert result.returncode == 0, result.stdout + result.stderr
    # Only Lean's standard logical axioms are allowed, not a compiler trust
    # axiom (native_decide), sorryAx, or a project-specific assumption.
    axiom_lists = re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout)
    assert len(axiom_lists) == 3, result.stdout
    for axioms in axiom_lists:
        assert set(axioms.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}, result.stdout


@pytest.mark.slow
@pytest.mark.parametrize("mutation", ["source_ast", "source_arithmetic", "ir_body"])
def test_corrupt_lowering_is_rejected_by_kernel(mutation, tmp_path):
    artifacts = compile_source(example_source("clamped_step"), namespace="Certificate")
    text = artifacts.lean_source
    baseline = check_lean(tmp_path, text)
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr
    if mutation == "source_ast":
        # Point a source variable at the wrong id.
        corrupted = text.replace("(.var 3)", "(.var 2)", 1)
    elif mutation == "source_arithmetic":
        corrupted = text.replace("(.bin .add", "(.bin .sub", 1)
    else:
        # Corrupt the emitted IR body instead of the source AST.
        corrupted = text.replace("⟨7, 6, 1⟩", "⟨7, 5, 1⟩", 1)
    assert corrupted != text
    result = check_lean(tmp_path, corrupted)
    assert result.returncode != 0, "corrupted lowering unexpectedly passed its certificate"
    assert "error:" in result.stdout + result.stderr


@pytest.mark.slow
@pytest.mark.parametrize("mutation", ["arithmetic", "phi", "fuel"])
def test_corrupt_codegen_is_rejected_by_kernel(mutation, tmp_path):
    source = example_source("clamped_step" if mutation == "phi" else "free_fall_loop")
    artifacts = compile_source(source, namespace="Certificate")
    text = artifacts.lean_source
    baseline = check_lean(tmp_path, text)
    assert baseline.returncode == 0, baseline.stdout + baseline.stderr
    if mutation == "arithmetic":
        corrupted = text.replace("(ops.add ", "(ops.sub ", 1)
    elif mutation == "phi":
        # Read the wrong predecessor in an otherwise intact parallel phi copy.
        corrupted = re.sub(r"(\.set \d+ \(next.get! )\(if branch then \d+ else \d+\)", r"\g<1>0", text, count=1)
    else:
        # The first executable leaf must not acquire a larger budget domain.
        corrupted = text.replace("| 0, _ => .outOfFuel", "| 0, env => .fellThrough env", 1)
    assert corrupted != text
    result = check_lean(tmp_path, corrupted)
    assert result.returncode != 0, "corrupted code unexpectedly passed its certificate"
    assert "error:" in result.stdout + result.stderr


@pytest.mark.slow
def test_float_backend_specialization_requires_no_float_computation(tmp_path):
    text = compile_source(textwrap.dedent(PROGRAMS["loop_then_continuation"]), namespace="Certificate").lean_source
    text += """
example (fuel : Nat) (args : List Float) :
    Certificate.fCompiled PyVerif.Ops.float fuel args =
      PyVerif.Fn.run PyVerif.Ops.float Certificate.fIR fuel args :=
  Certificate.f_compiled_link PyVerif.Ops.float fuel args
"""
    result = check_lean(tmp_path, text)
    assert result.returncode == 0, result.stdout + result.stderr
