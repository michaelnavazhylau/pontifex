"""P1: completed failures are observable; exhaustion is the only unknown."""

from __future__ import annotations

import textwrap
from fractions import Fraction

import pytest

from pontifex.frontend import translate
from pontifex.interp import Failed, Stuck, OutOfFuel, Returned, run_exact, run_float
from pontifex.ir import Fn, Ret, Slot, Ite, Seq, Where, Phi, Assign, Lit
from pontifex.pipeline import compare_outcomes, run_lean, compile_source
from lean_helpers import check_lean

CASES = [
    ("def f(x, y):\n    return x / y\n", [1, 0], Failed("divisionByZero")),
    ("def f(x, y):\n    return x / y\n", [0, 0], Failed("divisionByZero")),
    ("def f(x, y):\n    return x / y\n", [1, 2], Returned((Fraction(1, 2),))),
    ("def f(x):\n    if False and x / 0 > 0:\n        x = 2\n    return x\n", [1], Returned((1,))),
    ("def f(x):\n    if True or x / 0 > 0:\n        x = 2\n    return x\n", [1], Returned((2,))),
    ("def f(x):\n    if x / 0 > 0:\n        x = 2\n    return x\n", [1], Failed("divisionByZero")),
    (
        "def f(x):\n    while x > 0:\n        x = x / 0\n    return x\n",
        [1],
        Failed("divisionByZero"),
    ),
    ("def f(x):\n    while x > 0:\n        x = x / 0\n    return x\n", [0], Returned((0,))),
    (
        "def f(x):\n    while x / 0 > 0:\n        x = x + 1\n    return x\n",
        [1],
        Failed("divisionByZero"),
    ),
]


@pytest.mark.parametrize("source,args,expected", CASES)
@pytest.mark.parametrize("mode", ["rat", "float"])
def test_failures_and_short_circuiting(source, args, expected, mode, lean_exe):
    fn = translate(source).fn
    run = run_exact if mode == "rat" else run_float
    ours = run(fn, args, fuel=64)
    assert ours == expected
    (theirs,) = run_lean(lean_exe, fn.to_json_text(), [args], mode=mode, fuel=64)
    assert compare_outcomes(ours, theirs) is None


@pytest.mark.parametrize("mode", ["rat", "float"])
def test_every_small_fuel_agrees_even_when_failure_is_pending(mode, lean_exe):
    fn = translate("def f(x):\n    x = x / 0\n    return x\n").fn
    run = run_exact if mode == "rat" else run_float
    for fuel in range(16):
        ours = run(fn, [1], fuel=fuel)
        (theirs,) = run_lean(lean_exe, fn.to_json_text(), [[1]], mode=mode, fuel=fuel)
        assert compare_outcomes(ours, theirs) is None, (fuel, ours, theirs)
    assert isinstance(run(fn, [1], fuel=1), OutOfFuel)
    assert run(fn, [1], fuel=4) == Failed("divisionByZero")


@pytest.mark.parametrize("mode", ["rat", "float"])
def test_missing_slot_and_phi_predecessor_are_stuck(mode, lean_exe):
    programs = [
        Fn("raw", (), (), Ret((Slot(0),))),
        Fn("gap", (), (), Seq((Assign(4, Lit(Fraction(1))), Ret((Slot(0),))))),
        Fn(
            "raw",
            (),
            (),
            Seq(
                (
                    Ite(Where(True), Seq(()), Seq(()), (Phi(0, 99, 99),)),
                    Ret((Slot(0),)),
                )
            ),
        ),
    ]
    run = run_exact if mode == "rat" else run_float
    for fn in programs:
        assert run(fn, [], fuel=16) == Stuck()
        (theirs,) = run_lean(lean_exe, fn.to_json_text(), [[]], mode=mode, fuel=16)
        assert theirs == Stuck()


def test_float_failures_and_evaluation_order(lean_exe):
    for source, expected in [
        ("def f(x):\n    return x ** 2\n", Failed("overflow")),
        ("def f(x):\n    return (x ** 2) + 1 / 0\n", Failed("overflow")),
        ("def f(x):\n    return 1 / 0 + (x ** 2)\n", Failed("divisionByZero")),
    ]:
        fn = translate(source).fn
        ours = run_float(fn, [1e308])
        (theirs,) = run_lean(lean_exe, fn.to_json_text(), [[1e308]], mode="float")
        assert ours == theirs == expected


def test_failure_is_not_bottom_and_refinement_is_kernel_checked(tmp_path):
    source = """
import Pontifex.Core.Refinement
import Pontifex.Audit.Command
open Pontifex
example : ¬Outcome.Refines (.failed .divisionByZero : Outcome Rat) (.returned []) := by
  intro h; rcases h with h | h <;> cases h
example : ¬Outcome.Refines (.stuck : Outcome Rat) (.returned []) := by
  intro h; rcases h with h | h <;> cases h
#audit_axioms Pontifex.exec_mono Pontifex.exec_completed_stable Pontifex.total_to_partial
"""
    result = check_lean(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.mark.parametrize(
    "program",
    [
        "def f(x, y):\n    return x / y\n",
        "def f(x):\n    return x ** 2\n",
        "def f(x):\n    if x / 0 > 0:\n        x = 0\n    return x\n",
        "def f(x):\n    return 5e-324 + x\n",
    ],
)
def test_checked_codegen_and_lowering_certificates(program, tmp_path):
    text = compile_source(program, namespace="Checked").lean_source
    result = check_lean(tmp_path, text)
    assert result.returncode == 0, result.stdout + result.stderr
