"""T15a: eager Python min/max, lazy scalar selection, and kernel agreement."""

from __future__ import annotations

from fractions import Fraction
import itertools
import json
import random
import re
import struct
import textwrap

import pytest

from pontifex.errors import FrontendError
from pontifex.frontend import translate
from pontifex.interp import Failed, Returned, Stuck, eval_value, make_ops, run_exact, run_float
from pontifex.ir import (
    ArrayLit,
    Bin,
    Cmp,
    Fn,
    Lit,
    Ret,
    Select,
    Slot,
    Where,
    fn_of_json,
    slots_read,
)
from pontifex.pipeline import (
    compile_source,
    compare_outcomes,
    load_python_function,
    observe_python,
    run_lean,
)
from pontifex.source import Select as SourceSelect, desugar
from pontifex.version import IR_VERSION
from lean_helpers import check_lean


PROGRAMS = {
    "straight_line": """
        def f(x, y):
            z = min(x, y)
            w = max(x, y)
            return z if x > 0 else w
    """,
    "nested_expressions": """
        def f(x, y):
            return max(min(x, y), x if x < 0 else -x) + (y if y > 0 else 1)
    """,
    "caller_control_flow": """
        def f(x, n):
            while n > 0:
                x = min(x + 1, 8) if x > 0 else max(x, -8)
                if (x if n > 1 else 0) > 5:
                    return min(x, 5)
                n -= 1
            return x
    """,
    "lazy_faults": """
        def f(x):
            return 1 / x if x != 0 and not (x < 0) else max(x, 0)
    """,
    "nested_condition": """
        def f(x, y):
            return (x if x > y else y) if (x if y > 0 else -x) > 0 else min(x, y)
    """,
    "array_elements": """
        def f(x):
            xs = [min(x, 0), max(x, 0)]
            xs[0] = xs[1] if x > 0 else xs[0]
            return xs[0] if x != 0 else len(xs)
    """,
    "inlined_helper": """
        def helper(x, y):
            z = min(x, y)
            return max(z, -y) if x > 0 and y != 0 else y
        def f(x, y):
            z = helper(min(x, y), x if y > 0 else y)
            return helper(z, y)
    """,
}


def artifact(name):
    return compile_source(textwrap.dedent(PROGRAMS[name]), function="f", namespace="Selection")


@pytest.mark.parametrize("name", PROGRAMS)
def test_selection_programs_agree_with_python_and_lean(name, lean_exe):
    compiled = artifact(name)
    fn = compiled.fn
    python = load_python_function(compiled.translated.source, "f")
    rng = random.Random(name)
    vectors = [
        [Fraction(rng.randint(-8, 8), rng.choice([1, 2, 4])) for _ in fn.params] for _ in range(20)
    ]
    if name == "caller_control_flow":
        for row in vectors:
            row[1] = Fraction(rng.randint(0, 5))
    assert fn_of_json(json.loads(compiled.ir_json)) == fn
    assert "fuelPolicy := .allFuel" in compiled.lean_source
    for mode, run, convert in (("rat", run_exact, Fraction), ("float", run_float, float)):
        inputs = [[convert(x) for x in row] for row in vectors]
        lean = run_lean(lean_exe, compiled.ir_json, inputs, mode=mode, fuel=128)
        for args, theirs in zip(inputs, lean):
            expected = observe_python(python, args)
            actual = run(fn, args, fuel=128)
            assert compare_outcomes(expected, actual) is None, (name, mode, args)
            assert compare_outcomes(actual, theirs) is None, (name, mode, args)


@pytest.mark.slow
@pytest.mark.parametrize("name", PROGRAMS)
def test_selection_certificates_are_kernel_checked(name, tmp_path):
    source = artifact(name).lean_source
    # The emitted executable is independent of reference expression evaluation.
    for declaration in re.findall(r"(?ms)^def .*?(?=^theorem |\Z)", source):
        assert not re.search(r"\b(exec|evalV|evalS|evalC)\b", declaration)
    assert "native_decide" not in source
    assert "sorry" not in source
    source += "\n#print axioms Selection.f_lowering\n#print axioms Selection.f_program_lowering\n#print axioms Selection.f_compiled_link\n"
    result = check_lean(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    axioms = re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout)
    assert len(axioms) == 3, result.stdout
    for names in axioms:
        assert set(names.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}


@pytest.mark.parametrize(
    "expr, result",
    [
        ("42 if True else 1 / 0", Returned((42,))),
        ("1 / 0 if False else 42", Returned((42,))),
        ("xs[1] if False else 42", Returned((42,))),
        ("42 if True else xs[1]", Returned((42,))),
        ("42 if False and 1 / 0 > 0 else 7", Returned((7,))),
        ("42 if True or xs[1] > 0 else 7", Returned((42,))),
        ("42 if 1 / 0 > 0 else xs[1]", Failed("divisionByZero")),
        ("42 if xs[1] > 0 else 1 / 0", Failed("indexOutOfBounds")),
        ("xs[1] if True else 1 / 0", Failed("indexOutOfBounds")),
        ("1 / 0 if True else xs[1]", Failed("divisionByZero")),
        *[(f"{op}(xs[1], 1 / 0)", Failed("indexOutOfBounds")) for op in ("min", "max")],
        *[(f"{op}(1 / 0, xs[1])", Failed("divisionByZero")) for op in ("min", "max")],
        *[(f"{op}(0, 1 / 0)", Failed("divisionByZero")) for op in ("min", "max")],
    ],
)
def test_fault_order_and_branch_laziness(expr, result, lean_exe):
    source = f"def f():\n    xs = []\n    return {expr}\n"
    fn = translate(source).fn
    assert observe_python(load_python_function(source, "f"), []) == result
    assert run_exact(fn, []) == result
    assert run_float(fn, []) == result
    for mode in ("rat", "float"):
        assert run_lean(lean_exe, fn.to_json_text(), [[]], mode=mode) == [result]


@pytest.mark.parametrize(
    "condition, then, otherwise, expected",
    [
        (Where(True), Lit(Fraction(7)), Slot(99), Returned((7,))),
        (Where(False), Slot(99), Lit(Fraction(7)), Returned((7,))),
        (Where(True), Slot(99), Lit(Fraction(7)), Stuck()),
        (Cmp("lt", Slot(99), Lit(Fraction(0))), Lit(Fraction(7)), Lit(Fraction(8)), Stuck()),
        (Where(True), ArrayLit(()), Lit(Fraction(7)), Stuck()),
        (Where(False), Lit(Fraction(7)), ArrayLit(()), Stuck()),
    ],
)
def test_raw_ir_selection_propagates_stuck(condition, then, otherwise, expected, lean_exe):
    fn = Fn("raw", (), (), Ret((Select(condition, then, otherwise),)))
    for run in (run_exact, run_float):
        assert run(fn, []) == expected
    assert run_lean(lean_exe, fn.to_json_text(), [[]]) == [expected]


@pytest.mark.parametrize("op", ["min", "max"])
@pytest.mark.parametrize("a, b", [("1", "1"), ("-0.0", "0.0"), ("0.0", "-0.0"), ("2", "2.0")])
def test_exact_mode_ties_return_the_first_exact_value(op, a, b):
    source = f"def f(a, b):\n    return {op}(a, b)\n"
    fn = translate(source).fn
    assert (
        run_exact(fn, [Fraction(a), Fraction(b)])
        == run_exact(fn, [Fraction(b), Fraction(a)])
        == Returned((Fraction(a),))
    )


@pytest.mark.parametrize("op", ["min", "max"])
def test_each_min_max_operand_is_evaluated_once(op):
    seen = []
    ops = make_ops(True)

    def literal(value):
        seen.append(value)
        return Fraction(value)

    ops["literal"] = literal
    expr = Bin(
        op,
        Bin("add", Lit(Fraction(1)), Lit(Fraction(2))),
        Bin("mul", Lit(Fraction(3)), Lit(Fraction(4))),
    )
    assert eval_value(expr, {}, ops) == (3 if op == "min" else 12)
    assert seen == [1, 2, 3, 4]


def test_condition_precedes_exactly_one_branch_evaluation():
    seen = []
    ops = make_ops(True)

    def literal(value):
        seen.append(value)
        return Fraction(value)

    ops["literal"] = literal
    expr = Select(Cmp("gt", Lit(Fraction(1)), Lit(Fraction(0))), Lit(Fraction(2)), Lit(Fraction(3)))
    assert eval_value(expr, {}, ops) == 2
    assert seen == [1, 0, 2]


def test_source_and_ir_keep_explicit_numeric_selection_nodes():
    compiled = artifact("straight_line")
    body = compiled.fn.body.body
    assert body[0].expr.op == "min"
    assert body[1].expr.op == "max"
    assert isinstance(body[2].exprs[0], Select)
    source = desugar(compiled.translated)
    assert isinstance(source.body[2].exprs[0], SourceSelect)
    assert slots_read(body[2].exprs[0]) == {0, 2, 3}
    assert "(.bin .min" in compiled.lean_source
    assert "(.bin .max" in compiled.lean_source
    assert "(.select" in compiled.lean_source


@pytest.mark.parametrize("op", ["min", "max"])
def test_ieee_selection_preserves_first_operand_bits_on_ties_or_nan(op, lean_exe):
    patterns = [
        0,
        1 << 63,
        1,
        (1 << 63) + 1,
        0x0010000000000000,
        0x3FF0000000000000,
        0xBFF0000000000000,
        0x7FEFFFFFFFFFFFFF,
        0x7FF0000000000000,
        0xFFF0000000000000,
        0x7FF8000000000001,
        0xFFF8000000000042,
        0x7FF0000000000001,
        0xFFF0000000000042,
    ]
    values = [struct.unpack(">d", struct.pack(">Q", bits))[0] for bits in patterns]
    vectors = [list(pair) for pair in itertools.product(values, repeat=2)]
    source = f"def f(x, y):\n    return {op}(x, y)\n"
    fn = translate(source).fn
    python = load_python_function(source, "f")
    lean = run_lean(lean_exe, fn.to_json_text(), vectors, mode="float")
    for args, theirs in zip(vectors, lean):
        expected = observe_python(python, args)
        # No NaN exemptions: these operations return an unchanged operand.
        assert compare_outcomes(expected, run_float(fn, args)) is None
        assert compare_outcomes(expected, theirs) is None


@pytest.mark.parametrize("op", ["min", "max"])
@pytest.mark.parametrize(
    "arguments", ["", "x", "x, x, x", "x, x, key=abs", "x, default=0", "*x", "x, *x", "**x"]
)
def test_unsupported_min_max_signatures(op, arguments):
    with pytest.raises(FrontendError, match="exactly two positional scalar arguments"):
        translate(f"def f(x):\n    return {op}({arguments})\n", filename="selection.py")


@pytest.mark.parametrize(
    "expr",
    [
        "min(xs, 0)",
        "max(0, xs)",
        "min([1], 0)",
        "max(0, [1])",
        "xs if True else 0",
        "0 if False else xs",
        "[1] if True else 0",
    ],
)
def test_array_selection_operands_are_rejected_even_on_dead_branches(expr):
    with pytest.raises(FrontendError):
        translate(f"def f():\n    xs = []\n    return {expr}\n")


@pytest.mark.parametrize("op", ["min", "max"])
def test_shadowed_min_max_are_not_silently_compiled_as_builtins(op):
    with pytest.raises(FrontendError, match="shadowed by a local variable"):
        translate(f"def f({op}, x):\n    return {op}(x, x)\n")
    source = f"def {op}(x, y):\n    return x + y\ndef f(x):\n    return {op}(x, 2)\n"
    fn = translate(source, function="f").fn
    assert run_exact(fn, [3]) == Returned((5,))


@pytest.mark.parametrize("old_schema", [1, 2, 3])
def test_selection_schema_rejects_old_artifacts(old_schema, lean_exe):
    payload = artifact("straight_line").fn.to_json()
    assert payload["irVersion"] == IR_VERSION == 4
    payload["irVersion"] = old_schema
    with pytest.raises(ValueError, match="IR version mismatch"):
        fn_of_json(payload)
    with pytest.raises(RuntimeError, match="IR version mismatch"):
        run_lean(lean_exe, json.dumps(payload), [[1, 2]])


@pytest.mark.slow
@pytest.mark.parametrize(
    "mutation", ["ir_operator", "source_branch", "code_comparison", "code_branch"]
)
def test_corrupted_selection_certificates_fail(mutation, tmp_path):
    source = artifact("straight_line").lean_source
    if mutation == "ir_operator":
        corrupted = source.replace("(.bin .min", "(.bin .max", 1)
    elif mutation == "source_branch":
        corrupted = source.replace(
            "(.select (.cmp .gt (.var 1) (.lit (0 : Rat))) (.var 3) (.var 0))",
            "(.select (.cmp .gt (.var 1) (.lit (0 : Rat))) (.var 0) (.var 3))",
            1,
        )
    elif mutation == "code_comparison":
        corrupted = source.replace("if ops.lt y x then y else x", "if ops.lt x y then y else x", 1)
    else:
        corrupted = source.replace(
            "if branch then (readSlot env 2) else (readSlot env 3)",
            "if branch then (readSlot env 3) else (readSlot env 2)",
            1,
        )
    assert corrupted != source
    result = check_lean(tmp_path, corrupted)
    assert result.returncode != 0, "corrupted selection unexpectedly passed kernel checking"
    assert "error:" in result.stdout + result.stderr
