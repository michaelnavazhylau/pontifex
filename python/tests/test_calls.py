"""Bounded, compositional white-box calls: execution, scope, and certificates."""

from __future__ import annotations

import re
import textwrap
from fractions import Fraction

import pytest

from pontifex.errors import FrontendError
from pontifex.frontend import translate
from pontifex.interp import Failed, OutOfFuel, Returned, run_exact, run_float
from pontifex.ir import fn_of_json
from pontifex.pipeline import compare_outcomes, compile_source, load_python_function, observe_python
from pontifex.source import InlineCall, desugar
from pontifex.source import Ret as SourceRet

from lean_helpers import check_lean


PROGRAMS = {
    "hygiene": """
        def helper(x, y):
            temp = x + y
            x = y
            y = temp
            return x - y
        def f(x, y):
            temp = 17
            z = helper(y, x)
            w = helper(x, y)
            return z, w, x, y, temp
    """,
    "forward_and_transitive": """
        def f(x, y):
            z: float = middle(x, y)
            return leaf(z, x)
        def middle(x, y):
            z = leaf(y, x)
            return leaf(z, y)
        def leaf(x, y):
            x += y
            return x * y
    """,
    "caller_control_flow": """
        def advance(x, step):
            x += step
            return x
        def f(x, n):
            while n > 0:
                if x < 0:
                    x = advance(x, 2)
                else:
                    x = advance(x, 1)
                if x > 8:
                    return advance(x, -1)
                n -= 1
            return x
    """,
    "zero_arity": """
        def constant():
            return 7
        def f(x):
            y = constant()
            return constant()
    """,
    "private_namespace": """
        def fIR(x):
            return x + 1
        def f(x):
            return fIR(x)
    """,
    "scalar_args_from_arrays": """
        def helper(x, y):
            return x / y
        def f(x):
            xs = [x, 2.0]
            y = helper(xs[0], len(xs))
            return y
    """,
    "annotations": """
        def helper(x):
            temp: tuple[float, float] = x + 1
            return temp
        def f(x):
            return helper(x)
    """,
    "unselected_call_does_not_fail": """
        def helper(x):
            unused = 1 / x
            return x + 1
        def f(x):
            if x == 0:
                return x
            else:
                return helper(x)
    """,
    "callee_fault": """
        def helper(x, y):
            unused = x / y
            return 7
        def f(x, y):
            return helper(x, y)
    """,
}


def program(name):
    return textwrap.dedent(PROGRAMS[name])


@pytest.mark.parametrize("name", PROGRAMS)
def test_calls_match_python_and_json_round_trip(name):
    source = program(name)
    translated = translate(source, function="f")
    original = load_python_function(source, "f")
    decoded = fn_of_json(translated.fn.to_json())
    for args in (
        [Fraction(-2), Fraction(3)],
        [Fraction(5), Fraction(0)],
        [Fraction(1, 2), Fraction(2)],
    ):
        args = args[: translated.fn.arity]
        for values, run in ((args, run_exact), (list(map(float, args)), run_float)):
            expected = observe_python(original, values)
            actual = run(translated.fn, values, fuel=128)
            assert compare_outcomes(expected, actual) is None
            assert compare_outcomes(actual, run(decoded, values, fuel=128)) is None
    assert isinstance(run_exact(translated.fn, [0] * translated.fn.arity, fuel=0), OutOfFuel)


@pytest.mark.parametrize(
    "args, expected",
    [
        ("xs[1], 1 / 0", "indexOutOfBounds"),
        ("1 / 0, xs[1]", "divisionByZero"),
        ("1, xs[1]", "indexOutOfBounds"),
    ],
)
def test_arguments_evaluated_left_to_right_even_if_unused(args, expected):
    source = f"""
def helper(a, b):
    bad = 1 / 0
    return 7

def f():
    xs = []
    return helper({args})
"""
    translated = translate(source, function="f")
    for run in (run_exact, run_float):
        assert run(translated.fn, []) == Failed(expected)
    assert observe_python(load_python_function(source, "f"), []) == Failed(expected)


def test_zero_arity_call_preserves_signed_zero_in_float_mode():
    source = "def constant():\n    return -0.0\ndef f():\n    return constant()\n"
    fn = translate(source, function="f").fn
    assert compare_outcomes(run_float(fn, []), Returned((-0.0,))) is None
    # The exact reading deliberately has no sign of zero.
    assert run_exact(fn, []) == Returned((Fraction(0),))


def test_source_keeps_callee_reference_not_retranscribed_expansion():
    translated = translate(program("forward_and_transitive"), function="f")
    source = desugar(translated)
    assert isinstance(source.body[0], InlineCall)
    assert source.body[0].callee == "middle"
    assert source.body[0].target is not None
    assert isinstance(source.body[1], InlineCall)
    assert source.body[1].target is None
    assert [c.function_name for c in translated.callees] == ["middle", "leaf"]
    assert translated.callees[0].callees[0] is translated.callees[1]


@pytest.mark.parametrize(
    "body, message",
    [
        ("if helper(x) > 0:\n    return 1\nreturn 0", "inside a condition"),
        ("while helper(x) > 0:\n    x = x - 1\nreturn x", "inside a condition"),
        ("if x > 0 and helper(x) != 0:\n    return 1\nreturn 0", "inside a condition"),
        ("return helper(x) if x > 0 else 0", "conditional expression"),
        ("return 0 if x > 0 else helper(x)", "conditional expression"),
        ("return (x / 2) + helper(x)", "may not follow an expression that can fail"),
        ("return (x ** 2) + helper(x)", "may not follow an expression that can fail"),
        ("return (1 if x > 0 else 2) + helper(x)", "may not follow an expression that can fail"),
        (
            "xs = [x]\nxs[0] = helper(x)\nreturn xs[0] + helper(x)",
            "may not follow an expression that can fail",
        ),
        ("return helper(x=x)", "positional arguments"),
        ("return helper(*x)", "positional arguments"),
        ("return helper()", "expects 1 argument"),
        ("return helper(x, x)", "expects 1 argument"),
        ("xs = [x]\nreturn helper(xs)", "array and cannot be used"),
        ("helper = x\nreturn helper(x)", "shadowed by a local variable"),
        ("y = helper(x)\nhelper = x\nreturn y", "shadowed by a local variable"),
        ("return helper(x)\nreturn x", "unreachable statement"),
    ],
)
def test_unsupported_call_sites_are_located(body, message):
    source = (
        "def helper(x):\n    return x + 1\n\ndef f(x):\n" + textwrap.indent(body, "    ") + "\n"
    )
    with pytest.raises(FrontendError, match=message) as exc:
        translate(source, function="f", filename="calls.py")
    assert "calls.py:" in str(exc.value)


@pytest.mark.parametrize(
    "helper, message",
    [
        ("if x > 0:\n    return x\nreturn -x", "straight-line body"),
        ("while x > 0:\n    x -= 1\nreturn x", "straight-line body"),
        ("return x, x", "tuple results are deferred"),
        ("xs = [x]\nreturn xs[0]", "arrays are deferred"),
        ("return helper(x)", "recursive calls"),
        ("return x\nx += 1", "must end with one scalar return"),
    ],
)
def test_unsupported_helpers_are_rejected(helper, message):
    source = (
        "def helper(x):\n"
        + textwrap.indent(helper, "    ")
        + "\n\ndef f(x):\n    return helper(x)\n"
    )
    with pytest.raises(FrontendError, match=message):
        translate(source, function="f")


def test_callee_locals_do_not_leak_into_caller():
    source = "def helper(x):\n    private = x + 1\n    return private\ndef f(x):\n    y = helper(x)\n    return private\n"
    with pytest.raises(FrontendError, match="undefined name 'private'"):
        translate(source, function="f")


def test_tail_call_arity_must_agree_with_other_returns():
    source = "def helper(x):\n    return x\ndef f(x):\n    if x > 0:\n        return x, x\n    return helper(x)\n"
    with pytest.raises(FrontendError, match="different arity"):
        translate(source, function="f")


def test_duplicate_module_definitions_rejected():
    source = "def helper(x):\n    return x\ndef helper(x):\n    return -x\ndef f(x):\n    return helper(x)\n"
    with pytest.raises(FrontendError, match="duplicate function definition 'helper'"):
        translate(source, function="f")


def test_mutual_recursion_rejected():
    source = "def f(x):\n    return g(x)\ndef g(x):\n    return f(x)\n"
    with pytest.raises(FrontendError, match="f -> g -> f"):
        translate(source, function="f")


def test_shadowed_builtins_are_not_silently_compiled_as_builtins():
    source = "def abs(x):\n    return -x\ndef f(x):\n    return abs(x)\n"
    translated = translate(source, function="f")
    assert run_exact(translated.fn, [2]) == Returned((Fraction(-2),))
    with pytest.raises(FrontendError, match="shadowed by a local variable"):
        translate("def f(abs, x):\n    return abs(x)\n")


@pytest.mark.slow
@pytest.mark.parametrize("name", PROGRAMS)
def test_call_certificates_are_kernel_checked(name, tmp_path):
    artifact = compile_source(program(name), function="f", namespace="Calls")
    source = artifact.lean_source
    assert "native_decide" not in source
    assert "sorry" not in source
    assert ".inlineCall" in source
    assert "Callee0." in source
    source += "\n#print axioms Calls.f_program_lowering\n#print axioms Calls.f_link\n"
    result = check_lean(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    axiom_lists = re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout)
    assert len(axiom_lists) == 2, result.stdout
    for axioms in axiom_lists:
        assert set(axioms.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}


@pytest.mark.slow
def test_cosmetic_callee_slot_names_do_not_control_frame_size(tmp_path):
    artifact = compile_source(program("hygiene"), function="f", namespace="Calls")
    source = re.sub(r"slotNames := \[[^\n]*\]", "slotNames := []", artifact.lean_source, count=1)
    assert source != artifact.lean_source
    result = check_lean(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.mark.slow
@pytest.mark.parametrize("mutation", ["callee_source", "caller_ir", "argument", "frame"])
def test_corrupted_call_certificates_fail(mutation, tmp_path):
    artifact = compile_source(program("hygiene"), function="f", namespace="Calls")
    source = artifact.lean_source
    if mutation == "callee_source":
        source = source.replace("(.bin .add (.var", "(.bin .sub (.var", 1)
    elif mutation == "caller_ir":
        start = source.index("def fIR : Fn")
        source = source[:start] + source[start:].replace("(.bin .add", "(.bin .sub", 1)
    elif mutation == "argument":
        source = source.replace(
            "Callee0.helperIR.body [(.var 3), (.var 2)]",
            "Callee0.helperIR.body [(.var 2), (.var 3)]",
            1,
        )
    else:
        # Overwrite a caller parameter instead of the first private argument slot.
        start = source.index("def fIR : Fn")
        source = source[:start] + source[start:].replace(
            "(.assign 3 (.slot 1))", "(.assign 0 (.slot 1))", 1
        )
    assert source != artifact.lean_source
    result = check_lean(tmp_path, source)
    assert result.returncode != 0, "corrupted call unexpectedly passed kernel checking"
    assert "error:" in result.stdout + result.stderr


# ---------------------------------------------------------------------------
# Nested expression calls (T13 part 2)
# ---------------------------------------------------------------------------

NESTED = {
    "operands": """
        def helper(x, y):
            return x * 2 + y
        def f(x, y):
            return helper(x, y) + helper(y, 1)
    """,
    "arguments": """
        def helper(x, y):
            return x * 2 + y
        def f(x, y):
            return helper(helper(x, y), y)
    """,
    "loop_and_array": """
        def helper(x, y):
            return x * 2 + y
        def f(x, y, n):
            xs = [helper(x, 1), y]
            while n > 0:
                x = helper(x, 1)
                n = n - 1
            return x, xs[0]
    """,
    "return_tuple": """
        def helper(x, y):
            return x + y
        def f(x, y):
            return helper(x, y), helper(y, x)
    """,
    "augassign_and_annotated": """
        def helper(x, y):
            return x * y
        def f(x, y):
            x += helper(x, y)
            z: float = helper(y, 2) + x
            return z
    """,
    "array_store_value": """
        def helper(x, y):
            return x + y
        def f(x, y):
            xs = [x, y]
            xs[0] = helper(y, 2)
            return xs[0]
    """,
}


@pytest.mark.parametrize("name", NESTED)
def test_nested_calls_match_python(name):
    source = textwrap.dedent(NESTED[name])
    translated = translate(source, function="f")
    original = load_python_function(source, "f")
    decoded = fn_of_json(translated.fn.to_json())
    for args in (
        [Fraction(2), Fraction(3)],
        [Fraction(-1), Fraction(2)],
        [Fraction(0), Fraction(4)],
    ):
        args = args[: translated.fn.arity]
        if translated.fn.arity == 3:
            args = args + [Fraction(2)]
        for values, run in ((args, run_exact), ([float(a) for a in args], run_float)):
            expected = observe_python(original, values)
            actual = run(translated.fn, values, fuel=256)
            assert compare_outcomes(expected, actual) is None, (name, values)
            assert compare_outcomes(actual, run(decoded, values, fuel=256)) is None


def test_nested_calls_preserve_left_to_right_fault_order():
    source = """
def helper(x, y):
    return x + y

def f():
    xs = []
    return helper(1 / 0, xs[1])
"""
    translated = translate(source, function="f")
    assert run_exact(translated.fn, []) == Failed("divisionByZero")
    assert observe_python(load_python_function(source, "f"), []) == Failed("divisionByZero")

    source = """
def helper(x, y):
    return x + y

def f():
    xs = []
    y = helper(xs[1], 1 / 0)
    return y
"""
    translated = translate(source, function="f")
    assert run_exact(translated.fn, []) == Failed("indexOutOfBounds")


def test_call_inside_loop_is_reevaluated_each_iteration():
    source = """
def step(x, n):
    return x + n

def f(n):
    total = 0
    while n > 0:
        total = total + step(n, 1)
        n = n - 1
    return total
"""
    translated = translate(source, function="f")
    original = load_python_function(source, "f")
    for n in (0, 1, 3, 5):
        expected = observe_python(original, [n])
        assert compare_outcomes(expected, run_exact(translated.fn, [Fraction(n)])) is None


def test_hoisted_call_is_a_temporary_not_a_user_variable():
    translated = translate(textwrap.dedent(NESTED["operands"]), function="f")
    source = desugar(translated)
    kinds = [type(statement).__name__ for statement in source.body]
    assert kinds[:2] == ["InlineTemp", "InlineTemp"]
    assert isinstance(source.body[2], SourceRet)
    assert all(0 <= statement.target < 10 for statement in source.body[:2])
    # Assignment-position calls keep binding the user variable.
    binding = translate(
        "def helper(x):\n    return x + 1\ndef f(x):\n    z = helper(x)\n    return z\n",
        function="f",
    )
    assert isinstance(desugar(binding).body[0], InlineCall)
    # The hoisted temporary never becomes an IR call node or JSON shape.
    assert "inline" not in translated.fn.to_json_text()


@pytest.mark.slow
@pytest.mark.parametrize("name", NESTED)
def test_nested_call_certificates_are_kernel_checked(name, tmp_path):
    artifact = compile_source(textwrap.dedent(NESTED[name]), function="f", namespace="Nested")
    source = artifact.lean_source
    assert ".inlineTemp" in source
    assert "sorry" not in source
    source += "\n#print axioms Nested.f_program_lowering\n#print axioms Nested.f_link\n"
    result = check_lean(tmp_path, source)
    assert result.returncode == 0, result.stdout + result.stderr
    axioms = re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout)
    assert len(axioms) == 2, result.stdout
    for names in axioms:
        assert set(names.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}


@pytest.mark.slow
@pytest.mark.parametrize("mutation", ["argument_order", "temp_slot", "callee_body"])
def test_corrupted_nested_call_certificates_fail(mutation, tmp_path):
    artifact = compile_source(
        textwrap.dedent(NESTED["arguments"]), function="f", namespace="Nested"
    )
    source = artifact.lean_source
    if mutation == "argument_order":
        corrupted = source.replace("[(.var 2), (.var 1)]", "[(.var 1), (.var 2)]", 1)
    elif mutation == "temp_slot":
        corrupted = re.sub(
            r"\(\.inlineTemp (\d+)",
            lambda m: f"(.inlineTemp {int(m.group(1)) + 1}",
            source,
            count=1,
        )
    else:
        corrupted = source.replace("(.bin .mul", "(.bin .add", 1)
    assert corrupted != source
    result = check_lean(tmp_path, corrupted)
    assert result.returncode != 0, "corrupted nested call passed kernel checking"
    assert "error:" in result.stdout + result.stderr
