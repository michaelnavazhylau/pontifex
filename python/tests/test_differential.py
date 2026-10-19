"""Differential testing: Python source vs IR interpreter vs Lean semantics.

Three implementations of the same function are compared:

* the original Python function (executed),
* the reference interpreter over the translated IR (exact and binary64),
* the Lean reference semantics, through ``lake exe pontifex``.

Hypothesis drives the source-vs-IR comparison; the Lean oracle is exercised in
batched calls because each call is a subprocess.
"""

from __future__ import annotations

import itertools
import random
from fractions import Fraction

import pytest
from hypothesis import HealthCheck, given, settings
from hypothesis import strategies as st

from pontifex.interp import (
    InterpreterError,
    float_bits,
    run_exact,
    run_float,
    to_option,
)
from pontifex.pipeline import compile_file, run_lean, run_python_source

from conftest import BRANCHING, EXAMPLES, LOOPING, STRAIGHT_LINE, example_source, translate_example

ALL_SIMPLE = STRAIGHT_LINE + BRANCHING


@st.composite
def small_rationals(draw):
    return Fraction(draw(st.integers(-20, 20)), draw(st.integers(1, 9)))


@st.composite
def finite_floats(draw):
    return draw(
        st.floats(
            min_value=-100.0,
            max_value=100.0,
            allow_nan=False,
            allow_infinity=False,
            width=64,
        )
    )


def _args_for(stem: str, values):
    """Shape raw random values according to the example's argument roles."""
    if stem in LOOPING:
        t_end, x, v, a, dt = values
        return [abs(t_end) % 5, x, v, a, (abs(dt) % Fraction(1, 2)) + Fraction(1, 8)]
    return list(values)


def _compare(left, right) -> str | None:
    lv, rv = to_option(left), to_option(right)
    if lv is None or rv is None:
        return None if type(left) is type(right) else f"{type(left)} vs {type(right)}"
    if len(lv) != len(rv):
        return f"arity {lv} vs {rv}"
    for i, (a, b) in enumerate(zip(lv, rv)):
        if isinstance(a, float) or isinstance(b, float):
            if float_bits(float(a)) != float_bits(float(b)):
                return f"arg {i}: {a!r} vs {b!r} bits"
        elif Fraction(a) != Fraction(b):
            return f"arg {i}: {a!r} vs {b!r}"
    return None


# ---------------------------------------------------------------------------
# Source vs IR (Hypothesis)
# ---------------------------------------------------------------------------


@pytest.mark.parametrize("stem", ALL_SIMPLE)
@settings(max_examples=60, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(values=st.lists(small_rationals(), min_size=4, max_size=4))
def test_source_equals_ir_exact(stem, values):
    fn = translate_example(stem).fn
    if fn.arity != 4:
        pytest.skip("strategy is shaped for arity 4")
    args = _args_for(stem, values)
    source = example_source(stem)
    expected = run_python_source(source, fn.name, args)
    actual = to_option(run_exact(fn, args))
    assert actual is not None
    assert [Fraction(v) for v in actual] == [Fraction(v) for v in expected]


@pytest.mark.parametrize("stem", ALL_SIMPLE)
@settings(max_examples=60, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(values=st.lists(finite_floats(), min_size=4, max_size=4))
def test_source_equals_ir_float(stem, values):
    fn = translate_example(stem).fn
    args = _args_for(stem, values)
    source = example_source(stem)
    expected = run_python_source(source, fn.name, args)
    actual = to_option(run_float(fn, args))
    assert actual is not None
    assert [float_bits(float(v)) for v in actual] == [float_bits(float(v)) for v in expected]


@pytest.mark.parametrize("stem", LOOPING)
@settings(max_examples=40, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    t_end=finite_floats(),
    x=finite_floats(),
    v=finite_floats(),
    a=finite_floats(),
    dt=finite_floats(),
)
def test_loop_source_equals_ir_float(stem, t_end, x, v, a, dt):
    fn = translate_example(stem).fn
    args = _args_for(stem, [t_end, x, v, a, dt])
    source = example_source(stem)
    expected = run_python_source(source, fn.name, args)
    actual = to_option(run_float(fn, args, fuel=4096))
    assert actual is not None
    assert [float_bits(float(v)) for v in actual] == [float_bits(float(v)) for v in expected]


@pytest.mark.parametrize("stem", LOOPING)
@settings(max_examples=40, deadline=None, suppress_health_check=[HealthCheck.too_slow])
@given(
    t_end=small_rationals(),
    x=small_rationals(),
    v=small_rationals(),
    a=small_rationals(),
    dt=small_rationals(),
)
def test_loop_source_equals_ir_exact(stem, t_end, x, v, a, dt):
    fn = translate_example(stem).fn
    args = _args_for(stem, [t_end, x, v, a, dt])
    source = example_source(stem)
    expected = run_python_source(source, fn.name, args)
    actual = to_option(run_exact(fn, args, fuel=4096))
    assert actual is not None
    assert [Fraction(v) for v in actual] == [Fraction(v) for v in expected]


# ---------------------------------------------------------------------------
# IR vs Lean (batched subprocess)
# ---------------------------------------------------------------------------


def _sample_vectors(stem: str) -> list[list[Fraction]]:
    values = [Fraction(0), Fraction(1), Fraction(-1), Fraction(1, 2), Fraction(3, 7)]
    fn = translate_example(stem).fn
    rng = random.Random(f"{stem}-seed")
    vectors = []
    for _ in range(6):
        args = [rng.choice(values) for _ in range(fn.arity)]
        if stem in LOOPING:
            args[0] = abs(args[0]) % 3  # t_end
            args[4] = abs(args[4]) % Fraction(1, 2) + Fraction(1, 8)  # dt
        vectors.append(args)
    return vectors


@pytest.mark.parametrize("stem", STRAIGHT_LINE + BRANCHING + LOOPING)
def test_ir_equals_lean_rat(stem, lean_exe):
    artifacts = compile_file(EXAMPLES / f"{stem}.py")
    vectors = _sample_vectors(stem)
    lean = run_lean(lean_exe, artifacts.ir_json, vectors, mode="rat", fuel=512)
    for args, lean_out in zip(vectors, lean):
        ours = run_exact(artifacts.fn, args, fuel=512)
        assert _compare(ours, lean_out) is None, (stem, args, ours, lean_out)


@pytest.mark.parametrize("stem", STRAIGHT_LINE + BRANCHING + LOOPING)
def test_ir_equals_lean_float(stem, lean_exe):
    artifacts = compile_file(EXAMPLES / f"{stem}.py")
    vectors = _sample_vectors(stem)
    lean = run_lean(lean_exe, artifacts.ir_json, vectors, mode="float", fuel=512)
    for args, lean_out in zip(vectors, lean):
        ours = run_float(artifacts.fn, args, fuel=512)
        assert _compare(ours, lean_out) is None, (stem, args, ours, lean_out)


@pytest.mark.parametrize("stem", STRAIGHT_LINE + BRANCHING + LOOPING)
def test_source_equals_lean_float_end_to_end(stem, lean_exe):
    artifacts = compile_file(EXAMPLES / f"{stem}.py")
    vectors = _sample_vectors(stem)
    lean = run_lean(lean_exe, artifacts.ir_json, vectors, mode="float", fuel=512)
    source = example_source(stem)
    for args, lean_out in zip(vectors, lean):
        expected = run_python_source(source, artifacts.fn.name, [float(a) for a in args])
        actual = to_option(lean_out)
        assert actual is not None
        assert [float_bits(float(v)) for v in actual] == [
            float_bits(float(v)) for v in expected
        ], (stem, args, expected, actual)
