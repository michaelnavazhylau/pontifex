"""Reference interpreter and the source-level oracle."""

from __future__ import annotations

import textwrap
from fractions import Fraction

import pytest

from pontifex.errors import InterpreterError
from pontifex.interp import (
    FellThrough,
    Failed,
    OutOfFuel,
    Returned,
    float_bits,
    rat_string,
    run_exact,
    run_float,
    to_option,
)
from pontifex.frontend import translate
from pontifex.pipeline import run_python_source

from conftest import example_source, translate_example


def test_exact_free_fall_step():
    fn = translate_example("free_fall").fn
    out = run_exact(fn, [Fraction(1), Fraction(2), Fraction(3), Fraction(4)])
    assert isinstance(out, Returned)
    assert out.values == (Fraction(57), Fraction(14))


def test_float_free_fall_step():
    fn = translate_example("free_fall").fn
    out = run_float(fn, [1.0, 2.0, 3.0, 4.0])
    assert out.values == (57.0, 14.0)


def test_source_and_ir_agree_exactly():
    source = example_source("free_fall")
    fn = translate_example("free_fall").fn
    args = (Fraction(1, 3), Fraction(-2, 7), Fraction(5, 11), Fraction(1, 13))
    assert run_python_source(source, fn.name, args) == to_option(run_exact(fn, args))


def test_loop_exact():
    fn = translate_example("free_fall_loop").fn
    out = run_exact(fn, [Fraction(1), Fraction(0), Fraction(0), Fraction(1), Fraction(1, 2)])
    assert out.values == (Fraction(3, 4), Fraction(1))


def test_loop_out_of_fuel():
    fn = translate_example("free_fall_loop").fn
    # dt = 0 -> the loop never advances: fuel must run out
    out = run_exact(fn, [Fraction(1), Fraction(0), Fraction(0), Fraction(1), Fraction(0)], fuel=32)
    assert isinstance(out, OutOfFuel)


def test_clamped_branch_merge():
    fn = translate_example("clamped_step").fn
    # x + v*dt = 0 + 10*1 = 10 > 3 -> clamp
    assert run_exact(fn, [Fraction(0), Fraction(10), Fraction(1), Fraction(3)]).values == (
        Fraction(3),
        Fraction(0),
    )
    # 0 + 1*1 = 1 <= 3 -> unchanged velocity
    assert run_exact(fn, [Fraction(0), Fraction(1), Fraction(1), Fraction(3)]).values == (
        Fraction(1),
        Fraction(1),
    )


def test_division_by_zero_is_an_observable_failure():
    from pontifex.frontend import translate

    fn = translate("def f(x: float, y: float):\n    return x / y\n", filename="div.py").fn
    assert run_exact(fn, [Fraction(1), Fraction(0)]) == Failed("divisionByZero")


def test_wire_formats():
    assert rat_string(Fraction(-6, 4)) == "-3/2"
    assert float_bits(1.0) == "0x3ff0000000000000"
    assert float_bits(-0.0) != float_bits(0.0)


def test_array_read_update_and_len():
    program = textwrap.dedent(
        """
        def f(i, dt):
            xs = [1.0, 2.0, 3.0]
            xs[i] = xs[i] + dt
            return xs[0], xs[1], xs[2], len(xs)
        """
    )
    fn = translate(program, filename="arr.py").fn
    out = run_exact(fn, [Fraction(1), Fraction(1, 2)])
    assert out.values == (Fraction(1), Fraction(5, 2), Fraction(3), Fraction(3))
    assert run_float(fn, [1, 0.5]).values == (1.0, 2.5, 3.0, 3.0)


def test_array_updates_are_functional_not_aliased():
    # The update writes a fresh slot; the slot bound before the store is
    # unchanged in the fell-through environment.
    program = textwrap.dedent(
        """
        def f(v):
            xs = [1.0, 2.0]
            xs[0] = v
            return xs[0]
        """
    )
    fn = translate(program, filename="alias.py").fn
    from pontifex.interp import Interpreter

    interp = Interpreter()
    before = interp.exec(fn.body.body[0], {0: Fraction(7)}, fuel=16)
    assert isinstance(before, FellThrough)
    after = interp.exec(fn.body.body[1], before.env, fuel=16)
    assert isinstance(after, FellThrough)
    assert before.env != after.env
    assert before.env[1] == [Fraction(1), Fraction(2)]  # slot 1 is the literal
    assert after.env[2] == [Fraction(7), Fraction(2)]  # slot 2 is the update


def test_array_index_failures():
    fn = translate("def f(i):\n    xs = [1.0, 2.0]\n    return xs[i]\n", filename="bounds.py").fn
    assert run_exact(fn, [Fraction(0)]).values == (Fraction(1),)
    for index in (Fraction(2), Fraction(-1), Fraction(1, 2)):
        outcome = run_exact(fn, [index])
        assert isinstance(outcome, Failed)
        assert outcome.error == "indexOutOfBounds"
