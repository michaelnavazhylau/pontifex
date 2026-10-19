"""Surface desugaring and the core-source transcription used by the certificate."""
from __future__ import annotations

import textwrap

from pyverif.frontend import translate
from pyverif.source import (
    Assign,
    Bin,
    Ite,
    Lit,
    Ret,
    Un,
    Var,
    While,
    desugar,
)


def _source(program: str):
    program = textwrap.dedent(program)
    translated = translate(program, filename="prog.py")
    return desugar(translated), translated


def test_ids_are_sorted_by_name():
    sfn, _ = _source(
        """
        def f(z, a):
            b = z + a
            return b
        """
    )
    # sorted names: a, b, z -> 0, 1, 2
    assert sfn.param_ids == (2, 0)
    assign = sfn.body[0]
    assert isinstance(assign, Assign)
    assert assign.var == 1
    assert assign.expr == Bin("add", Var(2), Var(0))


def test_annotations_are_not_variables():
    sfn, _ = _source(
        """
        def f(x: float, y: tuple[float, float]) -> tuple[float, float]:
            if x > 0:
                x = x + 1
            return x, y
        """
    )
    # Only x and y exist; ids are 0 and 1 in sorted order (x < y).
    assert sfn.param_ids == (0, 1)


def test_augassign_desugars_to_bin():
    sfn, _ = _source(
        """
        def f(x, y):
            x += y
            x *= 2
            return x
        """
    )
    first, second = sfn.body[0], sfn.body[1]
    assert first.expr == Bin("add", Var(0), Var(1))
    assert second.expr == Bin("mul", Var(first.var), Lit(2))


def test_pow_is_repeated_multiplication():
    sfn, _ = _source("def f(x):\n    return x ** 3\n")
    ret = sfn.body[0]
    assert isinstance(ret, Ret)
    expected = Lit(1)
    for _ in range(3):
        expected = Bin("mul", expected, Var(0))
    assert ret.exprs[0] == expected


def test_docstrings_and_pass_become_skip():
    sfn, _ = _source(
        '''
        def f(x):
            """doc"""
            pass
            return x
        '''
    )
    kinds = [type(s).__name__ for s in sfn.body]
    assert kinds[:2] == ["Skip", "Skip"]


def test_control_flow_shape_is_preserved():
    sfn, _ = _source(
        """
        def f(x):
            while x < 3:
                if x == 1:
                    x = x + 2
            return x
        """
    )
    loop = sfn.body[0]
    assert isinstance(loop, While)
    assert isinstance(loop.body[0], Ite)
    assert loop.body[0].else_ == ()


def test_abs_and_unary_minus_desugar_to_un():
    sfn, _ = _source("def f(x):\n    return abs(-x)\n")
    assert sfn.body[0].exprs[0] == Un("abs", Un("neg", Var(0)))
