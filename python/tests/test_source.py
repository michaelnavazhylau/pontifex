"""Surface desugaring and the core-source transcription used by the certificate."""
from __future__ import annotations

import textwrap

from pontifex.frontend import translate
from pontifex.source import (
    ArrayLit,
    Assign,
    Bin,
    Index,
    Ite,
    Len,
    Lit,
    Ret,
    Pow,
    Set,
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


def test_pow_is_explicit_in_core_source():
    sfn, _ = _source("def f(x):\n    return x ** 3\n")
    ret = sfn.body[0]
    assert isinstance(ret, Ret)
    assert ret.exprs[0] == Pow(Var(0), 3)


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


def test_returns_are_preserved_inside_branches():
    sfn, _ = _source(
        """
        def f(x):
            if x > 0:
                return x
            return -x
        """
    )
    assert isinstance(sfn.body[0], Ite)
    assert isinstance(sfn.body[0].then_[0], Ret)
    assert isinstance(sfn.body[1], Ret)


def test_array_constructs_are_preserved():
    sfn, _ = _source(
        """
        def f(i):
            xs = [1.0, 2.0]
            xs[i] = xs[i] + 1
            return xs[0], len(xs)
        """
    )
    assert isinstance(sfn.body[0], Assign)
    assert isinstance(sfn.body[0].expr, ArrayLit)
    assert isinstance(sfn.body[1], Assign)
    store = sfn.body[1].expr
    assert isinstance(store, Set)
    assert isinstance(store.array, Var)
    assert isinstance(store.value, Bin)
    assert isinstance(store.value.lhs, Index)
    assert isinstance(sfn.body[2].exprs[1], Len)
