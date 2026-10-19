"""Frontend: lowering, SSA discipline, and precise rejections."""

from __future__ import annotations

import textwrap

import pytest

from pontifex.errors import FrontendError, UnsupportedError
from pontifex.frontend import translate
from pontifex.interp import run_exact, to_option
from pontifex.ir import (
    And,
    ArrayLit,
    Assign,
    Bin,
    Cmp,
    Index,
    Ite,
    Len,
    Lit,
    Not,
    Ret,
    Seq,
    Set,
    Slot,
    Pow,
    Un,
    While,
    fn_of_json,
    slots_read,
    stmts,
)

from conftest import translate_example


def written_slots(stmt) -> list[int]:
    out: list[int] = []
    for s in stmts(stmt):
        if isinstance(s, Assign):
            out.append(s.slot)
        if isinstance(s, (Ite, While)):
            out.extend(p.slot for p in s.phis)
    return out


def test_free_fall_ssa_slots():
    t = translate_example("free_fall")
    fn = t.fn
    assert fn.name == "step"
    assert fn.params == ("x", "v", "a", "dt")
    # two fresh slots for the two assignments
    assert len(fn.slot_names) == 6
    writes = written_slots(fn.body)
    assert len(writes) == len(set(writes)) == 2
    assert set(writes).isdisjoint(range(4))
    # returns the two fresh slots, in source order (x then v)
    ret = [s for s in stmts(fn.body) if isinstance(s, Ret)][0]
    assert [e.index for e in ret.exprs] == [5, 4]


def test_augassign_and_abs():
    t = translate(
        textwrap.dedent(
            """
            def f(x: float, y: float):
                x += y
                x *= 2
                y = abs(x - y)
                return x, y
            """
        ),
        filename="aug.py",
    )
    ops = [s.expr.op for s in stmts(t.fn.body) if isinstance(s, Assign)]
    assert ops[:2] == ["add", "mul"]
    unary = [s.expr for s in stmts(t.fn.body) if isinstance(s, Assign) and isinstance(s.expr, Un)]
    assert unary[0].op == "abs"


def test_pow_preserves_backend_specific_operation():
    t = translate("def f(x: float):\n    return x ** 3\n", filename="pow.py")
    ret = [s for s in stmts(t.fn.body) if isinstance(s, Ret)][0]
    expr = ret.exprs[0]
    assert isinstance(expr, Pow)
    assert expr.base == Slot(0)
    assert expr.exponent == 3


def test_if_produces_phis():
    t = translate_example("clamped_step")
    ite = [s for s in stmts(t.fn.body) if isinstance(s, Ite)][0]
    assert len(ite.phis) == 2  # both v and x are reassigned in the branch
    writes = written_slots(t.fn.body)
    assert len(writes) == len(set(writes))
    # phi slot chosen by the branch, not by the condition being true
    assert all(p.slot not in (p.lhs, p.rhs) for p in ite.phis)


def test_while_carries_loop_variables():
    t = translate_example("free_fall_loop")
    loop = [s for s in stmts(t.fn.body) if isinstance(s, While)][0]
    headers = {p.slot for p in loop.phis}
    assert headers == {6, 7, 8}  # t, v, x headers
    assert loop.phis[0].rhs in range(6)  # initial value comes from before the loop
    assigns = [s.slot for s in stmts(t.fn.body) if isinstance(s, Assign)]
    # header slots are written on entry (explicit init) and on the back edge (the
    # phi), which is exactly the two incoming edges of an SSA loop phi; every
    # other slot is written exactly once.
    non_header = [slot for slot in assigns if slot not in headers]
    assert len(non_header) == len(set(non_header))
    assert set(assigns) & headers == headers
    # the condition reads a loop-carried header
    assert slots_read(loop.cond) & headers


def test_boolean_conditions():
    t = translate(
        textwrap.dedent(
            """
            def f(x: float, y: float):
                if x < y and not (x == 0):
                    x = y
                return x
            """
        ),
        filename="cond.py",
    )
    ite = [s for s in stmts(t.fn.body) if isinstance(s, Ite)][0]
    assert isinstance(ite.cond, And)
    assert isinstance(ite.cond.rhs, Not)
    assert isinstance(ite.cond.rhs.arg, Cmp)
    assert ite.cond.rhs.arg.op == "eq"


def test_float_literals_are_exact_binary_values():
    t = translate("def f():\n    return 0.1\n", filename="lit.py")
    ret = [s for s in stmts(t.fn.body) if isinstance(s, Ret)][0]
    value = ret.exprs[0]
    assert isinstance(value, Lit)
    assert value.value == 0.1  # Fraction == float compares by numeric value
    assert value.value.denominator == 2**55


def test_json_roundtrip():
    t = translate_example("clamped_step")
    import json

    decoded = fn_of_json(json.loads(t.fn.to_json_text()))
    assert decoded == t.fn


BAD_PROGRAMS = {
    "import": "import math\ndef f(x: float):\n    return x\n",
    "for": "def f(x: float):\n    for i in range(3):\n        x = x + i\n    return x\n",
    "break": "def f(x: float):\n    while x < 3:\n        break\n    return x\n",
    "fallthrough": "def f(x: float):\n    if x > 0:\n        return x\n",
    "return_arity": "def f(x: float, y: float):\n    if x > 0:\n        return x\n    return x, y\n",
    "chained_compare": "def f(x: float, y: float):\n    if x < y < 3:\n        x = y\n    return x\n",
    "subscript": "def f(x: float):\n    return x[0]\n",
    "call": "def f(x: float):\n    return min(x, 2)\n",
    "attribute": "def f(x: float):\n    return x.real\n",
    "list_literal": "def f(x: float):\n    return [x]\n",
    "default_arg": "def f(x: float = 1):\n    return x\n",
    "decorator": "@staticmethod\ndef f(x: float):\n    return x\n",
    "kwonly": "def f(*, x: float):\n    return x\n",
    "undefined": "def f(x: float):\n    return y\n",
    "frac_pow": "def f(x: float):\n    return x ** 0.5\n",
    "neg_pow": "def f(x: float):\n    return x ** -1\n",
    "bool_scalar": "def f(x: float):\n    return True\n",
    "bool_as_scalar": "def f(x: float, y: float):\n    return x < y\n",
    "no_return": "def f(x: float):\n    x = x + 1\n",
    "return_not_last": "def f(x: float):\n    return x\n    x = x + 1\n",
    "else_loop": "def f(x: float):\n    while x < 1:\n        x = x + 1\n    else:\n        x = 0\n    return x\n",
    "tuple_assign": "def f(x: float):\n    y, z = x, x\n    return y\n",
    "chained_assign": "def f(x: float):\n    y = z = x\n    return y\n",
    "lambda": "def f(x: float):\n    g = lambda y: y\n    return x\n",
    "ifexp": "def f(x: float, y: float):\n    return x if y > 0 else y\n",
    "multiple_functions": "def f(x: float):\n    return x\n\ndef g(y: float):\n    return y\n",
    "loop_uninitialised": "def f(x: float):\n    while x < 3:\n        z = 1\n        x = x + z\n    return x\n",
}


@pytest.mark.parametrize("name", sorted(BAD_PROGRAMS))
def test_rejections(name):
    with pytest.raises(FrontendError):
        translate(BAD_PROGRAMS[name], filename=f"{name}.py")


def test_error_message_has_location_and_reason():
    with pytest.raises(UnsupportedError) as info:
        translate("def f(x: float):\n    return x.real\n", filename="attr.py")
    text = str(info.value)
    assert "attr.py:2" in text
    assert "attribute" in text


def test_select_function_by_name():
    source = "def f(x: float):\n    return x\n\ndef g(x: float, y: float):\n    return x + y\n"
    t = translate(source, filename="two.py", function="g")
    assert t.fn.params == ("x", "y")


# ---------------------------------------------------------------------------
# Multi-exit returns (T11)
# ---------------------------------------------------------------------------


def _agrees_with_python(program: str, vectors):
    from fractions import Fraction

    source = textwrap.dedent(program)
    fn = translate(source, filename="prog.py").fn
    namespace: dict = {}
    exec(source, namespace)  # noqa: S102 - CPython is the oracle in this test
    python_fn = namespace[fn.name]
    for args in vectors:
        raw = python_fn(*args)
        expected = tuple(Fraction(v) for v in (raw if isinstance(raw, tuple) else (raw,)))
        assert to_option(run_exact(fn, args)) == expected, args


def test_early_return_guard_needs_no_phi():
    t = translate(
        textwrap.dedent(
            """
            def f(x: float, y: float):
                if x < 0:
                    return -x
                return x + y
            """
        ),
        filename="guard.py",
    )
    body = t.fn.body
    assert isinstance(body, Seq)
    ite = body.body[0]
    assert isinstance(ite, Ite)
    assert ite.phis == ()
    assert isinstance(ite.then_.body[0], Ret)
    _agrees_with_python(
        """
        def f(x: float, y: float):
            if x < 0:
                return -x
            return x + y
        """,
        [(-2, 3), (2, 3), (0, 0)],
    )


def test_returning_branch_contributes_no_merge_input():
    from fractions import Fraction

    program = """
        def f(x: float, c: float):
            if c > 0:
                y = x + 1
            else:
                return x
            return y
    """
    fn = translate(textwrap.dedent(program), filename="phi.py").fn
    ite = fn.body.body[0]
    assert isinstance(ite, Ite)
    assert len(ite.phis) == 1
    phi = ite.phis[0]
    # The false branch returns, so its phi input is a dead but defined slot.
    assert phi.lhs == phi.rhs
    namespace: dict = {}
    exec(textwrap.dedent(program), namespace)  # noqa: S102 - oracle
    for args in [
        (Fraction(2), Fraction(1)),
        (Fraction(2), Fraction(0)),
        (Fraction(2), Fraction(-1)),
    ]:
        expected = namespace["f"](*args)
        assert to_option(run_exact(fn, args)) == (expected,)
    _agrees_with_python(program, [(2, 1), (2, -1)])


def test_returns_on_every_path_without_trailing_return():
    from pontifex.emit import return_arity

    fn = translate(
        textwrap.dedent(
            """
            def f(x: float):
                if x > 0:
                    return 1
                else:
                    return 2
            """
        ),
        filename="both.py",
    ).fn
    assert isinstance(fn.body, Seq)
    assert isinstance(fn.body.body[0], Ite)
    assert not isinstance(fn.body.body[-1], Ret)
    assert return_arity(fn.body) == 1
    _agrees_with_python(
        """
        def f(x: float):
            if x > 0:
                return 1
            else:
                return 2
        """,
        [(1,), (-1,), (0,)],
    )


def test_early_return_inside_a_loop():
    program = """
        def f(x: float, n: float):
            if n <= 0:
                return x
            while n > 0:
                if x > 8:
                    return 8
                x = x + 1
                n = n - 1
            return x
    """
    t = translate(textwrap.dedent(program), filename="loop.py")
    loop = [s for s in stmts(t.fn.body) if isinstance(s, While)][0]
    assert {p.slot for p in loop.phis} == {2, 3}  # n and x headers
    assert any(isinstance(s, Ret) for s in stmts(loop.body))
    _agrees_with_python(program, [(-2, 3), (2, 3), (9, 2), (1, 0), (0, 0)])


def test_variable_assigned_only_on_returning_path_is_not_loop_carried():
    program = """
        def f(x: float):
            while x < 3:
                if x > 0:
                    y = 1
                    return y
                x = x + 1
            return x
    """
    fn = translate(textwrap.dedent(program), filename="unbound.py").fn
    loop = [s for s in stmts(fn.body) if isinstance(s, While)][0]
    assert len(loop.phis) == 1  # only x is carried; y never reaches the back edge
    _agrees_with_python(program, [(2,), (-1,), (5,)])


def test_unreachable_code_after_return_is_rejected():
    with pytest.raises(UnsupportedError, match="unreachable"):
        translate("def f(x: float):\n    return x\n    x = x + 1\n", filename="dead.py")


def test_function_must_return_on_every_path():
    with pytest.raises(FrontendError, match="does not return on every path"):
        translate("def f(x: float):\n    if x > 0:\n        return x\n", filename="partial.py")


# ---------------------------------------------------------------------------
# Arrays (T12)
# ---------------------------------------------------------------------------

ARRAY_PROGRAM = """
def f(i: float, dt: float):
    xs = [1.0, 2.0, 3.0]
    xs[i] = xs[i] + dt
    return xs[0], xs[1], xs[2], len(xs)
"""


def test_array_literal_store_and_len_lower_to_ssa():
    t = translate(textwrap.dedent(ARRAY_PROGRAM), filename="arr.py")
    assigns = [s for s in stmts(t.fn.body) if isinstance(s, Assign)]
    assert isinstance(assigns[0].expr, ArrayLit)
    assert isinstance(assigns[1].expr, Set)
    # xs starts in slot 2; the store writes a *fresh* slot, so the update is a
    # functional array value and earlier bindings are not aliased.
    assert assigns[1].expr.array == Slot(2)
    assert assigns[1].slot == 3
    assert isinstance(assigns[1].expr.value, Bin)
    assert isinstance(assigns[1].expr.value.lhs, Index)
    ret = [s for s in stmts(t.fn.body) if isinstance(s, Ret)][0]
    assert isinstance(ret.exprs[-1], Len)
    _agrees_with_python(textwrap.dedent(ARRAY_PROGRAM), [(1, 0), (0, 2)])


def test_array_kinds_are_tracked_through_branches():
    program = """
        def f(c: float, dt: float):
            if c > 0:
                xs = [1.0, 2.0]
            else:
                xs = [3.0, 4.0]
            xs[0] = xs[0] + dt
            return xs[0], xs[1]
    """
    t = translate(textwrap.dedent(program), filename="merge.py")
    ite = [s for s in stmts(t.fn.body) if isinstance(s, Ite)][0]
    assert len(ite.phis) == 1  # one phi carries the array through the merge
    _agrees_with_python(textwrap.dedent(program), [(1, 1), (-1, 1)])


def test_scalar_and_array_kinds_cannot_be_confused():
    with pytest.raises(UnsupportedError, match="scalar, not an array"):
        translate("def f(x: float):\n    return x[0]\n", filename="s.py")
    with pytest.raises(UnsupportedError, match="array and cannot be used"):
        translate("def f(x: float):\n    xs = [1.0]\n    return xs\n", filename="a.py")
