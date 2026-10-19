"""Frontend: lowering, SSA discipline, and precise rejections."""

from __future__ import annotations

import textwrap

import pytest

from pontifex.errors import FrontendError, UnsupportedError
from pontifex.frontend import translate
from pontifex.ir import (
    And,
    Assign,
    Bin,
    Cmp,
    Ite,
    Lit,
    Not,
    Ret,
    Seq,
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
    "return_in_if": "def f(x: float):\n    if x < 0:\n        return x\n    return x\n",
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
