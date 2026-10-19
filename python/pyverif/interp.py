"""Reference interpreter over the SSA IR.

This is the *Python-side* reading of the IR, used for differential testing
against the Lean reference semantics.  It mirrors ``PyVerif/Core/Semantics.lean``
clause by clause, including the fuel discipline for loops.

Two numeric modes:

``exact=True``
    scalars are :class:`fractions.Fraction`; the mathematical reading.
``exact=False``
    scalars are Python ``float``, i.e. IEEE-754 binary64; the operational
    reading of CPython.

Division by zero is an error in both modes (the Lean `Rat`/`Float` backends are
total, so zero division is *outside* the modelled subset; the frontend cannot
detect it statically and the harness avoids it).
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Callable, Mapping, Sequence

from .errors import InterpreterError
from .ir import (
    And,
    Assign,
    Bin,
    Cmp,
    Cond,
    Expr,
    Fn,
    Ite,
    Lit,
    Not,
    Or,
    Ret,
    Seq,
    Skip,
    Slot,
    Stmt,
    Un,
    Where,
    While,
)

Number = Any  # Fraction or float

DEFAULT_FUEL = 512


@dataclass(frozen=True)
class Returned:
    values: tuple[Number, ...]


@dataclass(frozen=True)
class FellThrough:
    env: dict[int, Number]


@dataclass(frozen=True)
class OutOfFuel:
    pass


Outcome = Returned | FellThrough | OutOfFuel


def to_option(outcome: Outcome) -> tuple[Number, ...] | None:
    if isinstance(outcome, Returned):
        return outcome.values
    return None


def make_ops(exact: bool) -> dict[str, Callable]:
    e = InterpreterError

    def div(a: Number, b: Number) -> Number:
        if b == 0:
            raise e("division by zero (outside the modelled subset)")
        return a / b

    def abs_(a: Number) -> Number:
        return -a if a < 0 else a

    return {
        "literal": Fraction if exact else float,
        "add": lambda a, b: a + b,
        "sub": lambda a, b: a - b,
        "mul": lambda a, b: a * b,
        "div": div,
        "neg": lambda a: -a,
        "abs": abs_,
        "lt": lambda a, b: a < b,
        "le": lambda a, b: a <= b,
        "gt": lambda a, b: a > b,
        "ge": lambda a, b: a >= b,
        "eq": lambda a, b: a == b,
        "ne": lambda a, b: a != b,
    }


def eval_expr(e: Expr, env: Mapping[int, Number], ops: Mapping[str, Callable]) -> Number:
    if isinstance(e, Slot):
        if e.index not in env:
            raise InterpreterError(f"slot {e.index} read before assignment (invalid IR)")
        return env[e.index]
    if isinstance(e, Lit):
        return ops["literal"](e.value)
    if isinstance(e, Bin):
        return ops[e.op](eval_expr(e.lhs, env, ops), eval_expr(e.rhs, env, ops))
    if isinstance(e, Un):
        return ops[e.op](eval_expr(e.arg, env, ops))
    raise TypeError(type(e))


def eval_cond(c: Cond, env: Mapping[int, Number], ops: Mapping[str, Callable]) -> bool:
    if isinstance(c, Cmp):
        return bool(ops[c.op](eval_expr(c.lhs, env, ops), eval_expr(c.rhs, env, ops)))
    if isinstance(c, And):
        return eval_cond(c.lhs, env, ops) and eval_cond(c.rhs, env, ops)
    if isinstance(c, Or):
        return eval_cond(c.lhs, env, ops) or eval_cond(c.rhs, env, ops)
    if isinstance(c, Not):
        return not eval_cond(c.arg, env, ops)
    if isinstance(c, Where):
        return c.value
    raise TypeError(type(c))


class Interpreter:
    def __init__(self, exact: bool = True, fuel: int = DEFAULT_FUEL):
        if fuel < 0:
            raise ValueError("fuel must be non-negative")
        self.exact = exact
        self.fuel = fuel
        self.ops = make_ops(exact)

    def convert(self, value: Number) -> Number:
        return Fraction(value) if self.exact else float(value)

    def run(self, fn: Fn, args: Sequence[Number]) -> Outcome:
        if len(args) != fn.arity:
            raise InterpreterError(f"{fn.name} expects {fn.arity} arguments, got {len(args)}")
        env: dict[int, Number] = {i: self.convert(a) for i, a in enumerate(args)}
        return self.exec(fn.body, env, self.fuel)

    def exec(self, s: Stmt, env: Mapping[int, Number], fuel: int) -> Outcome:
        if fuel == 0:
            return OutOfFuel()
        ops = self.ops
        if isinstance(s, Skip):
            return FellThrough(dict(env))
        if isinstance(s, Assign):
            new_env = dict(env)
            new_env[s.slot] = eval_expr(s.expr, env, ops)
            return FellThrough(new_env)
        if isinstance(s, Seq):
            current: Outcome = FellThrough(dict(env))
            # Each cons cell consumes one level, just like `exec (.seq (s :: rest))`
            # in Lean. Even the empty tail needs a positive budget.
            remaining = fuel
            for item in s.body:
                remaining -= 1
                current = self.exec(item, self._env(current), remaining)
                if not isinstance(current, FellThrough):
                    return current
            return current if remaining > 0 else OutOfFuel()
        if isinstance(s, Ite):
            branch = eval_cond(s.cond, env, ops)
            out = self.exec(s.then_ if branch else s.else_, env, fuel - 1)
            if not isinstance(out, FellThrough):
                return out
            merged = dict(out.env)
            for phi in s.phis:
                merged[phi.slot] = out.env[phi.lhs if branch else phi.rhs]
            return FellThrough(merged)
        if isinstance(s, While):
            return self.loop(s, env, fuel)
        if isinstance(s, Ret):
            return Returned(tuple(eval_expr(e, env, ops) for e in s.exprs))
        raise TypeError(type(s))

    def _env(self, outcome: Outcome) -> dict[int, Number]:
        if isinstance(outcome, FellThrough):
            return outcome.env
        raise InterpreterError("internal error: continuation expected")

    def loop(self, s: While, env: Mapping[int, Number], fuel: int) -> Outcome:
        if fuel == 0:
            return OutOfFuel()
        if not eval_cond(s.cond, env, self.ops):
            return FellThrough(dict(env))
        out = self.exec(s.body, env, fuel - 1)
        if not isinstance(out, FellThrough):
            return out
        next_env = dict(out.env)
        for phi in s.phis:
            next_env[phi.slot] = out.env[phi.lhs]
        return self.loop(s, next_env, fuel - 1)


def run_exact(fn: Fn, args: Sequence[Number], fuel: int = DEFAULT_FUEL) -> Outcome:
    return Interpreter(exact=True, fuel=fuel).run(fn, args)


def run_float(fn: Fn, args: Sequence[Number], fuel: int = DEFAULT_FUEL) -> Outcome:
    return Interpreter(exact=False, fuel=fuel).run(fn, args)


def rat_string(value: Fraction) -> str:
    """Wire format shared with the Lean runner: exact ``num/den``."""
    value = Fraction(value)
    return f"{value.numerator}/{value.denominator}"


def float_bits(value: float) -> str:
    import struct

    (bits,) = struct.unpack("<Q", struct.pack("<d", value))
    return "0x" + format(bits, "x")
