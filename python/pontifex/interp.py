"""Reference semantics, mirroring Lean's explicit outcomes and structured fuel.

Exact arithmetic is Fraction; binary64 arithmetic uses Python float. Expression
faults propagate left-to-right, and boolean conditions short-circuit faults.
Only outOfFuel is an incomplete observation; failed/stuck are stable results.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Callable, Mapping, Sequence
import math
import struct

from .ir import (
    And,
    ArrayLit,
    Assign,
    Bin,
    Cmp,
    Cond,
    Expr,
    Fn,
    Index,
    Ite,
    Len,
    Lit,
    Not,
    Or,
    Pow,
    Ret,
    Seq,
    Select,
    Set,
    Skip,
    Slot,
    Stmt,
    Un,
    Where,
    While,
)
from .errors import InterpreterError

Number = Any
DEFAULT_FUEL = 512


@dataclass(frozen=True)
class Returned:
    values: tuple[Number, ...]


@dataclass(frozen=True)
class FellThrough:
    #: Slot values: scalars (Fraction / float) or arrays (lists of scalars).
    env: dict[int, Number]


@dataclass(frozen=True)
class Failed:
    error: str


@dataclass(frozen=True)
class Stuck:
    pass


@dataclass(frozen=True)
class OutOfFuel:
    pass


Outcome = Returned | FellThrough | Failed | Stuck | OutOfFuel


def to_option(outcome: Outcome) -> tuple[Number, ...] | None:
    return outcome.values if isinstance(outcome, Returned) else None


class _StuckSignal(Exception):
    pass


class _IndexSignal(Exception):
    pass


def make_ops(exact: bool) -> dict[str, Callable]:
    def div(a, b):
        if b == 0:
            raise ZeroDivisionError
        return a / b

    return {
        "literal": Fraction if exact else float,
        "add": lambda a, b: a + b,
        "sub": lambda a, b: a - b,
        "mul": lambda a, b: a * b,
        "div": div,
        # Two-argument Python scan: keep the first object on ties/unordered
        # comparisons. Do not use a symmetric IEEE fmin/fmax implementation.
        "min": lambda a, b: b if b < a else a,
        "max": lambda a, b: b if b > a else a,
        "pow": lambda a, n: a**n,
        "neg": lambda a: -a,
        "abs": abs,
        "lt": lambda a, b: a < b,
        "le": lambda a, b: a <= b,
        "gt": lambda a, b: a > b,
        "ge": lambda a, b: a >= b,
        "eq": lambda a, b: a == b,
        "ne": lambda a, b: a != b,
    }


def _read(env, slot):
    if slot not in env:
        raise _StuckSignal
    return env[slot]


def _index_of(value) -> int | None:
    """Non-negative integral scalars only; anything else is a bad index."""
    if isinstance(value, Fraction):
        if value.denominator == 1 and value >= 0:
            return int(value.numerator)
        return None
    if isinstance(value, float):
        if math.isfinite(value) and value >= 0 and value.is_integer() and value <= 2**53:
            return int(value)
        return None
    return None


def eval_value(e: Expr, env: Mapping[int, Number], ops: Mapping[str, Callable]) -> Number:
    """Evaluate to a scalar or a list of scalars (a `Val`)."""
    if isinstance(e, Slot):
        return _read(env, e.index)
    if isinstance(e, Lit):
        if e.bits is not None and ops["literal"] is float:
            return struct.unpack(">d", struct.pack(">Q", e.bits))[0]
        return ops["literal"](e.value)
    if isinstance(e, Bin):
        return ops[e.op](eval_scalar(e.lhs, env, ops), eval_scalar(e.rhs, env, ops))
    if isinstance(e, Select):
        branch = e.then_ if eval_cond(e.cond, env, ops) else e.else_
        return eval_scalar(branch, env, ops)
    if isinstance(e, Un):
        return ops[e.op](eval_scalar(e.arg, env, ops))
    if isinstance(e, Pow):
        return ops["pow"](eval_scalar(e.base, env, ops), e.exponent)
    if isinstance(e, Index):
        array = eval_value(e.array, env, ops)
        index = eval_scalar(e.index, env, ops)
        if not isinstance(array, list):
            raise _StuckSignal
        i = _index_of(index)
        if i is None or i >= len(array):
            raise _IndexSignal
        return array[i]
    if isinstance(e, Len):
        array = eval_value(e.array, env, ops)
        if not isinstance(array, list):
            raise _StuckSignal
        return ops["literal"](len(array))
    if isinstance(e, ArrayLit):
        return [eval_scalar(item, env, ops) for item in e.items]
    if isinstance(e, Set):
        # Python evaluates the right-hand side first, then the target array and
        # the index expression.
        value = eval_scalar(e.value, env, ops)
        array = eval_value(e.array, env, ops)
        index = eval_scalar(e.index, env, ops)
        if not isinstance(array, list):
            raise _StuckSignal
        i = _index_of(index)
        if i is None or i >= len(array):
            raise _IndexSignal
        updated = list(array)
        updated[i] = value
        return updated
    raise TypeError(type(e))


def eval_scalar(e: Expr, env: Mapping[int, Number], ops: Mapping[str, Callable]) -> Number:
    value = eval_value(e, env, ops)
    if isinstance(value, list):
        raise _StuckSignal
    return value


def eval_cond(c: Cond, env: Mapping[int, Number], ops: Mapping[str, Callable]) -> bool:
    if isinstance(c, Cmp):
        return bool(ops[c.op](eval_scalar(c.lhs, env, ops), eval_scalar(c.rhs, env, ops)))
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

    def run(self, fn: Fn, args: Sequence[Number]) -> Outcome:
        convert = Fraction if self.exact else float
        env = {i: convert(a) for i, a in enumerate(args)}
        return self.exec(fn.body, env, self.fuel)

    def exec(self, s: Stmt, env: Mapping[int, Number], fuel: int) -> Outcome:
        try:
            return self._exec(s, env, fuel)
        except ZeroDivisionError:
            return Failed("divisionByZero")
        except OverflowError:
            return Failed("overflow")
        except _IndexSignal:
            return Failed("indexOutOfBounds")
        except _StuckSignal:
            return Stuck()

    def _exec(self, s: Stmt, env: Mapping[int, Number], fuel: int) -> Outcome:
        if fuel == 0:
            return OutOfFuel()
        if isinstance(s, Skip):
            return FellThrough(dict(env))
        if isinstance(s, Assign):
            updated = dict(env)
            updated[s.slot] = eval_value(s.expr, env, self.ops)
            return FellThrough(updated)
        if isinstance(s, Seq):
            current = FellThrough(dict(env))
            remaining = fuel
            for item in s.body:
                remaining -= 1
                current = self.exec(item, current.env, remaining)
                if not isinstance(current, FellThrough):
                    return current
            return current if remaining > 0 else OutOfFuel()
        if isinstance(s, Ite):
            branch = eval_cond(s.cond, env, self.ops)
            out = self.exec(s.then_ if branch else s.else_, env, fuel - 1)
            if not isinstance(out, FellThrough):
                return out
            merged = dict(out.env)
            for phi in s.phis:
                merged[phi.slot] = _read(out.env, phi.lhs if branch else phi.rhs)
            return FellThrough(merged)
        if isinstance(s, While):
            # Iterative host execution avoids Python recursion-limit artifacts.
            current = dict(env)
            remaining = fuel
            while remaining:
                if not eval_cond(s.cond, current, self.ops):
                    return FellThrough(current)
                out = self.exec(s.body, current, remaining - 1)
                if not isinstance(out, FellThrough):
                    return out
                current = dict(out.env)
                for phi in s.phis:
                    current[phi.slot] = _read(out.env, phi.lhs)
                remaining -= 1
            return OutOfFuel()
        if isinstance(s, Ret):
            return Returned(tuple(eval_scalar(e, env, self.ops) for e in s.exprs))
        raise TypeError(type(s))


def run_exact(fn: Fn, args: Sequence[Number], fuel: int = DEFAULT_FUEL) -> Outcome:
    return Interpreter(exact=True, fuel=fuel).run(fn, args)


def run_float(fn: Fn, args: Sequence[Number], fuel: int = DEFAULT_FUEL) -> Outcome:
    return Interpreter(exact=False, fuel=fuel).run(fn, args)


def rat_string(value: Fraction) -> str:
    value = Fraction(value)
    return f"{value.numerator}/{value.denominator}"


def float_bits(value: float) -> str:
    (bits,) = struct.unpack(">Q", struct.pack(">d", value))
    return "0x" + format(bits, "x")
