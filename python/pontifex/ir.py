"""Intermediate representation shared with the Lean semantics.

The dataclasses in this module are a one-to-one mirror of ``Pontifex/Core/IR.lean``:

===============  ==========================================================
Lean             Python
===============  ==========================================================
``Expr``         :class:`Slot`, :class:`Lit`, :class:`Bin`, :class:`Un`
``Cond``         :class:`Cmp`, :class:`And`, :class:`Or`, :class:`Not`, :class:`Where`
``Phi``          :class:`Phi`
``Stmt``         :class:`Skip`, :class:`Assign`, :class:`Seq`, :class:`Ite`,
                 :class:`While`, :class:`Ret`
``Fn``           :class:`Fn`
===============  ==========================================================

Integer literals carry an exact rational. Float literals carry both their
exact binary rational value and original binary64 bits, so exact and Float
readings remain explicit without losing subnormals or signed zero. Power is a
separate operation rather than a multiplication expansion.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any, Iterable, Sequence

from .version import IR_VERSION

Json = dict[str, Any]


# ---------------------------------------------------------------------------
# Operators
# ---------------------------------------------------------------------------

BIN_OPS = ("add", "sub", "mul", "div")
CMP_OPS = ("lt", "le", "gt", "ge", "eq", "ne")
UN_OPS = ("neg", "abs")


# ---------------------------------------------------------------------------
# Scalar expressions
# ---------------------------------------------------------------------------


class Expr:
    """Base class for scalar expressions."""

    def to_json(self) -> Json:  # pragma: no cover - abstract
        raise NotImplementedError


@dataclass(frozen=True)
class Slot(Expr):
    index: int

    def __str__(self) -> str:
        return f"slot({self.index})"

    def to_json(self) -> Json:
        return {"k": "slot", "i": self.index}


@dataclass(frozen=True)
class Lit(Expr):
    value: Fraction
    bits: int | None = None

    def __str__(self) -> str:
        return str(self.value)

    def to_json(self) -> Json:
        payload = {"k": "lit", "num": self.value.numerator, "den": self.value.denominator}
        if self.bits is not None:
            payload.update(k="floatLit", bits=str(self.bits))
        return payload


@dataclass(frozen=True)
class Pow(Expr):
    base: Expr
    exponent: int

    def to_json(self) -> Json:
        return {"k": "pow", "e": self.base.to_json(), "n": self.exponent}


@dataclass(frozen=True)
class Bin(Expr):
    op: str
    lhs: Expr
    rhs: Expr

    def __str__(self) -> str:
        return f"({self.lhs} {self.op} {self.rhs})"

    def to_json(self) -> Json:
        return {"k": "bin", "op": self.op, "l": self.lhs.to_json(), "r": self.rhs.to_json()}


@dataclass(frozen=True)
class Un(Expr):
    op: str
    arg: Expr

    def __str__(self) -> str:
        return f"{self.op}({self.arg})"

    def to_json(self) -> Json:
        return {"k": "un", "op": self.op, "e": self.arg.to_json()}


# ---------------------------------------------------------------------------
# Conditions
# ---------------------------------------------------------------------------


class Cond:
    def to_json(self) -> Json:  # pragma: no cover - abstract
        raise NotImplementedError


@dataclass(frozen=True)
class Cmp(Cond):
    op: str
    lhs: Expr
    rhs: Expr

    def __str__(self) -> str:
        return f"({self.lhs} {self.op} {self.rhs})"

    def to_json(self) -> Json:
        return {"k": "cmp", "op": self.op, "l": self.lhs.to_json(), "r": self.rhs.to_json()}


@dataclass(frozen=True)
class And(Cond):
    lhs: Cond
    rhs: Cond

    def to_json(self) -> Json:
        return {"k": "and", "l": self.lhs.to_json(), "r": self.rhs.to_json()}


@dataclass(frozen=True)
class Or(Cond):
    lhs: Cond
    rhs: Cond

    def to_json(self) -> Json:
        return {"k": "or", "l": self.lhs.to_json(), "r": self.rhs.to_json()}


@dataclass(frozen=True)
class Not(Cond):
    arg: Cond

    def to_json(self) -> Json:
        return {"k": "not", "e": self.arg.to_json()}


@dataclass(frozen=True)
class Where(Cond):
    """A boolean constant (``True``/``False`` in source)."""

    value: bool

    def to_json(self) -> Json:
        return {"k": "const", "b": self.value}


# ---------------------------------------------------------------------------
# Statements
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Phi:
    """SSA merge: ``slot := if cond then lhs else rhs`` (if), or
    ``slot := lhs`` after a loop iteration with ``rhs`` the entry value."""

    slot: int
    lhs: int
    rhs: int

    def to_json(self) -> Json:
        return {"k": "phi", "slot": self.slot, "lhs": self.lhs, "rhs": self.rhs}


class Stmt:
    def to_json(self) -> Json:  # pragma: no cover - abstract
        raise NotImplementedError


@dataclass(frozen=True)
class Skip(Stmt):
    def to_json(self) -> Json:
        return {"k": "skip"}


@dataclass(frozen=True)
class Assign(Stmt):
    slot: int
    expr: Expr

    def to_json(self) -> Json:
        return {"k": "assign", "slot": self.slot, "e": self.expr.to_json()}


@dataclass(frozen=True)
class Seq(Stmt):
    body: tuple[Stmt, ...] = ()

    def to_json(self) -> Json:
        return {"k": "seq", "ss": [s.to_json() for s in self.body]}


@dataclass(frozen=True)
class Ite(Stmt):
    cond: Cond
    then_: Stmt
    else_: Stmt
    phis: tuple[Phi, ...] = ()

    def to_json(self) -> Json:
        return {
            "k": "ite",
            "c": self.cond.to_json(),
            "t": self.then_.to_json(),
            "e": self.else_.to_json(),
            "phis": [p.to_json() for p in self.phis],
        }


@dataclass(frozen=True)
class While(Stmt):
    cond: Cond
    phis: tuple[Phi, ...]
    body: Stmt

    def to_json(self) -> Json:
        return {
            "k": "while",
            "c": self.cond.to_json(),
            "phis": [p.to_json() for p in self.phis],
            "body": self.body.to_json(),
        }


@dataclass(frozen=True)
class Ret(Stmt):
    exprs: tuple[Expr, ...]

    def to_json(self) -> Json:
        return {"k": "ret", "es": [e.to_json() for e in self.exprs]}


@dataclass(frozen=True)
class Fn:
    name: str
    params: tuple[str, ...]
    slot_names: tuple[str, ...]
    body: Stmt
    #: Names of the variables returned, in order (documentation only; the IR
    #: itself only knows slots, so this field does not participate in equality).
    result_names: tuple[str, ...] = field(default=(), compare=False)

    def to_json(self) -> Json:
        return {
            "irVersion": IR_VERSION,
            "name": self.name,
            "params": list(self.params),
            "slotNames": list(self.slot_names),
            "body": self.body.to_json(),
        }

    def to_json_text(self) -> str:
        import json

        return json.dumps(self.to_json(), indent=2) + "\n"

    @property
    def arity(self) -> int:
        return len(self.params)


# ---------------------------------------------------------------------------
# JSON decoding (used by tests; the authoritative decoder lives in Lean)
# ---------------------------------------------------------------------------


def _expr_of_json(j: Json) -> Expr:
    k = j["k"]
    if k == "slot":
        return Slot(int(j["i"]))
    if k in {"lit", "floatLit"}:
        bits = int(j["bits"]) if k == "floatLit" else None
        return Lit(Fraction(int(j["num"]), int(j["den"])), bits)
    if k == "pow":
        return Pow(_expr_of_json(j["e"]), int(j["n"]))
    if k == "bin":
        return Bin(j["op"], _expr_of_json(j["l"]), _expr_of_json(j["r"]))
    if k == "un":
        return Un(j["op"], _expr_of_json(j["e"]))
    raise ValueError(f"unknown expression kind {k!r}")


def _cond_of_json(j: Json) -> Cond:
    k = j["k"]
    if k == "cmp":
        return Cmp(j["op"], _expr_of_json(j["l"]), _expr_of_json(j["r"]))
    if k == "and":
        return And(_cond_of_json(j["l"]), _cond_of_json(j["r"]))
    if k == "or":
        return Or(_cond_of_json(j["l"]), _cond_of_json(j["r"]))
    if k == "not":
        return Not(_cond_of_json(j["e"]))
    if k == "const":
        return Where(bool(j["b"]))
    raise ValueError(f"unknown condition kind {k!r}")


def _stmt_of_json(j: Json) -> Stmt:
    k = j["k"]
    if k == "skip":
        return Skip()
    if k == "assign":
        return Assign(int(j["slot"]), _expr_of_json(j["e"]))
    if k == "seq":
        return Seq(tuple(_stmt_of_json(s) for s in j["ss"]))
    if k == "ite":
        return Ite(
            _cond_of_json(j["c"]),
            _stmt_of_json(j["t"]),
            _stmt_of_json(j["e"]),
            tuple(Phi(int(p["slot"]), int(p["lhs"]), int(p["rhs"])) for p in j["phis"]),
        )
    if k == "while":
        return While(
            _cond_of_json(j["c"]),
            tuple(Phi(int(p["slot"]), int(p["lhs"]), int(p["rhs"])) for p in j["phis"]),
            _stmt_of_json(j["body"]),
        )
    if k == "ret":
        return Ret(tuple(_expr_of_json(e) for e in j["es"]))
    raise ValueError(f"unknown statement kind {k!r}")


def fn_of_json(j: Json) -> Fn:
    version = j.get("irVersion")
    if version != IR_VERSION:
        raise ValueError(
            f"IR version mismatch: artifact has {version!r}, this package expects {IR_VERSION}"
        )
    return Fn(
        name=j["name"],
        params=tuple(j["params"]),
        slot_names=tuple(j["slotNames"]),
        body=_stmt_of_json(j["body"]),
    )


# ---------------------------------------------------------------------------
# Small utilities
# ---------------------------------------------------------------------------


def slots_read(e: Expr | Cond) -> set[int]:
    """Slots referenced by an expression or condition."""
    if isinstance(e, Slot):
        return {e.index}
    if isinstance(e, Lit):
        return set()
    if isinstance(e, Bin):
        return slots_read(e.lhs) | slots_read(e.rhs)
    if isinstance(e, Un):
        return slots_read(e.arg)
    if isinstance(e, Pow):
        return slots_read(e.base)
    if isinstance(e, Cmp):
        return slots_read(e.lhs) | slots_read(e.rhs)
    if isinstance(e, (And, Or)):
        return slots_read(e.lhs) | slots_read(e.rhs)
    if isinstance(e, Not):
        return slots_read(e.arg)
    if isinstance(e, Where):
        return set()
    raise TypeError(type(e))


def stmts(stmt: Stmt) -> Iterable[Stmt]:
    """Flatten a statement tree (pre-order)."""
    yield stmt
    if isinstance(stmt, Seq):
        for s in stmt.body:
            yield from stmts(s)
    elif isinstance(stmt, Ite):
        yield from stmts(stmt.then_)
        yield from stmts(stmt.else_)
    elif isinstance(stmt, While):
        yield from stmts(stmt.body)
