"""White-box expansion of bounded, scalar helper bodies (no new IR nodes).

The independent Lean counterpart lives in Core/Inline.lean. Only a sequence
of assignments/skips followed by one scalar return is accepted. Argument
expressions are captured before entering the relocated, private callee frame.
"""

from __future__ import annotations

from dataclasses import replace
from typing import Callable, Sequence

from .ir import Assign, Bin, Expr, Fn, Lit, Pow, Ret, Seq, Skip, Slot, Stmt, Un


def shift_expr(expr: Expr, offset: int) -> Expr:
    if isinstance(expr, Slot):
        return Slot(expr.index + offset)
    if isinstance(expr, Lit):
        return expr
    if isinstance(expr, Bin):
        return replace(expr, lhs=shift_expr(expr.lhs, offset), rhs=shift_expr(expr.rhs, offset))
    if isinstance(expr, (Un, Pow)):
        field = "arg" if isinstance(expr, Un) else "base"
        return replace(expr, **{field: shift_expr(getattr(expr, field), offset)})
    raise ValueError("inlined helpers must use only scalar arithmetic")


def flatten(stmt: Stmt) -> list[Stmt]:
    if isinstance(stmt, Seq):
        return [item for child in stmt.body for item in flatten(child)]
    return [stmt]


def inline_body(
    callee: Fn,
    args: Sequence[Expr],
    fresh: Callable[[str], int],
    target: str | None,
) -> tuple[Stmt, int | None]:
    """Allocate an isolated frame and optionally bind the scalar result.

    ``None`` is a tail call: retain the callee's return, so it exits the caller.
    Slot allocation stays dense and in exactly the callee's original order.
    """
    if len(args) != callee.arity:
        raise ValueError("call arity mismatch")
    flat = flatten(callee.body)
    # Slot names remain cosmetic: frame bounds come from the actual IR.
    size = max([callee.arity, *(s.slot + 1 for s in flat if isinstance(s, Assign))])
    names = [
        callee.slot_names[i] if i < len(callee.slot_names) else f"slot{i}" for i in range(size)
    ]
    frame = [fresh(f"{callee.name}#{name}") for name in names]
    offset = frame[0] if frame else None
    # A zero-parameter constant helper can have no slots. Its expressions then
    # have no slot reads, so any offset is observationally equivalent.
    if offset is None:
        offset = 0
    body: list[Stmt] = [Assign(slot, arg) for slot, arg in zip(frame, args)]
    if not flat or not isinstance(flat[-1], Ret) or len(flat[-1].exprs) != 1:
        raise ValueError("inlined helpers must end with one scalar return")
    for stmt in flat[:-1]:
        if isinstance(stmt, Assign):
            body.append(Assign(stmt.slot + offset, shift_expr(stmt.expr, offset)))
        elif isinstance(stmt, Skip):
            body.append(stmt)
        else:
            raise ValueError("inlined helpers must have straight-line bodies")
    value = shift_expr(flat[-1].exprs[0], offset)
    result = fresh(target) if target is not None else None
    body.append(Assign(result, value) if result is not None else Ret((value,)))
    return Seq(tuple(body)), result
