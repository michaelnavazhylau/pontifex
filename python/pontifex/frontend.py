"""Python ``ast`` frontend: restricted subset -> SSA IR.

Pipeline
--------
1. Parse with ``ast.parse`` (syntax only -- Python's parser deliberately does
   not establish semantic properties, so nothing here relies on it doing so).
2. Reject everything outside the documented subset, with a located message.
3. Lower to the slot-based IR, performing SSA renaming:

   * every assignment allocates a fresh slot, so a slot is written at most once
     (this is what makes the emission to Lean a pure substitution);
   * assignments under an ``if`` produce explicit ``Phi`` merges;
   * assignments inside a ``while`` become loop-carried header slots, with the
     body's final value as the back edge.

Documented subset (v0)
----------------------
* one function per module (or a selected function), no decorators, no
  ``*args``/``**kwargs``/keyword-only parameters, no defaults;
* scalar parameters (annotations are advisory and are not used for typing);
* statements: simple/annotated/augmented assignment, ``if``/``else``,
  ``while``, ``return`` (single exit, last statement of the function), ``pass``;
* expressions: names, int/float literals, ``+ - * /``, ``**`` with a small
  non-negative integer exponent, unary minus, ``abs(x)``;
* conditions: comparisons (one operator, not chained), ``and``/``or``/``not``,
  boolean literals.

Explicitly rejected: imports, classes, ``for``, ``break``/``continue``,
``try``/``except``, ``with``, ``assert``, ``del``, lambdas, comprehensions,
attribute access, subscripting, lists/dicts/tuples outside ``return``,
``min``/``max``, conditional expressions, chained comparisons, and any call
other than ``abs``.
"""

from __future__ import annotations

import ast
import math
import struct
from dataclasses import dataclass
from fractions import Fraction
from typing import Iterable, Sequence

from .errors import FrontendError, UnsupportedError
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
    Phi,
    Pow,
    Ret,
    Seq,
    Skip,
    Slot,
    Stmt,
    Un,
    Where,
    While,
)

BINOP_NAMES = {
    ast.Add: "add",
    ast.Sub: "sub",
    ast.Mult: "mul",
    ast.Div: "div",
}

AUGOP_NAMES = {
    ast.Add: "add",
    ast.Sub: "sub",
    ast.Mult: "mul",
    ast.Div: "div",
}

CMP_NAMES = {
    ast.Lt: "lt",
    ast.LtE: "le",
    ast.Gt: "gt",
    ast.GtE: "ge",
    ast.Eq: "eq",
    ast.NotEq: "ne",
}

MAX_POW_EXPONENT = 8


@dataclass
class Translated:
    """A translated function plus the source it came from."""

    fn: Fn
    source: str
    filename: str
    function_name: str


# ---------------------------------------------------------------------------
# Static analysis used for SSA merges
# ---------------------------------------------------------------------------


def assigned_names(nodes: Iterable[ast.stmt]) -> set[str]:
    """Names assigned anywhere inside ``nodes`` (including nested control flow).

    Used to decide which slots need a phi at an ``if`` merge or loop header.
    Raises ``FrontendError`` for statements that cannot appear in the subset, so
    an unsupported construct is never silently ignored.
    """
    out: set[str] = set()
    for node in nodes:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if not isinstance(target, ast.Name):
                    raise UnsupportedError(
                        "only simple assignments to a single name are supported", node
                    )
                out.add(target.id)
        elif isinstance(node, ast.AnnAssign):
            if not isinstance(node.target, ast.Name) or node.value is None:
                raise UnsupportedError("only annotated assignments with a value are supported", node)
            out.add(node.target.id)
        elif isinstance(node, ast.AugAssign):
            if not isinstance(node.target, ast.Name):
                raise UnsupportedError("only augmented assignment to a name is supported", node)
            out.add(node.target.id)
        elif isinstance(node, ast.If):
            out |= assigned_names(node.body)
            out |= assigned_names(node.orelse)
        elif isinstance(node, ast.While):
            out |= assigned_names(node.body)
        elif isinstance(node, (ast.Pass, ast.Expr)):
            pass
        elif isinstance(node, ast.Return):
            pass
        else:
            raise UnsupportedError(
                f"statement '{type(node).__name__}' is not supported in this position", node
            )
    return out


# ---------------------------------------------------------------------------
# Lowering
# ---------------------------------------------------------------------------


class _Lowerer:
    def __init__(self, filename: str, fn_name: str, params: Sequence[str]):
        self.filename = filename
        self.fn_name = fn_name
        self.slot_names: list[str] = list(params)
        self.env: dict[str, int] = {name: i for i, name in enumerate(params)}
        self._next_slot = len(params)

    # -- slots -------------------------------------------------------------

    def fresh(self, hint: str) -> int:
        slot = self._next_slot
        self._next_slot += 1
        name = hint
        index = 1
        while name in self.slot_names:
            name = f"{hint}_{index}"
            index += 1
        self.slot_names.append(name)
        return slot

    def lookup(self, node: ast.Name) -> int:
        if node.id not in self.env:
            raise UnsupportedError(
                f"undefined name '{node.id}' (variables must be parameters or assigned before use)",
                node,
            )
        return self.env[node.id]

    def err(self, node: ast.AST, msg: str) -> UnsupportedError:
        return UnsupportedError(msg, node, self.filename)

    # -- expressions -------------------------------------------------------

    def expr(self, node: ast.expr) -> Expr:
        if isinstance(node, ast.Name):
            return Slot(self.lookup(node))
        if isinstance(node, ast.Constant):
            value = node.value
            if isinstance(value, bool):
                raise self.err(node, "boolean value used where a scalar is expected")
            if isinstance(value, int):
                return Lit(Fraction(value))
            if isinstance(value, float):
                if not math.isfinite(value):
                    raise self.err(node, "non-finite float literals are not supported")
                num, den = value.as_integer_ratio()
                bits, = struct.unpack(">Q", struct.pack(">d", value))
                return Lit(Fraction(num, den), bits)
            raise self.err(node, f"literal of type {type(value).__name__} is not supported")
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                return self.pow(node)
            op = BINOP_NAMES.get(type(node.op))
            if op is None:
                raise self.err(
                    node, f"binary operator '{type(node.op).__name__}' is not supported"
                )
            return Bin(op, self.expr(node.left), self.expr(node.right))
        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.USub):
                return Un("neg", self.expr(node.operand))
            if isinstance(node.op, ast.UAdd):
                return self.expr(node.operand)
            raise self.err(node, f"unary operator '{type(node.op).__name__}' is not supported here")
        if isinstance(node, ast.Call):
            if (
                isinstance(node.func, ast.Name)
                and node.func.id == "abs"
                and len(node.args) == 1
                and not node.keywords
            ):
                return Un("abs", self.expr(node.args[0]))
            raise self.err(
                node,
                "only the call abs(x) is supported; imports, math functions, min/max and "
                "user calls are rejected by the v0 frontend",
            )
        if isinstance(node, ast.Attribute):
            raise self.err(
                node,
                f"attribute access '.{node.attr}' is not supported "
                "(no modules, objects or methods in the verified subset)",
            )
        if isinstance(node, ast.Subscript):
            raise self.err(
                node, "subscripting is not supported (no arrays/sequences in the verified subset)"
            )
        if isinstance(node, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
            raise self.err(
                node,
                f"{type(node).__name__.lower()} literals are not supported in expressions "
                "(return a flat tuple of scalars instead)",
            )
        if isinstance(node, ast.IfExp):
            raise self.err(node, "conditional expressions are not supported")
        if isinstance(node, ast.Compare):
            raise self.err(node, "comparison produces a boolean and cannot be used as a scalar")
        if isinstance(node, ast.BoolOp):
            raise self.err(node, "boolean expression used where a scalar is expected")
        raise self.err(node, f"expression '{type(node).__name__}' is not supported")

    def pow(self, node: ast.BinOp) -> Expr:
        exponent = node.right
        if not (isinstance(exponent, ast.Constant) and isinstance(exponent.value, int)):
            raise self.err(
                node,
                "only '**' with an integer literal exponent is supported "
                "(represented by a backend-specific power operation)",
            )
        n = exponent.value
        if isinstance(exponent.value, bool) or n < 0 or n > MAX_POW_EXPONENT:
            raise self.err(
                node,
                f"'**' exponent must be an integer in [0, {MAX_POW_EXPONENT}], got {n} "
                "(non-integer powers would require a transcendental function)",
            )
        base = self.expr(node.left)
        return Pow(base, n)

    # -- conditions --------------------------------------------------------

    def cond(self, node: ast.expr) -> Cond:
        if isinstance(node, ast.Compare):
            if len(node.ops) != 1 or len(node.comparators) != 1:
                raise self.err(node, "chained comparisons are not supported")
            op = CMP_NAMES.get(type(node.ops[0]))
            if op is None:
                raise self.err(
                    node, f"comparison '{type(node.ops[0]).__name__}' is not supported"
                )
            return Cmp(op, self.expr(node.left), self.expr(node.comparators[0]))
        if isinstance(node, ast.BoolOp):
            parts = [self.cond(v) for v in node.values]
            acc = parts[0]
            for part in parts[1:]:
                acc = And(acc, part) if isinstance(node.op, ast.And) else Or(acc, part)
            return acc
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return Not(self.cond(node.operand))
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return Where(node.value)
        raise self.err(
            node, f"'{type(node).__name__}' is not a supported condition "
            "(use comparisons combined with and/or/not)"
        )

    # -- statements --------------------------------------------------------

    def block(self, nodes: Sequence[ast.stmt], *, allow_return: bool) -> Stmt:
        out: list[Stmt] = []
        for index, node in enumerate(nodes):
            if isinstance(node, ast.Return):
                if not allow_return:
                    raise self.err(
                        node,
                        "return is only supported as the final statement of the function "
                        "(single-exit restriction of the v0 subset)",
                    )
                if index != len(nodes) - 1:
                    raise self.err(
                        node, "return must be the last statement of the function (single exit)"
                    )
                out.append(Ret(self.returns(node)))
                continue
            out.append(self.stmt(node))
        return Seq(tuple(out))

    def returns(self, node: ast.Return) -> tuple[Expr, ...]:
        if node.value is None:
            raise self.err(node, "return must produce at least one scalar (state vector)")
        if isinstance(node.value, ast.Tuple):
            if not node.value.elts:
                raise self.err(node, "empty return tuple")
            return tuple(self.expr(e) for e in node.value.elts)
        return (self.expr(node.value),)

    def stmt(self, node: ast.stmt) -> Stmt:
        if isinstance(node, ast.Pass):
            return Skip()
        if isinstance(node, ast.Expr):
            if isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                return Skip()  # docstring
            raise self.err(
                node,
                "expression statements (including calls) are not supported; "
                "only assignments, control flow and return are allowed",
            )
        if isinstance(node, ast.Assign):
            if len(node.targets) != 1:
                raise self.err(node, "chained assignment (a = b = c) is not supported")
            target = node.targets[0]
            if not isinstance(target, ast.Name):
                raise self.err(
                    node,
                    "only assignment to a plain name is supported "
                    "(no attributes, indexing, tuple unpacking or slicing)",
                )
            value = self.expr(node.value)
            slot = self.fresh(target.id)
            self.env[target.id] = slot
            return Assign(slot, value)
        if isinstance(node, ast.AnnAssign):
            if not isinstance(node.target, ast.Name) or node.value is None:
                raise self.err(node, "only 'name: type = value' is supported")
            value = self.expr(node.value)
            slot = self.fresh(node.target.id)
            self.env[node.target.id] = slot
            return Assign(slot, value)
        if isinstance(node, ast.AugAssign):
            if not isinstance(node.target, ast.Name):
                raise self.err(node, "only augmented assignment to a name is supported")
            op = AUGOP_NAMES.get(type(node.op))
            if op is None:
                raise self.err(
                    node, f"augmented operator '{type(node.op).__name__}' is not supported"
                )
            current = Slot(self.lookup(node.target))
            value = Bin(op, current, self.expr(node.value))
            slot = self.fresh(node.target.id)
            self.env[node.target.id] = slot
            return Assign(slot, value)
        if isinstance(node, ast.If):
            return self.if_(node)
        if isinstance(node, ast.While):
            return self.while_(node)
        raise self.err(node, f"statement '{type(node).__name__}' is not supported")

    def if_(self, node: ast.If) -> Stmt:
        pre = dict(self.env)
        cond = self.cond(node.test)

        self.env = dict(pre)
        then_stmt = self.block(node.body, allow_return=False)
        then_env = dict(self.env)

        self.env = dict(pre)
        else_stmt = self.block(node.orelse, allow_return=False) if node.orelse else Skip()
        else_env = dict(self.env)

        merged = sorted(assigned_names(node.body) | assigned_names(node.orelse))
        phis: list[Phi] = []
        self.env = dict(pre)
        for name in merged:
            if name not in then_env or name not in else_env:
                # Unreachable: assigned_names is computed from the same nodes.
                raise self.err(node, f"internal error: no value for '{name}' after if")
            slot = self.fresh(name)
            phis.append(Phi(slot, then_env[name], else_env[name]))
            self.env[name] = slot
        return Ite(cond, then_stmt, else_stmt, tuple(phis))

    def while_(self, node: ast.While) -> Stmt:
        if node.orelse:
            raise self.err(node, "while/else is not supported")
        pre = dict(self.env)
        loop_vars = sorted(assigned_names(node.body))
        for name in loop_vars:
            if name not in pre:
                raise self.err(
                    node,
                    f"variable '{name}' is assigned inside the loop but has no value before it; "
                    "initialise it before the loop so the loop-carried slot is well-defined",
                )
        headers = {name: self.fresh(f"{name}#loop") for name in loop_vars}
        self.env = dict(pre)
        self.env.update(headers)
        cond = self.cond(node.test)
        body = self.block(node.body, allow_return=False)
        body_env = dict(self.env)
        phis = tuple(Phi(headers[name], body_env[name], pre[name]) for name in loop_vars)
        # Initialise the header slots explicitly, in source order of the loop
        # variables; `While` itself only performs the back-edge updates.
        init = tuple(Assign(headers[name], Slot(pre[name])) for name in sorted(loop_vars))
        self.env = dict(pre)
        self.env.update(headers)
        return Seq(init + (While(cond, phis, body),))


# ---------------------------------------------------------------------------
# Module level
# ---------------------------------------------------------------------------


def _check_signature(fn: ast.FunctionDef, filename: str) -> list[str]:
    args = fn.args
    if fn.decorator_list:
        raise FrontendError("decorators are not supported", fn, filename)
    if args.vararg is not None or args.kwarg is not None:
        raise FrontendError("*args/**kwargs are not supported", fn, filename)
    if args.kwonlyargs:
        raise FrontendError("keyword-only parameters are not supported", fn, filename)
    if args.posonlyargs:
        names = [a.arg for a in args.posonlyargs]
        raise FrontendError(
            "positional-only parameters ('/' in the signature) are not supported: "
            + ", ".join(names),
            fn,
            filename,
        )
    if args.defaults or args.kw_defaults:
        raise FrontendError("default parameter values are not supported", fn, filename)
    if fn.returns is None:
        pass  # annotations are advisory; arity comes from the return statement
    params = [a.arg for a in args.args]
    if len(set(params)) != len(params):
        raise FrontendError("duplicate parameter names", fn, filename)
    return params


def translate(source: str, *, filename: str = "<string>", function: str | None = None) -> Translated:
    """Translate one function from Python source into the SSA IR."""
    try:
        module = ast.parse(source, filename=filename)
    except SyntaxError as exc:  # pragma: no cover - ast provides good messages
        raise FrontendError(f"syntax error: {exc.msg}", None, filename) from exc

    functions: list[ast.FunctionDef] = []
    for node in module.body:
        if isinstance(node, ast.Expr) and isinstance(node.value, ast.Constant) and isinstance(
            node.value.value, str
        ):
            continue  # module docstring
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            raise UnsupportedError(
                "imports are not supported: translated programs must be self-contained", node, filename
            )
        if isinstance(node, ast.FunctionDef):
            functions.append(node)
            continue
        if isinstance(node, ast.AsyncFunctionDef):
            raise UnsupportedError("async functions are not supported", node, filename)
        raise UnsupportedError(
            "only function definitions may appear at module level", node, filename
        )

    if function is None:
        if len(functions) != 1:
            names = ", ".join(f.name for f in functions) or "<none>"
            raise FrontendError(
                f"expected exactly one function definition, found {len(functions)} ({names}); "
                "select one explicitly",
                functions[0] if functions else None,
                filename,
            )
        target = functions[0]
    else:
        matches = [f for f in functions if f.name == function]
        if not matches:
            raise FrontendError(f"no function named '{function}' in {filename}", None, filename)
        target = matches[0]

    params = _check_signature(target, filename)
    lowerer = _Lowerer(filename, target.name, params)
    body = lowerer.block(target.body, allow_return=True)

    ret_exprs = _return_exprs(body)
    result_names = tuple(
        lowerer.slot_names[e.index]
        if isinstance(e, Slot) and e.index < len(lowerer.slot_names)
        else str(e)
        for e in ret_exprs
    )
    fn = Fn(
        name=target.name,
        params=tuple(params),
        slot_names=tuple(lowerer.slot_names),
        body=body,
        result_names=result_names,
    )
    return Translated(fn=fn, source=source, filename=filename, function_name=target.name)


def _return_exprs(body: Stmt) -> tuple[Expr, ...]:
    if isinstance(body, Seq):
        for stmt in reversed(body.body):
            if isinstance(stmt, Ret):
                return stmt.exprs
    raise FrontendError("function has no return statement")
