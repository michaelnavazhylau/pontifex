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

A ``return`` may appear early, anywhere a statement is allowed.  The IR
sequence already short-circuits on the ``returned`` outcome, so a returning
branch never reaches its enclosing ``if`` merge or loop back edge.  Merge slots
are computed from the environments of the branches that can still fall
through; a branch that always returns contributes a dead (but defined)
placeholder to the other side.  Two restrictions keep this sound and explicit:
code after a statement that always returns is rejected as unreachable, and a
function must return on every path (implicit ``None`` fall-through is not
modelled).

Documented subset (v0)
----------------------
* one function per module (or a selected function), no decorators, no
  ``*args``/``**kwargs``/keyword-only parameters, no defaults;
* scalar parameters (annotations are advisory and are not used for typing);
* statements: simple/annotated/augmented assignment, ``if``/``else``,
  ``while``, ``return`` (early exits allowed; every path must return), ``pass``;
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
    Phi,
    Pow,
    Ret,
    Seq,
    Set,
    Skip,
    Slot,
    Stmt,
    Un,
    Where,
    While,
    stmts,
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

#: Static kinds of source variables.  Arrays are one-dimensional, immutable
#: values; ``xs[i] = v`` rebinds ``xs`` to a new array value (SSA), so there is
#: no aliasing.  Array parameters and array returns are not in the subset.
SCALAR = "scalar"
ARRAY = "array"


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


def stmt_returns(node: ast.stmt) -> bool:
    """True when executing ``node`` never falls through to the next statement."""
    if isinstance(node, ast.Return):
        return True
    if isinstance(node, ast.If):
        return block_returns(node.body) and block_returns(node.orelse)
    return False


def block_returns(nodes: Sequence[ast.stmt]) -> bool:
    """True when the block cannot reach the end (its last statement returns)."""
    return bool(nodes) and stmt_returns(nodes[-1])


def assigned_names(nodes: Iterable[ast.stmt]) -> set[str]:
    """Names assigned anywhere inside ``nodes`` (including nested control flow).

    Used to choose loop-carried header slots (an ``if`` merge is computed from
    the lowered branch environments instead, so a branch that always returns
    contributes nothing).
    Raises ``FrontendError`` for statements that cannot appear in the subset, so
    an unsupported construct is never silently ignored.
    """
    out: set[str] = set()
    for node in nodes:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Subscript) and isinstance(target.value, ast.Name):
                    out.add(target.value.id)
                elif not isinstance(target, ast.Name):
                    raise UnsupportedError(
                        "only simple assignments to a single name are supported", node
                    )
                else:
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
        #: Arity fixed by the first return; every later return must agree.
        self.result_arity: int | None = None
        #: Static kind (scalar/array) of each bound name, threaded like `env`.
        self.kinds: dict[str, str] = {name: SCALAR for name in params}

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
            if self.kinds.get(node.id) == ARRAY:
                raise self.err(
                    node,
                    f"'{node.id}' is an array and cannot be used where a scalar is expected "
                    "(index it, take its length, or return a scalar)",
                )
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
            if (
                isinstance(node.func, ast.Name)
                and node.func.id == "len"
                and len(node.args) == 1
                and not node.keywords
            ):
                return Len(self.array_expr(node.args[0]))
            raise self.err(
                node,
                "only the calls abs(x) and len(xs) are supported; imports, math functions, "
                "min/max and user calls are rejected by the v0 frontend",
            )
        if isinstance(node, ast.Attribute):
            raise self.err(
                node,
                f"attribute access '.{node.attr}' is not supported "
                "(no modules, objects or methods in the verified subset)",
            )
        if isinstance(node, ast.Subscript):
            if isinstance(node.slice, ast.Slice):
                raise self.err(node, "slices are not supported")
            return Index(self.array_expr(node.value), self.expr(node.slice))
        if isinstance(node, ast.List):
            raise self.err(
                node,
                "a list literal is an array and cannot be used where a scalar is expected "
                "(assign it to a name, index it, or take len(...))",
            )
        if isinstance(node, (ast.Tuple, ast.Set, ast.Dict)):
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

    # -- arrays ------------------------------------------------------------

    def kind(self, node: ast.expr) -> str:
        """Static kind of an assignment value (without lowering it)."""
        if isinstance(node, ast.List):
            return ARRAY
        if isinstance(node, ast.Name) and self.kinds.get(node.id) == ARRAY:
            return ARRAY
        return SCALAR

    def array_literal(self, node: ast.List) -> Expr:
        items: list[Expr] = []
        for element in node.elts:
            if isinstance(element, (ast.List, ast.Tuple, ast.Set, ast.Dict)):
                raise self.err(
                    element,
                    "nested arrays are not supported "
                    "(the verified subset has one array dimension)",
                )
            items.append(self.expr(element))
        return ArrayLit(tuple(items))

    def array_expr(self, node: ast.expr) -> Expr:
        """Lower an expression that must be an array (literal or variable)."""
        if isinstance(node, ast.List):
            return self.array_literal(node)
        if isinstance(node, ast.Name):
            slot = self.lookup(node)
            if self.kinds.get(node.id) != ARRAY:
                raise self.err(
                    node,
                    f"'{node.id}' is a scalar, not an array; only arrays can be indexed "
                    "or measured",
                )
            return Slot(slot)
        raise self.err(
            node, "only a list literal or an array variable can be indexed or measured"
        )

    # -- statements --------------------------------------------------------

    def block(self, nodes: Sequence[ast.stmt]) -> Stmt:
        out: list[Stmt] = []
        for index, node in enumerate(nodes):
            if index and stmt_returns(nodes[index - 1]):
                raise self.err(
                    node,
                    "unreachable statement: the preceding statement always returns",
                )
            if isinstance(node, ast.Return):
                out.append(Ret(self.returns(node)))
            else:
                out.append(self.stmt(node))
        return Seq(tuple(out))

    def returns(self, node: ast.Return) -> tuple[Expr, ...]:
        if node.value is None:
            raise self.err(node, "return must produce at least one scalar (state vector)")
        if isinstance(node.value, ast.Tuple):
            if not node.value.elts:
                raise self.err(node, "empty return tuple")
            exprs = tuple(self.expr(e) for e in node.value.elts)
        else:
            exprs = (self.expr(node.value),)
        if self.result_arity is None:
            self.result_arity = len(exprs)
        elif len(exprs) != self.result_arity:
            raise self.err(
                node,
                f"return produces {len(exprs)} value(s) but an earlier return produces "
                f"{self.result_arity}; all returns of a function must have the same arity",
            )
        return exprs

    def bind(self, name: str, value_node: ast.expr) -> Stmt:
        kind = self.kind(value_node)
        if kind == ARRAY:
            if not isinstance(value_node, ast.List):
                raise self.err(
                    value_node,
                    f"array assignment copies are not supported (no aliasing): "
                    f"assign a fresh list literal to '{name}' instead",
                )
            value = self.array_literal(value_node)
        else:
            value = self.expr(value_node)
        slot = self.fresh(name)
        self.env[name] = slot
        self.kinds[name] = kind
        return Assign(slot, value)

    def subscript_store(self, target: ast.Subscript, value_node: ast.expr) -> Stmt:
        if not isinstance(target.value, ast.Name):
            raise self.err(
                target, "only subscript assignment to a named array is supported"
            )
        if isinstance(target.slice, ast.Slice):
            raise self.err(target, "slice assignment is not supported")
        name = target.value.id
        array = self.array_expr(target.value)
        index = self.expr(target.slice)
        stored = self.expr(value_node)
        slot = self.fresh(name)
        self.env[name] = slot
        self.kinds[name] = ARRAY
        return Assign(slot, Set(array, index, stored))

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
            if isinstance(target, ast.Subscript):
                return self.subscript_store(target, node.value)
            if not isinstance(target, ast.Name):
                raise self.err(
                    node,
                    "only assignment to a plain name or xs[i] is supported "
                    "(no attributes, tuple unpacking or slicing)",
                )
            return self.bind(target.id, node.value)
        if isinstance(node, ast.AnnAssign):
            if not isinstance(node.target, ast.Name) or node.value is None:
                raise self.err(node, "only 'name: type = value' is supported")
            return self.bind(node.target.id, node.value)
        if isinstance(node, ast.AugAssign):
            if isinstance(node.target, ast.Subscript):
                raise self.err(
                    node,
                    "augmented subscript assignment (xs[i] += v) is not supported; "
                    "write xs[i] = xs[i] + v",
                )
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
        pre_kinds = dict(self.kinds)
        cond = self.cond(node.test)
        then_returns = block_returns(node.body)
        else_returns = block_returns(node.orelse)

        self.env = dict(pre)
        self.kinds = dict(pre_kinds)
        then_stmt = self.block(node.body)
        then_env = dict(self.env)
        then_kinds = dict(self.kinds)

        self.env = dict(pre)
        self.kinds = dict(pre_kinds)
        else_stmt = self.block(node.orelse) if node.orelse else Skip()
        else_env = dict(self.env)
        else_kinds = dict(self.kinds)

        # Merge only variables whose binding differs between the paths that can
        # still fall through.  A definitely-returning branch never reaches the
        # merge, so it contributes no input (its side becomes a dead slot).
        merged: set[str] = set()
        if then_returns and else_returns:
            pass
        elif then_returns:
            merged = {name for name, slot in else_env.items() if pre.get(name) != slot}
        elif else_returns:
            merged = {name for name, slot in then_env.items() if pre.get(name) != slot}
        else:
            for name in set(then_env) | set(else_env):
                lhs, rhs = then_env.get(name), else_env.get(name)
                if lhs == rhs:
                    continue
                if lhs is None or rhs is None:
                    raise self.err(
                        node,
                        f"variable '{name}' may be unbound after the if: "
                        "it is assigned in only one branch",
                    )
                merged.add(name)

        phis: list[Phi] = []
        self.env = dict(pre)
        self.kinds = dict(pre_kinds)
        for name in sorted(merged):
            then_slot = then_env.get(name, pre.get(name))
            else_slot = else_env.get(name, pre.get(name))
            if then_slot is None:
                then_slot = else_slot
            if else_slot is None:
                else_slot = then_slot
            if then_slot is None or else_slot is None:  # pragma: no cover - invariant
                raise self.err(node, f"internal error: no value for '{name}' after if")
            if then_returns and not else_returns:
                merged_kind = else_kinds.get(name, pre_kinds.get(name))
            elif else_returns and not then_returns:
                merged_kind = then_kinds.get(name, pre_kinds.get(name))
            elif then_returns and else_returns:  # pragma: no cover - unreachable code
                merged_kind = pre_kinds.get(name)
            else:
                then_kind, else_kind = then_kinds.get(name), else_kinds.get(name)
                if then_kind != else_kind:
                    raise self.err(
                        node,
                        f"variable '{name}' changes between scalar and array in the "
                        "branches of the if",
                    )
                merged_kind = then_kind
            if merged_kind is None:  # pragma: no cover - invariant
                raise self.err(node, f"internal error: no kind for '{name}' after if")
            slot = self.fresh(name)
            phis.append(Phi(slot, then_slot, else_slot))
            self.env[name] = slot
            self.kinds[name] = merged_kind
        return Ite(cond, then_stmt, else_stmt, tuple(phis))

    def while_(self, node: ast.While) -> Stmt:
        if node.orelse:
            raise self.err(node, "while/else is not supported")
        pre = dict(self.env)
        pre_kinds = dict(self.kinds)
        assigned = sorted(assigned_names(node.body))
        # Only variables that already have a value can be loop-carried.  A
        # variable first assigned inside the body is checked after lowering:
        # if it is assigned only on a path that returns, it never reaches the
        # back edge and needs no header.
        carried = [name for name in assigned if name in pre]
        introduced = [name for name in assigned if name not in pre]
        headers = {name: self.fresh(f"{name}#loop") for name in carried}
        self.env = dict(pre)
        self.kinds = dict(pre_kinds)
        self.env.update(headers)
        cond = self.cond(node.test)
        body = self.block(node.body)
        body_env = dict(self.env)
        body_kinds = dict(self.kinds)
        for name in introduced:
            if name in body_env:
                raise self.err(
                    node,
                    f"variable '{name}' is assigned inside the loop but has no value before it; "
                    "initialise it before the loop so the loop-carried slot is well-defined",
                )
        for name in carried:
            if body_kinds.get(name) != pre_kinds[name]:
                raise self.err(
                    node,
                    f"variable '{name}' changes between scalar and array inside the loop",
                )
        phis = tuple(Phi(headers[name], body_env[name], pre[name]) for name in carried)
        # Initialise the header slots explicitly, in source order of the loop
        # variables; `While` itself only performs the back-edge updates.
        init = tuple(Assign(headers[name], Slot(pre[name])) for name in carried)
        self.env = dict(pre)
        self.kinds = dict(pre_kinds)
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
    body = lowerer.block(target.body)

    ret_exprs = _return_exprs(body)
    if not block_returns(target.body):
        raise FrontendError(
            f"function '{target.name}' does not return on every path; "
            "implicit fall-through (returning None) is not supported",
            target,
            filename,
        )
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
    """Return expressions of the first return in pre-order (arity is uniform)."""
    for stmt in stmts(body):
        if isinstance(stmt, Ret):
            return stmt.exprs
    raise FrontendError("function has no return statement")
