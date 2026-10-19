"""Surface Python -> core source AST, for the verified lowering certificate.

The frontend validates the supported subset; this module performs the *purely
syntactic* desugaring (augmented assignment, explicit `**`, `abs`, docstring and
`pass` removal) and emits the core AST as a Lean value.

Variable names are replaced by integer ids assigned in **sorted name order**, so
that "sorted assigned names" in the SSA lowering becomes "sorted ids". The Lean
lowering (`Pontifex/Core/Lower.lean`) then reproduces the IR body and the
generated module checks that by `rfl`:

    theorem <fn>_lowering : Source.lowerBody <fn>Source = .ok <fn>IR.body := rfl

That certificate checks Python's SSA output against the Lean reference lowering.
It is not a source/IR semantic-preservation theorem: the reference algorithm's
fidelity, transcription below, and surface desugaring remain trusted and tested.
"""

from __future__ import annotations

import ast
import math
import struct
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from .errors import FrontendError, UnsupportedError
from .frontend import MAX_POW_EXPONENT, Translated

BIN_OPS = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul", ast.Div: "div"}
CMP_OPS = {
    ast.Lt: "lt",
    ast.LtE: "le",
    ast.Gt: "gt",
    ast.GtE: "ge",
    ast.Eq: "eq",
    ast.NotEq: "ne",
}


class SExpr:
    pass


@dataclass(frozen=True)
class Var(SExpr):
    id: int


@dataclass(frozen=True)
class Lit(SExpr):
    value: Fraction
    bits: int | None = None


@dataclass(frozen=True)
class Pow(SExpr):
    base: SExpr
    exponent: int


@dataclass(frozen=True)
class Bin(SExpr):
    op: str
    lhs: SExpr
    rhs: SExpr


@dataclass(frozen=True)
class Un(SExpr):
    op: str
    arg: SExpr


class SCond:
    pass


@dataclass(frozen=True)
class Cmp(SCond):
    op: str
    lhs: SExpr
    rhs: SExpr


@dataclass(frozen=True)
class And(SCond):
    lhs: SCond
    rhs: SCond


@dataclass(frozen=True)
class Or(SCond):
    lhs: SCond
    rhs: SCond


@dataclass(frozen=True)
class Not(SCond):
    arg: SCond


@dataclass(frozen=True)
class BoolConst(SCond):
    value: bool


class SStmt:
    pass


@dataclass(frozen=True)
class Assign(SStmt):
    var: int
    expr: SExpr


@dataclass(frozen=True)
class Ite(SStmt):
    cond: SCond
    then_: tuple[SStmt, ...]
    else_: tuple[SStmt, ...]


@dataclass(frozen=True)
class While(SStmt):
    cond: SCond
    body: tuple[SStmt, ...]


@dataclass(frozen=True)
class Ret(SStmt):
    exprs: tuple[SExpr, ...]


@dataclass(frozen=True)
class Skip(SStmt):
    pass


@dataclass(frozen=True)
class SourceFn:
    param_ids: tuple[int, ...]
    body: tuple[SStmt, ...]


class _NameCollector(ast.NodeVisitor):
    """Collect variable names in the function body.

    Annotations are skipped: `x: float = ...` mentions `float` syntactically,
    but it is a type expression, not a program variable.
    """

    def __init__(self) -> None:
        self.names: set[str] = set()

    def visit_Name(self, node: ast.Name) -> None:
        self.names.add(node.id)

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        self.visit(node.target)
        if node.value is not None:
            self.visit(node.value)

    def visit_Call(self, node: ast.Call) -> None:
        # The callee is a builtin (abs), not a program variable.
        for argument in node.args:
            self.visit(argument)
        for keyword in node.keywords:
            self.visit(keyword.value)


class _NameTable:
    def __init__(self, fn: ast.FunctionDef):
        names: set[str] = {arg.arg for arg in fn.args.args}
        collector = _NameCollector()
        for statement in fn.body:
            collector.visit(statement)
        names |= collector.names
        ordered = sorted(names)
        self.ids = {name: index for index, name in enumerate(ordered)}

    def __call__(self, name: str) -> int:
        return self.ids[name]


class _Desugar:
    def __init__(self, fn: ast.FunctionDef, filename: str):
        self.fn = fn
        self.filename = filename
        self.ids = _NameTable(fn)

    def err(self, node: ast.AST, msg: str) -> UnsupportedError:
        return UnsupportedError(msg, node, self.filename)

    # -- expressions -------------------------------------------------------

    def expr(self, node: ast.expr) -> SExpr:
        if isinstance(node, ast.Name):
            return Var(self.ids(node.id))
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
                if not (isinstance(node.right, ast.Constant) and isinstance(node.right.value, int)):
                    raise self.err(node, "only integer literal exponents are supported")
                n = node.right.value
                if isinstance(node.right.value, bool) or not (0 <= n <= MAX_POW_EXPONENT):
                    raise self.err(node, f"exponent must be in [0, {MAX_POW_EXPONENT}]")
                base = self.expr(node.left)
                return Pow(base, n)
            op = BIN_OPS.get(type(node.op))
            if op is None:
                raise self.err(node, f"unsupported operator {type(node.op).__name__}")
            return Bin(op, self.expr(node.left), self.expr(node.right))
        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.USub):
                return Un("neg", self.expr(node.operand))
            if isinstance(node.op, ast.UAdd):
                return self.expr(node.operand)
            raise self.err(node, "unsupported unary operator")
        if isinstance(node, ast.Call):
            if (
                isinstance(node.func, ast.Name)
                and node.func.id == "abs"
                and len(node.args) == 1
                and not node.keywords
            ):
                return Un("abs", self.expr(node.args[0]))
            raise self.err(node, "only abs(x) calls are supported")
        raise self.err(node, f"expression '{type(node).__name__}' is not supported")

    def cond(self, node: ast.expr) -> SCond:
        if isinstance(node, ast.Compare):
            if len(node.ops) != 1 or len(node.comparators) != 1:
                raise self.err(node, "chained comparisons are not supported")
            op = CMP_OPS.get(type(node.ops[0]))
            if op is None:
                raise self.err(node, f"unsupported comparison {type(node.ops[0]).__name__}")
            return Cmp(op, self.expr(node.left), self.expr(node.comparators[0]))
        if isinstance(node, ast.BoolOp):
            parts = [self.cond(v) for v in node.values]
            out = parts[0]
            for part in parts[1:]:
                out = And(out, part) if isinstance(node.op, ast.And) else Or(out, part)
            return out
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return Not(self.cond(node.operand))
        if isinstance(node, ast.Constant) and isinstance(node.value, bool):
            return BoolConst(node.value)
        raise self.err(node, "'not a supported condition'")

    # -- statements --------------------------------------------------------

    def block(self, nodes: Sequence[ast.stmt]) -> tuple[SStmt, ...]:
        return tuple(self.stmt(node) for node in nodes)

    def stmt(self, node: ast.stmt) -> SStmt:
        if isinstance(node, ast.Pass):
            return Skip()
        if isinstance(node, ast.Expr):
            if isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
                return Skip()
            raise self.err(node, "expression statements are not supported")
        if isinstance(node, ast.Assign):
            if len(node.targets) != 1 or not isinstance(node.targets[0], ast.Name):
                raise self.err(node, "only 'name = expr' is supported")
            return Assign(self.ids(node.targets[0].id), self.expr(node.value))
        if isinstance(node, ast.AnnAssign):
            if not isinstance(node.target, ast.Name) or node.value is None:
                raise self.err(node, "only 'name: type = expr' is supported")
            return Assign(self.ids(node.target.id), self.expr(node.value))
        if isinstance(node, ast.AugAssign):
            if not isinstance(node.target, ast.Name):
                raise self.err(node, "only augmented assignment to a name is supported")
            op = BIN_OPS.get(type(node.op))
            if op is None:
                raise self.err(node, "unsupported augmented operator")
            var = self.ids(node.target.id)
            return Assign(var, Bin(op, Var(var), self.expr(node.value)))
        if isinstance(node, ast.If):
            return Ite(self.cond(node.test), self.block(node.body), self.block(node.orelse))
        if isinstance(node, ast.While):
            if node.orelse:
                raise self.err(node, "while/else is not supported")
            return While(self.cond(node.test), self.block(node.body))
        if isinstance(node, ast.Return):
            if node.value is None:
                raise self.err(node, "return must produce at least one scalar")
            if isinstance(node.value, ast.Tuple):
                return Ret(tuple(self.expr(e) for e in node.value.elts))
            return Ret((self.expr(node.value),))
        raise self.err(node, f"statement '{type(node).__name__}' is not supported")

    def source_fn(self) -> SourceFn:
        return SourceFn(
            param_ids=tuple(self.ids(arg.arg) for arg in self.fn.args.args),
            body=self.block(self.fn.body),
        )


def desugar(translated: Translated) -> SourceFn:
    """Desugar the function selected by ``Translated`` into the core AST."""
    tree = ast.parse(translated.source, filename=translated.filename)
    functions = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
    matches = [f for f in functions if f.name == translated.function_name]
    if not matches:  # pragma: no cover - frontend guarantees selection
        raise FrontendError(f"no function named {translated.function_name!r}")
    return _Desugar(matches[0], translated.filename).source_fn()


# ---------------------------------------------------------------------------
# Lean emission
# ---------------------------------------------------------------------------


def _rat(value: Fraction) -> str:
    if value.denominator == 1:
        return f"({value.numerator} : Rat)"
    return f"(({value.numerator} : Rat) / {value.denominator})"


def _expr(e: SExpr) -> str:
    if isinstance(e, Var):
        return f"(.var {e.id})"
    if isinstance(e, Lit):
        if e.bits is not None:
            return f"(.floatLit {_rat(e.value)} {e.bits})"
        return f"(.lit {_rat(e.value)})"
    if isinstance(e, Pow):
        return f"(.pow {_expr(e.base)} {e.exponent})"
    if isinstance(e, Bin):
        return f"(.bin .{e.op} {_expr(e.lhs)} {_expr(e.rhs)})"
    if isinstance(e, Un):
        return f"(.un .{e.op} {_expr(e.arg)})"
    raise TypeError(type(e))


def _cond(c: SCond) -> str:
    if isinstance(c, Cmp):
        return f"(.cmp .{c.op} {_expr(c.lhs)} {_expr(c.rhs)})"
    if isinstance(c, And):
        return f"(.and {_cond(c.lhs)} {_cond(c.rhs)})"
    if isinstance(c, Or):
        return f"(.or {_cond(c.lhs)} {_cond(c.rhs)})"
    if isinstance(c, Not):
        return f"(.not {_cond(c.arg)})"
    if isinstance(c, BoolConst):
        return f"(.const {'true' if c.value else 'false'})"
    raise TypeError(type(c))


def _stmt(s: SStmt) -> str:
    if isinstance(s, Skip):
        return ".skip"
    if isinstance(s, Assign):
        return f"(.assign {s.var} {_expr(s.expr)})"
    if isinstance(s, Ite):
        then = ", ".join(_stmt(x) for x in s.then_)
        other = ", ".join(_stmt(x) for x in s.else_)
        return f"(.ite {_cond(s.cond)} [{then}] [{other}])"
    if isinstance(s, While):
        body = ", ".join(_stmt(x) for x in s.body)
        return f"(.whil {_cond(s.cond)} [{body}])"
    if isinstance(s, Ret):
        return "(.ret [" + ", ".join(_expr(e) for e in s.exprs) + "])"
    raise TypeError(type(s))


def source_declaration(name: str, fn: SourceFn) -> str:
    params = ", ".join(str(i) for i in fn.param_ids)
    body = "\n      ".join(_stmt(s) + "," for s in fn.body)
    return (
        f"/-- Core source AST of the Python function, with names replaced by ids\n"
        f"    assigned in sorted name order (see `pontifex/source.py`). -/\n"
        f"def {name}Source : Source.Fn :=\n"
        f"  {{ paramIds := [{params}]\n"
        f"    body := [\n      {body}\n    ] }}\n\n"
        f"set_option maxRecDepth 100000 in\n"
        f"/-- Kernel certificate: the verified SSA lowering reproduces the emitted IR body. -/\n"
        f"theorem {name}_lowering :\n"
        f"    Source.lowerBody {name}Source = .ok {name}IR.body :=\n"
        f"  rfl\n"
    )
