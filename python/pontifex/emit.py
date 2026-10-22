"""Lean 4 code generation from the SSA IR.

Emitted per function:

* ``<fn>IR`` -- the IR itself, as a Lean *value* (the same data written to
  ``.ir.json``, so the Lean JSON decoder can be checked against it).
* ``<fn>`` -- a functional translation. Straight-line assignments become local
  ``let`` bindings; control flow uses independently emitted slot-state blocks
  with exactly the reference interpreter's fuel discipline (see certify.py).
* ``<fn>_link`` -- kernel-checked code-versus-IR linkage. Straight-line code is
  checked by ``rfl`` at the selected fuel. Control-flow blocks are certified for
  ALL fuels and arbitrary numeric backends (including Rat and Float).
Native conformance checks are emitted separately by ``emit_native_samples``;
they must never be appended to a certificate module.
"""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction

from .frontend import Translated
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
    Select,
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
from .version import (
    FUEL_POLICY_ALL_FUEL,
    FUEL_POLICY_LITERAL,
    IR_VERSION,
    NUMERIC_MODE_EXACT_RAT,
)

OP_SYMBOLS = {"add": "+", "sub": "-", "mul": "*", "div": "/"}

Env = dict[int, str]


# ---------------------------------------------------------------------------
# Literals, tuples, names, layout
# ---------------------------------------------------------------------------


def rat_literal(value: Fraction) -> str:
    num, den = value.numerator, value.denominator
    if den == 1:
        return f"({num} : Rat)"
    return f"(({num} : Rat) / {den})"


def lean_string(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def tuple_type(n: int) -> str:
    if n == 0:
        return "Unit"
    if n == 1:
        return "Rat"
    return " × ".join(["Rat"] * n)


def option_type(n: int) -> str:
    return f"Option {tuple_type(n)}" if n <= 1 else f"Option ({tuple_type(n)})"


def tuple_term(items: Sequence[str], n: int) -> str:
    if n == 0:
        return "()"
    if n == 1:
        return items[0]
    return "(" + ", ".join(items) + ")"


def ind(text: str, n: int = 2) -> str:
    """Indent every non-empty line by ``n`` spaces."""
    pad = " " * n
    return "\n".join(pad + line if line.strip() else line for line in text.splitlines())


def safe_name(name: str) -> str:
    out = "".join(c if (c.isalnum() or c == "_") else "_" for c in name)
    if not out or out[0].isdigit():
        out = "v_" + out
    return out


# ---------------------------------------------------------------------------
# IR -> Lean value (for the `<fn>IR` declaration)
# ---------------------------------------------------------------------------


def expr_of_ir(e: Expr) -> str:
    if isinstance(e, Slot):
        return f"(.slot {e.index})"
    if isinstance(e, Lit):
        if e.bits is not None:
            return f"(.floatLit {rat_literal(e.value)} {e.bits})"
        return f"(.lit {rat_literal(e.value)})"
    if isinstance(e, Pow):
        return f"(.pow {expr_of_ir(e.base)} {e.exponent})"
    if isinstance(e, Bin):
        return f"(.bin .{e.op} {expr_of_ir(e.lhs)} {expr_of_ir(e.rhs)})"
    if isinstance(e, Un):
        return f"(.un .{e.op} {expr_of_ir(e.arg)})"
    if isinstance(e, Select):
        return f"(.select {cond_of_ir(e.cond)} {expr_of_ir(e.then_)} {expr_of_ir(e.else_)})"
    if isinstance(e, Index):
        return f"(.index {expr_of_ir(e.array)} {expr_of_ir(e.index)})"
    if isinstance(e, Len):
        return f"(.len {expr_of_ir(e.array)})"
    if isinstance(e, ArrayLit):
        items = ", ".join(expr_of_ir(i) for i in e.items)
        return f"(.arrayLit [{items}])"
    if isinstance(e, Set):
        return f"(.set {expr_of_ir(e.array)} {expr_of_ir(e.index)} {expr_of_ir(e.value)})"
    raise TypeError(type(e))


def cond_of_ir(c: Cond) -> str:
    if isinstance(c, Cmp):
        return f"(.cmp .{c.op} {expr_of_ir(c.lhs)} {expr_of_ir(c.rhs)})"
    if isinstance(c, And):
        return f"(.and {cond_of_ir(c.lhs)} {cond_of_ir(c.rhs)})"
    if isinstance(c, Or):
        return f"(.or {cond_of_ir(c.lhs)} {cond_of_ir(c.rhs)})"
    if isinstance(c, Not):
        return f"(.not {cond_of_ir(c.arg)})"
    if isinstance(c, Where):
        return f"(.const {'true' if c.value else 'false'})"
    raise TypeError(type(c))


def phis_of_ir(phis: Sequence[Phi]) -> str:
    return "[" + ", ".join(f"⟨{p.slot}, {p.lhs}, {p.rhs}⟩" for p in phis) + "]"


def stmt_of_ir(s: Stmt) -> str:
    if isinstance(s, Skip):
        return ".skip"
    if isinstance(s, Assign):
        return f"(.assign {s.slot} {expr_of_ir(s.expr)})"
    if isinstance(s, Seq):
        return "(.seq [" + ", ".join(stmt_of_ir(x) for x in s.body) + "])"
    if isinstance(s, Ite):
        return (
            f"(.ite {cond_of_ir(s.cond)} {stmt_of_ir(s.then_)} {stmt_of_ir(s.else_)} "
            f"{phis_of_ir(s.phis)})"
        )
    if isinstance(s, While):
        return f"(.whil {cond_of_ir(s.cond)} {phis_of_ir(s.phis)} {stmt_of_ir(s.body)})"
    if isinstance(s, Ret):
        return "(.ret [" + ", ".join(expr_of_ir(e) for e in s.exprs) + "])"
    raise TypeError(type(s))


def ir_declaration(name: str, fn: Fn) -> str:
    params = ", ".join(lean_string(p) for p in fn.params)
    slots = ", ".join(lean_string(p) for p in fn.slot_names)
    return (
        f"/-- The checked SSA IR that `{name}` was generated from. -/\n"
        f"def {name}IR : Fn :=\n"
        f"  {{ name := {lean_string(fn.name)}\n"
        f"    params := [{params}]\n"
        f"    slotNames := [{slots}]\n"
        f"    body := {stmt_of_ir(fn.body)} }}\n"
    )


# ---------------------------------------------------------------------------
# Direct translation
# ---------------------------------------------------------------------------


class Emitter:
    def __init__(self, fn: Fn):
        self.fn = fn
        self.slot_names = fn.slot_names
        self._slot_var: dict[int, str] = {i: name for i, name in enumerate(fn.params)}
        self._used: set[str] = {name for name in fn.params}

    # -- naming ------------------------------------------------------------

    def slot_var(self, slot: int) -> str:
        if slot in self._slot_var:
            return self._slot_var[slot]
        hint = safe_name(self.slot_names[slot]) if slot < len(self.slot_names) else f"v{slot}"
        name = hint
        index = 1
        while name in self._used:
            name = f"{hint}_{index}"
            index += 1
        self._used.add(name)
        self._slot_var[slot] = name
        return name

    # -- expressions -------------------------------------------------------

    def expr(self, e: Expr, env: Env) -> str:
        if isinstance(e, Slot):
            if e.index not in env:
                raise ValueError(f"slot {e.index} read before assignment (invalid SSA IR)")
            return env[e.index]
        if isinstance(e, Lit):
            return rat_literal(e.value)
        if isinstance(e, Bin):
            return f"({self.expr(e.lhs, env)} {OP_SYMBOLS[e.op]} {self.expr(e.rhs, env)})"
        if isinstance(e, Un):
            if e.op == "neg":
                return f"(-{self.expr(e.arg, env)})"
            if e.op == "abs":
                return f"(Rat.abs {self.expr(e.arg, env)})"
        if isinstance(e, (Index, Len, ArrayLit, Set)):
            raise TypeError("array expressions require the certified backend")
        raise TypeError(type(e))

    # -- statements -------------------------------------------------------

    def emits(self, s: Stmt, env: Env, k) -> str:
        """Emit ``s`` then the continuation ``k(env_after)``.

        The emitted text uses relative indentation only; embedding sites indent
        it.  Assignments are emitted as ``let`` bindings so that no expression
        is duplicated.
        """
        if isinstance(s, Skip):
            return k(env)
        if isinstance(s, Assign):
            value = self.expr(s.expr, env)
            name = self.slot_var(s.slot)
            new_env = dict(env)
            new_env[s.slot] = name
            return f"let {name} := {value};\n" + k(new_env)
        if isinstance(s, Seq):

            def step(rest: tuple[Stmt, ...], env: Env) -> str:
                if not rest:
                    return k(env)
                return self.emits(rest[0], env, lambda e: step(rest[1:], e))

            return step(tuple(s.body), env)
        if isinstance(s, Ret):
            values = tuple_term([self.expr(e, env) for e in s.exprs], len(s.exprs))
            return f"some {values}"
        raise TypeError(type(s))


def return_arity(s: Stmt) -> int:
    """Arity of the function's returns; every return must agree (frontend)."""
    returns = [stmt for stmt in stmts(s) if isinstance(stmt, Ret)]
    if not returns:
        raise ValueError("function body has no return statement")
    arity = len(returns[0].exprs)
    for ret in returns[1:]:
        if len(ret.exprs) != arity:
            raise ValueError("return statements disagree on arity")
    return arity


def needs_checked_backend(s: Stmt) -> bool:
    """Use full-outcome code for control flow or possibly failing arithmetic."""

    def checked(value):
        if isinstance(value, dict):
            if value.get("k") in {
                "ite",
                "while",
                "pow",
                "index",
                "len",
                "arrayLit",
                "set",
                "select",
            } or value.get("op") in {"div", "min", "max"}:
                return True
            return any(checked(v) for v in value.values())
        if isinstance(value, list):
            return any(checked(v) for v in value)
        return False

    return checked(s.to_json())


def has_control_flow(s: Stmt) -> bool:
    if isinstance(s, (Ite, While)):
        return True
    if isinstance(s, Seq):
        return any(has_control_flow(x) for x in s.body)
    return False


# ---------------------------------------------------------------------------
# Module emission
# ---------------------------------------------------------------------------


def _link_proof(fn: Fn, arity: int, fuel: int) -> str:
    params = " ".join(f"({p} : Rat)" for p in fn.params)
    args = " ".join(fn.params)
    args_list = ", ".join(fn.params)
    target = tuple_term([f"vs[{i}]!" for i in range(arity)], arity)
    rhs = (
        f"(Outcome.toOption (Fn.run Ops.rat {fn.name}IR {fuel} [{args_list}])).map "
        f"(fun vs => {target})"
    )
    return (
        f"/-- Kernel-checked linkage: the emitted `{fn.name}` is definitionally the\n"
        f"    reference semantics of `{fn.name}IR`.  `rfl` fails if the emitter disagrees. -/\n"
        f"theorem {fn.name}_link {params} :\n"
        f"    {fn.name} {fuel} {args} =\n"
        f"      {rhs} :=\n"
        f"  rfl\n"
    )


def emit_module(
    translated: Translated,
    *,
    namespace: str,
    fuel: int = 64,
    generator: str = "python -m pontifex compile",
) -> str:
    fn = translated.fn
    arity = return_arity(fn.body)
    straight_line = not needs_checked_backend(fn.body)
    body = ""
    if straight_line:
        emitter = Emitter(fn)
        env: Env = {i: name for i, name in enumerate(fn.params)}
        body = emitter.emits(fn.body, env, lambda _e: "none")
    binder = " ".join(f"({p} : Rat)" for p in fn.params)

    lines: list[str] = []
    lines.append("/-")
    lines.append(f"  Generated by pontifex from {translated.filename} (function `{fn.name}`).")
    lines.append("  DO NOT EDIT; regenerate with:")
    lines.append(f"    {generator}")
    lines.append("")
    lines.append(f"  `{fn.name}` is a pure functional translation of the Python source.")
    lines.append(f"  `{fn.name}IR` is the SSA IR it was generated from (the same data as the")
    lines.append("  accompanying `.ir.json`, which the Lean JSON decoder also accepts).")
    lines.append("-/")
    lines.append("import Pontifex.Core.Config")
    lines.append("import Pontifex.Core.Semantics")
    lines.append("import Pontifex.Core.Lower")
    if not straight_line:
        # Some blocks only copy state or ignore their positive fuel predecessor.
        lines.append("set_option linter.unusedVariables false")
    lines.append("")
    lines.append(f"namespace {namespace}")
    lines.append("")
    lines.append("open Pontifex")
    lines.append("")
    fuel_policy = FUEL_POLICY_LITERAL if straight_line else FUEL_POLICY_ALL_FUEL
    lines.append("/-- Semantic configuration this artifact was generated under. -/")
    lines.append("def pontifexConfig : Config :=")
    lines.append(f"  {{ irVersion := {IR_VERSION}")
    lines.append(f"    fuelPolicy := .{fuel_policy}")
    lines.append(f"    numericMode := .{NUMERIC_MODE_EXACT_RAT} }}")
    lines.append("")
    lines.append("#guard pontifexConfig.schemaMatches")
    lines.append(f"#guard pontifexConfig.fuelPolicy == .{fuel_policy}")
    lines.append(f"#guard pontifexConfig.numericMode == .{NUMERIC_MODE_EXACT_RAT}")
    lines.append("")
    # Private namespaces avoid collisions with caller locals, generated suffixes,
    # and other helper names. Every helper retains its own lowering/code linkage.
    callees: dict[str, str] = {}
    for index, callee in enumerate(translated.callees):
        callee_ns = f"Callee{index}"
        module = emit_module(callee, namespace=callee_ns, fuel=fuel, generator=generator)
        lines.append(module[module.index(f"namespace {callee_ns}\n") :])
        callees[callee.function_name] = f"{callee_ns}.{callee.function_name}"
    lines.append(ir_declaration(fn.name, fn))
    from .source import desugar, source_declaration

    lines.append(source_declaration(fn.name, desugar(translated), callees))
    facts = [f"Source.lowerBody {fn.name}Source = .ok {fn.name}IR.body"]
    proofs = [f"{fn.name}_lowering"]
    for ref in callees.values():
        facts.append(f"{ref}_program_lowering_spec")
        proofs.append(f"{ref}_program_lowering")
    proposition = " ∧\n    ".join(facts)
    proof = proofs[0] if len(proofs) == 1 else "⟨" + ", ".join(proofs) + "⟩"
    lines.append(
        f"/-- Own lowering and the recursively composed lowering evidence of every callee. -/\n"
        f"def {fn.name}_program_lowering_spec : Prop :=\n    {proposition}\n\n"
        f"theorem {fn.name}_program_lowering : {fn.name}_program_lowering_spec :=\n"
        f"  {proof}\n"
    )
    if straight_line:
        lines.append(f"/-- Direct Lean translation of the Python function `{fn.name}`. -/")
        lines.append(f"def {fn.name} (_fuel : Nat) {binder} : {option_type(arity)} :=")
        lines.append(ind(body, 2))
        lines.append("")
        lines.append(_link_proof(fn, arity, fuel))
    else:
        from .certify import emit_certified

        lines.append(emit_certified(fn))
    lines.append(f"end {namespace}")
    lines.append("")
    return "\n".join(lines)


def emit_native_samples(
    fn: Fn,
    *,
    namespace: str,
    fuel: int = 64,
    conformance: Sequence[tuple[Sequence[Fraction], Sequence[Fraction]]] = (),
) -> str:
    """Test declarations only: import the certificate in a separate test module.

    Native evaluation trusts Lean's compiler. These finite checks are not
    correctness certificates and must not become dependencies of audited code.
    """
    lines = [f"namespace {namespace}", ""]
    for index, (args, expected) in enumerate(conformance):
        arglist = " ".join(rat_literal(Fraction(a)) for a in args)
        values = tuple_term([rat_literal(Fraction(v)) for v in expected], len(expected))
        lines.append("/-- Finite native conformance test, not a correctness certificate. -/")
        lines.append(
            f"theorem {fn.name}_sample_{index} :\n"
            f"    {fn.name} {fuel} {arglist} = some {values} := by\n"
            f"  native_decide\n"
        )
    lines.extend([f"end {namespace}", ""])
    return "\n".join(lines)
