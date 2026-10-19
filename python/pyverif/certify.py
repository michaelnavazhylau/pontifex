"""Proof-producing control-flow backend.

Each structured statement is specialized into a Lean function over slot state.
Generated executable code never calls `exec`, `evalE`, or `evalC`: expressions,
branches, phi copies, and recursion are emitted independently. Child blocks get
certificates before their parents. A loop's certificate is induction on fuel,
generalized over the entire environment (including all loop-carried values).

Certificates quantify over arbitrary `Ops α`, so they apply to both Rat and
Float without evaluating any arithmetic in the kernel. This establishes code
versus IR equivalence, NOT Python versus IR equivalence.
"""
from __future__ import annotations

from .ir import (
    And, Assign, Bin, Cmp, Cond, Expr, Fn, Ite, Lit, Not, Or, Ret, Seq,
    Skip, Slot, Stmt, Un, Where, While,
)


def emit_certified(fn: Fn) -> str:
    # Local import avoids a cycle: emit_module selects this backend.
    from .emit import ind, option_type, rat_literal, stmt_of_ir, tuple_term

    blocks: list[str] = []
    counter = 0

    def expr(e: Expr) -> str:
        if isinstance(e, Slot):
            return f"(env.get! {e.index})"
        if isinstance(e, Lit):
            return f"(ops.ofRat {rat_literal(e.value)})"
        if isinstance(e, Bin):
            return f"(ops.{e.op} {expr(e.lhs)} {expr(e.rhs)})"
        if isinstance(e, Un):
            return f"(ops.{e.op} {expr(e.arg)})"
        raise TypeError(type(e))

    def cond(c: Cond) -> str:
        if isinstance(c, Cmp):
            return f"(ops.{c.op} {expr(c.lhs)} {expr(c.rhs)})"
        if isinstance(c, (And, Or)):
            op = "&&" if isinstance(c, And) else "||"
            return f"({cond(c.lhs)} {op} {cond(c.rhs)})"
        if isinstance(c, Not):
            return f"(!{cond(c.arg)})"
        if isinstance(c, Where):
            return "true" if c.value else "false"
        raise TypeError(type(c))

    def copies(phis, source: str, choice: str) -> str:
        # All reads use a snapshot, NOT the partly updated accumulator.
        result = source
        for p in phis:
            index = p.lhs if choice == "back" else f"(if branch then {p.lhs} else {p.rhs})"
            result = f"({result}.set {p.slot} ({source}.get! {index}))"
        return result

    def block(s: Stmt) -> str:
        nonlocal counter
        name = f"{fn.name}_block{counter}"
        counter += 1
        children: list[str] = []
        recursive = False
        if isinstance(s, Skip):
            body = ".fellThrough env"
        elif isinstance(s, Assign):
            body = f".fellThrough (env.set {s.slot} {expr(s.expr)})"
        elif isinstance(s, Ret):
            body = ".returned [" + ", ".join(expr(e) for e in s.exprs) + "]"
        elif isinstance(s, Seq):
            if not s.body:
                body = ".fellThrough env"
            else:
                first = block(s.body[0])
                rest = block(Seq(s.body[1:]))
                children = [first, rest]
                body = (
                    f"match {first} ops fuel env with\n"
                    f"| .fellThrough next => {rest} ops fuel next\n"
                    f"| other => other"
                )
        elif isinstance(s, Ite):
            then = block(s.then_)
            otherwise = block(s.else_)
            children = [then, otherwise]
            body = (
                f"let branch := {cond(s.cond)}\n"
                f"match (if branch then {then} ops fuel env else {otherwise} ops fuel env) with\n"
                f"| .fellThrough next => .fellThrough {copies(s.phis, 'next', 'branch')}\n"
                f"| other => other"
            )
        elif isinstance(s, While):
            child = block(s.body)
            children = [child]
            recursive = True
            body = (
                f"if {cond(s.cond)} then\n"
                f"  match {child} ops fuel env with\n"
                f"  | .fellThrough next => {name} ops fuel {copies(s.phis, 'next', 'back')}\n"
                f"  | other => other\n"
                f"else .fellThrough env"
            )
        else:
            raise TypeError(type(s))

        rules = [name, "exec", *(f"{c}_correct" for c in children)]
        if recursive:
            rules.append("ih")
        proof = (
            "  induction fuel generalizing env with\n"
            "  | zero => rfl\n"
            f"  | succ fuel ih =>\n"
            f"    simp only [{', '.join(rules)}] <;> rfl\n"
        ) if recursive else f"  cases fuel <;> simp only [{', '.join(rules)}] <;> rfl\n"
        blocks.append(
            f"/-- Specialized executable block (no IR interpreter calls). -/\n"
            f"def {name} (ops : Ops α) [Inhabited α] : Nat → Env α → Outcome α\n"
            f"  | 0, _ => .outOfFuel\n"
            f"  | fuel + 1, env =>\n{ind(body, 4)}\n\n"
            f"/-- Kernel-checked block certificate, for every arithmetic backend and fuel. -/\n"
            f"theorem {name}_correct (ops : Ops α) [Inhabited α] (fuel : Nat) (env : Env α) :\n"
            f"    {name} ops fuel env = exec ops fuel {stmt_of_ir(s)} env := by\n"
            f"{proof}"
        )
        return name

    root = block(fn.body)
    # Public arguments remain positional. Do not let source names such as
    # `fuel`, `env`, or `ops` capture compiler-generated binders.
    inputs = [f"input{i}" for i in range(fn.arity)]
    params = " ".join(f"({p} : Rat)" for p in inputs)
    args = " ".join(inputs)
    args_list = ", ".join(inputs)
    # Functions in the supported subset always end in a flat return.
    from .emit import return_arity
    arity = return_arity(fn.body)
    projection = tuple_term([f"vs[{i}]!" for i in range(arity)], arity)
    blocks.append(
        f"/-- The compiled function preserves full outcomes, including exhaustion. -/\n"
        f"def {fn.name}Compiled (ops : Ops α) [Inhabited α] (fuel : Nat) (args : List α) :\n"
        f"    Outcome α := {root} ops fuel args\n\n"
        f"theorem {fn.name}_compiled_link (ops : Ops α) [Inhabited α]\n"
        f"    (fuel : Nat) (args : List α) :\n"
        f"    {fn.name}Compiled ops fuel args = Fn.run ops {fn.name}IR fuel args := by\n"
        f"  exact {root}_correct ops fuel args\n\n"
        f"/-- Public exact-rational tuple interface. `none` includes fuel exhaustion. -/\n"
        f"def {fn.name} (fuel : Nat) {params} : {option_type(arity)} :=\n"
        f"  ({fn.name}Compiled Ops.rat fuel [{args_list}]).toOption.map (fun vs => {projection})\n\n"
        f"/-- All-input, all-fuel linkage, with no native evaluation or proof holes. -/\n"
        f"theorem {fn.name}_link (fuel : Nat) {params} :\n"
        f"    {fn.name} fuel {args} =\n"
        f"      (Fn.run Ops.rat {fn.name}IR fuel [{args_list}]).toOption.map\n"
        f"        (fun vs => {projection}) := by\n"
        f"  unfold {fn.name}\n"
        f"  rw [{fn.name}_compiled_link]\n"
    )
    return "\n".join(blocks)
