/-
  Pontifex.Core.Source

  A **verified core source language**: the surface Python subset after purely
  syntactic desugaring (augmented assignment, explicit natural-exponent power,
  docstring removal), before SSA lowering.

  Variable references are `Nat` identifiers rather than strings.  This is a
  canonical renaming: the frontend assigns ids in sorted order of the original
  name (see `python/pontifex/source.py`), so ordering decisions in the lowering
  (`sorted` of assigned names, sorted loop variables) become ordering by id.
  Keeping the certificate free of strings means the kernel never has to reduce
  string equality, which is opaque in modern Lean.

  This language is deliberately *not* the whole Python subset: it is the part
  whose translation into SSA can be proved.  Surface desugaring remains trusted
  (and is cross-checked by the lowering certificate, since both pipelines start
  from the same source AST).
-/
import Std
import Pontifex.Core.IR

namespace Pontifex.Source

/-- Scalar expressions of the core source language. -/
inductive Expr where
  | var : Nat → Expr
  | lit : Rat → Expr
  | floatLit : Rat → UInt64 → Expr
  | pow : Expr → Nat → Expr
  | bin : BinOp → Expr → Expr → Expr
  | un : UnOp → Expr → Expr
  /-- `a[i]` (bounds checked in the IR semantics). -/
  | index : Expr → Expr → Expr
  /-- `len(a)`. -/
  | len : Expr → Expr
  /-- `[e1, e2, ...]`, one-dimensional. -/
  | arrayLit : List Expr → Expr
  /-- Functional update `a[i] = v` producing a new array. -/
  | set : Expr → Expr → Expr → Expr
  deriving Repr

/-- Boolean conditions of the core source language. -/
inductive Cond where
  | cmp : CmpOp → Expr → Expr → Cond
  | and : Cond → Cond → Cond
  | or : Cond → Cond → Cond
  | not : Cond → Cond
  | const : Bool → Cond
  deriving Repr

/-- Statements of the core source language. -/
inductive Stmt where
  /-- Bind a source variable. -/
  | assign : Nat → Expr → Stmt
  /-- `if c: thenBody else: elseBody`. -/
  | ite : Cond → List Stmt → List Stmt → Stmt
  /-- `while c: body`. -/
  | whil : Cond → List Stmt → Stmt
  /-- Return a flat tuple of scalars.  May appear early: a block stops at the
      first `ret`, matching the IR's `returned` outcome. -/
  | ret : List Expr → Stmt
  /-- `pass` and removed docstrings. -/
  | skip : Stmt
  deriving Repr

/-- A core source function: parameter ids (in signature order) and a body. -/
structure Fn where
  /-- Source ids of the parameters, in positional order. -/
  paramIds : List Nat
  /-- Body statements (a flat sequence; nesting only through `ite`/`whil`). -/
  body : List Stmt
  deriving Repr

end Pontifex.Source
