/-
  Pontifex.Core.IR

  The deep embedding of the *core language*: the small, explicitly typed,
  SSA-shaped intermediate representation that the Python frontend lowers into.

  Design notes
  ------------
  * Slots (natural numbers) replace source-level names.  Every assignment
    writes a fresh slot, which is what makes translation to a functional
    language immediate: slot references are pure substitutions.
  * `Phi` nodes make control-flow joins explicit.  For an `if`, the `slot` is
    the merged value, `lhs` is read when the condition holds, `rhs` otherwise.
    For a `while`, `slot` is the loop-carried header slot, `lhs` is the value
    produced by the body (back edge) and `rhs` is the value before the loop.
  * Literals are exact rationals.  The numeric meaning of a literal is decided
    by the `Ops` instance used by the interpreter: exact for `Rat`, rounded for
    `Float` (`ofRat`).
  * Expressions are total and scalar-valued; conditions are a separate sort so
    that the IR is simply typed by construction.
-/
import Std

namespace Pontifex

/-- Binary arithmetic operators supported by the core language. -/
inductive BinOp where
  | add | sub | mul | div
  deriving Repr, DecidableEq, Inhabited

/-- Comparison operators; these produce `Bool`, never a scalar. -/
inductive CmpOp where
  | lt | le | gt | ge | eq | ne
  deriving Repr, DecidableEq, Inhabited

/-- Unary scalar operators. -/
inductive UnOp where
  | neg | abs
  deriving Repr, DecidableEq, Inhabited

/-- Runtime values held in slots.

    Scalars are the arithmetic backend's numbers.  Arrays are fixed-length
    `List` values of scalars: length is intrinsic, and every access is
    bounds-checked.  There are no nested arrays, references, or aliasing.

    Keeping arrays as values (rather than a second environment) means slots,
    phis, `Outcome`, `exec`, `Fn.run`, and `exec_mono` keep their existing
    shape: an array can merge through an `if` or a loop header just like a
    scalar. -/
inductive Val (α : Type) where
  | scalar : α → Val α
  | array : List α → Val α
  deriving Repr, Inhabited, DecidableEq

/-- Scalar-typed expressions over slots.

    Evaluation is value-typed (`evalV`); scalar contexts unwrap with
    `Val.asScalar`, so an array where a scalar is required is `stuck`.

    * `index a i` reads element `i` of array `a`; a bad or out-of-range index
      is `failed .indexOutOfBounds`.
    * `len a` is the array's length as a scalar.
    * `arrayLit es` builds a fresh array from scalar expressions.
    * `set a i v` is a functional update: it produces a new array value.  This
      is what makes `xs[i] = v` SSA-friendly (the frontend assigns the result
      to a fresh slot for `xs`) and keeps the IR free of aliasing. -/
inductive Expr where
  | slot : Nat → Expr
  | lit : Rat → Expr
  | floatLit : Rat → UInt64 → Expr
  | pow : Expr → Nat → Expr
  | bin : BinOp → Expr → Expr → Expr
  | un : UnOp → Expr → Expr
  | index : Expr → Expr → Expr
  | len : Expr → Expr
  | arrayLit : List Expr → Expr
  | set : Expr → Expr → Expr → Expr
  deriving Repr

/-- Boolean-sorted expressions. -/
inductive Cond where
  | cmp : CmpOp → Expr → Expr → Cond
  | and : Cond → Cond → Cond
  | or : Cond → Cond → Cond
  | not : Cond → Cond
  | const : Bool → Cond
  deriving Repr

/-- A control-flow join: `slot := if cond then env[lhs] else env[rhs]`.

    For loops the same shape is used with `lhs` = value written by the body (the
    back edge) and `rhs` = the slot holding the value before the loop.  The
    header slot itself is initialised by an explicit assignment emitted by the
    frontend *before* the loop; `whil` only performs back-edge updates, so that
    exiting a loop keeps the loop-carried values. -/
structure Phi where
  slot : Nat
  lhs : Nat
  rhs : Nat
  deriving Repr, DecidableEq

/-- Structured statements.  There is no unstructured `goto`; the frontend
    guarantees every path ends in a `ret`. -/
inductive Stmt where
  | skip
  | assign : Nat → Expr → Stmt
  | seq : List Stmt → Stmt
  | ite : Cond → Stmt → Stmt → List Phi → Stmt
  | whil : Cond → List Phi → Stmt → Stmt
  | ret : List Expr → Stmt
  deriving Repr

namespace Stmt

/-- Concatenation of two statements (used by the frontend). -/
def append (s t : Stmt) : Stmt :=
  match s, t with
  | .seq ss, .seq ts => .seq (ss ++ ts)
  | .seq ss, t => .seq (ss ++ [t])
  | s, .seq ts => .seq (s :: ts)
  | s, t => .seq [s, t]

/-- Names of all slots written anywhere in a statement. -/
def writtenSlots : Stmt → List Nat
  | .skip => []
  | .assign i _ => [i]
  | .seq ss => ss.flatMap writtenSlots
  | .ite _ t e phis => writtenSlots t ++ writtenSlots e ++ phis.map (·.slot)
  | .whil _ phis body => phis.map (·.slot) ++ writtenSlots body
  | .ret _ => []

end Stmt

/-- A translated function: parameter names, slot names for readability, body. -/
structure Fn where
  name : String
  params : List String
  slotNames : List String
  body : Stmt
  deriving Repr

/-- The number of parameters (arity) of a function. -/
def Fn.arity (f : Fn) : Nat := f.params.length

end Pontifex
