/-
  Pontifex.Core.Lower

  Reference SSA lowering of the core source syntax into the IR.

  This is the Lean counterpart of `python/pontifex/frontend.py`'s lowering.  For
  every generated module, `Pontifex.Generated.*` contains

      def <fn>Source : Source.Fn := …
      theorem <fn>_lowering : lowerBody <fn>Source = .ok <fn>IR.body := rfl

  so the kernel checks that the IR body really is the image of the source AST
  under this function. This checks Python's SSA output against the Lean
  reference algorithm (slot allocation, phi merges, loop-carried headers).
  There is no source evaluator or semantic-preservation proof for this
  algorithm. Source transcription, desugaring, and fidelity of this reference
  lowering to Python remain trust boundaries; see `docs/TRUST.md`.

  Slot *names* are not produced: they are cosmetic, and omitting them keeps the
  kernel from having to evaluate string operations.
-/
import Std
import Pontifex.Core.IR
import Pontifex.Core.Source

namespace Pontifex.Source

/-- Lowering state: source id → current IR slot, plus the next fresh slot. -/
structure LowerState where
  env : List (Nat × Nat) := []
  next : Nat := 0
  deriving Repr

namespace LowerState

/-- Look up the current slot of a source variable (most recent binding wins). -/
def get? (st : LowerState) (v : Nat) : Option Nat :=
  (st.env.find? fun p => p.1 == v).map (·.2)

/-- Bind a source variable to a slot. -/
def bind (st : LowerState) (v slot : Nat) : LowerState :=
  { st with env := (v, slot) :: st.env }

/-- Bind a variable to a freshly allocated slot and advance the counter. -/
def bindFresh (st : LowerState) (v : Nat) : Nat × LowerState :=
  (st.next, { st with env := (v, st.next) :: st.env, next := st.next + 1 })

/-- Look up a variable that must be bound. -/
def require (st : LowerState) (v : Nat) : Except String Nat :=
  match st.get? v with
  | some slot => .ok slot
  | none => .error s!"source variable {v} is not bound at this point"

end LowerState

/-- Desugar-free expression lowering. -/
def lowerExpr (st : LowerState) : Expr → Except String _root_.Pontifex.Expr
  | .var v =>
      match st.get? v with
      | some slot => .ok (.slot slot)
      | none => .error s!"source variable {v} is not bound at this point"
  | .lit q => .ok (.lit q)
  | .floatLit q bits => .ok (.floatLit q bits)
  | .pow a n => do return .pow (← lowerExpr st a) n
  | .bin op a b => do
      return .bin op (← lowerExpr st a) (← lowerExpr st b)
  | .un op a => do
      return .un op (← lowerExpr st a)

/-- Condition lowering. -/
def lowerCond (st : LowerState) : Cond → Except String _root_.Pontifex.Cond
  | .cmp op a b => do
      return .cmp op (← lowerExpr st a) (← lowerExpr st b)
  | .and a b => do
      return .and (← lowerCond st a) (← lowerCond st b)
  | .or a b => do
      return .or (← lowerCond st a) (← lowerCond st b)
  | .not a => do
      return .not (← lowerCond st a)
  | .const b => .ok (.const b)

mutual

/-- Assigned variables of a single statement. -/
def assignedStmt : Stmt → List Nat
  | .assign v _ => [v]
  | .ite _ t e => assignedNames t ++ assignedNames e
  | .whil _ b => assignedNames b
  | .ret _ => []
  | .skip => []

/-- Source variables assigned anywhere inside these statements. -/
def assignedNames : List Stmt → List Nat
  | [] => []
  | s :: rest => assignedStmt s ++ assignedNames rest

end

/-- Insert into a sorted list. -/
def insertNat (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertNat x ys

/-- Insertion sort. Structural and `Nat`-only, so the kernel can evaluate it
    (unlike `List.mergeSort`, which is defined by well-founded recursion and is
    therefore opaque to `rfl`). -/
def sortNats : List Nat → List Nat
  | [] => []
  | x :: xs => insertNat x (sortNats xs)

/-- Assigned variables in the order the Python frontend uses: sorted, unique.

    The frontend assigns ids in sorted name order, so sorting ids reproduces
    `sorted(names)` exactly. -/
def assignedSorted (ss : List Stmt) : List Nat :=
  (sortNats (assignedNames ss)).eraseDups

mutual

/-- Lower a block of statements, threading slots and state.

    Recursion is structural on the statement list; callers wrap the resulting
    list in a `Seq`, matching the Python frontend's block lowering. -/
def lowerBlock (st : LowerState) : List Stmt →
    Except String (List _root_.Pontifex.Stmt × LowerState)
  | [] => .ok ([], st)
  | s :: rest => do
      let (s', st') ← lowerStmt st s
      let (rest', st'') ← lowerBlock st' rest
      return (s' :: rest', st'')

/-- Lower one statement. -/
def lowerStmt (st : LowerState) : Stmt →
    Except String (_root_.Pontifex.Stmt × LowerState)
  | .skip => .ok (.skip, st)
  | .assign v e => do
      -- The right-hand side is lowered *before* the target slot is allocated.
      let e' ← lowerExpr st e
      let (slot, st') := st.bindFresh v
      return (.assign slot e', st')
  | .ret es => do
      let es' ← es.mapM (lowerExpr st)
      return (.ret es', st)
  | .ite c t e => do
      let c' ← lowerCond st c
      let (thenStmts, stThen) ← lowerBlock st t
      -- The else branch restarts from the incoming environment but keeps the
      -- globally increasing slot counter.  An absent `else` is a `Skip`
      -- (matching the Python frontend).  This is written without a nested
      -- `do ... return` so that layout and early-return cannot swallow the phi
      -- construction below.
      let (elseStmt, stElse) ←
        match e with
        | [] => pure ((_root_.Pontifex.Stmt.skip), { stThen with env := st.env })
        | _ =>
            (lowerBlock { stThen with env := st.env } e).map
              (fun (stmts, st') => ((.seq stmts : _root_.Pontifex.Stmt), st'))
      let merged := assignedSorted (t ++ e)
      let (phis, env, next) ←
        merged.foldlM
          (fun (acc : List _root_.Pontifex.Phi × List (Nat × Nat) × Nat) v => do
            let thenSlot ← stThen.require v
            let elseSlot ← stElse.require v
            let (phis, env, next) := acc
            return (phis ++ [{ slot := next, lhs := thenSlot, rhs := elseSlot }],
              (v, next) :: env, next + 1))
          ([], st.env, stElse.next)
      return (.ite c' (.seq thenStmts) elseStmt phis,
        { env := env, next := next })
  | .whil c body => do
      let loopVars := assignedSorted body
      -- Allocate one header slot per loop variable, in sorted order.
      let (preSlots, headerSlots, headerEnv, next) ←
        loopVars.foldlM
          (fun (acc : List Nat × List Nat × List (Nat × Nat) × Nat) v => do
            let preSlot ← st.require v
            let (pre, headers, env, next) := acc
            return (pre ++ [preSlot], headers ++ [next], (v, next) :: env, next + 1))
          ([], [], st.env, st.next)
      let withHeaders : LowerState := { env := headerEnv, next := next }
      let c' ← lowerCond withHeaders c
      let (bodyStmts, stBody) ← lowerBlock withHeaders body
      let phis ←
        (loopVars.zip (headerSlots.zip preSlots)).mapM
          (fun (v, (header, pre)) => do
            let back ← stBody.require v
            return ({ slot := header, lhs := back, rhs := pre } : _root_.Pontifex.Phi))
      let init := (headerSlots.zip preSlots).map fun (header, pre) =>
        (_root_.Pontifex.Stmt.assign header (.slot pre) : _root_.Pontifex.Stmt)
      return (.seq (init ++ [.whil c' phis (.seq bodyStmts)]),
        { env := headerEnv, next := stBody.next })
end

/-- Lower a whole core source function, returning the IR body only.

    Parameter `i` occupies slot `i`; every other slot is allocated by the
    lowering.  Slot *names* are deliberately not produced: they are cosmetic and
    would force the kernel to evaluate string operations. -/
def lowerBody (f : Fn) : Except String _root_.Pontifex.Stmt := do
  let st : LowerState :=
    { env := f.paramIds.zipIdx.map (fun (v, i) => (v, i)), next := f.paramIds.length }
  let (body, _) ← lowerBlock st f.body
  return .seq body

end Pontifex.Source
