/-
  PyVerif.Core.Semantics

  The reference (big-step, environment-based) semantics of the core language.

  These definitions are the trusted reference reading of the IR. Generated
  control-flow code is checked against them by per-block certificates, including
  induction on fuel for loops. This does not prove the frontend or these
  definitions faithful to Python; that remains a separate obligation.

  Partiality: `while` loops are interpreted with an explicit fuel argument, so
  the semantics is total (`outOfFuel` is a distinguished outcome).  Generated
  Lean code is likewise fuel-parameterised; this makes the linkage theorem
  between generated code and this semantics provable for *all* fuels instead of
  requiring a termination proof of the source program.
-/
import Std
import PyVerif.Core.IR
import PyVerif.Core.Ops

set_option linter.unusedVariables false

namespace PyVerif

/-- A slot environment is a dense list: slot `i` lives at index `i`. -/
abbrev Env (α : Type) := List α

namespace Env

/-- Total lookup: an unset slot is `none`. -/
def get? {α : Type} : Env α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n + 1 => get? as n

/-- Lookup with a default; `default` is unreachable for well-formed programs
    (the frontend guarantees that every referenced slot is assigned first). -/
def get! {α : Type} [Inhabited α] (e : Env α) (i : Nat) : α :=
  (get? e i).getD default

/-- Overwriting update that *extends* the environment with `default` when the
    slot has not been materialised yet.  Extension must be explicit: `List.set`
    silently drops out-of-range writes, which would make translated branch-local
    slots disappear. -/
def set {α : Type} [Inhabited α] : Env α → Nat → α → Env α
  | [], 0, v => [v]
  | [], n + 1, v => default :: set [] n v
  | _ :: as, 0, v => v :: as
  | a :: as, n + 1, v => a :: set as n v

end Env

/-- Outcome of executing a statement. -/
inductive Outcome (α : Type) where
  /-- The statement executed `ret`, producing the returned scalars. -/
  | returned : List α → Outcome α
  /-- The statement completed without returning, leaving this environment. -/
  | fellThrough : Env α → Outcome α
  /-- The budget was exhausted (possibly even in a straight-line block).
      This is not a proof that the source program diverges. -/
  | outOfFuel : Outcome α
  deriving Repr, DecidableEq

namespace Outcome

/-- Forget which way a program terminated, keeping only returned values. -/
def toOption {α : Type} : Outcome α → Option (List α)
  | .returned vs => some vs
  | .fellThrough _ => none
  | .outOfFuel => none

end Outcome

/-- Scalar expression evaluation. -/
def evalE (o : Ops α) [Inhabited α] (env : Env α) : Expr → α
  | .slot i => env.get! i
  | .lit q => o.ofRat q
  | .bin op a b =>
      let x := evalE o env a
      let y := evalE o env b
      match op with
      | .add => o.add x y
      | .sub => o.sub x y
      | .mul => o.mul x y
      | .div => o.div x y
  | .un op a =>
      let x := evalE o env a
      match op with
      | .neg => o.neg x
      | .abs => o.abs x

/-- Boolean expression evaluation (with short-circuiting `and`/`or`). -/
def evalC (o : Ops α) [Inhabited α] (env : Env α) : Cond → Bool
  | .cmp op a b =>
      let x := evalE o env a
      let y := evalE o env b
      match op with
      | .lt => o.lt x y
      | .le => o.le x y
      | .gt => o.gt x y
      | .ge => o.ge x y
      | .eq => o.eq x y
      | .ne => o.ne x y
  | .and a b => evalC o env a && evalC o env b
  | .or a b => evalC o env a || evalC o env b
  | .not a => !evalC o env a
  | .const b => b

/-- Apply the phis of an `if`: read `lhs` from the then-environment or `rhs` from
    the else-environment, depending on which branch was taken. -/
def mergePhis [Inhabited α] (b : Bool) (phis : List Phi) (env : Env α) : Env α :=
  phis.foldl (fun acc p => acc.set p.slot (env.get! (if b then p.lhs else p.rhs))) env

/-- Set the loop-header slots from the body's back-edge slots. -/
def applyBackEdges [Inhabited α] (phis : List Phi) (env : Env α) : Env α :=
  phis.foldl (fun acc p => acc.set p.slot (env.get! p.lhs)) env


/-- Statement execution with a step budget.

    The budget is consumed by every statement and by every loop iteration, so
    the recursion is *structural on the fuel argument*.  This is a deliberate
    design choice:

    * the semantics stays total, so no source program needs a termination proof
      before it can be discussed;
    * `exec` is a plain structural recursion, which the kernel can evaluate for
      literal fuel budgets.  That is what makes the `rfl` linkage checks between
      emitted Lean code and this semantics possible;
    * loop-friendly theorems are proved by induction on the fuel argument.

    Fuel bounds both loop iterations and structured execution depth, not total
    instruction count. A sequence cons consumes one level, giving the remaining
    budget to BOTH its head and its tail. An if consumes one level before its
    chosen branch; a while consumes one level before BOTH its body and back edge.
    Consequently even a false loop condition needs positive fuel. -/
def exec (o : Ops α) [Inhabited α] : Nat → Stmt → Env α → Outcome α
  | 0, _, _ => .outOfFuel
  | fuel + 1, .skip, env => .fellThrough env
  | fuel + 1, .assign i e, env => .fellThrough (env.set i (evalE o env e))
  | fuel + 1, .seq [], env => .fellThrough env
  | fuel + 1, .seq (s :: rest), env =>
      match exec o fuel s env with
      | .fellThrough env' => exec o fuel (.seq rest) env'
      | other => other
  | fuel + 1, .ite c t e phis, env =>
      let b := evalC o env c
      match (if b then exec o fuel t env else exec o fuel e env) with
      | .fellThrough env' => .fellThrough (mergePhis b phis env')
      | other => other
  | fuel + 1, .whil c phis body, env =>
      -- The header slots are initialised by explicit assignments emitted before
      -- the loop (see `Phi.rhs`), so entering a loop never rewrites them again.
      -- Re-initialising here would discard the loop-carried values on exit.
      if evalC o env c then
        match exec o fuel body env with
        | .fellThrough env' => exec o fuel (.whil c phis body) (applyBackEdges phis env')
        | other => other
      else .fellThrough env
  | fuel + 1, .ret es, env => .returned (es.map (evalE o env))

/-- Run a translated function on arguments. -/
def Fn.run (o : Ops α) [Inhabited α] (f : Fn) (fuel : Nat) (args : List α) :
    Outcome α :=
  exec o fuel f.body args

end PyVerif
