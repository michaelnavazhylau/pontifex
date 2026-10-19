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

/-- A dense slot environment. Uninitialized/gap slots are none, not invented
    scalar defaults. An initialized slot i contains some value at index i. -/
abbrev Env (α : Type) := List (Option α)

namespace Env

/-- Total lookup: an unset slot is `none`. -/
def get? {α : Type} : Env α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => a
  | _ :: as, n + 1 => get? as n

/-- Overwriting update that extends the environment with uninitialized none slots when the
    slot has not been materialised yet.  Extension must be explicit: `List.set`
    silently drops out-of-range writes, which would make translated branch-local
    slots disappear. -/
def set {α : Type} [Inhabited α] : Env α → Nat → α → Env α
  | [], 0, v => [some v]
  | [], n + 1, v => none :: set [] n v
  | _ :: as, 0, v => some v :: as
  | a :: as, n + 1, v => a :: set as n v

end Env

/-- Observable completed outcomes are stable; only fuel exhaustion is incomplete. -/
inductive Outcome (α : Type) where
  | returned : List α → Outcome α
  | fellThrough : Env α → Outcome α
  | failed : Error → Outcome α
  | stuck
  | outOfFuel
  deriving Repr, DecidableEq

namespace Outcome

def toOption : Outcome α → Option (List α)
  | .returned vs => some vs
  | _ => none

/-- Continue only normal fall-through; preserve every other outcome unchanged. -/
def bindEnv (r : Outcome α) (k : Env α → Outcome α) : Outcome α :=
  match r with
  | .fellThrough env => k env
  | other => other

/-- Convert an expression/condition fault into its observable outcome. -/
def fromEval (r : Eval β) (k : β → Outcome α) : Outcome α :=
  match r with
  | .ok x => k x
  | .error (.failed e) => .failed e
  | .error .stuck => .stuck

end Outcome

/-- Reading an undefined slot is stuck, never an invented default value. -/
def readSlot (env : Env α) (i : Nat) : Eval α :=
  match env.get? i with
  | some x => .ok x
  | none => .error .stuck

/-- Python-style division: either sign of zero raises, including NaN / zero. -/
def checkedDiv (o : Ops α) (x y : α) : Eval α :=
  if o.isZero y then .error (.failed .divisionByZero) else .ok (o.div x y)

/-- Left-to-right scalar expression evaluation with explicit failures. -/
def evalE (o : Ops α) (env : Env α) : Expr → Eval α
  | .slot i => readSlot env i
  | .lit q => .ok (o.ofRat q)
  | .floatLit q bits => .ok (o.ofFloatBits q bits)
  | .pow a n => do o.pow (← evalE o env a) n
  | .bin op a b => do
      let x ← evalE o env a
      let y ← evalE o env b
      match op with
      | .add => return o.add x y
      | .sub => return o.sub x y
      | .mul => return o.mul x y
      | .div => checkedDiv o x y
  | .un op a => do
      let x ← evalE o env a
      match op with
      | .neg => return o.neg x
      | .abs => return o.abs x

/-- Conditions short-circuit, including their failure behavior. -/
def evalC (o : Ops α) (env : Env α) : Cond → Eval Bool
  | .cmp op a b => do
      let x ← evalE o env a
      let y ← evalE o env b
      return match op with
      | .lt => o.lt x y
      | .le => o.le x y
      | .gt => o.gt x y
      | .ge => o.ge x y
      | .eq => o.eq x y
      | .ne => o.ne x y
  | .and a b => do
      if ← evalC o env a then evalC o env b else return false
  | .or a b => do
      if ← evalC o env a then return true else evalC o env b
  | .not a => do return !(← evalC o env a)
  | .const b => .ok b

/-- Parallel phi copies read the original snapshot, not the accumulator. -/
def mergePhis [Inhabited α] (b : Bool) (phis : List Phi) (env : Env α) : Eval (Env α) :=
  phis.foldlM (fun acc p => do
    let x ← readSlot env (if b then p.lhs else p.rhs)
    return acc.set p.slot x) env

def applyBackEdges [Inhabited α] (phis : List Phi) (env : Env α) : Eval (Env α) :=
  phis.foldlM (fun acc p => do
    let x ← readSlot env p.lhs
    return acc.set p.slot x) env

/-- Fuel is structured depth: a cons/if/while gives one less level to each
    child/back edge, not a globally shared step counter. A false loop still
    requires positive fuel. Failures and stuck states propagate unchanged. -/
def exec (o : Ops α) [Inhabited α] : Nat → Stmt → Env α → Outcome α
  | 0, _, _ => .outOfFuel
  | _ + 1, .skip, env => .fellThrough env
  | _ + 1, .assign i e, env =>
      Outcome.fromEval (evalE o env e) (fun x => .fellThrough (env.set i x))
  | _ + 1, .seq [], env => .fellThrough env
  | fuel + 1, .seq (s :: rest), env =>
      (exec o fuel s env).bindEnv (fun next => exec o fuel (.seq rest) next)
  | fuel + 1, .ite c t e phis, env =>
      Outcome.fromEval (evalC o env c) fun b =>
        (if b then exec o fuel t env else exec o fuel e env).bindEnv fun next =>
          Outcome.fromEval (mergePhis b phis next) Outcome.fellThrough
  | fuel + 1, .whil c phis body, env =>
      Outcome.fromEval (evalC o env c) fun b =>
        if b then
          (exec o fuel body env).bindEnv fun next =>
            Outcome.fromEval (applyBackEdges phis next) fun header =>
              exec o fuel (.whil c phis body) header
        else .fellThrough env
  | _ + 1, .ret es, env =>
      Outcome.fromEval (es.mapM (evalE o env)) Outcome.returned

def Fn.run (o : Ops α) [Inhabited α] (f : Fn) (fuel : Nat) (args : List α) : Outcome α :=
  exec o fuel f.body (args.map some)

end PyVerif
