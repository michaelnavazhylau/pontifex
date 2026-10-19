/-
  `pontifex_step`: a small proof engine for translated programs.

  It unfolds the reference semantics (and the generated definition), splits
  symbolic branches, and tries the local decision procedures (`rfl`, `rat_ring`,
  `omega`, `simp`, assumptions, `decide`).  Unlike a global `simp` set, the
  rules are listed here explicitly so the behavior is reviewable and stable.

  `pontifex_step?` prints the simplified goal state and then attempts to finish;
  `pontifex_step*?` additionally prints usage guidance.  They are diagnostics:
  remaining goals are reported normally.

  Scope: this is an unfolding/proof-driver tactic. It does not invent facts,
  and every successful run is still checked by the kernel.
-/
import Pontifex.Core.Refinement
import Pontifex.Core.PolyTactic

namespace Pontifex

/-! ## Named evaluation rules (the tactic's rule database) -/

@[simp] theorem fromEval_ok {α β : Type} (x : β) (k : β → Outcome α) :
    Outcome.fromEval (.ok x) k = k x := rfl

@[simp] theorem fromEval_failed {α β : Type} (e : Error) (k : β → Outcome α) :
    Outcome.fromEval (.error (.failed e)) k = .failed e := rfl

@[simp] theorem fromEval_stuck {α β : Type} (k : β → Outcome α) :
    Outcome.fromEval (.error .stuck) k = .stuck := rfl

@[simp] theorem bindEnv_fellThrough {α : Type} (env : Env α) (k : Env α → Outcome α) :
    (Outcome.fellThrough env).bindEnv k = k env := rfl

@[simp] theorem bindEnv_returned {α : Type} (vs : List α) (k : Env α → Outcome α) :
    (Outcome.returned vs).bindEnv k = .returned vs := rfl

@[simp] theorem bindEnv_failed {α : Type} (e : Error) (k : Env α → Outcome α) :
    (Outcome.failed e).bindEnv k = .failed e := rfl

@[simp] theorem bindEnv_stuck {α : Type} (k : Env α → Outcome α) :
    (Outcome.stuck).bindEnv k = .stuck := rfl

@[simp] theorem bindEnv_outOfFuel {α : Type} (k : Env α → Outcome α) :
    (Outcome.outOfFuel).bindEnv k = .outOfFuel := rfl

end Pontifex

/-- Unfold, split, and finish with the local decision procedures.

    `pontifex_step [f, g]` additionally unfolds the named definitions (typically
    the generated `<fn>` and any specification functions). -/
macro "pontifex_step" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (simp [$ts,*, Pontifex.Fn.run, Pontifex.exec, Pontifex.evalS, Pontifex.evalV, Pontifex.Val.asScalar, Pontifex.evalC,
        Pontifex.evalScalars, Pontifex.indexVal, Pontifex.setVal, Pontifex.lenVal,
        Pontifex.evalScalars, Pontifex.indexVal, Pontifex.setVal, Pontifex.lenVal,
        Pontifex.readSlot, Pontifex.checkedDiv, Pontifex.mergePhis,
        Pontifex.applyBackEdges, Pontifex.Outcome.bindEnv,
        Pontifex.Outcome.fromEval, Pontifex.Outcome.toOption,
        Pontifex.Env.get?, Pontifex.Env.set, Pontifex.Ops.rat, Pontifex.Ops.float,
        Pontifex.Ops.binary64, Pontifex.Binary64.toFloat, Pontifex.Binary64.ofFloat]
     try (repeat' split)
     all_goals (try (simp_all [$ts,*, Pontifex.exec, Pontifex.evalS, Pontifex.evalV, Pontifex.Val.asScalar, Pontifex.evalC,
        Pontifex.evalScalars, Pontifex.indexVal, Pontifex.setVal, Pontifex.lenVal,
        Pontifex.readSlot, Pontifex.checkedDiv, Pontifex.mergePhis,
        Pontifex.applyBackEdges, Pontifex.Outcome.bindEnv,
        Pontifex.Outcome.fromEval, Pontifex.Env.get?, Pontifex.Env.set,
        Pontifex.Ops.rat, Pontifex.Ops.float, Pontifex.Ops.binary64]))
     all_goals first
       | rfl
       | rat_ring
       | omega
       | simp_all
       | assumption
       | decide))

macro "pontifex_step" : tactic =>
  `(tactic|
    (simp [Pontifex.Fn.run, Pontifex.exec, Pontifex.evalS, Pontifex.evalV, Pontifex.Val.asScalar, Pontifex.evalC,
        Pontifex.evalScalars, Pontifex.indexVal, Pontifex.setVal, Pontifex.lenVal,
        Pontifex.readSlot, Pontifex.checkedDiv, Pontifex.mergePhis,
        Pontifex.applyBackEdges, Pontifex.Outcome.bindEnv,
        Pontifex.Outcome.fromEval, Pontifex.Outcome.toOption,
        Pontifex.Env.get?, Pontifex.Env.set, Pontifex.Ops.rat, Pontifex.Ops.float,
        Pontifex.Ops.binary64, Pontifex.Binary64.toFloat, Pontifex.Binary64.ofFloat]
     try (repeat' split)
     all_goals (try (simp_all [Pontifex.exec, Pontifex.evalS, Pontifex.evalV, Pontifex.Val.asScalar, Pontifex.evalC,
        Pontifex.evalScalars, Pontifex.indexVal, Pontifex.setVal, Pontifex.lenVal,
        Pontifex.readSlot, Pontifex.checkedDiv, Pontifex.mergePhis,
        Pontifex.applyBackEdges, Pontifex.Outcome.bindEnv,
        Pontifex.Outcome.fromEval, Pontifex.Env.get?, Pontifex.Env.set,
        Pontifex.Ops.rat, Pontifex.Ops.float, Pontifex.Ops.binary64]))
     all_goals first
       | rfl
       | rat_ring
       | omega
       | simp_all
       | assumption
       | decide))

/-- Print the simplified state with extra definitions, then try to finish. -/
macro "pontifex_step?" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (simp [$ts,*, Pontifex.Fn.run, Pontifex.exec, Pontifex.evalS, Pontifex.evalV, Pontifex.Val.asScalar, Pontifex.evalC,
        Pontifex.evalScalars, Pontifex.indexVal, Pontifex.setVal, Pontifex.lenVal,
        Pontifex.evalScalars, Pontifex.indexVal, Pontifex.setVal, Pontifex.lenVal,
        Pontifex.readSlot, Pontifex.checkedDiv, Pontifex.mergePhis,
        Pontifex.applyBackEdges, Pontifex.Outcome.bindEnv,
        Pontifex.Outcome.fromEval, Pontifex.Outcome.toOption,
        Pontifex.Env.get?, Pontifex.Env.set, Pontifex.Ops.rat, Pontifex.Ops.float,
        Pontifex.Ops.binary64, Pontifex.Binary64.toFloat, Pontifex.Binary64.ofFloat]
     try (repeat' split)
     trace_state
     all_goals first
       | rfl
       | rat_ring
       | omega
       | simp_all
       | assumption
       | decide))

/-- Print the simplified state, then try to finish. -/
macro "pontifex_step?" : tactic =>
  `(tactic|
    (simp [Pontifex.Fn.run, Pontifex.exec, Pontifex.evalS, Pontifex.evalV, Pontifex.Val.asScalar, Pontifex.evalC,
        Pontifex.evalScalars, Pontifex.indexVal, Pontifex.setVal, Pontifex.lenVal,
        Pontifex.readSlot, Pontifex.checkedDiv, Pontifex.mergePhis,
        Pontifex.applyBackEdges, Pontifex.Outcome.bindEnv,
        Pontifex.Outcome.fromEval, Pontifex.Outcome.toOption,
        Pontifex.Env.get?, Pontifex.Env.set, Pontifex.Ops.rat, Pontifex.Ops.float,
        Pontifex.Ops.binary64, Pontifex.Binary64.toFloat, Pontifex.Binary64.ofFloat]
     try (repeat' split)
     trace_state
     all_goals first
       | rfl
       | rat_ring
       | omega
       | simp
       | assumption
       | decide))

/-- Script-printer variant with extra definitions and a usage hint. -/
macro "pontifex_step*?" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    (trace "pontifex_step*?: finish the state below with rfl / rat_ring / omega / simp_all / assumption"
     pontifex_step? [$ts,*]))

/-- Script-printer variant with a usage hint. -/
macro "pontifex_step*?" : tactic =>
  `(tactic|
    (trace "pontifex_step*?: finish the state below with rfl / rat_ring / omega / simp / assumption"
     pontifex_step?))
