import Pontifex.Core.Semantics

namespace Pontifex
namespace Outcome

/-- Flat information order. Only exhaustion is unknown. Failures and stuck
    states are completed observations, not approximations of successful runs.
    This is a partial order with bottom, not a lattice: distinct results have
    no common upper bound. -/
def Refines (a b : Outcome α) : Prop := a = .outOfFuel ∨ a = b

theorem refines_refl (a : Outcome α) : Refines a a := .inr rfl

theorem refines_trans {a b c : Outcome α} (h : Refines a b) (k : Refines b c) :
    Refines a c := by
  rcases h with h | h
  · exact .inl h
  · subst b; exact k

theorem refines_antisymm {a b : Outcome α} (h : Refines a b) (k : Refines b a) : a = b := by
  rcases h with h | h
  · rcases k with k | k
    · exact h.trans k.symm
    · exact k.symm
  · exact h

theorem refines_completed {a b : Outcome α} (h : Refines a b) (hn : a ≠ .outOfFuel) : b = a := by
  rcases h with h | h
  · exact False.elim (hn h)
  · exact h.symm

theorem bindEnv_mono {a b : Outcome α} {k l : Env α → Outcome α}
    (h : Refines a b) (hk : ∀ env, Refines (k env) (l env)) :
    Refines (a.bindEnv k) (b.bindEnv l) := by
  rcases h with h | h
  · subst a; exact .inl rfl
  · subst b
    cases a <;> first | exact hk _ | exact refines_refl _

theorem fromEval_mono (r : Eval β) {k l : β → Outcome α}
    (h : ∀ x, Refines (k x) (l x)) :
    Refines (fromEval r k) (fromEval r l) := by
  cases r with
  | ok x => exact h x
  | error f => cases f <;> exact refines_refl _

end Outcome

/-- More fuel preserves every completed observation, for every arithmetic
    backend and every IR statement (including malformed inputs). -/
theorem exec_mono (o : Ops α) [Inhabited α] {n m : Nat} (h : n ≤ m)
    (s : Stmt) (env : Env α) : Outcome.Refines (exec o n s env) (exec o m s env) := by
  induction n generalizing m s env with
  | zero => exact .inl rfl
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hm : n ≤ m := by omega
      cases s with
      | skip => exact Outcome.refines_refl _
      | assign i e => exact Outcome.refines_refl _
      | ret es => exact Outcome.refines_refl _
      | seq ss =>
        cases ss with
        | nil => exact Outcome.refines_refl _
        | cons head tail =>
          exact Outcome.bindEnv_mono (ih hm head env) (fun next => ih hm (.seq tail) next)
      | ite c t e phis =>
        apply Outcome.fromEval_mono
        intro b
        apply Outcome.bindEnv_mono
        · cases b <;> exact ih hm _ env
        · intro next; exact Outcome.refines_refl _
      | whil c phis body =>
        apply Outcome.fromEval_mono
        intro b
        cases b with
        | false => exact Outcome.refines_refl _
        | true =>
          apply Outcome.bindEnv_mono (ih hm body env)
          intro next
          apply Outcome.fromEval_mono
          intro header
          exact ih hm (.whil c phis body) header

theorem exec_completed_stable (o : Ops α) [Inhabited α] {n m : Nat} (h : n ≤ m)
    (s : Stmt) (env : Env α) (done : exec o n s env ≠ .outOfFuel) :
    exec o m s env = exec o n s env :=
  Outcome.refines_completed (exec_mono o h s env) done

/-- Total correctness: some finite run returns successfully with the postcondition.
    Failure, stuck, and exhaustion are not successful termination. -/
def TotalSpec (o : Ops α) [Inhabited α] (f : Fn) (args : List α)
    (post : List α → Prop) : Prop :=
  ∃ fuel values, f.run o fuel args = .returned values ∧ post values

/-- Partial correctness: every successful return has the postcondition, and no
    finite observation fails or gets stuck. Exhaustion remains permissible. -/
def PartialSpec (o : Ops α) [Inhabited α] (f : Fn) (args : List α)
    (post : List α → Prop) : Prop :=
  ∀ fuel, match f.run o fuel args with
    | .outOfFuel => True
    | .returned values => post values
    | _ => False

theorem total_to_partial (o : Ops α) [Inhabited α] (f : Fn) (args : List α)
    (post : List α → Prop) (h : TotalSpec o f args post) : PartialSpec o f args post := by
  rcases h with ⟨n, values, hn, hp⟩
  intro m
  by_cases le : n ≤ m
  · have done : exec o n f.body (args.map some) ≠ .outOfFuel := by
      change f.run o n args ≠ .outOfFuel
      rw [hn]; intro bad; cases bad
    have eq := exec_completed_stable o le f.body (args.map some) done
    change f.run o m args = f.run o n args at eq
    rw [eq, hn]; exact hp
  · have le' : m ≤ n := by omega
    have ref := exec_mono o le' f.body (args.map some)
    rcases ref with exhausted | same
    · change f.run o m args = .outOfFuel at exhausted
      simp only [exhausted]
    · change f.run o m args = f.run o n args at same
      rw [same, hn]; exact hp

end Pontifex
