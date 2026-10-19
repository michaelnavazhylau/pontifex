/-
  Mathlib spike: how much do `ring`/`push_cast` simplify the spec layer?

  This file is deliberately outside `Pontifex/` so the default library and all
  generated certificates remain core-Lean-only. It imports the existing
  `Pontifex.Spec` definitions and re-proves selected theorems with Mathlib
  automation.

  Build with:
    lake build MathlibSpike

  It is not part of `defaultTargets` and must not be imported by generated code.
-/
import Mathlib.Tactic
import Pontifex.Spec.Mechanics
import Pontifex.Spec.FreeFall
import Pontifex.Audit.Command

open Pontifex.Spec

namespace Pontifex.Spec.MathlibSpike

/-! ## One-step algebra -/

theorem constantAccelStep_expanded (a dt x v : Rat) :
    constantAccelStep a dt ⟨x, v⟩ = ⟨x + v * dt + a * dt * dt, v + a * dt⟩ := by
  simp only [constantAccelStep]
  congr 1
  all_goals ring

theorem symplecticStep_expanded (omega2 dt x v : Rat) :
    symplecticStep omega2 dt ⟨x, v⟩ =
      ⟨x + v * dt - omega2 * x * dt * dt, v - omega2 * x * dt⟩ := by
  simp only [symplecticStep]
  congr 1
  all_goals ring

/-- The one-step position error, stated without clearing the factor `2`. -/
theorem constantAccelStep_position_error (a dt x v : Rat) :
    (constantAccelStep a dt ⟨x, v⟩).x - (constantAccelFlow a dt ⟨x, v⟩).x =
      (1 / 2 : Rat) * a * dt * dt := by
  simp only [constantAccelStep, constantAccelFlow]
  ring

/-- The general modified-energy invariant. -/
theorem symplecticStep_modifiedEnergy (omega2 dt x v : Rat) :
    modifiedEnergy omega2 dt (symplecticStep omega2 dt ⟨x, v⟩) =
      modifiedEnergy omega2 dt ⟨x, v⟩ := by
  simp only [modifiedEnergy, symplecticStep]
  ring

/-! ## Multi-step formulas -/

theorem repeatStep_velocity (n : Nat) (a dt x v : Rat) :
    (repeatStep n a dt ⟨x, v⟩).v = v + (n : Rat) * a * dt := by
  induction n with
  | zero =>
      rw [repeatStep_zero]
      ring
  | succ k ih =>
      rw [repeatStep_succ]
      dsimp only [constantAccelStep]
      rw [ih]
      push_cast
      ring

/-- Position after `n` steps, with the mathematically natural `1/2` coefficient. -/
theorem repeatStep_position (n : Nat) (a dt x v : Rat) :
    (repeatStep n a dt ⟨x, v⟩).x =
      x + (n : Rat) * v * dt +
        (1 / 2 : Rat) * a * dt * dt * (n : Rat) * ((n : Rat) + 1) := by
  induction n with
  | zero =>
      rw [repeatStep_zero]
      ring
  | succ k ih =>
      rw [repeatStep_succ]
      dsimp only [constantAccelStep]
      rw [ih, repeatStep_velocity]
      push_cast
      ring

/-- The same closed form with the denominator cleared, for comparison with the
    core-only `repeatStep_position_twice`. -/
theorem repeatStep_position_twice (n : Nat) (a dt x v : Rat) :
    2 * (repeatStep n a dt ⟨x, v⟩).x =
      2 * x + 2 * (n : Rat) * v * dt +
        a * dt * dt * (n : Rat) * ((n : Rat) + 1) := by
  rw [repeatStep_position]
  ring

/-! ## Trust check -/

#audit_axioms
  Pontifex.Spec.MathlibSpike.constantAccelStep_expanded
  Pontifex.Spec.MathlibSpike.symplecticStep_expanded
  Pontifex.Spec.MathlibSpike.constantAccelStep_position_error
  Pontifex.Spec.MathlibSpike.symplecticStep_modifiedEnergy
  Pontifex.Spec.MathlibSpike.repeatStep_velocity
  Pontifex.Spec.MathlibSpike.repeatStep_position
  Pontifex.Spec.MathlibSpike.repeatStep_position_twice

end Pontifex.Spec.MathlibSpike
