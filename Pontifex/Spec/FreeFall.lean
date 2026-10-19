/-
  Exact rational free-fall integration: velocity and position after `n` steps.

  The position formula is stated with the factor 2 cleared so every coefficient
  is an integer; `rat_ring` then proves the induction step without a `ring`
  tactic or Mathlib.
-/
import Pontifex.Spec.Mechanics
import Pontifex.Core.PolyTactic

namespace Pontifex.Spec

/-- `n` applications of the one-step constant-acceleration integrator. -/
def repeatStep (n : Nat) (a dt : Rat) (s : State) : State :=
  Nat.rec s (fun _ s' => constantAccelStep a dt s') n

theorem repeatStep_zero (a dt : Rat) (s : State) : repeatStep 0 a dt s = s := rfl

theorem repeatStep_succ (n : Nat) (a dt : Rat) (s : State) :
    repeatStep (n + 1) a dt s = constantAccelStep a dt (repeatStep n a dt s) := rfl

/-! ## Nat casts, via the `Int` casts available in core -/

theorem ratNatCast_add (a b : Nat) : ((a + b : Nat) : Rat) = (a : Rat) + (b : Rat) := by
  rw [← Rat.intCast_natCast (a + b), Int.natCast_add, Rat.intCast_add,
    Rat.intCast_natCast a, Rat.intCast_natCast b]

theorem ratNatCast_mul (a b : Nat) : ((a * b : Nat) : Rat) = (a : Rat) * (b : Rat) := by
  rw [← Rat.intCast_natCast (a * b), Int.natCast_mul, Rat.intCast_mul,
    Rat.intCast_natCast a, Rat.intCast_natCast b]

theorem ratNatCast_one : ((1 : Nat) : Rat) = 1 := by
  rw [← Rat.intCast_natCast 1, Int.natCast_one, Rat.intCast_one]

theorem ratNatCast_succ (n : Nat) : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
  rw [ratNatCast_add, ratNatCast_one]

/-- Velocity after `n` exact rational steps. -/
theorem repeatStep_velocity (n : Nat) (a dt x v : Rat) :
    (repeatStep n a dt ⟨x, v⟩).v = v + (n : Rat) * a * dt := by
  induction n with
  | zero => rw [repeatStep_zero]; simp [Rat.add_zero]
  | succ k ih =>
    rw [repeatStep_succ]
    dsimp only [constantAccelStep]
    rw [ih, ratNatCast_succ]
    rat_ring

/-- Position after `n` exact rational steps, with the factor 2 cleared. -/
theorem repeatStep_position_twice (n : Nat) (a dt x v : Rat) :
    2 * (repeatStep n a dt ⟨x, v⟩).x =
      2 * x + 2 * (n : Rat) * v * dt + a * dt * dt * (n : Rat) * ((n : Rat) + 1) := by
  induction n with
  | zero => rw [repeatStep_zero]; simp [Rat.add_zero]
  | succ k ih =>
    rw [repeatStep_succ]
    dsimp only [constantAccelStep]
    rw [repeatStep_velocity, Rat.mul_add, ih, ratNatCast_succ]
    rat_ring

end Pontifex.Spec
