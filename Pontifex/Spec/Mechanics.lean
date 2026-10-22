/-
  Pontifex.Spec.Mechanics

  Independent mathematical specification of the physics examples.

  Nothing in this file is generated: it is the "what the program is supposed to
  compute" side of the commuting square

      Python P --(pontifex)--> Lean code C
         |                        |
    Runs to result            Proved to satisfy
         |                        |
         +------> Spec <----------+

  Numeric domain: exact `Rat` (core Lean has no `ℝ`).  `Rat` is the exact
  stand-in for the reals; the operational `Float` reading lives in
  `Pontifex.Core.Ops` and is exercised by the differential harness instead of by
  these proofs.

  Proof-power note: `rat_simp` handles distribution and re-association;
  `rat_ring` is a kernel-checked integer-coefficient polynomial normalizer.
  General rational literal coefficients still require denominator clearing;
  see docs/TRUST.md.
-/
import Std
import Pontifex.Core.Semantics
import Pontifex.Tactic
import Pontifex.Core.PolyTactic

namespace Pontifex.Spec

/-- One-dimensional state (position, velocity). -/
structure State where
  x : Rat
  v : Rat
  deriving Repr

/-- Exact flow of constant acceleration `a` for time `dt`. -/
def constantAccelFlow (a dt : Rat) (s : State) : State where
  x := s.x + s.v * dt + (1 / 2 : Rat) * a * dt * dt
  v := s.v + a * dt

/-- One velocity-first (symplectic) Euler step of constant acceleration. -/
def constantAccelStep (a dt : Rat) (s : State) : State where
  v := s.v + a * dt
  x := s.x + (s.v + a * dt) * dt

/-- The integrator, written in expanded polynomial form.

    This is a real algebraic lemma (distribution plus re-association), and its
    right-hand side is the truncated Taylor step: `½a·dt²` is replaced by the
    full `a·dt²`, which is exactly the one-step position error of the
    velocity-first scheme. -/
theorem constantAccelStep_expanded (a dt x v : Rat) :
    constantAccelStep a dt ⟨x, v⟩ = ⟨x + v * dt + a * dt * dt, v + a * dt⟩ := by
  simp only [constantAccelStep]
  congr 1
  rat_simp

/-- The integrator's velocity is exact after one step. -/
theorem constantAccelStep_velocity_exact (a dt x v : Rat) :
    (constantAccelStep a dt ⟨x, v⟩).v = (constantAccelFlow a dt ⟨x, v⟩).v := rfl

/-- Zero acceleration leaves the velocity unchanged. -/
theorem constantAccelStep_zero_accel (dt x v : Rat) :
    (constantAccelStep 0 dt ⟨x, v⟩).v = v := by
  simp [constantAccelStep, Rat.add_zero]

/-! ### Harmonic oscillator -/

/-- One velocity-first Euler step of `x'' = -ω²x`. -/
def symplecticStep (omega2 dt : Rat) (s : State) : State where
  v := s.v - omega2 * s.x * dt
  x := s.x + (s.v - omega2 * s.x * dt) * dt

/-- Expanded form of the step (pure distribution/algebra). -/
theorem symplecticStep_expanded (omega2 dt x v : Rat) :
    symplecticStep omega2 dt ⟨x, v⟩ =
      ⟨x + v * dt - omega2 * x * dt * dt, v - omega2 * x * dt⟩ := by
  simp only [symplecticStep]
  congr 1
  rat_simp

/-- The modified energy exactly preserved by `symplecticStep`. -/
def modifiedEnergy (omega2 dt : Rat) (s : State) : Rat :=
  s.v * s.v + omega2 * s.x * s.x - omega2 * dt * s.x * s.v

/-- The symplectic Euler step exactly preserves the modified energy.
    This is the general polynomial identity; `rat_ring` normalizes both sides
    over `Int` coefficients and the kernel checks the result. -/
theorem symplecticStep_modifiedEnergy (omega2 dt x v : Rat) :
    modifiedEnergy omega2 dt (symplecticStep omega2 dt ⟨x, v⟩) =
      modifiedEnergy omega2 dt ⟨x, v⟩ := by
  simp only [modifiedEnergy, symplecticStep]
  rat_ring

/-- The previous finite grid (9 × 9 × 5 rational states).
    Its correctness now follows in the kernel from the universal invariant,
    without evaluating opaque rational arithmetic or trusting native code. -/
def modifiedEnergyGridOk : Bool :=
  (List.range 9).all fun xi =>
    (List.range 9).all fun vi =>
      (List.range 5).all fun di =>
        let x : Rat := (xi : Rat) - 4
        let v : Rat := (vi : Rat) - 4
        let dt : Rat := ((di : Rat) - 2) / 3
        let s : State := ⟨x, v⟩
        let s' := symplecticStep 7 dt s
        modifiedEnergy 7 dt s' == modifiedEnergy 7 dt s

theorem modifiedEnergyGridOk_eq_true : modifiedEnergyGridOk = true := by
  simp [modifiedEnergyGridOk, symplecticStep_modifiedEnergy]

end Pontifex.Spec
