/-
  Worked uses of `pontifex_step`: prove properties of a generated function with
  one tactic line, without manually unfolding `Fn.run`/`exec`.
-/
import Pontifex.Step
import Pontifex.Generated.FreeFall
import Pontifex.Generated.HarmonicOscillator

namespace Pontifex.Examples

/-- The translated free-fall step's position component, in closed form. -/
theorem freeFall_step_position (x v a dt : Rat) :
    (Generated.FreeFall.step 64 x v a dt).map Prod.fst =
      some (x + (v + a * dt) * dt) := by
  pontifex_step [Generated.FreeFall.step]

/-- The translated free-fall step's velocity component, in closed form. -/
theorem freeFall_step_velocity (x v a dt : Rat) :
    (Generated.FreeFall.step 64 x v a dt).map Prod.snd =
      some (v + a * dt) := by
  pontifex_step [Generated.FreeFall.step]

/-- The translated harmonic-oscillator step's velocity component. -/
theorem harmonicOscillator_step_velocity (x v omega2 dt : Rat) :
    (Generated.HarmonicOscillator.step 64 x v omega2 dt).map Prod.snd =
      some (v - omega2 * x * dt) := by
  pontifex_step [Generated.HarmonicOscillator.step]

end Pontifex.Examples
