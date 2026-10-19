/-
  End-to-end links: Python source -> IR -> Lean code -> independent spec.

  `Generated.*.step_link` (emitted, proved by `rfl`) relates the compiled Lean
  function to the reference semantics of the checked IR.  The theorems below
  relate that semantics to the hand-written specification in
  `Pontifex.Spec.Mechanics`.  Together they form the verified chain for the
  straight-line examples:

      Python source  ~  IR semantics  =  Lean code  =  physics spec
      (tested only)     (rfl, emitted)  (rfl, here)   (definitions)

  The frontend translation is still unverified and checked by differential
  testing. Control-flow code now has generated, all-fuel certificates; worked
  uses are in `Pontifex.Examples.ControlFlow`. See docs/TRUST.md.
-/
import Pontifex.Generated.FreeFall
import Pontifex.Generated.HarmonicOscillator
import Pontifex.Spec.Mechanics

namespace Pontifex.Examples

open Pontifex

/-- The translated free-fall step is the specification's symplectic Euler step. -/
theorem freeFall_matches_spec (x v a dt : Rat) :
    Generated.FreeFall.step 64 x v a dt =
      some ((Spec.constantAccelStep a dt ⟨x, v⟩).x,
            (Spec.constantAccelStep a dt ⟨x, v⟩).v) :=
  rfl

/-- The translated harmonic-oscillator step is the specification's symplectic
    Euler step. -/
theorem harmonicOscillator_matches_spec (x v omega2 dt : Rat) :
    Generated.HarmonicOscillator.step 64 x v omega2 dt =
      some ((Spec.symplecticStep omega2 dt ⟨x, v⟩).x,
            (Spec.symplecticStep omega2 dt ⟨x, v⟩).v) :=
  rfl

/-- Combining the emitted linkage theorem with the spec link: the reference
    semantics of the checked IR is the physics spec. -/
theorem freeFall_ir_matches_spec (x v a dt : Rat) :
    (Outcome.toOption (Fn.run Ops.rat Generated.FreeFall.stepIR 64 [x, v, a, dt])).map
        (fun vs => (vs[0]!, vs[1]!)) =
      some ((Spec.constantAccelStep a dt ⟨x, v⟩).x,
            (Spec.constantAccelStep a dt ⟨x, v⟩).v) := by
  rw [← Generated.FreeFall.step_link]
  exact freeFall_matches_spec x v a dt

end Pontifex.Examples
