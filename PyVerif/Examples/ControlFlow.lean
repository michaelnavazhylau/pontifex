/- Worked uses of the generated certificates: a physics safety property and
   backend-independent exhaustion preservation. No native_decide is used. -/
import PyVerif.Generated.ClampedStep
import PyVerif.Generated.FreeFallLoop

namespace PyVerif.Examples

/-- The position-clamping integrator implements its independent piecewise spec.
    This connects a branching program to a useful property, not just its IR. -/
theorem clampedStep_matches_spec (x v dt limit : Rat) :
    Generated.ClampedStep.step 64 x v dt limit =
      some (if x + v * dt > limit then (limit, 0) else (x + v * dt, v)) := by
  rw [Generated.ClampedStep.step_link]
  by_cases h : x + v * dt > limit <;>
    simp [Generated.ClampedStep.stepIR, Fn.run, exec, evalE, evalC,
      Ops.rat, Env.get?, Env.set, readSlot, mergePhis,
      Outcome.fromEval, Outcome.bindEnv, Outcome.toOption, bind, pure,
      Except.bind, Except.pure, h]

/-- Instantiating the parametric certificate at Float needs no floating-point
    computation or algebraic assumptions in the proof. -/
theorem freeFallLoop_float_link (fuel : Nat) (args : List Float) :
    Generated.FreeFallLoop.simulateCompiled Ops.float fuel args =
      Fn.run Ops.float Generated.FreeFallLoop.simulateIR fuel args :=
  Generated.FreeFallLoop.simulate_compiled_link Ops.float fuel args

/-- A zero budget is preserved as a full outcome, not merely collapsed to none. -/
theorem freeFallLoop_zero_budget (ops : Ops α) [Inhabited α] (args : List α) :
    Generated.FreeFallLoop.simulateCompiled ops 0 args = .outOfFuel := rfl

end PyVerif.Examples
