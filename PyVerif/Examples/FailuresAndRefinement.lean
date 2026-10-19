import PyVerif.Core.Refinement
import PyVerif.Generated.FreeFallLoop

namespace PyVerif.Examples

/-- Division succeeds exactly when its rational divisor is nonzero. -/
theorem rat_div_success_iff (x y : Rat) :
    (∃ z, checkedDiv Ops.rat x y = .ok z) ↔ y ≠ 0 := by
  by_cases h : y = 0 <;> simp [checkedDiv, Ops.rat, h]

theorem rat_div_failed_iff (x y : Rat) :
    checkedDiv Ops.rat x y = .error (.failed .divisionByZero) ↔ y = 0 := by
  by_cases h : y = 0 <;> simp [checkedDiv, Ops.rat, h]

/-- Refinement specializes to generated code for all numeric backends, without
    floating-point evaluation, success-only projections, or hidden fuel bounds. -/
theorem freeFallLoop_compiled_mono (ops : Ops α) [Inhabited α]
    (n m : Nat) (h : n ≤ m) (args : List α) :
    Outcome.Refines
      (Generated.FreeFallLoop.simulateCompiled ops n args)
      (Generated.FreeFallLoop.simulateCompiled ops m args) := by
  rw [Generated.FreeFallLoop.simulate_compiled_link,
      Generated.FreeFallLoop.simulate_compiled_link]
  exact exec_mono ops h _ (args.map some)

/-- A fuel-free total spec for the zero-duration loop: it returns its initial
    state, for arbitrary position, velocity, acceleration, and step size. -/
theorem freeFallLoop_zero_time_total (x v a dt : Rat) :
    TotalSpec Ops.rat Generated.FreeFallLoop.simulateIR [0, x, v, a, dt]
      (fun values => values = [x, v]) := by
  refine ⟨32, [x, v], ?_, rfl⟩
  simp [Fn.run, Generated.FreeFallLoop.simulateIR, exec, evalE, evalC, Ops.rat,
    readSlot, Env.get?, Env.set, Outcome.fromEval, Outcome.bindEnv,
    bind, pure, Except.bind, Except.pure]

/-- The same property holds for every observation, without a fuel parameter
    in the public specification. -/
theorem freeFallLoop_zero_time_partial (x v a dt : Rat) :
    PartialSpec Ops.rat Generated.FreeFallLoop.simulateIR [0, x, v, a, dt]
      (fun values => values = [x, v]) :=
  total_to_partial _ _ _ _ (freeFallLoop_zero_time_total x v a dt)

end PyVerif.Examples
