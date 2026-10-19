# `pyverif_step`: proving properties of translated programs

`PyVerif/Step.lean` provides a small, reviewable proof driver for generated
definitions. It does not add assumptions: every successful run is a
kernel-checked proof.

```lean
import PyVerif.Step
import PyVerif.Generated.FreeFall

example (x v a dt : Rat) :
    (Generated.FreeFall.step 64 x v a dt).map Prod.snd = some (v + a * dt) := by
  pyverif_step [Generated.FreeFall.step]
```

## What it does

1. `simp` with an explicit rule list: the semantics (`Fn.run`, `exec`, `evalE`,
   `evalC`, `readSlot`, `checkedDiv`, phi helpers, `Outcome.bindEnv/fromEval/
   toOption`, `Env.get?/set`), both arithmetic backends, and any definitions
   passed in brackets.
2. `split` on symbolic branches.
3. Try, per goal: `rfl`, `rat_ring`, `omega`, `simp_all`, an assumption, or
   `decide`.

The named evaluation rules (`fromEval_ok`, `fromEval_failed`,
`bindEnv_fellThrough`, …) live in `PyVerif/Step.lean`. There is no custom simp
extension in core Lean; extending the tactic means adding lemmas to that file
and the explicit list in the macro.

## Diagnostics

* `pyverif_step? [defs]` prints the simplified state and then tries to finish.
* `pyverif_step*? [defs]` adds a hint about the finishing tactics.

Remaining goals are reported normally; these variants never silently admit a
goal.

## Scope and limits

* Straight-line code and simple branches work well.
* For deeply nested `if`/`while`, the outer `match` may need a preceding
  `by_cases` on the branch condition; `split` chooses the first match/if.
* Loop properties generally need an invariant and induction on fuel; use the
  all-fuel certificates (`<fn>_compiled_link`) and `exec_mono` instead of
  enumerating fuel.
* Arithmetic beyond integer polynomials may need `rat_ring`'s denominator
  clearing step or a hand-written lemma.

## Worked proofs

`PyVerif/Examples/StepDemo.lean` proves the position and velocity components of
the free-fall and harmonic-oscillator steps with one tactic line each. These
theorems are included in the build-time axiom audit.
