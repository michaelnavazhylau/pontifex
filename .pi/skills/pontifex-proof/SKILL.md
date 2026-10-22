---
name: pontifex-proof
description: Prove or debug Pontifex Lean specifications, certificate linkage, fuel refinements, and polynomial identities. Use before unfolding generated semantics or increasing proof budgets.
---

# Reuse Pontifex's proof routes

Repository root is `../../..` from this skill directory. Run lookup there:
`uv run --locked --no-sync python scripts/pontifex_workflow.py lookup --feature proofs`.
Read only the relevant example and policy section.

## Choose the proof shape first

| Goal shape | First route | Worked reference (repository-relative) |
|---|---|---|
| Component of a direct straight-line definition | `pontifex_step [definition]` | `Pontifex/Examples/StepDemo.lean` |
| Public wrapper emitted as certified blocks | Unfold the wrapper; rewrite using `_compiled_link`; reason about full outcomes | `Pontifex/Examples/FailuresAndRefinement.lean`, `ControlFlow.lean` |
| Integer-coefficient polynomial identity | Unfold just the spec, then `rat_ring` | `Pontifex/Spec/Mechanics.lean`, `FreeFall.lean` |
| Loop property | State an invariant; induction on fuel or iteration count | `Pontifex/Core/Refinement.lean`, `Pontifex/Spec/FreeFall.lean` |
| Stable completed observation at larger fuel | `exec_mono`, `exec_completed_stable` | `Pontifex/Core/Refinement.lean` |
| Total implies partial specification | `total_to_partial` | `Pontifex/Examples/FailuresAndRefinement.lean` |
| Caller lowering with helpers | `_program_lowering` composes callee evidence | `docs/CALLS.md` |

Read `docs/STEP_TACTIC.md` for tactic scope and trace variants. The tactic's rule
list is explicit in `Pontifex/Step.lean`; there is no hidden global spec database.

## Avoid expensive dead ends

- `rat_ring` normalizes integer-coefficient polynomials. Clear rational literal
  denominators with valid nonzero evidence first. Division by variables and
  non-polynomial terms are atoms, not automatically solved algebra.
- Do not repeatedly unfold `exec` at a large literal fuel. Certified wrapper
  projections (`vs[i]!`) are not generally direct `pontifex_step` goals.
- For symbolic branches, expose the intended condition with `by_cases` when
  needed; deeply nested loops require invariants, not more simplifier retries.
- Before increasing heartbeats, inspect reduction shape and run the long-block
  certificate regression in `python/tests/test_certificates.py`. The direct
  mutual recursor in `Pontifex/Core/Lower.lean` intentionally avoids exponential
  `brecOn` reduction. Its `noncomputable` status is deliberate proof-only code.

## Preserve what the theorem actually says

- Direct infallible linkage is at a selected literal fuel; certified-block
  linkage quantifies over all fuel, environments, and arithmetic backends.
- Preserve `returned`, `fellThrough`, `failed`, `stuck`, and `outOfFuel`.
  More fuel preserves completed failures too. Exhaustion is not divergence;
  partial correctness does not prove termination.
- Tier/component Float lemmas are not native-rounding proofs. Source/IR
  agreement with a reference lowering is not universal Python preservation.
- Never use `sorry`, new axioms, or `native_decide` to close certificates.
  Native sample theorems belong only in the explicit `PontifexNativeTests`
  target (`NativeTests.lean`), never in certificates or their imports.

Use `python/tests/lean_helpers.py` for new kernel checks. Audit new handwritten
spec theorems via `scripts/generate.py`'s `AUDIT_EXAMPLES`, regenerate explicitly,
and include a false/corrupted case when extending proof automation. Validate
with focused `proofs`/`lowering` features, then full project gates. Report the
actual theorem scope and any remaining proof obligation.
