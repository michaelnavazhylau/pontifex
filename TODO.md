# TODO — implementation roadmap

Ordered by value per unit of risk, derived from the current trust report
(`docs/TRUST.md`) and the Charon/Aeneas review (`docs/RELATED_WORK.md`).

**Definition of done for every item below**

- `python scripts/generate.py && lake build && uv run pytest` all pass;
- generated artifacts are fresh (`python scripts/generate.py --check`);
- no new `sorry`, no new axioms beyond Lean's standard three, and no new
  `native_decide` outside explicitly labelled sample checks;
- `docs/TRUST.md` (status matrix, gaps) is updated in the same change;
- new behavior has a regression test that fails if the feature is reverted.

Sizes: **S** ≤ 1 day, **M** 2–4 days, **L** > 1 week.

---

## P0 — trust plumbing and test corpus — ✅ complete

Implemented in this repository: schema/config stamping with `#guard`, build-time
axiom auditing of every certificate, 57 committed rejection snapshots, and an
18-program triple-differential corpus.

### ✅ T1. Stamp the artifact configuration and guard it — **S**, low risk

**Why.** A generated proof silently weakens if a semantic flag changes (fuel
policy, future float mode, certificate mode). Charon solves this by embedding
`charon_version` and the `CliOpts` used in the artifact; Aeneas ships
`translation.json` metadata.

**Scope.**

- add `irVersion`, `fuelPolicy`, and `numericMode` constants to the Python IR
  module and to `PyVerif/Core/IR.lean`;
- emit `def pyverifConfig : PyVerif.Config := …` in every generated module;
- `#guard` the invariants the file depends on (e.g. `irVersion = 3`,
  `fuelPolicy = .structured`);
- extend `--check` so a stale version is a build failure.

**Acceptance.** Changing a constant without regenerating fails `lake build` with
a pointed message; `generate.py --check` detects the mismatch.

### ✅ T2. Axiom and `sorry` gate for generated modules — **S**, low risk

**Why.** We already audit axioms in one test; make it a build-level gate so a
future tactic cannot sneak `native_decide` into a linkage proof.

**Scope.**

- a generated `PyVerif/Audit.lean` that `#print axioms` every
  `<fn>_lowering`, `<fn>_link`, and `<fn>_compiled_link` (the generator knows
  the names);
- a pytest gate that fails if the printed axiom set is not a subset of
  `{propext, Classical.choice, Quot.sound}`;
- a scan that rejects `sorry`/`axiom` anywhere under `PyVerif/Generated/`.

**Acceptance.** Deliberately inserting `by native_decide` into a generated
linkage theorem fails the gate with the theorem name.

### ✅ T3. Rejection corpus with committed diagnostics — **S**, low risk

**Why.** Aeneas keeps `known-failure` tests with committed `.out` files so
“correctly rejects this” is a regression. We assert only that an error is
raised, not what it says.

**Scope.**

- `tests/rejections/<case>.py` for each unsupported construct and each subtle
  boundary (non-ASCII names, Unicode ordering, empty return, loop variable
  uninitialised, return in branch, annotation-only names, chained comparison,
  …);
- expected `.error` snapshots (exception class, message, line:column);
- a test that regenerates diagnostics and diffs them, plus a documented update
  command.

**Acceptance.** Corpus runs in `make check`; changing a diagnostic message
requires updating the snapshot deliberately.

### ✅ T4. Differential corpus and allowlist — **M**, low risk

**Why.** Four examples are too few to catch frontend regressions. Charon
translates the top 500 crates; Aeneas has 113 programs.

**Scope.**

- a `corpus/` directory of self-contained functions inside the subset
  (integrators, root finding, recurrence/economy-style loops, branch-heavy
  clamps, division-free numerics, nested loops);
- fixed-seed input vectors per program, run through CPython, the IR interpreter,
  and the Lean oracle (exact and binary64);
- a per-case allowlist file for known floating-point boundary cases, printed
  explicitly at the end of the run (no silent skips);
- `make corpus` target wired into CI.

**Acceptance.** ≥ 15 programs; every case either matches or is listed in the
allowlist with a reason; adding a corpus program requires no test code.

---

## P1 — semantics hardening — ✅ complete (schema 2)

Implemented: generic fuel refinement and total→partial specs; stable failed/stuck
outcomes; checked left-to-right division and short-circuiting; sparse uninitialized
slots; bit-authoritative Float transport/literals; explicit power semantics;
and a 100,000-pattern boundary corpus. See `docs/FLOAT_POLICY.md` and the current
trust matrix. The order is flat with bottom, not a lattice; only exhaustion is
below completed observations. Native arithmetic agreement is tested, not proved.
The worked fuel-free loop spec covers zero duration, not general termination.

T5 and T6 should land together: both reshape `Outcome`, the JSON encoding, and
the generated certificates. Doing them before language growth avoids rework.

### ✅ T5. Outcome lattice and fuel-refinement theorem — **M**, medium risk

**Why.** Fuel is currently threaded through every theorem, and `OutOfFuel` is
just an inert constructor. Aeneas makes divergence the bottom of an order and
derives total (`DWP`) and partial (`DWLP`) readings from one definition.

**Scope.**

- define `Outcome.Refines : Outcome α → Outcome α → Prop` with exhaustion below completed runs;
  failure and stuck are stable observations, not bottom;
- prove fuel monotonicity: if a run with `n` returned, a run with `m ≥ n`
  returns the same values; if it fell through, likewise;
- expose `spec`/`dspec`-style wrappers: total correctness (no exhaustion) and
  partial correctness (exhaustion allowed) with a `total → partial` lemma;
- port the loop certificate tests to quantify with the refinement lemma.

**Acceptance.** `exec_mono` and `total_to_partial` proved for `Ops α`; the
free-fall loop spec is restated without per-proof fuel plumbing; no certificate
depends on `native_decide`.

### ✅ T6. Exceptional and stuck outcomes — **M**, medium risk

**Why.** Lean's `Rat` division is total while Python raises; NaN/∞ and future
bounds checks have no home. Aeneas models `Result` failures explicitly, so specs
can say “fails iff”. Doing this now prevents widening `Option` later.

**Scope.**

- extend `Outcome` with `failed : Error → Outcome α` and `stuck : Outcome α`;
- `Error` starts with `divisionByZero` (plus `overflow` for Float power;
  `indexOutOfBounds` and `assertionFailure` are reserved);
- make `IR.div` checked: zero divisor produces `failed .divisionByZero` in both
  `Rat` and `Float` backends (with a documented `floatDiv` policy for NaN/∞);
- update the Python reference interpreter, JSON codec, Lean runner, emitter
  outcome plumbing, and certificates;
- document the semantics of each error kind and what is not modelled.

**Acceptance.** A theorem “`x / y` returns iff `y ≠ 0`” for exact rationals;
Python `ZeroDivisionError` maps to `failed`; fuel-boundary differential tests
cover both success and failure outcomes.

### ✅ T7. Close the Float boundary model — **M/L**, medium risk

**Why.** `ofRat` is not a correct-conversion proof for subnormals, the wire format
loses `-0.0`, and `**` semantics differ between exact and binary64 readings.
These are currently documented gaps, not tested boundaries.

**Scope.**

- exact literal path: emit float literals as original bits plus an exact rational;
  prove raw UInt64 representation round-trip, and test native/wire behavior on
  random patterns, zero signs, extremes, subnormals, and NaNs;
- bit-preserving input/output wire format (hex bits both ways, including `-0.0`);
- state and test policies for NaN, ±∞, overflow/underflow, and `-0.0 == 0.0`;
- define `**` consistently: use exact rational power or native Float.pow for literal natural
  exponents 0..8, with explicit overflow failure; reject other exponents;
- document which claims are proved vs tested vs out of scope.

**Acceptance.** A boundary corpus over ~10⁵ random doubles (values, ±0, NaN,
subnormals) compares CPython, IR interpreter, and Lean bit-for-bit, with an
explicit allowlist for unsupported operations.

---

## P2 — proof power and usability

### T8. Verified reflective `Rat` normaliser (`rat_ring`) — **L**, medium/high risk

**Why.** Core Lean has no `ring`; `rat_simp` cannot combine coefficients or
cancel opposing terms. This blocks the general modified-energy invariant and the
n-step free-fall closed form — the two most interesting domain theorems left.

**Scope.**

- reify goals over `+ - * neg`, numerals, and atoms;
- normalise to integer-coefficient monomials with a structurally recursive
  function (no `mergeSort`, no WF recursion — kernel-reducible);
- prove soundness (`eval (norm p) = eval p`) and close goals by `decide` on
  normal forms, or emit a proof term from a small certificate check;
- clear rational denominators with a nonzero proof that survives kernel
  reduction;
- register as `rat_ring`; keep `rat_simp` as the cheap fallback.

**Acceptance.** `symplecticStep` preserves `modifiedEnergy` for all rationals,
and the n-step free-fall position formula is proved; both with no new axioms.
Corruption tests confirm the normaliser rejects false identities.

### T9. Spec database and `pyverif_step` tactic — **M**, low risk

**Why.** Aeneas's usability comes from ~180 `@[step]` lemmas and `step*?`.
Our spec links are hand-written against generated definitions.

**Scope.**

- one registered lemma per IR operator and statement form (`evalE_add`,
  `evalE_mul`, `assign_sem`, `ite_sem`, …);
- a `pyverif_step` tactic that unfolds a translated function to arithmetic and
  discharges side conditions with `assumption`/`simp`/`omega` as configured;
- a `pyverif_step*?` script printer;
- rewrite `PyVerif/Examples/SpecLinks.lean` to use the tactic as the
  acceptance test;
- document when to use the tactic vs `rfl` linkage.

**Acceptance.** Existing spec links shrink to a few tactic lines; a new corpus
program’s spec is provable with the tactic without unfolding `exec`.

### T10. Two-tier arithmetic lemmas for Float — **L**, high risk

**Why.** Aeneas proves `*_equiv` (value level) and `*_bv_spec` (bit level) per
scalar op. Our generic `Ops` certificate proves identical structure, not IEEE
correctness.

**Scope.**

- state bit-level specs for `+ - * /` on finite doubles (round-to-nearest-even,
  no-NaN side conditions);
- state value-level corollaries and reuse them in the differential harness as
  the specification of the oracle;
- decide what to prove vs cite/assume about the hardware/Lean runtime.

**Acceptance.** `Float` add/sub/mul specs proved for finite operands; the
differential harness references the same statements; docs state precisely where
the hardware/compiler enters the trusted base.

---

## P3 — language growth (after P1)

### T11. Multi-exit returns with verified lowering — **M**

Design spike first: early `return` inside branches/loops currently rejected.
Options: (a) lower to an explicit result/flag slot and one exit; (b) introduce a
CFG. (a) preserves the structured IR and is likely enough for numerical code.

**Acceptance.** Early returns accepted, lowering certificate still `rfl`-checked,
semantics and tests updated; no certificate weakened.

### T12. State vectors / arrays — **L**

Model as `List Rat` with an explicit length and bounds checks producing
`failed .indexOutOfBounds` (Aeneas's `Slice`/`Vec` discipline). Requires T6.

**Acceptance.** A translated vector integrator with in-bounds accesses proved
safe; out-of-bounds produces the defined failure outcome.

### T13. Function calls — **L**

Start with white-box inlining of callables in the subset (no recursion); then
calls with summaries. Keep the lowering certificate compositional (per callee).

**Acceptance.** A two-function program where the caller’s certificate references
the callee’s, both `rfl`/kernel-checked.

### T14. Opacity lattice and verified-path assertion — **M**

Levels `Transparent / Modeled / Opaque / Invisible`, per-item metadata, Lean
`opaque` constants for the opaque level, and an assertion in each certificate
that no opaque node was reached on the verified path. Model after Charon's
four-level lattice and Aeneas's `is_opaque`.

**Acceptance.** A function calling an opaque helper still yields a certificate
for its own body; the generated proof states the opacity precondition explicitly.

### T15. Python integer semantics, `min`/`max`, conditional expressions — **M**

Python `int` is unbounded; the current IR only has exact rationals. Decide
whether to (a) model `int` as `ℤ` with explicit coercion points, or (b) keep
rejecting mixed int/float code. Add `min`/`max` and `a if c else b` only with
defined, tested numeric semantics.

**Acceptance.** A documented numeric tower with tests; no expression silently
changes meaning between exact and float modes.

---

## P4 — research options (not scheduled)

- **CFG-first IR** (ULLBC analogue) with a separately verified structuring pass
  and a `--unstructured` fallback. Unlocks irreducible control flow and makes
  loop structuring a proof obligation rather than a frontend assumption.
- **Termination without fuel**: a total-correctness layer (variant measures or
  `partial_fixpoint`-style definitions) for selected functions.
- **Broad Python exception model**: `KeyError`, `TypeError`, `OverflowError`,
  and user `raise`, with an effect/outcome discipline.
- **Aliasing/state**: references or arrays shared across functions; today the
  IR is strictly scalar and functional.

---

## Recommended sequence

1. ✅ **T1–T4** complete.
2. ✅ **T5–T7** complete. Computed-NaN exemptions are explicit and counted;
   native arithmetic proofs and a full Python numeric tower remain open.
4. **T8** (ring) to unlock the two remaining physics theorems; then **T9**
   (tactics) to make the library pleasant.
5. Grow the language only after the outcome model and corpus are stable:
   **T11 → T12 → T13 → T14 → T15**.

## Explicit non-goals (for now)

- general borrow checking, concurrency, or a heap model;
- full Python object semantics (classes, generators, exceptions hierarchy);
- a rustc-style pinned-compiler/Nix build matrix;
- proving the Python parser or the surface desugaring correct (they remain
  tested, not verified; the certified boundary starts at the emitted core AST).
