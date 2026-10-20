# TODO — implementation roadmap

> GitHub tracking: epic [#15](https://github.com/michaelnavazhylau/pontifex/issues/15);
> P3 issues [#1–#6](https://github.com/michaelnavazhylau/pontifex/milestone/1)
> ([#1](https://github.com/michaelnavazhylau/pontifex/issues/1) and
> [#4](https://github.com/michaelnavazhylau/pontifex/issues/4) implemented);
> P4 issues [#7–#14](https://github.com/michaelnavazhylau/pontifex/milestone/2);
> tooling issue [#16](https://github.com/michaelnavazhylau/pontifex/issues/16)
> ([milestone #3](https://github.com/michaelnavazhylau/pontifex/milestone/3)).

Ordered by value per unit of risk, derived from the current trust report
(`docs/TRUST.md`) and the Charon/Aeneas review (`docs/RELATED_WORK.md`).

**Definition of done for every item below**

- `make check` passes: generated-artifact freshness, axiom audit, rejection
  snapshots, differential corpus, Float boundary corpus, and the pytest suite;
- no new `sorry`, no new axioms beyond Lean's standard three, and no new
  `native_decide` outside explicitly labelled sample checks;
- `docs/TRUST.md` (status matrix, gaps) is updated in the same change;
- new behavior has a regression test that fails if the feature is reverted.

Sizes: **S** ≤ 1 day, **M** 2–4 days, **L** > 1 week.

---

## P0 — trust plumbing and test corpus — ✅ complete

Implemented in this repository: schema/config stamping with `#guard`, build-time
axiom auditing of every certificate, 91 committed rejection snapshots, and a
32-program triple-differential corpus (both corpora have grown since P0 closed;
see the current counts in [README](README.md#validation)).

### ✅ T1. Stamp the artifact configuration and guard it — **S**, low risk

**Why.** A generated proof silently weakens if a semantic flag changes (fuel
policy, future float mode, certificate mode). Charon solves this by embedding
`charon_version` and the `CliOpts` used in the artifact; Aeneas ships
`translation.json` metadata.

**Scope.**

- add `irVersion`, `fuelPolicy`, and `numericMode` constants to the Python IR
  module and to `Pontifex/Core/IR.lean`;
- emit `def pontifexConfig : Pontifex.Config := …` in every generated module;
- `#guard` the invariants the file depends on (e.g. `irVersion = 4`,
  `fuelPolicy = .structured`);
- extend `--check` so a stale version is a build failure.

**Acceptance.** Changing a constant without regenerating fails `lake build` with
a pointed message; `generate.py --check` detects the mismatch.

### ✅ T2. Axiom and `sorry` gate for generated modules — **S**, low risk

**Why.** We already audit axioms in one test; make it a build-level gate so a
future tactic cannot sneak `native_decide` into a linkage proof.

**Scope.**

- a generated `Pontifex/Audit.lean` that `#print axioms` every
  `<fn>_lowering`, `<fn>_link`, and `<fn>_compiled_link` (the generator knows
  the names);
- a pytest gate that fails if the printed axiom set is not a subset of
  `{propext, Classical.choice, Quot.sound}`;
- a scan that rejects `sorry`/`axiom` anywhere under `Pontifex/Generated/`.

**Acceptance.** Deliberately inserting `by native_decide` into a generated
linkage theorem fails the gate with the theorem name.

### ✅ T3. Rejection corpus with committed diagnostics — **S**, low risk

**Why.** Aeneas keeps `known-failure` tests with committed `.out` files so
“correctly rejects this” is a regression. We assert only that an error is
raised, not what it says.

**Scope.**

- `tests/rejections/cases/<case>.py` for each unsupported construct and each subtle
  boundary (non-ASCII names, Unicode ordering, empty return, loop variable
  uninitialised, unreachable code after a return, mismatched return arity,
  array aliasing/kind changes, annotation-only names, chained comparison, …);
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
  clamps, division-free numerics, nested loops, and array/vector programs);
- fixed-seed input vectors per program, run through CPython, the IR interpreter,
  and the Lean oracle (exact and binary64);
- a per-case allowlist file for known floating-point boundary cases, printed
  explicitly at the end of the run (no silent skips);
- `make corpus` target wired into `make check`.

**Acceptance.** ≥ 15 programs; every case either matches or is listed in the
allowlist with a reason; adding a corpus program requires no test code.

---

## P1 — semantics hardening — ✅ complete (landed in schema 2; current schema 4)

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
  `indexOutOfBounds` was reserved here and is now used by arrays in T12;
  `assertionFailure` remains reserved);
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

## P2 — proof power and usability — ✅ complete

### ✅ T8. Verified reflective `Rat` normaliser (`rat_ring`) — **L**, medium/high risk

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

**Acceptance.** ✅ `symplecticStep` preserves `modifiedEnergy` for all rationals,
and `repeatStep_position_twice` is proved; both with no new axioms and covered by
the build-time audit. Corruption tests reject false identities and rational
literal coefficients (clear denominators first).

### ✅ T9. Spec database and `pontifex_step` tactic — **M**, low risk

**Why.** Aeneas's usability comes from ~180 `@[step]` lemmas and `step*?`.
Our spec links are hand-written against generated definitions.

**Scope.**

- one registered lemma per IR operator and statement form where useful (the
  implemented tactic unfolds `evalS`/`evalV` and the array value helpers, and
  uses named outcome lemmas such as `fromEval_ok`/`bindEnv_fellThrough`);
- a `pontifex_step` tactic that unfolds a translated function to arithmetic and
  discharges side conditions with `assumption`/`simp`/`omega` as configured;
- a `pontifex_step*?` script printer;
- rewrite `Pontifex/Examples/SpecLinks.lean` to use the tactic as the
  acceptance test;
- document when to use the tactic vs `rfl` linkage.

**Acceptance.** ✅ `pontifex_step` has an explicit rule list, a trace variant,
and worked component specs in `Pontifex/Examples/StepDemo.lean`; proofs no longer
unfold `exec` by hand. Deeply nested loops still need invariants/fuel induction.

### ✅ T10. Two-tier arithmetic lemmas for Float — **L**, high risk

**Why.** Aeneas proves `*_equiv` (value level) and `*_bv_spec` (bit level) per
scalar op. Our generic `Ops` certificate proves identical structure, not IEEE
correctness.

**Scope.**

- state bit-level specs for `+ - * /` on finite doubles (round-to-nearest-even,
  no-NaN side conditions);
- state value-level corollaries and reuse them in the differential harness as
  the specification of the oracle;
- decide what to prove vs cite/assume about the hardware/Lean runtime.

**Acceptance.** ✅ `FloatSpec` proves bit/value component specs for add/sub/mul/
div/pow/neg/abs by `rfl`; docs state precisely that native rounding remains the
tested trust boundary. Full IEEE arithmetic proofs remain future work.

---

## P3 — language growth — in progress

### ✅ T11. Multi-exit returns with verified lowering — **M**, low risk (schema unchanged)

Implemented without a CFG or a result/flag slot. IR sequences already stop at
the first `returned` outcome, so an early exit short-circuits its enclosing
sequence, `if` merge, and loop back edge. The lowering now computes `if` merges
from the environments of the branches that can still fall through, so a branch
that always returns contributes no phi input (its side is a dead but defined
slot); loop variables assigned only on a returning path are not loop-carried.
New restrictions: unreachable code after a definitely-returning statement,
functions that can fall through without a return, and mismatched return arity
are rejected with located diagnostics.

**Acceptance.** ✅ Early returns are accepted in branches and loop bodies; the
per-program `<fn>_lowering := rfl` certificate still checks the Lean reference
lowering; `examples/early_exit.py`, three kernel-checked certificate programs,
a corpus program, and the rejection snapshots cover the new shapes. `Seq`
semantics and the emitted-code certificates were already correct and are
unchanged.

### ✅ T12. State vectors / arrays — **L**, medium risk (schema 3)

Implemented as tagged slot values: `Val α = .scalar α | .array (List α)` in the
existing environment, so arrays flow through the same phis and loop headers as
scalars and `Outcome`/`exec`/`Fn.run`/`exec_mono` keep their signatures. Length
is intrinsic to the `List`. Surface syntax is one-dimensional list literals,
`xs[i]` reads, `xs[i] = v` functional updates, and `len(xs)`. Both the read and
the update are bounds-checked; a fractional, negative, non-finite, or
out-of-range index is `failed .indexOutOfBounds`. The update is an `Expr.set`
assigned to a fresh slot, which keeps the IR alias-free (no array parameters,
array returns, nested arrays, or array copies). The frontend tracks static
scalar/array kinds through branches and loops and rejects kind mismatches.

**Acceptance.** ✅ `examples/array_step.py` (kernel-checked lowering, compiled
link, axiom audit), three kernel-checked certificate programs (vector loop,
array phi, bounds failure), three corpus programs (including out-of-bounds in
both read and store positions), rejection snapshots for aliasing, nested arrays,
kind changes, and scalar/array confusion. `exec_mono` and the refinement layer
required no proof changes beyond the value-tag plumbing.

**Deferred (not scheduled).** Array parameters and array returns need their own
wire/CLI/corpus argument plumbing; shared-array aliasing is F7; multi-dimensional
arrays remain out of scope. T13 calls will meet the value model as it stands:
arrays are functional values, so passing or returning one is copy-free until
aliasing is modelled.

### T13. Function calls — **L**, in progress

**First slice implemented:** white-box expansion of module-local straight-line,
single-scalar helpers at complete assignment/annotated-assignment/return sites.
Arguments are positional scalar expressions, evaluated once in order before
callee work, including unused arguments. Fresh private slot frames isolate
callee locals and parameter reassignments. Forward references and acyclic
helper chains work; caller branches, loops, early returns, and arrays retain
their existing rules. Calls added no runtime node or JSON/schema change when
they landed on schema 3; T15a now uses schema 4.

The core Source AST references each independently emitted callee IR. The Lean
`Inline.expand` reference algorithm reproduces the Python expansion inside the
caller's `_lowering := rfl`. `<fn>_program_lowering` composes that fact with
all per-callee program certificates recursively, so the callee's source/IR
agreement is checked too. The usual code linkage proves the expanded code/IR
agreement. Inlining fidelity remains tested, not a universal preservation proof.
See [`docs/CALLS.md`](docs/CALLS.md).

**First-slice acceptance met:** `examples/call_step.py` emits a caller program
certificate referencing the helper's certificate, with both lowering facts
`rfl`/kernel-checked and every certificate axiom-audited. Regression coverage
includes transitive helpers, control-flow callers, private locals, eager faults,
JSON round trips, kernel mutation rejection, three call corpus programs, and
located rejection snapshots.

**Second slice implemented:** calls may now appear inside scalar expressions —
operands of arithmetic/`min`/`max`/`abs`/`**`, array elements and indices, the
value of `xs[i] = v`, augmented-assignment right-hand sides, call arguments, and
return-tuple elements. Each nested call is hoisted, in Python evaluation order,
into a fresh-slot assignment before the enclosing statement. The core source AST
marks it `inlineTemp`, so the result is an SSA temporary that never enters `if`
merges or loop-carried analysis; the reference lowering binds it locally instead
of threading extra state. Calls remain rejected inside conditions and
conditional-expression branches (short-circuit / re-evaluation), and a call may
not follow a failing operand in the same statement, because hoisting would
reorder the reported failure.

**Still open (T13 is not complete):** callee branches/loops/early returns,
calls inside conditions and conditional-expression branches, tuple
results/unpacking, keyword/starred/ignored-result calls, array
arguments/results/locals in helpers, and calls with summaries. Recursion and
external calls remain unsupported.

**Certificate cost (#21, fixed):** the `rfl` lowering certificate used to be
roughly exponential in the length of a straight-line block (~0.7 s at 8
statements, ~3.4 s at 10, over the default heartbeat budget at 11), so inlining
(which adds statements) reached the limit sooner. `Source.lowerRec` now applies
the plain mutual recursor `Source.Stmt.rec_1` instead of the equation compiler's
`brecOn` form, whose auxiliary "below" structure duplicated the recursive
result at every level. Reduction is linear: 16 statements check in well under a
second and 60 in about 0.3 s. The definition is `noncomputable` because Lean's
code generator does not support the mutual recursor; it is reference/proof code,
and the executable lowering remains the Python frontend. A regression test
kernel-checks a 30-statement body. See T16.

### T14. Opacity lattice and verified-path assertion — **M**

Levels `Transparent / Modeled / Opaque / Invisible`, per-item metadata, Lean
`opaque` constants for the opaque level, and an assertion in each certificate
that no opaque node was reached on the verified path. Model after Charon's
four-level lattice and Aeneas's `is_opaque`.

**Acceptance.** A function calling an opaque helper still yields a certificate
for its own body; the generated proof states the opacity precondition explicitly.

### T15a. `min`, `max`, and conditional expressions — **M**, schema 4

Implemented following [#2](https://github.com/michaelnavazhylau/pontifex/issues/2)'s
explicit-IR scope (superseding the older frontend-desugaring sketch).
`BinOp.min` / `BinOp.max` accept exactly two positional scalar arguments and
evaluate both once, left to right. They return the second operand only when it
compares strictly less/greater; ties and unordered comparisons retain the first
operand unchanged, including binary64 zero signs and NaN payloads.

`Expr.select` / Source `select` evaluate a boolean-sorted condition, then only
the selected scalar branch. Expressions and conditions are mutually recursive
in syntax, evaluation, lowering, and helper relocation. The reference algorithms
remain kernel-reducible: lowering is still `rfl`-checked. All three forms use
the independent certified backend, even without statement control flow, with
full-outcome/all-fuel/all-backend linkage. Schemas 1–3 must be regenerated.
See [`docs/SELECTION.md`](docs/SELECTION.md).

**Acceptance evidence.** `examples/limited_step.py` and kernel-checked
straight-line/control-flow/array/helper programs; mutation rejection for source,
IR, and executable selection changes; eager argument/fault order, lazy branch
faults and `stuck`, exact/Float differential coverage, strict IEEE edge tests
(including signaling NaNs, ties, and signed zero), three new corpus programs,
and snapshots for arity/keyword/unpacking/array/condition restrictions.
Scalar truthiness, iterable/variadic `min`/`max`, and array results remain out
of scope; the Python numeric tower is still T15b.

### T15b. Python integer and numeric-tower semantics — **M**, design spike

Python `int` is unbounded; the current IR has one scalar type per backend. Decide
whether to (a) model `int` as `ℤ` with explicit coercion points, or (b) keep
rejecting mixed int/float code and document the boundary. This choice also fixes
whether array indices remain scalars or become a separate integer sort.

**Acceptance.** A documented numeric tower with tests; no expression silently
changes meaning between exact and float modes; array-index conversion is either
subsumed by the tower or explicitly documented as the remaining exception.

### ✅ T16. Linear-cost lowering certificates ([#21](https://github.com/michaelnavazhylau/pontifex/issues/21)) — **M**, low risk

The reference `Source.lowerBody` previously compiled through `brecOn`, whose
auxiliary below structure duplicated each recursive result. With the growing
slot/environment state that made `rfl` certificates roughly exponential in block
length, and inlining (which adds statements) reached the default heartbeat
budget sooner. `lowerRec` now applies the plain mutual recursor with explicit
`motive_1`/`motive_2`, keeping recursive results linear without changing the
algorithm or any certificate shape. The definition is `noncomputable` because
Lean's code generator does not support that recursor; the lowering is proof-only
reference code, while the executable lowering remains the Python frontend.

**Acceptance met.** Every existing generated certificate still checks by `rfl`;
a 30-statement straight-line body kernel-checks in about a second (regression in
`test_certificates.py`), the lowering of 60 statements takes ~0.3 s, and a
complete 50-statement artifact takes ~2 s; the old implementation took ~25 s at
12 statements and minutes at 16. [`docs/TRUST.md`](docs/TRUST.md)
records the proof-only status and [`docs/CALLS.md`](docs/CALLS.md) records the
linear certificate cost.

---

## P4 — research options (not scheduled)

- **CFG-first IR** (ULLBC analogue) with a separately verified structuring pass
  and a `--unstructured` fallback. Unlocks irreducible control flow and makes
  loop structuring a proof obligation rather than a frontend assumption.
- **Termination without fuel**: a total-correctness layer (variant measures or
  `partial_fixpoint`-style definitions) for selected functions.
- **Broad Python exception model**: `KeyError`, `TypeError`, `OverflowError`,
  and user `raise`, with an effect/outcome discipline.
- **Aliasing and shared state (F7)**: references or arrays shared across
  functions. Today the IR is strictly functional: slots hold scalars or
  one-dimensional arrays, and an update produces a fresh value, so there is no
  observable sharing to reason about.

---

## Recommended sequence

1. ✅ **T1–T4** complete.
2. ✅ **T5–T7** complete. Computed-NaN exemptions are explicit and counted;
   native arithmetic proofs and a full Python numeric tower remain open.
3. ✅ **T8–T10** complete: certified normalization, the step tactic, and
   two-tier Float specs. Native IEEE proofs and rational-coefficient
   normalization remain open.
4. ✅ **T11–T12** complete: early returns and one-dimensional arrays with bounds
   failures.
5. **In progress:** **T13** (bounded white-box calls landed; broader call shapes
   and summaries remain). **T15a** now implements `min`/`max` and scalar
   conditional expressions. **T14** (opacity) can follow calls. **T15b** should
   be a design spike before any further numeric growth.
6. **Tooling and follow-ups:** [#16](https://github.com/michaelnavazhylau/pontifex/issues/16)
   `pontifex check` capability preflight remains open; it makes the subset
   boundary explicit and is a natural home for reporting T12's array
   restrictions. [#21](https://github.com/michaelnavazhylau/pontifex/issues/21)
   lowering-certificate reduction cost is fixed (T16).

## Explicit non-goals (for now)

- general borrow checking, concurrency, or a heap model;
- full Python object semantics (classes, generators, exceptions hierarchy);
- a rustc-style pinned-compiler/Nix build matrix;
- proving the Python parser or the surface desugaring correct (they remain
  tested, not verified; the certified boundary starts at the emitted core AST).
