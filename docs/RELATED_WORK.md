# Related work: what to take from Charon and Aeneas

Reading notes from a deep review of the two upstream repositories that define the
current state of the art for Rust → proof-assistant translation.

**Sources and provenance.** Two fresh-context subagents performed independent
read-throughs of shallow clones; the parent then spot-checked the load-bearing
claims against those clones.

| Repository | Commit reviewed | Spot-checked |
| --- | --- | --- |
| [AeneasVerif/charon](https://github.com/AeneasVerif/charon) | `3f821f7` (Charon 0.1.293, toolchain `nightly-2026-09-17`) | `ullbc_to_llbc.rs` (structured reconstruction, `Irreducible`), `ast/bodies/unstructured.rs`, `src/minirust.rs`, `docs/` |
| [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas) | `fc321a2` | `Float are not supported` (`SynthesizeSymbolic.ml:77`), `partial_fixpoint` (`ExtractBase.ml:1461`), `loop`/`ControlFlow` (`Std/Primitives.lean:447-452`), `-use-fuel` rejected for Lean (`Main.ml:535`), `spec`/`dspec` (`Std/WP.lean:56-59`) |

The full reports are preserved verbatim in
[`docs/related-work/charon-review.md`](related-work/charon-review.md) and
[`docs/related-work/aeneas-review.md`](related-work/aeneas-review.md). They are
reading notes, not independent verification of every claim; the commits above
are the ground truth for line references.

## Executive summary

1. **Charon is a serialized compiler-frontend, not a verifier.** It turns rustc
   MIR into a uniform IR with two forms (unstructured `ULLBC` CFG and
   structured `LLBC`), always emitting *something* (even `Body::Error`), and
   publishes an explicit trust statement plus a MiniRust reference semantics.
2. **Aeneas's functionalization happens in its abstract interpreter**, not in a
   separate CFG-to-functional pass: the interpreter's environment is a dynamic
   SSA form, branches become `Join` nodes, loop headers are fixed points, and
   loops later become either structural recursion or a single `loop`
   combinator.
3. **Aeneas separates totality from partial correctness through one fixpoint
   theory**: recursive definitions use `partial_fixpoint`, `spec` is a least
   fixpoint (divergence impossible) and `dspec` a greatest fixpoint (partial
   correctness), with a one-way bridge `DWP.toPartial`. Fuel is legacy and
   rejected for the Lean backend.
4. **Neither project has a proof of translation correctness or an independent
   certificate.** Trust is engineering-grade: pinned frontend, CI typechecking
   and proof replay, internal invariant checks, freshness checks for generated
   models, differential layout fuzzing, a top-500-crates test, and committed
   `known-failure` outputs. This is precisely the gap our per-program `rfl`
   certificates close for a much smaller language.
5. **The highest-value ideas for us are about interfaces, not compiler
   internals**: an outcome lattice with divergence as bottom, a derived
   total/partial spec layer, an opacity/annotation lattice, options + version
   stamping inside the artifact, a registered spec database (`@[step]`), and
   committed negative tests.

## Architecture at a glance

```
Rust source
  └─ rustc MIR ──Charon──▶ ULLBC (CFG) ──1 pass──▶ LLBC (structured)
                                                   │
                                     Aeneas prepasses, symbolic interpreter
                                                   │
                       symbolic AST (Join/Loop/Continue/Break/Expansion)
                                                   │
                                       SymbolicToPure + micro-passes
                                                   │
                                  Pure lambda calculus (Result, Loop, LoopResult)
                                                   │
                      extractor ──▶ Lean / F* / Coq / HOL4 definitions
                                                   │
                                  hand-written specs + WP tactics (Lean)
```

Our pipeline for comparison:

```
Python source ──ast──▶ core AST (ids) ──verified lowering──▶ SSA IR
                                                              │
                             ┌────────────────────────────────┤
                             ▼                                ▼
                 direct code (straight-line)        certified slot-state blocks
                             │                                │
                             └────────── kernel `rfl` ────────┘
                                              │
                                    hand-written spec lemmas
```

## Mechanisms worth studying

### Two IR forms, one semantics (Charon)

`ULLBC` is a CFG whose `BlockData` carries `statements`, a `terminator`, and an
`UnwindKind`; every call/assert/drop has an `on_unwind` edge, so unwinding is
first-class control flow. `LLBC` is reconstructed by a single pass
(`transform/control_flow/ullbc_to_llbc.rs`), with an explicit failure mode
(`struct Irreducible`) and a documented `--ullbc` fallback.

*Why it matters for us:* our generator supports only structured `if`/`while`
with a single exit. A canonical unstructured form would handle multi-exit
programs and make "structuring" a separately checkable view. It also explains
why their loop translation is total: the CFG is the authority.

### Functionalization by abstract interpretation (Aeneas)

There is no SSA pass. The interpreter maps places to symbolic values
(`src/interp/Contexts.ml`), so its environment *is* the SSA form. Branches
produce `Join` nodes; loop entries are computed as fixed points
(`compute_loop_entry_fixed_point`, bounded by `loop_fixed_point_max_num_iters =
2`), which yields the loop-carried variables plus their backward continuations.
`decompose_loops` then emits either a recursive `_loop` (when a structural
measure is found) or a call to one generic combinator:

```lean
inductive ControlFlow (α β) where | cont : α → ControlFlow α β | done : β → ControlFlow α β
def loop (body : α → Result (ControlFlow α β)) (x : α) : Result β
```

### Totality via fixpoints (Aeneas)

Recursive Lean definitions are emitted with `partial_fixpoint`, so they unfold
definitionally without a termination proof. `Result` is an ITree with `ok`,
`fail`, and `div`; `div` is the bottom of the order. `spec` uses the least
fixpoint (`DWP`, divergence disallowed); `dspec` uses the greatest fixpoint
(`DWLP`, partial correctness); `DWP.toPartial` bridges them. For Lean, fuel is
explicitly rejected (`The Lean backend doesn't support the -use-fuel option`).

*Why it matters for us:* our fuel-based semantics is total and kernel-reducible,
which we rely on for `rfl`; switching wholesale to `partial_fixpoint` would trade
that away. The transferable part is the **interface**: define an outcome order
with exhaustion/divergence as bottom, prove refinement lemmas ("more fuel cannot
change a completed result"), and derive total vs partial spec readings from one
definition.

### Trust is industrial, not formal; negative tests are first-class

Aeneas trusts Charon, its ~60 pure-code micro-passes, its hand-written std
models (29 types / 58 traits / 75 functions), and `axiom`s for opaque
declarations. Mitigations: every generated file must typecheck and every proof
module replay (`make verify`), internal well-boundedness and interpreter
invariant checks, generated-model freshness diffs, and `known-failure` outputs
that make "we correctly reject this" a regression test.

Charon similarly publishes an explicit trust FAQ, names `src/minirust.rs` as the
authoritative semantics with an "unsoundly translated" list, fuzzes layout
against rustc under randomized layout, and translates the top 500 crates with
commented blocklists.

*Why it matters for us:* we already have stronger per-program guarantees, but
weaker **corpus-scale** validation. Negative tests and a curated corpus are
cheap and directly increase confidence in the parts certificates cannot cover
(parsing, desugaring, rejection).

### Artifacts carry their configuration and version

Charon serializes `charon_version` next to the crate and refuses to decode a
mismatch (`export.rs`); it embeds the `CliOpts` used so consumers can assert
required flags (`ast/krate.rs`). Aeneas ships `translation.json` with Lean ↔
Rust spans and `can_fail`/`can_diverge`/`is_rec` flags.

*Why it matters for us:* generated Lean currently records only the source file.
If a flag changes the semantics (`fuel`, future float modes, certificate mode),
the proof can silently weaken. Stamping an IR/config version and asserting it in
the generated module turns that into a build error.

### Opacity/annotation lattice

Charon has four fidelity levels (`Transparent / Foreign / Opaque / Invisible`)
resolved by structured name patterns, and source attributes that can only
*increase* opacity. Aeneas turns opacity into `axiom` plus a template file and
`is_opaque` metadata, and degrades unsupported constructs to `fail .undef`
rather than silently mis-modelling them.

*Why it matters for us:* "supported subset" is a boolean today. A lattice would
let a mostly-verifiable function call an unmodelled helper, with the verified
path asserting that no opaque node was reached. This is the natural way to grow
from scalar physics kernels toward real numerical code.

### Proof UX: registered specs and a step tactic

Aeneas users state `f args ⦃ r => P r ⦄`. Specs are registered with `@[step]`;
`step` peels one monadic bind and discharges preconditions with configured
tactics; `step*` repeats with case splits; `step*?` prints a reviewable script.
The std library ships ~180 step lemmas, so builtins are transparent. Loops are
proved by a per-loop theorem with `termination_by`/`decreasing_by` or by
`loop.spec_decr_nat`.

*Why it matters for us:* our spec links are currently `rfl`/`simp` one-offs.
A small registered rule set (one lemma per IR operator and statement form) plus
a script printer would make downstream proofs about translated Python routines
substantially easier.

## Where pyverif stands relative to them

| Dimension | Charon + Aeneas | pyverif |
| --- | --- | --- |
| Translation trust | trusted translator; CI + invariants | **per-program kernel certificate** for lowering and codegen (small language) |
| Loop semantics | CFG authority; fixed-point abstraction; `partial_fixpoint`; total/partial WP | structured IR; fuel; kernel-reducible; full outcomes |
| Termination | extrinsic (`DWP`/`DWLP`); divergence is bottom | fuel exhaustion; no termination proofs; no refinement theorem yet |
| Numeric model | integers as `BitVec` with overflow `Result`; **no floats** | exact `Rat` **and** binary64 `Float`; no integer-overflow model |
| Error model | `Result` with `assertionFailure`, `integerOverflow`, `divisionByZero`, `undef` | outcomes `returned / fellThrough / outOfFuel`; Python exceptions, `NaN`, signed zero are outside the model |
| Aliasing/state | borrow/loan symbolic semantics, backward lenses | none (scalar locals only) |
| Surface | Rust (rustc MIR), huge feature surface, opacity lattice | small Python subset, strict rejection, no opacity levels |
| Proof UX | `@[step]`, `step*`, WP calculus, std lemmas | hand-written `rfl`/`simp` spec links |
| Validation | typecheck + replay, freshness, fuzz, top-500 crates, known-failure | 115 tests, triple differential (CPython/IR/Lean), corruption tests |
| Artifact metadata | version + options embedded | source path only |

## Ranked recommendations

Ordered by payoff per unit of risk for this repository. Each is deliberately
scoped so it can land without changing the existing certificates.

### 1. Introduce an explicit outcome lattice and refinement theorem

Define an order on outcomes with exhaustion (and a future `stuck`/`error`) as
bottom, prove that `n ≤ m` implies "if the run with fuel `n` returned, the run
with fuel `m` returns the same values", and state total vs partial correctness
readings on top. This is the cheapest transfer of Aeneas's `DWP`/`DWLP` idea and
removes per-proof fuel plumbing. It also gives a principled home for exceptions
and undefined behaviour when we add them, instead of widening `Option`.

**First step:** `PyVerif/Core/OutcomeOrder.lean` with `Refines`, monotonicity for
`exec`, and tests instantiating it on the loop example.

### 2. Add an exceptional/undefined outcome before adding features

Right now `IR.div` is total in Lean but raises in Python, and the model simply
excludes zero divisors. Aeneas makes failure explicit in `Result` (`fail
.integerOverflow`, `.divisionByZero`, `.undef`) so specs can say "fails iff".
Adding `Outcome.failed : Error → Outcome α` forces the semantics, the reference
interpreter, the JSON encoding, and the certificates to agree once, before more
IR constructs arrive.

**First step:** a design note plus `Outcome.failed`, wired through `exec` and
the Python interpreter, with division-by-zero as the first error kind.

### 3. Stamp and assert the artifact configuration

Emit a `def pyverifConfig : Config := { irVersion := …, fuelPolicy := … }` in
each generated module and `#guard` the invariants the proof depends on. Extend
`scripts/generate.py --check` to include a schema version. This directly copies
Charon's version/options-in-artifact discipline and prevents silent weakening.

**First step:** a version constant in `pyverif/ir.py` and `PyVerif/Core/IR.lean`,
plus a `#guard` in generated files.

### 4. Make the canonical IR unstructured (or at least support multiple exits)

Charon's ULLBC authority and one explicitly fallible structuring pass is a
proven design for handling early returns, `break`, and irreducible control flow.
Our single-exit restriction is the largest *language* limitation left. Either
lower to a CFG and reconstruct structured forms (harder), or add a restricted
multi-exit `return` with a proved lowering to the existing structured IR
(cheaper).

**First step:** a design spike on `return` inside branches, with the lowering
certificate as the acceptance criterion.

### 5. Add an opacity/annotation lattice for gradual adoption

Instead of rejecting any call to an unmodelled function, classify items as
`Transparent / Modeled / Opaque / Invisible`, emit `opaque` Lean constants for
the opaque level, and assert in the certificate that the verified path contains
no opaque node. This mirrors Charon's fidelity levels and Aeneas's
`is_opaque`/template workflow, and is the path from scalar kernels to real code.

**First step:** a `#pyverif.opaque` source comment/attribute convention and a
metadata block in the JSON.

### 6. Build a registered spec database and a step tactic

Provide `@[pyverif_step]` lemmas for expressions/statements and a `pyverif_step`
tactic that unfolds a translated function into its arithmetic, plus a script
printer. This is the main usability gap relative to Aeneas: our specs are
currently written by hand against generated definitions.

**First step:** one lemma per IR operator (`evalE_add`, `evalE_mul`, …) and a
macro that repeatedly applies them, then rewrite the free-fall spec link to use
it.

### 7. Add a negative-test corpus with committed expected errors

Our rejection tests assert "raises", but not the exact diagnostic, and there is
no repository of programs we deliberately refuse. Aeneas's `known-failure`
outputs make rejection behavior reviewable and regression-proof. Snapshot the
error message, kind, and location for each unsupported construct, and run the
whole corpus in CI.

**First step:** extend `test_frontend.py` to compare against committed
`.error` snapshots and add a `tests/rejections/` directory.

### 8. Add a differential corpus beyond examples

Translate a small curated set of real numerical routines (e.g. from
`math`/physics exercises) inside the subset, and run the triple differential
over a fixed seed corpus in CI. Charon's top-500-crates test and Aeneas's
113-program test suite are the model; our four examples are too few to catch
frontend regressions.

**First step:** a `corpus/` directory plus a generator that emits both Lean and
IR for every file and runs the oracle comparison.

### 9. Prepare the arithmetic two-tier lemma shape

Aeneas proves `*_equiv` and `*_bv_spec` per scalar operation. Our `Float` side
has no such bridge: the generic `Ops` certificate shows identical structure, not
IEEE-754 correctness or agreement with CPython. When float reasoning starts, the
two-tier shape (value-level result + bit-level specification) is the right
interface.

**First step:** design `Float` specs for `+ - * /` as value/bit lemmas, even if
the proofs initially cover only finite, non-NaN cases.

## What not to copy

* **A trusted translator plus CI as the main assurance story.** Certificates are
  stronger and already work for our fragment; keep them.
* **`partial_fixpoint` everywhere.** It buys definitional unfolding without
  termination proofs, but our fuel interpreter is kernel-reducible, which is what
  makes `rfl` certificates cheap. Adopt the *interface* (order, total/partial
  readings), not necessarily the implementation.
* **A 60-pass micro-pass pipeline.** It is the largest unverified surface in
  Aeneas. Our pass count is small enough that each can be certified or kept
  definitional.
* **Stringly-typed name generation.** Unicode identifiers, name shadowing and
  Lean keyword clashes are recurring bug classes upstream; our ids-instead-of-
  names source AST avoids them by construction.
* **Axioms for opaque code without an assertion.** Aeneas exposes `is_opaque`;
  if we grow opacity, the certificate must *require* that no opaque node was
  reached on the verified path.

## References

* Charon: <https://github.com/AeneasVerif/charon> — README, `docs/faq.md`,
  `docs/minirust.md`, `docs/limitations.md`, `charon/src/ast/bodies*`,
  `charon/src/transform/control_flow/ullbc_to_llbc.rs`.
* Aeneas: <https://github.com/AeneasVerif/aeneas> — README,
  `documentation/`, `src/interp/`, `src/symbolic/`, `src/pure/`,
  `backends/lean/Aeneas/{Std/WP.lean,Std/Primitives.lean,Tactic/Step/}`,
  `tests/README.md`.
* Papers cited by upstream: ICFP'22 (functional translation), ICFP'24
  (sound borrow checking via symbolic semantics).
* Full reports: [`related-work/charon-review.md`](related-work/charon-review.md),
  [`related-work/aeneas-review.md`](related-work/aeneas-review.md).
