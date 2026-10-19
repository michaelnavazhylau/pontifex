# Aeneas — technical review

> Captured from a fresh-context read-through of
> <https://github.com/AeneasVerif/aeneas>, shallow clone at commit `fc321a2`
> ("Fix several unsupported cases in the symbolic evaluation (#1457)"), pinned
> Charon `de8736f`. The parent spot-checked the key claims (`Float are not
> supported`, `partial_fixpoint`, the `loop` combinator, `-use-fuel` rejection
> for Lean, `spec`/`dspec`) against the clone. This is a reading record, not an
> independent verification of the project.

## 1. Pipeline

`Rust → Charon → LLBC → PrePasses → symbolic interpreter → symbolic AST → pure
AST → micro-passes → extractor → backend text`.

1. **Charon** (external, version-pinned in `charon-pin`, checked by
   `scripts/ci-check-charon-pin-is-*.sh`) compiles Rust MIR to `.llbc`. Aeneas
   reads it in `src/llbc/LlbcOfJson.ml` / `src/llbc/Values.ml` (`src/llbc/`
   holds its own copy of the Charon AST).
2. **PrePasses** (`src/PrePasses.ml:2328` `apply_passes`) — erases body regions,
   removes unreachable code, normalizes loops, `remove_useless_joins`,
   `simplify_panics`, `decompose_global_accesses`, `simplify_trait_calls`,
   vtable removal. Each pass is wrapped in `apply_function_pass`
   (`src/PrePasses.ml:2356`) which turns a failure into `ErrorBody` so one
   broken function does not kill the crate.
3. **Symbolic interpreter** (`src/interp/`, 15k lines) is the heart.
   `Translate.translate_function_to_symbolics` (`src/Translate.ml:22`) calls
   `evaluate_function_symbolic`, producing a `SymbolicAst.expr`
   (`src/symbolic/SymbolicAst.ml:146`) — a CPS-style tree of `Return`, `Panic`,
   `FunCall`, `EndAbs`, `Assertion`, `Expansion`, `Join`, `Loop`, `Continue`,
   `Break`.
4. **Symbolic → pure**: `SymbolicToPure` (`src/symbolic/SymbolicToPure.ml`,
   split across 6 files) lowers to `Pure.expr` (`src/pure/Pure.ml`) — a lambda
   calculus with `Result`/`LoopResult`, `Loop of int`, `RecLoopCall of int`,
   `FuelDecrease`/`FuelEqZero`, `UpdateAtIndex` (`src/pure/Pure.ml:100-152`).
5. **Micro-passes**: ~60 named passes in `src/pure/PureMicroPasses.ml:12-260`
   (name prettification, let simplification, struct updates, loop filtering,
   then `decompose_loops` / `decompose_loop_bodies` / `loops_to_fixed_points` in
   `apply_passes_to_pure_fun_translations`,
   `src/pure/PureMicroPasses.ml:373-437`).
6. **Extraction**: `src/extract/Extract.ml` (3.8k lines) + per-backend
   `ExtractBuiltin*.ml`; syntax differences are localized in
   `fun_decl_kind_to_qualif` and friends (`src/extract/ExtractBase.ml:1403-1467`).

**Backends.** Lean is primary: `backends/lean` is 49k lines with data
structures, std-library models, WP calculus and ~20 tactic files;
`backends/coq/Primitives.v` (1k lines) and `backends/fstar/Primitives.fst` (1k
lines) are comparatively thin and full of `Axiom`s (e.g.
`array_index_usize`, `backends/coq/Primitives.v:775`). README:143-150 names Lean
and HOL4 the mature targets. `documentation/aeneas-overview.md:29-31` says Lean
is the most actively maintained.

**Artifacts.** Generated `Types.lean` / `Funs.lean`, plus `*_Template.lean`
stubs for external definitions with `-split-files` (README:152-193); optional
`translation.json` manifest mapping Lean names to Rust spans and
`can_fail`/`can_diverge`/`is_rec` flags (`src/EmitJson.ml:1-60`,
`documentation/emit-json.md`). **Specs and proofs are not generated** except
`termination_by`/`decreasing_by` templates (`src/extract/Extract.ml:1927-2350`).

## 2. Functionalization

Aeneas has no CFG→functional reconstruction pass and, as far as I can tell, no
SSA IR (`grep -r SSA src` is empty). Functionalization happens *during* abstract
interpretation: `eval_ctx` maps places to symbolic values
(`src/interp/Contexts.ml`), so the interpreter's environment *is* a dynamic SSA
form. Branching creates a `Join` node (`src/symbolic/SymbolicAst.ml:234`)
carrying the merged context and both branch values; `translate_join`
(`src/symbolic/SymbolicToPureExpressions.ml:2163`) emits a tuple of all live
values, which micro-passes then sink into `let (x,y) := if b then ... else ...`.
Short-circuiting and early returns therefore become ordinary functional code
rather than jumps.

**Loops.** At a loop entry the interpreter computes a *fixed point* of the
environment: `compute_loop_entry_fixed_point`
(`src/interp/InterpLoopsFixedPoint.ml:38`) iterates the body (bounded by
`Config.loop_fixed_point_max_num_iters = 2`, `src/Config.ml:186`) over
"reborrowed", abstraction-stabilized contexts, yielding a loop abstraction over
the loop-carried variables plus their backward continuations
(`src/interp/InterpLoops.mli:1-55` documents this with the `list_nth_mut`
example). `decompose_loops` (`src/pure/PureMicroPassesLoops.ml:2946`) then
splits each loop into a `_loop` function and a `_loop.body` continuation,
producing either:

- **a recursive `_loop`** when `loop_satisfies_recursive_criteria_aux`
  (`src/pure/PureMicroPassesLoops.ml:2475`) finds identity input continuations,
  terminal backward calls, and a *structural* termination measure
  (`loop_rel_has_termination_measure`, line 2430). Example: `list_mem_loop` in
  `tests/lean/Loops.lean:227`;
- **a `loop` combinator call** `loop (body : α → Result (ControlFlow α β)) (x :
  α) : Result β` (`backends/lean/Aeneas/Std/Primitives.lean:446-457`), with
  `ControlFlow.cont/done`. Example: `iter_loop` in `tests/lean/Loops.lean:38`.

`loops_to_recursive` (`src/pure/PureMicroPassesLoops.ml:2782-2830`) shows how
input backward functions are eliminated to make a loop structurally recursive.

**Termination/divergence.** Recursive Lean definitions are emitted with
`partial_fixpoint` (`src/extract/ExtractBase.ml:1449-1455`), i.e. a monotone
fixed point — *no* termination proof is required at definition time, and
`unfold` works definitionally. `div` is the bottom element of the `PartialOrder`
on `Result` (`backends/lean/Aeneas/Data/Coinductive/ITree.lean:20,132`,
`CoInd.bot = ITree.div`), so non-termination is literally ⊥. Totality is
recovered *extrinsically*: `spec` is `DWP` (least fixpoint, divergence
disallowed) while `dspec` is `DWLP` (greatest fixpoint, partial correctness)
(`backends/lean/Aeneas/Std/WP.lean:48-64`, `ITreeWP/DWP.lean:1-33`,
`DWLP.lean:35`, `DWP.toPartial` in `ITreeWP/Taxonomy.lean:17`). `spec_fail`/
`spec_div` are `False` (`WP.lean:112-118`). **Fuel is legacy**: `-use-fuel`
(`src/Config.ml:217`) adds `FuelDecrease`/`FuelEqZero` for F*/Coq only and is
rejected for Lean/HOL4 (`src/Main.ml:533-556`).

**Error monad.** `Result α = ITree RustEffect α` with `ok`, `fail : Error →
Result α`, `div` (`Primitives.lean:39-92`); `Error` = `assertionFailure |
integerOverflow | divisionByZero | arrayOutOfBounds | maximumSizeExceeded |
panic | undef`. `massert b` fails with `assertionFailure`
(`Primitives.lean:235`). **Backward functions**: a function returning `&mut T`
returns `(value, back)` where `back` is a lens; machinery is `back_sg_info`
(`src/pure/Pure.ml:1625-1646`) with level-indexed inputs/outputs. Signature-level
*state threading* is documented (`src/pure/Pure.ml:1707-1730`) but no `TState`
type exists — generated code is state-free today.

## 3. Memory model and data structures

There is **no heap model**. Rust's ownership discipline is exploited by
*symbolic borrow tracking*: each value position holds either a value, `VLoan`,
`VBorrow`, or `VBottom`; region abstractions (`abs`) group loans/borrows for one
lifetime. `src/interp/InterpBorrows.ml` (2.6k lines) implements borrow/loan
creation and ending, `src/interp/InterpAbs.ml` (2.9k) converts values into
abstractions and reifies `output`/`input` continuation expressions,
`src/interp/Invariants.ml:55+` asserts runtime invariants (loan-id uniqueness,
borrow/loan correspondence, two-phase borrows not inside abstractions). A `&mut
T` parameter becomes a plain `T`; returning a reborrow produces the backward
continuation. `Box<T>` is erased (README:143; `eliminate_box_functions`,
`src/pure/PureMicroPasses.ml:50`).

**Data structures are modelled functionally, not axiomatized:**

- `Array α n` = `ListN α n.val` (`backends/lean/Aeneas/Std/Array/Array.lean:26-30`);
- `Slice α` = `{ leng : Nat; list : ListN α leng; bound : leng ≤ Usize.max }`
  (`SliceDef.lean:10-17`);
- `Vec α` = `{ slice : Slice α }` (`Alloc/Vec.lean:28-31`), with `push` appending
  to a `List` and failing `maximumSizeExceeded` instead of allocating
  (`Alloc/Vec.lean:157-166`), plus a `@[step]` lemma. Capacity/allocation are
  gone; `usize` addressability is the only constraint.
- Both `Array` and `Slice` deliberately avoid subtypes because of positivity
  issues in recursive inductives (comment cites issue #1138).

**Integers** are `UScalar ty`/`IScalar ty` wrapping `BitVec ty.numBits` with
`.val : ℕ`/`ℤ` views (`Scalar/Core.lean:38-77`). Arithmetic goes through
`tryMk`, so `x + y : Result (UScalar ty)` fails with `integerOverflow` on
out-of-bounds; each op carries an `*_equiv` and a `*_bv_spec` linking `Result`,
`.val` and `.bv` (`Scalar/Ops/Add.lean:15-100`). Casts fail in Lean but are
total in other backends (`src/symbolic/SymbolicToPureExpressions.ml:583`,
`can_fail = not (backend () = Lean)`).

**Floats are unsupported** in the current pipeline: `SynthesizeSymbolic.ml:76`
raises "Float are not supported in Aeneas yet", float literals are rejected in
`src/extract/ExtractTypes.ml:103`, and there is no `Float` model or test in
`backends/lean` or `tests/src`. Raw pointers are placeholders
(`structure RawPtr (T) (M) where v : T`, `Std/RawPtr.lean:10-12`) and casts
among them return `.fail .undef` (`RawPtr.lean:33`).

## 4. Trust model

Trusted base, precisely:

1. **Charon's LLBC** — trusted blindly; version pinned, CI checks the pin is a
   merged, forward commit.
2. **The translator itself** (prepasses, symbolic interpreter, micro-passes,
   extractor). There is **no proof of translation correctness, no certificate,
   and no independent checker** in the repo. README:198-208 points at two
   papers: ICFP'22 for the functional translation and ICFP'24 for "sound
   borrow-checking via symbolic semantics" — the *borrow-checking* argument is
   the mechanized/published part, not a per-run certificate.
3. **The Lean std models** — 29 `rust_type`, 58 `rust_trait`, 75 `rust_fun`
   models in `backends/lean/Aeneas/Std/**` (e.g. `Vec.push`). These are
   hand-written Rust-semantics axioms; `ExtractBuiltinLean.ml` is generated from
   them and CI fails if it is stale.
4. **Opaque/external declarations** become `axiom`
   (`src/extract/ExtractBase.ml:1413`), surfaced in `translation.json` as
   `is_opaque`; users are pushed to supply models via `-split-files` templates
   (README:152-193).
5. Unsafe code / unsupported constructs degrade to `fail .undef` rather than
   being silently mis-modelled (`Std/RawPtr.lean`, `Error.undef`).

**Mitigations against translator bugs** are engineering, not formal:

- every generated file must **typecheck in the backend** (`make verify` →
  `lake build`, `tests/lean/Makefile:34-38`), and all 127 hand-written proof
  modules must replay — a mistranslation usually shows up as an unprovable spec
  or type error;
- internal sanity checks (`-checks`, `src/Config.ml:98`, enabled in CI via
  `Makefile:175-178`) check well-boundedness of every generated function
  (`Translate.check_fun_decl_vars_are_well_bound`, `src/Translate.ml:58`) and
  interpreter invariants (`src/interp/Invariants.ml`);
- optional internal typechecker on the pure AST
  (`src/pure/PureTypeCheck.ml`, `-type-check-pure-code`);
- a *concrete* interpreter run over all zero-argument functions (`-test-units`,
  `Test.test_unit_functions`, `src/interp/Interp.ml:695-706`) — a weak
  differential test that only checks "does not panic";
- `#guard_msgs` regression tests inside the Lean library itself (e.g.
  `WP.lean:540-556`).

## 5. Proof UX

The user states `f args ⦃ r => P r ⦄` (`spec`, `WP.lean:48-60`; `⦃ x back =>
... ⦄` for backward functions via the `uncurry'` delaborator, `WP.lean:96-104`).
Specs are registered with `@[step]`; `step` peels one monadic bind, discharging
preconditions with `assumTac`/`grind`/`simp`
(`backends/lean/Aeneas/Tactic/Step/Init.lean:45-90`). `step*` repeats with case
splits; `step*?` prints a reviewable script
(`documentation/proof-strategies.md:27-56`). The std library ships **180
`@[step]` lemmas**, so `Vec.push`, array indexing, scalar ops all step
automatically.

Loops are proved by a *separate theorem per `_loop` function* (recursive:
`termination_by` + `decreasing_by scalar_decr_tac`; combinator:
`loop.spec_decr_nat` with invariant + `Nat` measure, or `loop.spec` with any
`WellFoundedRelation`, `WP.lean:757-807`). For partial correctness of
`partial_fixpoint` definitions there is a `dspec_induction` tactic that
discharges the admissibility side-goal via a `@[dspec_admissible]` discrimination
tree (`Tactic/Step/DspecInduction.lean:10-40`, `WP.lean:79-88`). Supporting
automation: `scalar_tac`, `simp_scalar`, `simp_lists`, `bv_tac`/`bvify`/`natify`/
`zmodify`, `agrind` (preferred over `grind`), `fcongr`, `split_conjs`
(`documentation/tactics-reference.md`, `glossary.md`).

Performance guidance is explicit: generated files set `maxHeartbeats 1000000`
and `maxRecDepth 2048` (`tests/lean/Loops.lean:19-22`, configurable with
`-max-heartbeats`, `src/Config.ml:619`), while
`documentation/tips-and-tricks.md:338-385` gives a budget table (simple spec
0.5–2 s, 20+ binds 10–60 s, ">1M heartbeats means restructure"). Large functions
are handled by hand-written *fold theorems* that refactor the monadic body into
helper definitions (`glossary.md`, "Function decomposition"). Worked examples:
`tests/lean/Tutorial/Solutions.lean` (`list_nth_mut1_spec` with a
backward-function lens spec) and `documentation/proof-strategies.md`.

## 6. Validation and CI

- `make test` regenerates backend output for all of `tests/src` (113 files +
  `avl`, `bst`, `tutorial` crates) via `tests/test_runner/`; `make verify`
  typechecks it and replays proofs (`tests/README.md`).
- Per-test options are embedded as `//@` comments or `aeneas-test-options`:
  `[lean] skip`, `[fstar] known-failure`, `charon-args=...`,
  `aeneas-args=-test-trans-units` (`tests/README.md:44-70`, parsed in
  `tests/test_runner/Input.ml`). Seven `known-failure` tests lock in current
  unsupported cases (`raw_pointers.rs`, `mutually-recursive-traits.rs`,
  `borrow-check-negative.rs`) with committed `.out` files.
- CI (`.github/workflows/ci.yml`): nix build with `aeneas-check-tidiness`;
  **generated-file freshness** — `diff_lean_files` only runs Lean tests if
  `tests/lean`, `backends/lean`, `ExtractBuiltinLean.ml` or `LeanKeywords.ml`
  changed, and then *fails if `make extract-lean-std` produces a diff* or if
  `LeanKeywords.ml` is stale; Charon pin forward/merged checks; `userdocs`
  build. HOL4 outputs are checked but not regenerated (tracked as issue #62).
- Version pinning is strict and enforced in three places: `charon-pin`,
  `Makefile check-charon`, `backends/lean/lean-toolchain` (copied into every
  test project).

## 7. Known limitations and design decisions

Documented in README:126-141: `return` from nested loops / labelled `break 'a`;
instantiating generics with `&mut`; unsafe code and concurrency (future
separation logic); plus interior mutability, nested borrows in signatures,
function pointers/closures in flux (`docs/user/src/README.md`). Floats are
unsupported everywhere.

**Copy:**

- extrinsic totality via `partial_fixpoint` + `DWP`/`DWLP`, which decouples
  "does it terminate" from "is the definition well-formed";
- the same proof carrying both total (`spec`) and partial (`dspec`) readings;
- treating the *environment of an abstract interpreter* as the functionalization
  mechanism;
- the `⦃ ⦄` WP notation with `uncurry'` so backward functions read like lenses;
- the std-model-attribute → generated-OCaml-table → CI-freshness loop.

**Avoid:** the enormous micro-pass surface (~60 passes, 3.7k lines in
`PureMicroPassesLoops.ml` alone) — the main place where a silent mistranslation
could hide, with no independent oracle; and the stringly-typed extraction
(`ctx_add ... extract_name`) that makes Lean name clashes a recurring bug class
(`src/extract/ExtractName.ml`, `LeanKeywords.ml`).

## 8. Transferable to a Python→Lean verifier

Ranked by expected payoff for our SSA-IR bridge.

1. **Split totality into two logics and define both from one fixed-point
   theory.** Adopt Aeneas's `DWP` (least fixpoint, divergence = `False`) for
   total specs and `DWLP` (greatest fixpoint) for partial specs
   (`backends/lean/Aeneas/Std/WP.lean:48-64`,
   `Data/Coinductive/ITreeWP/DWP.lean`, `DWLP.lean`). Our all-fuel
   `returned/fellThrough/outOfFuel` certificates are a *syntactic* variant of
   the same idea; making `outOfFuel` the bottom of an order and proving `total ⇒
   partial` once (`DWP.toPartial`) would remove per-program fuel plumbing from
   every theorem.
2. **Emit `partial_fixpoint`, not `partial`, for recursive IR interpreters.**
   `partial` blocks unfolding and hence reasoning; `partial_fixpoint` gives
   definitional unfolding plus a fixpoint-induction principle, with admissibility
   discharged by an attribute-indexed tactic (`Tactic/Step/DspecInduction.lean`,
   `@[dspec_admissible]`). This directly addresses if/while certificate
   ergonomics.
3. **Make the WP layer the *interface*, not the semantics.** Aeneas generates
   executable definitions, then proves `spec_ok`/`spec_fail`/`spec_bind`/
   `spec_mono` simp lemmas once (`WP.lean:100-200`) so users never unfold
   `Result`. For our Lean oracle, provide the same small, `simp`-annotated rule
   set keyed on the IR's outcomes — it is what makes `step`-style automation
   possible.
4. **Adopt the `@[step]` spec-database pattern with a `step*?` script printer.**
   180 std lemmas make library calls transparent (`backends/lean/Aeneas/Std/**`,
   `Tactic/Step/StepStar.lean`). For Python: one registered spec per
   builtin/`int`/`list` operation, plus a script-generating variant so users can
   review and then re-automate proofs.
5. **Model containers as list-like structures with explicit bounds, not
   axioms.** `Array α n = ListN α n.val`, `Slice` = `ListN` + `length ≤
   Usize.max`, `Vec` wraps `Slice` (`Std/Array/Array.lean:26`,
   `Std/SliceDef.lean:10`, `Std/Alloc/Vec.lean:28`) — exactly the discipline that
   lets exact-`Rat`/`Float` backends coexist with proof-friendly list lemmas
   (`simp_lists`). Note their positivity workaround (issue #1138), worth
   mirroring if the SSA IR is a Lean inductive.
6. **Give every generated arithmetic fact an `_equiv` + a `_bv_spec`, and derive
   tactics from them.** Aeneas proves `UScalar.add_equiv`/`add_bv_spec` per
   operation (`Std/Scalar/Ops/Add.lean:43-100`) and `scalar_tac` consumes the
   `*_spec` family. Our exact `Rat` and IEEE-754 `Float` backends need the same
   two-tier lemma shape (value-level + bit-level) or automation will not fire.
7. **Turn the trust boundary into a checked artifact.** Aeneas mostly relies on
   "generated code typechecks and specs replay", plus stale-artifact CI checks
   (`ci.yml diff_lean_files`, `make extract-lean-std`). Our explicit trust docs
   are stronger; add their *automation*: a CI job that (i) rejects
   `axiom`/`sorry` in generated output, (ii) reproduces model tables from the
   Lean source and diffs them, (iii) pins the frontend with forward/merged
   checks (`scripts/ci-check-charon-pin-is-*.sh`).
8. **Use the differential interpreter as a first-class CI mode, but know its
   limit.** `-test-units` runs a concrete interpreter over zero-argument
   functions (`src/interp/Interp.ml:695`) and `-borrow-check` runs the symbolic
   pass with synthesis disabled (`src/BorrowCheck.ml:14-30`). Our
   CPython-vs-IR-vs-Lean triple differential is strictly stronger; keep it, and
   add Aeneas's *negative* testing habit — committed `known-failure` `.out`
   files make "we correctly reject this" a regression test
   (`tests/src/raw_pointers.lean.out`, `tests/README.md:72-86`).
