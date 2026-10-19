# Charon — technical review

> Captured from a fresh-context read-through of
> <https://github.com/AeneasVerif/charon>, shallow clone at commit `3f821f7`
> (Charon `0.1.293`, pinned toolchain `nightly-2026-09-17`). Claims were
> spot-checked by the parent against the clone; line and path references are
> relative to that commit. This is a reading record, not an independent
> verification of the project.

## 1. Purpose and position in the Aeneas ecosystem

Charon is a **rustc driver that dumps a whole crate (plus reachable
dependencies) into a uniform, semantic IR**, serialized as JSON/postcard
(`README.md:11-20`, `charon/src/export.rs:12-25`). It exists to *centralize* the
"extract usable facts from compiler internals" problem so each downstream
verifier does not re-solve it (`README.md:44-50`,
`docs/what_charon_does_for_you.md`).

It is the **front half of a pipeline**, not a verifier. Input = a Cargo package
(or a single `.rs`, subcommand `Rustc` in `charon/src/bin/charon/cli.rs:9-20`).
Output = `CrateData { charon_version, translated: TranslatedCrate, has_errors }`
(`charon/src/export.rs:12-25`), containing `type_decls / fun_decls /
global_decls / trait_decls / trait_impls` plus names, ordered declarations,
source files and a span table (`charon/src/ast/krate.rs:36-130`).

Consumers are explicit in the source: the `Preset` enum contains `Aeneas`,
`Eurydice`, `Soteria`, `Tests`, `RawMir`, `Fast`, `OldDefaults`
(`charon/src/options.rs:430-443`) — the output shape is tuned per consumer by
flag presets. `charon-ml/` is a first-class OCaml binding tree
(`charon-ml/src/CharonVersion.ml`, `charon-ml/src/Charon/src/generated/`), which
is what Aeneas uses; Rust consumers use
`serde_json::from_reader::<charon_lib::export::CrateData>(file)`
(`README.md:33-36`). Charon is thus a **serialized-API project** whose real
contract is the `.llbc` schema.

## 2. IR design: LLBC

Two bodies of the same language (`charon/src/ast/bodies.rs:36-80`): **ULLBC**
(*Unstructured LLBC* — CFG; "cleaned-up MIR",
`charon/src/ast/bodies/unstructured.rs:1-2`) and **LLBC** (*Low-Level Borrow
Calculus* — structured; default, reconstructed from ULLBC by one pass,
`transform/control_flow/ullbc_to_llbc.rs`). `Body` also has `Extern`,
`Intrinsic`, `Opaque`, `Missing`, `Error`, `TargetDispatch` variants — a body is
*always representable*, even when translation failed.

**CFG form.** `BlockData { statements: Vec<Statement>, terminator: Terminator,
kind: UnwindKind }` (`ast/bodies/unstructured.rs:32-40`); entry is always block 0
(`START_BLOCK_ID`, `:20-22`). `TerminatorKind` = `Goto | Switch | Call{target,
on_unwind} | Drop | InlineAsm | Assert | Panic | UnwindTerminate | UnwindResume |
Return | UndefinedBehavior` (`:89-157`). **Unwinding is a first-class CFG edge**
(`UnwindKind::{Regular,Cleanup,Terminate}`, `:42-53`), which is why every
call/assert/drop carries an `on_unwind` target.

**Structured form.** `Block { span, id, statements }`
(`ast/bodies/structured.rs:25-34`) and `StatementKind` merges MIR statements
*and* terminators (`:46-131`): `Assign`, `StorageLive/Dead`, `PlaceMention`,
`Borrowck`, `Drop{on_unwind}`, `Assert`, `Call{on_unwind}`, `Switch{data,
branches: IndexVec<BranchId, Block>}`, **`Loop(Block)`**, **`Break(usize)`**,
**`Continue(usize)`**, `Panic`, `UnwindResume`, `Return`, `UndefinedBehavior`,
`Nop`. `break`/`continue` take an **inside-out de Bruijn depth** (`:108-120`), so
multi-level breaks are O(1) rather than labelled.

**Rust feature mapping.**

- `loop` → `Loop`; `while c { b }` → `Loop { Switch(c) { true → b; continue 0,
  false → break 0 } }` (see `charon/tests/ui/control-flow/loops.out`, which
  reproduces `while i < max` from `control-flow/loops.rs:6`).
- `for x in it` is **not** a construct: rustc desugars it to `loop { match
  Iterator::next(&mut it) { … } }`, so LLBC shows a loop over a trait-method
  call.
- `match` → `Switch` over `SwitchScrutinee::Discriminant(place)`
  (`ast/bodies.rs:135-145`) with `branches: Vec<(ConstantExpr, BranchId)>` and
  optional `fallback`. Shared early blocks mean `E1::V1 | E1::V2 => {}` appears
  as one branch shared by two constants (`charon/tests/ui/matches.out:49-60`).
- Early `return` → explicit `Return` statement; a `duplicate_return` pass clones
  return blocks so reconstructed `break`s stay clean
  (`transform/control_flow/duplicate_return.rs`).
- `while`/`loop`/`for` distinction is **deliberately erased**
  (`docs/limitations.md`, "By-design limitations"): only semantic info is kept.
- **Closures** become *real items*: a struct of upvars + up to three
  `Fn`/`FnMut`/`FnOnce` impls and `call`/`call_mut`/`call_once` methods
  (`bin/charon-driver/translate/translate_closures.rs:1-40`). Function items
  reuse the same generated impls with an empty state.
- **Drops** are `DropKind::{Precise, Conditional}` (`ast/bodies.rs:251-274`).
  `Precise` is a call to `<T as Destruct>::drop_glue(&mut place)`; `Destruct` is
  a trait Charon *injects* so drop code is trackable in polymorphic code. MIR
  `built` gives `Conditional` drops; `--precise-drops` re-runs at
  `elaborated`/`optimized`; `--desugar-drops` rewrites drops into ordinary calls
  (`transform/normalize/desugar_drops.rs`).

## 3. Ownership, borrowing, lifetimes: model vs proof

This is the sharpest difference from PL verifiers: **Charon does not implement a
borrow model, and does not prove anything.** It *re-exports* rustc's
borrow-checker facts and *records* borrow-shaped structure.

- **Regions**: `Region::{Var(RegionDbVar), Static, Body(RegionId), Erased}`
  (`ast/type_level/regions.rs:11-20`). `Body` regions are **existentially bound
  per body** — `GExprBody.bound_body_regions: usize` (`ast/bodies.rs:118-121`) —
  with `--erase-body-lifetimes` as an opt-out. Lifetimes in *signatures* are
  structural data; lifetimes inside *bodies* are explicitly not planned
  (`docs/limitations.md`).
- **Borrowck statements**: `BorrowckStatement::{FakeRead, SetType{place,ty,
  variance}, SetOutlives(Ty,Region), PredicateHolds(PolyTraitRef)}`
  (`ast/bodies.rs:210-227`). These are *assertions the borrow checker made*,
  shipped as inert statements for downstream consumption. `--skip-borrowck`
  replaces `mir_borrowck` with `Default::default()`
  (`bin/charon-driver/driver.rs:64-73`), which shows Charon's own soundness does
  not depend on them.
- **Moves/copies**: `Operand::{Copy(Place), Move(Place), Const(ConstantExpr)}`
  (`ast/bodies/expressions.rs:83-90`); mutation is plain
  `Assign(Place, Rvalue)` with `Rvalue::Ref{place, kind, ptr_metadata}` for
  borrows; `WithRetag` on `Use` preserves Rust's retagging/aliasing model
  (`:17-19`, `:92-100`). Allocation lifetime is `StorageLive`/`StorageDead`
  (`ast/bodies/structured.rs:55-66`).
- **No loans, no permissions, no ghost state.** There is nothing like a
  `Borrow`/`Loan`/`Permission` type in the AST. The concrete "who owns what"
  separation is done downstream (Aeneas). What Charon *does* model is **safety
  preconditions**: `Safety::{Safe, Unsafe, Unknown(reason)}` and `HasSafety`
  compute, per operation, whether it requires `unsafe`
  (`ast/bodies/safety.rs:10-22`, `:69-110`) — a *model of obligations*, not a
  proof.

Charon is a **translation + fact-extraction layer**; the "borrow calculus" of
the name is realized in Aeneas's formalization, not here.

## 4. Type system handling

`Ty` is a **hash-consed interned** wrapper around `TyKind`
(`ast/type_level/types.rs:11-16`); `TyKind` covers `Scalar, Array, Slice, Adt,
Ref, RawPtr, FnDef, FnPtr, DynTrait, Pattern, Never, TypeVar, TraitType,
PtrMetadata, Error` (`:22-97`). `FnDef` is notable: a function *item* gets its own
ZST type with a `RegionBinder<FnPtr>` for late-bound lifetimes (`:50-70`).

- **Generics**: `GenericParams { regions, types, const_generics, trait_clauses,
  regions_outlive, types_outlive, trait_type_constraints }` and mirror-image
  `GenericArgs` (`ast/type_level.rs:23-78`). Binding is explicit via
  `RegionBinder<T>` / `Binder<T>` with a `BinderKind` discriminator (`:96-135`),
  and visitors carry a binder stack (`transform/typecheck_and_unify.rs:39-45`).
- **Traits / "trait proofs"**: every trait obligation is materialized as a
  `TraitRef` with a `TraitRefKind` explaining *how it was proven* —
  `TraitImpl(ref)`, `Clause(dbvar)`, `ParentClause`, `ItemClause`,
  `BuiltinOrAuto`, … (`ast/type_level/trait_proofs.rs:10-25`, `:39-100`, each
  with an ASCII worked example). Trait methods are called through
  `FnPtrKind::Trait(trait_ref, method_id)` so a call site names both the method
  and the proof of the bound.
- **Monomorphization**: `--monomorphize` plus `hax::FullDef` instantiated at
  concrete `GenericArgs`, which substitutes and normalizes so results match
  rustc (`docs/internals/hax.md`). `--monomorphize-mut` does *partial*
  monomorphization so that no item is ever instantiated at a type containing
  `&mut` (`transform/normalize/partial_monomorphization.rs:1-12`) — a
  divergence-shaped transformation introduced specifically for Aeneas.
- **Associated types**: `--lift-associated-types=<pat>` rewrites `trait
  Iterator { type Item }` into `trait Iterator<Item>` plus a fresh type parameter
  at each use (`docs/transformations.md`), implemented by
  `transform/normalize/expand_associated_types.rs`; the doc lists five known
  limitations (GATs, recursive traits, `dyn Trait`, bound lifetimes, no
  impl-unicity reasoning).
- **`dyn`**: `TyKind::DynTrait(DynPredicate)`; each `TraitImpl` carries a
  `VTableDecl` (`ast/items/trait_impl.rs:79-86` — `NotDynCompatible | Lazy |
  Computed | Unsupported(reason)`), and `transform_dyn_trait_calls` turns `dyn`
  calls into vtable fn-pointer calls.
- **Opaque/external**: a 4-level opacity lattice — *Transparent / Foreign /
  Opaque / Invisible* (`charon/src/ast/meta.rs:191`), resolved by a name-pattern
  matcher with "most specific pattern wins"
  (`charon/src/name_matcher/mod.rs:51-125`, `:189-221`).
- **User annotations**: `#[charon::opaque]`, `#[charon::exclude]`,
  `#[charon::rename("…")]`, `#[charon::variants_prefix/suffix]`,
  `#[charon::transparent]`, `#[charon::contract(kind=…, for=…)]`
  (`ast/meta/attrs.rs:22-52`). Source annotations can only *increase* opacity,
  never decrease (`docs/what_charon_translates.md`, footnote 2 →
  `translate_meta.rs:776-785`). `--start-from-attribute` lets an attribute serve
  as the entry-point selector.

## 5. Trust and validation

Charon publishes its trust story rather than only its tests. `docs/faq.md`
("How much can I trust what Charon outputs") states: function-body semantics are
the **most** reliable (near-verbatim MIR, executed against MiniRust's test suite,
and interpreted/compared against Miri by Soteria); **lifetime generics are the
least** reliable (most Charon-specific reasoning); **layout guarantees are
computed by Charon itself** from the Rust Reference. `docs/minirust.md` declares
the MiniRust translation in `charon/src/minirust.rs` to be the **authoritative
semantics** of the IR — an unusually honest move — and also lists what is
"translated unsoundly" (pointer-to-static offset, `#[track_caller]`, union
padding).

Assumes vs checks: Charon assumes rustc's MIR, trait solving and const-eval are
correct; it *checks* its own invariants twice with `typecheck_and_unify::Check`
(`PostTranslation` and `PostTransformation`, `transform/mod.rs:110-113`, `:301`),
reporting violations through `register_error!`/`raise_error!`
(`charon/src/errors.rs:17-50`) with a partial `.llbc` still emitted
(`export.rs:137-146`).

**rustc coupling** is total and honest: pinned nightly + `rustc-dev`
(`rust-toolchain:1-3`), rustc internals isolated behind a `hax` façade whose
entrypoint `FullDef` "marks the boundary of rustc versus Charon"
(`docs/internals/hax.md`), plus `set_mir_options()` forcing `always_encode_mir`,
`mir_opt_level=0`, `mir_preserve_ub`, and disabling `CheckAlignment`/`CheckNull`
(`bin/charon-driver/driver.rs:28-46`) — the underlying MIR is *deliberately* not
what `cargo build` produces. The schema is versioned by exact string equality:
`CharonVersion::deserialize` errors unless `version == crate::VERSION`
(`export.rs:56-72`), and `docs/versioning.md` says the patch number is bumped on
*every* AST change with no semver.

**Test strategy** (six kinds):

1. 486 snapshot UI tests, each `.rs` → pretty-printed `.out` in CI
   (`charon/tests/ui.rs:1-12`), with magic comments `//@ ignore`,
   `//@ known-failure`, `//@ known-ub`, `//@ revisions=` (`ui.rs:33-64`).
2. `cargo` integration tests with hand-built project fixtures
   (`charon/tests/cargo.rs`, 19 cases).
3. `crate_data.rs` unit tests over `TranslatedCrate` structure.
4. **Differential** layout fuzz test under `-Zrandomize-layout` with 10 seeds,
   checking Charon's computed layout guarantees against rustc's chosen layouts
   (`charon/tests/fuzz_layout.rs:1-16`).
5. `popular-crates.rs` — translate the **top 500 crates.io crates**, with two
   explicit, commented blocklists `BUILD_FAILURES` / `CHARON_FAILURES`
   (`:22-45`).
6. `minirust.rs` runs MiniRust's own `minimize` pass/UB suite through Charon,
   with a skip list and a per-failure allowlist.

Failure modes when rustc moves are caught as *snapshot diffs* plus a pinned
toolchain that makes upgrading a deliberate act.

## 6. Engineering

Rust, as a `rustc_private` driver following clippy's architecture: `charon`
shells out to `cargo` with `RUSTC_WRAPPER=charon-driver` and passes its own
options through the `CHARON_ARGS` env var as JSON (`bin/charon/main.rs:1-30`,
`options.rs:16-18`; driver entry `bin/charon-driver/main.rs:150`). Subcommands:
`Cargo`, `Rustc`, `UiTest`, `PrettyPrint`, `PrintSysroot`,
`ToolchainPath/Version` (`bin/charon/cli.rs:11-30`). A full-MIR sysroot is built
via Miri so std bodies are available (`bin/charon/main.rs:117-125`, `:278-290`).

- **Serialization**: `serde` + `serde_state`, with a `DedupSerializer` state that
  deduplicates types/trait-refs into a shared table (`export.rs:27-44`),
  disableable via `--no-dedup-serialized-ast`; formats `json | postcard |
  minirust | all` (`options.rs:476-490`); deserialization disables serde's
  recursion limit and grows the stack with `serde_stacker`
  (`export.rs:163-172`).
- **Pass architecture**: ~60 micro-passes in 7 categories
  (`transform/mod.rs:1-60`), each a tiny `TransformPass`/`UllbcPass`/`LlbcPass`
  impl with `should_run(options)` gating (`transform/ctx.rs:26-107`; `:97-107`
  lets a pass declare prerequisites, e.g. "required declaration found"). Bodies
  are processed **fused** — all passes in a batch run per body before moving to
  the next body, with `apply_preceding_passes` so inlining passes can replay
  earlier passes on pulled-in bodies (`transform/mod.rs:307-345`). The ordered
  pipeline with per-pass justification comments is `transform/mod.rs:93-300`.
- **Self-hosting codegen**: `generate-asts` runs Charon **on Charon itself**
  (`--features charon_on_charon`, `--start-from=charon_lib::ast::krate::
  TranslatedCrate`) and generates the OCaml AST types plus
  `OfJson`/`OfPostcard` deserializers into `charon-ml/src/generated/`
  (`bin/generate-asts/main.rs:14-46`, `bin/generate-asts/generate_ml.rs:1-10`).
  `#[cfg_attr(feature="charon_on_charon", charon::rename(...)/opaque/...)]`
  attributes appear on nearly every AST node purely to steer that
  self-translation.
- **Names**: `Name { name: Vec<PathElem> }` where `PathElem ∈
  {Ident(String, Disambiguator), Impl(..), Instantiated(Binder<GenericArgs>),
  Target(..), Builtin(..)}` (`ast/meta/names.rs:24-39`, `:131-133`) — so name
  matching uses real syntactic structure rather than string prefixes. Short
  names and a topologically sorted `ordered_decls` with `NonRec`/`Rec` SCC
  grouping are computed for consumers that need stable order
  (`ast/krate.rs:120-126`, `transform/add_missing_info/reorder_decls.rs:1-10`).
- **Performance**: explicitly not a goal (robustness over speed, `docs/faq.md`),
  with an escape hatch `--preset fast` disabling typecheck, normalization, CFG
  reconstruction and layout guarantees (`options.rs:551-559`).

## 7. Limitations and design decisions to copy / avoid

**Copy:** the ULLBC/LLBC duality with one reconstruction pass and a
`--no-code-duplication` escape; `Body::Error`/`Missing`/`Opaque` so partial
output is always valid; the dual typecheck (pre/post passes);
MiniRust-as-authoritative-semantics; the two-blocklist popular-crates test; the
self-hosting OCaml codegen; the opacity lattice + name patterns; "one pass, with
`should_run` gating and documented ordering".

**Avoid / be careful with:**

- *Irreducible* CFGs are a hard failure — `ullbc_to_llbc` returns
  `Err(Irreducible(block))` and then `panic!("can't reconstruct irreducible
  control-flow")` (`transform/control_flow/ullbc_to_llbc.rs:167-169`,
  `:1338-1348`); the doc admits the algorithm's complexity is "probably very
  bad" (`:5-13`).
- Structured output **duplicates code** by default; `--no-code-duplication` uses
  Beyond Relooper which "consumers which expect `if`/`loop`-shaped bodies (e.g.
  aeneas) may not support" (`options.rs:39-46`).
- `async` is unsupported (`docs/introduction.md:22`).
- The Rust and OCaml name matchers diverge (`docs/usage.md`, issue #319).
- `--lift-associated-types` has five documented holes.
- The extensive flag surface + presets means the "same" crate can produce
  mutually incompatible IRs, mitigated only by shipping `options` inside the
  output for consumers to assert on (`ast/krate.rs:44-46`).

## 8. Transferable to a Python→Lean verifier

Ranked by expected payoff for our pipeline.

1. **Add an explicit "trust boundary" module and a semantics-authority
   document.** Charon isolates every rustc query behind `FullDef`
   (`docs/internals/hax.md`) and names `src/minirust.rs` as the authoritative
   semantics, with an explicit "translated unsoundly" list (`docs/minirust.md`).
   We already have trust docs; promote them to one file per assumption matching
   one code directory, plus a *conformance suite* — MiniRust's `minimize` suite
   played that role (`charon/tests/minirust.rs`). Concretely: run CPython's own
   `test/` subset (or a Hypothesis corpus) through CPython → IR interpreter →
   Lean oracle and diff all three, in CI, with a per-failure allowlist file
   rather than silent skips.
2. **Adopt the ULLBC → LLBC split: keep an unstructured IR as the canonical
   target of lowering, and make structuring a separate, optional, verifiable
   pass.** Straight-line `rfl` linkage is naturally a property of the
   *unstructured* IR, and `if`/`while` certificates are naturally a property of
   the *structured* IR. Charon does exactly this and gives a fallback (emit
   ULLBC, i.e. `--ullbc`) when structuring would be unsound or ugly
   (`transform/control_flow/ullbc_to_llbc.rs`;
   `docs/output-choices/control-flow.md`). A while-loop certificate quantifying
   over the whole environment maps cleanly onto "structured IR is a *view* over
   a CFG whose semantics you already have".
3. **Totalize the IR: give every program point an outcome lattice including
   unwind/abort.** Charon's terminators always carry `on_unwind`; aborts are a
   3-way `AbortKind::{Panic, UndefinedBehavior, UnwindTerminate}`
   (`ast/bodies.rs:237-244`); loops/breaks are explicit. Our
   `returned/fellThrough/outOfFuel` triple is the same idea; extend it with an
   explicit *exceptional* outcome and a distinguished "stuck/UB" outcome, and
   make every IR statement's semantics return that 4-tuple instead of leaving
   panics as an unmodelled Lean `Option`.
4. **Materialize "how each obligation was discharged" as data, not as proof
   search.** `TraitRefKind` (`ast/type_level/trait_proofs.rs:39-100`) records
   `TraitImpl | Clause(dbvar) | ParentClause | ItemClause | BuiltinOrAuto` with
   worked examples. For Python, for every runtime check the IR inserts (bounds,
   `ZeroDivisionError`, `KeyError`, attribute existence), record a
   `CheckWitness` naming the static fact that justifies it, or `Dynamic` if it
   must be checked at runtime. Then Lean proves *per witness kind* once instead
   of re-deriving per program, and the `rfl` certificates stay small.
5. **Introduce an opacity lattice + name patterns instead of one big "supported
   subset" predicate.** The four levels (`Transparent/Foreign/Opaque/Invisible`,
   `ast/meta.rs:191`) with "most specific pattern wins" over structural names
   (`ast/name_matcher/mod.rs:51-125`) is how a mature tool survives a language
   far bigger than its semantics. For Python this is the difference between "we
   support a subset" and "we support everything, with three grades of fidelity
   per module/function/class" — exactly what you want when a `pandas` call shows
   up in an otherwise-verifiable function. Attach the chosen opacity per item to
   the artifact so the Lean side can assert "no Opaque node was reached in the
   verified path".
6. **Fuse passes and gate them with declared prerequisites.**
   `UllbcPass::should_run(&options)` plus `apply_preceding_passes`
   (`transform/ctx.rs:26-107`, `transform/mod.rs:307-345`) lets Charon keep ~60
   transformations correct by construction. If the Python frontend grows a
   desugaring/normalization chain, copy the *shape*: one trait, `should_run`
   predicates (which double as documentation of ordering constraints), and a
   single ordered list with a comment justifying each position
   (`transform/mod.rs:93-300`).
7. **Bake a cheap, high-signal differential test on representation.**
   `fuzz_layout.rs` compares Charon's own derived layout guarantees against
   rustc under `-Zrandomize-layout` with 10 seeds. Our `Rat`/`Float` backends
   have an exact analogue: randomized differential testing of (CPython result,
   IR interpreter result, Lean `decide`/`native_decide` result) on arithmetic
   expressions, including NaN payloads, signed zeros, `-0.0 == 0.0`, and
   `Fraction`/`int` promotion. One test file, high seed count, small fixed
   regression corpus.
8. **Publish the serializer version as an exact-match string and stamp the
   config into the artifact.** `CharonVersion` refuses to deserialize unless
   versions are exactly equal (`export.rs:56-72`), and
   `TranslatedCrate.options: CliOpts` is embedded so consumers can assert the
   flags they need (`ast/krate.rs:44-46`). Make the Lean artifact carry
   `(ir_version, rat_mode, float_mode, fuel_policy)` and have Lean `#guard`
   assert them, turning "we changed a flag and the proof silently weakened" into
   a build error.
