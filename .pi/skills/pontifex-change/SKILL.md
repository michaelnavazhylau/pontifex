---
name: pontifex-change
description: Safely change Pontifex language features, lowering, IR, emission, schemas, or regression tests. Use for Python/Lean compiler changes and verification-boundary reviews.
---

# Change Pontifex without missing a layer

Repository root is `../../..` from this skill directory. Resolve the root once;
run commands there. Do not load every reference or the entire roadmap.

## Locate and reuse

1. Run `uv run --locked --no-sync python scripts/pontifex_workflow.py lookup`.
   Pick the relevant feature(s); `lookup --feature NAME` returns live symbol
   locations, test modules, policy documents, and hazards. Missing symbols are
   index drift, not permission to invent an alternate implementation.
2. Read the nearest implementation and regression example. For a new feature,
   read `references/change-map.md` (relative to this skill directory).
3. Reuse `compile_source`/`compile_file`, `run_lean`, `observe_python`, and
   `compare_outcomes` from `python/pontifex/pipeline.py`. Reuse `check_lean` from
   `python/tests/lean_helpers.py` for kernel tests. Extend shared infrastructure
   instead of importing helpers from unrelated test modules.
4. Keep CPython, IR interpretation, Lean reference semantics, generated
   executables, and independent domain specs independent. Shared transport/test
   setup is good; making both sides call the same evaluator defeats the check.

## Implement deliberately

- Trace the feature through surface validation/desugaring → Source → IR →
  lowering → interpreters → independent certified emission → JSON/relocation.
  Not every change needs every layer; explicitly identify the applicable ones.
- Preserve eager/lazy evaluation and first-failure order, unused eager arguments,
  fresh frames, parallel phi copies, early returns, all outcomes, and structured
  fuel. Never move a call out of a short-circuit or repeatedly evaluated condition
  just to bypass rejection.
- Check `python/pontifex/version.py` and `Pontifex/Core/Config.lean` together if
  serialized semantics change. Test rejection of old artifacts in both decoders.
- Add a regression that fails on reversion. Language growth normally needs
  positive tests, located rejection snapshots, differential cases, valid
  certificates, and kernel rejection of corrupt Source/IR/executable evidence.
- Add corpus programs through `corpus/manifest.json`; use existing runners.
  Review changes to rejection diagnostics and NaN allowlists explicitly.
- Keep native sample checks in `NativeTests.lean` / `PontifexNativeTests`,
  separate from certificates and their imports; labels alone are not exceptions.
- Edit generators, never committed generated outputs. Explicit regeneration:
  `uv run python scripts/generate.py`. Refresh rejection snapshots only after
  reviewing the diagnostic change with `scripts/update_rejections.py`.

## Validate and report

1. Plan a focused run with explicit `--feature NAME` flags. `focused` defaults
   to `core`, not automatic dependency inference. It builds Lean before tests.
2. Run focused validation while iterating; run `--profile full` before claiming
   complete project verification. Full logs and the report live in `.pi/state/`.
   Do not infer Python-only tests from `-m "not slow"`.
3. Update `docs/TRUST.md` when behavior or claims change; update feature-specific
   docs and roadmap status as appropriate. Do not claim source-preservation or
   native IEEE proofs from differential tests or definitional tier lemmas.
4. Report changed files, exact validation scope, failures/skips, and remaining
   obligations. `status` must be current for a cached report to be evidence.
   Full project verification includes Node guard/bridge tests but excludes separate
   lint and Pi TypeScript load tests;
   see the report's explicit coverage and `docs/AGENT_WORKFLOW.md`.
