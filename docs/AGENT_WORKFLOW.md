# Token-efficient project workflows

This integration supplies two lazy-loaded skills, one small Pi tool, generated-file
accident guards, and a reusable Python workflow runner. No model calls, agents,
embedding service, or npm installation are used by the implementation.

## Setup and discovery

```bash
uv sync --locked --all-groups
lake build
# Full validation also needs Node 20+ for the Pi guard/bridge tests.
```

Start Pi at the repository root, review/grant project trust, and run `/reload`
if the session predates these files. `.pi/settings.json` adds codemode without
replacing your tool selection. Pi discovers `.pi/extensions/pontifex/index.ts`
and both `.pi/skills/*/SKILL.md` files automatically. The host provides TypeBox
and the Pi API; do not install a second runtime copy in the project.

- `/skill:pontifex-change` — compiler/language/schema/test changes.
- `/skill:pontifex-proof` — proof routing, specs, and reduction-cost debugging.
- `/pontifex lookup` — available feature routes.
- `/pontifex lookup calls` — live symbols, tests, policy references, hazards.
- `/pontifex plan focused calls,selection` — inspect commands before execution.
- `/pontifex validate focused calls,selection` — build dependencies and test a slice.
- `/pontifex validate full` — complete local project verification profile.
- `/pontifex status` — inspect the most recent report and its fingerprint.

Slash commands display deterministic results without triggering a model turn.
The optional tool has `codemode` exposure so its full schema is not permanently
declared to the model. For example, from codemode:

```js
text(await tools.pontifex_workflow({
  action: "plan", profile: "focused", features: ["calls", "selection"]
}));
```

The tool supports `plan`, `validate`, `status`, and `lookup`. `lookup` accepts
at most one feature; omit it to list routes. The same implementation works without Pi:

```bash
uv run --locked --no-sync python scripts/pontifex_workflow.py lookup --feature calls
uv run --locked --no-sync python scripts/pontifex_workflow.py plan --profile focused --feature calls
uv run --locked --no-sync python scripts/pontifex_workflow.py validate --profile full
uv run --locked --no-sync python scripts/pontifex_workflow.py status --json
```

## Validation scope

| Profile | Gates |
|---|---|
| `freshness` (default) | Ruff format check; schema/generated-artifact freshness; rejection-snapshot freshness |
| `focused` | Freshness; `lake build` (including axiom audit); local runner prerequisite; explicit feature test modules |
| `full` | Freshness; build/audit; local runner; kernel replay with `lake env leanchecker Pontifex`; separate `PontifexNativeTests` target (finite tests, not proofs); 32-sample differential corpus; default 100,000-pattern Float boundary corpus; Node guard/bridge tests; all pytest tests |

Focused defaults to `core`. Repeat `--feature` to union test modules. The index
is a navigation aid, **not** automatic dependency analysis or evidence that no
other test can be affected. Never interpret `-m "not slow"` as Python-only:
some integration tests have no slow marker.

A passing profile is not necessarily full verification. `full_verified` can be
true only for a passing full run. This means the local project profile, **not**
the multi-version CI matrix or higher-volume nightly sampling. Lint is separate;
Node guard/bridge tests are included in full and can also be run independently:

```bash
make lint                                  # lint is distinct from formatting
node --test .pi/tests/pontifex.test.mjs      # Node 20+, also included in full
```

Pi guard/bridge tests also run in CI's Python workflow. They do not replace an
actual Pi extension load check: after changing its TypeScript API integration,
use `/reload` and confirm there are no extension diagnostics. Runtime loading
was smoke-tested during initial implementation. No model request is needed to
use `/pontifex lookup calls` after loading.

### Honest failures and coverage

- Validation never runs a generator in write mode. Source edits are not intended;
  builds, dependency/test caches, and ignored reports can be written. Tests and
  toolchain commands are trusted code, not a sandbox.
- `make check` now checks freshness **without** first regenerating. Use `make gen`
  explicitly. `make fmt` only formats; it no longer silently attempts lint fixes.
- Every subprocess has an explicit timeout, captured exit code, and complete log.
  Later gates are `NOT_RUN` after the first failure/incomplete gate.
- Missing tools, timeouts, cancellation, missing/malformed JUnit reports, skipped
  pytest tests, or an empty suite are incomplete evidence. Test/assertion failures
  remain failures. Pytest coverage is parsed from JUnit, not guessed from output.
- Build before invoking integration tests. External `PONTIFEX_EXE` overrides are
  rejected for focused/full runs unless they point to the local built runner.
- A source edit during validation invalidates the run. Validation is serialized
  across sessions with an OS file lock. The runner supports macOS/Linux; Node
  helpers are portable. Cancellation/timeout kills the active subprocess group.
- CLI exit codes: `0` successful profile or informational query, `1` failed gate,
  `2` incomplete evidence/invalid invocation. `status` is an inspection command:
  a `STALE` result is not a reusable success even though the query exits zero.

## Reports, fingerprints, and token budget

Each validation creates an ignored `.pi/state/run-*/` with full logs, pytest
JUnit XML, and `report.json`. `.pi/state/last.json` points to the latest run's
report contents, including its fingerprint. A pending run replaces an older
success with incomplete evidence before checks start. No reports are committed.

Reports identify profile, per-gate status, coverage, test counts, and log paths.
The Pi adapter bounds its summary to roughly 8,000 characters; full output stays
on disk. Failure diagnostics are bounded excerpts, never a substitute for logs.
Tool structured output has the same compact summary, status, `fullVerified`, and
optional profile/log path. UI rendering is not used as a substitute for reducing
model-facing content.

Fingerprints include tracked and non-ignored untracked source contents (including
lockfiles, schema/config, tests, and agent resources), platform, Python/dependency
versions, uv/Lean versions, executable paths, the built runner hash, and a hash of
the process environment. Environment values are not stored. `status` recomputes
this fingerprint; mismatches yield `STALE` and `full_verified: false`. The check
is deliberately conservative: environment changes can invalidate otherwise
usable evidence. Dependency caches and arbitrary filesystem state are not a
hermetic build guarantee. Validation always reruns; it does not skip checks based
on a stored success or silently reuse results from another scope.

## Generated-artifact protection

The extension intercepts built-in `edit`/`write` operations on:

- `Pontifex/Generated/**/*.lean`
- `Pontifex/Generated.lean`
- `Pontifex/Audit.lean`
- `NativeTests.lean` (finite native test module)
- `build/ir/**/*.json`

Relative paths, absolute paths, normalization, and symlink aliases are checked.
The error points to `scripts/generate.py`. Temporary corruption-test files outside
these directories remain writable. For an intentional exception, the operator
can run `/pontifex-allow-generated PATH` and confirm the dialog. This grants one
edit/write for that canonical file and expires at session change/reload/shutdown.
There is no model-callable unlock action; headless clients without a confirmation
UI cannot grant it.

These are **accident guards, not security enforcement**. Bash, custom filesystem
tools, external processes, hard links, and races can bypass tool-level guards.
Do not parse shell strings and pretend that constitutes comprehensive protection.

## Maintaining reusable knowledge

`AGENTS.md` contains only invariants and routing. Skills load detailed guidance
on demand; references point back to existing policy/specs instead of copying them.
`scripts/workflow_features.json` maps feature names to symbols, tests, docs, and
pitfalls. Line locations are calculated on lookup. `test_workflow.py` verifies
that every indexed symbol and path exists, and Node tests check feature-name
alignment with the Pi adapter.

Reuse `pontifex.pipeline` compilation, transport, and outcome comparison helpers,
and `python/tests/lean_helpers.py` for kernel invocations. Keep CPython, reference
semantics, independent generated executable blocks, and domain specifications
independent: deduplicating both sides into one evaluator weakens verification.
