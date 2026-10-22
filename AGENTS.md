# Pontifex agent guide

Pontifex is a restricted Python → SSA IR → Lean bridge. Start with targeted
symbol lookup, not a full README/TODO dump:

```bash
uv run --locked --no-sync python scripts/pontifex_workflow.py lookup
uv run --locked --no-sync python scripts/pontifex_workflow.py lookup --feature calls
```

- Language/compiler changes: load `.pi/skills/pontifex-change/SKILL.md`.
- Lean/spec work: load `.pi/skills/pontifex-proof/SKILL.md`.
- Reuse `pontifex.pipeline` compilation/oracle/comparison helpers and
  `python/tests/lean_helpers.py`; keep executable code and reference evaluators
  independent. Do not DRY away correctness oracles.
- Never hand-edit `Pontifex/Generated/`, `Pontifex/Generated.lean`,
  `Pontifex/Audit.lean`, `NativeTests.lean`, or generated `build/ir/*.json`. Change the generator,
  then explicitly run `uv run python scripts/generate.py`.
- No `sorry`, new axioms, or `native_decide` in correctness certificates.
  Native samples belong only in `NativeTests.lean` / `PontifexNativeTests`;
  never import that test module from the certificate library. Finite sample
  checks are not proofs of universal correctness.
- Preserve full outcomes, structured fuel, failure/evaluation order, and raw
  binary64 bits. Parsing/transcription and native arithmetic remain tested trust
  boundaries; consult `docs/TRUST.md` only as needed.
- Validate with `scripts/pontifex_workflow.py`: `plan`, then `validate`, with
  `--profile freshness|focused|full`. Focused accepts repeated `--feature`.
  Missing/skipped coverage is incomplete; never claim full verification from a
  focused run or stale report. `status` checks report fingerprints.
- `make check` does not regenerate. `make fmt` only formats; `make lint` is
  separate. Do not refresh rejection snapshots or broaden allowlists to hide
  regressions. Run `node --test .pi/tests/pontifex.test.mjs` for Pi guard/bridge tests.

Setup: `uv sync --locked --all-groups`; `lake build`. Pi usage and coverage:
`docs/AGENT_WORKFLOW.md`.
