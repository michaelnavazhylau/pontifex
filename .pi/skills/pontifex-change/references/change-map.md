# Cross-layer change map

Paths below are relative to the repository root, not this reference file.
Use symbol lookup/search to read bounded portions; this is a routing map, not
another copy of the implementation or trust policy.

| Concern | Python | Lean |
|---|---|---|
| Surface restrictions, entry points, helper hoisting | `python/pontifex/frontend.py`, `source.py` | `Pontifex/Core/Source.lean` (emitted core syntax, not the Python parser) |
| SSA nodes and JSON schema | `python/pontifex/ir.py`, `version.py` | `Pontifex/Core/IR.lean`, `Config.lean`, `Pontifex/Json.lean` |
| Lowering, frames, relocation | `python/pontifex/frontend.py`, `inline.py`, `source.py` | `Pontifex/Core/Lower.lean`, `Inline.lean` |
| Arithmetic and outcomes | `python/pontifex/interp.py` | `Pontifex/Core/Ops.lean`, `Semantics.lean`, `Error.lean`, `Refinement.lean` |
| Independent executable blocks and certificates | `python/pontifex/certify.py`, `emit.py` | Per-program generated modules; do not edit these by hand |
| Bit transport and native boundary | `python/pontifex/interp.py`, `pipeline.py` | `Pontifex/Core/Binary64.lean`, `FloatSpec.lean`, `Pontifex/Json.lean` |
| Artifact and audit manifests | `scripts/generate.py` (`EXAMPLES`, `EXAMPLE_FUNCTIONS`, `AUDIT_EXAMPLES`) | Generated umbrella module and `Pontifex/Audit.lean` |

## Reusable acceptance patterns

- `python/tests/test_selection.py`: cross-layer feature, eager/lazy faults,
  IEEE operand selection, schema rejection, and corruption rejection.
- `python/tests/test_calls.py`: private frames, transitive certificates,
  expression hoisting, and frontend boundaries.
- `python/tests/test_certificates.py`: independently emitted code checks,
  Source/IR/code mutations, and the long-block reduction-cost regression.
- `python/tests/test_failures_refinement.py`: failures, stuck, exhaustion, and
  small-fuel agreement (not just successful results).
- `python/tests/test_trust_gates.py`: axiom audit and sample/certificate separation.
- `tests/rejections/README.md`, `corpus/README.md`: corpus extension contracts.

For a new checked-in example, register it in `scripts/generate.py`; let the
script update generated Lean, JSON, umbrella imports, and certificate audits.
Handwritten public spec theorems need deliberate `AUDIT_EXAMPLES` registration.
Add/update `scripts/workflow_features.json` references if navigation changes;
`test_workflow.py` checks that referenced symbols and paths still exist.
