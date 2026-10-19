# Trust model and verification status

## What is (and is not) checked

```
Python file -- trusted parsing/transcription --> core Source AST
                                                    |
                          Source.lowerBody (Lean reference lowering)
                                                    |
                                         emitted SSA IR
                                          /         \
                               reference exec   compiled blocks
                                          \========= /
                                         kernel certificates
```

* `<fn>_lowering` checks **agreement** between the emitted IR body and the Lean
  reference lowering of the emitted Source AST, by `rfl`. There is no separate
  Source-language evaluator or semantic-preservation proof for that lowering.
  The lowering is a formal executable specification, not a verified compiler
  for all Python programs. Transcription/desugaring and fidelity of that
  reference lowering remain trust boundaries.
* `<fn>_program_lowering` composes that fact with the program lowering
  certificates of every white-box callee recursively. For call-containing
  programs, this is the complete lowering evidence: the caller's `_lowering`
  alone checks expansion of the referenced callee IR, not its source agreement.
  Inlining fidelity remains tested, not proved; see [CALLS.md](CALLS.md).
* `<fn>_compiled_link` checks code↔IR behavioral equivalence for every fuel,
  environment, and `Ops α`. Generated blocks do not call `exec`, `evalV`,
  `evalS`, or `evalC`; they independently emit operations, control flow, and
  phi copies.
  Parent certificates compose child certificates, with fuel induction for loops.
* Fallible arithmetic (division/power) uses the same certified backend even
  without control flow. It preserves all outcomes, not just successful results.
* Infallible straight-line code keeps the small direct `Rat`/tuple translation,
  with `<fn>_link := rfl` at a selected literal fuel. That function ignores its
  fuel parameter; its linkage theorem is **not** an all-fuel statement.
* Worked generated functions are linked to independent physics specifications.
  This verifies the modeled algorithms, not all behaviors of a Python runtime.

## P1 outcomes, refinement, and specs

`Outcome α` is now:

```
returned values | fellThrough env | failed Error | stuck | outOfFuel
```

`Error` currently includes `divisionByZero`, `overflow` (Float power), and
`indexOutOfBounds` (array access/update). `assertionFailure` remains reserved.
Undefined slots/phi predecessors yield `stuck`. Environments contain
`Option (Val α)` cells: gaps are uninitialized, never manufactured zeros.

`Outcome.Refines a b := a = outOfFuel ∨ a = b` is a **flat partial order with
bottom**, not a lattice. Distinct results have no common upper bound. Failures
and stuck states are stable observations, not approximations of success.

The kernel-checked `exec_mono` theorem says more fuel refines any run, for any
`Ops α`, IR statement, and environment. `exec_completed_stable` consequently
preserves returned values, fall-through state, failure identity, and stuck.
These are generic proofs, not finite test results.

* `TotalSpec`: some finite observation returns values satisfying the postcondition.
* `PartialSpec`: every observation either exhausts or returns values satisfying
  the postcondition; failures/stuck are forbidden.
* `total_to_partial` derives the latter from the former using refinement.

`Examples/FailuresAndRefinement.lean` includes a fuel-free zero-duration
free-fall specification, its total→partial corollary, a generated-code
monotonicity theorem, and rational division success/failure iff lemmas. General
positive-duration loop termination and physics error bounds remain separate
proof obligations; P1 does not establish them.

## Multi-exit returns

`return` may appear anywhere a statement is allowed, including inside `if`
branches and `while` bodies. This needed no change to the IR or its semantics:
`Seq` and the certified block composition already continue only on
`fellThrough`, so a `returned` result short-circuits the enclosing sequence,
branch, and loop (and skips the `if` merge / loop back edge) without a flag
slot or a CFG.

SSA merging is env-based. Only names whose binding differs between the paths
that can still fall through need a phi, so a branch that always returns
contributes no phi input; its side is a dead but defined placeholder (the
incoming value, else the other branch's slot). A loop variable assigned only on
a returning path is not loop-carried, because it never reaches the back edge.

The frontend additionally rejects unreachable statements after a
definitely-returning statement, functions that can fall through without a
return, and returns that disagree on arity. The per-program
`<fn>_lowering := rfl` certificate checks that the Lean reference lowering
computes the same merges and slot allocation; the generated code certificates
are unaffected because the outcome algebra was already right.

## Arrays

Slots hold a tagged value:

```
Val α := .scalar α | .array (List α)
```

There is no second environment and no reference model. Arrays therefore merge
through the existing `if` and loop `Phi` nodes, and `Outcome`, `exec`,
`Fn.run`, `exec_mono`, and `exec_completed_stable` keep their signatures. Length
is intrinsic to the `List`; there is no separate size slot to desynchronise.

The surface subset is one-dimensional list literals, `xs[i]`, `xs[i] = v`, and
`len(xs)`:

* `index` and `set` are bounds-checked. A fractional, negative, non-finite, or
  out-of-range index is `failed .indexOutOfBounds`; an array used where a scalar
  is required (or a scalar indexed) is `stuck`, but the frontend rejects that
  statically.
* `set` is a functional expression. `xs[i] = v` assigns it to a fresh slot for
  `xs`, so earlier bindings are unchanged. This is what keeps the IR alias-free.
  Array-to-array assignment, array parameters/returns, nested arrays, and
  augmented subscript assignment are rejected by the frontend.
* `len` returns `Ops.ofNat` of the list length, so it is a scalar in every
  backend.
* `set` evaluates its right-hand side first, then the array, then the index,
  matching Python's evaluation order for `xs[i] = v` (only the reported failure
  can differ otherwise).
* Static scalar/array kinds are tracked through `if` merges and loop bodies.
  A variable that changes kind across paths is rejected. This is a frontend
  restriction checked by tests, not a proved type system.
* `Ops.toIndex` is exact for `Rat`. In the Float/binary64 backends it accepts
  non-negative integral values up to `2^53` via native `Float.floor`/
  `Float.toUInt64`; that conversion is **tested**, not proved, and every
  rejection is the same defined bounds failure.

## White-box calls

The first T13 slice inlines module-local, straight-line single-scalar helpers
at complete assignment/return sites, with positional scalar arguments. It
preserves eager left-to-right evaluation in a private fresh-slot frame; unused
arguments and potentially failing dead callee assignments are retained. Caller
branches, loops, early returns, and arrays still use their existing paths.
Forward definitions and acyclic helper chains are supported, but recursive,
nested-expression, summary/opaque, array, tuple-result, and control-flow-callee
calls are deferred. See [CALLS.md](CALLS.md) for the precise subset.

Core Source `inlineCall` references independently emitted callee IR. Lean's
`Inline.expand` checks the expansion via the caller's `rfl` lowering fact;
`<fn>_program_lowering` additionally requires the callee's program certificate.
Existing code linkage then checks the expanded IR, without new runtime nodes
or a schema change. Axiom audits include every nested helper's certificates.
This is an executable reference algorithm with per-program agreement checks,
not a universal semantic-preservation theorem for inlining.

## Numeric readings and transport

See **[FLOAT_POLICY.md](FLOAT_POLICY.md)** for the precise boundary contract.

* `Ops.rat`: exact rationals, **not** the full real field. Float literals use
  their exact binary rational value in this reading.
* `Ops.float`: Lean's built-in native Float model.
* `Ops.binary64`: raw UInt64 boundary representation with numeric operations
  through built-in Float. This preserves identity/literal/sign bits even though
  Lean's Float model canonicalizes NaNs.
* Float wire mode uses hexadecimal bit strings in both directions, preserving
  signed zero, subnormals, infinities, and raw NaN payloads on identity transport.
* Division checks zero (including -0.0) before computing. Power is an explicit
  backend operation: exact rational power or native Float power with overflow
  mapped to a language failure. A failing base is evaluated even at exponent 0.
* Native rounding/libm equivalence is tested, **not proved**. Computed NaN
  sign/payload differences have a narrow, counted allowlist; finite differences
  and failure mismatches are never exempt.
* General Python integer coercions, huge integers, and mixed integer-only
  subexpressions are not modeled by a verified numeric tower. The exact and
  Float readings are deliberate scalar interpretations, not interchangeable
  claims about all accepted Python expressions.

Schema **3** covers tagged slot values (`Val`), array expressions, and the
array-index policy; schema-2 and schema-1 artifacts are intentionally rejected
and must be regenerated.

## Fuel convention

Both interpreters and certified code follow the same structured budget:

* zero exhausts immediately, even for return or a false loop;
* assign/skip/return/empty sequence need one positive level;
* a sequence cons with n+1 gives n to both its head and tail;
* an if gives n to its selected branch;
* a while gives n to its body and back edge.

Fuel is execution depth, not a shared instruction counter. Headers are
initialized before loop entry; back edges copy from a snapshot. Exhaustion is
not evidence of divergence. Partial correctness does not prove termination.

## Build-time trust gates

| Gate | Mechanism |
| --- | --- |
| Schema drift | stamped config, Lean `#guard`, generator Python/Lean cross-check, JSON decoder version check |
| Axiom leakage | generated `Audit.lean` audits all lowering/linkage certificates and P1 core/example theorems |
| Stale artifacts | `generate.py --check` compares Lean, JSON, and audit manifest |
| Rejection drift | committed class/message/location snapshots and `update_rejections.py --check` |
| Corpus drift | fixed-seed CPython↔IR↔Lean comparisons, including explicit failures |
| Float regressions | 100,000-pattern boundary corpus, bit-exact comparisons and counted computed-NaN exemptions |

The audit allows only Lean's `propext`, `Classical.choice`, and `Quot.sound`.
It rejects `sorryAx`, native-evaluation trust hooks, and project-specific axioms.
Optional `*_sample_*` theorems and the harmonic energy grid use `native_decide`;
those are finite build-time tests, not universal correctness certificates.

## Status

| Claim | Status |
| --- | --- |
| Emitted Source/IR agreement with reference lowering | Kernel-checked, per program |
| Checked code↔IR full-outcome equivalence | Proved, all fuel and arithmetic backends |
| Direct infallible rational code↔IR | Proved, selected fuel |
| Fuel monotonicity and completed-outcome stability | Proved generically |
| Total→partial spec implication | Proved generically |
| Rational division success iff divisor nonzero | Proved |
| Raw binary64 representation round-trip | Proved by rfl |
| Two-tier Float bit/value component specs | Proved by rfl (`FloatSpec`) |
| `pontifex_step`-proved component specs | Proved and audited (`Examples/StepDemo`) |
| Native Float/CPython arithmetic agreement | Tested at IEEE edges and random bits, not proved |
| Python source↔IR equivalence | Tested only; still unproved |
| Physics step/spec links and clamping spec | Proved for the modeled algorithms |
| General harmonic modified-energy invariant | **Proved**, `symplecticStep_modifiedEnergy` |
| Multi-step free-fall position closed form | **Proved**, `repeatStep_position_twice` |
| General positive-duration loop termination | Open |

## Remaining boundaries

* AST parsing/transcription, reference lowering fidelity, annotation/type handling,
  and JSON parsing are not proved correct with respect to Python.
* Codegen certificates are per-program checks, not a universal compiler theorem.
* Native machine-code semantics and Float arithmetic implementations remain
  trusted/tested boundaries. `FloatSpec` proves how the bit and value tiers are
  connected; it does not prove native rounding. IEEE arithmetic proofs remain
  future work.
* `rat_ring` is a certified integer-coefficient normalizer, not a general ring
  tactic: rational literal coefficients must be cleared, and non-polynomial
  functions (`abs`, division by variables) are treated as atoms. It proves the
  symplectic invariant and the multi-step free-fall formula. Broader algebra
  automation (rational coefficients, ordered/nonlinear reasoning) remains open.
* General calls (beyond bounded white-box scalar helpers), array parameters/
  returns and sharing, a general exception hierarchy, and a Python numeric
  tower remain unsupported features, not silent assumptions. Local arrays and
  early returns are implemented.

## Reproduce

```bash
make check                 # freshness, audit, corpora, tests
make float-boundaries      # full 100,000-pattern Float run
```

Certificate corruption tests exercise wrong arithmetic, source/IR mismatches,
phi copies, and exhaustion. P1 adds failure/short-circuit/evaluation-order tests,
malformed-state tests, schema migration checks, and Float payload/zero/subnormal
regressions. Finite tests complement, but do not replace, the kernel proofs.
