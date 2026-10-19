# Trust model and verification status

## What the certificates establish

```
Python source -- parse/check -- core AST -- verified lowering --> IR
     |                                                            |
 CPython eval                                   reference `exec` + compiled blocks
     |                                                            |
     +-------- tested only ----------- code ↔ IR: kernel proof ----+
```

Three layers are kernel-checked per program:

1. **Core AST → IR** (`<fn>_lowering`): the verified lowering function
   `PyVerif/Source/Lower` reproduces the emitted IR body, by `rfl`. This puts
   slot allocation, phi merges, loop headers, and sorted-name ordering into the
   proved core instead of the Python frontend.
2. **IR → compiled code** (`<fn>_link`, `<fn>_compiled_link`): straight-line
   code by `rfl` at the selected fuel; control flow for every fuel and every
   `Ops α` backend with full outcome preservation.
3. **Compiled code → spec** for the worked physics examples.

**Python → core AST is not proved.** Parsing, subset checking, and the
syntactic transcription in `python/pyverif/source.py` remain trusted; the
certificate only starts at the emitted core AST. Concretely, a bug that made
the emitted AST differ from the Python program in an IR-visible way would break
`<fn>_lowering` (both pipelines start from the same AST), but a bug in the
transcription itself is not checked against the file.

## Verified lowering

`PyVerif/Core/Source.lean` defines the pre-SSA language: assignments, `if`,
`while`, `return`, `pass`, with variables as `Nat` ids. The frontend assigns ids
in **sorted name order**, so the lowering's `sorted(assigned_names)` and sorted
loop variables become sorting of ids. Consequently:

* the emitted `<fn>Source` contains no strings in its body, so the kernel never
  has to reduce string equality;
* the certificate compares `Source.lowerBody <fn>Source` with `<fn>IR.body`.
  Slot *names* and parameter names are cosmetic and are not compared; parameter
  ids come from the emitted AST and parameter slots are positional.

The certificate is checked with a raised `maxRecDepth` because the lowering is
a nested structural recursion. It is plain `rfl`: no `native_decide`, no
`sorry`, no arithmetic evaluation, no backend specialization.

Corrupting the source AST, the desugared arithmetic, or the emitted IR body
makes the certificate fail; `python/tests/test_certificates.py` exercises those
mutations, along with control-flow codegen corruptions.

### Straight-line backend

Assignments become direct `let` bindings over `Rat`. `<fn>_link` is proved by
`rfl` at the chosen literal fuel (64 in checked-in examples). The direct
function ignores its fuel argument; the theorem is **not** an all-fuel claim.
Too small a fuel makes that theorem fail to check.

### Certified control-flow backend

`python/pyverif/certify.py` independently emits one specialized function per
statement/sequence tail. The executable blocks:

* operate on explicit slot environments;
* emit arithmetic calls and branch conditions directly, without calling
  `exec`, `evalE`, `evalC`, or the reference phi-copy helpers;
* compile branches and parallel phi copies, and recurse structurally on fuel
  for loops;
* preserve **full outcomes**, distinguishing `returned`, `fellThrough`, and
  `outOfFuel`, rather than only equating a lossy `Option` projection.

Each block receives a kernel-checked `_correct` theorem. Parent certificates
compose child certificates; loop certificates induct on fuel while generalizing
the entire environment. For every generated control-flow function:

```lean
<fn>_compiled_link (ops : Ops α) [Inhabited α] (fuel : Nat) (args : List α) :
  <fn>Compiled ops fuel args = Fn.run ops <fn>IR fuel args
```

This quantifies over **every fuel, input environment, and arithmetic backend**.
In particular it applies to `Ops.rat` and `Ops.float` without evaluating floats
in the kernel. The public `<fn>` wrapper projects to a rational tuple;
`<fn>_link` proves that wrapper agrees with the corresponding reference
projection at every fuel too.

This replaces the scaffold's old tuple-style loop emitter, which had different
fuel accounting and only sample checks. The specialized slot-state output is
less pretty but gives an exact, independently checked target for nested loops,
branches, continuations after loops, and exhaustion.

The proof generator is not itself verified. Its generated proofs are checked
per program; corrupting arithmetic, a phi predecessor, or fuel behavior makes
the certificate fail. The tests exercise those mutations explicitly.

## Build-time trust gates

| Gate | Mechanism | Failure mode |
| --- | --- | --- |
| Schema drift | `pyverifConfig` + `#guard pyverifConfig.schemaMatches`; `generate.py` also cross-checks `IR_VERSION` against `irSchemaVersion` | `lake build` or regeneration fails |
| Axiom leakage | generated `PyVerif/Audit.lean` runs `#audit_axioms` on every lowering/linkage theorem | build fails naming the theorem and axiom |
| Stale artifacts | `scripts/generate.py --check` compares generated Lean, JSON, and the audit manifest | nonzero exit with the stale paths |
| Wire-format drift | Lean JSON decoder rejects a mismatched `irVersion` | runner exits with a version error |
| Rejection drift | `scripts/update_rejections.py --check` compares diagnostics byte-for-byte | nonzero exit listing stale snapshots |
| Corpus regression | `scripts/run_corpus.py` compares CPython, IR exact, IR binary64, and Lean on deterministic inputs | nonzero exit listing the program and mode |

`native_decide` remains allowed only in explicitly labelled `*_sample_*`
theorems (build-time regression checks); the audit excludes those by name and
the trust-gate tests reject `native_decide` anywhere else in generated files.

## Verification status

| Claim | Status |
| --- | --- |
| Artifact config and IR schema stamped | **Checked** by `#guard` in every generated module |
| Certificates depend only on standard axioms | **Checked** at build time by `#audit_axioms` |
| Rejection diagnostics are stable | **Snapshotted** (57 cases, exact class/message/location) |
| Differential corpus (source ↔ IR ↔ Lean) | **Tested** (18 programs × exact/rat/float) |
| Core AST → emitted IR body | **Proved**, `rfl`, every generated program |
| Straight-line code = IR semantics | **Proved**, `rfl`, selected fuel, exact Rat |
| Branch/loop compiled code = IR semantics | **Proved**, all fuel and `Ops α`, full outcomes |
| Control-flow tuple wrapper = reference tuple projection | **Proved**, all fuel |
| Free-fall and harmonic steps = independent Euler specs | **Proved**, `PyVerif/Examples/SpecLinks.lean` |
| Clamped step = independent piecewise spec | **Proved**, `PyVerif/Examples/ControlFlow.lean` |
| Free-fall velocity exactness and step expansions | **Proved**, `PyVerif/Spec/Mechanics.lean` |
| General harmonic modified-energy invariant | **Open**; a finite grid is checked |
| Python source = IR semantics | **Tested only**, exact and binary64 |
| JSON decoder agrees with emitted IR | **Tested only** |
| Python interpreter fuel = Lean interpreter fuel | **Tested**, including small boundary budgets |

The lowering and linkage proofs use no `sorry`, `native_decide`, or
project-specific axioms.
Tests inspect `#print axioms` and allow only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. Optional `*_sample_i` theorems and the
modified-energy grid use `native_decide`; they remain **finite tests** with a
compiler-trust dependency, not universal correctness proofs.

## Exact fuel convention

Both the Python reference interpreter and certified Lean code now follow
`PyVerif/Core/Semantics.lean` exactly:

* zero fuel exhausts immediately, even for `return` or a false loop;
* an assignment, skip, return, or empty sequence needs one positive level;
* a sequence cons with budget `n+1` gives `n` to its head AND its tail;
* an if with `n+1` gives `n` to the selected branch;
* a while with `n+1` gives `n` to its body AND the recursive back edge.

Fuel bounds structured execution depth and loop iterations, not total executed
instructions. Identical straight-line siblings do not share a global counter.
Headers are initialized by explicit assignments before entering a loop; back
edges copy from a snapshot, and the false exit does not reinitialize headers.

An exhausted run does **not** establish divergence or termination. All-fuel
code equivalence is not a termination proof for the Python program.

## Remaining trust boundaries

### Frontend and well-formedness

The Python AST frontend, SSA lowering, annotation handling, and JSON decoder
are not formally verified. Unsupported syntax is rejected, but accepted syntax
can still contain translation bugs. Types are scalar-by-construction in the
IR; Python annotations are advisory, not a verified type discipline. A JSON
consumer does not establish well-formed slot usage. Lean's environment lookup
uses defaults for unset slots; the Python interpreter rejects those accesses.
The generated theorem equates the two Lean programs even on malformed inputs;
it does not establish the frontend's well-formedness promises.

The next frontend milestone is to define a restricted source language and
semantics in Lean and certify lowering or generate independently checked
lowering evidence. Differential tests remain useful but are not a substitute.

### Numeric semantics

* `Rat` models exact rational arithmetic, **not** the full real field. Float
  literals use their exact binary value, not their decimal spelling.
* `Ops.float` is Lean's binary64 arithmetic. A generic code/IR certificate
  establishes identical operation structure, **not** equivalence to CPython's
  runtime or correctness of IEEE-754 implementations.
* Rational transport loses negative zero. The Float literal/input conversion
  divides separately converted numerator and denominator; extreme values or
  nonrepresentable components can overflow, underflow, or double-round. The
  small test corpus does not establish correctness of that conversion for all
  Python floats (notably subnormals).
* Division by zero is total in Lean but raises in Python. Exceptions, NaN/∞,
  signed-zero fidelity, fused operations, and Python integer/float coercions
  remain outside the current Python-equivalence claim.
* `**` is lowered to repeated multiplication. This is mathematically valid
  over Rat but is not generally bit-equivalent to Python floating-point power.

### Physics algebra

Core Lean supplies rational arithmetic lemmas but no `ring` tactic.
`rat_simp` distributes and reassociates terms; it does not normalize
coefficients or fully cancel polynomial terms. This is an **automation gap**,
not an impossibility of proving those facts in core Lean. Stronger identities
need explicit lemmas, a verified reflective normalizer, or an optional Mathlib
layer. The modified-energy invariant remains a finite grid test today.

## Reproduce the checks

```bash
python scripts/generate.py
lake build
uv run pytest
python scripts/generate.py --check
```

`test_certificates.py` compiles fresh nested/empty/diverging control-flow
programs, audits lowering and linkage axiom dependencies, specializes a
certificate at Float, and checks that corrupted source ASTs, desugared
arithmetic, IR bodies, generated code, phi copies, and fuel behavior are
rejected. `test_fuel.py` compares
small-budget Python/Lean runs, including terminating, diverging, and nested
cases. Generated linkage proofs do not depend on those finite tests.
