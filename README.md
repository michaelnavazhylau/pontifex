# pyverif — a Python → SSA IR → Lean 4 verification bridge

An Aeneas-style pipeline for a small, statically shaped subset of Python.
You write a numerical routine in Python; `pyverif` gives it a Lean 4
counterpart together with a **kernel-checked** link to a reference semantics,
and a differential harness that compares

1. the original Python program,
2. the reference interpreter for the intermediate representation, and
3. the Lean reference semantics (via the `pyverif` executable).

The first application is a physics integrator, but nothing is physics-specific.

```
Python source (ast)          SSA IR (JSON + Lean value)        Lean 4
──────────────────           ──────────────────────────        ──────
def step(x,v,a,dt):   ==>    slots, phis, while headers   ==>  def step … := …
  v = v + a*dt               assign 4 (add …)                   theorem step_link … := rfl
  x = x + v*dt               ret [5,4]                          (exact ℚ or IEEE-754 Float)
  return x, v
```

## Quick start

```bash
uv sync                                   # Python tooling (pytest, hypothesis)
lake build                                # Lean library, generated examples, runner
python scripts/generate.py                # regenerate PyVerif/Generated/*.lean
uv run pytest                             # frontend, interpreter, differential tests
make corpus                               # triple differential: CPython / IR / Lean
python scripts/update_rejections.py       # refresh rejection diagnostics after review

# translate one file
uv run python -m pyverif ir       examples/free_fall.py
uv run python -m pyverif emit     examples/free_fall.py
uv run python -m pyverif eval     examples/free_fall.py --args 1,2,3,4        # exact ℚ
uv run python -m pyverif eval     examples/free_fall.py --args 1,2,3,4 --float # binary64
uv run python -m pyverif compile  examples/free_fall.py --out /tmp/FreeFall.lean --json /tmp/ff.json
```

`lake exe pyverif rat|float ir.json inputs.json [fuel]` is the Lean oracle used
by the differential tests.

## What is actually verified

| Claim | Mechanism |
| --- | --- |
| Straight-line Lean code = reference semantics of the *same* IR | `<fn>_link` by `rfl`, at the selected fuel |
| Generated Lean code = hand-written physics spec | `PyVerif/Examples/SpecLinks.lean` (`rfl`) |
| Reference semantics is deterministic and total (fuel) | `PyVerif/Core/Semantics.lean` |
| Python source = IR semantics | **not proved** — checked by differential testing (exact ℚ and binary64) |
| Control-flow compiled code (`if`/`while`) = IR semantics | **proved** for every fuel, input, and `Ops α` backend; full outcomes preserved |
| Clamped integrator = independent piecewise spec | `PyVerif/Examples/ControlFlow.lean`, kernel-checked |
| General modified-energy invariant | **open**; current core-only algebra helper is limited, and only a finite grid is checked |
| Artifact config/schema stamped | `#guard` in every generated module; `generate.py` cross-checks Lean and Python versions |
| Certificate axiom hygiene | `#audit_axioms` over every lowering/linkage theorem at build time |

Two numeric readings are first class and never confused:

* `Ops.rat` — exact rational arithmetic (the mathematical reading; `Rat` stands
  in for `ℝ` in this core-Lean-only build),
* `Ops.float` — IEEE-754 binary64 (the operational reading of Python `float`).

Literals in the IR are exact rationals; the frontend encodes a Python float
literal by the *exact binary value* of that float, rather than its decimal
spelling. This is a deliberate alternative reading, not a proof of equivalence
to Python floats. Exceptions, extreme float conversions, signed zero, and
floating-point `**` remain modelling gaps; see `docs/TRUST.md`.

## The language subset (v0)

One function per module, scalar parameters, and:

* statements: `x = e`, `x: T = e`, `x += e` (also `-=`, `*=`, `/=`), `if/else`,
  `while`, `pass`, `return` (single exit, last statement only);
* expressions: names, int/float literals, `+ - * /`, `**` with an integer
  literal exponent in `[0, 8]` (desugared to multiplication), unary `-`,
  `abs(x)`;
* conditions: one comparison at a time (not chained), `and` / `or` / `not`,
  boolean literals.

Everything else is rejected with a located message — no imports, `for`,
`break`/`continue`, `try`, `with`, lambdas, comprehensions, attributes,
subscripting, `min`/`max`, conditional expressions, or tuple unpacking.

## Layout

```
PyVerif/
  Core/IR.lean          deep embedding: Expr, Cond, Phi, Stmt, Fn
  Core/Source.lean      core source language (pre-SSA), ids instead of names
  Core/Lower.lean       verified SSA lowering; checked per program by `rfl`
  Core/Ops.lean         Rat and Float numeric backends
  Core/Semantics.lean   Env, evalE/evalC, exec (fuel), Fn.run
  Json.lean             JSON decoder/encoder for the IR (Lean side)
  Tactic.lean           missing Rat AC instances + `rat_simp`
  Spec/Mechanics.lean   independent physics specification and proven lemmas
  Generated/*.lean      checked-in translations of examples/ (regenerated)
  Examples/SpecLinks.lean   straight-line code/IR links to physics specs
  Examples/ControlFlow.lean clamped-step spec and Float certificate examples
python/pyverif/
  certify.py            proof-producing control-flow backend (all-fuel linkage)
  version.py            IR schema version shared with Lean
  ...                   frontend, SSA lowering, emitter, interpreter, CLI
corpus/                 18-program triple-differential corpus + manifest
tests/rejections/       57 rejected programs with committed diagnostics
examples/               Python programs that are translated
python/tests/           unit, rejection, differential (incl. Lean oracle) tests
TODO.md                 ordered implementation roadmap with acceptance criteria
docs/TRUST.md           trust model, status matrix, open obligations
docs/RELATED_WORK.md    review of Charon/Aeneas and ranked lessons for us
docs/related-work/      full reading reports for both upstream repositories
```

## Design notes

* **Why SSA?** It resolves mutation into explicit values and phi joins.
  Straight-line code uses `let` bindings. Control-flow code uses specialized
  slot-state functions and parallel phi copies, each with a kernel-checked
  certificate. Executable blocks do not call the IR interpreter.
* **Why fuel?** Total semantics without termination proofs. Certified blocks
  and both reference interpreters use the same structured budget: sequence
  heads/tails, selected branches, and loop bodies/back edges receive one less
  level. All-fuel certificates include exhaustion, not just successful returns.
* **Why emit the IR as a Lean value?** The linkage theorem is a statement about
  the *same data* the frontend emitted; the JSON is that same data in wire form,
  so the Lean JSON decoder can be tested against it.

## Related work

The pipeline is deliberately Aeneas-shaped, so the two upstream projects were
reviewed in depth: [Charon](https://github.com/AeneasVerif/charon) (rustc MIR to
a serialized IR) and [Aeneas](https://github.com/AeneasVerif/aeneas) (IR to
Lean/F*/Coq/HOL4 plus a WP proof layer). Notes and full reports:

- `docs/RELATED_WORK.md` — comparison table and nine ranked, scoped
  recommendations (outcome lattice and refinement, exceptional outcomes,
  versioned artifacts, multi-exit lowering, opacity lattice, a `step`-style
  spec database, negative-test corpus, differential corpus, Float two-tier
  arithmetic lemmas).
- `docs/related-work/charon-review.md`,
  `docs/related-work/aeneas-review.md` — the complete reviews with commit pins
  and file references.

The main deliberate divergence: Aeneas trusts its translator and relies on
typechecking plus proof replay, whereas this project checks lowering and code
generation **per program** in the kernel. Conversely, Aeneas has far stronger
corpus-scale and proof-UX infrastructure, which is where its lessons are most
useful.

## Roadmap

Completed: all-fuel code↔IR certificates for nested `if`/`while`, a verified
SSA lowering with per-program `rfl` certificates, backend-parametric
full-outcome preservation, and corruption-rejection tests.

The ordered, acceptance-criteria-backed plan lives in `TODO.md`. P0 is
complete (config stamping, axiom gate, rejection corpus, differential corpus).
Next:

1. **P1:** an outcome lattice with a fuel-refinement theorem, explicit
   exceptional/stuck outcomes (division by zero first), and closing the Float
   boundary model.
2. **P2:** a verified reflective `Rat` normaliser (closes the modified-energy
   and n-step theorems), a spec database with `pyverif_step`, and Float
   value/bit-level lemmas.
3. **P3:** multi-exit returns, state vectors, function calls, an opacity
   lattice, and Python integer semantics.
