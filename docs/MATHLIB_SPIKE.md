# Mathlib spike

Status: **experiment successful; not adopted on `main`.** Branch:
`spike/mathlib`.

## Question

Would Mathlib simplify the specification layer without compromising the
core-only generated certificates?

## Setup

- Mathlib tag **`v4.35.0`** (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`),
  matching this repository's `lean-toolchain`.
- `[[require]]` is spike-only. The default targets remain `Pontifex` and the
  `pontifex` executable.
- The proofs live in `MathlibSpike.lean` at the repository root, deliberately
  outside `Pontifex/`, so no library module or generated artifact imports
  Mathlib.
- `MathlibSpike` is a separate `lean_lib`, built only on demand:

  ```bash
  lake build MathlibSpike
  ```

For the benchmark, Mathlib was already built in a sibling project
(`PhysicsSim`), so its package directory was reused through
`.lake/packages`. That is a local measurement convenience, not part of the
committed setup.

## What got simpler

The spike re-proves the hard specification theorems using `ring` and `push_cast`:

| Theorem | Core-only proof | Mathlib proof |
| --- | --- | --- |
| `constantAccelStep_expanded` | `rat_simp` | `congr 1; ring` |
| `symplecticStep_expanded` | `rat_simp` | `congr 1; ring` |
| `symplecticStep_modifiedEnergy` | `rat_ring` | `ring` |
| `constantAccelStep_position_error` | not stated | `ring` with `1/2` |
| `repeatStep_velocity` | four custom `ratNatCast_*` lemmas + `rat_ring` | `push_cast; ring` |
| `repeatStep_position` | not stated without clearing `2` | `push_cast; ring` |
| `repeatStep_position_twice` | cleared factor `2` + `rat_ring` | derived from the `1/2` version with `ring` |

The spike is 103 lines including imports, theorem statements, proofs, and the
audit; it contains **7 theorems** and **no** `rat_ring`, `rat_simp`, or
`ratNatCast_*` lemmas.

The biggest practical wins:

- rational coefficients are natural (`(1/2 : Rat)` needs no denominator
  clearing);
- induction steps need only `push_cast` and `ring`;
- the four hand-written Nat-cast lemmas disappear;
- the mathematically natural closed form can be stated directly, with the
  cleared form derived as a corollary.

The core-only `Poly.lean` + `PolyTactic.lean` (312 + 126 lines) were not
deleted: they remain necessary for a Mathlib-free build and for
`pontifex_step`'s fallback.

## Cost

Measured on this machine with an already-built Mathlib:

| Target | Jobs | Warm time |
| --- | ---: | ---: |
| default `lake build` | 41 | ~4.9 s |
| `lake build MathlibSpike` | 3149 | ~15.5 s first, ~2.9 s incremental |

Mathlib's package tree is **6.8 GB**, of which **6.6 GB** is build output. A
cold checkout needs the Mathlib cache or a full build; that cost is not
measured here.

Other costs:

- Mathlib master currently targets Lean `4.36.0-rc1`; the spike pins the
  `v4.35.0` tag. A project-wide Lean bump would recheck every certificate.
- Importing `Mathlib.Tactic` from this non-`module` file emits a module-system
  warning. Keeping the spike outside the core library is what matters.
- If generated modules ever imported Mathlib, every certificate's build
  closure would grow from 41 jobs to thousands. They do not: a grep of
  `Pontifex/Generated` finds no Mathlib import.

## Trust

- `#audit_axioms` passes for all seven spike theorems: only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Mathlib is kernel-checked, so it does not add logical axioms. The concern is
  dependency and build surface, not soundness.
- `make check` still passes: **330 tests**, 21-program corpus, 269,724 Float
  comparisons, 0 unallowlisted mismatches.

## Recommendation

1. **Do not make Mathlib a dependency of the core library or generated code.**
   Keep the 41-job, Mathlib-free `rfl`/link certificate path.
2. If adopted, add an **optional `Pontifex.Mathlib` specification library** for
   `ring`, `field_simp`, `linarith`, `positivity`, `Vector`, and `ℝ`-based
   specs. Users opt in; generated artifacts never do.
3. Use it where it pays: rational coefficients (#9), termination measures
   (#11), array/bounds lemmas (#12), and math-heavy specs.
4. Do not expect it to help with native IEEE-754 (#8), the certified frontend
   (#7), or the IR/control-flow work (#1, #2, #5, #6, #10).
5. Next step: port the actual `Spec/Mechanics.lean` and `Spec/FreeFall.lean`
   into a Mathlib-only spec package and measure the full line reduction and
   cold-build cost before deciding to adopt.

## Reproduce

On a fresh checkout of this branch, let Lake fetch and build Mathlib first:

```bash
lake update
lake exe cache get        # or build Mathlib from source
make mathlib-spike      # or: lake build MathlibSpike
```

Then confirm the core path is unchanged:

```bash
lake build                # 41 jobs, no Mathlib
make check
```
