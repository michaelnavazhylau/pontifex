# Scalar selection (T15a / issue #2, schema 4)

```python
def advance(x, v, a, dt, limit):
    v = min(max(v + a * dt, -limit), limit)
    x += v * dt
    return x if x > 0 else 0, v
```

```bash
uv run python -m pontifex emit examples/limited_step.py --out /tmp/LimitedStep.lean
lake env lean /tmp/LimitedStep.lean
```

## Two-argument `min` and `max`

Only `min(a, b)` and `max(a, b)` with **exactly two positional scalar arguments**
are supported. Iterable/variadic forms, `key=`, `default=`, keyword arguments,
unpacking, and array operands are rejected. A locally shadowed builtin is not
silently treated as the builtin; module-local functions named `min`/`max` still
follow the bounded helper-call rules.

Both operands are evaluated **once, left to right**, including the second
operand when the first would ultimately be selected. Faults propagate in that
order. These are explicit `BinOp.min` / `BinOp.max` operations, not duplicated
expressions or frontend rewrites to comparisons:

| Operation | Result after evaluating `a`, then `b` |
| --- | --- |
| `min(a, b)` | `b` if `b < a`, otherwise `a` |
| `max(a, b)` | `b` if `b > a`, otherwise `a` |

This is Python's two-argument scan, **not IEEE `fmin`/`fmax`**:

* Exact mode compares rational scalars. Equal values retain the first operand;
  rationals have neither NaN nor a sign of zero.
* Float/binary64 mode returns the original selected operand, without arithmetic
  or reconstruction. Equal values retain the first operand, including its sign
  of zero: `min(-0.0, 0.0)` is `-0.0`, while reversing the operands gives `0.0`.
  The same rule applies to `max`.
* An ordered comparison with NaN is false. A first-operand NaN is retained; a
  second-operand NaN is ignored. Two NaNs retain the first operand's original
  payload and sign in `Ops.binary64`, including signaling-NaN bit patterns.
* Native comparison behavior remains tested, not a proof of hardware semantics.
  All cases above are compared bit-for-bit against CPython, without a NaN
  exemption. The existing arithmetic exemption does not apply to selection.

As throughout this project, this is one scalar type per backend, **not** Python's
full integer/float/object numeric tower or object-identity semantics (T15b).

## Conditional expressions

`a if condition else b` evaluates the condition **first**, then exactly one
scalar branch. The unselected expression is never evaluated, so it cannot fail,
read an unset slot, or consume runtime fuel. For example,
`x / y if y != 0 else 0` does not divide by zero when `y` is zero.

Conditions use the existing boolean sort: comparisons, `and`/`or`/`not`, and
boolean literals, with the same short-circuiting and fault behavior. General
Python scalar truthiness (`a if x else b`) is not supported. Both result branches
must be statically valid scalar expressions; arrays and unsupported syntax are
rejected even in a dead branch.

These constructs may nest in arithmetic, conditions, array elements/stores,
return tuples, and scalar arguments to supported helpers. Straight-line scalar
helper bodies may also use them. Nested user-helper calls in supported scalar
expression positions now work under T13; calls in conditions or conditional
branches and statement-level callee control flow remain deferred. See
[CALLS.md](CALLS.md) for evaluation-order restrictions.

## IR, certificates, and migration

Schema **4** adds `min`/`max` binary operators and `Expr.select` / Source `select`.
Its JSON shape is `{"k":"bin","op":"min",...}` (or `max`) and
`{"k":"select","c":condition,"t":thenExpression,"e":elseExpression}`.
Schemas 1–3 are rejected by both JSON decoders; regenerate old artifacts.

Expressions and conditions are mutually recursive, both in the syntax and in
Lean's kernel-reducible evaluation/lowering/relocation functions. No extra
statement-level fuel is consumed by scalar selection. The normal
`<fn>_lowering := rfl` checks the reference lowering. Selection always uses the
independent certified backend, even in a straight-line caller, with full-outcome
linkage for **all fuel, environments, and `Ops α`**. Helper program certificates
still compose per callee. Existing fuel-refinement theorems are unchanged.

Source transcription and fidelity of the reference reading to Python remain
tested boundaries; this is not a universal frontend-correctness or IEEE proof.
Tests include kernel rejection of corrupted operators, branch order, comparison
direction, and emitted executable branches. See [TRUST.md](TRUST.md) and
[FLOAT_POLICY.md](FLOAT_POLICY.md).
