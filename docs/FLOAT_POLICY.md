# Binary64 boundary and arithmetic policy (schema 2)

This is an explicit scalar binary64 reading, not a complete model of Python's
mixed `int`/`float` tower. Its code↔IR certificates are kernel-checked; agreement
with CPython's native arithmetic is **tested**, not a compiler/hardware proof.

## Representation and wire format

* Canonical Float input format: JSON strings `"0x<1..16 hex digits>"`, interpreted
  as raw UInt64 bits, **not** hexadecimal numeric floating-point literals.
* Python `run_lean(..., mode="float")` sends those bits, never rationalizes inputs.
  The CLI `eval --float` also preserves `-0.0` and accepts raw bit strings.
* `Binary64` stores a UInt64. Identity transport preserves every pattern,
  including negative zero, infinities, signaling NaNs, signs, and payloads.
  `Binary64.bits_roundtrip` proves the representation round-trip by `rfl`.
* Lean's built-in `Float` canonicalizes NaNs. The wire backend is therefore
  `Ops.binary64`, not `Ops.float`. Arithmetic explicitly converts through built-in
  Float, whereas identity, literal loading, negation, and abs keep raw bits.
* Float source literals carry both their exact rational value and their original
  bits. Exact mode uses the rational; binary64 uses the bits, so subnormals do not
  go through numerator/denominator conversion. Non-finite **source literals**
  (`1e999`) are rejected; non-finite runtime inputs enter through the bit protocol.
* Legacy rational strings in the native runner's Float mode are a convenience,
  not the bit-exact protocol. Their conversion can round or overflow. General
  large Python integer coercions and integer-only subexpressions are still not
  a verified numeric-tower model (P3).

## Two-tier representation and proved component specs

`Binary64` stores a raw `bits : UInt64` tier and a native `value : Float` tier.
`PyVerif/Core/FloatSpec.lean` proves, for every arithmetic operation, both
faces of the result:

```lean
FloatSpec.add_value : (Ops.binary64.add x y).toFloat = x.toFloat + y.toFloat
FloatSpec.add_bits  : (Ops.binary64.add x y).bits  = (x.toFloat + y.toFloat).toBits
```

and analogously for subtraction, multiplication, division, power, negation,
and absolute value. `Binary64.neg_bits` is the sign-bit flip;
`abs_bits` is the magnitude mask; `bits_roundtrip` is exact for wire values.

These are *definitional* connections between the two tiers, **not** proofs that
native `Float` operations round correctly. That is the remaining trusted
boundary, exercised by the boundary corpus and documented below.

## Arithmetic and failures

| Operation | Policy |
| --- | --- |
| `+ - *` | Built-in native binary64; overflow produces infinity, underflow produces a rounded/subnormal/zero result |
| `/` | Either sign of zero raises `failed divisionByZero`, even for NaN/zero or infinity/zero; otherwise native binary64 |
| `** n` | Natural literal exponent 0..8 only; an explicit IR operation, NOT repeated multiplication in Float mode |
| Float power overflow | Finite base producing infinity yields `failed overflow`, like CPython `float ** int` |
| Exact power | Rational power; no fixed-width overflow |
| `abs`, unary `-` | Clear/flip sign bit; preserve zero signs and NaN payloads |
| `==`, `!=` | +0 equals -0; NaN equals nothing (including itself) |
| ordered comparison | False with NaN; ordinary binary64 otherwise |
| NaN arithmetic | NaN propagates; computed payload/sign can canonicalize |

The base of `e ** 0` is still evaluated: `(1 / 0) ** 0` fails. Expressions and
return tuples evaluate left-to-right. Boolean `and`/`or` short-circuit faults.

## Boundary corpus and allowlist

```bash
make float-boundaries
# or
uv run python scripts/check_float_boundaries.py --samples 100000 --arithmetic 4096
```

Default corpus: 100,000 fixed-seed random bit patterns plus signed zeros,
smallest/largest subnormals, normal extremes, infinity, quiet/signaling NaNs,
and decimal source-literal round trips. It compares CPython, Python IR, and
Lean on identity, `+ - * /`, power, sign/abs, and comparisons. A full local run
performed **269,724 comparisons**, with **zero unallowlisted mismatches**.

`corpus/float_allowlist.json` contains one narrow rule: computed arithmetic
results may differ in bits **only if both results are NaN**. Identity transport,
literals, sign/abs operations, finite values, infinities, and error outcomes
cannot use that exemption. The runner reports the number of exemptions and
the reason; this is not silent normalization. The local full run used 451
computed-NaN exemptions (counts can vary by runtime/platform).

This evidence is not exhaustive. It does not prove native rounding/libm, the
CPython parser, or generated machine code correct. Exact hardware-level
arithmetic proofs remain P2 work.
