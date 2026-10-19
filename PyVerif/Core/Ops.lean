/-
  PyVerif.Core.Ops

  Numeric backends.  The IR is deliberately *parametric* in its arithmetic:
  the same translated program can be interpreted

  * exactly over `Rat` (the mathematical reading; the exact stand-in for `ℝ`
    in a core-Lean-only build), or
  * over IEEE-754 binary64 via `Float` (the operational reading of Python
    `float`).

  A verified pipeline must never confuse the two, so the distinction lives in
  the types rather than in a comment.
-/
import Std
import PyVerif.Core.IR
import PyVerif.Core.Error
import PyVerif.Core.Binary64

namespace PyVerif

/-- The arithmetic and comparison interface required by the interpreter. -/
structure Ops (α : Type) where
  /-- Embed an exact rational literal.  For `Float` this is the (rounding)
      conversion of the rational's numeric value to binary64. -/
  ofRat : Rat → α
  /-- Float literal carries both its exact rational value and its original bits. -/
  ofFloatBits : Rat → UInt64 → α
  isZero : α → Bool
  pow : α → Nat → Eval α
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  div : α → α → α
  neg : α → α
  abs : α → α
  lt : α → α → Bool
  le : α → α → Bool
  gt : α → α → Bool
  ge : α → α → Bool
  eq : α → α → Bool
  ne : α → α → Bool

/-- Exact rational arithmetic: the mathematical reading of a program. -/
def Ops.rat : Ops Rat where
  ofRat := id
  ofFloatBits := fun q _ => q
  isZero := fun x => decide (x = 0)
  pow := fun x n => .ok (x ^ n)
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := Neg.neg
  abs := Rat.abs
  lt := (· < ·)
  le := (· ≤ ·)
  gt := (· > ·)
  ge := (· ≥ ·)
  eq := fun a b => decide (a = b)
  ne := fun a b => decide (a ≠ b)

/-- Built-in Float numeric backend. Floating literals use their original bits,
    not rational numerator/denominator conversion. ofRat remains for integer
    literals and legacy rational inputs; large integer coercions are not a full
    model of Python's numeric tower. Checked division lives in Semantics.
    Float.pow raises overflow when a finite base produces infinity.
    The bit-authoritative wire backend below additionally avoids the built-in
    Float model's NaN canonicalization during identity transport. -/
def Ops.float : Ops Float where
  ofRat := fun q => Float.ofInt q.num / Float.ofNat q.den
  ofFloatBits := fun _ bits => Float.ofBits bits
  isZero := fun x => x == 0.0
  pow := fun x n =>
    let y := Float.pow x (Float.ofNat n)
    if y.isInf && !x.isInf then .error (.failed .overflow) else .ok y
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := Neg.neg
  abs := Float.abs
  lt := (· < ·)
  le := (· ≤ ·)
  gt := (· > ·)
  ge := (· ≥ ·)
  eq := (· == ·)
  ne := (!· == ·)

/-- Bit-preserving wire backend. Numeric operations use the built-in Float
    model; identity/literals/sign changes preserve the original representation.
    A computed NaN may have a canonical payload, as documented in the policy. -/
def Ops.binary64 : Ops Binary64 where
  ofRat := fun q => .ofFloat (Ops.float.ofRat q)
  ofFloatBits := fun _ bits => .ofBits bits
  isZero := fun x => x.value == 0.0
  pow := fun x n => (Ops.float.pow x.value n).map Binary64.ofFloat
  add := fun x y => .ofFloat (x.value + y.value)
  sub := fun x y => .ofFloat (x.value - y.value)
  mul := fun x y => .ofFloat (x.value * y.value)
  div := fun x y => .ofFloat (x.value / y.value)
  neg := Binary64.neg
  abs := Binary64.abs
  lt := fun x y => x.value < y.value
  le := fun x y => x.value ≤ y.value
  gt := fun x y => x.value > y.value
  ge := fun x y => x.value ≥ y.value
  eq := fun x y => x.value == y.value
  ne := fun x y => !(x.value == y.value)

end PyVerif
