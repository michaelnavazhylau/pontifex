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

namespace PyVerif

/-- The arithmetic and comparison interface required by the interpreter. -/
structure Ops (α : Type) where
  /-- Embed an exact rational literal.  For `Float` this is the (rounding)
      conversion of the rational's numeric value to binary64. -/
  ofRat : Rat → α
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

/-- IEEE-754 binary64 arithmetic: the operational reading of Python `float`.

    `ofRat q` is computed as `q.num / q.den` in binary64. When both components
    are represented exactly, this gives one correctly rounded division. Not
    all frontend literals satisfy that condition: subnormal literals can have
    denominators beyond the finite Float range. Extreme rationals can overflow,
    underflow, or double-round; conversion correctness remains a modelling gap.

    Note that `Float` arithmetic in Lean is compiled to native double
    operations, so it agrees with CPython for `+ - * /` under the assumption
    that Python's compiler does not fuse operations (adversarial expressions
    with division by zero, NaN and `-0.0` are outside the verified subset). -/
def Ops.float : Ops Float where
  ofRat := fun q => Float.ofInt q.num / Float.ofNat q.den
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

end PyVerif
