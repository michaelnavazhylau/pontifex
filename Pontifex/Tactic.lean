/-
  Pontifex.Tactic

  Small reasoning helpers for exact-rational goals in a *core-Lean* build.

  Motivation (an important finding of this scaffold)
  --------------------------------------------------
  Lean core ships `Rat` with `Rat.add_comm`, `Rat.mul_comm`, ... but *not* the
  `Std.Associative`/`Std.Commutative` instances for `Rat` multiplication, and it
  ships no `ring` tactic.  `ac_rfl` therefore only closes goals up to
  associativity/commutativity of *addition*.  Declaring the missing instances
  (below) restores AC reasoning for products too.

  `Pontifex.Core.Poly` provides `rat_ring`, a certified normalizer that
  reifies both sides into integer-coefficient polynomials, normalizes with
  kernel-reducible `Int`/list operations, and proves equality when the normal
  forms coincide. It handles coefficient arithmetic and cancellation (for
  example the symplectic modified-energy identity). Rational literal
  coefficients are rejected; clear denominators first.

  `rat_simp` is the older, cheaper fallback: it eliminates subtraction,
  distributes products over sums and then closes with `ac_rfl`.  It handles polynomial identities whose two sides have
  the same multiset of monomials with the same coefficients (typically after
  distribution).  It is *not* a ring tactic: any identity that requires
  *combining coefficients* (such as `2 * (1/2) = 1`, or
  `n·(n+1) + 2·(n+1) = (n+1)·(n+2)`, or cancellation of opposing cubic terms in
  an unreduced form) is out of reach.  See docs/TRUST.md for the planned replacement (a verified reflective
  normaliser, or enabling the optional Mathlib layer).
-/
import Std

namespace Pontifex

/-- Lean core provides these for `Rat` addition but not multiplication. -/
instance : Std.Associative (· * · : Rat → Rat → Rat) := ⟨Rat.mul_assoc⟩

instance : Std.Commutative (· * · : Rat → Rat → Rat) := ⟨Rat.mul_comm⟩

/-- Distribute products over sums (left and right) in a goal over `Rat`.

    Use as the last tactic step: it normalises the goal into a sum of monomials
    and then discharges it with `ac_rfl`, which works when both sides have the
    same multiset of monomials. -/
macro "rat_simp" : tactic =>
  `(tactic|
    (simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_neg, Rat.neg_mul,
        Rat.neg_neg, Rat.mul_assoc]
     ac_rfl))

end Pontifex
