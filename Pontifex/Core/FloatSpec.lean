/-
  Two-tier binary64 specifications.

  For every arithmetic operation we state both faces of the result:
  * the value tier (`toFloat`) used by the semantics and comparisons;
  * the bit tier (`bits`) used by the wire protocol and identity transport.

  These lemmas are definitional: they relate the two representations of
  `Ops.binary64`, not native IEEE-754 rounding. The latter is a documented,
  differential-tested trust boundary (see docs/FLOAT_POLICY.md).
-/
import Pontifex.Core.Ops

namespace Pontifex.FloatSpec

open Pontifex

/-- A boundary value whose value tier is neither NaN nor infinite. -/
def Finite (x : Binary64) : Prop :=
  x.value.isNaN = false ∧ x.value.isInf = false

theorem add_value (x y : Binary64) :
    (Ops.binary64.add x y).toFloat = x.toFloat + y.toFloat := rfl

theorem add_bits (x y : Binary64) :
    (Ops.binary64.add x y).bits = (x.toFloat + y.toFloat).toBits := rfl

theorem sub_value (x y : Binary64) :
    (Ops.binary64.sub x y).toFloat = x.toFloat - y.toFloat := rfl

theorem sub_bits (x y : Binary64) :
    (Ops.binary64.sub x y).bits = (x.toFloat - y.toFloat).toBits := rfl

theorem mul_value (x y : Binary64) :
    (Ops.binary64.mul x y).toFloat = x.toFloat * y.toFloat := rfl

theorem mul_bits (x y : Binary64) :
    (Ops.binary64.mul x y).bits = (x.toFloat * y.toFloat).toBits := rfl

theorem div_value (x y : Binary64) :
    (Ops.binary64.div x y).toFloat = x.toFloat / y.toFloat := rfl

theorem div_bits (x y : Binary64) :
    (Ops.binary64.div x y).bits = (x.toFloat / y.toFloat).toBits := rfl

theorem pow_spec (x : Binary64) (n : Nat) :
    Ops.binary64.pow x n = (Ops.float.pow x.toFloat n).map Binary64.ofFloat := rfl

end Pontifex.FloatSpec
