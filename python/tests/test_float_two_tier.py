"""P2/T10: two-tier binary64 values and their proved component specs."""
from __future__ import annotations

from test_certificates import check_lean

PRELUDE = """import Pontifex.Core.FloatSpec
import Pontifex.Audit.Command
open Pontifex
"""


def _run(tmp_path, body: str):
    return check_lean(tmp_path, PRELUDE + body)


def test_value_and_bit_tiers_for_each_operation(tmp_path):
    result = _run(tmp_path, """
example (x y : Binary64) :
    (Ops.binary64.add x y).toFloat = x.toFloat + y.toFloat := FloatSpec.add_value x y
example (x y : Binary64) :
    (Ops.binary64.add x y).bits = (x.toFloat + y.toFloat).toBits := FloatSpec.add_bits x y
example (x y : Binary64) :
    (Ops.binary64.sub x y).toFloat = x.toFloat - y.toFloat := FloatSpec.sub_value x y
example (x y : Binary64) :
    (Ops.binary64.sub x y).bits = (x.toFloat - y.toFloat).toBits := FloatSpec.sub_bits x y
example (x y : Binary64) :
    (Ops.binary64.mul x y).toFloat = x.toFloat * y.toFloat := FloatSpec.mul_value x y
example (x y : Binary64) :
    (Ops.binary64.mul x y).bits = (x.toFloat * y.toFloat).toBits := FloatSpec.mul_bits x y
example (x y : Binary64) :
    (Ops.binary64.div x y).toFloat = x.toFloat / y.toFloat := FloatSpec.div_value x y
example (x y : Binary64) :
    (Ops.binary64.div x y).bits = (x.toFloat / y.toFloat).toBits := FloatSpec.div_bits x y
""")
    assert result.returncode == 0, result.stdout + result.stderr


def test_raw_identity_and_sign_layers(tmp_path):
    result = _run(tmp_path, """
example (bits : UInt64) : (Binary64.ofBits bits).bits = bits := Binary64.ofBits_bits bits
example (bits : UInt64) : (Binary64.ofBits bits).toBits = bits := Binary64.bits_roundtrip bits
example (f : Float) : (Binary64.ofFloat f).toFloat = f := Binary64.ofFloat_value f
example (x : Binary64) : (Binary64.neg x).bits = x.bits ^^^ Binary64.signBit :=
  Binary64.neg_bits x
example (x : Binary64) : (Binary64.neg x).toFloat = -x.toFloat := Binary64.neg_value x
example (x : Binary64) : (Binary64.abs x).bits = x.bits &&& Binary64.magnitudeMask :=
  Binary64.abs_bits x
example : (Binary64.neg (Binary64.ofBits 0)).bits = 0x8000000000000000 := rfl
example : (Binary64.abs (Binary64.ofBits 0x8000000000000000)).bits = 0 := rfl
""")
    assert result.returncode == 0, result.stdout + result.stderr


def test_two_tier_specs_are_axiom_clean(tmp_path):
    result = _run(tmp_path, """
#audit_axioms Pontifex.FloatSpec.add_value Pontifex.FloatSpec.add_bits
#audit_axioms Pontifex.FloatSpec.sub_value Pontifex.FloatSpec.mul_value
#audit_axioms Pontifex.FloatSpec.div_value Pontifex.FloatSpec.pow_spec
#audit_axioms Pontifex.Binary64.neg_bits Pontifex.Binary64.abs_bits
""")
    assert result.returncode == 0, result.stdout + result.stderr
