"""P2/T8: the certified rational polynomial normalizer."""

from __future__ import annotations

from conftest import ROOT
from test_certificates import check_lean

PRELUDE = """import Pontifex.Core.PolyTactic
import Pontifex.Spec.FreeFall
import Pontifex.Audit.Command
"""


def _run(tmp_path, body: str):
    return check_lean(tmp_path, PRELUDE + body)


def test_expands_and_combines_coefficients(tmp_path):
    result = _run(
        tmp_path,
        """
example (x y : Rat) : (x + y) * (x + y) = x*x + 2*x*y + y*y := by rat_ring
example (x y : Rat) : (x - y) * (x + y) = x*x - y*y := by rat_ring
example (x : Rat) : x + 0 = x := by rat_ring
example (x y z : Rat) : (x + y + z)*(x + y + z) = x*x + y*y + z*z + 2*x*y + 2*x*z + 2*y*z := by rat_ring
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_rejects_false_identity(tmp_path):
    result = _run(tmp_path, "example (x y : Rat) : x + y = y + y := by rat_ring\n")
    assert result.returncode != 0
    assert "same polynomial normal form" in (result.stdout + result.stderr)


def test_rejects_rational_literal_coefficients(tmp_path):
    result = _run(tmp_path, "example (x : Rat) : (1/2 : Rat) * x = x / 2 := by rat_ring\n")
    assert result.returncode != 0
    assert "rational literal coefficients" in (result.stdout + result.stderr)


def test_rejects_non_rat_goals(tmp_path):
    result = _run(tmp_path, "example (n : Nat) : n + 1 = 1 + n := by rat_ring\n")
    assert result.returncode != 0
    assert "not over Rat" in (result.stdout + result.stderr)


def test_harmonic_invariant_and_nstep_formula_are_kernel_checked(tmp_path):
    result = _run(
        tmp_path,
        """
example (w2 dt x v : Rat) :
    Pontifex.Spec.modifiedEnergy w2 dt (Pontifex.Spec.symplecticStep w2 dt ⟨x, v⟩) =
      Pontifex.Spec.modifiedEnergy w2 dt ⟨x, v⟩ :=
  Pontifex.Spec.symplecticStep_modifiedEnergy w2 dt x v
example (n : Nat) (a dt x v : Rat) :
    2 * (Pontifex.Spec.repeatStep n a dt ⟨x, v⟩).x =
      2*x + 2*(n:Rat)*v*dt + a*dt*dt*(n:Rat)*((n:Rat)+1) :=
  Pontifex.Spec.repeatStep_position_twice n a dt x v
#audit_axioms Pontifex.Spec.symplecticStep_modifiedEnergy
#audit_axioms Pontifex.Spec.repeatStep_position_twice
#audit_axioms Pontifex.Spec.repeatStep_velocity
#audit_axioms Pontifex.Poly.eval_normalize
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_invalid_polynomial_does_not_get_a_certificate(tmp_path):
    """Corrupt a valid identity and confirm the tactic rejects it."""
    result = _run(
        tmp_path,
        """
example (x v w2 dt : Rat) :
  (v - w2*x*dt)*(v - w2*x*dt) + w2*(x + (v - w2*x*dt)*dt)*(x + (v - w2*x*dt)*dt)
    - w2*dt*(x + (v - w2*x*dt)*dt)*(v - w2*x*dt)
  = v*v + w2*x*x - w2*dt*x*v + 1 := by rat_ring
""",
    )
    assert result.returncode != 0
    assert "same polynomial normal form" in (result.stdout + result.stderr)
