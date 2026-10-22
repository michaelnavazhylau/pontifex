"""P2/T9: the `pontifex_step` proof driver."""

from __future__ import annotations

from lean_helpers import check_lean

PRELUDE = """import Pontifex.Step
import Pontifex.Generated.FreeFall
import Pontifex.Generated.HarmonicOscillator
import Pontifex.Audit.Command
open Pontifex
"""


def _run(tmp_path, body: str):
    return check_lean(tmp_path, PRELUDE + body)


def test_step_tactic_proves_component_specs(tmp_path):
    result = _run(
        tmp_path,
        """
example (x v a dt : Rat) :
    (Generated.FreeFall.step 64 x v a dt).map Prod.fst =
      some (x + (v + a * dt) * dt) := by
  pontifex_step [Generated.FreeFall.step]
example (x v a dt : Rat) :
    (Generated.FreeFall.step 64 x v a dt).map Prod.snd = some (v + a * dt) := by
  pontifex_step [Generated.FreeFall.step]
example (x v w2 dt : Rat) :
    (Generated.HarmonicOscillator.step 64 x v w2 dt).map Prod.snd =
      some (v - w2 * x * dt) := by
  pontifex_step [Generated.HarmonicOscillator.step]
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_step_tactic_rejects_a_false_property(tmp_path):
    result = _run(
        tmp_path,
        """
example (x v a dt : Rat) :
    (Generated.FreeFall.step 64 x v a dt).map Prod.snd = some (v + a * dt + 1) := by
  pontifex_step [Generated.FreeFall.step]
""",
    )
    assert result.returncode != 0


def test_step_tactic_trace_variant_prints_and_finishes(tmp_path):
    result = _run(
        tmp_path,
        """
example (x v a dt : Rat) :
    (Generated.FreeFall.step 64 x v a dt).map Prod.fst =
      some (x + (v + a * dt) * dt) := by
  pontifex_step? [Generated.FreeFall.step]
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_step_rules_and_demo_theorems_are_audited(tmp_path):
    result = _run(
        tmp_path,
        """
#audit_axioms Pontifex.fromEval_ok Pontifex.bindEnv_fellThrough
#audit_axioms Pontifex.Examples.freeFall_step_position
#audit_axioms Pontifex.Examples.freeFall_step_velocity
#audit_axioms Pontifex.Examples.harmonicOscillator_step_velocity
""",
    )
    assert result.returncode == 0, result.stdout + result.stderr
