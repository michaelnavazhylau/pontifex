"""P1/T7: bit-authoritative wire, literal, power, and IEEE edge policies."""

from __future__ import annotations

from fractions import Fraction
import json
import math
import struct
import subprocess
import sys

import pytest

from pontifex.frontend import translate
from pontifex.interp import Returned, Failed, FellThrough, float_bits, run_float
from pontifex.ir import Fn, Assign, Lit
from pontifex.pipeline import (
    compare_outcomes,
    run_lean,
    compile_source,
    observe_python,
    load_python_function,
)
from conftest import ROOT
from lean_helpers import check_lean


def from_bits(bits):
    return struct.unpack(">d", struct.pack(">Q", bits))[0]


PATTERNS = [
    0,
    1 << 63,
    1,
    (1 << 63) + 1,
    0x000FFFFFFFFFFFFF,
    0x0010000000000000,
    0x7FEFFFFFFFFFFFFF,
    0xFFEFFFFFFFFFFFFF,
    0x7FF0000000000000,
    0xFFF0000000000000,
    0x7FF8000000000001,
    0xFFF8000000000001,
    0x7FF0000000000001,
]


def test_identity_preserves_every_edge_bit_including_nan_payloads(lean_exe):
    fn = translate("def f(x):\n    return x\n").fn
    vectors = [[from_bits(bits)] for bits in PATTERNS]
    outputs = run_lean(lean_exe, fn.to_json_text(), vectors, mode="float")
    assert [float_bits(out.values[0]) for out in outputs] == [hex(bits) for bits in PATTERNS]


@pytest.mark.parametrize(
    "text", ["5e-324", "-5e-324", "-0.0", "0.1", "1.7976931348623157e308", "2.225073858507201e-308"]
)
def test_literal_path_uses_original_bits_not_num_over_den(text, lean_exe, tmp_path):
    source = f"def f():\n    return {text}\n"
    fn = translate(source).fn
    expected = float_bits(float(text))
    ir = run_float(fn, [])
    (lean,) = run_lean(lean_exe, fn.to_json_text(), [[]], mode="float")
    assert float_bits(ir.values[0]) == float_bits(lean.values[0]) == expected
    # The lowering + direct-rational linkage remain kernel-checked with the
    # large denominator (2^1074) carried alongside the float's original bits.
    result = check_lean(tmp_path, compile_source(source, namespace="Literal").lean_source)
    assert result.returncode == 0, result.stdout + result.stderr


@pytest.mark.parametrize("divisor", [0.0, -0.0])
def test_zero_division_even_with_nan_or_infinity(divisor, lean_exe):
    fn = translate("def f(x, y):\n    return x / y\n").fn
    vectors = [[x, divisor] for x in [0.0, 1.0, float("inf"), float("nan")]]
    outputs = run_lean(lean_exe, fn.to_json_text(), vectors, mode="float")
    assert outputs == [Failed("divisionByZero")] * len(vectors)


def test_pow_differs_from_repeated_multiplication_and_handles_overflow(lean_exe):
    # This value's power is a regression against the former multiplication
    # expansion; libm pow and two successive multiplications can round apart.
    x = 0.3
    assert x**3 != x * x * x
    fn = translate("def f(x):\n    return x ** 3\n").fn
    inputs = [[x], [1e308], [-0.0], [float("inf")], [float("nan")]]
    outputs = run_lean(lean_exe, fn.to_json_text(), inputs, mode="float")
    assert float_bits(outputs[0].values[0]) == float_bits(x**3)
    assert outputs[1] == Failed("overflow")
    assert float_bits(outputs[2].values[0]) == float_bits(-0.0)
    assert outputs[3].values[0] == float("inf")
    assert math.isnan(outputs[4].values[0])
    # Base evaluation must not disappear even when the exponent is zero.
    fn = translate("def f(x):\n    return (x / 0) ** 0\n").fn
    assert run_float(fn, [1]) == Failed("divisionByZero")


def test_nan_comparison_and_signed_zero_equality(lean_exe):
    source = "def f(x, y):\n    a = 0\n    b = 0\n    if x == y:\n        a = 1\n    if x != y:\n        b = 1\n    return a, b\n"
    fn = translate(source).fn
    outputs = run_lean(
        lean_exe, fn.to_json_text(), [[-0.0, 0.0], [float("nan"), float("nan")]], mode="float"
    )
    assert outputs == [Returned((1.0, 0.0)), Returned((0.0, 1.0))]


def test_sparse_fallthrough_preserves_slots_and_signed_zero(lean_exe):
    fn = Fn("raw", (), (), Assign(4, Lit(Fraction(0), 1 << 63)))
    ours = run_float(fn, [])
    (theirs,) = run_lean(lean_exe, fn.to_json_text(), [[]], mode="float")
    assert isinstance(theirs, FellThrough)
    assert compare_outcomes(ours, theirs) is None
    assert set(theirs.env) == {4}
    assert float_bits(theirs.env[4]) == hex(1 << 63)


def test_bit_transport_theorem_is_audited(tmp_path):
    text = "import Pontifex.Core.Binary64\nimport Pontifex.Audit.Command\n#audit_axioms Pontifex.Binary64.bits_roundtrip\n"
    result = check_lean(tmp_path, text)
    assert result.returncode == 0, result.stdout + result.stderr


def test_float_boundary_corpus_smoke():
    result = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts/check_float_boundaries.py"),
            "--samples",
            "2048",
            "--arithmetic",
            "256",
        ],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=120,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert "0 mismatches" in result.stdout
    assert "computed_nan_payload" in result.stdout


def test_nonfinite_source_literal_is_explicitly_rejected():
    from pontifex.errors import FrontendError

    with pytest.raises(FrontendError, match="non-finite float literals"):
        translate("def f():\n    return 1e999\n")


def test_nan_exemption_cannot_hide_finite_zero_or_transport_mismatches():
    import runpy

    policy = runpy.run_path(str(ROOT / "scripts/check_float_boundaries.py"))[
        "permitted_nan_difference"
    ]
    left = Returned((from_bits(0x7FF8000000000001),))
    right = Returned((from_bits(0xFFF8000000000002),))
    assert policy(left, right, transport=False, allow_nan=True)
    assert not policy(left, right, transport=True, allow_nan=True)
    assert not policy(left, right, transport=False, allow_nan=False)
    assert not policy(Returned((1.0,)), Returned((2.0,)), transport=False, allow_nan=True)
    assert not policy(Returned((-0.0,)), Returned((0.0,)), transport=False, allow_nan=True)
    assert not policy(Failed("overflow"), Failed("divisionByZero"), transport=False, allow_nan=True)


def test_cli_float_does_not_erase_negative_zero(tmp_path, capsys):
    from pontifex.cli import main

    path = tmp_path / "identity.py"
    path.write_text("def f(x):\n    return x\n")
    assert main(["eval", str(path), "--float", "--args=-0.0"]) == 0
    assert capsys.readouterr().out.strip() == "-0.0"
