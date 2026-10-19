"""Fuel boundaries must match, not merely large-budget terminating runs."""
from fractions import Fraction

import pytest

from pontifex.frontend import translate
from pontifex.interp import OutOfFuel, Returned, run_exact, run_float
from pontifex.pipeline import compare_outcomes, run_lean

PROGRAMS = [
    ("def f(x):\n    return x\n", [1]),
    ("def f(x):\n    x = x + 1\n    return x\n", [1]),
    ("def f(x):\n    if x > 0:\n        x = x + 1\n    return x\n", [1]),
    ("def f(x):\n    if x > 0:\n        x = x + 1\n    return x\n", [-1]),
    ("def f(x):\n    while x < 2:\n        x = x + 1\n    return x\n", [0]),
    ("def f(x):\n    while x < 2:\n        x = x + 1\n    return x\n", [3]),
    ("def f(x):\n    while True:\n        pass\n    return x\n", [0]),
    ("def f(x):\n    if x > 0:\n        while x < 2:\n            x = x + 1\n    return x\n", [1]),
]


@pytest.mark.parametrize("source,args", PROGRAMS)
@pytest.mark.parametrize("mode", ["rat", "float"])
def test_all_small_fuels_match_lean(source, args, mode, lean_exe):
    fn = translate(source).fn
    run = run_exact if mode == "rat" else run_float
    for fuel in range(16):
        ours = run(fn, args, fuel=fuel)
        theirs, = run_lean(lean_exe, fn.to_json_text(), [args], mode=mode, fuel=fuel)
        assert compare_outcomes(ours, theirs) is None, (fuel, ours, theirs)


def test_literal_only_arithmetic_rounds_in_float_mode():
    fn = translate("def f():\n    return (0.1 + 0.2) - 0.3\n").fn
    out = run_float(fn, [])
    assert isinstance(out, Returned)
    assert type(out.values[0]) is float
    assert out.values[0] == (0.1 + 0.2) - 0.3
    assert run_exact(fn, []).values != out.values


def test_fuel_boundaries_are_observable():
    fn = translate("def f(x):\n    return x\n").fn
    assert isinstance(run_exact(fn, [1], fuel=1), OutOfFuel)
    assert run_exact(fn, [1], fuel=2) == Returned((Fraction(1),))
    with pytest.raises(ValueError, match="non-negative"):
        run_exact(fn, [1], fuel=-1)


def test_cli_eval_honors_budget(tmp_path, capsys):
    from pontifex.cli import main

    path = tmp_path / "loop.py"
    path.write_text("def f(x):\n    while x < 2:\n        x = x + 1\n    return x\n")
    assert main(["eval", str(path), "--args", "0", "--fuel", "1"]) == 1
    assert "OutOfFuel" in capsys.readouterr().out
    assert main(["eval", str(path), "--args", "0", "--fuel", "32"]) == 0
    assert capsys.readouterr().out.strip() == "2"


def test_sample_generation_uses_requested_budget(tmp_path):
    from pontifex.cli import main

    source = tmp_path / "branch.py"
    source.write_text("def f(x):\n    if x < 0:\n        x = -x\n    return x\n")
    output = tmp_path / "Branch.lean"
    assert main(["compile", str(source), "--out", str(output), "--fuel", "0", "--with-samples"]) == 0
    text = output.read_text()
    assert "theorem f_link" in text  # the universal certificate still exists
    assert "native_decide" not in text  # zero fuel cannot produce sample returns
