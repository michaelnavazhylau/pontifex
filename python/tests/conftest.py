"""Shared test fixtures and helpers."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "python"))

from pontifex.frontend import Translated, translate  # noqa: E402
from pontifex.pipeline import find_lean_exe  # noqa: E402

EXAMPLES = ROOT / "examples"

STRAIGHT_LINE = ["free_fall", "harmonic_oscillator"]
BRANCHING = ["clamped_step"]
LOOPING = ["free_fall_loop"]


def example_source(stem: str) -> str:
    return (EXAMPLES / f"{stem}.py").read_text()


def translate_example(stem: str) -> Translated:
    path = EXAMPLES / f"{stem}.py"
    return translate(path.read_text(), filename=str(path))


@pytest.fixture(scope="session")
def lean_exe() -> Path:
    exe = find_lean_exe(ROOT)
    if exe is None:
        pytest.skip("Lean runner not built; run `lake build pontifex`")
    return exe


@pytest.fixture(scope="session")
def repo_root() -> Path:
    return ROOT
