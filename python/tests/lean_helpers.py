"""Shared kernel-checking infrastructure, not a correctness oracle."""

from __future__ import annotations

import subprocess

from conftest import ROOT


def check_lean(tmp_path, source: str, *, timeout: int = 90, name: str = "Certificate.lean"):
    path = tmp_path / name
    path.write_text(source)
    return subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        check=False,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
