"""P0/T2: generated artifacts must not smuggle in axioms or untrusted proofs."""
from __future__ import annotations

import re
import subprocess

from conftest import ROOT

GENERATED_DIR = ROOT / "PyVerif" / "Generated"
AUDIT_FILE = ROOT / "PyVerif" / "Audit.lean"


def _generated_modules():
    return sorted(p for p in GENERATED_DIR.glob("*.lean") if p.name != "Generated.lean")


def test_generated_modules_contain_no_sorry_or_axiom():
    for path in _generated_modules():
        text = path.read_text()
        assert not re.search(r"\bsorry\b", text), path
        assert not re.search(r"(?m)^\s*(axiom|opaque)\b", text), path


def test_native_decide_only_in_labelled_sample_theorems():
    for path in _generated_modules():
        text = path.read_text()
        blocks = re.split(r"\n(?=(?:theorem|def|example|set_option)\b)", text)
        for block in blocks:
            if "native_decide" not in block:
                continue
            names = re.findall(r"theorem\s+(\w+)", block)
            assert names, f"native_decide outside a theorem in {path}"
            assert all("_sample_" in name for name in names), (path, names)


def _run_lean(tmp_path, text: str):
    path = tmp_path / "Audit.lean"
    path.write_text(text)
    return subprocess.run(
        ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True, timeout=120
    )


def test_axiom_audit_accepts_kernel_proofs(tmp_path):
    result = _run_lean(
        tmp_path,
        "import PyVerif.Audit.Command\n"
        "theorem good : (1 : Nat) + 1 = 2 := rfl\n"
        "#audit_axioms good\n",
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_axiom_audit_rejects_native_decide(tmp_path):
    result = _run_lean(
        tmp_path,
        "import PyVerif.Audit.Command\n"
        "theorem cheat : (1 : Nat) + 1 = 2 := by native_decide\n"
        "#audit_axioms cheat\n",
    )
    assert result.returncode != 0
    output = result.stdout + result.stderr
    assert "axiom audit failed" in output
    assert "cheat" in output


def test_axiom_audit_rejects_sorry(tmp_path):
    result = _run_lean(
        tmp_path,
        "import PyVerif.Audit.Command\n"
        "theorem hole : (1 : Nat) + 1 = 2 := by sorry\n"
        "#audit_axioms hole\n",
    )
    assert result.returncode != 0
    assert "axiom audit failed" in (result.stdout + result.stderr)


def test_audit_manifest_covers_every_generated_certificate():
    audited = set(re.findall(r"#audit_axioms\s+(\S+)", AUDIT_FILE.read_text()))
    missing: list[str] = []
    for path in _generated_modules():
        namespace = f"PyVerif.Generated.{path.stem}"
        text = path.read_text()
        for fn in re.findall(r"def\s+(\w+)IR\s*:\s*Fn", text):
            for suffix in ("_lowering", "_link"):
                name = f"{namespace}.{fn}{suffix}"
                if name not in audited:
                    missing.append(name)
    assert not missing, missing
