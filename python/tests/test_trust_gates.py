"""P0/T2: generated artifacts must not smuggle in axioms or untrusted proofs."""

from __future__ import annotations

import re
import subprocess

import pytest
from conftest import ROOT
from lean_helpers import check_lean

GENERATED_DIR = ROOT / "Pontifex" / "Generated"
AUDIT_FILE = ROOT / "Pontifex" / "Audit.lean"


def _generated_modules():
    return sorted(p for p in GENERATED_DIR.glob("*.lean") if p.name != "Generated.lean")


def test_generated_modules_contain_no_sorry_or_axiom():
    for path in _generated_modules():
        text = path.read_text()
        assert not re.search(r"\bsorry\b", text), path
        assert not re.search(r"(?m)^\s*(axiom|opaque)\b", text), path


def _lean_code(text: str) -> str:
    """Mask nested comments and strings, retaining line positions for diagnostics."""
    result = []
    index, depth = 0, 0
    while index < len(text):
        if text.startswith("/-", index):
            depth += 1
            result.append("  ")
            index += 2
        elif depth and text.startswith("-/", index):
            depth -= 1
            result.append("  ")
            index += 2
        elif depth:
            result.append("\n" if text[index] == "\n" else " ")
            index += 1
        elif text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end == -1 else end
            result.append(" " * (end - index))
            index = end
        elif text[index] == '"':
            result.append(" ")
            index += 1
            while index < len(text):
                char = text[index]
                result.append("\n" if char == "\n" else " ")
                index += 1
                if char == "\\" and index < len(text):
                    result.append("\n" if text[index] == "\n" else " ")
                    index += 1
                elif char == '"':
                    break
        else:
            result.append(text[index])
            index += 1
    return "".join(result)


def _native_boundary_violations(root):
    violations = []
    for path in sorted(root.rglob("*.lean")):
        relative = path.relative_to(root)
        if set(relative.parts) & {".lake", ".git", ".venv", "build"}:
            continue
        code = _lean_code(path.read_text())
        if relative.as_posix() == "NativeTests.lean":
            continue  # The only permitted native test module.
        for match in re.finditer(r"\bnative_decide\b|\bimport\s+[^\n]*\bNativeTests\b", code):
            line = code.count("\n", 0, match.start()) + 1
            violations.append(f"{relative}:{line}: {match.group()}")
    return violations


def test_native_decide_only_in_dedicated_test_module():
    assert not _native_boundary_violations(ROOT)


@pytest.mark.parametrize(
    "path",
    [
        "Pontifex/Generated/Cheat.lean",
        "Pontifex/Core/Cheat.lean",
        "Pontifex/Spec/Cheat.lean",
        "Elsewhere.lean",
    ],
)
def test_native_boundary_rejects_even_labelled_samples_elsewhere(tmp_path, path):
    target = tmp_path / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("theorem f_sample_0 : True := by native_decide\n")
    assert _native_boundary_violations(tmp_path) == [f"{path}:1: native_decide"]


@pytest.mark.parametrize(
    "command",
    ["import NativeTests", "import Pontifex.Core.Ops NativeTests", "public import NativeTests"],
)
def test_native_boundary_rejects_imports_and_allows_only_explicit_test_module(tmp_path, command):
    (tmp_path / "NativeTests.lean").write_text("example : True := by native_decide\n")
    (tmp_path / "Main.lean").write_text(command + "\n")
    match = command.removeprefix("public ")
    assert _native_boundary_violations(tmp_path) == [f"Main.lean:1: {match}"]


def test_native_boundary_ignores_documentation_and_string_literals(tmp_path):
    (tmp_path / "Doc.lean").write_text(
        "/- native_decide /- nested -/ import NativeTests -/\n"
        "-- native_decide\n"
        'def message := "native_decide \\" import NativeTests"\n'
    )
    assert not _native_boundary_violations(tmp_path)


@pytest.mark.slow
def test_native_samples_are_an_explicit_nondefault_build_target():
    config = (ROOT / "lakefile.toml").read_text()
    defaults = re.search(r"defaultTargets\s*=\s*\[([^]]*)\]", config)
    assert defaults and "PontifexNativeTests" not in defaults.group(1)
    assert re.search(r'name = "PontifexNativeTests"\s+roots = \["NativeTests"\]', config)
    result = subprocess.run(
        ["lake", "build", "PontifexNativeTests"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=120,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def _run_lean(tmp_path, text: str):
    return check_lean(tmp_path, text, name="Audit.lean", timeout=120)


def test_axiom_audit_accepts_kernel_proofs(tmp_path):
    result = _run_lean(
        tmp_path,
        "import Pontifex.Audit.Command\n"
        "theorem good : (1 : Nat) + 1 = 2 := rfl\n"
        "#audit_axioms good\n",
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_axiom_audit_rejects_native_decide(tmp_path):
    result = _run_lean(
        tmp_path,
        "import Pontifex.Audit.Command\n"
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
        "import Pontifex.Audit.Command\n"
        "theorem hole : (1 : Nat) + 1 = 2 := by sorry\n"
        "#audit_axioms hole\n",
    )
    assert result.returncode != 0
    assert "axiom audit failed" in (result.stdout + result.stderr)


def test_audit_manifest_covers_every_generated_certificate():
    audited = set(re.findall(r"#audit_axioms\s+(\S+)", AUDIT_FILE.read_text()))
    assert "Pontifex.Spec.modifiedEnergyGridOk_eq_true" in audited
    assert not any("_sample_" in name for name in audited)
    missing: list[str] = []
    for path in _generated_modules():
        # Call dependencies live in private, recursively nested namespaces.
        namespaces: list[str] = []
        for line in path.read_text().splitlines():
            namespace = re.fullmatch(r"namespace (\S+)", line)
            if namespace:
                namespaces.append(namespace.group(1))
            elif re.fullmatch(r"end \S+", line):
                namespaces.pop()
            else:
                theorem = re.match(r"theorem (\w+)", line)
                if theorem and theorem.group(1).endswith(("_lowering", "_link")):
                    name = ".".join([*namespaces, theorem.group(1)])
                    if name not in audited:
                        missing.append(name)
    assert not missing, missing
