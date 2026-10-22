"""Workflow infrastructure tests: no Lean process or model calls required."""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest
from conftest import ROOT

SPEC = importlib.util.spec_from_file_location(
    "pontifex_workflow", ROOT / "scripts/pontifex_workflow.py"
)
workflow = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(workflow)


@pytest.fixture
def repo(tmp_path):
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    (tmp_path / ".gitignore").write_text(".pi/state/\n__pycache__/\n")
    (tmp_path / "source.py").write_text("x = 1\n")
    return tmp_path


@pytest.fixture
def identities(monkeypatch):
    monkeypatch.setattr(workflow, "tool_identity", lambda *args: {"version": "test", "code": 0})


def test_feature_index_resolves_all_references():
    for name in workflow.feature_map():
        result = workflow.lookup(ROOT, name)
        assert all(ref["status"] == "FOUND" for ref in result["symbols"]), result
        for path in result["tests"] + result["docs"]:
            assert (ROOT / path).is_file(), path
    assert "calls" in workflow.lookup(ROOT)["features"]
    with pytest.raises(ValueError, match="unknown feature"):
        workflow.lookup(ROOT, "made-up")


def test_freshness_never_regenerates_or_builds():
    result = workflow.plan("freshness")
    commands = [item["argv"] for item in result["steps"]]
    assert all("--check" in cmd for cmd in commands)
    assert not result["coverage"]["build_and_axiom_audit"]
    assert not any(cmd[:2] == ["lake", "build"] for cmd in commands)


def test_focused_builds_before_tests_and_explicitly_selects_modules():
    result = workflow.plan("focused", ["selection", "calls", "selection"])
    names = [item["name"] for item in result["steps"]]
    assert names.index("lean-build-audit") < names.index("runner") < names.index("pytest")
    tests = result["steps"][-1]["argv"]
    assert "python/tests/test_selection.py" in tests
    assert tests.count("python/tests/test_calls.py") == 1
    assert "-m" not in tests
    assert not result["coverage"]["all_pytest"]
    with pytest.raises(ValueError, match="unknown features"):
        workflow.plan("focused", ["missing"])


def test_full_plan_covers_all_project_verification_gates():
    result = workflow.plan("full")
    assert {
        "kernel-replay",
        "native-samples",
        "corpus",
        "float-boundaries",
        "pi-workflow-tests",
        "pytest",
    } <= {item["name"] for item in result["steps"]}
    assert "python/tests" in result["steps"][-1]["argv"]
    assert not result["coverage"]["lint"]  # Formatting and linting are distinct claims.
    assert result["coverage"]["pi_extension_tests"]
    assert "--no-sync" in result["steps"][-1]["argv"]


@pytest.mark.parametrize("skipped,expected", [(0, "PASS"), (1, "INCOMPLETE")])
def test_junit_skips_are_not_full_coverage(tmp_path, skipped, expected):
    source = (
        "import pathlib, sys; "
        "pathlib.Path(sys.argv[-1].split('=', 1)[1]).write_text("
        f'\'<testsuites><testsuite tests="2" failures="0" errors="0" skipped="{skipped}"/>\''
        "'</testsuites>')"
    )
    result = workflow.execute(
        workflow.step("pytest", [sys.executable, "-c", source], junit=True), tmp_path, tmp_path
    )
    assert result["status"] == expected
    assert result["tests"]["skipped"] == skipped
    assert Path(result["log"]).is_file()


def test_missing_junit_is_incomplete(tmp_path):
    result = workflow.execute(
        workflow.step("pytest", [sys.executable, "-c", "pass"], junit=True), tmp_path, tmp_path
    )
    assert result["status"] == "INCOMPLETE"
    assert "JUnit" in result["reason"]


def test_failures_preserve_exit_code_full_logs_and_bounded_diagnostics(tmp_path):
    result = workflow.execute(
        workflow.step("failure", [sys.executable, "-c", "print('x' * 20000); raise SystemExit(7)"]),
        tmp_path,
        tmp_path,
    )
    assert result["status"] == "FAIL"
    assert result["exit_code"] == 7
    assert len(result["diagnostic"]) <= 3000
    assert Path(result["log"]).stat().st_size > 20000


def test_timeout_and_missing_tool_are_incomplete(tmp_path):
    result = workflow.execute(
        workflow.step(
            "timeout", [sys.executable, "-c", "import time; time.sleep(10)"], timeout=0.05
        ),
        tmp_path,
        tmp_path,
    )
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "timeout"
    result = workflow.execute(
        workflow.step("missing", [str(tmp_path / "not-an-executable")]), tmp_path, tmp_path
    )
    assert result["status"] == "INCOMPLETE"
    assert result["exit_code"] is None


@pytest.mark.parametrize("profile", ["freshness", "focused", "full"])
def test_profile_success_never_overstates_full_verification(repo, identities, monkeypatch, profile):
    monkeypatch.delenv("PONTIFEX_EXE", raising=False)
    monkeypatch.setattr(
        workflow, "execute", lambda check, *args: {"name": check["name"], "status": "PASS"}
    )
    before = (repo / "source.py").read_bytes()
    result = workflow.validate(repo, profile, ["calls"])
    assert result["status"] == "PASS"
    assert result["full_verified"] == (profile == "full")
    assert (repo / "source.py").read_bytes() == before
    assert (repo / ".pi/state/last.json").is_file()
    assert (Path(result["logs"]) / "report.json").is_file()
    assert workflow.status(repo)["current"]


def test_failure_stops_later_gates_and_remains_failure(repo, identities, monkeypatch):
    calls = []

    def fail(check, *args):
        calls.append(check["name"])
        return {"name": check["name"], "status": "FAIL", "exit_code": 9}

    monkeypatch.setattr(workflow, "execute", fail)
    result = workflow.validate(repo, "freshness")
    assert result["status"] == "FAIL"
    assert not result["full_verified"]
    assert calls == ["format"]
    assert result["steps"][1]["status"] == "NOT_RUN"
    assert not any(result["coverage"].values())
    assert result["requested_coverage"]["freshness"]


def test_pending_run_replaces_previous_success(repo, identities, monkeypatch):
    monkeypatch.delenv("PONTIFEX_EXE", raising=False)
    monkeypatch.setattr(
        workflow, "execute", lambda check, *args: {"name": check["name"], "status": "PASS"}
    )
    assert workflow.validate(repo, "full")["full_verified"]

    def observe_pending(check, *args):
        pending = json.loads((repo / ".pi/state/last.json").read_text())
        assert pending["status"] == "INCOMPLETE"
        assert not pending["full_verified"]
        assert not any(pending["coverage"].values())
        return {"name": check["name"], "status": "PASS"}

    monkeypatch.setattr(workflow, "execute", observe_pending)
    assert workflow.validate(repo, "full")["full_verified"]


def test_cancellation_is_incomplete_and_stops_the_process_group(tmp_path, monkeypatch):
    class Interrupted:
        returncode = -9

        def wait(self, **kwargs):
            raise KeyboardInterrupt

    proc = Interrupted()
    stopped = []
    monkeypatch.setattr(workflow.subprocess, "Popen", lambda *args, **kwargs: proc)
    monkeypatch.setattr(workflow, "stop_process", lambda process: stopped.append(process))
    result = workflow.execute(workflow.step("cancel", ["unused"]), tmp_path, tmp_path)
    assert result["status"] == "INCOMPLETE"
    assert result["reason"] == "cancelled"
    assert stopped == [proc]


def test_source_edits_during_run_invalidate_success(repo, identities, monkeypatch):
    def mutate(check, *args):
        (repo / "source.py").write_text("x = 2\n")
        return {"name": check["name"], "status": "PASS"}

    monkeypatch.setattr(workflow, "execute", mutate)
    result = workflow.validate(repo, "freshness")
    assert result["status"] == "INCOMPLETE"
    assert "source files changed" in result["reason"]


def test_external_runner_override_cannot_bypass_local_build(repo, identities, monkeypatch):
    monkeypatch.setenv("PONTIFEX_EXE", "/tmp/external-runner")
    result = workflow.validate(repo, "full")
    assert result["status"] == "INCOMPLETE"
    assert not result["full_verified"]
    assert not result["steps"]
    assert "PONTIFEX_EXE" in result["reason"]


def test_status_invalidates_source_tool_environment_and_runner_changes(
    repo, identities, monkeypatch
):
    monkeypatch.delenv("PONTIFEX_EXE", raising=False)
    monkeypatch.setattr(
        workflow, "execute", lambda check, *args: {"name": check["name"], "status": "PASS"}
    )
    workflow.validate(repo, "full")
    assert workflow.status(repo)["full_verified"]
    original = (repo / "source.py").read_text()
    (repo / "source.py").write_text("x = 7\n")
    assert workflow.status(repo)["status"] == "STALE"
    (repo / "source.py").write_text(original)
    assert workflow.status(repo)["current"]
    monkeypatch.setenv("PONTIFEX_WORKFLOW_TEST", "changed")
    assert not workflow.status(repo)["full_verified"]
    monkeypatch.delenv("PONTIFEX_WORKFLOW_TEST")
    executable = repo / ".lake/build/bin/pontifex"
    executable.parent.mkdir(parents=True)
    executable.write_bytes(b"changed runner")
    assert not workflow.status(repo)["current"]
    executable.unlink()
    monkeypatch.setattr(workflow, "tool_identity", lambda *args: {"version": "changed", "code": 0})
    assert not workflow.status(repo)["current"]


def test_fingerprint_includes_untracked_deleted_and_lock_files(repo):
    before = workflow.source_fingerprint(repo)
    (repo / "uv.lock").write_text("version = 1\n")
    assert workflow.source_fingerprint(repo) != before
    (repo / "uv.lock").unlink()
    assert workflow.source_fingerprint(repo) == before
    (repo / "source.py").unlink()
    assert workflow.source_fingerprint(repo) != before


def test_concurrent_validation_is_rejected(repo):
    state = repo / ".pi/state"
    state.mkdir(parents=True)
    with (
        workflow.validation_lock(state),
        pytest.raises(ValueError, match="another Pontifex validation"),
        workflow.validation_lock(state),
    ):
        pytest.fail("lock unexpectedly acquired")


def test_status_without_report_is_not_run(repo):
    assert workflow.status(repo) == {"status": "NOT_RUN", "full_verified": False}


def test_make_check_does_not_regenerate_and_formatter_does_not_hide_lint_failures():
    text = (ROOT / "Makefile").read_text()
    assert "check: fmt-check\n" in text
    assert "|| true" not in text
    assert "lint:\n\tuv run ruff check python scripts" in text


def test_cli_machine_result_and_invalid_inputs():
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts/pontifex_workflow.py"), "plan", "--json"],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0
    assert json.loads(result.stdout)["profile"] == "freshness"
    result = subprocess.run(
        [
            sys.executable,
            str(ROOT / "scripts/pontifex_workflow.py"),
            "lookup",
            "--feature",
            "unknown",
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 2
