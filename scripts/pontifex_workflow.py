#!/usr/bin/env python3
"""Bounded, deterministic project navigation and validation. No regeneration or LLM calls.

Run with ``uv run --locked --no-sync python scripts/pontifex_workflow.py --help``.
Validation writes build products and ignored logs, never intentionally edits sources.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.metadata
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import xml.etree.ElementTree as ET
from contextlib import contextmanager
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FEATURES = Path(__file__).with_name("workflow_features.json")
UV = ["uv", "run", "--locked", "--no-sync"]
PROFILES = ("freshness", "focused", "full")


def feature_map() -> dict:
    return json.loads(FEATURES.read_text())


def lookup(root: Path, feature: str | None = None) -> dict:
    features = feature_map()
    if feature is None:
        return {"features": {name: item["summary"] for name, item in features.items()}}
    if feature not in features:
        raise ValueError(f"unknown feature {feature!r}; choose from {', '.join(features)}")
    item = features[feature]
    locations = []
    for ref in item["symbols"]:
        path, symbol = ref["path"], ref["symbol"]
        pattern = re.compile(
            r"^\s*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
            r"(?:def|class|theorem|inductive|structure)\s+" + re.escape(symbol) + r"(?=[\s(:{]|$)"
        )
        lines = (root / path).read_text().splitlines() if (root / path).is_file() else []
        matches = [i for i, line in enumerate(lines, 1) if pattern.search(line)]
        locations.append({**ref, "lines": matches, "status": "FOUND" if matches else "MISSING"})
    return {"feature": feature, **item, "symbols": locations}


def git_files(root: Path) -> list[str]:
    result = subprocess.run(
        ["git", "ls-files", "-co", "--exclude-standard", "-z"],
        cwd=root,
        capture_output=True,
        check=True,
    )
    return sorted(set(os.fsdecode(result.stdout).strip("\0").split("\0")) - {""})


def source_fingerprint(root: Path) -> str:
    digest = hashlib.sha256()
    for name in git_files(root):
        path = root / name
        digest.update(os.fsencode(name) + b"\0")
        if path.is_symlink():
            data = os.fsencode(os.readlink(path))
        elif path.is_file():
            data = path.read_bytes()
        else:
            data = b"<missing>"
        digest.update(hashlib.sha256(data).digest())
    return digest.hexdigest()


def tool_identity(command: list[str], root: Path) -> dict:
    try:
        result = subprocess.run(
            command, cwd=root, capture_output=True, text=True, timeout=15, check=False
        )
        return {
            "code": result.returncode,
            "version": (result.stdout + result.stderr).strip()[:1000],
        }
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {"error": str(exc)}


def fingerprint(root: Path) -> dict:
    """Persist identities, not environment secrets. Cached reports are never executed/reused."""
    packages = {}
    for name in ("pytest", "hypothesis", "ruff"):
        try:
            packages[name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            packages[name] = None
    runner = Path(os.environ.get("PONTIFEX_EXE", root / ".lake/build/bin/pontifex"))
    if not runner.is_absolute():
        runner = root / runner
    runner_hash = hashlib.sha256(runner.read_bytes()).hexdigest() if runner.is_file() else None
    environment = {
        "python": sys.version,
        "executable": sys.executable,
        "platform": platform.platform(),
        "packages": packages,
        "uv": tool_identity(["uv", "--version"], root),
        "lean": tool_identity(["lake", "env", "lean", "--version"], root),
        "paths": {name: shutil.which(name) for name in ("uv", "lake", "leanchecker")},
        "runner": str(runner),
        "runner_hash": runner_hash,
        "env_hash": hashlib.sha256(
            json.dumps(dict(sorted(os.environ.items())), sort_keys=True).encode()
        ).hexdigest(),
    }
    source = source_fingerprint(root)
    value = hashlib.sha256(json.dumps([source, environment], sort_keys=True).encode()).hexdigest()
    return {"digest": value, "source": source, "environment": environment}


def step(name: str, argv: list[str], *, timeout: int = 300, junit: bool = False) -> dict:
    return {"name": name, "argv": argv, "timeout": timeout, "junit": junit}


def plan(profile: str, features: list[str] | None = None) -> dict:
    if profile not in PROFILES:
        raise ValueError(f"unknown profile: {profile}")
    features = sorted(set(features or ["core"]))
    mapping = feature_map()
    unknown = set(features) - mapping.keys()
    if unknown:
        raise ValueError(f"unknown features: {', '.join(sorted(unknown))}")
    checks = [
        step("format", UV + ["ruff", "format", "--check", "python", "scripts"]),
        step("generated", UV + ["python", "scripts/generate.py", "--check"]),
        step("rejections", UV + ["python", "scripts/update_rejections.py", "--check"]),
    ]
    if profile != "freshness":
        checks += [step("lean-build-audit", ["lake", "build"], timeout=1800)]
        # Building first prevents stale or absent local runners; reject external overrides below.
        checks += [
            step(
                "runner",
                UV
                + [
                    "python",
                    "-c",
                    (
                        "import os; from pathlib import Path; p = Path('.lake/build/bin/pontifex'); "
                        "assert p.is_file() and os.access(p, os.X_OK), 'local Lean runner missing'; print(p)"
                    ),
                ],
            )
        ]
        if profile == "full":
            checks += [
                step("kernel-replay", ["lake", "env", "leanchecker", "Pontifex"], timeout=1800),
                step("native-samples", ["lake", "build", "PontifexNativeTests"], timeout=900),
                step("corpus", UV + ["python", "scripts/run_corpus.py", "--samples", "32"]),
                step("pi-workflow-tests", ["node", "--test", ".pi/tests/pontifex.test.mjs"]),
                step(
                    "float-boundaries",
                    UV + ["python", "scripts/check_float_boundaries.py"],
                    timeout=900,
                ),
            ]
        tests = (
            sorted({p for name in features for p in mapping[name]["tests"]})
            if profile == "focused"
            else ["python/tests"]
        )
        checks += [step("pytest", UV + ["pytest", "-ra", *tests], timeout=2700, junit=True)]
    return {
        "profile": profile,
        "features": features,
        "steps": checks,
        "coverage": {
            "freshness": True,
            "build_and_axiom_audit": profile != "freshness",
            "kernel_replay": profile == "full",
            "native_samples": profile == "full",
            "differential_corpora": profile == "full",
            "all_pytest": profile == "full",
            "lint": False,
            "pi_extension_tests": profile == "full",
        },
        "note": "Focused selection is explicit, not a proof of dependency completeness. No regeneration.",
    }


def junit_counts(path: Path) -> dict:
    tree = ET.parse(path)
    suites = [tree.getroot()] if tree.getroot().tag == "testsuite" else tree.findall(".//testsuite")
    if not suites:
        raise ValueError("JUnit report contains no test suites")
    return {
        key: sum(int(s.get(key, 0)) for s in suites)
        for key in ("tests", "failures", "errors", "skipped")
    }


def stop_process(proc: subprocess.Popen) -> None:
    if os.name == "posix":
        # Children (uv/lake/Lean) share this new group. Also kill descendants after parent exit.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    elif proc.poll() is None:
        proc.kill()
    proc.wait()


def execute(check: dict, root: Path, directory: Path) -> dict:
    log = directory / f"{check['name']}.log"
    argv = list(check["argv"])
    report = directory / "pytest.xml"
    if check["junit"]:
        argv += [f"--junitxml={report}"]
    start = time.monotonic()
    result = {"name": check["name"], "argv": argv, "log": str(log), "status": "PASS"}
    with log.open("w") as output:
        output.write(json.dumps(argv) + "\n")
        output.flush()
        try:
            proc = subprocess.Popen(
                argv,
                cwd=root,
                stdout=output,
                stderr=subprocess.STDOUT,
                start_new_session=os.name == "posix",
            )
        except OSError as exc:
            output.write(str(exc) + "\n")
            result.update(status="INCOMPLETE", exit_code=None, reason=str(exc))
        else:
            try:
                code = proc.wait(timeout=check["timeout"])
                result.update(exit_code=code, status="PASS" if code == 0 else "FAIL")
            except subprocess.TimeoutExpired:
                stop_process(proc)
                result.update(status="INCOMPLETE", exit_code=proc.returncode, reason="timeout")
            except KeyboardInterrupt:
                stop_process(proc)
                result.update(status="INCOMPLETE", exit_code=proc.returncode, reason="cancelled")
    result["seconds"] = round(time.monotonic() - start, 2)
    if check["junit"] and result["status"] == "PASS":
        try:
            counts = junit_counts(report)
            result["tests"] = counts
            if counts["errors"] or counts["failures"]:
                result.update(status="FAIL", reason="JUnit reports failures/errors")
            elif counts["skipped"] or not counts["tests"]:
                result.update(status="INCOMPLETE", reason="skipped tests or empty test suite")
        except (OSError, ET.ParseError, ValueError) as exc:
            result.update(status="INCOMPLETE", reason=f"missing/invalid JUnit coverage: {exc}")
    if result["status"] != "PASS":
        # Only bounded failure context enters the model; the complete log remains on disk.
        with log.open("rb") as source:
            source.seek(max(0, log.stat().st_size - 3000))
            result["diagnostic"] = source.read().decode(errors="replace")
    return result


@contextmanager
def validation_lock(state: Path):
    """Serialize lake builds and last-report updates across sessions (macOS/Linux)."""
    import fcntl

    with (state / "validation.lock").open("w") as lock:
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise ValueError("another Pontifex validation is running") from exc
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def save_report(state: Path, report: dict) -> None:
    encoded = json.dumps(report, indent=2) + "\n"
    (Path(report["logs"]) / "report.json").write_text(encoded)
    temporary = state / "last.tmp"
    temporary.write_text(encoded)
    temporary.replace(state / "last.json")


def validate(root: Path, profile: str, features: list[str] | None = None) -> dict:
    selected = plan(profile, features)
    state = root / ".pi/state"
    state.mkdir(parents=True, exist_ok=True)
    with validation_lock(state):
        directory = Path(tempfile.mkdtemp(prefix="run-", dir=state)).resolve()
        before = source_fingerprint(root)
        report = {
            **selected,
            "steps": [],
            "requested_coverage": selected["coverage"],
            "coverage": dict.fromkeys(selected["coverage"], False),
            "status": "INCOMPLETE",
            "full_verified": False,
            "logs": str(directory),
            "time": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        }
        report["fingerprint"] = fingerprint(root)
        save_report(state, report)  # Never leave an old PASS visible while a new run is pending.
        # External overrides can bypass the freshly built oracle and invalidate evidence.
        override = os.environ.get("PONTIFEX_EXE")
        if (
            profile != "freshness"
            and override
            and Path(override).resolve() != (root / ".lake/build/bin/pontifex").resolve()
        ):
            report["reason"] = (
                "unset PONTIFEX_EXE: verification requires the local freshly built runner"
            )
        else:
            blocked = False
            for check in selected["steps"]:
                result = (
                    {
                        "name": check["name"],
                        "status": "NOT_RUN",
                        "reason": "previous gate did not pass",
                    }
                    if blocked
                    else execute(check, root, directory)
                )
                report["steps"].append(result)
                blocked |= result["status"] != "PASS"
            statuses = {item["status"] for item in report["steps"]}
            report["status"] = (
                "FAIL" if "FAIL" in statuses else "PASS" if statuses == {"PASS"} else "INCOMPLETE"
            )
        passed = {item["name"] for item in report["steps"] if item["status"] == "PASS"}
        report["coverage"].update(
            freshness={"format", "generated", "rejections"} <= passed,
            build_and_axiom_audit="lean-build-audit" in passed,
            kernel_replay="kernel-replay" in passed,
            native_samples="native-samples" in passed,
            differential_corpora={"corpus", "float-boundaries"} <= passed,
            all_pytest=profile == "full" and "pytest" in passed,
            pi_extension_tests="pi-workflow-tests" in passed,
        )
        report["fingerprint"] = fingerprint(root)
        if before != report["fingerprint"]["source"]:
            report.update(
                status="INCOMPLETE", reason="source files changed during validation; rerun"
            )
        report["full_verified"] = profile == "full" and report["status"] == "PASS"
        save_report(state, report)
        return report


def status(root: Path) -> dict:
    path = root / ".pi/state/last.json"
    if not path.is_file():
        return {"status": "NOT_RUN", "full_verified": False}
    report = json.loads(path.read_text())
    current = fingerprint(root)["digest"] == report["fingerprint"]["digest"]
    return {
        **report,
        "current": current,
        "recorded_status": report["status"],
        "status": report["status"] if current else "STALE",
        "full_verified": current and report["full_verified"],
    }


def render(data: dict) -> str:
    if "symbols" in data:
        lines = [f"{data['feature']}: {data['summary']}"]
        lines += [
            f"{ref['path']}:{','.join(map(str, ref['lines'])) or 'MISSING'} — {ref['symbol']}"
            for ref in data["symbols"]
        ]
        lines += ["Tests: " + ", ".join(data["tests"]), "Docs: " + ", ".join(data["docs"])]
        lines += ["! " + hazard for hazard in data["hazards"]]
        return "\n".join(lines)
    if "status" not in data and "steps" not in data:
        return "\n".join(f"{name}: {summary}" for name, summary in data["features"].items())
    lines = [f"Profile: {data.get('profile', 'none')} | Status: {data.get('status', 'PLAN')}"]
    if "full_verified" in data:
        lines += ["Full verification: " + ("PASS" if data["full_verified"] else "INCOMPLETE")]
    for check in data.get("steps", []):
        lines.append(f"{check['name']}: {check.get('status', 'PLANNED')}")
        if "status" not in check:
            lines.append("  " + json.dumps(check["argv"]))
        if "tests" in check:
            lines.append("  " + json.dumps(check["tests"], sort_keys=True))
        if "reason" in check:
            lines.append("  " + check["reason"])
        if "diagnostic" in check:
            lines.append(check["diagnostic"])
    lines += (
        [f"Coverage: {json.dumps(data['coverage'], sort_keys=True)}"] if "coverage" in data else []
    )
    for key in ("reason", "note", "logs"):
        if key in data:
            lines.append(f"{key}: {data[key]}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "validate", "status", "lookup"))
    parser.add_argument("--profile", choices=PROFILES, default="freshness")
    parser.add_argument("--feature", action="append", choices=sorted(feature_map()))
    parser.add_argument("--json", action="store_true", help="machine-readable result")
    args = parser.parse_args(argv)
    try:
        if args.action == "lookup":
            if args.feature and len(args.feature) != 1:
                raise ValueError("lookup accepts exactly one --feature")
            data = lookup(ROOT, args.feature[0] if args.feature else None)
        elif args.action == "plan":
            data = plan(args.profile, args.feature)
        elif args.action == "status":
            data = status(ROOT)
        else:
            data = validate(ROOT, args.profile, args.feature)
    except (OSError, ValueError, subprocess.SubprocessError, KeyboardInterrupt) as exc:
        data = {"status": "INCOMPLETE", "full_verified": False, "reason": str(exc)}
    public = {key: value for key, value in data.items() if key != "fingerprint"}
    print(json.dumps(public, indent=2) if args.json else render(public))
    return 1 if data.get("status") == "FAIL" else 2 if data.get("status") == "INCOMPLETE" else 0


if __name__ == "__main__":

    def interrupt(signum, frame):
        raise KeyboardInterrupt

    signal.signal(signal.SIGTERM, interrupt)
    raise SystemExit(main())
