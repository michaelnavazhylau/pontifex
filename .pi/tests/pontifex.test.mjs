import assert from "node:assert/strict";
import { mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";
import { canonicalPath, createArtifactGuard, protectedArtifact } from "../extensions/pontifex/guards.mjs";
import { commandInput, features, runWorkflow, summarize, workflowArgs } from "../extensions/pontifex/bridge.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "../..");
function fixture(t) {
  const path = canonicalPath(mkdtempSync(join(tmpdir(), "pontifex-guard-")));
  t.after(() => rmSync(path, { recursive: true, force: true }));
  return path;
}

test("protect all generated paths, including missing files and normalized absolute paths", (t) => {
  const repo = fixture(t);
  const guard = createArtifactGuard(repo);
  for (const path of ["Pontifex/Generated/New.lean", "Pontifex/Generated.lean", "Pontifex/Audit.lean", "NativeTests.lean", "build/ir/new.json"]) {
    assert.equal(guard.check("write", { path }, repo).block, true);
    assert.equal(guard.check("edit", { path: join(repo, path) }, repo).block, true);
    assert.equal(guard.check("write", { path: `../${path}` }, join(repo, "python")).block, true);
  }
  assert.equal(guard.check("write", { path: "Pontifex/Generated/../Audit.lean" }, repo).block, true);
});

test("source files, corpus data, unrelated tools, temporary corruption tests, and sibling repos remain writable", (t) => {
  const repo = fixture(t);
  const guard = createArtifactGuard(repo);
  for (const path of ["python/pontifex/emit.py", "corpus/manifest.json", "Pontifex/Examples/New.lean", "tests/Certificate.lean", "../sibling/Pontifex/Audit.lean"]) {
    assert.equal(guard.check("write", { path }, repo), undefined);
  }
  assert.equal(guard.check("bash", { command: "anything" }, repo), undefined);
  assert.equal(guard.check("write", {}, repo), undefined);
});

test("symlink aliases cannot accidentally bypass generated protection", (t) => {
  const repo = fixture(t);
  mkdirSync(join(repo, "Pontifex/Generated"), { recursive: true });
  writeFileSync(join(repo, "Pontifex/Generated/X.lean"), "generated");
  symlinkSync(join(repo, "Pontifex/Generated"), join(repo, "alias"));
  assert.equal(createArtifactGuard(repo).check("edit", { path: "alias/X.lean" }, repo).block, true);
  assert.equal(protectedArtifact(repo, repo, "alias/Missing.lean"), join(repo, "Pontifex/Generated/Missing.lean"));
  const outside = fixture(t);
  writeFileSync(join(outside, "source.lean"), "external target");
  symlinkSync(join(outside, "source.lean"), join(repo, "Pontifex/Audit.lean"));
  assert.equal(createArtifactGuard(repo).check("write", { path: "Pontifex/Audit.lean" }, repo).block, true);
});

test("one-shot exceptions match exactly one canonical artifact and reset at session boundaries", (t) => {
  const repo = fixture(t);
  const guard = createArtifactGuard(repo);
  const target = join(repo, "Pontifex/Audit.lean");
  guard.allow(target);
  assert.equal(guard.check("write", { path: "Pontifex/Generated.lean" }, repo).block, true);
  assert.equal(guard.check("read", { path: target }, repo), undefined); // Not consumed by reads.
  assert.equal(guard.check("edit", { path: target }, repo), undefined);
  assert.equal(guard.check("edit", { path: target }, repo).block, true);
  guard.allow(target);
  guard.clear();
  assert.equal(guard.check("write", { path: target }, repo).block, true);
  assert.equal(canonicalPath(target), target);
});

test("feature names match the single repository index", () => {
  const mapping = JSON.parse(readFileSync(join(root, "scripts/workflow_features.json"), "utf8"));
  assert.deepEqual([...features].sort(), Object.keys(mapping).sort());
});

test("commands default to status and never interpolate shell input", () => {
  assert.deepEqual(commandInput(""), { action: "status", profile: undefined, features: [] });
  assert.deepEqual(commandInput("validate focused calls,selection"), { action: "validate", profile: "focused", features: ["calls", "selection"] });
  assert.deepEqual(commandInput("lookup calls"), { action: "lookup", features: ["calls"] });
  for (const input of ["validate full;rm", "lookup calls extra", "status full", "validate full calls extra"]) {
    assert.throws(() => commandInput(input));
  }
  assert.throws(() => workflowArgs({ action: "lookup", features: ["calls", "float"] }));
  assert.throws(() => workflowArgs({ action: "validate", features: ["calls; touch /tmp/x"] }));
  assert.throws(() => workflowArgs({ action: "unknown" }));
});

test("process adapter forwards signal, root, fixed argv, and honest focused coverage", async () => {
  const signal = new AbortController().signal;
  let call;
  const pi = { exec: async (...args) => {
    call = args;
    return { stdout: JSON.stringify({ profile: "focused", status: "PASS", full_verified: false, steps: [{ name: "pytest", status: "PASS", tests: { tests: 2, skipped: 0 } }], logs: "/logs" }), stderr: "", code: 0, killed: false };
  } };
  const result = await runWorkflow(pi, root, { action: "validate", profile: "focused", features: ["calls"] }, signal);
  assert.equal(call[0], "uv");
  assert.deepEqual(call[1].slice(0, 4), ["run", "--locked", "--no-sync", "python"]);
  assert.equal(call[2].cwd, root);
  assert.equal(call[2].signal, signal);
  assert.equal(result.fullVerified, false);
  assert.match(result.summary, /Full verification: INCOMPLETE/);
  assert.equal(result.logs, "/logs");
});

test("adapter preserves failed/incomplete statuses and never upgrades killed results", async () => {
  for (const status of ["FAIL", "INCOMPLETE"]) {
    const pi = { exec: async () => ({ stdout: JSON.stringify({ status, full_verified: false }), stderr: "", code: 1, killed: false }) };
    assert.equal((await runWorkflow(pi, root, { action: "validate" })).status, status);
  }
  const pi = { exec: async () => ({ stdout: JSON.stringify({ status: "PASS", full_verified: true }), stderr: "", code: 0, killed: true }) };
  const result = await runWorkflow(pi, root, { action: "validate" });
  assert.equal(result.status, "INCOMPLETE");
  assert.equal(result.fullVerified, false);
});

test("non-JSON process failures retain full output outside model context", async (t) => {
  const repo = fixture(t);
  const output = "x".repeat(20000);
  const pi = { exec: async () => ({ stdout: output, stderr: "missing dependencies", code: 2, killed: false }) };
  const result = await runWorkflow(pi, repo, { action: "plan" });
  assert.equal(result.status, "INCOMPLETE");
  assert.ok(result.summary.length < 8000);
  assert.ok(readFileSync(join(result.logs, "process.log"), "utf8").includes(output));
});

test("summaries retain scope and log pointers while bounding diagnostics", () => {
  const result = summarize({ status: "FAIL", full_verified: false, steps: Array.from({ length: 20 }, () => ({ name: "failure", status: "FAIL", diagnostic: "x".repeat(20000) })), logs: "/complete/logs" });
  assert.ok(result.summary.length < 8000);
  assert.match(result.summary, /Full verification: INCOMPLETE/);
  assert.ok(result.summary.endsWith("Logs: /complete/logs"));
});

test("extension source exposes a small codemode tool and operator-only exception command", () => {
  const source = readFileSync(join(root, ".pi/extensions/pontifex/index.ts"), "utf8");
  assert.match(source, /exposure: "codemode"/);
  assert.match(source, /outputSchema:/);
  assert.match(source, /structuredContent: result/);
  assert.match(source, /triggerTurn: false/);
  assert.match(source, /ctx\.ui\.confirm/);
  assert.match(source, /session_switch/);
});
