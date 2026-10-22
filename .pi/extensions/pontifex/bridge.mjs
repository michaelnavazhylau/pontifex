// Pure formatting and a thin process adapter; usable without loading the Pi runtime.
import { mkdir, mkdtemp, writeFile } from "node:fs/promises";
import { join } from "node:path";

export const actions = ["plan", "validate", "status", "lookup"];
export const profiles = ["freshness", "focused", "full"];
export const features = ["core", "calls", "selection", "arrays", "float", "proofs", "lowering"];

export function workflowArgs(input) {
  if (!actions.includes(input.action)) throw new Error("Unknown workflow action");
  if (input.profile && !profiles.includes(input.profile)) throw new Error("Unknown validation profile");
  if (input.features?.some((feature) => !features.includes(feature))) throw new Error("Unknown feature");
  if (input.action === "lookup" && input.features?.length > 1) throw new Error("Lookup accepts one feature");
  const args = ["run", "--locked", "--no-sync", "python", "scripts/pontifex_workflow.py", input.action, "--json"];
  if (input.profile) args.push("--profile", input.profile);
  for (const feature of input.features ?? []) args.push("--feature", feature);
  return args;
}

export function commandInput(args) {
  const [action = "status", second, third, ...extra] = args.trim().split(/\s+/).filter(Boolean);
  if (extra.length || (action === "lookup" && third) || (action === "status" && second)) {
    throw new Error("Usage: /pontifex [status|lookup [feature]|plan|validate [profile] [feature,...]]");
  }
  const input = action === "lookup"
    ? { action, features: second ? [second] : [] }
    : { action, profile: second, features: third ? third.split(",") : [] };
  workflowArgs(input); // Slash commands and tool calls share validation; no shell interpolation.
  return input;
}

export function summarize(data) {
  const lines = [];
  if (data.feature) {
    lines.push(`${data.feature}: ${data.summary}`);
    for (const ref of data.symbols ?? []) lines.push(`${ref.path}:${ref.lines.join(",") || "MISSING"} — ${ref.symbol}`);
    lines.push(`Tests: ${data.tests.join(", ")}`, `Docs: ${data.docs.join(", ")}`);
    lines.push(...data.hazards.map((hazard) => `! ${hazard}`));
  } else if (!data.steps && data.features && !Array.isArray(data.features)) {
    lines.push(...Object.entries(data.features).map(([name, summary]) => `${name}: ${summary}`));
  } else {
    lines.push(`Profile: ${data.profile ?? "none"} | Status: ${data.status ?? "PLAN"}`);
    lines.push(`Full verification: ${data.full_verified ? "PASS" : "INCOMPLETE"}`);
    for (const check of data.steps ?? []) {
      lines.push(`${check.name}: ${check.status ?? "PLANNED"}`);
      if (!check.status) lines.push(`  ${JSON.stringify(check.argv)}`);
      if (check.tests) lines.push(`  ${JSON.stringify(check.tests)}`);
      if (check.reason) lines.push(`  ${check.reason}`);
      if (check.diagnostic) lines.push(check.diagnostic.slice(-1800));
    }
    if (data.coverage) lines.push(`Coverage: ${JSON.stringify(data.coverage)}`);
  }
  if (data.reason) lines.push(`Reason: ${data.reason}`);
  if (data.note) lines.push(data.note);
  // Bound model-facing text, retaining the log pointer and explicit scope at the end.
  let summary = lines.join("\n");
  if (summary.length > 7500) summary = summary.slice(0, 7500) + "\n[Summary truncated; inspect full logs.]";
  if (data.logs) summary += `\nLogs: ${data.logs}`;
  return {
    summary,
    status: data.status ?? "INFO",
    fullVerified: data.full_verified === true,
    ...(data.profile ? { profile: data.profile } : {}),
    ...(data.logs ? { logs: data.logs } : {}),
  };
}

export async function runWorkflow(pi, root, input, signal) {
  const args = workflowArgs(input);
  const result = await pi.exec("uv", args, { cwd: root, signal, timeout: 2 * 60 * 60 * 1000 });
  let data;
  try {
    data = JSON.parse(result.stdout);
    if (!data || typeof data !== "object" || Array.isArray(data)) throw new Error("Invalid result");
  } catch {
    const state = join(root, ".pi/state");
    await mkdir(state, { recursive: true });
    const logs = await mkdtemp(join(state, "bridge-"));
    await writeFile(join(logs, "process.log"), result.stdout + "\n" + result.stderr);
    data = {
      status: "INCOMPLETE", full_verified: false, logs,
      reason: `Workflow process did not return JSON (exit ${result.code}). ${result.stderr.slice(-1500)}`,
    };
  }
  if (result.killed || (result.code !== 0 && !["FAIL", "INCOMPLETE"].includes(data.status))) {
    data = { ...data, status: "INCOMPLETE", full_verified: false, reason: "Workflow process interrupted or failed" };
  }
  return summarize(data);
}
