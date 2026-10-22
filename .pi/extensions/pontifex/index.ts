import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { dirname, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { commandInput, runWorkflow } from "./bridge.mjs";
import { createArtifactGuard, protectedArtifact } from "./guards.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "../../..");
const feature = Type.Union([
  Type.Literal("core"), Type.Literal("calls"), Type.Literal("selection"),
  Type.Literal("arrays"), Type.Literal("float"), Type.Literal("proofs"), Type.Literal("lowering"),
]);

export default function (pi: ExtensionAPI) {
  const guard = createArtifactGuard(root);
  for (const event of ["session_start", "session_switch", "session_shutdown"] as const) {
    pi.on(event, () => guard.clear());
  }
  pi.on("tool_call", (event, ctx) => guard.check(event.toolName, event.input, ctx.cwd));

  pi.registerTool({
    name: "pontifex_workflow",
    label: "Pontifex workflow",
    description: "Plan or run source-preserving validation, inspect fingerprinted status, or locate reusable feature implementations. Focused is not full verification; no regeneration.",
    exposure: "codemode",
    namespace: { name: "pontifex", description: "Bounded project validation and reusable feature navigation" },
    executionMode: "sequential",
    annotations: { readOnlyHint: false, destructiveHint: false, idempotentHint: false, openWorldHint: false },
    parameters: Type.Object({
      action: Type.Union([Type.Literal("plan"), Type.Literal("validate"), Type.Literal("status"), Type.Literal("lookup")]),
      profile: Type.Optional(Type.Union([Type.Literal("freshness"), Type.Literal("focused"), Type.Literal("full")])),
      features: Type.Optional(Type.Array(feature, { maxItems: 7 })),
    }, { additionalProperties: false }),
    outputSchema: Type.Object({
      summary: Type.String(), status: Type.String(), fullVerified: Type.Boolean(),
      profile: Type.Optional(Type.String()), logs: Type.Optional(Type.String()),
    }, { additionalProperties: false }),
    async execute(_id, input, signal) {
      const result = await runWorkflow(pi, root, input, signal);
      return {
        content: [{ type: "text", text: result.summary }],
        structuredContent: result,
        details: result,
        isError: result.status === "FAIL" || result.status === "INCOMPLETE",
      };
    },
  });

  pi.registerCommand("pontifex", {
    description: "Project workflow: status | lookup [feature] | plan/validate [profile] [feature,...]",
    handler: async (args, ctx) => {
      try {
        const result = await runWorkflow(pi, root, commandInput(args), undefined);
        // No triggerTurn: user commands do not spend a model request to explain deterministic output.
        pi.sendMessage({ customType: "pontifex-workflow", content: result.summary, display: true }, { triggerTurn: false });
      } catch (error) {
        if (ctx.hasUI) ctx.ui.notify(String(error), "error");
        else throw error;
      }
    },
  });

  pi.registerCommand("pontifex-allow-generated", {
    description: "Operator-confirmed one-shot edit/write exception for one generated artifact",
    handler: async (args, ctx) => {
      const path = protectedArtifact(root, ctx.cwd, args.trim());
      if (!path) {
        if (ctx.hasUI) ctx.ui.notify("Specify one protected generated artifact path.", "warning");
        return;
      }
      if (!ctx.hasUI) throw new Error("Generated-file exceptions require operator confirmation in a UI; use the generator otherwise.");
      if (await ctx.ui.confirm("Allow one generated-file edit?", `${path}\nPrefer changing the generator; this permission expires after one edit/write or session change.`)) {
        guard.allow(path);
        ctx.ui.notify(`Allowed one edit/write: ${path}`, "warning");
      }
    },
  });
}
