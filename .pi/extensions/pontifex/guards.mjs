// Accident prevention for built-in edit/write calls, not a sandbox or shell parser.
import { realpathSync } from "node:fs";
import { dirname, isAbsolute, relative, resolve } from "node:path";

export function canonicalPath(path) {
  const absolute = resolve(path);
  try {
    return realpathSync(absolute);
  } catch (error) {
    if (error.code !== "ENOENT" && error.code !== "ENOTDIR") throw error;
    const parent = dirname(absolute);
    if (parent === absolute) return absolute;
    return resolve(canonicalPath(parent), relative(parent, absolute));
  }
}

export function protectedArtifact(root, cwd, path) {
  if (typeof path !== "string" || !path) return undefined;
  const target = canonicalPath(resolve(cwd, path));
  const names = [
    relative(canonicalPath(root), target),
    relative(resolve(root), resolve(cwd, path)),
  ].map((name) => name.split("\\").join("/"));
  if (names.some((name) => !name.startsWith("../") && !isAbsolute(name) && (
    name === "NativeTests.lean" ||
    name === "Pontifex/Generated.lean" ||
    name === "Pontifex/Audit.lean" ||
    (name.startsWith("Pontifex/Generated/") && name.endsWith(".lean")) ||
    (name.startsWith("build/ir/") && name.endsWith(".json"))
  ))) return target;
  return undefined;
}

export function createArtifactGuard(root) {
  const permitted = new Set();
  return {
    allow(path) { permitted.add(canonicalPath(path)); },
    clear() { permitted.clear(); },
    check(toolName, input, cwd) {
      if (toolName !== "edit" && toolName !== "write") return undefined;
      const path = protectedArtifact(root, cwd, input?.path);
      if (!path) return undefined;
      if (permitted.delete(path)) return undefined;
      return {
        block: true,
        reason: `Generated artifact: ${path}. Edit its generator, then run ` +
          "uv run python scripts/generate.py. For a deliberate one-shot exception, " +
          "ask the operator to run /pontifex-allow-generated PATH. " +
          "Corruption tests should use temporary files outside generated directories.",
      };
    },
  };
}
