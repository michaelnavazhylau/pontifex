/-
  PyVerif.Audit.Command

  Build-time audit of the kernel dependencies of generated certificates.

  `#audit_axioms foo bar` checks that `foo` and `bar` depend only on Lean's
  standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`).  It
  rejects `sorryAx`, `Lean.ofReduceBool` (the trust hook behind
  `native_decide`), and any project-specific axiom.

  `PyVerif/Audit.lean` is generated and lists every lowering/linkage theorem,
  so `lake build` fails if a certificate ever acquires a disallowed dependency.
-/
import Lean

open Lean Elab Command

namespace PyVerif.Audit

/-- Axioms permitted in kernel-checked certificates. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- Check that each identifier's proof depends only on `allowedAxioms`. -/
def auditAxioms (names : Array Name) : CommandElabM Unit := do
  let mut bad : Array (Name × Name) := #[]
  for name in names do
    let axioms ← Lean.collectAxioms (m := CommandElabM) name
    for ax in axioms do
      unless allowedAxioms.contains ax do
        bad := bad.push (name, ax)
  unless bad.isEmpty do
    let lines := bad.toList.map fun (n, a) => s!"  {n} depends on disallowed axiom {a}"
    throwError "axiom audit failed:\n{String.intercalate "\n" lines}"

end PyVerif.Audit

elab "#audit_axioms " ids:ident+ : command => do
  PyVerif.Audit.auditAxioms (ids.map (·.getId))
