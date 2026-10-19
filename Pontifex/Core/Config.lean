/-
  Pontifex.Core.Config

  Semantic configuration stamped into every generated artifact.

  A proof can silently weaken when a semantic parameter changes (numeric mode,
  fuel discipline, IR schema).  Generated modules therefore record the
  configuration they were produced under and the build checks it against the
  Lean-side schema version.  This mirrors Charon's version-plus-options
  stamping, scaled down to a single scalar schema.

  Bump `irSchemaVersion` together with `IR_VERSION` in
  `python/pontifex/version.py`; regeneration then updates every artifact, and a
  mismatch fails `#guard` in the generated module.
-/
import Std

namespace Pontifex

/-- How the artifact's linkage theorem treats fuel. -/
inductive FuelPolicy where
  /-- Linkage is proved at one literal fuel budget (straight-line code). -/
  | literal
  /-- Linkage holds for every fuel and every numeric backend (control flow). -/
  | allFuel
  deriving Repr, DecidableEq

/-- Numeric reading used by the emitted executable definition. -/
inductive NumericMode where
  | exactRat
  | binary64
  deriving Repr, DecidableEq

/-- Configuration of one generated artifact. -/
structure Config where
  irVersion : Nat
  fuelPolicy : FuelPolicy
  numericMode : NumericMode
  deriving Repr, DecidableEq

/-- Schema version of the IR, JSON wire format, and generated-artifact shape. -/
def irSchemaVersion : Nat := 2

/-- Does this artifact use the schema version this library understands? -/
def Config.schemaMatches (c : Config) : Bool :=
  c.irVersion == irSchemaVersion

end Pontifex
