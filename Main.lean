import Pontifex.Json

open Pontifex

def usage : IO UInt32 := do
  IO.eprintln "usage: pontifex (rat|float) <ir.json> <inputs.json> [fuel]"
  return 2

/-- Rat inputs use n/d; Float inputs use 0x + up to 16 hexadecimal bits.
    All outputs, including language failures, are machine-readable outcomes. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | mode :: irPath :: inputsPath :: rest =>
    if mode != "rat" && mode != "float" then return ← usage
    let fuel ← match rest with
      | [] => pure 128
      | [f] => match f.toNat? with
        | some n => pure n
        | none => IO.eprintln "fuel must be a natural number"; return 2
      | _ => return ← usage
    let irText ← IO.FS.readFile irPath
    let fn ← match Json.parseFn irText with
      | .ok f => pure f
      | .error e => IO.eprintln s!"error: cannot decode IR: {e}"; return 1
    let inputText ← IO.FS.readFile inputsPath
    let decoded := if mode == "rat" then
        (Json.parseInputs inputText).map (fun rows => rows.map fun vs =>
          Json.encodeOutcome Json.encodeRat (fn.run Ops.rat fuel vs))
      else
        (Json.parseFloatInputs inputText).map (fun rows => rows.map fun vs =>
          Json.encodeOutcome Json.encodeBinary64 (fn.run Ops.binary64 fuel vs))
    match decoded with
    | .error e => IO.eprintln s!"error: cannot decode inputs: {e}"; return 1
    | .ok outputs =>
      IO.println (Lean.Json.compress (Lean.Json.arr outputs.toArray))
      return 0
  | _ => usage
