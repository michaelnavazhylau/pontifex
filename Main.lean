/-
  PyVerif conformance runner.

  Usage:

      pyverif rat   <ir.json> <inputs.json> [fuel]
      pyverif float <ir.json> <inputs.json> [fuel]

  `inputs.json` is an array of argument vectors, each scalar written exactly as
  `"num"` or `"num/den"`.  One JSON object is printed per input vector.

  This executable is the *Lean oracle* used by the Python differential-testing
  harness: the same IR that the Python reference interpreter runs is also run by
  the Lean reference semantics, and the two transcripts are compared.
-/
import PyVerif.Json

open PyVerif

def runOneRat (fn : Fn) (fuel : Nat) (args : List Rat) : Lean.Json :=
  Json.encodeOutcome Json.encodeRat (Fn.run Ops.rat fn fuel args)

def runOneFloat (fn : Fn) (fuel : Nat) (args : List Rat) : Lean.Json :=
  Json.encodeOutcome Json.encodeFloat
    (Fn.run Ops.float fn fuel (args.map Ops.float.ofRat))

def usage : IO UInt32 := do
  IO.eprintln "usage: pyverif (rat|float) <ir.json> <inputs.json> [fuel]"
  return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | mode :: irPath :: inputsPath :: rest =>
      let fuel : Nat :=
        match rest with
        | [] => 128
        | f :: _ => (f.toNat?).getD 128
      let irText ← IO.FS.readFile irPath
      let fn ←
        match Json.parseFn irText with
        | .ok fn => pure fn
        | .error e => do
            IO.eprintln s!"error: cannot decode IR: {e}"
            return 1
      let inputText ← IO.FS.readFile inputsPath
      let inputs ←
        match Json.parseInputs inputText with
        | .ok is => pure is
        | .error e => do
            IO.eprintln s!"error: cannot decode inputs: {e}"
            return 1
      let outputs := inputs.map fun args =>
        match mode with
        | "rat" => runOneRat fn fuel args
        | "float" => runOneFloat fn fuel args
        | _ => Lean.Json.str "unknown-mode"
      IO.println (Lean.Json.compress (Lean.Json.arr outputs.toArray))
      return 0
  | _ => usage
