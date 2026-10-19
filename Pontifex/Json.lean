/-
  Pontifex.Json

  JSON wire format for the IR.

  The Python frontend is the producer; this module is the *consumer*.  Keeping
  a single machine-readable IR (rather than only emitting Lean source text) is
  what lets the Lean side be an independent semantic oracle for differential
  testing, and it is the natural seam for a future proof-producing translator.

  Literals are transmitted as exact `num`/`den` integer pairs.  Never as JSON
  floats: a float literal would silently commit the frontend to one numeric
  interpretation.
-/
import Lean
import Pontifex.Core.Config
import Pontifex.Core.Semantics

namespace Pontifex.Json

open Lean

/-! ## Small helpers -/

private def getNat (j : Json) (k : String) : Except String Nat :=
  j.getObjVal? k >>= Json.getNat?

private def getInt (j : Json) (k : String) : Except String Int :=
  j.getObjVal? k >>= Json.getInt?

private def getStr (j : Json) (k : String) : Except String String :=
  j.getObjVal? k >>= Json.getStr?

private def getArr (j : Json) (k : String) : Except String (Array Json) :=
  j.getObjVal? k >>= Json.getArr?

/-! ## Decoding -/

def decodeBinOp (s : String) : Except String BinOp :=
  match s with
  | "add" => .ok .add
  | "sub" => .ok .sub
  | "mul" => .ok .mul
  | "div" => .ok .div
  | other => .error s!"unknown binary operator '{other}'"

def decodeCmpOp (s : String) : Except String CmpOp :=
  match s with
  | "lt" => .ok .lt
  | "le" => .ok .le
  | "gt" => .ok .gt
  | "ge" => .ok .ge
  | "eq" => .ok .eq
  | "ne" => .ok .ne
  | other => .error s!"unknown comparison operator '{other}'"

def decodeUnOp (s : String) : Except String UnOp :=
  match s with
  | "neg" => .ok .neg
  | "abs" => .ok .abs
  | other => .error s!"unknown unary operator '{other}'"

mutual

partial def decodeExpr (j : Json) : Except String Expr := do
  match ← getStr j "k" with
  | "slot" => return .slot (← getNat j "i")
  | "lit" =>
      let num ← getInt j "num"
      let den ← getNat j "den"
      if den == 0 then throw "literal denominator must be positive"
      return .lit (Rat.divInt num (Int.ofNat den))
  | "floatLit" =>
      let num ← getInt j "num"
      let den ← getNat j "den"
      if den == 0 then throw "literal denominator must be positive"
      let bitsText ← getStr j "bits"
      let some bits := bitsText.toNat? | throw "invalid float literal bits"
      if bits >= 2^64 then throw "float literal bits exceed 64 bits"
      return .floatLit (Rat.divInt num (Int.ofNat den)) (UInt64.ofNat bits)
  | "pow" =>
      let ej ← j.getObjVal? "e"
      let e ← decodeExpr ej
      return .pow e (← getNat j "n")
  | "bin" =>
      let op ← decodeBinOp (← getStr j "op")
      let lj ← j.getObjVal? "l"
      let rj ← j.getObjVal? "r"
      let l ← decodeExpr lj
      let r ← decodeExpr rj
      return .bin op l r
  | "un" =>
      let op ← decodeUnOp (← getStr j "op")
      let ej ← j.getObjVal? "e"
      let e ← decodeExpr ej
      return .un op e
  | "index" =>
      let aj ← j.getObjVal? "a"
      let ij ← j.getObjVal? "i"
      return .index (← decodeExpr aj) (← decodeExpr ij)
  | "len" =>
      let aj ← j.getObjVal? "a"
      return .len (← decodeExpr aj)
  | "arrayLit" =>
      let arr ← getArr j "es"
      return .arrayLit (← arr.toList.mapM decodeExpr)
  | "set" =>
      let aj ← j.getObjVal? "a"
      let ij ← j.getObjVal? "i"
      let vj ← j.getObjVal? "v"
      return .set (← decodeExpr aj) (← decodeExpr ij) (← decodeExpr vj)
  | other => throw s!"unknown expression kind '{other}'"

partial def decodeCond (j : Json) : Except String Cond := do
  match ← getStr j "k" with
  | "cmp" =>
      let op ← decodeCmpOp (← getStr j "op")
      let lj ← j.getObjVal? "l"
      let rj ← j.getObjVal? "r"
      let l ← decodeExpr lj
      let r ← decodeExpr rj
      return .cmp op l r
  | "and" =>
      let lj ← j.getObjVal? "l"
      let rj ← j.getObjVal? "r"
      let l ← decodeCond lj
      let r ← decodeCond rj
      return .and l r
  | "or" =>
      let lj ← j.getObjVal? "l"
      let rj ← j.getObjVal? "r"
      let l ← decodeCond lj
      let r ← decodeCond rj
      return .or l r
  | "not" =>
      let ej ← j.getObjVal? "e"
      let e ← decodeCond ej
      return .not e
  | "const" =>
      let bj ← j.getObjVal? "b"
      let b ← Json.getBool? bj
      return .const b
  | other => throw s!"unknown condition kind '{other}'"

partial def decodePhi (j : Json) : Except String Phi := do
  return { slot := ← getNat j "slot", lhs := ← getNat j "lhs", rhs := ← getNat j "rhs" }

partial def decodePhis (j : Json) (k : String) : Except String (List Phi) := do
  let arr ← getArr j k
  arr.toList.mapM decodePhi

partial def decodeStmt (j : Json) : Except String Stmt := do
  match ← getStr j "k" with
  | "skip" => return .skip
  | "assign" =>
      let ej ← j.getObjVal? "e"
      let e ← decodeExpr ej
      return .assign (← getNat j "slot") e
  | "seq" =>
      let arr ← getArr j "ss"
      return .seq (← arr.toList.mapM decodeStmt)
  | "ite" =>
      let cj ← j.getObjVal? "c"
      let tj ← j.getObjVal? "t"
      let ej ← j.getObjVal? "e"
      let c ← decodeCond cj
      let t ← decodeStmt tj
      let e ← decodeStmt ej
      let phis ← decodePhis j "phis"
      return .ite c t e phis
  | "while" =>
      let cj ← j.getObjVal? "c"
      let bj ← j.getObjVal? "body"
      let c ← decodeCond cj
      let body ← decodeStmt bj
      let phis ← decodePhis j "phis"
      return .whil c phis body
  | "ret" =>
      let arr ← getArr j "es"
      return .ret (← arr.toList.mapM decodeExpr)
  | other => throw s!"unknown statement kind '{other}'"

end

def decodeStrList (j : Json) (k : String) : Except String (List String) := do
  let arr ← getArr j k
  arr.toList.mapM Json.getStr?

def decodeFn (j : Json) : Except String Fn := do
  let version ← getNat j "irVersion"
  if version != Pontifex.irSchemaVersion then
    throw s!"IR version mismatch: artifact has version {version}, \
      this library expects {Pontifex.irSchemaVersion}; regenerate the artifact"
  let name ← getStr j "name"
  let params ← decodeStrList j "params"
  let slotNames ← decodeStrList j "slotNames"
  let bj ← j.getObjVal? "body"
  let body ← decodeStmt bj
  return { name, params, slotNames, body }

def parseFn (s : String) : Except String Fn :=
  Json.parse s >>= decodeFn

/-! ## Encoding results -/

/-- Exact rational rendered as `num/den` (integers, no whitespace). -/
def encodeRat (q : Rat) : Json :=
  Json.str s!"{q.num}/{q.den}"

/-- Float rendered as the hexadecimal bit pattern, so the Python harness can
    compare bit-for-bit (avoids decimal round-trip discrepancies). -/
def encodeFloat (f : Float) : Json :=
  Json.str s!"0x{String.ofList (Nat.toDigits 16 (UInt64.toNat (Float.toBits f)))}"

def encodeBinary64 (x : Binary64) : Json :=
  Json.str s!"0x{String.ofList (Nat.toDigits 16 x.bits.toNat)}"

def encodeVals (enc : α → Json) (vs : List α) : Json :=
  Json.arr (vs.toArray.map enc)

def encodeOutcome (enc : α → Json) : Outcome α → Json
  | .returned vs => Json.mkObj [("kind", Json.str "returned"), ("vals", encodeVals enc vs)]
  | .fellThrough env => Json.mkObj [("kind", Json.str "fellThrough"),
      ("slots", Json.arr (env.toArray.map fun slot => match slot with
        | none => Json.null
        | some (.scalar x) => enc x
        | some (.array xs) => Json.arr (xs.toArray.map enc)))]
  | .outOfFuel => Json.mkObj [("kind", Json.str "outOfFuel")]
  | .stuck => Json.mkObj [("kind", Json.str "stuck")]
  | .failed e => Json.mkObj [("kind", Json.str "failed"), ("error", Json.str (match e with
      | .divisionByZero => "divisionByZero"
      | .overflow => "overflow"
      | .indexOutOfBounds => "indexOutOfBounds"
      | .assertionFailure => "assertionFailure"))]

/-! ## Input parsing (exact rationals) -/

/-- Parse `"n"` or `"n/d"` into an exact rational. -/
def parseRat (s : String) : Except String Rat :=
  match s.splitOn "/" with
  | [n] =>
      match n.toInt? with
      | some i => .ok (Rat.divInt i 1)
      | none => .error s!"expected an integer, got '{n}'"
  | [n, d] =>
      match n.toInt?, d.toNat? with
      | some i, some j => if j == 0 then .error "zero denominator" else .ok (Rat.divInt i (Int.ofNat j))
      | _, _ => .error s!"expected n/d with integers, got '{s}'"
  | _ => .error s!"expected n or n/d, got '{s}'"

def parseInputs (s : String) : Except String (List (List Rat)) := do
  let j ← Json.parse s
  let rows ← j.getArr?
  rows.toList.mapM fun row => do
    let items ← row.getArr?
    items.toList.mapM fun v => do
      parseRat (← Json.getStr? v)

/-- Hexadecimal wire input is authoritative in Float mode. It preserves all
    binary64 patterns, including signed zero and NaN payloads. Rational strings
    remain a convenience for humans, not the bit-exact protocol. -/
def parseFloat (s : String) : Except String Binary64 := do
  if s.startsWith "0x" then
    let chars := (s.drop 2).toString.toList
    if chars.isEmpty || chars.length > 16 then throw "expected 1..16 hexadecimal digits"
    let bits ← chars.foldlM (fun acc c => do
      let code := c.toNat
      let digit ←
        if 48 ≤ code && code ≤ 57 then pure (code - 48)
        else if 97 ≤ code && code ≤ 102 then pure (code - 87)
        else if 65 ≤ code && code ≤ 70 then pure (code - 55)
        else throw "invalid hexadecimal float bits"
      return acc * 16 + digit) 0
    return Binary64.ofBits (UInt64.ofNat bits)
  let q ← parseRat s
  return Ops.binary64.ofRat q

def parseFloatInputs (s : String) : Except String (List (List Binary64)) := do
  let j ← Json.parse s
  let rows ← j.getArr?
  rows.toList.mapM fun row => do
    let items ← row.getArr?
    items.toList.mapM fun v => do
      parseFloat (← Json.getStr? v)

end Pontifex.Json
