/-
  Bounded white-box inlining. No call node survives into the IR (schema 3).
  The caller evaluates arguments once, left to right, into a fresh frame;
  callee slots are relocated by an offset. Only straight-line scalar bodies
  ending in one return are accepted. A tail call retains that return.

  Like Lower.lean, this is a kernel-reducible reference algorithm, not a
  semantic-preservation theorem. Generated per-callee lowering certificates
  and a compositional program certificate check its inputs; source fidelity
  and the algorithm's correspondence to Python remain tested boundaries.
-/
import Pontifex.Core.IR

namespace Pontifex.Inline

/-- Relocate scalar arithmetic, rejecting expressions outside this first slice. -/
def shiftExpr (offset : Nat) : Expr → Except String Expr
  | .slot i => .ok (.slot (offset + i))
  | .lit q => .ok (.lit q)
  | .floatLit q bits => .ok (.floatLit q bits)
  | .bin op a b => do return .bin op (← shiftExpr offset a) (← shiftExpr offset b)
  | .un op a => do return .un op (← shiftExpr offset a)
  | .pow a n => do return .pow (← shiftExpr offset a) n
  | _ => .error "inlined helpers must use only scalar arithmetic"

mutual

def flatten : Stmt → List Stmt
  | .seq ss => flattenList ss
  | s => [s]

def flattenList : List Stmt → List Stmt
  | [] => []
  | s :: rest => flatten s ++ flattenList rest

end

/-- Frame size is derived from actual writes and parameter slots, never the
    cosmetic `Fn.slotNames` metadata. Source lowering allocates dense slots. -/
def frameSize (arity : Nat) (body : Stmt) : Nat :=
  (flatten body).foldl (fun size stmt =>
    match stmt with
    | .assign slot _ => max size (slot + 1)
    | _ => size) arity

/-- Relocate assignments, and bind (or retain) the final return. In particular,
    a return in a non-final position is rejected, not silently rewritten. -/
def relocate (offset : Nat) (target : Option Nat) : List Stmt → Except String (List Stmt)
  | [.ret [e]] => do
      let e' ← shiftExpr offset e
      return [match target with | some i => .assign i e' | none => .ret [e']]
  | .assign i e :: rest => do
      let e' ← shiftExpr offset e
      return .assign (offset + i) e' :: (← relocate offset target rest)
  | .skip :: rest => do return .skip :: (← relocate offset target rest)
  | _ => .error "inlined helpers must be straight-line with one final scalar return"

/-- Argument expressions refer to the caller frame and are NOT relocated. -/
def expand (offset arity : Nat) (target : Option Nat) (body : Stmt)
    (args : List Expr) : Except String Stmt := do
  if args.length != arity then throw "inline call arity mismatch"
  let bindings := args.zipIdx.map fun (e, i) => Stmt.assign (offset + i) e
  let body' ← relocate offset target (flatten body)
  return .seq (bindings ++ body')

end Pontifex.Inline
