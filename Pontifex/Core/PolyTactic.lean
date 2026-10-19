/-
  `rat_ring`: kernel-checked polynomial normalization for `Rat`, in core Lean.

  The tactic reifies both sides of an equality into `Poly.Expr`, evaluates them
  under an environment of the goal's atoms, reduces `Poly.normalize` with the
  kernel, and closes the goal when both normal forms are identical. All
  arithmetic in the check is over `Int`; no `native_decide`, `ring`, or
  `norm_num` is involved. Integer coefficients only: rational literal
  coefficients are rejected with a message asking to clear denominators.
-/
import Lean
import Pontifex.Core.Poly

open Lean Meta Elab Tactic

namespace Pontifex.RatRing

/-- Environment built from the reified atoms; `env i` reduces structurally. -/
def envOf (atoms : List Rat) : Nat → Rat :=
  fun i => atoms.getD i 0

/-- Empty atom list, as a constant so meta code can build it without metavars. -/
def nilRat : List Rat := []

private def isRat (e : Expr) : MetaM Bool :=
  isDefEq e (mkConst ``Rat)

private def mkAtom (e : Expr) (vars : Array Expr) : MetaM (Expr × Array Expr) := do
  if let some i := vars.findIdx? (fun v => v == e) then
    return (mkApp (mkConst ``Pontifex.Poly.Expr.var) (toExpr i), vars)
  let i := vars.size
  return (mkApp (mkConst ``Pontifex.Poly.Expr.var) (toExpr i), vars.push e)

partial def reify (e : Expr) (vars : Array Expr) : MetaM (Expr × Array Expr) := do
  let e ← whnfR e
  let args := e.getAppArgs
  let fn := e.getAppFn
  if fn.isConstOf ``HAdd.hAdd && args.size == 6 then
    let (l, v) ← reify args[4]! vars
    let (r, v) ← reify args[5]! v
    return (mkApp2 (mkConst ``Pontifex.Poly.Expr.add) l r, v)
  else if fn.isConstOf ``HSub.hSub && args.size == 6 then
    let (l, v) ← reify args[4]! vars
    let (r, v) ← reify args[5]! v
    return (mkApp2 (mkConst ``Pontifex.Poly.Expr.sub) l r, v)
  else if fn.isConstOf ``HMul.hMul && args.size == 6 then
    let (l, v) ← reify args[4]! vars
    let (r, v) ← reify args[5]! v
    return (mkApp2 (mkConst ``Pontifex.Poly.Expr.mul) l r, v)
  else if fn.isConstOf ``Neg.neg && args.size == 3 then
    let (p, v) ← reify args[2]! vars
    return (mkApp (mkConst ``Pontifex.Poly.Expr.neg) p, v)
  else if fn.isConstOf ``OfNat.ofNat && args.size == 3 then
    match args[1]! with
    | .lit (.natVal n) =>
        return (mkApp (mkConst ``Pontifex.Poly.Expr.const) (toExpr (Int.ofNat n)), vars)
    | _ => mkAtom e vars
  else if fn.isConstOf ``HDiv.hDiv then
    throwError "rat_ring: rational literal coefficients are not supported; \
      clear denominators before normalizing"
  else
    mkAtom e vars

private def mkExprEval (env p : Expr) : Expr :=
  mkApp2 (mkConst ``Pontifex.Poly.Expr.eval) env p

private def mkNorm (p : Expr) : Expr :=
  mkApp (mkConst ``Pontifex.Poly.normalize) p

private def mkNormalEval (env normal : Expr) : Expr :=
  mkApp2 (mkConst ``Pontifex.Poly.Normal.eval) env normal

private def mkEnv (vars : Array Expr) : MetaM Expr := do
  let list ← vars.foldrM
    (fun v acc => mkAppM ``List.cons #[v, acc])
    (mkConst ``nilRat)
  mkAppM ``envOf #[list]

private def ratTy : Expr := mkConst ``Rat

/-- Raw proof builders. They apply `Eq` constructors without elaborating the
    implicit endpoints, so kernel definitional equality (not the elaborator's
    default transparency) decides whether the chain type-checks. -/
private def mkRefl (x : Expr) : Expr :=
  mkAppN (mkConst ``Eq.refl [Level.one]) #[ratTy, x]

private def mkSymm (a b h : Expr) : Expr :=
  mkAppN (mkConst ``Eq.symm [Level.one]) #[ratTy, a, b, h]

private def mkTrans (a b c h₁ h₂ : Expr) : Expr :=
  mkAppN (mkConst ``Eq.trans [Level.one]) #[ratTy, a, b, c, h₁, h₂]

/-- Close a `Rat` equality by certified polynomial normalization. -/
def ratRing (goal : MVarId) : MetaM Unit := do
  let target ← instantiateMVars (← goal.getType)
  let some (α, lhs, rhs) := target.eq?
    | throwError "rat_ring: goal is not an equality"
  unless ← isRat α do throwError "rat_ring: goal is not over Rat"
  let (pL, vars) ← reify lhs #[]
  let (pR, vars) ← reify rhs vars
  let env ← mkEnv vars
  let evalL := mkExprEval env pL
  let evalR := mkExprEval env pR
  let normL := mkNorm pL
  let normR := mkNorm pR
  let evalNormL := mkNormalEval env normL
  let evalNormR := mkNormalEval env normR
  let nl ← withTransparency .all <| whnf normL
  let nr ← withTransparency .all <| whnf normR
  unless ← withTransparency .all (isDefEq nl nr) do
    throwError "rat_ring: the two sides do not have the same polynomial normal form"
  let hL ← mkAppM ``Pontifex.Poly.eval_normalize #[env, pL]
  let hR ← mkAppM ``Pontifex.Poly.eval_normalize #[env, pR]
  -- lhs is defeq to evalL; rhs is defeq to evalR.  The chain proves
  -- evalL = eval(norm pL) = eval(norm pR) = evalR.
  let step2 := mkRefl evalNormL
  let step3 := mkSymm evalR evalNormR hR
  let inner := mkTrans evalNormL evalNormR evalR step2 step3
  let proof := mkTrans evalL evalNormL evalR hL inner
  goal.assign proof

end Pontifex.RatRing

elab "rat_ring" : tactic => do
  let goal ← getMainGoal
  Pontifex.RatRing.ratRing goal
