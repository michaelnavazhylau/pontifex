/-
  Pontifex.Core.Poly

  A certified multivariate polynomial normalizer over `Rat` for core Lean
  (no Mathlib, no `ring` tactic).

  * `Expr` is a raw expression tree (integer constants, variables, `+ - * neg`).
    Its evaluation is structural, so reifying a goal side yields a term that is
    definitionally equal to that side.
  * `Normal` is canonical sparse data: terms with integer coefficients and
    sorted monomials, sorted by monomial with equal monomials merged.
  * `normalize` uses only `Int` and list operations (kernel-reducible), and
    `eval_normalize` proves `Expr.eval env p = Normal.eval env (normalize p)`.
  * The tactic reifies both sides, reduces the normal forms, and closes the
    goal when they are identical.

  Only integer coefficients are supported. Rational literal coefficients must be
  cleared by the caller.
-/
import Std
import Pontifex.Tactic

-- Proof scripts below deliberately over-specify simp sets while iterating;
-- the kernel checks the resulting terms, so warning noise is disabled here.
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace Pontifex
namespace Poly

/-! ## Raw polynomials -/

inductive Expr where
  | const : Int → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | neg : Expr → Expr
  deriving Repr, DecidableEq

@[reducible] def Expr.eval (env : Nat → Rat) : Expr → Rat
  | .const c => (c : Rat)
  | .var i => env i
  | .add p q => p.eval env + q.eval env
  | .sub p q => p.eval env - q.eval env
  | .mul p q => p.eval env * q.eval env
  | .neg p => -p.eval env

/-! ## Canonical normal forms -/

structure Mono where
  vars : List Nat
  deriving Repr, DecidableEq

structure Term where
  coeff : Int
  mono : Mono
  deriving Repr, DecidableEq

abbrev Normal := List Term

@[reducible] def evalVars (env : Nat → Rat) : List Nat → Rat
  | [] => 1
  | v :: vs => env v * evalVars env vs

@[reducible] def Mono.eval (env : Nat → Rat) (m : Mono) : Rat :=
  evalVars env m.vars

@[reducible] def Term.eval (env : Nat → Rat) (t : Term) : Rat :=
  (t.coeff : Rat) * Mono.eval env t.mono

@[reducible] def Normal.eval (env : Nat → Rat) : Normal → Rat
  | [] => 0
  | t :: ts => t.eval env + Normal.eval env ts

/-! ## Monomials -/

def listLt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true else if y < x then false else listLt xs ys

def Mono.lt (a b : Mono) : Bool := listLt a.vars b.vars

@[reducible] def insertVar (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertVar x ys

@[reducible] def sortVars : List Nat → List Nat
  | [] => []
  | x :: xs => insertVar x (sortVars xs)

def Mono.mul (a b : Mono) : Mono := ⟨sortVars (a.vars ++ b.vars)⟩

theorem eval_appendVars (env : Nat → Rat) (xs ys : List Nat) :
    evalVars env (xs ++ ys) = evalVars env xs * evalVars env ys := by
  induction xs with
  | nil => simp [evalVars]
  | cons x xs ih => simp [evalVars, ih, Rat.mul_assoc]

theorem eval_insertVar (env : Nat → Rat) (x : Nat) (xs : List Nat) :
    evalVars env (insertVar x xs) = env x * evalVars env xs := by
  induction xs with
  | nil => simp [insertVar, evalVars]
  | cons y ys ih =>
    by_cases h : x ≤ y
    · simp [insertVar, h, evalVars]
    · simp only [insertVar, h, ite_false, evalVars]
      rw [ih]
      ac_rfl

theorem eval_sortVars (env : Nat → Rat) (xs : List Nat) :
    evalVars env (sortVars xs) = evalVars env xs := by
  induction xs with
  | nil => simp [sortVars, evalVars]
  | cons x xs ih =>
    simp only [sortVars]
    rw [eval_insertVar, ih]

theorem eval_mul (env : Nat → Rat) (a b : Mono) :
    Mono.eval env (a.mul b) = Mono.eval env a * Mono.eval env b := by
  cases a; cases b
  simp [Mono.mul, Mono.eval, eval_sortVars, eval_appendVars]

theorem eval_term_mul (env : Nat → Rat) (t u : Term) :
    Term.eval env ⟨t.coeff * u.coeff, t.mono.mul u.mono⟩ =
      Term.eval env t * Term.eval env u := by
  simp only [Term.eval, eval_mul, Rat.intCast_mul]
  ac_rfl

theorem eval_term_add (env : Nat → Rat) (c₁ c₂ : Int) (m : Mono) :
    Term.eval env ⟨c₁ + c₂, m⟩ =
      Term.eval env ⟨c₁, m⟩ + Term.eval env ⟨c₂, m⟩ := by
  simp only [Term.eval, Rat.intCast_add, Rat.add_mul]

/-! ## Insertion with merging -/

@[reducible] def insertTerm (t : Term) : Normal → Normal
  | [] => if t.coeff = 0 then [] else [t]
  | u :: us =>
      if h : t.mono.vars = u.mono.vars then
        let c := u.coeff + t.coeff
        if c = 0 then us else ⟨c, u.mono⟩ :: us
      else if t.mono.lt u.mono then
        if t.coeff = 0 then u :: us else t :: u :: us
      else
        u :: insertTerm t us

theorem eval_normal_append (env : Nat → Rat) (xs ys : Normal) :
    Normal.eval env (xs ++ ys) = Normal.eval env xs + Normal.eval env ys := by
  induction xs with
  | nil => simp [Normal.eval, Rat.zero_add]
  | cons x xs ih => simp [Normal.eval, ih, Rat.add_assoc]

theorem eval_insertTerm (env : Nat → Rat) (t : Term) (ts : Normal) :
    Normal.eval env (insertTerm t ts) = t.eval env + Normal.eval env ts := by
  induction ts with
  | nil =>
    by_cases h : t.coeff = 0
    · simp [insertTerm, h, Normal.eval, Term.eval, Rat.intCast_zero,
        Rat.zero_mul, Rat.zero_add]
    · simp [insertTerm, h, Normal.eval]
  | cons u us ih =>
    rcases u with ⟨uc, um⟩
    rcases t with ⟨tc, tm⟩
    by_cases hsame : tm.vars = um.vars
    · have hmono : tm = um := by
        cases tm; cases um
        simpa using hsame
      by_cases hc : uc + tc = 0
      · have hsum : Term.eval env ⟨uc, um⟩ + Term.eval env ⟨tc, um⟩ = 0 := by
          have h := eval_term_add env uc tc um
          rw [hc, Term.eval, Rat.intCast_zero, Rat.zero_mul] at h
          exact h.symm
        have ht : Term.eval env ⟨tc, tm⟩ = -Term.eval env ⟨uc, um⟩ := by
          rw [hmono]
          apply Rat.add_left_cancel (Term.eval env ⟨uc, um⟩)
          rw [hsum, Rat.add_neg_cancel]
        simp only [insertTerm, dif_pos hsame, hc, ite_true, ite_false,
          Normal.eval, ht]
        rcases us with _ | ⟨v, vs⟩
        · simp [Normal.eval]
          rw [Rat.add_zero, Rat.neg_add_cancel]
        · simp only [Normal.eval]
          rw [← Rat.add_assoc, Rat.neg_add_cancel, Rat.zero_add]
      · have hsum : Term.eval env ⟨uc, um⟩ + Term.eval env ⟨tc, um⟩ =
            Term.eval env ⟨uc + tc, um⟩ := by
          rw [eval_term_add]
        simp only [insertTerm, dif_pos hsame, hc, ite_true, ite_false,
          Normal.eval]
        rw [hmono, ← hsum]
        rcases us with _ | ⟨v, vs⟩
        · simp [Normal.eval, Rat.add_zero]
          ac_rfl
        · simp only [Normal.eval]
          ac_rfl
    · simp only [insertTerm, dif_neg hsame]
      cases hlt : tm.lt um with
      | true =>
        by_cases hc : tc = 0
        · simp [hlt, hc, Normal.eval, Term.eval, Rat.intCast_zero,
            Rat.zero_mul, Rat.zero_add]
        · simp [hlt, hc, Normal.eval]
      | false =>
        simp [hlt, Normal.eval]
        rw [ih]
        ac_rfl

theorem eval_foldr_add (env : Nat → Rat) (xs ys : Normal) :
    Normal.eval env (xs.foldr (fun t acc => insertTerm t acc) ys) =
      Normal.eval env xs + Normal.eval env ys := by
  induction xs with
  | nil => simp [Normal.eval, Rat.zero_add]
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [eval_insertTerm, ih, Normal.eval, Rat.add_assoc]

theorem eval_map_mul (env : Nat → Rat) (t : Term) (ys : Normal) :
    Normal.eval env (ys.map fun u => ⟨t.coeff * u.coeff, t.mono.mul u.mono⟩) =
      t.eval env * Normal.eval env ys := by
  induction ys with
  | nil => simp [Normal.eval, Term.eval]
  | cons u us ih =>
    simp only [List.map_cons, Normal.eval]
    rw [ih, eval_term_mul]
    rw [Rat.mul_add]

@[reducible] def addNormal (xs ys : Normal) : Normal :=
  xs.foldr (fun t acc => insertTerm t acc) ys

theorem eval_addNormal (env : Nat → Rat) (xs ys : Normal) :
    Normal.eval env (addNormal xs ys) = Normal.eval env xs + Normal.eval env ys := by
  simpa [addNormal] using eval_foldr_add env xs ys

@[reducible] def mulNormal (xs ys : Normal) : Normal :=
  xs.foldr
    (fun t acc =>
      addNormal (ys.map fun u => ⟨t.coeff * u.coeff, t.mono.mul u.mono⟩) acc)
    []

theorem eval_foldr_mul (env : Nat → Rat) (xs ys : Normal) :
    Normal.eval env
        (xs.foldr
          (fun t acc =>
            addNormal (ys.map fun u => ⟨t.coeff * u.coeff, t.mono.mul u.mono⟩) acc)
          []) =
      Normal.eval env xs * Normal.eval env ys := by
  induction xs with
  | nil => simp [Normal.eval, Rat.zero_mul]
  | cons x xs ih =>
    simp only [List.foldr_cons]
    rw [eval_addNormal, eval_map_mul, ih]
    simp only [Normal.eval]
    rw [Rat.add_mul]

theorem eval_mulNormal (env : Nat → Rat) (xs ys : Normal) :
    Normal.eval env (mulNormal xs ys) = Normal.eval env xs * Normal.eval env ys := by
  simpa [mulNormal] using eval_foldr_mul env xs ys

/-- Canonical normalization of a raw polynomial. -/
@[reducible] def normalize : Expr → Normal
  | .const c => if c = 0 then [] else [⟨c, ⟨[]⟩⟩]
  | .var i => [⟨1, ⟨[i]⟩⟩]
  | .add p q => addNormal (normalize p) (normalize q)
  | .sub p q =>
      addNormal (normalize p) ((normalize q).map fun t => ⟨-t.coeff, t.mono⟩)
  | .mul p q => mulNormal (normalize p) (normalize q)
  | .neg p => (normalize p).map fun t => ⟨-t.coeff, t.mono⟩

theorem eval_map_neg (env : Nat → Rat) (xs : Normal) :
    Normal.eval env (xs.map fun t => ⟨-t.coeff, t.mono⟩) = -Normal.eval env xs := by
  induction xs with
  | nil => simp [Normal.eval]
  | cons x xs ih =>
    simp only [List.map_cons, Normal.eval, ih, Term.eval, Rat.intCast_neg]
    rw [Rat.neg_mul, Rat.neg_add]

theorem eval_addNormal_neg (env : Nat → Rat) (p q : Normal) :
    Normal.eval env (addNormal p (q.map fun t => ⟨-t.coeff, t.mono⟩)) =
      Normal.eval env p - Normal.eval env q := by
  rw [eval_addNormal, eval_map_neg, Rat.sub_eq_add_neg]

theorem eval_normalize (env : Nat → Rat) (p : Expr) :
    Expr.eval env p = Normal.eval env (normalize p) := by
  induction p with
  | const c =>
    by_cases h : c = 0
    · simp [normalize, h, Expr.eval, Normal.eval, Term.eval, Rat.intCast_zero]
    · simp [normalize, h, Expr.eval, Normal.eval, Term.eval, Mono.eval,
        Rat.mul_one, Rat.add_zero]
  | var i =>
    simp [normalize, Expr.eval, Normal.eval, Term.eval, Mono.eval, evalVars,
      Rat.one_mul, Rat.mul_one, Rat.add_zero]
  | add p q ihp ihq =>
    simp only [Expr.eval, normalize]
    rw [ihp, ihq, eval_addNormal]
  | sub p q ihp ihq =>
    simp only [Expr.eval, normalize]
    rw [ihp, ihq, eval_addNormal_neg]
  | mul p q ihp ihq =>
    simp only [Expr.eval, normalize]
    rw [ihp, ihq, eval_mulNormal]
  | neg p ih =>
    simp only [Expr.eval, normalize]
    rw [ih, eval_map_neg]

end Poly
end Pontifex
