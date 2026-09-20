/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Basic
public import Geb.Mathlib.Data.PFunctor.Slice.Decidable
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Syntactic expressions of Oitavem's Logs

Definition 3.1 of {cite}`Oitavem2010` as a W-type of a polynomial functor in
the slice over pairs of normal and safe arities. An expression is admitted solely
by its constructor and child arities. No bound term, boundedness certificate, or
semantic side condition is part of the syntax.

## Main definitions

* {lit}`sig` is the slice polynomial signature.
* {lit}`Expr` is its W-type at a specified arity.
* {lit}`Expr.initial`, {lit}`Expr.comp`, {lit}`Expr.safeRec`, {lit}`Expr.concatRec`,
  and {lit}`Expr.logTransition` are the constructors of Definition 3.1.
* {lit}`Expr.eval` folds the syntax into word functions.

## Main statements

* {lit}`Expr.eval_node` gives the interpretation of any constructor.
* {lit}`Expr.eval_safeRec_nil` and {lit}`Expr.eval_safeRec_cons` give the safe
  recursion equations; the corresponding concatenation equations are also proved.

## References

* {cite}`Oitavem2010`, Definition 3.1.

## Tags

logspace, implicit complexity, slice polynomial functor, W-type
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Oitavem

open scoped FinEnum
open BellantoniCook (Sem transport)

/-- Constructor labels. The boolean of composition specifies whether its head
and result have the single safe argument. All substituted arguments are normal. -/
inductive Shape
  | initial (p : Initial)
  | comp (n m : ℕ) (safe : Bool)
  | safeRec (n : ℕ)
  | concatRec (n : ℕ)
  | logTransition (n : ℕ)
  deriving DecidableEq, Repr

/-- Children of a node: none for initials, a head and its normal arguments for
composition, a base and two steps for recursion, or one child for log-transition. -/
@[reducible] def Direction : Shape → Type
  | .initial _ => Fin 0
  | .comp _ m _ => Unit ⊕ Fin m
  | .safeRec _ | .concatRec _ => Unit ⊕ Bool
  | .logTransition _ => Unit

/-- The normal and safe arities required at a child position. -/
@[reducible] def childArity : (s : Shape) → Direction s → ℕ × ℕ
  | .initial _, d => d.elim0
  | .comp _ m safe, .inl () => (m, safe.toNat)
  | .comp n _ _, .inr _ => (n, 0)
  | .safeRec n, .inl () | .concatRec n, .inl () => (n, 0)
  | .safeRec n, .inr _ => (n + 1, 1)
  | .concatRec n, .inr _ => (n + 1, 0)
  | .logTransition n, () => (n + 1, 0)

/-- The arity produced by a node. -/
@[reducible] def resultArity : Shape → ℕ × ℕ
  | .initial p => (p.arity, 0)
  | .comp n _ safe => (n, safe.toNat)
  | .safeRec n | .concatRec n => (n + 1, 0)
  | .logTransition n => (n + 2, 1)

/-- The normal/safe arity-indexed polynomial signature of Logs. -/
def sig : SlicePFunctor (ℕ × ℕ) (ℕ × ℕ) where
  A := Shape
  B := Direction
  r x := childArity x.1 x.2
  q := resultArity

/-- The syntax has finitely many children at every node. -/
instance sigFinitary : sig.toPFunctor.Finitary
  | .initial _ => inferInstanceAs (FinEnum (Fin 0))
  | .comp _ m _ => inferInstanceAs (FinEnum (Unit ⊕ Fin m))
  | .safeRec _ | .concatRec _ =>
      letI : FinEnum Bool :=
        { card := 2
          equiv :=
            { toFun := fun b ↦ if b then 1 else 0
              invFun := fun i ↦ i = 1
              left_inv := fun b ↦ by cases b <;> rfl
              right_inv := fun i ↦ Fin.cases rfl (Fin.cases rfl fun j ↦ j.elim0) i }
          decEq := inferInstance }
      inferInstanceAs (FinEnum (Unit ⊕ Bool))
  | .logTransition _ => inferInstanceAs (FinEnum Unit)

/-- Arity-correct trees with a specified number of normal and safe arguments. -/
def Expr (n s : ℕ) : Type := {w : sig.W // sig.wIndex w = (n, s)}

/-- Check only the constructor arity equations throughout a raw tree. -/
def wellFormed (w : sig.toPFunctor.W) : Bool := decide (sig.WValid w)

/-- The executable syntax check accepts exactly the admissible trees. -/
@[simp] theorem wellFormed_eq_true (w : sig.toPFunctor.W) :
    wellFormed w = true ↔ sig.WValid w := by simp [wellFormed]

/-- Interpret one constructor using its already-interpreted children. -/
def evalNode : (s : Shape) → ((d : Direction s) → Sem (childArity s d)) → Sem (resultArity s)
  | .initial p, _ => fun x _ ↦ p.eval x
  | .comp _ _ _, c => fun x y ↦ c (.inl ()) (fun i ↦ c (.inr i) x Fin.elim0) y
  | .safeRec _, c => fun x y ↦
      BellantoniCook.evalRec (c (.inl ())) (c (.inr false)) (c (.inr true))
        (x 0) (Fin.tail x) y
  | .concatRec _, c => fun x y ↦
      Oitavem.concatRec (c (.inl ())) (fun b ↦ c (.inr b)) (x 0) (Fin.tail x) y
  | .logTransition _, c => Oitavem.logTransition (c ())

/-- The interpreting algebra in the slice over arities. -/
def evalStep : sig.toSliceDomPFunctor.Obj (Sigma.fst (β := Sem)) → Σ i, Sem i :=
  fun z ↦ ⟨resultArity z.1.1, evalNode z.1.1 fun d ↦
    transport (((sig.toSliceDomPFunctor.compatible_iff _ z.1.1 z.1.2).mp z.2) d)
      (z.1.2 d).2⟩

/-- The fold interpreting a syntactically admissible tree. -/
def interpret : sig.W → Σ i, Sem i :=
  SlicePFunctor.W.elim sig (Σ i, Sem i) (Sigma.fst (β := Sem)) evalStep rfl

/-- Interpretation preserves the arity of the syntax. -/
theorem fst_interpret (w : sig.W) : (interpret w).1 = sig.wIndex w :=
  congrFun (SlicePFunctor.W.comp_elim sig (Σ i, Sem i) (Sigma.fst (β := Sem)) evalStep rfl) w

namespace Expr

/-- Build an admissible node; its only obligations are the syntactic child arities. -/
def node (s : Shape) (c : (d : Direction s) → Expr (childArity s d).1 (childArity s d).2) :
    Expr (resultArity s).1 (resultArity s).2 :=
  ⟨⟨WType.mk s (fun d ↦ (c d).1.1), (sig.wValid_mk _ _).mpr
    ⟨fun d ↦ (c d).1.2, funext fun d ↦ (c d).2⟩⟩, rfl⟩

/-- An initial function, with no safe input. -/
def initial (p : Initial) : Expr p.arity 0 := node (.initial p) fun d ↦ d.elim0

/-- Normal composition substitutes only safe-free functions into normal slots. -/
def comp {n m : ℕ} {safe : Bool} (h : Expr m safe.toNat) (g : Fin m → Expr n 0) :
    Expr n safe.toNat :=
  node (.comp n m safe) fun d ↦ match d with
    | .inl () => h
    | .inr i => g i

/-- Safe recursion passes the previous result as the step's sole safe argument. -/
def safeRec {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 1) 1) : Expr (n + 1) 0 :=
  node (.safeRec n) fun d ↦ match d with
    | .inl () => g
    | .inr b => h b

/-- Concatenation recursion never passes its accumulated result to the step. -/
def concatRec {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 1) 0) : Expr (n + 1) 0 :=
  node (.concatRec n) fun d ↦ match d with
    | .inl () => g
    | .inr b => h b

/-- Transfer a length-bounded part of the safe input into the normal offset. -/
def logTransition {n : ℕ} (h : Expr (n + 1) 0) : Expr (n + 2) 1 :=
  node (.logTransition n) fun () ↦ h

/-- Evaluate an expression at its declared normal and safe arities. -/
def eval {n s : ℕ} (e : Expr n s) : Sem (n, s) :=
  transport ((fst_interpret e.1).trans e.2) (interpret e.1).2

/-- The fold commutes with the constructor. -/
theorem eval_node (s : Shape) (c : (d : Direction s) → Expr (childArity s d).1 (childArity s d).2) :
    (node s c).eval = evalNode s (fun d ↦ (c d).eval) := rfl

/-- Structural induction at declared arities, through the slice W-type recursor. -/
theorem induction {P : (i : ℕ × ℕ) → Expr i.1 i.2 → Prop}
    (step : ∀ s (c : (d : Direction s) → Expr (childArity s d).1 (childArity s d).2),
      (∀ d, P (childArity s d) (c d)) → P (resultArity s) (node s c))
    {n s : ℕ} (e : Expr n s) : P (n, s) e := by
  have go : ∀ w : sig.W, ∀ i (h : sig.wIndex w = i), P i ⟨w, h⟩ := by
    refine SlicePFunctor.W.induction fun x ih i hi ↦ ?_
    cases hi
    exact step x.1.1 (fun d ↦ ⟨x.1.2 d,
      ((sig.toSliceDomPFunctor.compatible_iff _ x.1.1 x.1.2).mp x.2) d⟩)
      (fun d ↦ ih d _ _)
  exact go e.1 (n, s) e.2

/-- Initial nodes interpret their initial function. -/
@[simp] theorem eval_initial (p : Initial) (x : Fin p.arity → List Bool) :
    (initial p).eval x Fin.elim0 = p.eval x := rfl

/-- Evaluation of normal composition. -/
theorem eval_comp {n m : ℕ} {safe : Bool} (h : Expr m safe.toNat) (g : Fin m → Expr n 0)
    (x : Fin n → List Bool) (y : Fin safe.toNat → List Bool) :
    (comp h g).eval x y = h.eval (fun i ↦ (g i).eval x Fin.elim0) y := rfl

/-- Safe recursion starts at its base. -/
theorem eval_safeRec_nil {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 1) 1)
    (x : Fin n → List Bool) :
    (safeRec g h).eval (Fin.cons [] x) Fin.elim0 = g.eval x Fin.elim0 := rfl

/-- Safe recursion passes the recursive result only in safe position. -/
theorem eval_safeRec_cons {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 1) 1)
    (b : Bool) (v : List Bool) (x : Fin n → List Bool) :
    (safeRec g h).eval (Fin.cons (b :: v) x) Fin.elim0 =
      (h b).eval (Fin.cons v x) ![(safeRec g h).eval (Fin.cons v x) Fin.elim0] := by
  cases b <;> rfl

/-- Concatenation recursion starts at its base. -/
theorem eval_concatRec_nil {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 1) 0)
    (x : Fin n → List Bool) :
    (concatRec g h).eval (Fin.cons [] x) Fin.elim0 = g.eval x Fin.elim0 := rfl

/-- Concatenation recursion produces one digit without inspecting the recursive result. -/
theorem eval_concatRec_cons {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 1) 0)
    (b : Bool) (v : List Bool) (x : Fin n → List Bool) :
    (concatRec g h).eval (Fin.cons (b :: v) x) Fin.elim0 =
      ((h b).eval (Fin.cons v x) Fin.elim0).headD false ::
        (concatRec g h).eval (Fin.cons v x) Fin.elim0 := rfl

/-- Log-transition uses its closed form, whose defining equations are proved in Basic. -/
theorem eval_logTransition {n : ℕ} (h : Expr (n + 1) 0) :
    (logTransition h).eval = Oitavem.logTransition h.eval := rfl

end Expr

end Geb.Oitavem
