/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Syntax
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The safe-input truncation lemma

Lemma 3.3 of {cite}`Oitavem2010`: a safe argument is used only through a
numerical truncation at the length of a word computed from the normal arguments.
The bound is itself an expression of Logs with no safe arguments. The theorem
here takes the paper's auxiliary function to be the original function itself.

## Main definitions

* {lit}`Expr.truncationBound` extracts a normal-only bound expression from the syntax.

## Main statements

* {lit}`Expr.truncates_truncationBound` verifies the extracted bound.
* {lit}`Expr.exists_truncation` states Lemma 3.3 for every expression.

## References

* {cite}`Oitavem2010`, Lemma 3.3.

## Tags

logspace, safe recursion, truncation, implicit complexity
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Oitavem

open BellantoniCook (Sem)

/-- The bound tree at a node, using the children's source trees and bound trees. -/
def truncationNode : (a : Shape) →
    (Direction a → sig.toPFunctor.W × sig.toPFunctor.W) → sig.toPFunctor.W
  | .comp n m _, c => WType.mk (.comp n m false) fun d ↦ match d with
      | .inl () => (c (.inl ())).2
      | .inr i => (c (.inr i)).1
  | .logTransition n, _ => WType.mk (.initial (.proj (n + 2) 0)) Fin.elim0
  | a, _ => WType.mk (.initial (.zero (resultArity a).1)) Fin.elim0

/-- Reconstruct the source and extract its truncation bound in one polynomial-functor fold. -/
def truncationData : sig.toPFunctor.W → sig.toPFunctor.W × sig.toPFunctor.W :=
  WType.elim _ fun x ↦ ⟨WType.mk x.1 (fun d ↦ (x.2 d).1), truncationNode x.1 x.2⟩

/-- The source component of the fold is the original tree. -/
theorem truncationData_fst (w : sig.toPFunctor.W) : (truncationData w).1 = w := by
  apply WType.rec (motive := fun w ↦ (truncationData w).1 = w) ?_ w
  intro a c ih
  change WType.mk a (fun d ↦ (truncationData (c d)).1) = WType.mk a c
  exact congrArg (WType.mk a) (funext ih)

/-- The extracted tree has the source's normal arity and no safe argument. -/
theorem truncationData_index (w : sig.toPFunctor.W) :
    sig.wIndexRoot (truncationData w).2 = ((sig.wIndexRoot w).1, 0) := by
  cases w with
  | mk a c => cases a <;> rfl

/-- Bound extraction preserves syntactic admissibility. -/
theorem Expr.truncationData_valid {n s : ℕ} (e : Expr n s) :
    sig.WValid (truncationData e.1.1).2 := by
  refine Expr.induction (P := fun _ e ↦ sig.WValid (truncationData e.1.1).2) ?_ e
  intro a c ih
  have hinit (p : Initial) : sig.WValid (WType.mk (.initial p) Fin.elim0) :=
    (sig.wValid_mk _ _).mpr ⟨fun d ↦ d.elim0, funext fun d ↦ d.elim0⟩
  cases a with
  | initial p => exact hinit (.zero p.arity)
  | safeRec n => exact hinit (.zero (n + 1))
  | concatRec n => exact hinit (.zero (n + 1))
  | logTransition n => exact hinit (.proj (n + 2) 0)
  | comp n m safe =>
    refine (sig.wValid_mk (.comp n m false) _).mpr ⟨?_, ?_⟩
    · intro d
      cases d with
      | inl u => cases u; exact ih (.inl ())
      | inr i =>
        change sig.WValid (truncationData (c (.inr i)).1.1).1
        rw [truncationData_fst]
        exact (c (.inr i)).1.2
    · funext d
      cases d with
      | inl u =>
        cases u
        change sig.wIndexRoot (truncationData (c (.inl ())).1.1).2 = (m, 0)
        rw [truncationData_index]
        exact congrArg (fun i : ℕ × ℕ ↦ (i.1, 0)) (c (.inl ())).2
      | inr i =>
        change sig.wIndexRoot (truncationData (c (.inr i)).1.1).1 = (n, 0)
        rw [truncationData_fst]
        exact (c (.inr i)).2

/-- Compute a normal-only expression bounding the observation of the safe input. -/
def Expr.truncationBound {n s : ℕ} (e : Expr n s) : Expr n 0 :=
  ⟨⟨(truncationData e.1.1).2, e.truncationData_valid⟩,
    (truncationData_index e.1.1).trans (congrArg (fun i : ℕ × ℕ ↦ (i.1, 0)) e.2)⟩

/-- At composition, substitute the original normal arguments into the head's bound. -/
theorem Expr.truncationBound_node_comp {n m : ℕ} {safe : Bool}
    (c : (d : Direction (.comp n m safe)) →
      Expr (childArity (.comp n m safe) d).1 (childArity (.comp n m safe) d).2) :
    (Expr.node (.comp n m safe) c).truncationBound =
      Expr.comp (safe := false) (c (.inl ())).truncationBound (fun j ↦ c (.inr j)) := by
  apply Subtype.ext
  apply Subtype.ext
  change (WType.mk (Shape.comp n m false) _ : sig.toPFunctor.W) = WType.mk _ _
  congr 1
  funext d
  cases d with
  | inl u => cases u; rfl
  | inr i => exact truncationData_fst _

/-- A function observes each safe argument only up to the bound's numerical index. -/
def Truncates {n s : ℕ} (f : Sem (n, s)) (bound : (Fin n → List Bool) → ℕ) : Prop :=
  ∀ x y, f x y = f x (fun j ↦ unrank (min (rank (y j)) (bound x)))

/-- With no safe positions, truncation changes no argument. -/
theorem truncates_no_safe {n : ℕ} (f : Sem (n, 0))
    (bound : (Fin n → List Bool) → ℕ) : Truncates f bound := by
  intro x y
  congr 1
  funext i
  exact i.elim0

/-- The automatically extracted expression bounds every observation of a safe input. -/
theorem Expr.truncates_truncationBound {n s : ℕ} (e : Expr n s) :
    Truncates e.eval (fun x ↦ (e.truncationBound.eval x Fin.elim0).length) := by
  refine Expr.induction (P := fun _ e ↦
    Truncates e.eval (fun x ↦ (e.truncationBound.eval x Fin.elim0).length)) ?_ e
  intro a c ih
  cases a with
  | initial _ => exact truncates_no_safe _ _
  | safeRec _ => exact truncates_no_safe _ _
  | concatRec _ => exact truncates_no_safe _ _
  | logTransition n =>
    intro x y
    change Oitavem.logTransition (c ()).eval x y =
      Oitavem.logTransition (c ()).eval x (fun j ↦ unrank (min (rank (y j)) (x 0).length))
    simp only [Oitavem.logTransition, rank_unrank]
    congr 3
    omega
  | comp n m safe =>
    rw [Expr.truncationBound_node_comp]
    intro x y
    exact ih (.inl ()) (fun i ↦ (c (.inr i)).eval x Fin.elim0) y

/-- Every expression has a safe-free syntactic bound as in Lemma 3.3. No
boundedness premise is imposed on the expression. -/
theorem Expr.exists_truncation {n s : ℕ} (e : Expr n s) :
    ∃ b : Expr n 0, Truncates e.eval (fun x ↦ (b.eval x Fin.elim0).length) :=
  ⟨e.truncationBound, e.truncates_truncationBound⟩

end Geb.Oitavem
