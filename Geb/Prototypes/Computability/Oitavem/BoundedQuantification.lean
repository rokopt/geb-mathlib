/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Derived

set_option doc.verso true in
/-!
# Bounded universal quantification in Oitavem's algebra

A scan over the suffixes of an input word quantifies over its positions,
including both endpoints. The scan is an expression of the existing algebra:
bounded recursion carries a Boolean verdict whose enumeration index is at most
two. A constant two-bit bound therefore retains the complete verdict.

## Main definitions

* {lit}`truth` represents true by a singleton word and false by the empty word.
* {lit}`Expr.const`, {lit}`Expr.nonempty`, and {lit}`Expr.conjunction` provide
  constants and normalized Boolean operations.
* {lit}`Expr.allSuffixes` universally checks all suffixes with fixed normal parameters.

## Main statements

* {lit}`Expr.eval_allSuffixes` identifies the scan with a finite universal test.

## Tags

logspace, function algebra, bounded quantification, recognizer
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Oitavem

/-- The two word-valued verdicts used by recognizers. -/
def truth (b : Bool) : List Bool := if b then [true] else []

/-- The word-valued verdict is empty exactly on rejection. -/
theorem isEmpty_truth (b : Bool) : (truth b).isEmpty = !b := by cases b <;> rfl

/-- Nonemptiness of a normalized verdict is Boolean truth. -/
theorem truth_ne_nil (b : Bool) : truth b ≠ [] ↔ b = true := by cases b <;> simp [truth]

/-- A two-bit bound retains either verdict in bounded recursion. -/
theorem cap_truth (b : Bool) : unrank (min (rank (truth b)) 2) = truth b := by
  cases b <;> rfl

namespace Expr

/-- A constant word at any normal arity. -/
def const (n : ℕ) : List Bool → Expr n 0 :=
  List.rec (initial (.zero n)) fun b _ e ↦ comp (safe := false) (initial (.succ b)) fun _ ↦ e

/-- Constant expressions return their word. -/
theorem eval_const (n : ℕ) (w : List Bool) (x : Fin n → List Bool) :
    (const n w).eval x Fin.elim0 = w :=
  List.rec rfl (fun _ _ ih ↦ congrArg (List.cons _) ih) w

/-- Evaluating a vector of expressions commutes with adjoining its first component. -/
theorem eval_cons {n m : ℕ} (e : Expr n 0) (es : Fin m → Expr n 0)
    (x : Fin n → List Bool) :
    (fun i ↦ ((Fin.cons e es : Fin (m + 1) → Expr n 0) i).eval x Fin.elim0) =
      Fin.cons (e.eval x Fin.elim0) (fun i ↦ (es i).eval x Fin.elim0) :=
  Fin.comp_cons (fun e : Expr n 0 ↦ e.eval x Fin.elim0) e es

/-- Normalize nonemptiness to a Boolean verdict. -/
def nonempty {n : ℕ} (e : Expr n 0) : Expr n 0 :=
  comp (safe := false) (initial .cond) ![e, const n [], const n [true]]

/-- Normalization accepts exactly nonempty outputs. -/
theorem eval_nonempty {n : ℕ} (e : Expr n 0) (x : Fin n → List Bool) :
    e.nonempty.eval x Fin.elim0 = truth (!(e.eval x Fin.elim0).isEmpty) := by
  simp only [nonempty, eval_comp, eval_initial, Initial.eval, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, eval_const]
  cases (e.eval x Fin.elim0).isEmpty <;> rfl

/-- Negate nonemptiness, returning a normalized verdict. -/
def negation {n : ℕ} (e : Expr n 0) : Expr n 0 :=
  comp (safe := false) (initial .cond) ![e, const n [true], const n []]

/-- Negation accepts exactly empty outputs. -/
theorem eval_negation {n : ℕ} (e : Expr n 0) (x : Fin n → List Bool) :
    e.negation.eval x Fin.elim0 = truth (e.eval x Fin.elim0).isEmpty := by
  change (if (e.eval x Fin.elim0).isEmpty then [true] else []) = _
  rfl

/-- Conjoin the nonemptiness of two outputs, returning a normalized verdict. -/
def conjunction {n : ℕ} (e f : Expr n 0) : Expr n 0 :=
  comp (safe := false) (initial .cond) ![e, const n [], f.nonempty]

/-- Conjunction agrees with Boolean conjunction of the nonemptiness tests. -/
theorem eval_conjunction {n : ℕ} (e f : Expr n 0) (x : Fin n → List Bool) :
    (conjunction e f).eval x Fin.elim0 =
      truth (!(e.eval x Fin.elim0).isEmpty && !(f.eval x Fin.elim0).isEmpty) := by
  change (if (e.eval x Fin.elim0).isEmpty then [] else f.nonempty.eval x Fin.elim0) = _
  rw [eval_nonempty]
  cases (e.eval x Fin.elim0).isEmpty <;> rfl

/-- Check every suffix, retaining only the accumulated Boolean verdict. -/
def allSuffixes {n : ℕ} (p : Expr (n + 1) 0) : Expr (n + 1) 0 :=
  boundedRec
    (comp (safe := false) p.nonempty
      (Fin.cons (const n []) (fun j ↦ initial (.proj n j))))
    (fun b ↦ conjunction (initial (.proj (n + 2) 0))
      (comp (safe := false) p
        (Fin.cons (comp (safe := false) (initial (.succ b))
          (fun _ ↦ initial (.proj (n + 2) 1)))
          (fun j ↦ initial (.proj (n + 2) j.succ.succ)))))
    (const (n + 1) [false, false])

/-- The expression performs finite universal quantification over input positions. -/
theorem eval_allSuffixes {n : ℕ} (p : Expr (n + 1) 0) (w : List Bool)
    (x : Fin n → List Bool) :
    p.allSuffixes.eval (Fin.cons w x) Fin.elim0 =
      truth (w.tails.all fun v ↦ !(p.eval (Fin.cons v x) Fin.elim0).isEmpty) := by
  apply List.rec (motive := fun w ↦ p.allSuffixes.eval (Fin.cons w x) Fin.elim0 =
    truth (w.tails.all fun v ↦ !(p.eval (Fin.cons v x) Fin.elim0).isEmpty)) ?_ ?_ w
  · simp only [allSuffixes, eval_boundedRec_nil, eval_comp, eval_nonempty,
      eval_cons, eval_initial, Initial.eval, eval_const]
    change truth _ = truth (_ && true)
    rw [Bool.and_true]
  · intro b v ih
    rw [allSuffixes, eval_boundedRec_cons]
    change (conjunction _ _).eval
      (Fin.cons (unrank (min (rank (p.allSuffixes.eval (Fin.cons v x) Fin.elim0)) 2))
        (Fin.cons v x)) Fin.elim0 = _
    rw [ih, cap_truth, eval_conjunction]
    simp only [eval_initial, Initial.eval, Fin.cons_zero, eval_comp, eval_cons, Fin.cons_succ,
      isEmpty_truth, Bool.not_not]
    change truth (_ && _) = truth (_ && _)
    exact congrArg truth (Bool.and_comm _ _)

end Expr

end Geb.Oitavem
