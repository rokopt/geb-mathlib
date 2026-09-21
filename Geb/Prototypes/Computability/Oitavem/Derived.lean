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
# Derived bounded recursion and word functions

The bounded-recursion construction in the proof of {cite}`Oitavem2010`
Lemma 3.2 uses safe recursion, normal composition, and log-transition. It is
derived here from exactly those constructors. The bound is an ordinary
expression producing a word; no proof about that word's length is required.

## Main definitions

* {lit}`Expr.boundedRec` is the recursion scheme of Definition 2.1, derived in Logs.
* {lit}`Expr.transitionOffset` expresses the log-transition offset using normal constructors.
* {lit}`Expr.logTransitionNormal` treats the safe input of a log-transition as normal.
* {lit}`lengthByRec` computes word length using safe recursion and log-transition.
* {lit}`squareWord` repeats its input as many times as the input's length.

## Main statements

* {lit}`Expr.eval_boundedRec_nil` and {lit}`Expr.eval_boundedRec_cons` prove
  the bounded-recursion equations.
* {lit}`eval_lengthByRec` verifies the recursive length example.
* {lit}`length_squareWord` exhibits quadratic output length.

## References

* {cite}`Oitavem2010`, Definition 2.1 and Lemma 3.2.

## Tags

logspace, bounded recursion, safe recursion, function algebra
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Oitavem

namespace Expr

/-- The bounded-recursion scheme of Definition 2.1 expressed using the syntactic
constructors of Logs. A step receives the capped recursive value first, then
the recursion prefix and the remaining parameters. -/
def boundedRec {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 2) 0)
    (bound : Expr (n + 1) 0) : Expr (n + 1) 0 :=
  safeRec g fun b ↦ comp (safe := true) (logTransition (h b))
    (Fin.cons bound (Fin.cons (initial (.zero (n + 1)))
      (fun j ↦ initial (.proj (n + 1) j))) : Fin (n + 3) → Expr (n + 1) 0)

/-- Derived bounded recursion starts at its base. -/
theorem eval_boundedRec_nil {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 2) 0)
    (bound : Expr (n + 1) 0) (x : Fin n → List Bool) :
    (boundedRec g h bound).eval (Fin.cons [] x) Fin.elim0 = g.eval x Fin.elim0 := rfl

/-- The recursion argument is capped at the numerical length of the bound word,
exactly as in Definition 2.1. -/
theorem eval_boundedRec_cons {n : ℕ} (g : Expr n 0) (h : Bool → Expr (n + 2) 0)
    (bound : Expr (n + 1) 0) (bit : Bool) (v : List Bool) (x : Fin n → List Bool) :
    (boundedRec g h bound).eval (Fin.cons (bit :: v) x) Fin.elim0 =
      (h bit).eval (Fin.cons
        (unrank (min
          (rank ((boundedRec g h bound).eval (Fin.cons v x) Fin.elim0))
          (bound.eval (Fin.cons v x) Fin.elim0).length)) (Fin.cons v x)) Fin.elim0 := by
  rw [boundedRec, eval_safeRec_cons, eval_comp, eval_logTransition]
  simp only [Oitavem.logTransition, Fin.cons_zero, Fin.cons_one, eval_initial,
    Initial.eval, rank_nil, Nat.zero_add, Matrix.cons_val_zero, Nat.min_comm]
  congr 2

/-- The log-transition offset, with normal arguments for the iteration word,
offset, and safe value. Subtraction from a sufficiently large virtual word
implements addition without storing the offset's numerical rank. -/
def transitionOffset : Expr 3 0 :=
  let arg (i : Fin 3) := initial (.proj 3 i)
  let len := comp (safe := false) (initial .length) ![arg 0]
  let cap := comp (safe := false) (initial .numericSub)
    ![comp (safe := false) (initial .numericSub) ![len, arg 2], arg 2]
  let upper := comp (safe := false) (initial .product)
    ![comp (safe := false) (initial (.succ false)) ![arg 1],
      comp (safe := false) (initial (.succ false)) ![arg 0]]
  comp (safe := false) (initial .numericSub)
    ![comp (safe := false) (initial .numericSub)
        ![cap, comp (safe := false) (initial .numericSub) ![arg 1, upper]],
      upper]

/-- The derived arithmetic expression has exactly the log-transition offset. -/
theorem eval_transitionOffset (w z y : List Bool) :
    transitionOffset.eval ![w, z, y] Fin.elim0 =
      unrank (rank z + min w.length (rank y)) := by
  have hupper (m : ℕ) :
      rank z + m ≤ rank ((List.replicate (m + 1) (false :: z)).flatten) := by
    refine Nat.rec ?_ (fun m ih ↦ ?_) m
    · simp [rank_cons]
      omega
    · rw [List.replicate_succ, List.flatten_cons]
      have h := length_add_rank_le_rank_append (false :: z)
        ((List.replicate (m + 1) (false :: z)).flatten)
      simp only [List.length_cons] at h
      omega
  simp only [transitionOffset, eval_comp, eval_initial, Initial.eval,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, numericSub,
    rank_unrank, List.length_cons]
  change unrank (rank ((List.replicate (w.length + 1) (false :: z)).flatten) -
    (rank ((List.replicate (w.length + 1) (false :: z)).flatten) - rank z -
      (rank y - (rank y - w.length)))) = _
  congr 1
  have h := hupper w.length
  omega

/-- A log-transition with its safe input supplied as the first normal input.
The remaining inputs retain the original order. -/
def logTransitionNormal {n : ℕ} (h : Expr (n + 1) 0) : Expr (n + 3) 0 :=
  comp (safe := false) h (Fin.cons
    (comp (safe := false) transitionOffset
      ![initial (.proj (n + 3) 1), initial (.proj (n + 3) 2), initial (.proj (n + 3) 0)])
    (fun i ↦ initial (.proj (n + 3) i.succ.succ.succ)))

/-- Moving the safe input into the normal environment preserves log-transition. -/
theorem eval_logTransitionNormal {n : ℕ} (h : Expr (n + 1) 0)
    (x : Fin (n + 2) → List Bool) (y : List Bool) :
    (logTransitionNormal h).eval (Fin.cons y x) Fin.elim0 =
      Oitavem.logTransition h.eval x ![y] := by
  simp only [logTransitionNormal, eval_comp, Oitavem.logTransition,
    Matrix.cons_val_zero]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [Fin.cons_zero, eval_comp]
    have hx :
        (fun i : Fin 3 ↦
          (![initial (.proj (n + 3) 1), initial (.proj (n + 3) 2),
            initial (.proj (n + 3) 0)] i).eval (Fin.cons y x) Fin.elim0) =
          ![x 0, x 1, y] := by
      funext i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j ↦ j.elim0))) i <;> rfl
    rw [hx]
    exact eval_transitionOffset (x 0) (x 1) y
  · rfl

end Expr

/-- The recursive length step increments the safe value, capped by the prefix length. -/
def lengthByRecStep : Expr 1 1 :=
  Expr.comp (safe := true) (Expr.logTransition (Expr.initial .numericSucc))
    ![Expr.initial (.proj 1 0), Expr.initial (.zero 1)]

/-- The length step uses the smaller of the prefix length and the previous value. -/
theorem eval_lengthByRecStep (w v : List Bool) :
    lengthByRecStep.eval ![w] ![v] = unrank (min w.length (rank v) + 1) := by
  rw [lengthByRecStep, Expr.eval_comp, Expr.eval_logTransition]
  change numericSucc (unrank (0 + min w.length (rank v))) = _
  simp [numericSucc]

/-- Word length, using only zero, projection, numerical successor, composition,
safe recursion, and log-transition. -/
def lengthByRec : Expr 1 0 :=
  Expr.safeRec (Expr.initial (.zero 0)) fun _ ↦ lengthByRecStep

/-- The recursive length example agrees with the length primitive on all words. -/
theorem eval_lengthByRec (w : List Bool) :
    lengthByRec.eval ![w] Fin.elim0 = unrank w.length := by
  apply List.rec (motive := fun w ↦ lengthByRec.eval ![w] Fin.elim0 = unrank w.length) ?_ ?_ w
  · rfl
  · intro b v ih
    change lengthByRec.eval (Fin.cons (b :: v) Fin.elim0) Fin.elim0 = _ at ⊢
    rw [lengthByRec, Expr.eval_safeRec_cons, lengthByRecStep,
      Expr.eval_comp, Expr.eval_logTransition]
    change numericSucc (unrank (0 + min v.length
      (rank (lengthByRec.eval (Fin.cons v Fin.elim0) Fin.elim0)))) = unrank (v.length + 1)
    have ih' : lengthByRec.eval (Fin.cons v Fin.elim0) Fin.elim0 = unrank v.length := ih
    rw [ih', rank_unrank, Nat.min_self, Nat.zero_add]
    simp [numericSucc]

/-- Repeat the input word once for each of its digits. -/
def squareWord : Expr 1 0 :=
  Expr.comp (safe := false) (Expr.initial .product) fun _ ↦ Expr.initial (.proj 1 0)

/-- The long-output example has exactly quadratic output length. -/
theorem length_squareWord (w : List Bool) :
    (squareWord.eval ![w] Fin.elim0).length = w.length * w.length := by
  simp [squareWord, Expr.eval_comp, Expr.eval_initial, Initial.eval, List.length_flatten]

end Geb.Oitavem
