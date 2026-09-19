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

end Expr

/-- Word length, using only zero, projection, numerical successor, composition,
safe recursion, and log-transition. -/
def lengthByRec : Expr 1 0 :=
  Expr.safeRec (Expr.initial (.zero 0)) fun _ ↦
    Expr.comp (safe := true) (Expr.logTransition (Expr.initial .numericSucc))
      ![Expr.initial (.proj 1 0), Expr.initial (.zero 1)]

/-- The recursive length example agrees with the length primitive on all words. -/
theorem eval_lengthByRec (w : List Bool) :
    lengthByRec.eval ![w] Fin.elim0 = unrank w.length := by
  apply List.rec (motive := fun w ↦ lengthByRec.eval ![w] Fin.elim0 = unrank w.length) ?_ ?_ w
  · rfl
  · intro b v ih
    change lengthByRec.eval (Fin.cons (b :: v) Fin.elim0) Fin.elim0 = _ at ⊢
    rw [lengthByRec, Expr.eval_safeRec_cons, Expr.eval_comp, Expr.eval_logTransition]
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
