/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Word
public import Geb.Mathlib.Computability.BellantoniCook.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The initial functions and recursion schemes of Logs

The word functions of {cite}`Oitavem2010` Definition 3.1. Normal arguments are
arbitrary binary words. There is at most one safe argument. Neither the initial
functions nor concatenation recursion can read a safe argument. Safe recursion
passes its result to that position, and log-transition is the only scheme that
can use its value.

## Main definitions

* {lit}`Initial` and {lit}`Initial.eval` give the twelve initial function families.
* {lit}`concatRec` is safe concatenation recursion on notation.
* {lit}`logTransition` is safe log-transition, evaluated by its closed form.

## Main statements

* {lit}`logTransition_nil`, {lit}`logTransition_cons_zero`, and
  {lit}`logTransition_cons_succ` verify all three equations in Definition 3.1.
* {lit}`logTransition_truncate` is the transition case of Lemma 3.3.

## Implementation notes

Words are reversed relative to the paper, so string successor prepends and string
predecessor takes the tail. A transition's normal environment is ordered as its
iteration word, offset, and remaining parameters. Its child receives the updated
offset followed by the parameters. This permutes the paper's placement of the
offset after the parameters.

## References

* {cite}`Oitavem2010`, Definition 3.1 and Lemma 3.3.

## Tags

implicit complexity, logspace, safe recursion, function algebra
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Oitavem

open BellantoniCook (Sem)

/-- The initial function families of Definition 3.1, all with normal arguments only. -/
inductive Initial
  | zero (n : ℕ)
  | proj (n : ℕ) (i : Fin n)
  | succ (bit : Bool)
  | pred
  | iterPred
  | numericSucc
  | numericPred
  | numericSub
  | length
  | last
  | cond
  | product
  deriving DecidableEq, Repr

/-- The number of normal arguments of an initial function. -/
@[reducible] def Initial.arity : Initial → ℕ
  | .zero n | .proj n _ => n
  | .succ _ | .pred | .numericSucc | .numericPred | .length | .last => 1
  | .iterPred | .numericSub | .product => 2
  | .cond => 3

/-- The word function assigned to each initial symbol. -/
def Initial.eval : (p : Initial) → (Fin p.arity → List Bool) → List Bool
  | .zero _, _ => []
  | .proj _ i, x => x i
  | .succ b, x => b :: x 0
  | .pred, x => (x 0).tail
  | .iterPred, x => (x 1).drop (x 0).length
  | .numericSucc, x => Oitavem.numericSucc (x 0)
  | .numericPred, x => Oitavem.numericPred (x 0)
  | .numericSub, x => Oitavem.numericSub (x 0) (x 1)
  | .length, x => unrank (x 0).length
  | .last, x => [(x 0).headD false]
  | .cond, x => if (x 0).isEmpty then x 1 else x 2
  | .product, x => (List.replicate (x 1).length (x 0)).flatten

/-- Concatenation recursion adds exactly one output digit per input digit; the
step functions cannot inspect the accumulated output. -/
def concatRec {n : ℕ} (g : Sem (n, 0)) (h : Bool → Sem (n + 1, 0)) :
    List Bool → Sem (n, 0) :=
  List.rec g fun b v ih x y ↦ (h b (Fin.cons v x) Fin.elim0).headD false :: ih x y

/-- Log-transition transfers at most the iteration word's length from the safe
argument's numerical value to the normal offset, then applies its child. -/
def logTransition {n : ℕ} (h : Sem (n + 1, 0)) : Sem (n + 2, 1) :=
  fun x y ↦ h (Fin.cons (unrank (rank (x 1) + min (x 0).length (rank (y 0))))
    (Fin.tail (Fin.tail x))) Fin.elim0

/-- At the empty iteration word, the transition applies its child to the offset. -/
theorem logTransition_nil {n : ℕ} (h : Sem (n + 1, 0)) (z w : List Bool)
    (x : Fin n → List Bool) :
    logTransition h (Fin.cons [] (Fin.cons z x)) ![w] = h (Fin.cons z x) Fin.elim0 := by
  simp [logTransition]

/-- A zero safe argument leaves the offset unchanged at each transition. -/
theorem logTransition_cons_zero {n : ℕ} (h : Sem (n + 1, 0)) (b : Bool)
    (v z : List Bool) (x : Fin n → List Bool) :
    logTransition h (Fin.cons (b :: v) (Fin.cons z x)) ![[]] =
      logTransition h (Fin.cons v (Fin.cons z x)) ![[]] := by
  simp [logTransition]

/-- A positive safe argument advances the offset once and consumes one unit. -/
theorem logTransition_cons_succ {n : ℕ} (h : Sem (n + 1, 0)) (b : Bool)
    (v z w : List Bool) (x : Fin n → List Bool) :
    logTransition h (Fin.cons (b :: v) (Fin.cons z x)) ![numericSucc w] =
      logTransition h (Fin.cons v (Fin.cons (numericSucc z) x)) ![w] := by
  simp [logTransition, Nat.add_assoc, Nat.add_comm 1]

/-- A log-transition observes only a length-bounded numerical part of its safe input. -/
theorem logTransition_truncate {n : ℕ} (h : Sem (n + 1, 0))
    (x : Fin (n + 2) → List Bool) (w : List Bool) :
    logTransition h x ![w] =
      logTransition h x ![unrank (min (rank w) (x 0).length)] := by
  simp [logTransition, Nat.min_comm]

end Geb.Oitavem
