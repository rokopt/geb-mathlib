/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Syntax
public import Geb.Prototypes.Computability.SizeBounded.Cost
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Polynomial output length in Logs

Every expression of {cite}`Oitavem2010` Definition 3.1 has a polynomial
output-length bound depending only on the lengths of its normal arguments. Safe
arguments may have arbitrary length. The bound is computed from the syntax;
it is not an admissibility condition. A safe-recursion step cannot increase this
bound through the recursive value, because that value is passed in safe position.

## Main definitions

* {lit}`lengthPoly` computes a length bound from a raw syntax tree.
* {lit}`LengthBound` states a bound independent of all safe arguments.

## Main statements

* {lit}`lengthPoly_mono` and {lit}`lengthPoly_isPolyBounded` give the bound's properties.
* {lit}`Expr.length_le` bounds the denotation of every admissible tree.

## References

* {cite}`Oitavem2010`, Definition 3.1 and the truncation argument in Theorem 3.4.

## Tags

logspace, safe recursion, polynomial length, implicit complexity
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Oitavem

open BellantoniCook (Sem)
open Geb.SizeBounded (IsPolyBounded finMax finMax_le le_finMax isPolyBounded_id
  isPolyBounded_succ isPolyBounded_add isPolyBounded_mul isPolyBounded_max
  isPolyBounded_finMax isPolyBounded_linear)

/-- Composition preserves polynomial boundedness. -/
theorem isPolyBounded_comp {p q : ℕ → ℕ} (hp : IsPolyBounded p) (hq : IsPolyBounded q) :
    IsPolyBounded (p ∘ q) := by
  obtain ⟨a, b, hp⟩ := hp
  obtain ⟨c, d, hq⟩ := hq
  refine ⟨a * (c + 1) ^ b, d * b, fun m ↦ ?_⟩
  have hpow : 1 ≤ (m + 1) ^ d := Nat.one_le_pow d (m + 1) (by omega)
  have hq' : q m + 1 ≤ (c + 1) * (m + 1) ^ d := by
    have := hq m
    rw [Nat.add_mul, Nat.one_mul]
    omega
  calc
    p (q m) ≤ a * (q m + 1) ^ b := hp (q m)
    _ ≤ a * ((c + 1) * (m + 1) ^ d) ^ b :=
      Nat.mul_le_mul_left a (Nat.pow_le_pow_left hq' b)
    _ = (a * (c + 1) ^ b) * (m + 1) ^ (d * b) := by
      rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]

/-- The polynomial bound at one node, from its children's bounds. -/
def lengthPolyNode : (s : Shape) → (Direction s → ℕ → ℕ) → ℕ → ℕ
  | .initial _, _, m => (m + 1) * (m + 1)
  | .comp _ k _, p, m => p (.inl ()) (finMax k fun j ↦ p (.inr j) m)
  | .safeRec _, p, m => max (p (.inl ()) m) (max (p (.inr false) m) (p (.inr true) m))
  | .concatRec _, p, m => p (.inl ()) m + m
  | .logTransition _, p, m => p () (2 * m)

/-- A syntax-derived bound independent of the safe argument. -/
def lengthPoly : sig.toPFunctor.W → ℕ → ℕ :=
  WType.elim (ℕ → ℕ) fun x ↦ lengthPolyNode x.1 x.2

/-- Each node preserves monotonicity of the inferred bound. -/
theorem lengthPolyNode_mono (s : Shape) (p : Direction s → ℕ → ℕ)
    (hp : ∀ d, Monotone (p d)) : Monotone (lengthPolyNode s p) := by
  intro m n h
  cases s with
  | initial _ => exact Nat.mul_le_mul (by omega) (by omega)
  | comp _ k _ =>
    exact hp (.inl ()) (finMax_le k _ _ fun j ↦
      (hp (.inr j) h).trans (le_finMax k (fun j ↦ p (.inr j) n) j))
  | safeRec _ =>
    have h₀ := hp (.inl ()) h
    have hf := hp (.inr false) h
    have ht := hp (.inr true) h
    change max _ (max _ _) ≤ max _ (max _ _)
    omega
  | concatRec _ => exact Nat.add_le_add (hp (.inl ()) h) h
  | logTransition _ => exact hp () (Nat.mul_le_mul_left 2 h)

/-- Inferred bounds are monotone. -/
theorem lengthPoly_mono (w : sig.toPFunctor.W) : Monotone (lengthPoly w) :=
  WType.rec (motive := fun w ↦ Monotone (lengthPoly w))
    (fun s c ih ↦ lengthPolyNode_mono s (fun d ↦ lengthPoly (c d)) ih) w

/-- Each node preserves polynomial boundedness. -/
theorem lengthPolyNode_isPolyBounded (s : Shape) (p : Direction s → ℕ → ℕ)
    (hp : ∀ d, IsPolyBounded (p d)) : IsPolyBounded (lengthPolyNode s p) := by
  cases s with
  | initial _ => exact isPolyBounded_mul isPolyBounded_succ isPolyBounded_succ
  | comp _ k _ =>
    exact isPolyBounded_comp (hp (.inl ())) (isPolyBounded_finMax k _ fun j ↦ hp (.inr j))
  | safeRec _ =>
    exact isPolyBounded_max (hp (.inl ())) (isPolyBounded_max (hp (.inr false)) (hp (.inr true)))
  | concatRec _ => exact isPolyBounded_add (hp (.inl ())) isPolyBounded_id
  | logTransition _ =>
    exact isPolyBounded_comp (hp ()) (isPolyBounded_linear 2 0)

/-- Inferred bounds are bounded by polynomials with natural coefficients. -/
theorem lengthPoly_isPolyBounded (w : sig.toPFunctor.W) : IsPolyBounded (lengthPoly w) :=
  WType.rec (motive := fun w ↦ IsPolyBounded (lengthPoly w))
    (fun s c ih ↦ lengthPolyNode_isPolyBounded s (fun d ↦ lengthPoly (c d)) ih) w

/-- Output length bounded in the normal lengths alone, uniformly in every safe argument. -/
def LengthBound {i : ℕ × ℕ} (p : ℕ → ℕ) (f : Sem i) : Prop :=
  ∀ x y m, (∀ j, (x j).length ≤ m) → (f x y).length ≤ p m

/-- Every initial function has a quadratic bound in its normal arguments' lengths. -/
theorem Initial.length_le (p : Initial) (x : Fin p.arity → List Bool) (m : ℕ)
    (hx : ∀ j, (x j).length ≤ m) : (p.eval x).length ≤ (m + 1) * (m + 1) := by
  have hm : m + 1 ≤ (m + 1) * (m + 1) := Nat.le_mul_of_pos_left _ (by omega)
  cases p with
  | zero n => exact Nat.zero_le _
  | proj n i => exact (hx i).trans (by omega)
  | succ b => exact (Nat.add_le_add_right (hx 0) 1).trans hm
  | pred =>
    simp only [Initial.eval, List.length_tail]
    have := hx 0
    omega
  | iterPred =>
    simp only [Initial.eval, List.length_drop]
    have := hx 1
    omega
  | numericSucc =>
    exact (length_unrank_add (x 0) 1).trans ((Nat.add_le_add_right (hx 0) 1).trans hm)
  | numericPred => exact (length_numericPred_le (x 0)).trans ((hx 0).trans (by omega))
  | numericSub => exact (length_numericSub_le (x 0) (x 1)).trans ((hx 1).trans (by omega))
  | length => exact (length_unrank_le_self _).trans ((hx 0).trans (by omega))
  | last => exact (show 1 ≤ m + 1 by omega).trans hm
  | cond =>
    change (if (x 0).isEmpty then x 1 else x 2).length ≤ _
    split <;> exact (hx _).trans (by omega)
  | product =>
    simp only [Initial.eval, List.length_flatten, List.map_replicate, List.sum_replicate]
    exact Nat.mul_le_mul (by have := hx 1; omega) (by have := hx 0; omega)

/-- Concatenation recursion adds the input length to the base output length. -/
theorem length_concatRec {n : ℕ} (g : Sem (n, 0)) (h : Bool → Sem (n + 1, 0))
    (w : List Bool) (x : Fin n → List Bool) (y : Fin 0 → List Bool) :
    (concatRec g h w x y).length = (g x y).length + w.length := by
  apply List.rec (motive := fun w ↦
    (concatRec g h w x y).length = (g x y).length + w.length) ?_ ?_ w
  · rfl
  · intro b v ih
    change (concatRec g h v x y).length + 1 = (g x y).length + (v.length + 1)
    omega

/-- A node satisfies its inferred length bound when its children satisfy theirs. -/
theorem lengthBound_evalNode (a : Shape) (c : (d : Direction a) → Sem (childArity a d))
    (p : Direction a → ℕ → ℕ) (hp : ∀ d, LengthBound (p d) (c d)) :
    LengthBound (lengthPolyNode a p) (evalNode a c) := by
  intro x y m hx
  cases a with
  | initial q => exact q.length_le x m hx
  | comp _ k _ =>
    exact hp (.inl ()) _ y _ fun j ↦
      (hp (.inr j) x Fin.elim0 m hx).trans (le_finMax k (fun i ↦ p (.inr i) m) j)
  | concatRec n =>
    change (concatRec _ _ (x 0) (Fin.tail x) y).length ≤ _
    rw [length_concatRec]
    exact Nat.add_le_add (hp (.inl ()) (Fin.tail x) y m fun j ↦ hx j.succ) (hx 0)
  | safeRec n =>
    change (BellantoniCook.evalRec _ _ _ (x 0) (Fin.tail x) y).length ≤ _
    cases hw : x 0 with
    | nil =>
      exact (hp (.inl ()) (Fin.tail x) y m fun j ↦ hx j.succ).trans (Nat.le_max_left _ _)
    | cons b v =>
      have hv : v.length ≤ m := by have := hx 0; rw [hw, List.length_cons] at this; omega
      have henv : ∀ j, (Fin.cons v (Fin.tail x) j).length ≤ m :=
        Fin.cases hv fun j ↦ hx j.succ
      cases b
      · exact (hp (.inr false) _ _ m henv).trans
          ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
      · exact (hp (.inr true) _ _ m henv).trans
          ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  | logTransition n =>
    apply hp () _ Fin.elim0 (2 * m)
    refine Fin.cases ?_ (fun j ↦ (hx j.succ.succ).trans (by omega))
    have h := length_unrank_add (x 1) (min (x 0).length (rank (y 0)))
    have h₀ := hx 0
    have h₁ := hx 1
    change (unrank (rank (x 1) + min (x 0).length (rank (y 0)))).length ≤ 2 * m
    omega

/-- Every admissible expression obeys the bound computed from its syntax. -/
theorem Expr.length_le {n s : ℕ} (e : Expr n s) : LengthBound (lengthPoly e.1.1) e.eval := by
  refine Expr.induction (P := fun _ e ↦ LengthBound (lengthPoly e.1.1) e.eval) ?_ e
  intro a c ih
  exact lengthBound_evalNode a (fun d ↦ (c d).eval) (fun d ↦ lengthPoly (c d).1.1) ih

/-- Output length is polynomial in normal input length, independently of safe input length. -/
theorem Expr.length_le_poly {n s : ℕ} (e : Expr n s) :
    ∃ c d : ℕ, ∀ x y m, (∀ j, (x j).length ≤ m) →
      (e.eval x y).length ≤ c * (m + 1) ^ d := by
  obtain ⟨c, d, h⟩ := lengthPoly_isPolyBounded e.1.1
  exact ⟨c, d, fun x y m hx ↦ (e.length_le x y m hx).trans (h m)⟩

end Geb.Oitavem
