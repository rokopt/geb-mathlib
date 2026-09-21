/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Length
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Output length as a function of expression size

The polynomial bound {name}`Geb.Oitavem.lengthPoly` on an expression's output
length has degree and coefficients depending on the expression. Uniformly in
the expression, the bound is a double exponential: at normal arguments of
length at most {lit}`m`, an expression of {lit}`s` nodes has output length at
most {lit}`(m + 2) ^ 2 ^ s`. The exponent's exponent is attained up to a
constant factor: composing a unary squaring, the product of an argument with
itself, {lit}`k` times over a two-bit constant is an expression of size linear
in {lit}`k` whose value at the empty word has length {lit}`2 ^ 2 ^ k`. The
logarithm of the largest intermediate word of an evaluation is therefore
exponential in the code's size, not polynomial, which sets the space of an
evaluator reading the expression from its input.

# Main definitions

* {lit}`sizeNode`, {lit}`size` — the number of nodes of a syntax tree.

# Main statements

* {lit}`lengthPoly_le_pow` — the length polynomial at {lit}`m` is at most
  {lit}`(m + 2) ^ 2 ^ size`.
* {lit}`Expr.length_le_pow` — the output length of an expression at normal
  arguments of length at most {lit}`m` is at most {lit}`(m + 2) ^ 2 ^ size`.

# References

* {cite}`Oitavem2010`, Definition 3.1.

# Tags

logspace, polynomial length, expression size, implicit complexity
-/

set_option doc.verso true

namespace Geb.Oitavem

open Geb.SizeBounded (finMax finMax_le le_finMax finSum)

public section

/-- Every member of a finite family is at most its sum. -/
theorem le_finSum : ∀ (m : ℕ) (f : Fin m → ℕ) (i : Fin m), f i ≤ finSum m f :=
  Nat.rec (fun _ i ↦ i.elim0) fun m ih f i ↦
    Fin.lastCases (motive := fun i ↦ f i ≤ finSum (m + 1) f) (Nat.le_add_left _ _)
      (fun j ↦ Nat.le_trans (ih (fun i ↦ f i.castSucc) j) (Nat.le_add_right _ _)) i

/-- The number of nodes at one node, from its children's. -/
@[expose] def sizeNode : (s : Shape) → (Direction s → ℕ) → ℕ
  | .initial _, _ => 1
  | .comp _ k _, p => 1 + p (.inl ()) + finSum k fun j ↦ p (.inr j)
  | .safeRec _, p => 1 + p (.inl ()) + p (.inr false) + p (.inr true)
  | .concatRec _, p => 1 + p (.inl ()) + p (.inr false) + p (.inr true)
  | .logTransition _, p => 1 + p ()

/-- The number of nodes of a syntax tree. -/
@[expose] def size : sig.toPFunctor.W → ℕ := WType.elim ℕ fun x ↦ sizeNode x.1 x.2

/-- The double exponential is monotone in the size. -/
theorem pow_pow_le_pow_pow (m : ℕ) {a b : ℕ} (h : a ≤ b) : (m + 2) ^ 2 ^ a ≤ (m + 2) ^ 2 ^ b :=
  Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) h)

/-- Adding two to a positive power of {lit}`m + 2` stays below the next power. -/
theorem pow_add_two_le (m : ℕ) {a : ℕ} (ha : 1 ≤ a) : (m + 2) ^ a + 2 ≤ (m + 2) ^ (a + 1) := by
  have h2 : 2 ≤ (m + 2) ^ a :=
    (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp ha) 2).trans (Nat.pow_le_pow_left (by omega) a)
  rw [Nat.pow_succ]
  calc (m + 2) ^ a + 2 ≤ (m + 2) ^ a + (m + 2) ^ a := Nat.add_le_add_left h2 _
    _ = (m + 2) ^ a * 2 := by omega
    _ ≤ (m + 2) ^ a * (m + 2) := Nat.mul_le_mul_left _ (by omega)

/-- A power of two plus one is at most the next power of two. -/
theorem two_pow_add_one_le (a : ℕ) : 2 ^ a + 1 ≤ 2 ^ (a + 1) := by
  rw [Nat.pow_succ]
  have := Nat.one_le_two_pow (n := a)
  omega

/-- The bound at one node is at most the double exponential in the node's size
when each child's bound is monotone and at most the double exponential in the
child's size. -/
theorem lengthPolyNode_le_pow (s : Shape) (p : Direction s → ℕ → ℕ) (k : Direction s → ℕ)
    (hp : ∀ d, Monotone (p d)) (hk : ∀ d m, p d m ≤ (m + 2) ^ 2 ^ k d) (m : ℕ) :
    lengthPolyNode s p m ≤ (m + 2) ^ 2 ^ sizeNode s k := by
  cases s with
  | initial _ =>
    change (m + 1) * (m + 1) ≤ (m + 2) ^ 2 ^ 1
    rw [Nat.pow_one, Nat.pow_two]
    exact Nat.mul_le_mul (by omega) (by omega)
  | comp _ j _ =>
    change p (.inl ()) (finMax j fun i ↦ p (.inr i) m) ≤
      (m + 2) ^ 2 ^ (1 + k (.inl ()) + finSum j fun i ↦ k (.inr i))
    have hmax : (finMax j fun i ↦ p (.inr i) m) ≤ (m + 2) ^ 2 ^ finSum j fun i ↦ k (.inr i) :=
      finMax_le j _ _ fun i ↦
        (hk (.inr i) m).trans (pow_pow_le_pow_pow m (le_finSum j (fun i ↦ k (.inr i)) i))
    calc p (.inl ()) (finMax j fun i ↦ p (.inr i) m)
        ≤ p (.inl ()) ((m + 2) ^ 2 ^ finSum j fun i ↦ k (.inr i)) := hp (.inl ()) hmax
      _ ≤ ((m + 2) ^ 2 ^ (finSum j fun i ↦ k (.inr i)) + 2) ^ 2 ^ k (.inl ()) := hk (.inl ()) _
      _ ≤ ((m + 2) ^ (2 ^ (finSum j fun i ↦ k (.inr i)) + 1)) ^ 2 ^ k (.inl ()) :=
        Nat.pow_le_pow_left (pow_add_two_le m Nat.one_le_two_pow) _
      _ = (m + 2) ^ ((2 ^ (finSum j fun i ↦ k (.inr i)) + 1) * 2 ^ k (.inl ())) := by
        rw [← Nat.pow_mul]
      _ ≤ (m + 2) ^ 2 ^ (1 + k (.inl ()) + finSum j fun i ↦ k (.inr i)) := by
        refine Nat.pow_le_pow_right (by omega) ?_
        rw [show 1 + k (.inl ()) + (finSum j fun i ↦ k (.inr i)) =
          (finSum j fun i ↦ k (.inr i)) + 1 + k (.inl ()) by omega, Nat.pow_add]
        exact Nat.mul_le_mul_right _ (two_pow_add_one_le _)
  | safeRec _ =>
    change max (p (.inl ()) m) (max (p (.inr false) m) (p (.inr true) m)) ≤
      (m + 2) ^ 2 ^ (1 + k (.inl ()) + k (.inr false) + k (.inr true))
    exact Nat.max_le.mpr ⟨(hk (.inl ()) m).trans (pow_pow_le_pow_pow m (by omega)),
      Nat.max_le.mpr ⟨(hk (.inr false) m).trans (pow_pow_le_pow_pow m (by omega)),
        (hk (.inr true) m).trans (pow_pow_le_pow_pow m (by omega))⟩⟩
  | concatRec _ =>
    change p (.inl ()) m + m ≤ (m + 2) ^ 2 ^ (1 + k (.inl ()) + k (.inr false) + k (.inr true))
    have hm : m ≤ (m + 2) ^ 2 ^ k (.inl ()) :=
      (Nat.le_add_right m 2).trans (Nat.le_self_pow (Nat.pos_iff_ne_zero.mp Nat.one_le_two_pow) _)
    calc p (.inl ()) m + m ≤ (m + 2) ^ 2 ^ k (.inl ()) + (m + 2) ^ 2 ^ k (.inl ()) :=
          Nat.add_le_add (hk (.inl ()) m) hm
      _ = (m + 2) ^ 2 ^ k (.inl ()) * 2 := by omega
      _ ≤ (m + 2) ^ 2 ^ k (.inl ()) * (m + 2) := Nat.mul_le_mul_left _ (by omega)
      _ = (m + 2) ^ (2 ^ k (.inl ()) + 1) := by rw [← Nat.pow_succ]
      _ ≤ (m + 2) ^ 2 ^ (k (.inl ()) + 1) :=
          Nat.pow_le_pow_right (by omega) (two_pow_add_one_le _)
      _ ≤ (m + 2) ^ 2 ^ (1 + k (.inl ()) + k (.inr false) + k (.inr true)) :=
          pow_pow_le_pow_pow m (by omega)
  | logTransition _ =>
    change p () (2 * m) ≤ (m + 2) ^ 2 ^ (1 + k ())
    have hsq : 2 * m + 2 ≤ (m + 2) ^ 2 := by
      rw [Nat.pow_two]
      calc 2 * m + 2 ≤ 2 * (m + 2) := by omega
        _ ≤ (m + 2) * (m + 2) := Nat.mul_le_mul_right _ (by omega)
    calc p () (2 * m) ≤ (2 * m + 2) ^ 2 ^ k () := hk () _
      _ ≤ ((m + 2) ^ 2) ^ 2 ^ k () := Nat.pow_le_pow_left hsq _
      _ = (m + 2) ^ 2 ^ (1 + k ()) := by
        rw [← Nat.pow_mul, Nat.add_comm 1, Nat.pow_succ, Nat.mul_comm]

/-- The length polynomial at {lit}`m` is at most {lit}`(m + 2) ^ 2 ^ size`. -/
theorem lengthPoly_le_pow (w : sig.toPFunctor.W) (m : ℕ) :
    lengthPoly w m ≤ (m + 2) ^ 2 ^ size w :=
  WType.rec (motive := fun w ↦ ∀ m, lengthPoly w m ≤ (m + 2) ^ 2 ^ size w)
    (fun s c ih ↦ lengthPolyNode_le_pow s (fun d ↦ lengthPoly (c d)) (fun d ↦ size (c d))
      (fun d ↦ lengthPoly_mono (c d)) ih) w m

/-- The output length of an expression at normal arguments of length at most
{lit}`m` is at most {lit}`(m + 2) ^ 2 ^ size`. -/
theorem Expr.length_le_pow {n s : ℕ} (e : Expr n s) (x : Fin n → List Bool)
    (y : Fin s → List Bool) (m : ℕ) (hx : ∀ j, (x j).length ≤ m) :
    (e.eval x y).length ≤ (m + 2) ^ 2 ^ size e.1.1 :=
  (e.length_le x y m hx).trans (lengthPoly_le_pow e.1.1 m)

end

end Geb.Oitavem
