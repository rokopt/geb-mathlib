/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Logic.Function.Basic
public import Aesop
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SplitIfs

set_option doc.verso true

/-!
# Maintaining the number of unequal binary digits

Counting unequal positions below a fixed width detects equality when both bit streams agree
beyond that width. Flipping one digit changes this count by one, positively for an initially
equal pair and negatively for an initially unequal pair.

## Main definitions

* {lit}`mismatchCount` counts unequal positions below a width.
* {lit}`flipAt` changes one position of a bit stream.

## Main statements

* {lit}`mismatchCount_le` bounds the count by the width.
* {lit}`mismatchCount_flip_left` gives the displacement caused by one bit change.

## Tags

binary counter, Hamming distance, bit stream
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

/-- The number of unequal positions below the given width. -/
def mismatchCount (width : ℕ) (a b : ℕ → Bool) : ℕ :=
  (List.range width).countP fun i ↦ a i != b i

/-- Flip one bit of a stream. -/
def flipAt (a : ℕ → Bool) (i : ℕ) : ℕ → Bool := Function.update a i (!a i)

/-- Extending the width adds the contribution from the new position. -/
theorem mismatchCount_succ (width : ℕ) (a b : ℕ → Bool) :
    mismatchCount (width + 1) a b =
      mismatchCount width a b + if a width = b width then 0 else 1 := by
  simp [mismatchCount, List.range_succ]

/-- There cannot be more unequal positions than positions. -/
theorem mismatchCount_le (width : ℕ) (a b : ℕ → Bool) :
    mismatchCount width a b ≤ width := by
  simpa [mismatchCount] using
    (List.countP_le_length (l := List.range width) (p := fun i ↦ a i != b i))

/-- The count depends only on the bits below the given width. -/
theorem mismatchCount_congr (width : ℕ) (a a' b b' : ℕ → Bool)
    (ha : ∀ i < width, a i = a' i) (hb : ∀ i < width, b i = b' i) :
    mismatchCount width a b = mismatchCount width a' b' := by
  apply List.countP_congr
  intro i hi
  rw [ha i (List.mem_range.mp hi), hb i (List.mem_range.mp hi)]

/-- Interchanging the streams preserves the mismatch count. -/
theorem mismatchCount_comm (width : ℕ) (a b : ℕ → Bool) :
    mismatchCount width a b = mismatchCount width b a := by
  apply List.countP_congr
  intro i _
  simp [ne_comm]

/-- A flip beyond the counted positions leaves the count unchanged. -/
theorem mismatchCount_flip_left_of_le (width i : ℕ) (a b : ℕ → Bool) (h : width ≤ i) :
    mismatchCount width (flipAt a i) b = mismatchCount width a b := by
  apply mismatchCount_congr
  · intro j hj
    exact Function.update_of_ne (by omega) _ _
  · intro j _
    rfl

/-- Flipping a position changes its contribution from zero to one or from one to zero. -/
theorem mismatchCount_flip_left (width i : ℕ) (a b : ℕ → Bool) (h : i < width) :
    (mismatchCount width (flipAt a i) b : ℤ) =
      (mismatchCount width a b : ℤ) + if a i = b i then 1 else -1 := by
  revert i
  apply Nat.rec (motive := fun width ↦ ∀ i, i < width →
    (mismatchCount width (flipAt a i) b : ℤ) =
      (mismatchCount width a b : ℤ) + if a i = b i then 1 else -1) ?_ ?_ width
  · intro i hi
    exact (Nat.not_lt_zero i hi).elim
  · intro k ih i hi
    rw [mismatchCount_succ, mismatchCount_succ]
    by_cases hik : i = k
    · subst i
      rw [mismatchCount_flip_left_of_le k k a b (Nat.le_refl _)]
      simp only [flipAt, Function.update_self]
      cases a k <;> cases b k <;> simp <;> omega
    · have hki : k ≠ i := Ne.symm hik
      have hrec := ih i (by omega)
      simp only [flipAt, Function.update_of_ne hki] at hrec ⊢
      split_ifs at hrec ⊢ <;> omega

/-- A flip of the other stream has the same displacement rule. -/
theorem mismatchCount_flip_right (width i : ℕ) (a b : ℕ → Bool) (h : i < width) :
    (mismatchCount width a (flipAt b i) : ℤ) =
      (mismatchCount width a b : ℤ) + if a i = b i then 1 else -1 := by
  rw [mismatchCount_comm width a (flipAt b i), mismatchCount_flip_left width i b a h,
    mismatchCount_comm width b a]
  simp only [eq_comm]

/-- Equality of bit streams below the width is equivalent to a zero count. -/
theorem mismatchCount_eq_zero (width : ℕ) (a b : ℕ → Bool) :
    mismatchCount width a b = 0 ↔ ∀ i < width, a i = b i := by
  apply Nat.rec (motive := fun width ↦
    mismatchCount width a b = 0 ↔ ∀ i < width, a i = b i) ?_ ?_ width
  · simp [mismatchCount]
  · intro k ih
    rw [mismatchCount_succ]
    constructor
    · intro h i hi
      have hk : a k = b k := by
        split_ifs at h
        omega
      have hprev : mismatchCount k a b = 0 := by omega
      by_cases hik : i < k
      · exact ih.mp hprev i hik
      · have he : i = k := by omega
        simpa [he] using hk
    · intro h
      have hk := h k (by omega)
      have hprev := ih.mpr (fun i hi ↦ h i (by omega))
      simp [hk, hprev]

/-- If the streams agree beyond the width, their bounded count detects their equality. -/
theorem mismatchCount_eq_zero_iff_eq (width : ℕ) (a b : ℕ → Bool)
    (h : ∀ i, width ≤ i → a i = b i) : mismatchCount width a b = 0 ↔ a = b := by
  rw [mismatchCount_eq_zero]
  constructor
  · intro hsmall
    funext i
    by_cases hi : i < width
    · exact hsmall i hi
    · exact h i (by omega)
  · intro he i _
    exact congrFun he i

end Geb.BitTree.BinaryMachine
