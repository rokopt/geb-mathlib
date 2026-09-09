/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.CodeBits

set_option doc.verso true

/-!
# Fixed-width binary countdown

Digits are stored least significant first, with leading zeroes retained. Decrement propagates
a borrow through the initial zeroes and clears the first one. At zero it wraps within the
existing width; numeric correctness is therefore stated for positive inputs.

## Main definitions

* {lit}`value` interprets a list of binary digits.
* {lit}`decrement` preserves the width while subtracting one.
* {lit}`borrowFlips` counts the digits changed by a borrow.

## Main statements

* {lit}`length_decrement` states width preservation.
* {lit}`value_decrement` gives the numeric meaning for positive counter values.

## Tags

binary counter, decrement, borrow, fixed width
-/

@[expose] public section

namespace Geb.BitTree.Elias.Counter

/-- Interpret binary digits, allowing leading zeroes. -/
def value (bs : List Bool) : ℕ := bs.foldr Nat.bit 0

/-- Adding a least significant digit doubles the value and adds that digit. -/
theorem value_cons (b : Bool) (bs : List Bool) :
    value (b :: bs) = 2 * value bs + b.toNat := Nat.bit_val b (value bs)

/-- Canonical binary digits represent the number from which they were obtained. -/
theorem value_bits (n : ℕ) : value n.bits = n := foldr_bits n

/-- A binary word represents zero exactly when all its digits are zero. -/
theorem value_eq_zero_iff (bs : List Bool) : value bs = 0 ↔ ∀ b ∈ bs, b = false := by
  apply List.rec (motive := fun bs ↦ value bs = 0 ↔ ∀ b ∈ bs, b = false) ?_ ?_ bs
  · simp [value]
  · intro b bs ih
    rw [value_cons, List.forall_mem_cons]
    cases b
    · simp only [Bool.toNat_false]
      constructor
      · intro h
        exact ⟨trivial, ih.mp (by omega)⟩
      · rintro ⟨_, h⟩
        have ht := ih.mpr h
        omega
    · simp only [Bool.toNat_true]
      constructor
      · intro h
        omega
      · rintro ⟨h, _⟩
        cases h

/-- The usual boolean test for an all-zero word agrees with its numeric value. -/
theorem all_not_eq_true_iff (bs : List Bool) :
    bs.all (fun b ↦ !b) = true ↔ value bs = 0 := by
  rw [value_eq_zero_iff, List.all_eq_true]
  constructor
  · intro h b hb
    have he := h b hb
    cases b
    · rfl
    · cases he
  · intro h b hb
    rw [h b hb]
    rfl

/-- Recording whether any digit is one detects a zero counter. -/
theorem any_eq_false_iff (bs : List Bool) : bs.any id = false ↔ value bs = 0 := by
  rw [List.any_eq_false, value_eq_zero_iff]
  constructor
  · intro h b hb
    have hn := h b hb
    cases b
    · rfl
    · exact False.elim (hn rfl)
  · intro h b hb
    rw [h b hb]
    intro he
    cases he

/-- Subtract one within the existing width, wrapping an all-zero word. -/
def decrement : List Bool → List Bool :=
  List.rec [] fun b bs next ↦ if b then false :: bs else true :: next

/-- Count the initial zeroes and the first one, or the whole width at zero. -/
def borrowFlips : List Bool → ℕ :=
  List.foldr (fun b n ↦ if b then 1 else n + 1) 0

/-- Decrement never changes the allocated width. -/
theorem length_decrement (bs : List Bool) : (decrement bs).length = bs.length := by
  apply List.rec (motive := fun bs ↦ (decrement bs).length = bs.length) ?_ ?_ bs
  · rfl
  · intro b bs ih
    cases b <;> simp_all [decrement]

/-- A borrow changes at most the allocated width. -/
theorem borrowFlips_le_length (bs : List Bool) : borrowFlips bs ≤ bs.length := by
  apply List.rec (motive := fun bs ↦ borrowFlips bs ≤ bs.length) ?_ ?_ bs
  · exact Nat.le_refl _
  · intro b bs ih
    cases b <;> simp_all [borrowFlips]

/-- Decrement subtracts one from every positive represented value. -/
theorem value_decrement (bs : List Bool) (h : 0 < value bs) :
    value (decrement bs) = value bs - 1 := by
  revert h
  apply List.rec (motive := fun bs ↦ 0 < value bs →
    value (decrement bs) = value bs - 1) ?_ ?_ bs
  · intro h
    exact (Nat.not_lt_zero 0 h).elim
  · intro b bs ih h
    cases b
    · have hp : 0 < value bs := by
        rw [value_cons] at h
        simp only [Bool.toNat_false] at h
        omega
      change value (true :: decrement bs) = value (false :: bs) - 1
      rw [value_cons, value_cons, ih hp]
      simp only [Bool.toNat_true, Bool.toNat_false]
      omega
    · change value (false :: bs) = value (true :: bs) - 1
      rw [value_cons, value_cons]
      simp only [Bool.toNat_true, Bool.toNat_false]
      omega

/-- A positive counter requires at least one changed digit. -/
theorem borrowFlips_pos (bs : List Bool) (h : 0 < value bs) : 0 < borrowFlips bs := by
  cases bs with
  | nil => exact (Nat.not_lt_zero 0 h).elim
  | cons b bs => cases b <;> simp [borrowFlips]

/-- Every digit before the final changed position is zero. -/
theorem getD_eq_false_of_lt_borrowFlips (bs : List Bool) (i : ℕ)
    (h : i + 1 < borrowFlips bs) : bs[i]?.getD false = false := by
  revert i
  apply List.rec (motive := fun bs ↦ ∀ i, i + 1 < borrowFlips bs →
    bs[i]?.getD false = false) ?_ ?_ bs
  · intro i _
    rfl
  · intro b bs ih i hi
    cases b
    · cases i with
      | zero => rfl
      | succ i =>
        change bs[i]?.getD false = false
        apply ih
        change i + 1 + 1 < borrowFlips bs + 1 at hi
        omega
    · change i + 1 < 1 at hi
      omega

/-- The final changed position of a positive counter contains one. -/
theorem getD_last_borrowFlips (bs : List Bool) (h : 0 < value bs) :
    bs[borrowFlips bs - 1]?.getD false = true := by
  revert h
  apply List.rec (motive := fun bs ↦ 0 < value bs →
    bs[borrowFlips bs - 1]?.getD false = true) ?_ ?_ bs
  · intro h
    exact (Nat.not_lt_zero 0 h).elim
  · intro b bs ih h
    cases b
    · have hp : 0 < value bs := by
        rw [value_cons] at h
        simp only [Bool.toNat_false] at h
        omega
      have hf := borrowFlips_pos bs hp
      have he : borrowFlips (false :: bs) - 1 = (borrowFlips bs - 1) + 1 := by
        change borrowFlips bs + 1 - 1 = borrowFlips bs - 1 + 1
        omega
      simpa only [he, List.getElem?_cons_succ] using ih hp
    · rfl

/-- Decrement flips exactly the initial borrow positions, preserving all later digits. -/
theorem getD_decrement (bs : List Bool) (i : ℕ) :
    (decrement bs)[i]?.getD false =
      if i < borrowFlips bs then !bs[i]?.getD false else bs[i]?.getD false := by
  revert i
  apply List.rec (motive := fun bs ↦ ∀ i,
    (decrement bs)[i]?.getD false =
      if i < borrowFlips bs then !bs[i]?.getD false else bs[i]?.getD false) ?_ ?_ bs
  · intro i
    change false = if i < 0 then true else false
    simp only [show ¬i < 0 from by omega, ↓reduceIte]
  · intro b bs ih i
    cases b
    · cases i with
      | zero =>
        change true = if 0 < borrowFlips bs + 1 then true else false
        simp only [show 0 < borrowFlips bs + 1 from by omega, ↓reduceIte]
      | succ i =>
        change (decrement bs)[i]?.getD false =
          if i + 1 < borrowFlips bs + 1 then !bs[i]?.getD false else bs[i]?.getD false
        have he : (i + 1 < borrowFlips bs + 1) ↔ (i < borrowFlips bs) := by
          constructor <;> intro h <;> omega
        simpa only [he] using ih i
    · cases i with
      | zero => rfl
      | succ i =>
        change bs[i]?.getD false =
          if i + 1 < 1 then !bs[i]?.getD false else bs[i]?.getD false
        simp only [show ¬i + 1 < 1 from by omega, ↓reduceIte]

/-- The zero-digit potential pays for a borrow even when zero wraps to all ones. -/
theorem borrowFlips_add_count_decrement_le (bs : List Bool) :
    borrowFlips bs + (decrement bs).count false ≤ bs.count false + 2 := by
  apply List.rec (motive := fun bs ↦
    borrowFlips bs + (decrement bs).count false ≤ bs.count false + 2) ?_ ?_ bs
  · decide
  · intro b bs ih
    cases b <;> simp_all [decrement, borrowFlips] <;> omega

end Geb.BitTree.Elias.Counter
