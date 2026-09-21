/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Word

set_option doc.verso true in
/-!
# Digitwise addition of a bounded carry to a shortlex word

The carry scan adds a natural number to a virtual shortlex word without decoding
that word's rank. It reads the sentinel encoding one digit at a time and emits any
remaining carry in binary. Removing the final sentinel gives the numerical sum.
The carried value never exceeds the larger of the original carry and one.

## Main definitions

* {lit}`carryBits` emits the digits of a sum while carrying a natural number.
* {lit}`carryAfter` records the carry after a prefix has been read.
* {lit}`shortlexAdd` adds a natural number to a word in the existing shortlex model.

## Main statements

* {lit}`shortlexAdd_eq_unrank_add` proves the arithmetic result.
* {lit}`carryAfter_take_le_max` bounds every intermediate carry.
* {lit}`carryBits_drop` describes resuming the scan from its saved carry.

## Implementation notes

The arithmetic proof was developed with Aristotle and adapted to the project's word
model. The list algorithm is a specification for a streaming implementation; it does
not by itself prove a Turing-machine space bound.

## Tags

binary arithmetic, addition, carry, shortlex
-/

set_option doc.verso true

namespace Geb.Oitavem

public section

open Geb.BitTreeScanner

/-! ## Binary digits of a natural number -/

/-- The binary digits of a nonzero number: the parity digit, then the digits of the
halved number. -/
theorem bits_eq_cons_of_ne_zero (n : ℕ) (hn : n ≠ 0) :
    n.bits = decide (n % 2 = 1) :: (n / 2).bits := by
  by_cases h : n % 2 = 1
  · have hn2 : n = 2 * (n / 2) + 1 := by omega
    rw [decide_eq_true h]
    conv_lhs => rw [hn2]
    rw [Nat.bit1_bits]
  · have hn2 : n = 2 * (n / 2) := by omega
    have hne : n / 2 ≠ 0 := by omega
    rw [decide_eq_false h]
    conv_lhs => rw [hn2]
    rw [Nat.bit0_bits _ hne]

/-! ## The digitwise scan -/

/-- The digits the scan emits from the input digits {lit}`bs`, read least significant
first, and an incoming carry {lit}`c`: one digit per input digit, then the binary digits
of the carry that is left. -/
@[expose] def carryBits : List Bool → ℕ → List Bool
  | [], c => c.bits
  | b :: bs, c => decide ((b.toNat + c) % 2 = 1) :: carryBits bs ((b.toNat + c) / 2)

/-- The carry the scan is left with after consuming the input digits {lit}`bs`. -/
@[expose] def carryAfter : List Bool → ℕ → ℕ
  | [], c => c
  | b :: bs, c => carryAfter bs ((b.toNat + c) / 2)

/-- With the input exhausted the scan emits the binary digits of the carry. -/
theorem carryBits_nil (c : ℕ) : carryBits [] c = c.bits := rfl

/-- One step of the scan: it reads the current digit and the carry, and nothing else. -/
theorem carryBits_cons (b : Bool) (bs : List Bool) (c : ℕ) :
    carryBits (b :: bs) c =
      decide ((b.toNat + c) % 2 = 1) :: carryBits bs ((b.toNat + c) / 2) :=
  rfl

/-- One step of the carry. -/
theorem carryAfter_cons (b : Bool) (bs : List Bool) (c : ℕ) :
    carryAfter (b :: bs) c = carryAfter bs ((b.toNat + c) / 2) :=
  rfl

/-- The canonical-binary invariant on a sentinelled input: the scan emits exactly the
binary digits of the value of the input plus the incoming carry. -/
theorem carryBits_append_true (l : List Bool) : (c : ℕ) →
    carryBits (l ++ [true]) c = (ofBits (l ++ [true]) + c).bits := by
  induction l with
  | nil =>
    intro c
    have h1 : ofBits ([] ++ [true]) = 1 := rfl
    rw [h1, List.nil_append, carryBits_cons, carryBits_nil,
      bits_eq_cons_of_ne_zero (1 + c) (by omega)]
    simp
  | cons b bs ih =>
    intro c
    have htail : ofBits (bs ++ [true]) = rank bs + 1 := (rank_add_one bs).symm
    have hpos : 1 ≤ ofBits (bs ++ [true]) := by omega
    have hval : ofBits (b :: (bs ++ [true])) = b.toNat + 2 * ofBits (bs ++ [true]) := by
      have hhead : ofBits ((b :: bs) ++ [true]) = rank (b :: bs) + 1 :=
        (rank_add_one (b :: bs)).symm
      have hcons : rank (b :: bs) = b.toNat + 2 * rank bs + 1 := by rw [rank_cons]; omega
      simp only [List.cons_append] at hhead
      omega
    have hne : ofBits (b :: (bs ++ [true])) + c ≠ 0 := by omega
    have hpar : (ofBits (b :: (bs ++ [true])) + c) % 2 = (b.toNat + c) % 2 := by omega
    have hhalf : (ofBits (b :: (bs ++ [true])) + c) / 2 =
        ofBits (bs ++ [true]) + (b.toNat + c) / 2 := by omega
    rw [List.cons_append, carryBits_cons, ih, bits_eq_cons_of_ne_zero _ hne, hpar, hhalf]

/-- The canonical-binary invariant: on an input whose last digit is {lit}`true` the scan
emits exactly the binary digits of the value of the input plus the incoming carry. -/
theorem carryBits_eq_bits_of_getLast (bs : List Bool) (h : bs.getLast? = some true)
    (c : ℕ) : carryBits bs c = (ofBits bs + c).bits := by
  rcases List.eq_nil_or_concat' bs with rfl | ⟨l, b, rfl⟩
  · simp at h
  · simp only [List.getLast?_concat, Option.some.injEq] at h
    subst h
    exact carryBits_append_true l c

/-! ## The carry stays bounded -/

/-- The carry never exceeds the larger of the incoming carry and one. -/
theorem carryAfter_le_max (bs : List Bool) : (c : ℕ) → carryAfter bs c ≤ max c 1 := by
  induction bs with
  | nil => intro c; rw [carryAfter]; omega
  | cons b bs ih =>
    intro c
    have hb : b.toNat ≤ 1 := by cases b <;> simp
    have h := ih ((b.toNat + c) / 2)
    rw [carryAfter_cons]
    omega

/-- Scanning more digits cannot raise the bound. -/
theorem carryAfter_take_le_max (w : List Bool) (n k : ℕ) :
    carryAfter ((w ++ [true]).take k) n ≤ max n 1 :=
  carryAfter_le_max _ n

/-- After {lit}`k` steps the scan's entire state is the carry {lit}`carryAfter`: the
digits still to be emitted are those the scan produces from the remaining input and that
carry. -/
theorem carryBits_drop : (k : ℕ) → (bs : List Bool) → (c : ℕ) → k ≤ bs.length →
    (carryBits bs c).drop k = carryBits (bs.drop k) (carryAfter (bs.take k) c)
  | 0, bs, c, _ => by simp [carryAfter]
  | k + 1, [], _, h => absurd h (by simp)
  | k + 1, b :: bs, c, h => by
    have h' : k ≤ bs.length := by simpa using h
    have ih := carryBits_drop k bs ((b.toNat + c) / 2) h'
    rw [carryBits_cons, List.drop_succ_cons, ih, List.take_succ_cons, List.drop_succ_cons,
      carryAfter_cons]

/-! ## The algorithm -/

/-- Add {lit}`n` to the number a word denotes: scan the sentinelled word with initial
carry {lit}`n` and drop the sentinel the scan emits last. -/
@[expose] def shortlexAdd (w : List Bool) (n : ℕ) : List Bool :=
  (carryBits (w ++ [true]) n).dropLast

/-- The algorithm computes the rank notation of {lit}`rank w + n`. -/
theorem shortlexAdd_eq_unrank_add (w : List Bool) (n : ℕ) :
    shortlexAdd w n = unrank (rank w + n) := by
  have hsucc : ofBits (w ++ [true]) + n = rank w + n + 1 := by
    rw [← rank_add_one w]; omega
  rw [shortlexAdd, carryBits_append_true w n, hsucc, unrank]

/-- The scan emits the answer followed by one sentinel {lit}`true`: the digit dropped is
exactly the sentinel. -/
theorem carryBits_append_true_eq_concat (w : List Bool) (n : ℕ) :
    carryBits (w ++ [true]) n = shortlexAdd w n ++ [true] := by
  rw [shortlexAdd_eq_unrank_add, unrank_append, carryBits_append_true, ← rank_add_one]
  congr 1
  omega

end

end Geb.Oitavem
