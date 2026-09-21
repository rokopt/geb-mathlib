/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Word
import Mathlib.Tactic.Ring

set_option doc.verso true in
/-!
# Bitstrings as natural numbers with a sentinel

A bitstring is represented by its enumeration index {name}`Geb.Oitavem.rank`,
the natural number one less than the numeral whose digits are the string's
bits followed by a sentinel one. Its length is then the binary logarithm of
the index plus one, its bits are the bits of that number, and concatenation,
prefix and suffix are arithmetic on it. In Lean's runtime a natural number
below {lit}`2^63` is an unboxed scalar and a larger one is a GMP integer, so every
operation below is a machine-word operation on strings of at most 62 bits and
a limb operation on longer ones, against one list cell per bit for
{lit}`List Bool`.

The representation is the natural number itself, under the namespace
{lit}`Bits`. Each operation is stated as arithmetic, whose lemmas are in mathlib; the
shift-and-mask forms the runtime executes for the same functions are the
subject of the measurements, not of the proofs.

# Main definitions

* {lit}`Bits.length`, {lit}`Bits.getBit`, {lit}`Bits.append`, {lit}`Bits.take`,
  {lit}`Bits.drop` — the word-level operations.

# Main statements

* {lit}`Bits.length_rank`, {lit}`Bits.getBit_rank`, {lit}`Bits.append_rank`,
  {lit}`Bits.take_rank`, {lit}`Bits.drop_rank` — each operation agrees with the
  list operation under {name}`Geb.Oitavem.rank`.

# Tags

bitstring, bijective numeration, machine word
-/

set_option doc.verso true

@[expose] public section

namespace Geb

open Geb.BitTreeScanner (ofBits ofBits_nil ofBits_cons ofBits_append_true_pos)
open Geb.Oitavem (rank unrank rank_add_one unrank_rank rank_unrank rank_cons
  pow_length_le_rank_add_one)

namespace Bits

/-- The numeral of a list is below two to its length. -/
theorem ofBits_lt_two_pow (d : List Bool) : ofBits d < 2 ^ d.length := by
  refine List.rec ?_ ?_ d
  · simp
  · intro b d ih
    rw [ofBits_cons, Nat.bit_val, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

/-- The numeral of a concatenation. -/
theorem ofBits_append (x y : List Bool) :
    ofBits (x ++ y) = ofBits x + 2 ^ x.length * ofBits y := by
  refine List.rec ?_ ?_ x
  · simp
  · intro b x ih
    rw [List.cons_append, ofBits_cons, ofBits_cons, ih, Nat.bit_val, Nat.bit_val,
      List.length_cons, Nat.pow_succ]
    ring

/-- The sentinel numeral of a string is below two to its length plus one. -/
theorem rank_add_one_lt (w : List Bool) : rank w + 1 < 2 ^ (w.length + 1) := by
  rw [rank_add_one]
  simpa using ofBits_lt_two_pow (w ++ [true])

/-- The length: the binary logarithm of the sentinel numeral. -/
def length (a : ℕ) : ℕ := (a + 1).log2

/-- The length of a string's index is the string's length. -/
@[simp] theorem length_rank (w : List Bool) : length (rank w) = w.length := by
  unfold length
  rw [Nat.log2_eq_iff (by omega)]
  exact ⟨pow_length_le_rank_add_one w, rank_add_one_lt w⟩

/-- The bit at a position, false beyond the length. -/
def getBit (i a : ℕ) : Bool := i < length a && (a + 1).testBit i

/-- The sentinel numeral, as the numeral of the string with its sentinel. -/
theorem rank_add_one_eq (w : List Bool) : rank w + 1 = ofBits w + 2 ^ w.length := by
  rw [rank_add_one, ofBits_append]
  simp [ofBits_cons]

/-- The bits of a numeral are the list's bits, false beyond its end. -/
theorem testBit_ofBits (d : List Bool) (i : ℕ) : (ofBits d).testBit i = d.getD i false := by
  refine List.rec (motive := fun d ↦ ∀ i, (ofBits d).testBit i = d.getD i false) ?_ ?_ d i
  · simp
  · intro b d ih i
    cases i with
    | zero => simp [ofBits_cons]
    | succ i => simp [ofBits_cons, Nat.testBit_bit_succ, ih]

/-- The bit at a position of a string's index is the string's bit there. -/
theorem getBit_rank (i : ℕ) (w : List Bool) : getBit i (rank w) = w.getD i false := by
  unfold getBit
  rw [length_rank, rank_add_one_eq, Nat.add_comm]
  by_cases h : i < w.length
  · rw [Nat.testBit_two_pow_add_gt h, testBit_ofBits]
    simp [h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp [h]

/-- Concatenation: the first string's payload, then the second string's
sentinel numeral shifted past it. -/
def append (a b : ℕ) : ℕ := (a + 1 - 2 ^ length a) + 2 ^ length a * (b + 1) - 1

/-- Concatenation of indices is the index of the concatenation. -/
@[simp] theorem append_rank (w v : List Bool) : append (rank w) (rank v) = rank (w ++ v) := by
  unfold append
  have h1 := rank_add_one_eq w
  have h2 := rank_add_one v
  have h3 := rank_add_one (w ++ v)
  rw [List.append_assoc, ofBits_append] at h3
  rw [length_rank, h2]
  generalize 2 ^ w.length = p at *
  generalize p * ofBits (v ++ [true]) = q at *
  omega

/-- The prefix of a given length: the low bits, with a new sentinel. -/
def take (k a : ℕ) : ℕ := (a + 1) % 2 ^ k + 2 ^ k - 1

/-- The suffix after a given length: the high bits, the sentinel kept. -/
def drop (k a : ℕ) : ℕ := (a + 1) / 2 ^ k - 1

/-- The prefix of an index is the index of the prefix. -/
theorem take_rank (k : ℕ) (w : List Bool) (hk : k ≤ w.length) :
    take k (rank w) = rank (w.take k) := by
  unfold take
  have h1 := rank_add_one_eq w
  have h2 := rank_add_one_eq (w.take k)
  have h3 : ofBits w = ofBits (w.take k) + 2 ^ k * ofBits (w.drop k) := by
    have := ofBits_append (w.take k) (w.drop k)
    rwa [List.take_append_drop, List.length_take, Nat.min_eq_left hk] at this
  have h4 := ofBits_lt_two_pow (w.take k)
  rw [List.length_take, Nat.min_eq_left hk] at h2 h4
  have h5 : (rank w + 1) % 2 ^ k = ofBits (w.take k) := by
    rw [h1, h3, ← Nat.pow_sub_mul_pow 2 hk, show ofBits (w.take k) + 2 ^ k * ofBits (w.drop k) +
      2 ^ (w.length - k) * 2 ^ k = ofBits (w.take k) + 2 ^ k * (ofBits (w.drop k) +
      2 ^ (w.length - k)) by ring, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt h4
  rw [h5]
  generalize 2 ^ k = p at *
  omega

/-- The suffix of an index is the index of the suffix. -/
theorem drop_rank (k : ℕ) (w : List Bool) (hk : k ≤ w.length) :
    drop k (rank w) = rank (w.drop k) := by
  unfold drop
  have h1 := rank_add_one_eq w
  have h2 := rank_add_one_eq (w.drop k)
  have h3 : ofBits w = ofBits (w.take k) + 2 ^ k * ofBits (w.drop k) := by
    have := ofBits_append (w.take k) (w.drop k)
    rwa [List.take_append_drop, List.length_take, Nat.min_eq_left hk] at this
  have h4 := ofBits_lt_two_pow (w.take k)
  rw [List.length_take, Nat.min_eq_left hk] at h4
  rw [List.length_drop] at h2
  have h5 : (rank w + 1) / 2 ^ k = ofBits (w.drop k) + 2 ^ (w.length - k) := by
    rw [h1, h3, ← Nat.pow_sub_mul_pow 2 hk, show ofBits (w.take k) + 2 ^ k * ofBits (w.drop k) +
      2 ^ (w.length - k) * 2 ^ k = ofBits (w.take k) + 2 ^ k * (ofBits (w.drop k) +
      2 ^ (w.length - k)) by ring, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k),
      Nat.div_eq_of_lt h4, Nat.zero_add]
  rw [h5]
  generalize 2 ^ (w.length - k) = p at *
  omega

end Bits

end Geb

end
