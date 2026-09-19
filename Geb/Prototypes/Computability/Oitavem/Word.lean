/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Encoding
public import Geb.Prototypes.Computability.BitTree.Counter
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Oitavem's enumeration of binary words

The bijection of {cite}`Oitavem2010` Remark 2.2, with lists written least significant
bit first, as in the other function algebras in this repository. Thus the paper's
rightmost bit is the head of a list. All words, including those with leading
zeroes, are distinct. The empty word represents zero, and the singleton words
represent one and two.

## Main definitions

* {lit}`rank` and {lit}`unrank` convert between words and their enumeration indices.
* {lit}`numericSucc`, {lit}`numericPred`, and {lit}`numericSub` implement the numerical
  primitives, as distinct from adjoining or deleting one digit.

## Main statements

* {lit}`rank_unrank` and {lit}`unrank_rank` prove the conversion is a bijection.
* {lit}`length_unrank` relates word length to binary size.

## References

* {cite}`Oitavem2010`, Sections 1.1 and 2, Remark 2.2.

## Tags

binary word, bijective numeration, logspace
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Oitavem

open Geb.BitTreeScanner (ofBits ofBits_append_true_pos bits_ofBits ofBits_bits
  exists_bits_eq_append_true)

/-- The index of a word in the paper's length-lexicographic enumeration. -/
def rank (w : List Bool) : ℕ := ofBits (w ++ [true]) - 1

/-- The word at a given enumeration index, obtained by deleting the binary sentinel. -/
def unrank (n : ℕ) : List Bool := (n + 1).bits.dropLast

/-- The sentinel representation of an index is positive. -/
theorem rank_add_one (w : List Bool) : rank w + 1 = ofBits (w ++ [true]) := by
  have := ofBits_append_true_pos w
  unfold rank
  omega

/-- Decoding an index gives the original word, including its leading zeroes. -/
@[simp] theorem unrank_rank (w : List Bool) : unrank (rank w) = w := by
  simp only [unrank, rank_add_one, bits_ofBits, List.dropLast_concat]

/-- The digits of a positive number consist of its payload and the sentinel. -/
theorem unrank_append (n : ℕ) : unrank n ++ [true] = (n + 1).bits := by
  obtain ⟨w, hw⟩ := exists_bits_eq_append_true (n + 1) (by omega)
  simp only [unrank, hw, List.dropLast_concat]

/-- Encoding the word at an index gives that index. -/
@[simp] theorem rank_unrank (n : ℕ) : rank (unrank n) = n := by
  rw [rank, unrank_append, ofBits_bits]
  omega

/-- Enumeration indices distinguish every pair of words. -/
theorem rank_injective : Function.Injective rank :=
  fun x y h ↦ by rw [← unrank_rank x, ← unrank_rank y, h]

/-- The empty word represents zero. -/
@[simp] theorem rank_nil : rank [] = 0 := rfl

/-- Index zero represents the empty word. -/
@[simp] theorem unrank_zero : unrank 0 = [] := rfl

/-- A word's length is one less than the binary size of its index plus one. -/
theorem length_unrank (n : ℕ) : (unrank n).length + 1 = (n + 1).size := by
  have h := congrArg List.length (unrank_append n)
  simpa only [List.length_append, List.length_singleton, ← Nat.size_eq_bits_len] using h

/-- Prepending a digit corresponds to bijective base-two arithmetic. -/
theorem rank_cons (b : Bool) (w : List Bool) :
    rank (b :: w) = 2 * rank w + b.toNat + 1 := by
  have h := rank_add_one w
  have h' := rank_add_one (b :: w)
  simp only [List.cons_append, Geb.BitTreeScanner.ofBits_cons, Nat.bit_val] at h'
  omega

/-- Every word of length k has enumeration index at least two to the k minus one. -/
theorem pow_length_le_rank_add_one (w : List Bool) : 2 ^ w.length ≤ rank w + 1 := by
  apply List.rec (motive := fun w ↦ 2 ^ w.length ≤ rank w + 1) ?_ ?_ w
  · simp
  · intro b v ih
    rw [List.length_cons, Nat.pow_succ, rank_cons]
    omega

/-- Deleting high-order digits cannot increase the enumeration index. -/
theorem rank_take_le (w : List Bool) (k : ℕ) : rank (w.take k) ≤ rank w := by
  apply List.rec (motive := fun w ↦ ∀ k, rank (w.take k) ≤ rank w) ?_ ?_ w k
  · intro k
    simp
  · intro b v ih k
    cases k with
    | zero => simp
    | succ k =>
      simp only [List.take_succ_cons, rank_cons]
      have := ih k
      omega

/-- The numerical successor in the enumeration of words. -/
def numericSucc (w : List Bool) : List Bool := unrank (rank w + 1)

/-- The numerical predecessor, with zero fixed. -/
def numericPred (w : List Bool) : List Bool := unrank (rank w - 1)

/-- Iterated numerical predecessor: subtract the index of the first argument. -/
def numericSub (v w : List Bool) : List Bool := unrank (rank w - rank v)

/-- Numerical successor increases the index by one. -/
@[simp] theorem rank_numericSucc (w : List Bool) : rank (numericSucc w) = rank w + 1 :=
  rank_unrank _

/-- Numerical predecessor undoes numerical successor. -/
@[simp] theorem numericPred_numericSucc (w : List Bool) :
    numericPred (numericSucc w) = w := by
  simp [numericPred]

/-- A numerical index bounded by a word-length bound has logarithmic representation length. -/
theorem length_unrank_le {n B : ℕ} (h : n ≤ B) :
    (unrank n).length ≤ (B + 1).size := by
  have hn := length_unrank n
  have hb := Geb.BitTree.Counter.size_mono (show n + 1 ≤ B + 1 by omega)
  omega

/-- Word lengths are monotone in their enumeration indices. -/
theorem length_unrank_mono {m n : ℕ} (h : m ≤ n) :
    (unrank m).length ≤ (unrank n).length := by
  have hm := length_unrank m
  have hn := length_unrank n
  have hs := Geb.BitTree.Counter.size_mono (show m + 1 ≤ n + 1 by omega)
  omega

/-- One numerical successor increases word length by at most one. -/
theorem length_unrank_succ_le (n : ℕ) :
    (unrank (n + 1)).length ≤ (unrank n).length + 1 := by
  have h := Geb.BitTree.Counter.size_mono (show n + 1 + 1 ≤ Nat.bit false (n + 1) by
    simp only [Nat.bit_val, Bool.toNat_false]
    omega)
  rw [Nat.size_bit (by simp [Nat.bit_val])] at h
  have h₀ := length_unrank n
  have h₁ := length_unrank (n + 1)
  omega

/-- Adding a numerical offset increases length by at most that offset. -/
theorem length_unrank_add (w : List Bool) (k : ℕ) :
    (unrank (rank w + k)).length ≤ w.length + k := by
  apply Nat.rec (motive := fun k ↦ (unrank (rank w + k)).length ≤ w.length + k) ?_ ?_ k
  · simp
  · intro k ih
    have h := length_unrank_succ_le (rank w + k)
    simpa only [Nat.add_assoc] using h.trans (Nat.add_le_add_right ih 1)

/-- The enumeration word is no longer than its index. -/
theorem length_unrank_le_self (n : ℕ) : (unrank n).length ≤ n := by
  simpa using length_unrank_add [] n

/-- Truncated numerical subtraction cannot increase word length. -/
theorem length_numericSub_le (v w : List Bool) : (numericSub v w).length ≤ w.length := by
  have h := length_unrank_mono (Nat.sub_le (rank w) (rank v))
  simpa only [numericSub, unrank_rank] using h

/-- Numerical predecessor cannot increase word length. -/
theorem length_numericPred_le (w : List Bool) : (numericPred w).length ≤ w.length := by
  have h := length_unrank_mono (Nat.sub_le (rank w) 1)
  simpa only [numericPred, unrank_rank] using h

end Geb.Oitavem
