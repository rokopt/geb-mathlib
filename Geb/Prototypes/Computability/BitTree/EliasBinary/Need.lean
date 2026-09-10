/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.Scanner
public import Mathlib.Tactic.NormNum

set_option doc.verso true

/-!
# A lower bound on the input a scanner state still requires

Every active phase of the Elias scanner commits to reading a number of further bits before
it can accept: a size field of a declared width, a length field of a declared value, and a
payload of a declared length. The bound below decreases by at most one per bit consumed, so
a state whose bound exceeds the remaining input cannot accept. A machine that abandons such
a state early decides the same language.

## Main definitions

* {lit}`need` bounds from below the bits an active state must still consume to accept.

## Main statements

* {lit}`need_step` states that one bit lowers the bound by at most one.
* {lit}`not_done_of_length_lt_need` excludes acceptance when the input is too short.

## Tags

Elias delta code, streaming recognizer, lower bound
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Geb.BitTree.Elias.Scanner

/-- A lower bound on the number of further input bits required before acceptance. -/
def need : State → ℕ
  | (.tree, n) => n
  | (.zeros z, n) => 2 ^ z + n - 2
  | (.size r v, n) => r + v * 2 ^ r + n - 2
  | (.length r v, n) => r + v * 2 ^ r + n - 2
  | (.payload r, n) => r + n - 1
  | (.done, _) => 0
  | (.dead, _) => 0

/-- Completing a leaf lowers the bound by at most one. -/
theorem need_finish (n : ℕ) : n ≤ need (finish n) + 1 := by
  unfold finish
  split
  · simp only [need]
    omega
  · simp only [need]
    omega

/-- The value carried through a size or length field at least doubles per bit. -/
theorem bit_mul_pow (b : Bool) (v r : ℕ) :
    v * 2 ^ (r + 1) ≤ Nat.bit b v * 2 ^ r := by
  rw [Nat.bit_val, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_comm v 2]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- One consumed bit lowers the bound by at most one. -/
theorem need_step (s : State) (b : Bool) (h : Active s) : need s ≤ need (step s b) + 1 := by
  rcases s with ⟨m, n⟩
  cases m with
  | tree =>
    change 0 < n at h
    cases b <;> simp only [step, need] <;> omega
  | zeros z =>
    change 0 < n at h
    cases b with
    | false =>
      simp only [step, need, Nat.pow_succ]
      omega
    | true =>
      simp only [step]
      split
      · rename_i hz
        subst hz
        have := need_finish n
        change 2 ^ 0 + n - 2 ≤ need (finish n) + 1
        simp only [Nat.pow_zero]
        omega
      · simp only [need]
        omega
  | size r v =>
    obtain ⟨hn, hr, hv⟩ := h
    simp only [step]
    split
    · rename_i he
      subst he
      simp only [need, Nat.pow_one]
      have hb : 2 * v ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
      have hp : 1 ≤ 2 ^ (Nat.bit b v - 1) := Nat.one_le_two_pow
      have hm : Nat.bit b v - 1 ≤ 1 * 2 ^ (Nat.bit b v - 1) := by
        rw [Nat.one_mul]
        exact Nat.le_of_lt (Nat.lt_two_pow_self)
      omega
    · rename_i he
      have hr2 : 2 ≤ r := by omega
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      simp only [need, Nat.add_sub_cancel]
      have := bit_mul_pow b v k
      omega
  | length r v =>
    obtain ⟨hn, hr, hv⟩ := h
    simp only [step]
    split
    · rename_i he
      subst he
      simp only [need, Nat.pow_one]
      have hb : 2 * v ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
      omega
    · rename_i he
      obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
      simp only [need, Nat.add_sub_cancel]
      have := bit_mul_pow b v k
      omega
  | payload r =>
    obtain ⟨hn, hr⟩ := h
    simp only [step]
    split
    · rename_i he
      subst he
      have := need_finish n
      change 1 + n - 1 ≤ need (finish n) + 1
      omega
    · simp only [need]
      omega
  | done => simp [step, need]
  | dead => simp [step, need]

/-- Consuming a word lowers the bound by at most its length. -/
theorem need_foldl (w : List Bool) : ∀ s, Active s →
    need s ≤ need (w.foldl step s) + w.length := by
  refine List.rec ?_ ?_ w
  · intro s _
    simp
  · intro b bs ih s hs
    have h1 := need_step s b hs
    have h2 := ih (step s b) (active_step s b hs)
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- A state requiring more bits than remain cannot accept. -/
theorem not_done_of_length_lt_need (w : List Bool) (s : State) (hs : Active s)
    (h : w.length < need s) : (w.foldl step s).1 ≠ .done := by
  intro hd
  have hf := need_foldl w s hs
  have hz : need (w.foldl step s) = 0 := by
    rcases hfold : w.foldl step s with ⟨m, k⟩
    rw [hfold] at hd
    simp only at hd
    subst hd
    rfl
  omega

end Geb.BitTree.EliasBinary
