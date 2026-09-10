/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Account
public import Geb.Prototypes.Computability.BitTree.Elias.CodeBits

set_option doc.verso true

/-!
# Amortized time of the binary-counter recognizer

Each input bit costs its read transition, at most one counter increment, and the walks
that set up or clear a header. A potential over the account pays for every walk out of
the bits that preceded it: the zero run funds the size setup and the later erasure of the
size pair, the length field funds the return of the ruler head and the erasure of the length
pair, and the ones in each counter fund its carries. The amortized cost of every bit is
bounded by a constant, so the second pass takes linear time. The first pass is bounded the
same way with its own potential.

## Main definitions

* {lit}`inc` is the time of one increment: a carry and its return.
* {lit}`macroCost` is the machine time of one complete input transition.
* {lit}`potential` is the amortization potential over accounts.
* {lit}`runCost` sums the macro costs over a prefix.
* {lit}`passOneCost` is the time of the first pass.

## Main statements

* {lit}`macroCost_potential_le` bounds each bit's amortized cost.
* {lit}`runCost_le` and {lit}`passOneCost_le` are the resulting linear bounds.

## Tags

binary counter, amortized complexity, potential, Elias delta code
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Geb.BitTree.Elias.Scanner
open Geb.BitTree.Counter (flips totalFlips increment_bits flips_add_count_increment)

/-- The time of one increment of a counter: the carry and the return. -/
def inc (x : ℕ) : ℕ := 2 * flips x.bits + 1

/-- The number of ones in a counter's binary representation. -/
def pop (x : ℕ) : ℕ := x.bits.count true

/-- An increment costs five minus twice the change in the number of ones. -/
theorem inc_add_pop (x : ℕ) : inc x + 2 * pop (x + 1) = 2 * pop x + 5 := by
  have h := flips_add_count_increment x.bits
  rw [increment_bits] at h
  unfold inc pop
  omega

/-- The zero run read so far. -/
def zerosCount : State → ℕ
  | (.zeros z, _) => z
  | _ => 0

/-- The length-field bits read so far, the position of the ruler head in that phase. -/
def lengthRuler : State → ℕ
  | (.length _ v, _) => v.size - 1
  | _ => 0

/-- Machine time for one complete input transition. -/
def macroCost (a : Account) (b : Bool) : ℕ :=
  if capped a b then 1
  else
    match a.state with
    | (.tree, _) => if b then 1 + inc a.forks else 1
    | (.zeros z, _) => if b then (if z = 0 then 1 + inc a.leaves else z + 3) else 1
    | (.size _ _, _) => 1
    | (.length r v, _) =>
      if r = 1 then inc v.size + 2 * ((v.size + 1).size - 1) + (v.size + 1) + 7
      else 1 + inc v.size
    | (.payload r, _) =>
      if r = 1 then 1 + inc (a.total - 1) + a.total.size + 1 + inc a.leaves
      else 1 + inc (a.total - r)
    | (.done, _) => 1
    | (.dead, _) => 1

/-- The amortization potential: twice the ones of every counter, and the walks funded by the
header bits read so far. -/
def potential (a : Account) : ℕ :=
  2 * pop a.forks + 2 * pop a.leaves + 2 * pop (sizeCount a.state) + 2 * pop (payloadCount a) +
    3 * sizeWidth a.state + 2 * lengthWidth a + 4 * zerosCount a.state + lengthRuler a.state

/-- Every number of ones is bounded by the binary size. -/
theorem pop_le_size (x : ℕ) : pop x ≤ x.size := by
  unfold pop
  rw [← Geb.BitTree.Counter.length_bits]
  exact List.count_le_length

/-- The binary size of a number is at most the number itself. -/
theorem size_le_self (x : ℕ) : x.size ≤ x :=
  Geb.BitTree.Counter.size_le_of_lt_pow x x Nat.lt_two_pow_self

/-- Zero has no ones. -/
theorem pop_zero : pop 0 = 0 := by simp [pop, Nat.zero_bits]

/-- The binary digits of one. -/
theorem bits_one : Nat.bits 1 = [true] := by
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, Nat.bit1_bits, Nat.zero_bits]

/-- One has a single one. -/
theorem pop_one : pop 1 = 1 := by
  unfold pop
  rw [bits_one]
  rfl

/-- A positive number has at least one one. -/
theorem pop_pos (x : ℕ) (hx : x ≠ 0) : 1 ≤ pop x := by
  unfold pop
  rw [← List.count_reverse, Geb.BitTree.Elias.reverse_bits_eq x hx, List.count_cons]
  exact Nat.le_add_left 1 _

/-- The amortized cost of every bit is bounded by a constant. -/
theorem macroCost_potential_le (n : ℕ) (a : Account) (b : Bool) (h : AccountValid n a) :
    macroCost a b + potential (accountStep a b) ≤ 13 + potential a := by
  have ha := h.active
  unfold macroCost accountStep
  split
  · rename_i hc
    simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
      lengthRuler, pop_zero]
    omega
  · rename_i hc
    rcases hs : a.state with ⟨m, k⟩
    rw [hs] at ha
    cases m with
    | tree =>
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      cases b
      · change 1 + potential ⟨(.zeros 0, k), a.forks, a.leaves, 0⟩ ≤ 13 + potential a
        simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
          lengthRuler, hs]
        omega
      · change 1 + inc a.forks + potential ⟨(.tree, k + 1), a.forks + 1, a.leaves, 0⟩ ≤
          13 + potential a
        have := inc_add_pop a.forks
        simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
          lengthRuler, hs, pop_zero]
        omega
    | zeros z =>
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      cases b with
      | false =>
        change 1 + potential ⟨(.zeros (z + 1), k), a.forks, a.leaves, 0⟩ ≤ 13 + potential a
        simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
          lengthRuler, hs, pop_zero]
        omega
      | true =>
        by_cases hz : z = 0
        · subst hz
          change 1 + inc a.leaves + potential ⟨finish k, a.forks, a.leaves + 1, 0⟩ ≤
            13 + potential a
          have := inc_add_pop a.leaves
          unfold finish
          split
          all_goals
            simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
              lengthRuler, hs, pop_zero]
            omega
        · have hstep : step (.zeros z, k) true = (.size z 1, k) := by simp [step, hz]
          have hle : leafEnds (.zeros z, k) true = false := by simp [leafEnds, hz]
          rw [hstep, hle]
          change (if z = 0 then 1 + inc a.leaves else z + 3) +
            potential ⟨(.size z 1, k), a.forks, a.leaves, 0⟩ ≤ 13 + potential a
          rw [ite_eq_right hz]
          simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
            lengthRuler, hs, Nat.size_one, pop_zero, pop_one]
          omega
    | size r v =>
      obtain ⟨hk0, hr, hv⟩ := ha
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      have hsb := size_bit b v hv
      rw [hnt]
      by_cases he : r = 1
      · subst he
        change 1 + potential ⟨(.length (Nat.bit b v - 1) 1, k), a.forks, a.leaves, 0⟩ ≤
          13 + potential a
        have hw : Nat.bit b v - 1 + 1 = Nat.bit b v := by
          have : 2 ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
          omega
        simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
          lengthRuler, hs, Nat.size_one, hw, hsb, pop_zero, pop_one]
        omega
      · have hstep : step (.size r v, k) b = (.size (r - 1) (Nat.bit b v), k) := by
          simp [step, he]
        rw [hstep]
        change 1 + potential ⟨(.size (r - 1) (Nat.bit b v), k), a.forks, a.leaves, 0⟩ ≤
          13 + potential a
        have hw : r - 1 + (Nat.bit b v).size = r + v.size := by rw [hsb]; omega
        simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
          lengthRuler, hs, hw, pop_zero, pop_one]
        omega
    | length r v =>
      obtain ⟨hk0, hr, hv⟩ := ha
      have hsb := size_bit b v hv
      have hvs := size_pos_of_pos v hv
      by_cases he : r = 1
      · subst he
        have hnt : nextTotal a b = Nat.bit b v := by simp [nextTotal, hs]
        rw [hnt]
        change inc v.size + 2 * ((v.size + 1).size - 1) + (v.size + 1) + 7 +
          potential ⟨(.payload (Nat.bit b v - 1), k), a.forks, a.leaves, Nat.bit b v⟩ ≤
          13 + potential a
        have hi := inc_add_pop v.size
        have hp := pop_pos (v.size + 1) (by omega)
        have hw : Nat.bit b v - (Nat.bit b v - 1) = 1 := by
          have : 2 ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
          omega
        have hc' : (1 + v.size).size = (v.size + 1).size := by rw [Nat.add_comm]
        have hS := size_pos_of_pos (v.size + 1) (by omega)
        simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
          lengthRuler, hs, hsb, hw, hc', pop_zero, pop_one]
        omega
      · have hstep : step (.length r v, k) b = (.length (r - 1) (Nat.bit b v), k) := by
          simp [step, he]
        have hnt : nextTotal a b = 0 := by simp [nextTotal, hs, he]
        rw [hstep, hnt]
        change (if r = 1 then _ else 1 + inc v.size) +
          potential ⟨(.length (r - 1) (Nat.bit b v), k), a.forks, a.leaves, 0⟩ ≤
          13 + potential a
        rw [ite_eq_right he]
        have hi := inc_add_pop v.size
        have hw : r - 1 + (v.size + 1) = r + v.size := by omega
        simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
          lengthRuler, hs, hsb, hw, pop_zero]
        omega
    | payload r =>
      obtain ⟨hk0, hr⟩ := ha
      have ht2 := h.total_ge r (by rw [hs])
      have hlt := h.payload_lt r (by rw [hs])
      by_cases he : r = 1
      · subst he
        have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
        rw [hnt]
        change 1 + inc (a.total - 1) + a.total.size + 1 + inc a.leaves +
          potential ⟨finish k, a.forks, a.leaves + 1, 0⟩ ≤ 13 + potential a
        have hi := inc_add_pop (a.total - 1)
        have hl := inc_add_pop a.leaves
        have hw : a.total - 1 + 1 = a.total := by omega
        have hs2 := size_le_self a.total
        rw [hw] at hi
        have hp := pop_pos a.total (by omega)
        unfold finish
        split
        all_goals
          simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
            lengthRuler, hs, pop_zero]
          omega
      · have hstep : step (.payload r, k) b = (.payload (r - 1), k) := by simp [step, he]
        have hle : leafEnds (.payload r, k) b = false := by simp [leafEnds, he]
        have hnt : nextTotal a b = a.total := by simp [nextTotal, hs, he]
        rw [hstep, hle, hnt]
        change (if r = 1 then _ else 1 + inc (a.total - r)) +
          potential ⟨(.payload (r - 1), k), a.forks, a.leaves, a.total⟩ ≤ 13 + potential a
        rw [ite_eq_right he]
        have hi := inc_add_pop (a.total - r)
        have hw : a.total - r + 1 = a.total - (r - 1) := by omega
        rw [hw] at hi
        simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
          lengthRuler, hs, pop_zero]
        omega
    | done =>
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      change 1 + potential ⟨(.dead, k), a.forks, a.leaves, 0⟩ ≤ 13 + potential a
      simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
        lengthRuler, hs, pop_zero]
      omega
    | dead =>
      have hnt : nextTotal a b = 0 := by simp [nextTotal, hs]
      rw [hnt]
      change 1 + potential ⟨(.dead, k), a.forks, a.leaves, 0⟩ ≤ 13 + potential a
      simp only [potential, sizeCount, payloadCount, sizeWidth, lengthWidth, zerosCount,
        lengthRuler, hs, pop_zero]
      omega

/-- One combined update of the account and accumulated cost. -/
def costStep (s : Account × ℕ) (b : Bool) : Account × ℕ :=
  (accountStep s.1 b, s.2 + macroCost s.1 b)

/-- The account component of the cost fold is the ordinary account fold. -/
theorem cost_foldl_fst (w : List Bool) : ∀ s c,
    (w.foldl costStep (s, c)).1 = w.foldl accountStep s :=
  List.rec (fun _ _ ↦ rfl) (fun b _ ih s c ↦ ih (accountStep s b) (c + macroCost s b)) w

/-- Sum of the macro costs over a prefix of an input of the given length. -/
def runCost (n : ℕ) (w : List Bool) : ℕ := (w.foldl costStep (initialAccount n, 0)).2

/-- Extending a prefix adds the macro cost at that prefix's account. -/
theorem runCost_append (n : ℕ) (w : List Bool) (b : Bool) :
    runCost n (w ++ [b]) = runCost n w + macroCost (account n w) b := by
  simp only [runCost, List.foldl_append, List.foldl_cons, List.foldl_nil, costStep,
    cost_foldl_fst, account]

/-- The next prefix adds exactly one macro cost. -/
theorem runCost_take_succ (n : ℕ) (w : List Bool) (t : ℕ) (h : t < w.length) :
    runCost n (w.take (t + 1)) =
      runCost n (w.take t) + macroCost (account n (w.take t)) w[t] := by
  rw [List.take_succ_eq_append_getElem h, runCost_append]

/-- The amortized bound summed over a valid fold. -/
theorem cost_foldl_le (n : ℕ) (w : List Bool) : ∀ a c, AccountValid n a →
    (w.foldl costStep (a, c)).2 + potential (w.foldl accountStep a) ≤
      c + 13 * w.length + potential a :=
  List.rec (fun _ _ _ ↦ by simp only [List.foldl_nil, List.length_nil]; omega)
    (fun b w ih a c hv ↦ by
    have hi := ih (accountStep a b) (c + macroCost a b) (accountStep_valid n a b hv)
    have hm := macroCost_potential_le n a b hv
    simp only [List.foldl_cons, List.length_cons, costStep]
    omega) w

/-- The second pass has linear macro cost. -/
theorem runCost_le (n : ℕ) (w : List Bool) :
    runCost n w + potential (account n w) ≤ 13 * w.length + potential (initialAccount n) := by
  have h := cost_foldl_le n w (initialAccount n) 0 (initialAccount_valid n)
  simpa only [runCost, account, Nat.zero_add] using h

/-- The initial potential counts the ones of both first-pass counters. -/
theorem potential_initial (n : ℕ) : potential (initialAccount n) = 2 * pop (n + 1) + 2 * pop n := by
  simp only [potential, initialAccount, sizeCount, payloadCount, sizeWidth, lengthWidth,
    zerosCount, lengthRuler, pop_zero]
  omega

/-- The time of the first pass over an input of the given length: each bit is consumed, then
the forks counter and the leaves counter are incremented. -/
def passOneCost : ℕ → ℕ :=
  Nat.rec 0 fun i cost ↦ cost + (1 + inc (i + 1) + inc i)

/-- The first pass plus its final potential is linear. -/
theorem passOneCost_add (n : ℕ) :
    passOneCost n + (2 * pop (n + 1) + 2 * pop n) = 11 * n + 2 := by
  refine Nat.rec ?_ ?_ n
  · simp [passOneCost, pop_zero, pop_one]
  · intro i ih
    have h1 := inc_add_pop (i + 1)
    have h2 := inc_add_pop i
    change passOneCost i + (1 + inc (i + 1) + inc i) +
      (2 * pop (i + 1 + 1) + 2 * pop (i + 1)) = 11 * (i + 1) + 2
    omega

/-- The first pass takes linear time. -/
theorem passOneCost_le (n : ℕ) : passOneCost n ≤ 11 * n + 2 := by
  have := passOneCost_add n
  omega

end Geb.BitTree.EliasBinary
