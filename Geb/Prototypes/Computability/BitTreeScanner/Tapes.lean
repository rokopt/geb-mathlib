/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Cost
public import Geb.Prototypes.Computability.BitTreeScanner.Machine

set_option doc.verso true

/-!
# The two-pass tree scanner's tapes, cell by cell

The contents of {name}`Geb.BitTreeScanner.bitTreeScanner`'s tapes at the
closed forms, cell by cell: the leaf tape outside a leaf and at each phase
of one, the ruler tape after an increment of the input's count, the count
tape after an increment and after a decrement of the pending count, and the
leaf tape after a decrement of the leaf's count. Each is the equation a
chain's absorbing step writes, stated over the counter's digit lemmas.

## Main definitions

* {lit}`Geb.BitTreeScanner.tapeBase` — a tape holding the base marker alone.
* {lit}`Geb.BitTreeScanner.raise` — the symbol a carry writes at the digit
  absorbing it.

## Main statements

* {lit}`Geb.BitTreeScanner.tapeLeaf_blank`,
  {lit}`Geb.BitTreeScanner.tapeLeaf_zeros_zero`,
  {lit}`Geb.BitTreeScanner.tapeLeaf_dead`,
  {lit}`Geb.BitTreeScanner.tapeLeaf_zeros_succ`,
  {lit}`Geb.BitTreeScanner.tapeLeaf_bits_full` — the leaf tape at each phase.
* {lit}`Geb.BitTreeScanner.tapeDigits_incB`,
  {lit}`Geb.BitTreeScanner.tapeDigits_decList` — the ruler tape after an
  increment and the leaf tape after a decrement.
* {lit}`Geb.BitTreeScanner.tapeCount_inc`, {lit}`Geb.BitTreeScanner.tapeCount_dec`
  — the count tape after an increment and after a decrement.

## Implementation notes

A cell is located by cases on the atomic inequalities bounding it rather
than on their conjunction: {lit}`omega` closing a conjunction, or reading a
negated conjunction among its hypotheses, depends on {lit}`Classical.choice`,
and the module is held to the standard axiom set. A digit above a list's
end is read through {lit}`Geb.BitTreeScanner.getD_of_length_le` rather than
mathlib's {lit}`List.getD_eq_default`, which also depends on it.

## Tags

Turing machine, tape, binary counter, carry, borrow
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

section Lists

/-- A digit read above a list's end is the default. -/
theorem getD_of_length_le {α : Type} (d : α) (l : List α) :
    ∀ n, l.length ≤ n → l.getD n d = d :=
  List.rec (motive := fun l ↦ ∀ n, l.length ≤ n → l.getD n d = d) (fun _ _ ↦ rfl)
    (fun _ l ih n hn ↦ by
      cases n with
      | zero => rw [List.length_cons] at hn; exact absurd hn (Nat.not_succ_le_zero _)
      | succ n =>
        rw [List.length_cons] at hn
        rw [List.getD_cons_succ]
        exact ih n (Nat.le_of_succ_le_succ hn)) l

/-- A cell above the base is the cell after a natural number. -/
theorem exists_eq_succ (z : ℤ) (h : 1 ≤ z) : ∃ i : ℕ, z = i + 1 := ⟨(z - 1).toNat, by omega⟩

end Lists

section Leaf

/-- A tape holding the base marker alone. -/
def tapeBase (z : ℤ) : Option (Fin 4) := if z = 0 then some 3 else none

/-- The leaf tape outside a leaf, before failure, holds the base marker
alone. -/
theorem tapeLeaf_blank (s : Scan) (hs : s.mode = .term ∨ s.mode = .done) :
    tapeLeaf s = tapeBase := by
  funext z
  rw [tapeLeaf, tapeBase]
  by_cases hz : z = 0
  · rw [ite_eq_left hz, ite_eq_left hz]
  · rw [ite_eq_right hz, ite_eq_right hz]
    rcases hs with h | h <;> rw [h]

/-- The leaf tape at the start of a leaf holds the base marker alone. -/
theorem tapeLeaf_zeros_zero (c : ℕ) : tapeLeaf ⟨.zeros, c, 0, []⟩ = tapeBase := by
  funext z
  rw [tapeLeaf, tapeBase]
  by_cases hz : z = 0
  · rw [ite_eq_left hz, ite_eq_left hz]
  · rw [ite_eq_right hz, ite_eq_right hz]
    change (if 1 ≤ z ∧ z ≤ ((0 : ℕ) : ℤ) then some 2 else none) = none
    rw [ite_eq_right (fun h ↦ by omega)]

/-- The leaf tape after failure holds the marks the zeros left. -/
theorem tapeLeaf_dead (c wd : ℕ) (d : List Bool) :
    tapeLeaf ⟨.dead, c, wd, d⟩ = tapeLeaf ⟨.zeros, c, wd, []⟩ := rfl

/-- The leaf tape after a zero of the gamma code: one more mark. -/
theorem tapeLeaf_zeros_succ (c wd : ℕ) (z : ℤ) :
    Function.update (tapeLeaf ⟨.zeros, c, wd, []⟩) (headLeaf ⟨.zeros, c, wd, []⟩) (some 2) z =
      tapeLeaf ⟨.zeros, c, wd + 1, []⟩ z := by
  rw [Function.update_apply, tapeLeaf, tapeLeaf, headLeaf_zeros]
  change (if z = (wd : ℤ) + 1 then some 2
    else if z = 0 then some 3 else if 1 ≤ z ∧ z ≤ (wd : ℤ) then some 2 else none) =
    if z = 0 then some 3 else if 1 ≤ z ∧ z ≤ ((wd + 1 : ℕ) : ℤ) then some 2 else none
  by_cases hz : z = (wd : ℤ) + 1
  · rw [ite_eq_left hz, ite_eq_right (show ¬z = 0 by omega), ite_eq_left ⟨by omega, by omega⟩]
  · rw [ite_eq_right hz]
    by_cases hz0 : z = 0
    · rw [ite_eq_left hz0, ite_eq_left hz0]
    · rw [ite_eq_right hz0, ite_eq_right hz0]
      by_cases h1 : 1 ≤ z
      · by_cases h2 : z ≤ (wd : ℤ)
        · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨h1, by omega⟩]
        · rw [ite_eq_right (fun h ↦ h2 h.2), ite_eq_right (fun h ↦ hz (by omega))]
      · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 h.1)]

/-- The closed form at complete digits: the leaf tape holds the digits over
the base marker, which the first decrement starts from. -/
theorem tapeLeaf_bits_full (c : ℕ) (d : List Bool) (z : ℤ) :
    tapeLeaf ⟨.bits, c, d.length, d⟩ z = tapeDigits d z := by
  rw [tapeLeaf, tapeDigits]
  by_cases hz : z = 0
  · rw [ite_eq_left hz, ite_eq_left hz]
  · rw [ite_eq_right hz, ite_eq_right hz]
    change (if 1 ≤ z ∧ z ≤ ((d.length - d.length : ℕ) : ℤ) then some 2
      else digitsAt ((d.length - d.length : ℕ) : ℤ) d z) = digitsAt 0 d z
    rw [Nat.sub_self, ite_eq_right (fun h ↦ by omega)]
    rfl

/-- Digits laid out above a base cell, at the cell above the base and above
it. -/
theorem digitsAt_cons (base : ℤ) (b : Bool) (d : List Bool) (z : ℤ) :
    digitsAt base (b :: d) z =
      if z = base + 1 then some (boolEmb b) else digitsAt (base + 1) d z := by
  rw [digitsAt, digitsAt, List.length_cons]
  by_cases hz : z = base + 1
  · rw [ite_eq_left hz, ite_eq_left ⟨by omega, by omega⟩, hz,
      show (base + 1 - base - 1).toNat = 0 by omega]
    rfl
  · rw [ite_eq_right hz]
    by_cases h1 : base < z
    · by_cases h2 : z ≤ base + ((d.length + 1 : ℕ) : ℤ)
      · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨by omega, by omega⟩,
          show (z - base - 1).toNat = (z - (base + 1) - 1).toNat + 1 by omega, List.getD_cons_succ]
      · rw [ite_eq_right (fun h ↦ h2 h.2), ite_eq_right (fun h ↦ h2 (by omega))]
    · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 (by omega))]

/-- The decremented leaf tape, cell by cell: ones below the borrow's length,
a zero at it, the original digits above. -/
theorem tapeDigits_decList (d : List Bool) (hd : allFalse d = false) (z : ℤ) :
    tapeDigits (decList d) z =
      if 1 ≤ z ∧ z ≤ borrowLength d then some 1
      else if z = borrowLength d + 1 then some 0 else tapeDigits d z := by
  have htz := borrowLength_lt_length d hd
  have hlen := length_decList d
  by_cases h1 : 1 ≤ z
  · obtain ⟨i, rfl⟩ := exists_eq_succ z h1
    by_cases h2 : (i : ℤ) + 1 ≤ borrowLength d
    · rw [ite_eq_left ⟨h1, h2⟩, tapeDigits_of_lt (decList d) i (by omega),
        getD_decList_of_lt d i (by omega)]
      rfl
    · rw [ite_eq_right (fun h ↦ h2 h.2)]
      by_cases h3 : (i : ℤ) + 1 = borrowLength d + 1
      · rw [ite_eq_left h3, h3,
          show (borrowLength d : ℤ) + 1 = ((borrowLength d : ℕ) : ℤ) + 1 from rfl,
          tapeDigits_of_lt (decList d) (borrowLength d) (by omega), getD_decList_borrowLength d hd]
        rfl
      · rw [ite_eq_right h3]
        by_cases hi : i < d.length
        · rw [tapeDigits_of_lt _ _ (by omega), tapeDigits_of_lt _ _ hi,
            getD_decList_of_gt d i (by omega)]
        · rw [tapeDigits_of_ge (decList d) ((i : ℤ) + 1) (by omega),
            tapeDigits_of_ge d ((i : ℤ) + 1) (by omega)]
  · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 (by omega))]
    by_cases hz0 : z = 0
    · rw [hz0, tapeDigits_zero, tapeDigits_zero]
    · rw [tapeDigits_of_neg _ _ (by omega), tapeDigits_of_neg _ _ (by omega)]

end Leaf

section Ruler

/-- The ruler tape after an increment, cell by cell: zeros below the carry's
length, a one at it, the original digits above. -/
theorem tapeDigits_incB (d : List Bool) (z : ℤ) :
    tapeDigits (incB d) z =
      if 1 ≤ z ∧ z ≤ carryLengthB d then some 0
      else if z = carryLengthB d + 1 then some 1 else tapeDigits d z := by
  have hk := carryLengthB_le_length d
  have hlen := length_incB d
  by_cases h1 : 1 ≤ z
  · obtain ⟨i, rfl⟩ := exists_eq_succ z h1
    by_cases h2 : (i : ℤ) + 1 ≤ carryLengthB d
    · rw [ite_eq_left ⟨h1, h2⟩, tapeDigits_of_lt (incB d) i (by omega),
        getD_incB_of_lt d i (by omega)]
      rfl
    · rw [ite_eq_right (fun h ↦ h2 h.2)]
      by_cases h3 : (i : ℤ) + 1 = carryLengthB d + 1
      · rw [ite_eq_left h3, h3,
          show (carryLengthB d : ℤ) + 1 = ((carryLengthB d : ℕ) : ℤ) + 1 from rfl,
          tapeDigits_of_lt (incB d) (carryLengthB d) (by omega), getD_incB_carryLengthB d]
        rfl
      · rw [ite_eq_right h3]
        by_cases hi : i < d.length
        · rw [tapeDigits_of_lt _ _ (by omega), tapeDigits_of_lt _ _ hi,
            getD_incB_of_gt d i (by omega)]
        · rw [tapeDigits_of_ge (incB d) ((i : ℤ) + 1) (by omega),
            tapeDigits_of_ge d ((i : ℤ) + 1) (by omega)]
  · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 (by omega))]
    by_cases hz0 : z = 0
    · rw [hz0, tapeDigits_zero, tapeDigits_zero]
    · rw [tapeDigits_of_neg _ _ (by omega), tapeDigits_of_neg _ _ (by omega)]

end Ruler

section Count

/-- The symbol a carry raises: a two at a one, a one at a zero or above the
top. -/
def raise (x : Option (Fin 4)) : Fin 4 := if x = some 1 then 2 else 1

/-- The count tape at the cell above the carry: blank, a zero or a one. -/
theorem tapeCount_carry (l : List Redundant.Digit) :
    tapeCount l (Redundant.carryLength l + 1) = none ∨
      tapeCount l (Redundant.carryLength l + 1) = some 0 ∨
      tapeCount l (Redundant.carryLength l + 1) = some 1 := by
  have hk := Redundant.carryLength_le_length l
  by_cases hlt : Redundant.carryLength l < l.length
  · rw [show (Redundant.carryLength l : ℤ) + 1 = ((Redundant.carryLength l : ℕ) : ℤ) + 1 from rfl,
      tapeCount_of_lt _ _ hlt]
    have := Redundant.getD_carryLength_ne_two l
    match h : l.getD (Redundant.carryLength l) 0 with
    | 0 => exact Or.inr (Or.inl rfl)
    | 1 => exact Or.inr (Or.inr rfl)
    | 2 => exact absurd h this
  · exact Or.inl (tapeCount_of_ge _ _ (by omega))

/-- The symbol the carry raises above the carry is the digit the increment
puts there. -/
theorem raise_tapeCount_carry (l : List Redundant.Digit) :
    raise (tapeCount l (Redundant.carryLength l + 1)) =
      digitEmb (if l.getD (Redundant.carryLength l) 0 = 1 then 2 else 1) := by
  have hk := Redundant.carryLength_le_length l
  by_cases hlt : Redundant.carryLength l < l.length
  · rw [show (Redundant.carryLength l : ℤ) + 1 = ((Redundant.carryLength l : ℕ) : ℤ) + 1 from rfl,
      tapeCount_of_lt _ _ hlt]
    have := Redundant.getD_carryLength_ne_two l
    match h : l.getD (Redundant.carryLength l) 0 with
    | 0 => rfl
    | 1 => rfl
    | 2 => exact absurd h this
  · rw [tapeCount_of_ge _ _ (by omega), getD_of_length_le _ _ _ (by omega)]
    rfl

/-- The count tape after an increment, cell by cell: ones below the carry's
length, the raised digit at it, the original digits above. -/
theorem tapeCount_inc (l : List Redundant.Digit) (z : ℤ) :
    tapeCount (Redundant.inc l) z =
      if 1 ≤ z ∧ z ≤ Redundant.carryLength l then some 1
      else if z = Redundant.carryLength l + 1 then
        some (digitEmb (if l.getD (Redundant.carryLength l) 0 = 1 then 2 else 1))
      else tapeCount l z := by
  have hk := Redundant.carryLength_le_length l
  have hlen := Redundant.length_inc l
  by_cases h1 : 1 ≤ z
  · obtain ⟨i, rfl⟩ := exists_eq_succ z h1
    by_cases h2 : (i : ℤ) + 1 ≤ Redundant.carryLength l
    · rw [ite_eq_left ⟨h1, h2⟩, tapeCount_of_lt (Redundant.inc l) i (by omega),
        Redundant.getD_inc_of_lt l i (by omega)]
      rfl
    · rw [ite_eq_right (fun h ↦ h2 h.2)]
      by_cases h3 : (i : ℤ) + 1 = Redundant.carryLength l + 1
      · rw [ite_eq_left h3, h3,
          show (Redundant.carryLength l : ℤ) + 1 = ((Redundant.carryLength l : ℕ) : ℤ) + 1 from rfl,
          tapeCount_of_lt (Redundant.inc l) (Redundant.carryLength l) (by omega),
          Redundant.getD_inc_carryLength l]
      · rw [ite_eq_right h3]
        by_cases hi : i < l.length
        · rw [tapeCount_of_lt _ _ (by omega), tapeCount_of_lt _ _ hi,
            Redundant.getD_inc_of_gt l i (by omega)]
        · rw [tapeCount_of_ge (Redundant.inc l) ((i : ℤ) + 1) (by omega),
            tapeCount_of_ge l ((i : ℤ) + 1) (by omega)]
  · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 (by omega))]
    by_cases hz0 : z = 0
    · rw [hz0, tapeCount_zero, tapeCount_zero]
    · rw [tapeCount_of_neg _ _ (by omega), tapeCount_of_neg _ _ (by omega)]

/-- A counter without leading zero that is not empty has a borrow shorter
than itself. -/
theorem borrowLength_lt_length_of_nlz (l : List Redundant.Digit) (hn : Redundant.nlz l = true)
    (h : l ≠ []) : Redundant.borrowLength l < l.length := by
  have hk := Redundant.borrowLength_le_length l
  have hne := getD_borrowLength_ne_zero l hn h
  by_cases heq : Redundant.borrowLength l = l.length
  · exact absurd (getD_of_length_le 0 l _ (le_of_eq heq.symm)) hne
  · omega

/-- The decremented counter's length, at a borrow absorbed by a two, by a one
that is not the top, and by a one at the top. -/
theorem length_dec_of_ne_top (l : List Redundant.Digit)
    (h : ¬(l.getD (Redundant.borrowLength l) 0 = 1 ∧ Redundant.borrowLength l + 1 = l.length)) :
    (Redundant.dec l).length = l.length := by
  rw [Redundant.length_dec, ite_eq_right h]

/-- The count tape after a decrement, cell by cell: ones below the borrow's
length; at it, a one where a two absorbed the borrow, else blank where a
one at the top did, else a zero; the original digits above. -/
theorem tapeCount_dec (l : List Redundant.Digit) (hn : Redundant.nlz l = true) (h : l ≠ [])
    (z : ℤ) :
    tapeCount (Redundant.dec l) z =
      if 1 ≤ z ∧ z ≤ Redundant.borrowLength l then some 1
      else if z = Redundant.borrowLength l + 1 then
        (if l.getD (Redundant.borrowLength l) 0 = 2 then some 1
          else if Redundant.borrowLength l + 1 = l.length then none else some 0)
      else tapeCount l z := by
  have hne := getD_borrowLength_ne_zero l hn h
  have hlt := borrowLength_lt_length_of_nlz l hn h
  have hlen := Redundant.length_dec l
  have hlow : l.length - 1 ≤ (Redundant.dec l).length := by
    rw [hlen]
    split_ifs <;> omega
  have hhigh : (Redundant.dec l).length ≤ l.length := by
    rw [hlen]
    split_ifs <;> omega
  by_cases h1 : 1 ≤ z
  · obtain ⟨i, rfl⟩ := exists_eq_succ z h1
    by_cases h2 : (i : ℤ) + 1 ≤ Redundant.borrowLength l
    · rw [ite_eq_left ⟨h1, h2⟩, tapeCount_of_lt (Redundant.dec l) i (by omega),
        Redundant.getD_dec_of_lt l i (by omega)]
      rfl
    · rw [ite_eq_right (fun h ↦ h2 h.2)]
      by_cases h3 : (i : ℤ) + 1 = Redundant.borrowLength l + 1
      · rw [ite_eq_left h3, h3]
        by_cases hd : l.getD (Redundant.borrowLength l) 0 = 2
        · rw [ite_eq_left hd,
            show (Redundant.borrowLength l : ℤ) + 1 = ((Redundant.borrowLength l : ℕ) : ℤ) + 1 from
              rfl,
            tapeCount_of_lt (Redundant.dec l) (Redundant.borrowLength l)
              (by
                rw [length_dec_of_ne_top l
                  (fun h' ↦ by rw [hd] at h'; exact absurd h'.1 (by decide))]
                exact hlt),
            Redundant.getD_dec_borrowLength l, ite_eq_left hd]
          rfl
        · rw [ite_eq_right hd]
          have hd1 : l.getD (Redundant.borrowLength l) 0 = 1 := by
            match h' : l.getD (Redundant.borrowLength l) 0 with
            | 0 => exact absurd h' hne
            | 1 => rfl
            | 2 => exact absurd h' hd
          by_cases htop : Redundant.borrowLength l + 1 = l.length
          · rw [ite_eq_left htop]
            have hlen' : (Redundant.dec l).length = l.length - 1 := by
              rw [hlen, ite_eq_left ⟨hd1, htop⟩]
            exact tapeCount_of_ge _ _ (by omega)
          · rw [ite_eq_right htop,
              show (Redundant.borrowLength l : ℤ) + 1 =
                ((Redundant.borrowLength l : ℕ) : ℤ) + 1 from rfl,
              tapeCount_of_lt (Redundant.dec l) (Redundant.borrowLength l)
                (by rw [length_dec_of_ne_top l (fun h' ↦ htop h'.2)]; exact hlt),
              Redundant.getD_dec_borrowLength l, ite_eq_right hd]
            rfl
      · rw [ite_eq_right h3]
        by_cases hi : i < (Redundant.dec l).length
        · rw [tapeCount_of_lt _ _ hi, tapeCount_of_lt _ _ (by omega),
            Redundant.getD_dec_of_gt l i (by omega)]
        · rw [tapeCount_of_ge (Redundant.dec l) ((i : ℤ) + 1) (by omega)]
          by_cases hi' : i < l.length
          · rw [tapeCount_of_lt _ _ hi']
            rw [hlen] at hi
            split_ifs at hi with hc
            · exact absurd (by omega : (i : ℤ) + 1 = Redundant.borrowLength l + 1) h3
            · exact absurd hi' hi
          · rw [tapeCount_of_ge l ((i : ℤ) + 1) (by omega)]
  · rw [ite_eq_right (fun h ↦ h1 h.1), ite_eq_right (fun h ↦ h1 (by omega))]
    by_cases hz0 : z = 0
    · rw [hz0, tapeCount_zero, tapeCount_zero]
    · rw [tapeCount_of_neg _ _ (by omega), tapeCount_of_neg _ _ (by omega)]

end Count

end Geb.BitTreeScanner
