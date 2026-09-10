/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Machine
public import Geb.Prototypes.Computability.BitTree.Counter
public import Geb.Prototypes.Computability.TreeScanner.Steps
public import Mathlib.Tactic.FinCases

set_option doc.verso true

/-!
# One increment at any site

A carry from the tagged least significant cell flips an initial run of ones and the first
zero, moving both digit heads towards higher significance and the mismatch head by the local
comparison; the return walks the digit heads back to the tag and reads the mismatch marker.
The statements are uniform in the site, hence in the layout and the digit direction, so one
proof serves the pending, size and length pairs.

## Main statements

* {lit}`configs_carry_bits` identifies a carry from the tag with binary-list increment.
* {lit}`configs_return_done` describes the complete return.
* {lit}`configs_increment` implements one increment in twice its bit-change count plus one
  step, preserving the pair representation, every other tape, and the cells of the digit
  tapes outside the counter.
* {lit}`configs_increment_head_bounds` bounds every visited digit and mismatch head.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its statements concern
CSLib's configuration sequence, which depends on {name}`Classical.choice` through the input
symbol access.

## Tags

Turing machine, binary counter, carry, return, simulation
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (digit origin flipped mismatchMove mismatchCount flipAt bitsAt
  digit_flipped origin_flipped mismatchCount_flip_left mismatchCount_flip_right
  mismatchCount_le)
open Geb.BitTree.Counter (flips increment)
open Geb.TreeScanner (step_of_state)

/-! ## Binary size after an increment -/

/-- The digits of one less than a power of two are a run of ones. -/
theorem bits_pow_sub_one (k : ℕ) : (2 ^ k - 1).bits = List.replicate k true := by
  refine Nat.rec ?_ ?_ k
  · simp [Nat.zero_bits]
  · intro k ih
    have h : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
      have := Nat.one_le_two_pow (n := k)
      rw [Nat.pow_succ]
      omega
    rw [h, Nat.bit1_bits, ih, List.replicate_succ]

/-- The bit changes of an increment together with the old size determine the new size. -/
theorem size_succ_eq_max (a : ℕ) : (a + 1).size = max (flips a.bits) a.size := by
  apply Nat.le_antisymm
  · by_cases h : (a + 1).size ≤ a.size
    · exact h.trans (Nat.le_max_right _ _)
    · have hlt : 2 ^ a.size ≤ a + 1 := Nat.lt_size.mp (by omega)
      have hself := Nat.lt_size_self a
      have he : a = 2 ^ a.size - 1 := by omega
      have hbits : a.bits = List.replicate a.size true := by
        conv_lhs => rw [he]
        exact bits_pow_sub_one a.size
      have hf : flips a.bits = a.size + 1 := by
        rw [hbits, ← List.append_nil (List.replicate _ true),
          Geb.BitTree.Counter.flips_replicate_true_append]
        rfl
      have hs : (a + 1).size ≤ a.size + 1 := by
        rw [Nat.size_le, Nat.pow_succ]
        omega
      rw [hf]
      exact hs.trans (Nat.le_max_left _ _)
  · exact Nat.max_le.mpr ⟨Geb.BitTree.Counter.flips_bits_le_succ_size a,
      Geb.BitTree.Counter.size_mono (Nat.le_succ a)⟩

/-! ## Sites -/

/-- Every site's layout has distinct tapes and a nonzero direction. -/
theorem siteLayout_proper (k : Fin 6) : (siteLayout k).Proper := by
  fin_cases k <;> exact ⟨by decide, by decide, by decide, by decide⟩

/-- The tape a site increments. -/
def siteSelected (k : Fin 6) : Fin 9 :=
  if siteSel k then (siteLayout k).second else (siteLayout k).first

/-- The digit tape a site leaves unchanged. -/
def siteOther (k : Fin 6) : Fin 9 :=
  if siteSel k then (siteLayout k).first else (siteLayout k).second

/-- The selected tape is a digit tape of the layout. -/
theorem siteSelected_mem (k : Fin 6) :
    siteSelected k = (siteLayout k).first ∨ siteSelected k = (siteLayout k).second := by
  unfold siteSelected
  split <;> simp

/-- The selected tape differs from the mismatch tape. -/
theorem siteSelected_ne_mism (k : Fin 6) : siteSelected k ≠ (siteLayout k).mism := by
  have h := siteLayout_proper k
  unfold siteSelected
  split
  · exact h.second_ne_mism
  · exact h.first_ne_mism

/-- The two digit tapes of a site differ. -/
theorem siteSelected_ne_other (k : Fin 6) : siteSelected k ≠ siteOther k := by
  have h := siteLayout_proper k
  unfold siteSelected siteOther
  split
  · exact h.first_ne_second.symm
  · exact h.first_ne_second

/-- The other digit tape differs from the mismatch tape. -/
theorem siteOther_ne_mism (k : Fin 6) : siteOther k ≠ (siteLayout k).mism := by
  have h := siteLayout_proper k
  unfold siteOther
  split
  · exact h.first_ne_mism
  · exact h.second_ne_mism

/-- The other tape is a digit tape of the layout. -/
theorem siteOther_mem (k : Fin 6) :
    siteOther k = (siteLayout k).first ∨ siteOther k = (siteLayout k).second := by
  unfold siteOther
  split <;> simp

/-! ## Single carry transitions -/

section CarryStep

variable {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (k : Fin 6)

/-- A carry does not move the input head. -/
theorem carry_inputMove (work : Fin 9 → Option (Fin 4)) :
    (carry (siteLayout k) (siteSel k) (stCarry k) (stReturn k) work).inputMove = 0 := rfl

/-- The work action of a carry on the selected tape. -/
theorem carry_action_selected (work : Fin 9 → Option (Fin 4)) :
    (carry (siteLayout k) (siteSel k) (stCarry k) (stReturn k) work).workActions
      (siteSelected k) = (some (some (flipped (work (siteSelected k)))), (siteLayout k).dir) := by
  have hm := siteSelected_ne_mism k
  have hmem := siteSelected_mem k
  unfold siteSelected at hm hmem ⊢
  unfold carry
  dsimp only
  rw [ite_eq_right hm, ite_eq_left hmem, ite_eq_left rfl]

/-- The work action of a carry on the other digit tape. -/
theorem carry_action_other (work : Fin 9 → Option (Fin 4)) :
    (carry (siteLayout k) (siteSel k) (stCarry k) (stReturn k) work).workActions
      (siteOther k) = (none, (siteLayout k).dir) := by
  have hm := siteOther_ne_mism k
  have hmem := siteOther_mem k
  have hne := siteSelected_ne_other k
  unfold siteSelected at hne
  unfold siteOther at hm hmem hne ⊢
  unfold carry
  dsimp only
  rw [ite_eq_right hm, ite_eq_left hmem, ite_eq_right (fun h ↦ hne h.symm)]

/-- The work action of a carry on the mismatch tape. -/
theorem carry_action_mism (work : Fin 9 → Option (Fin 4)) :
    (carry (siteLayout k) (siteSel k) (stCarry k) (stReturn k) work).workActions
      (siteLayout k).mism =
      (none, mismatchMove (work (siteLayout k).first) (work (siteLayout k).second)) := by
  simp [carry]

/-- The work action of a carry on any tape outside its layout. -/
theorem carry_action_untouched (work : Fin 9 → Option (Fin 4)) (i : Fin 9)
    (h1 : i ≠ (siteLayout k).first) (h2 : i ≠ (siteLayout k).second)
    (h3 : i ≠ (siteLayout k).mism) :
    (carry (siteLayout k) (siteSel k) (stCarry k) (stReturn k) work).workActions i =
      (none, 0) := by
  simp [carry, h1, h2, h3]

/-- A carry flips exactly the selected tape's current digit. -/
theorem step_carry_digits (lsb : ℤ) (p : ℕ) (hq : cfg.state = some (stCarry k))
    (hp : cfg.workTapePos (siteSelected k) = cell lsb (siteLayout k).dir p) :
    digitsFrom (machine.step cfg) (siteSelected k) lsb (siteLayout k).dir =
      Function.update (digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir) p
        (!(digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir p)) := by
  funext j
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only [digitsFrom]
  rw [carry_action_selected]
  dsimp only
  simp only [Cfg.workTapeSymbols, hp]
  by_cases h : j = p
  · subst j
    rw [Function.update_self, Function.update_self]
    exact digit_flipped _
  · have hz : cell lsb (siteLayout k).dir j ≠ cell lsb (siteLayout k).dir p :=
      fun he ↦ h (cell_injective _ _ (siteLayout_proper k).dir_ne_zero _ _ he)
    rw [Function.update_of_ne hz, Function.update_of_ne h]
    rfl

/-- The selected tape changes only at its current cell. -/
theorem step_carry_selected_cells (hq : cfg.state = some (stCarry k)) (z : ℤ)
    (hz : z ≠ cfg.workTapePos (siteSelected k)) :
    (machine.step cfg).workTapes (siteSelected k) z = cfg.workTapes (siteSelected k) z := by
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only
  rw [carry_action_selected]
  dsimp only
  exact Function.update_of_ne hz _ _

/-- The selected tape's current cell is written. -/
theorem step_carry_selected_written (hq : cfg.state = some (stCarry k)) :
    (machine.step cfg).workTapes (siteSelected k) (cfg.workTapePos (siteSelected k)) ≠
      none := by
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only
  rw [carry_action_selected]
  dsimp only
  simp

/-- The other digit tape is unchanged by a carry. -/
theorem step_carry_other (hq : cfg.state = some (stCarry k)) :
    (machine.step cfg).workTapes (siteOther k) = cfg.workTapes (siteOther k) := by
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only
  rw [carry_action_other]

/-- The other digit tape reads the same digits after a carry. -/
theorem step_carry_other_digits (lsb : ℤ) (hq : cfg.state = some (stCarry k)) :
    digitsFrom (machine.step cfg) (siteOther k) lsb (siteLayout k).dir =
      digitsFrom cfg (siteOther k) lsb (siteLayout k).dir := by
  funext j
  simp only [digitsFrom, step_carry_other cfg k hq]

/-- The mismatch tape is unchanged by a carry. -/
theorem step_carry_marker (hq : cfg.state = some (stCarry k)) :
    (machine.step cfg).workTapes (siteLayout k).mism = cfg.workTapes (siteLayout k).mism := by
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only
  rw [carry_action_mism]

/-- Tapes outside the layout are unchanged by a carry. -/
theorem step_carry_untouched (hq : cfg.state = some (stCarry k)) (i : Fin 9)
    (h1 : i ≠ (siteLayout k).first) (h2 : i ≠ (siteLayout k).second)
    (h3 : i ≠ (siteLayout k).mism) :
    (machine.step cfg).workTapes i = cfg.workTapes i ∧
      (machine.step cfg).workTapePos i = cfg.workTapePos i := by
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only
  rw [carry_action_untouched _ _ _ h1 h2 h3]
  simp

/-- Both digit heads move one cell towards higher significance. -/
theorem step_carry_pos (hq : cfg.state = some (stCarry k)) :
    (machine.step cfg).workTapePos (siteSelected k) =
        cfg.workTapePos (siteSelected k) + (siteLayout k).dir ∧
      (machine.step cfg).workTapePos (siteOther k) =
        cfg.workTapePos (siteOther k) + (siteLayout k).dir := by
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only
  rw [carry_action_selected, carry_action_other]
  exact ⟨rfl, rfl⟩

/-- The mismatch head moves by the local digit comparison. -/
theorem step_carry_mismatchPos (hq : cfg.state = some (stCarry k)) :
    (machine.step cfg).workTapePos (siteLayout k).mism = cfg.workTapePos (siteLayout k).mism +
      (mismatchMove (cfg.workTapeSymbols (siteLayout k).first)
        (cfg.workTapeSymbols (siteLayout k).second)).cast := by
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only
  rw [carry_action_mism]

/-- Carry propagation does not move the input head. -/
theorem step_carry_inputPos (hq : cfg.state = some (stCarry k)) :
    (machine.step cfg).inputPos = cfg.inputPos := by
  rw [step_of_state _ _ _ hq, tr_carry]
  dsimp only
  rw [carry_inputMove]
  exact moveInputPos_zero _

/-- A carry continues through ones and ends at the first zero. -/
theorem step_carry_state (hq : cfg.state = some (stCarry k)) :
    (machine.step cfg).state =
      some (if digit (cfg.workTapeSymbols (siteSelected k)) then stCarry k else stReturn k) := by
  rw [step_of_state _ _ _ hq, tr_carry]
  rfl

/-- Carry propagation emits no output symbols. -/
theorem outputSymbol_carry (hq : cfg.state = some (stCarry k)) :
    machine.outputSymbol cfg = none := by
  simp only [outputSymbol, hq, tr_carry]
  rfl

/-- A carry preserves every origin tag on the first tape. -/
theorem step_carry_origin (hq : cfg.state = some (stCarry k)) (z : ℤ) :
    origin ((machine.step cfg).workTapes (siteLayout k).first z) =
      origin (cfg.workTapes (siteLayout k).first z) := by
  rcases hsel : siteSel k with _ | _
  · have hs : siteSelected k = (siteLayout k).first := by simp [siteSelected, hsel]
    by_cases hz : z = cfg.workTapePos (siteSelected k)
    · subst z
      rw [← hs, step_of_state _ _ _ hq, tr_carry]
      dsimp only
      rw [carry_action_selected]
      dsimp only
      rw [Function.update_self]
      exact origin_flipped _
    · rw [← hs, step_carry_selected_cells cfg k hq z hz]
  · have hs : siteOther k = (siteLayout k).first := by simp [siteOther, hsel]
    rw [← hs, step_carry_other cfg k hq]

/-- One carry transition preserves the mismatch-count invariant. -/
theorem step_carry_mismatch (lsb : ℤ) (width p : ℕ) (hq : cfg.state = some (stCarry k))
    (hp0 : cfg.workTapePos (siteLayout k).first = cell lsb (siteLayout k).dir p)
    (hp1 : cfg.workTapePos (siteLayout k).second = cell lsb (siteLayout k).dir p) (hp : p < width)
    (hm : cfg.workTapePos (siteLayout k).mism = (mismatchCount width
      (digitsFrom cfg (siteLayout k).first lsb (siteLayout k).dir)
      (digitsFrom cfg (siteLayout k).second lsb (siteLayout k).dir) : ℤ)) :
    (machine.step cfg).workTapePos (siteLayout k).mism = (mismatchCount width
      (digitsFrom (machine.step cfg) (siteLayout k).first lsb (siteLayout k).dir)
      (digitsFrom (machine.step cfg) (siteLayout k).second lsb (siteLayout k).dir) : ℤ) := by
  rw [step_carry_mismatchPos cfg k hq, hm]
  rcases hsel : siteSel k with _ | _
  · have hs : siteSelected k = (siteLayout k).first := by simp [siteSelected, hsel]
    have ho : siteOther k = (siteLayout k).second := by simp [siteOther, hsel]
    have hd := step_carry_digits cfg k lsb p hq (by rw [hs]; exact hp0)
    have he := step_carry_other_digits cfg k lsb hq
    rw [hs] at hd
    rw [ho] at he
    rw [hd, he, ← flipAt, mismatchCount_flip_left width p _ _ hp]
    congr 1
    simp only [mismatchMove, Cfg.workTapeSymbols, hp0, hp1, digitsFrom, beq_iff_eq]
    split_ifs <;> simp_all
  · have hs : siteSelected k = (siteLayout k).second := by simp [siteSelected, hsel]
    have ho : siteOther k = (siteLayout k).first := by simp [siteOther, hsel]
    have hd := step_carry_digits cfg k lsb p hq (by rw [hs]; exact hp1)
    have he := step_carry_other_digits cfg k lsb hq
    rw [hs] at hd
    rw [ho] at he
    rw [hd, he, ← flipAt, mismatchCount_flip_right width p _ _ hp]
    congr 1
    simp only [mismatchMove, Cfg.workTapeSymbols, hp0, hp1, digitsFrom, beq_iff_eq]
    split_ifs <;> simp_all

end CarryStep

/-! ## Carry propagation -/

section Carry

variable {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (k : Fin 6) (lsb : ℤ)

/-- The heads of a carry at elapsed time {lit}`t` from significance {lit}`p`. -/
theorem carry_head_eq (p t : ℕ) :
    cell lsb (siteLayout k).dir p + ((siteLayout k).dir : ℤ) * t =
      cell lsb (siteLayout k).dir (p + t) := by
  simp only [cell, Nat.cast_add, Int.mul_add, Int.add_assoc]

/-- Resetting an initial sequence of ones preserves the carry state and advances both heads. -/
theorem configs_carry_prefix (p n : ℕ)
    (hq : cfg.state = some (stCarry k))
    (hp0 : cfg.workTapePos (siteLayout k).first = cell lsb (siteLayout k).dir p)
    (hp1 : cfg.workTapePos (siteLayout k).second = cell lsb (siteLayout k).dir p)
    (hones : ∀ j < n, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir (p + j) = true)
    (t : ℕ) (ht : t ≤ n) :
    let now := machine.configs cfg t
    now.state = some (stCarry k) ∧
    now.workTapePos (siteLayout k).first = cell lsb (siteLayout k).dir (p + t) ∧
    now.workTapePos (siteLayout k).second = cell lsb (siteLayout k).dir (p + t) ∧
    now.inputPos = cfg.inputPos ∧
    digitsFrom now (siteSelected k) lsb (siteLayout k).dir =
      (fun j ↦ if p ≤ j ∧ j < p + t then false
        else digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir j) ∧
    now.workTapes (siteOther k) = cfg.workTapes (siteOther k) ∧
    now.workTapes (siteLayout k).mism = cfg.workTapes (siteLayout k).mism ∧
    (∀ z, (∀ j, j < t → z ≠ cell lsb (siteLayout k).dir (p + j)) →
      now.workTapes (siteSelected k) z = cfg.workTapes (siteSelected k) z) ∧
    (∀ j, j < t → now.workTapes (siteSelected k) (cell lsb (siteLayout k).dir (p + j)) ≠ none) ∧
    (∀ z, origin (now.workTapes (siteLayout k).first z) =
      origin (cfg.workTapes (siteLayout k).first z)) ∧
    (∀ i, i ≠ (siteLayout k).first → i ≠ (siteLayout k).second → i ≠ (siteLayout k).mism →
      now.workTapes i = cfg.workTapes i ∧ now.workTapePos i = cfg.workTapePos i) := by
  revert ht
  refine Nat.rec ?_ ?_ t
  · intro _
    refine ⟨hq, by simpa using hp0, by simpa using hp1, rfl, ?_, rfl, rfl, fun _ _ ↦ rfl,
      fun j hj ↦ (Nat.not_lt_zero j hj).elim, fun _ ↦ rfl, fun _ _ _ _ ↦ ⟨rfl, rfl⟩⟩
    funext j
    have hj : ¬(p ≤ j ∧ j < p + 0) := by omega
    simp only [configs_zero, hj, ↓reduceIte]
  · intro t ih ht
    obtain ⟨hstate, hpos0, hpos1, hin, hselected, hother, hmark, hcells, hwritten, horig,
      hunt⟩ := ih (by omega)
    set now := machine.configs cfg t with hnow
    have hpsel : now.workTapePos (siteSelected k) = cell lsb (siteLayout k).dir (p + t) := by
      rcases siteSelected_mem k with hs | hs <;> rw [hs] <;> assumption
    have hpoth : now.workTapePos (siteOther k) = cell lsb (siteLayout k).dir (p + t) := by
      rcases siteOther_mem k with hs | hs <;> rw [hs] <;> assumption
    have hone := hones t (by omega)
    have hd : digit (now.workTapeSymbols (siteSelected k)) = true := by
      change digit (now.workTapes (siteSelected k) (now.workTapePos (siteSelected k))) = true
      rw [hpsel]
      change digitsFrom now (siteSelected k) lsb (siteLayout k).dir (p + t) = true
      rw [hselected]
      simp only [Nat.lt_irrefl, and_false, ↓reduceIte]
      exact hone
    have hstep := step_carry_pos now k hstate
    rw [configs_succ_eq_step']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [step_carry_state now k hstate, hd]
      rfl
    · change _ = cell lsb (siteLayout k).dir (p + (t + 1))
      rcases siteSelected_mem k with hs | hs
      · rw [← hs, hstep.1, hpsel, ← cell_succ, Nat.add_assoc]
      · have ho : siteOther k = (siteLayout k).first := by
          rcases siteOther_mem k with h | h
          · exact h
          · exact (siteSelected_ne_other k (hs.trans h.symm)).elim
        rw [← ho, hstep.2, hpoth, ← cell_succ, Nat.add_assoc]
    · change _ = cell lsb (siteLayout k).dir (p + (t + 1))
      rcases siteSelected_mem k with hs | hs
      · have ho : siteOther k = (siteLayout k).second := by
          rcases siteOther_mem k with h | h
          · exact (siteSelected_ne_other k (hs.trans h.symm)).elim
          · exact h
        rw [← ho, hstep.2, hpoth, ← cell_succ, Nat.add_assoc]
      · rw [← hs, hstep.1, hpsel, ← cell_succ, Nat.add_assoc]
    · rw [step_carry_inputPos now k hstate, hin]
    · rw [step_carry_digits now k lsb (p + t) hstate hpsel, hselected]
      funext j
      by_cases hj : j = p + t
      · subst j
        simp [Function.update_self, hone]
      · rw [Function.update_of_ne hj]
        have he : (p ≤ j ∧ j < p + t) ↔ (p ≤ j ∧ j < p + (t + 1)) := by omega
        simp only [he]
    · rw [step_carry_other now k hstate, hother]
    · rw [step_carry_marker now k hstate, hmark]
    · intro z hz
      rw [step_carry_selected_cells now k hstate z (by
        rw [hpsel]
        exact hz t (Nat.lt_succ_self t))]
      exact hcells z (fun j hj ↦ hz j (by omega))
    · intro j hj
      by_cases hjt : j = t
      · subst j
        rw [← hpsel]
        exact step_carry_selected_written now k hstate
      · rw [step_carry_selected_cells now k hstate _ (by
          rw [hpsel]
          intro he
          have := cell_injective _ _ (siteLayout_proper k).dir_ne_zero _ _ he
          exact hjt (by omega))]
        exact hwritten j (by omega)
    · intro z
      rw [step_carry_origin now k hstate, horig]
    · intro i h1 h2 h3
      obtain ⟨ht1, ht2⟩ := step_carry_untouched now k hstate i h1 h2 h3
      obtain ⟨hu1, hu2⟩ := hunt i h1 h2 h3
      exact ⟨ht1.trans hu1, ht2.trans hu2⟩

/-- Carry propagation emits nothing before its terminal step. -/
theorem outputString_carry_prefix (p n : ℕ)
    (hq : cfg.state = some (stCarry k))
    (hp0 : cfg.workTapePos (siteLayout k).first = cell lsb (siteLayout k).dir p)
    (hp1 : cfg.workTapePos (siteLayout k).second = cell lsb (siteLayout k).dir p)
    (hones : ∀ j < n, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir (p + j) = true) :
    machine.outputString cfg (n + 1) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro t ht
  have hq' := (configs_carry_prefix cfg k lsb p n hq hp0 hp1 hones t
    (by have h := List.mem_range.mp ht; omega)).1
  rw [outputSymbol_carry _ k hq']
  rfl

/-- The complete carry from the tag: the digit list is incremented, every cell below the
bit-change count is written, and nothing else changes. -/
theorem configs_carry_bits (bs : List Bool)
    (hq : cfg.state = some (stCarry k))
    (hp0 : cfg.workTapePos (siteLayout k).first = lsb)
    (hp1 : cfg.workTapePos (siteLayout k).second = lsb)
    (hbits : ∀ j, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir j = bs[j]?.getD false) :
    let f := flips bs
    let now := machine.configs cfg f
    now.state = some (stReturn k) ∧
    now.workTapePos (siteLayout k).first = cell lsb (siteLayout k).dir f ∧
    now.workTapePos (siteLayout k).second = cell lsb (siteLayout k).dir f ∧
    now.inputPos = cfg.inputPos ∧
    digitsFrom now (siteSelected k) lsb (siteLayout k).dir =
      (fun j ↦ (increment bs)[j]?.getD false) ∧
    now.workTapes (siteOther k) = cfg.workTapes (siteOther k) ∧
    now.workTapes (siteLayout k).mism = cfg.workTapes (siteLayout k).mism ∧
    (∀ z, (∀ j, j < f → z ≠ cell lsb (siteLayout k).dir j) →
      now.workTapes (siteSelected k) z = cfg.workTapes (siteSelected k) z) ∧
    (∀ j, j < f → now.workTapes (siteSelected k) (cell lsb (siteLayout k).dir j) ≠ none) ∧
    (∀ z, origin (now.workTapes (siteLayout k).first z) =
      origin (cfg.workTapes (siteLayout k).first z)) ∧
    (∀ i, i ≠ (siteLayout k).first → i ≠ (siteLayout k).second → i ≠ (siteLayout k).mism →
      now.workTapes i = cfg.workTapes i ∧ now.workTapePos i = cfg.workTapePos i) ∧
    machine.outputString cfg f = [] := by
  have hf := Geb.BitTree.Counter.flips_pos bs
  have he : flips bs - 1 + 1 = flips bs := by omega
  have hones : ∀ j < flips bs - 1,
      digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir (0 + j) = true := by
    intro j hj
    rw [Nat.zero_add, hbits]
    exact Geb.BitTree.Counter.getD_eq_true_of_lt_flips bs j (by omega)
  have hzero : digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir (0 + (flips bs - 1)) =
      false := by
    rw [Nat.zero_add, hbits]
    exact Geb.BitTree.Counter.getD_last_flip bs
  have hp0' : cfg.workTapePos (siteLayout k).first = cell lsb (siteLayout k).dir 0 := by
    rw [hp0, cell_zero]
  have hp1' : cfg.workTapePos (siteLayout k).second = cell lsb (siteLayout k).dir 0 := by
    rw [hp1, cell_zero]
  obtain ⟨hstate, hpos0, hpos1, hin, hselected, hother, hmark, hcells, hwritten, horig, hunt⟩ :=
    configs_carry_prefix cfg k lsb 0 (flips bs - 1) hq hp0' hp1' hones (flips bs - 1)
      (Nat.le_refl _)
  set now := machine.configs cfg (flips bs - 1) with hnow
  have hpsel : now.workTapePos (siteSelected k) = cell lsb (siteLayout k).dir (flips bs - 1) := by
    rcases siteSelected_mem k with hs | hs
    · rw [hs]
      simpa using hpos0
    · rw [hs]
      simpa using hpos1
  have hpoth : now.workTapePos (siteOther k) = cell lsb (siteLayout k).dir (flips bs - 1) := by
    rcases siteOther_mem k with hs | hs
    · rw [hs]
      simpa using hpos0
    · rw [hs]
      simpa using hpos1
  have hd : digit (now.workTapeSymbols (siteSelected k)) = false := by
    change digit (now.workTapes (siteSelected k) (now.workTapePos (siteSelected k))) = false
    rw [hpsel]
    change digitsFrom now (siteSelected k) lsb (siteLayout k).dir (flips bs - 1) = false
    rw [hselected]
    simpa using hzero
  have hstep := step_carry_pos now k hstate
  have hout := outputString_carry_prefix cfg k lsb 0 (flips bs - 1) hq hp0' hp1' hones
  rw [he] at hout
  simp only [Nat.zero_add] at hpos0 hpos1 hselected hcells hwritten
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hout⟩ <;>
    (try rw [show flips bs = flips bs - 1 + 1 from he.symm, configs_succ_eq_step'])
  · rw [step_carry_state now k hstate, hd]
    rfl
  · rcases siteSelected_mem k with hs | hs
    · rw [← hs, hstep.1, hpsel, ← cell_succ]
    · have ho : siteOther k = (siteLayout k).first := by
        rcases siteOther_mem k with h | h
        · exact h
        · exact (siteSelected_ne_other k (hs.trans h.symm)).elim
      rw [← ho, hstep.2, hpoth, ← cell_succ]
  · rcases siteSelected_mem k with hs | hs
    · have ho : siteOther k = (siteLayout k).second := by
        rcases siteOther_mem k with h | h
        · exact (siteSelected_ne_other k (hs.trans h.symm)).elim
        · exact h
      rw [← ho, hstep.2, hpoth, ← cell_succ]
    · rw [← hs, hstep.1, hpsel, ← cell_succ]
  · rw [step_carry_inputPos now k hstate, hin]
  · rw [step_carry_digits now k lsb (flips bs - 1) hstate hpsel, hselected]
    funext j
    rw [Geb.BitTree.Counter.getD_increment]
    by_cases hj : j = flips bs - 1
    · subst j
      simp only [Function.update_self, Nat.lt_irrefl, and_false, ↓reduceIte, Nat.zero_le,
        true_and]
      rw [show flips bs - 1 + 1 = flips bs from he, ite_eq_right (Nat.lt_irrefl _), ite_eq_left rfl]
      simpa using hzero
    · rw [Function.update_of_ne hj]
      rw [hbits]
      split_ifs <;> first | rfl | omega
  · rw [step_carry_other now k hstate, hother]
  · rw [step_carry_marker now k hstate, hmark]
  · intro z hz
    rw [step_carry_selected_cells now k hstate z (by
      rw [hpsel]
      exact hz (flips bs - 1) (by omega))]
    exact hcells z (fun j hj ↦ hz j (by omega))
  · intro j hj
    by_cases hjt : j = flips bs - 1
    · subst j
      rw [← hpsel]
      exact step_carry_selected_written now k hstate
    · rw [step_carry_selected_cells now k hstate _ (by
        rw [hpsel]
        intro he'
        exact hjt (cell_injective _ _ (siteLayout_proper k).dir_ne_zero _ _ he'))]
      exact hwritten j (by omega)
  · intro z
    rw [step_carry_origin now k hstate, horig]
  · intro i h1 h2 h3
    obtain ⟨ht1, ht2⟩ := step_carry_untouched now k hstate i h1 h2 h3
    obtain ⟨hu1, hu2⟩ := hunt i h1 h2 h3
    exact ⟨ht1.trans hu1, ht2.trans hu2⟩

/-- The digit heads at every time of a carry from the tag, including its terminal state. -/
theorem configs_carry_bits_pos (bs : List Bool)
    (hq : cfg.state = some (stCarry k))
    (hp0 : cfg.workTapePos (siteLayout k).first = lsb)
    (hp1 : cfg.workTapePos (siteLayout k).second = lsb)
    (hbits : ∀ j, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir j = bs[j]?.getD false)
    (t : ℕ) (ht : t ≤ flips bs) :
    (machine.configs cfg t).workTapePos (siteLayout k).first = cell lsb (siteLayout k).dir t ∧
    (machine.configs cfg t).workTapePos (siteLayout k).second = cell lsb (siteLayout k).dir t ∧
    (∀ i, i ≠ (siteLayout k).first → i ≠ (siteLayout k).second → i ≠ (siteLayout k).mism →
      (machine.configs cfg t).workTapePos i = cfg.workTapePos i) := by
  by_cases he : t = flips bs
  · subst t
    have h := configs_carry_bits cfg k lsb bs hq hp0 hp1 hbits
    exact ⟨h.2.1, h.2.2.1, fun i h1 h2 h3 ↦ (h.2.2.2.2.2.2.2.2.2.2.1 i h1 h2 h3).2⟩
  · have hones : ∀ j < flips bs - 1,
        digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir (0 + j) = true := by
      intro j hj
      rw [Nat.zero_add, hbits]
      exact Geb.BitTree.Counter.getD_eq_true_of_lt_flips bs j (by omega)
    have h := configs_carry_prefix cfg k lsb 0 (flips bs - 1) hq (by rw [hp0, cell_zero])
      (by rw [hp1, cell_zero]) hones t (by omega)
    exact ⟨by simpa using h.2.1, by simpa using h.2.2.1,
      fun i h1 h2 h3 ↦ (h.2.2.2.2.2.2.2.2.2.2 i h1 h2 h3).2⟩

/-- The mismatch head at every time of a carry from the tag. -/
theorem configs_carry_bits_mismatch (bs : List Bool) (width : ℕ)
    (hq : cfg.state = some (stCarry k))
    (hp0 : cfg.workTapePos (siteLayout k).first = lsb)
    (hp1 : cfg.workTapePos (siteLayout k).second = lsb)
    (hbits : ∀ j, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir j = bs[j]?.getD false)
    (hw : flips bs ≤ width)
    (hm : cfg.workTapePos (siteLayout k).mism = (mismatchCount width
      (digitsFrom cfg (siteLayout k).first lsb (siteLayout k).dir)
      (digitsFrom cfg (siteLayout k).second lsb (siteLayout k).dir) : ℤ))
    (t : ℕ) (ht : t ≤ flips bs) :
    (machine.configs cfg t).workTapePos (siteLayout k).mism = (mismatchCount width
      (digitsFrom (machine.configs cfg t) (siteLayout k).first lsb (siteLayout k).dir)
      (digitsFrom (machine.configs cfg t) (siteLayout k).second lsb (siteLayout k).dir) : ℤ) := by
  revert ht
  refine Nat.rec ?_ ?_ t
  · intro _
    simpa using hm
  · intro t ih ht
    have hprev := ih (by omega)
    have hones : ∀ j < flips bs - 1,
        digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir (0 + j) = true := by
      intro j hj
      rw [Nat.zero_add, hbits]
      exact Geb.BitTree.Counter.getD_eq_true_of_lt_flips bs j (by omega)
    have h := configs_carry_prefix cfg k lsb 0 (flips bs - 1) hq (by rw [hp0, cell_zero])
      (by rw [hp1, cell_zero]) hones t (by omega)
    rw [configs_succ_eq_step']
    exact step_carry_mismatch _ k lsb width t h.1 (by simpa using h.2.1) (by simpa using h.2.2.1)
      (by omega) hprev

end Carry

/-! ## The return -/

section Return

variable {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (k : Fin 6) (lsb : ℤ)

/-- A return configuration with both digit heads at the given significance. -/
def returnCfg (p : ℕ) : Cfg 9 (Fin 4) Control input where
  state := some (stReturn k)
  inputPos := cfg.inputPos
  workTapes := cfg.workTapes
  workTapePos i := if i = (siteLayout k).first ∨ i = (siteLayout k).second
    then cell lsb (siteLayout k).dir p else cfg.workTapePos i

/-- The configuration reached when the return's final state change has completed. -/
def returnedCfg : Cfg 9 (Fin 4) Control input :=
  { returnCfg cfg k lsb 0 with
    state := some (if cfg.workTapes (siteLayout k).mism (cfg.workTapePos (siteLayout k).mism)
      == some 0 then siteZero k else siteNext k) }

/-- A configuration in the return state with aligned digit heads is its own return form. -/
theorem returnCfg_self (p : ℕ) (hq : cfg.state = some (stReturn k))
    (hp0 : cfg.workTapePos (siteLayout k).first = cell lsb (siteLayout k).dir p)
    (hp1 : cfg.workTapePos (siteLayout k).second = cell lsb (siteLayout k).dir p) :
    returnCfg cfg k lsb p = cfg := by
  refine Cfg.ext hq.symm rfl rfl ?_
  funext i
  simp only [returnCfg]
  split_ifs with h
  · rcases h with rfl | rfl
    · exact hp0.symm
    · exact hp1.symm
  · rfl

/-- Away from the tag, the return transition moves both digit heads back. -/
theorem tr_return_pos (p : ℕ)
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb)) :
    machine.tr (stReturn k) (returnCfg cfg k lsb (p + 1)).inputSymbol
        (returnCfg cfg k lsb (p + 1)).workTapeSymbols =
      { inputMove := 0
        workActions := fun i ↦ (none, if i = (siteLayout k).first ∨ i = (siteLayout k).second
          then -(siteLayout k).dir else 0)
        outS := none
        q' := some (stReturn k) } := by
  have h : origin ((returnCfg cfg k lsb (p + 1)).workTapeSymbols (siteLayout k).first) = false := by
    simp only [Cfg.workTapeSymbols, returnCfg, true_or, ↓reduceIte]
    rw [ho, decide_eq_false]
    intro he
    have := cell_injective _ _ (siteLayout_proper k).dir_ne_zero (p + 1) 0
      (he.trans (cell_zero _ _).symm)
    omega
  rw [tr_return]
  simp only [returnTr, h, Bool.false_eq_true, ↓reduceIte]

/-- A return step away from the tag moves the digit heads and changes nothing else. -/
theorem step_return_pos (p : ℕ)
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb)) :
    machine.step (returnCfg cfg k lsb (p + 1)) = returnCfg cfg k lsb p := by
  rw [step_of_state _ _ (stReturn k) rfl, tr_return_pos cfg k lsb p ho]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  simp only [returnCfg]
  split_ifs with h
  · rw [cell_succ]
    simp
  · simp

/-- Returning away from the tag emits nothing. -/
theorem outputSymbol_return_pos (p : ℕ)
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb)) :
    machine.outputSymbol (returnCfg cfg k lsb (p + 1)) = none := by
  change (machine.tr (stReturn k) _ _).outS = none
  rw [tr_return_pos cfg k lsb p ho]

/-- Every return configuration and its empty output, before the final state change. -/
theorem configs_return
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb)) (t p : ℕ) :
    machine.configs (returnCfg cfg k lsb (p + t)) t = returnCfg cfg k lsb p ∧
      machine.outputString (returnCfg cfg k lsb (p + t)) t = [] := by
  revert p
  refine Nat.rec ?_ ?_ t
  · intro p
    exact ⟨rfl, rfl⟩
  · intro t ih p
    obtain ⟨hc, hout⟩ := ih (p + 1)
    rw [show p + (t + 1) = p + 1 + t by omega]
    constructor
    · rw [configs_succ_eq_step', hc, step_return_pos cfg k lsb p ho]
    · rw [outputString_succ, hout, hc, outputSymbol_return_pos cfg k lsb p ho]
      rfl

/-- At the tag, the return transition reads the mismatch marker. -/
theorem tr_return_zero
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb)) :
    machine.tr (stReturn k) (returnCfg cfg k lsb 0).inputSymbol
        (returnCfg cfg k lsb 0).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none,
        q' := some (if cfg.workTapes (siteLayout k).mism (cfg.workTapePos (siteLayout k).mism)
          == some 0 then siteZero k else siteNext k) } := by
  have h : origin ((returnCfg cfg k lsb 0).workTapeSymbols (siteLayout k).first) = true := by
    simp only [Cfg.workTapeSymbols, returnCfg, true_or, ↓reduceIte]
    rw [cell_zero, ho]
    simp
  have hm : (returnCfg cfg k lsb 0).workTapeSymbols (siteLayout k).mism =
      cfg.workTapes (siteLayout k).mism (cfg.workTapePos (siteLayout k).mism) := by
    have h1 := (siteLayout_proper k).first_ne_mism
    have h2 := (siteLayout_proper k).second_ne_mism
    simp only [Cfg.workTapeSymbols, returnCfg, h1.symm, h2.symm, or_self, ↓reduceIte]
  rw [tr_return]
  simp only [returnTr, h, ↓reduceIte, hm]

/-- The tag transition changes only the finite control. -/
theorem step_return_zero
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb)) :
    machine.step (returnCfg cfg k lsb 0) = returnedCfg cfg k lsb := by
  rw [step_of_state _ _ (stReturn k) rfl, tr_return_zero cfg k lsb ho]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  simp [returnedCfg, returnCfg]

/-- Returning at the tag emits nothing. -/
theorem outputSymbol_return_zero
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb)) :
    machine.outputSymbol (returnCfg cfg k lsb 0) = none := by
  change (machine.tr (stReturn k) _ _).outS = none
  rw [tr_return_zero cfg k lsb ho]

/-- From significance {lit}`p`, the complete return takes exactly {lit}`p + 1` steps. -/
theorem configs_return_done
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb)) (p : ℕ) :
    machine.configs (returnCfg cfg k lsb p) (p + 1) = returnedCfg cfg k lsb ∧
      machine.outputString (returnCfg cfg k lsb p) (p + 1) = [] := by
  obtain ⟨hc, hout⟩ := configs_return cfg k lsb ho p 0
  simp only [Nat.zero_add] at hc hout
  constructor
  · rw [configs_succ_eq_step', hc, step_return_zero cfg k lsb ho]
  · rw [outputString_succ, hout, hc, outputSymbol_return_zero cfg k lsb ho]
    rfl

/-- Every return configuration keeps its digit heads at a significance at most the start. -/
theorem configs_return_pos
    (ho : ∀ z, origin (cfg.workTapes (siteLayout k).first z) = decide (z = lsb))
    (p t : ℕ) (ht : t ≤ p + 1) :
    ∃ q, q ≤ p ∧
      (machine.configs (returnCfg cfg k lsb p) t).workTapePos (siteLayout k).first =
        cell lsb (siteLayout k).dir q ∧
      (machine.configs (returnCfg cfg k lsb p) t).workTapePos (siteLayout k).second =
        cell lsb (siteLayout k).dir q ∧
      (∀ i, i ≠ (siteLayout k).first → i ≠ (siteLayout k).second →
        (machine.configs (returnCfg cfg k lsb p) t).workTapePos i = cfg.workTapePos i) := by
  by_cases htp : t ≤ p
  · have hc := (configs_return cfg k lsb ho t (p - t)).1
    rw [show p - t + t = p by omega] at hc
    rw [hc]
    refine ⟨p - t, by omega, by simp [returnCfg], by simp [returnCfg], ?_⟩
    intro i h1 h2
    simp [returnCfg, h1, h2]
  · have he : t = p + 1 := by omega
    subst t
    rw [(configs_return_done cfg k lsb ho p).1]
    refine ⟨0, Nat.zero_le _, by simp [returnedCfg, returnCfg], by simp [returnedCfg, returnCfg],
      ?_⟩
    intro i h1 h2
    simp [returnedCfg, returnCfg, h1, h2]

end Return

/-! ## The complete increment -/

section Macro

variable {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (k : Fin 6) (lsb : ℤ)

/-- The state a return selects for the two counter values. -/
def continuation (a b : ℕ) : Control := if a = b then siteZero k else siteNext k

/-- The counter values after a site's increment. -/
def incremented (a b : ℕ) : ℕ × ℕ :=
  if siteSel k then (a, b + 1) else (a + 1, b)

/-- A complete carry and return implements one increment: the pair representation moves to
the incremented values at the continuation state, the input head and every tape outside the
layout are unchanged, and nothing is emitted. -/
theorem configs_increment (width a b n : ℕ) (hn : n = if siteSel k then b else a)
    (h : PairRep (siteLayout k) lsb width cfg a b) (hq : cfg.state = some (stCarry k))
    (hnext : (n + 1).size ≤ width) :
    let f := flips n.bits
    let now := machine.configs cfg (2 * f + 1)
    PairRep (siteLayout k) lsb width now (incremented k a b).1 (incremented k a b).2 ∧
      now.state = some (continuation k (incremented k a b).1 (incremented k a b).2) ∧
      now.inputPos = cfg.inputPos ∧
      (∀ i, i ≠ (siteLayout k).first → i ≠ (siteLayout k).second → i ≠ (siteLayout k).mism →
        now.workTapes i = cfg.workTapes i ∧ now.workTapePos i = cfg.workTapePos i) ∧
      (∀ z, (∀ j, z ≠ cell lsb (siteLayout k).dir j) →
        now.workTapes (siteLayout k).first z = cfg.workTapes (siteLayout k).first z ∧
        now.workTapes (siteLayout k).second z = cfg.workTapes (siteLayout k).second z) ∧
      machine.outputString cfg (2 * f + 1) = [] := by
  set f := flips n.bits with hf
  have hbits : ∀ j, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir j =
      n.bits[j]?.getD false := by
    intro j
    rcases hsel : siteSel k with _ | _
    · simp only [siteSelected, hsel, Bool.false_eq_true, ↓reduceIte, hn]
      exact congrFun h.firstDigits j
    · simp only [siteSelected, hsel, ↓reduceIte, hn]
      exact congrFun h.secondDigits j
  obtain ⟨hstate, hpos0, hpos1, hin, hselected, hother, hmark, hcells, hwritten, horig, hunt,
    hout⟩ := configs_carry_bits cfg k lsb n.bits hq h.firstPos h.secondPos hbits
  have hw : f ≤ width := (Geb.BitTree.Counter.flips_bits_le_succ_size n).trans hnext
  have hm : cfg.workTapePos (siteLayout k).mism = (mismatchCount width
      (digitsFrom cfg (siteLayout k).first lsb (siteLayout k).dir)
      (digitsFrom cfg (siteLayout k).second lsb (siteLayout k).dir) : ℤ) := by
    rw [h.firstDigits, h.secondDigits]
    exact h.mismatchPos
  have hmis := configs_carry_bits_mismatch cfg k lsb n.bits width hq h.firstPos h.secondPos hbits
    hw hm f (Nat.le_refl _)
  set after := machine.configs cfg f with hafter
  set a' := (incremented k a b).1 with ha'
  set b' := (incremented k a b).2 with hb'
  have hd0 : digitsFrom after (siteLayout k).first lsb (siteLayout k).dir = bitsAt a' := by
    rcases hsel : siteSel k with _ | _
    · have hs : siteSelected k = (siteLayout k).first := by simp [siteSelected, hsel]
      rw [← hs, hselected]
      funext j
      simp [Geb.BitTree.Counter.increment_bits, hn, hsel, ha', incremented, bitsAt]
    · have hs : siteOther k = (siteLayout k).first := by simp [siteOther, hsel]
      rw [← hs]
      funext j
      simp only [digitsFrom, hother]
      rw [hs]
      have := congrFun h.firstDigits j
      simp only [digitsFrom] at this
      simpa [ha', incremented, hsel] using this
  have hd1 : digitsFrom after (siteLayout k).second lsb (siteLayout k).dir = bitsAt b' := by
    rcases hsel : siteSel k with _ | _
    · have hs : siteOther k = (siteLayout k).second := by simp [siteOther, hsel]
      rw [← hs]
      funext j
      simp only [digitsFrom, hother]
      rw [hs]
      have := congrFun h.secondDigits j
      simp only [digitsFrom] at this
      simpa [hb', incremented, hsel] using this
    · have hs : siteSelected k = (siteLayout k).second := by simp [siteSelected, hsel]
      rw [← hs, hselected]
      funext j
      simp [Geb.BitTree.Counter.increment_bits, hn, hsel, hb', incremented, bitsAt]
  have ho : ∀ z, origin (after.workTapes (siteLayout k).first z) = decide (z = lsb) :=
    fun z ↦ (horig z).trans (h.originTag z)
  have hmark' : ∀ z, after.workTapes (siteLayout k).mism z = if z = 0 then some 0 else none := by
    intro z
    rw [hmark, h.marker]
  have hm' : after.workTapePos (siteLayout k).mism =
      (mismatchCount width (bitsAt a') (bitsAt b') : ℤ) := by
    rw [← hd0, ← hd1]
    exact hmis
  have hm'' : (returnedCfg after k lsb).workTapePos (siteLayout k).mism =
      (mismatchCount width (bitsAt a') (bitsAt b') : ℤ) := by
    have h1 := (siteLayout_proper k).first_ne_mism
    have h2 := (siteLayout_proper k).second_ne_mism
    simp only [returnedCfg, returnCfg, h1.symm, h2.symm, or_self, ↓reduceIte]
    exact hm'
  have ha's : a'.size ≤ width := by
    rcases hsel : siteSel k with _ | _
    · simpa [ha', incremented, hsel, hn] using hnext
    · simpa [ha', incremented, hsel] using h.firstSize
  have hb's : b'.size ≤ width := by
    rcases hsel : siteSel k with _ | _
    · simpa [hb', incremented, hsel] using h.secondSize
    · simpa [hb', incremented, hsel, hn] using hnext
  have hblank : ∀ j, after.workTapes (siteLayout k).first (cell lsb (siteLayout k).dir j) =
      none ↔ a'.size ≤ j := by
    intro j
    rcases hsel : siteSel k with _ | _
    · have hs : siteSelected k = (siteLayout k).first := by simp [siteSelected, hsel]
      have hmax := size_succ_eq_max a
      have ha'a : a' = a + 1 := by simp [ha', incremented, hsel]
      have hna : n = a := by simp [hn, hsel]
      rw [hna] at hf
      rw [ha'a, hmax, ← hf]
      by_cases hj : j < f
      · rw [← hs]
        have := hwritten j hj
        constructor
        · intro he
          exact (this he).elim
        · intro hle
          omega
      · rw [← hs, hcells _ (by
          intro i hi he
          exact hj (cell_injective _ _ (siteLayout_proper k).dir_ne_zero _ _ he ▸ hi)), hs,
          h.firstBlank]
        omega
    · have hs : siteOther k = (siteLayout k).first := by simp [siteOther, hsel]
      have ha'a : a' = a := by simp [ha', incremented, hsel]
      rw [← hs, hother, hs, ha'a]
      exact h.firstBlank j
  have hrep := returnCfg_self after k lsb f hstate hpos0 hpos1
  obtain ⟨hc, hout'⟩ := configs_return_done after k lsb ho f
  rw [hrep] at hc hout'
  have hfinal : machine.configs cfg (2 * f + 1) = returnedCfg after k lsb := by
    rw [show 2 * f + 1 = f + (f + 1) by omega, configs_add]
    exact hc
  have hzero : after.workTapes (siteLayout k).mism (after.workTapePos (siteLayout k).mism) ==
      some 0 ↔ a' = b' := by
    have hdata : PairData (siteLayout k) lsb width after a' b' :=
      ⟨hd0, hd1, ho, hblank, hmark', hm', ha's, hb's⟩
    rw [hmark']
    constructor
    · intro hz
      by_cases hp : after.workTapePos (siteLayout k).mism = 0
      · exact hdata.mismatchPos_eq_zero_iff.mp hp
      · simp [hp] at hz
    · intro hab
      have hp := hdata.mismatchPos_eq_zero_iff.mpr hab
      simp [hp]
  have hstate' : (returnedCfg after k lsb).state = some (continuation k a' b') := by
    simp only [returnedCfg, continuation]
    by_cases hab : a' = b'
    · rw [ite_eq_left (hzero.mpr hab), ite_eq_left hab]
    · rw [ite_eq_right (fun hz ↦ hab (hzero.mp hz)), ite_eq_right hab]
  have hcells' : ∀ z, (∀ j, z ≠ cell lsb (siteLayout k).dir j) →
      after.workTapes (siteLayout k).first z = cfg.workTapes (siteLayout k).first z ∧
      after.workTapes (siteLayout k).second z = cfg.workTapes (siteLayout k).second z := by
    intro z hz
    have hsel : after.workTapes (siteSelected k) z = cfg.workTapes (siteSelected k) z :=
      hcells z (fun j _ ↦ hz j)
    have hoth : after.workTapes (siteOther k) z = cfg.workTapes (siteOther k) z := by
      rw [hother]
    rcases hsel' : siteSel k with _ | _
    · have hs : siteSelected k = (siteLayout k).first := by simp [siteSelected, hsel']
      have ho' : siteOther k = (siteLayout k).second := by simp [siteOther, hsel']
      rw [hs] at hsel
      rw [ho'] at hoth
      exact ⟨hsel, hoth⟩
    · have hs : siteSelected k = (siteLayout k).second := by simp [siteSelected, hsel']
      have ho' : siteOther k = (siteLayout k).first := by simp [siteOther, hsel']
      rw [hs] at hsel
      rw [ho'] at hoth
      exact ⟨hoth, hsel⟩
  change PairRep (siteLayout k) lsb width _ a' b' ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [hfinal]
  refine ⟨⟨⟨hd0, hd1, ho, hblank, hmark', hm'', ha's, hb's⟩, ?_, ?_⟩, hstate', hin, ?_,
    hcells', ?_⟩
  · simp [returnedCfg, returnCfg, cell_zero]
  · simp [returnedCfg, returnCfg, cell_zero]
  · intro i h1 h2 h3
    obtain ⟨hu1, hu2⟩ := hunt i h1 h2 h3
    refine ⟨hu1, ?_⟩
    simp [returnedCfg, returnCfg, h1, h2, hu2]
  · rw [show 2 * f + 1 = f + (f + 1) by omega, outputString_add_eq_append, hout, hout']
    rfl

/-- Every digit and mismatch head stays within the bounds during an increment, provided the
cells up to the bit-change count are within them. -/
theorem configs_increment_head_bounds (width a b n : ℕ) (hn : n = if siteSel k then b else a)
    (h : PairRep (siteLayout k) lsb width cfg a b) (hq : cfg.state = some (stCarry k))
    (hnext : (n + 1).size ≤ width)
    (hcell : ∀ p, p ≤ flips n.bits → -1 ≤ cell lsb (siteLayout k).dir p ∧
      cell lsb (siteLayout k).dir p ≤ width)
    (t : ℕ) (ht : t ≤ 2 * flips n.bits + 1) (i : Fin 9) :
    (i = (siteLayout k).first ∨ i = (siteLayout k).second ∨ i = (siteLayout k).mism →
      -1 ≤ (machine.configs cfg t).workTapePos i ∧
        (machine.configs cfg t).workTapePos i ≤ width) ∧
    (i ≠ (siteLayout k).first → i ≠ (siteLayout k).second → i ≠ (siteLayout k).mism →
      (machine.configs cfg t).workTapePos i = cfg.workTapePos i) := by
  set f := flips n.bits with hf
  have hw : f ≤ width := (Geb.BitTree.Counter.flips_bits_le_succ_size n).trans hnext
  have hbits : ∀ j, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir j =
      n.bits[j]?.getD false := by
    intro j
    rcases hsel : siteSel k with _ | _
    · simp only [siteSelected, hsel, Bool.false_eq_true, ↓reduceIte, hn]
      exact congrFun h.firstDigits j
    · simp only [siteSelected, hsel, ↓reduceIte, hn]
      exact congrFun h.secondDigits j
  have hm : cfg.workTapePos (siteLayout k).mism = (mismatchCount width
      (digitsFrom cfg (siteLayout k).first lsb (siteLayout k).dir)
      (digitsFrom cfg (siteLayout k).second lsb (siteLayout k).dir) : ℤ) := by
    rw [h.firstDigits, h.secondDigits]
    exact h.mismatchPos
  by_cases htf : t ≤ f
  · obtain ⟨hp0, hp1, hunt⟩ :=
      configs_carry_bits_pos cfg k lsb n.bits hq h.firstPos h.secondPos hbits t htf
    have hm' := configs_carry_bits_mismatch cfg k lsb n.bits width hq h.firstPos h.secondPos
      hbits hw hm t htf
    have hcount := mismatchCount_le width
      (digitsFrom (machine.configs cfg t) (siteLayout k).first lsb (siteLayout k).dir)
      (digitsFrom (machine.configs cfg t) (siteLayout k).second lsb (siteLayout k).dir)
    have hc := hcell t (by omega)
    refine ⟨fun hi ↦ ?_, fun h1 h2 h3 ↦ hunt i h1 h2 h3⟩
    rcases hi with rfl | rfl | rfl
    · rw [hp0]
      exact hc
    · rw [hp1]
      exact hc
    · rw [hm']
      omega
  · have hm' := configs_carry_bits_mismatch cfg k lsb n.bits width hq h.firstPos h.secondPos
      hbits hw hm f (Nat.le_refl _)
    have hcount := mismatchCount_le width
      (digitsFrom (machine.configs cfg f) (siteLayout k).first lsb (siteLayout k).dir)
      (digitsFrom (machine.configs cfg f) (siteLayout k).second lsb (siteLayout k).dir)
    obtain ⟨hstate, hpos0, hpos1, hin, hselected, hother, hmark, hcells, hwritten, horig, hunt,
      hout⟩ := configs_carry_bits cfg k lsb n.bits hq h.firstPos h.secondPos hbits
    set after := machine.configs cfg f with hafter
    have ho : ∀ z, origin (after.workTapes (siteLayout k).first z) = decide (z = lsb) :=
      fun z ↦ (horig z).trans (h.originTag z)
    have hrep := returnCfg_self after k lsb f hstate hpos0 hpos1
    obtain ⟨q, hq', hq0, hq1, hqu⟩ := configs_return_pos after k lsb ho f (t - f) (by omega)
    rw [hrep] at hq0 hq1 hqu
    rw [show t = f + (t - f) by omega, configs_add]
    have hc := hcell q (by omega)
    refine ⟨fun hi ↦ ?_, fun h1 h2 h3 ↦ ?_⟩
    · rcases hi with rfl | rfl | rfl
      · rw [hq0]
        exact hc
      · rw [hq1]
        exact hc
      · rw [hqu _ (siteLayout_proper k).first_ne_mism.symm
          (siteLayout_proper k).second_ne_mism.symm, hm']
        omega
    · rw [hqu i h1 h2]
      exact (hunt i h1 h2 h3).2

end Macro

end Geb.BitTree.EliasBinary
