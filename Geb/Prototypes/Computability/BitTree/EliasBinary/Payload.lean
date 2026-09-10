/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Steps
public import Geb.Prototypes.Computability.BitTree.EliasBinary.Increment

set_option doc.verso true

/-!
# The payload phase

A payload bit is one read transition followed by an increment of the payload counter. When
the counter reaches the length register, the length pair is erased cell by cell from its
least significant cell down to the origin, and the completed leaf increments the leaves
counter.

## Main definitions

* {lit}`eraseCfg` is the configuration during the erasure of the length pair.
* {lit}`erasedCfg` is the configuration after the erasure, at the pending increment.

## Main statements

* {lit}`configs_erase` describes the erasure walk.
* {lit}`configs_bit_payload_aux` realizes a bit read in the payload state.

## Tags

Turing machine, simulation, Elias delta code, payload
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb digit origin bitsAt mismatchCount)
open Geb.BitTree.Counter (flips)
open Geb.TreeScanner (step_of_state)

/-! ## Transport along the tapes of a pair -/

section Transport

variable {input : List (Fin 4)} {cfg cfg' : Cfg 9 (Fin 4) Control input}

/-- A counter pair's contents transport along its three tapes. -/
theorem PairData.congrTapes {lay : Layout} {lsb : ℤ} {width a b : ℕ}
    (h : PairData lay lsb width cfg a b)
    (h1 : cfg'.workTapes lay.first = cfg.workTapes lay.first)
    (h2 : cfg'.workTapes lay.second = cfg.workTapes lay.second)
    (h3 : cfg'.workTapes lay.mism = cfg.workTapes lay.mism ∧
      cfg'.workTapePos lay.mism = cfg.workTapePos lay.mism) :
    PairData lay lsb width cfg' a b :=
  ⟨by funext j; simp only [digitsFrom, h1]; exact congrFun h.firstDigits j,
    by funext j; simp only [digitsFrom, h2]; exact congrFun h.secondDigits j,
    fun z ↦ by rw [h1]; exact h.originTag z, fun j ↦ by rw [h1]; exact h.firstBlank j,
    fun z ↦ by rw [h3.1]; exact h.marker z, by rw [h3.2]; exact h.mismatchPos, h.firstSize,
    h.secondSize⟩

/-- A counter pair with its heads transports along its three tapes. -/
theorem PairRep.congrTapes {lay : Layout} {lsb : ℤ} {width a b : ℕ}
    (h : PairRep lay lsb width cfg a b)
    (h1 : cfg'.workTapes lay.first = cfg.workTapes lay.first ∧
      cfg'.workTapePos lay.first = cfg.workTapePos lay.first)
    (h2 : cfg'.workTapes lay.second = cfg.workTapes lay.second ∧
      cfg'.workTapePos lay.second = cfg.workTapePos lay.second)
    (h3 : cfg'.workTapes lay.mism = cfg.workTapes lay.mism ∧
      cfg'.workTapePos lay.mism = cfg.workTapePos lay.mism) :
    PairRep lay lsb width cfg' a b :=
  ⟨h.toPairData.congrTapes h1.1 h2.1 h3, by rw [h1.2]; exact h.firstPos,
    by rw [h2.2]; exact h.secondPos⟩

/-- An idle size pair transports along its three tapes. -/
theorem IdleSize.congrTapes (h : IdleSize cfg)
    (h3 : cfg'.workTapes 3 = cfg.workTapes 3 ∧ cfg'.workTapePos 3 = cfg.workTapePos 3)
    (h4 : cfg'.workTapes 4 = cfg.workTapes 4 ∧ cfg'.workTapePos 4 = cfg.workTapePos 4)
    (h5 : cfg'.workTapes 5 = cfg.workTapes 5 ∧ cfg'.workTapePos 5 = cfg.workTapePos 5) :
    IdleSize cfg' :=
  ⟨by rw [h3.1]; exact h.register, by rw [h3.2]; exact h.registerPos,
    by rw [h4.1]; exact h.counter, by rw [h4.2]; exact h.counterPos,
    by rw [h5.1]; exact h.marker, by rw [h5.2]; exact h.mismPos⟩

/-- An idle length pair transports along its three tapes. -/
theorem IdleLength.congrTapes (h : IdleLength cfg)
    (h6 : cfg'.workTapes 6 = cfg.workTapes 6 ∧ cfg'.workTapePos 6 = cfg.workTapePos 6)
    (h7 : cfg'.workTapes 7 = cfg.workTapes 7 ∧ cfg'.workTapePos 7 = cfg.workTapePos 7)
    (h8 : cfg'.workTapes 8 = cfg.workTapes 8 ∧ cfg'.workTapePos 8 = cfg.workTapePos 8) :
    IdleLength cfg' :=
  ⟨by rw [h6.1]; exact h.register, by rw [h6.2]; exact h.registerPos,
    by rw [h7.1]; exact h.counter, by rw [h7.2]; exact h.counterPos,
    by rw [h8.1]; exact h.marker, by rw [h8.2]; exact h.mismPos⟩

end Transport

/-! ## Cells of the length pair -/

/-- The cells of the length pair extend leftwards from the least significant cell. -/
theorem cell_length (lsb : ℤ) (j : ℕ) : cell lsb (siteLayout 5).dir j = lsb - j := by
  simp only [cell, siteLayout, lengthLayout, SignType.coe_neg_one]
  omega

/-- After an increment, every cell of the selected tape above the bit-change count is
unchanged. -/
theorem configs_increment_selected {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (k : Fin 6) (lsb : ℤ) (width a b n : ℕ) (hn : n = if siteSel k then b else a)
    (h : PairRep (siteLayout k) lsb width cfg a b) (hq : cfg.state = some (stCarry k)) :
    ∀ z, (∀ j, j < flips n.bits → z ≠ cell lsb (siteLayout k).dir j) →
      (machine.configs cfg (2 * flips n.bits + 1)).workTapes (siteSelected k) z =
        cfg.workTapes (siteSelected k) z := by
  intro z hz
  have hbits : ∀ j, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir j =
      n.bits[j]?.getD false := by
    intro j
    rcases hsel : siteSel k with _ | _
    · simp only [siteSelected, hsel, Bool.false_eq_true, ↓reduceIte, hn]
      exact congrFun h.firstDigits j
    · simp only [siteSelected, hsel, ↓reduceIte, hn]
      exact congrFun h.secondDigits j
  obtain ⟨hstate, hpos0, hpos1, _, _, _, _, hcells, _, horig, _, _⟩ :=
    configs_carry_bits cfg k lsb n.bits hq h.firstPos h.secondPos hbits
  set f := flips n.bits with hf
  set after := machine.configs cfg f with hafter
  have ho : ∀ z, origin (after.workTapes (siteLayout k).first z) = decide (z = lsb) :=
    fun z ↦ (horig z).trans (h.originTag z)
  have hrep := returnCfg_self after k lsb f hstate hpos0 hpos1
  obtain ⟨hc, _⟩ := configs_return_done after k lsb ho f
  rw [hrep] at hc
  rw [show 2 * f + 1 = f + (f + 1) by omega, configs_add, ← hafter, hc]
  exact hcells z (fun j hj ↦ hz j hj)

/-! ## The erasure of the length pair -/

section Erase

variable {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (lsb : ℤ)

/-- The configuration after erasing the top {lit}`t` cells of both length tapes, with both
digit heads at the next cell to erase. -/
def eraseCfg (t : ℕ) : Cfg 9 (Fin 4) Control input where
  state := some stEraseLength
  inputPos := cfg.inputPos
  workTapes i := if i = 6 ∨ i = 7 then fun z ↦ if lsb - t < z then none else cfg.workTapes i z
    else cfg.workTapes i
  workTapePos i := if i = 6 ∨ i = 7 then lsb - t else cfg.workTapePos i

/-- The configuration after the erasure, with both digit heads moved back one cell. -/
def erasedCfg (t : ℕ) : Cfg 9 (Fin 4) Control input :=
  { eraseCfg cfg lsb t with
    state := some (stCarry 3)
    workTapePos := fun i ↦ if i = 6 ∨ i = 7 then lsb - t + 1 else cfg.workTapePos i }

/-- A configuration in the erasing state with both length heads at the least significant
cell, and blanks above it, is its own erasure form. -/
theorem eraseCfg_self (hq : cfg.state = some stEraseLength) (hp6 : cfg.workTapePos 6 = lsb)
    (hp7 : cfg.workTapePos 7 = lsb)
    (hb : ∀ z, lsb < z → cfg.workTapes 6 z = none ∧ cfg.workTapes 7 z = none) :
    eraseCfg cfg lsb 0 = cfg := by
  refine Cfg.ext hq.symm rfl ?_ ?_
  · funext i z
    simp only [eraseCfg, Nat.cast_zero, Int.sub_zero]
    split_ifs with hi
    · dsimp only
      split_ifs with hz
      · rcases hi with rfl | rfl
        · exact (hb z hz).1.symm
        · exact (hb z hz).2.symm
      · rfl
    · rfl
  · funext i
    simp only [eraseCfg, Nat.cast_zero, Int.sub_zero]
    split_ifs with hi
    · rcases hi with rfl | rfl
      · exact hp6.symm
      · exact hp7.symm
    · rfl

/-- The phase table at a non-blank cell of the erasure. -/
theorem tr_erase (t : ℕ) (hne : cfg.workTapes 6 (lsb - t) ≠ none) :
    machine.tr stEraseLength (eraseCfg cfg lsb t).inputSymbol
        (eraseCfg cfg lsb t).workTapeSymbols =
      act stEraseLength (fun i ↦ if i = 6 ∨ i = 7 then (some none, -1) else (none, 0)) := by
  have h : (eraseCfg cfg lsb t).workTapeSymbols 6 ≠ none := by
    simpa [Cfg.workTapeSymbols, eraseCfg] using hne
  rw [tr_phase stEraseLength (by simp), phaseTr_eraseLength, ite_eq_right h]

/-- Erasing a non-blank cell moves both length heads down one cell. -/
theorem step_erase (t : ℕ) (hne : cfg.workTapes 6 (lsb - t) ≠ none) :
    machine.step (eraseCfg cfg lsb t) = eraseCfg cfg lsb (t + 1) := by
  rw [step_of_state _ _ stEraseLength rfl, tr_erase cfg lsb t hne]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext i z
    simp only [act, eraseCfg]
    split_ifs with hi
    · simp only [Function.update_apply, Nat.cast_succ]
      split_ifs <;> first | rfl | omega
    · rfl
  · funext i
    simp only [act, eraseCfg]
    split_ifs with hi
    · simp only [SignType.coe_neg_one, Nat.cast_succ]
      omega
    · simp

/-- Erasing a non-blank cell emits nothing. -/
theorem outputSymbol_erase (t : ℕ) (hne : cfg.workTapes 6 (lsb - t) ≠ none) :
    machine.outputSymbol (eraseCfg cfg lsb t) = none := by
  change (machine.tr stEraseLength _ _).outS = none
  rw [tr_erase cfg lsb t hne]
  rfl

/-- The erasure walk over non-blank cells: its configuration and its empty output. -/
theorem configs_erase (m : ℕ) (hfull : ∀ j, j < m → cfg.workTapes 6 (lsb - j) ≠ none)
    (t : ℕ) (ht : t ≤ m) :
    machine.configs (eraseCfg cfg lsb 0) t = eraseCfg cfg lsb t ∧
      machine.outputString (eraseCfg cfg lsb 0) t = [] := by
  revert ht
  refine Nat.rec ?_ ?_ t
  · intro _
    exact ⟨rfl, rfl⟩
  · intro t ih ht
    obtain ⟨hc, hout⟩ := ih (by omega)
    have hne := hfull t (by omega)
    constructor
    · rw [configs_succ_eq_step', hc, step_erase cfg lsb t hne]
    · rw [outputString_succ, hout, hc, outputSymbol_erase cfg lsb t hne]
      rfl

/-- The phase table at the blank cell ending the erasure. -/
theorem tr_erase_exit (t : ℕ) (hb : cfg.workTapes 6 (lsb - t) = none) :
    machine.tr stEraseLength (eraseCfg cfg lsb t).inputSymbol
        (eraseCfg cfg lsb t).workTapeSymbols =
      act (stCarry 3) (fun i ↦ (none, if i = 6 ∨ i = 7 then 1 else 0)) := by
  have h : (eraseCfg cfg lsb t).workTapeSymbols 6 = none := by
    simpa [Cfg.workTapeSymbols, eraseCfg] using hb
  rw [tr_phase stEraseLength (by simp), phaseTr_eraseLength, ite_eq_left h]

/-- At the blank cell, both length heads step back and the pending increment starts. -/
theorem step_erase_exit (t : ℕ) (hb : cfg.workTapes 6 (lsb - t) = none) :
    machine.step (eraseCfg cfg lsb t) = erasedCfg cfg lsb t := by
  rw [step_of_state _ _ stEraseLength rfl, tr_erase_exit cfg lsb t hb]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext i
    rfl
  · funext i
    simp only [act, eraseCfg, erasedCfg]
    split_ifs with hi
    · simp
    · simp

/-- The exit transition emits nothing. -/
theorem outputSymbol_erase_exit (t : ℕ) (hb : cfg.workTapes 6 (lsb - t) = none) :
    machine.outputSymbol (eraseCfg cfg lsb t) = none := by
  change (machine.tr stEraseLength _ _).outS = none
  rw [tr_erase_exit cfg lsb t hb]
  rfl

/-- The complete erasure of {lit}`m` cells ending at a blank: {lit}`m + 1` steps. -/
theorem configs_erase_done (m : ℕ) (hfull : ∀ j, j < m → cfg.workTapes 6 (lsb - j) ≠ none)
    (hb : cfg.workTapes 6 (lsb - m) = none) :
    machine.configs (eraseCfg cfg lsb 0) (m + 1) = erasedCfg cfg lsb m ∧
      machine.outputString (eraseCfg cfg lsb 0) (m + 1) = [] := by
  obtain ⟨hc, hout⟩ := configs_erase cfg lsb m hfull m (Nat.le_refl _)
  constructor
  · rw [configs_succ_eq_step', hc, step_erase_exit cfg lsb m hb]
  · rw [outputString_succ, hout, hc, outputSymbol_erase_exit cfg lsb m hb]
    rfl

/-- The heads during the erasure stay within the bounds of the starting configuration. -/
theorem eraseCfg_headBound (width t : ℕ) (h : HeadBound width cfg) (h1 : -1 ≤ lsb - t)
    (h2 : lsb ≤ width) : HeadBound width (eraseCfg cfg lsb t) := by
  intro i
  simp only [eraseCfg]
  split_ifs
  · omega
  · exact h i

/-- The heads after the erasure stay within the bounds of the starting configuration. -/
theorem erasedCfg_headBound (width t : ℕ) (h : HeadBound width cfg) (h1 : -1 ≤ lsb - t + 1)
    (h2 : lsb - t + 1 ≤ width) : HeadBound width (erasedCfg cfg lsb t) := by
  intro i
  simp only [erasedCfg]
  split_ifs
  · omega
  · exact h i

/-- Every head bound holds throughout the complete erasure. -/
theorem configs_erase_headBound (width m : ℕ)
    (hfull : ∀ j, j < m → cfg.workTapes 6 (lsb - j) ≠ none)
    (hb : cfg.workTapes 6 (lsb - m) = none) (h : HeadBound width cfg) (h1 : lsb - m = -1)
    (h2 : lsb ≤ width) :
    ∀ u, u ≤ m + 1 → HeadBound width (machine.configs (eraseCfg cfg lsb 0) u) := by
  intro u hu
  by_cases hum : u ≤ m
  · rw [(configs_erase cfg lsb m hfull u hum).1]
    exact eraseCfg_headBound cfg lsb width u h (by omega) h2
  · rw [show u = m + 1 by omega, (configs_erase_done cfg lsb m hfull hb).1]
    exact erasedCfg_headBound cfg lsb width m h (by omega) (by omega)

/-- Tapes outside the length pair are unchanged by the erasure. -/
theorem erasedCfg_untouched (t : ℕ) (i : Fin 9) (h6 : i ≠ 6) (h7 : i ≠ 7) :
    (erasedCfg cfg lsb t).workTapes i = cfg.workTapes i ∧
      (erasedCfg cfg lsb t).workTapePos i = cfg.workTapePos i := by
  simp [erasedCfg, eraseCfg, h6, h7]

end Erase

/-! ## One payload bit -/

/-- The finite state of a completed leaf is the continuation of the leaves increment. -/
theorem phaseState_finish (k f l : ℕ) (hk : k + l = f) :
    phaseState (Elias.Scanner.finish k) = continuation 3 f (l + 1) := by
  unfold Elias.Scanner.finish continuation
  by_cases h1 : k = 1
  · rw [ite_eq_left h1, ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_right h1, ite_eq_right (by omega)]
    rfl

/-- The ruler head is at the origin after a completed leaf. -/
theorem rulerPos_finish (k : ℕ) : rulerPos (Elias.Scanner.finish k) = 0 := by
  unfold Elias.Scanner.finish
  split <;> rfl

/-- After a completed leaf, both header pairs are idle. -/
theorem phaseRep_finish {input : List (Fin 4)} (width : ℕ) (cfg : Cfg 9 (Fin 4) Control input)
    (k f l t : ℕ) (h : IdleSize cfg ∧ IdleLength cfg) :
    PhaseRep width cfg ⟨Elias.Scanner.finish k, f, l, t⟩ := by
  unfold PhaseRep
  by_cases h1 : k = 1
  · rw [show Elias.Scanner.finish k = (.done, 0) by
      unfold Elias.Scanner.finish; rw [ite_eq_left h1]]
    exact h
  · rw [show Elias.Scanner.finish k = (.tree, k - 1) by
      unfold Elias.Scanner.finish; rw [ite_eq_right h1]]
    exact h

/-- One step realizes its empty output. -/
theorem outputString_one_payload {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (b : Bool) (hq : cfg.state = some stPayloadBit) (hi : cfg.inputSymbol = some (boolEmb b)) :
    machine.outputString cfg 1 = [] := by
  rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero,
    outputSymbol_scan cfg stPayloadBit hq (by simp) b hi]
  rfl

/-- A payload bit enters the payload increment, changing only the finite control and the
input head. -/
theorem step_payload {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (b : Bool) (hq : cfg.state = some stPayloadBit) (hi : cfg.inputSymbol = some (boolEmb b)) :
    machine.step cfg =
      { cfg with state := some (stCarry 5), inputPos := moveInputPos cfg.inputPos 1 } := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stPayloadBit (by simp), scanTr_payload]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    rfl
  · funext i
    simp [consumeAct, stay]

/-- A bit read in the payload state, given that the payload counter is blank below the
origin: the counter is incremented, and when it reaches the register the length pair is
erased and the leaves counter is incremented. -/
theorem configs_bit_payload {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) (b : Bool) (n width : ℕ) (hv : AccountValid n a)
    (h : Represents width cfg a) (hi : cfg.inputSymbol = some (boolEmb b))
    (hw1 : a.forks.size + 1 ≤ width) (hw3 : (a.leaves + 1).size ≤ width)
    (r k : ℕ) (hs : a.state = (.payload r, k)) : BitSpec cfg a b width := by
  have hl := h.live (by rw [hs]; simp)
  have hph := hl.phase
  unfold PhaseRep at hph
  rw [hs] at hph
  have hb7 : ∀ z, z < 0 → cfg.workTapes 7 z = none := fun z hz ↦ (hph.2.2 z (Or.inl hz)).2
  obtain ⟨hsize, hpair, hbeyond'⟩ := hph
  have hbeyond : ∀ z, ((a.total.size - 1 : ℕ) : ℤ) < z →
      cfg.workTapes 6 z = none ∧ cfg.workTapes 7 z = none :=
    fun z hz ↦ hbeyond' z (Or.inr hz)
  have hact := hv.active
  rw [hs] at hact
  obtain ⟨hk, hr⟩ := hact
  have ht2 := hv.total_ge r (by rw [hs])
  have hlt := hv.payload_lt r (by rw [hs])
  have hts := hv.total_size_le r (by rw [hs])
  have hkl : k + a.leaves = a.forks := by
    have := hv.pending (by rw [hs]; simp)
    rw [hs] at this
    exact this
  have hpos := size_pos_of_pos a.total (by omega)
  set lsb : ℤ := ((a.total.size - 1 : ℕ) : ℤ) with hlsb
  have hq : cfg.state = some stPayloadBit := by rw [h.state, hs]; rfl
  have hcap : capped a b = false := by simp [capped, hs]
  have hpend : PairRep pendingLayout 0 width cfg a.forks a.leaves :=
    hl.pendingRep (by rw [hs]; rfl)
  have hv' := accountStep_valid n a b hv
  -- the read transition
  have hstep := step_payload cfg b hq hi
  set cfg1 : Cfg 9 (Fin 4) Control input :=
    { cfg with state := some (stCarry 5), inputPos := moveInputPos cfg.inputPos 1 } with hcfg1
  have hc1 : machine.configs cfg 1 = cfg1 := by
    rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hstep]
  have ht1 : ∀ i, cfg1.workTapes i = cfg.workTapes i := fun _ ↦ rfl
  have hp1 : ∀ i, cfg1.workTapePos i = cfg.workTapePos i := fun _ ↦ rfl
  have hout1 := outputString_one_payload cfg b hq hi
  have hh1 : ∀ u ≤ 1, HeadBound width (machine.configs cfg u) := by
    intro u hu
    have hu' : u = 0 ∨ u = 1 := by omega
    rcases hu' with rfl | rfl
    · exact h.bound
    · rw [hc1]
      exact h.bound
  -- the payload increment
  have hpair1 : PairRep (siteLayout 5) lsb width cfg1 a.total (a.total - r) :=
    hpair.congr ht1 hp1
  have hnext : (a.total - r + 1).size ≤ width := by
    have := Geb.BitTree.Counter.size_mono (show a.total - r + 1 ≤ a.total by omega)
    omega
  have hfle : flips (a.total - r).bits ≤ a.total.size :=
    (Geb.BitTree.Counter.flips_bits_le_succ_size _).trans
      (Geb.BitTree.Counter.size_mono (show a.total - r + 1 ≤ a.total by omega))
  set f := flips (a.total - r).bits with hf
  obtain ⟨hrep, hstate, hin, hunt, hcells, hout⟩ :=
    configs_increment cfg1 5 lsb width a.total (a.total - r) (a.total - r) rfl hpair1 rfl hnext
  have hcell : ∀ p, p ≤ f → -1 ≤ cell lsb (siteLayout 5).dir p ∧
      cell lsb (siteLayout 5).dir p ≤ width := by
    intro p hp
    rw [cell_length]
    omega
  have hbounds := configs_increment_head_bounds cfg1 5 lsb width a.total (a.total - r)
    (a.total - r) rfl hpair1 rfl hnext hcell
  have hsel := configs_increment_selected cfg1 5 lsb width a.total (a.total - r) (a.total - r)
    rfl hpair1 rfl
  simp only [incremented, siteSel, ↓reduceIte] at hrep hstate
  set cfg2 := machine.configs cfg1 (2 * f + 1) with hcfg2
  have hh2 : ∀ u ≤ 2 * f + 1, HeadBound width (machine.configs cfg1 u) := by
    intro u hu i
    obtain ⟨hin', hout'⟩ := hbounds u hu i
    by_cases hmem : i = (siteLayout 5).first ∨ i = (siteLayout 5).second ∨
        i = (siteLayout 5).mism
    · exact hin' hmem
    · rw [not_or, not_or] at hmem
      rw [hout' hmem.1 hmem.2.1 hmem.2.2, hp1]
      exact h.bound i
  have hbeyond2 : ∀ z, lsb < z → cfg2.workTapes 6 z = none ∧ cfg2.workTapes 7 z = none := by
    intro z hz
    have hne : ∀ j, z ≠ cell lsb (siteLayout 5).dir j := by
      intro j
      rw [cell_length]
      omega
    obtain ⟨h6, h7⟩ := hcells z hne
    exact ⟨h6.trans (hbeyond z hz).1, h7.trans (hbeyond z hz).2⟩
  have hb7' : ∀ z, z < 0 → cfg2.workTapes 7 z = none := by
    intro z hz
    have hne : ∀ j, j < f → z ≠ cell lsb (siteLayout 5).dir j := by
      intro j hj
      rw [cell_length]
      omega
    rw [show (7 : Fin 9) = siteSelected 5 from rfl, hsel z hne, ht1]
    exact hb7 z hz
  have hunt2 : ∀ i, i ≠ 6 → i ≠ 7 → i ≠ 8 →
      cfg2.workTapes i = cfg.workTapes i ∧ cfg2.workTapePos i = cfg.workTapePos i :=
    fun i h6 h7 h8 ↦ hunt i h6 h7 h8
  have hcadd2 : machine.configs cfg (1 + (2 * f + 1)) = cfg2 := by
    rw [configs_add, hc1]
  have hin2 : cfg2.inputPos = moveInputPos cfg.inputPos 1 := by rw [hin]
  have hout2 : machine.outputString cfg (1 + (2 * f + 1)) = [] :=
    outputString_add_nil cfg 1 _ hout1 (by rw [hc1]; exact hout)
  have hhb2 : ∀ u ≤ 1 + (2 * f + 1), HeadBound width (machine.configs cfg u) :=
    headBound_add cfg width 1 _ hh1 (by rw [hc1]; exact hh2)
  by_cases hr1 : r = 1
  · -- the counter reaches the register: erase the length pair and complete the leaf
    subst hr1
    have hcost : macroCost a b = 1 + (2 * f + 1) + (a.total.size + 1) +
        (2 * flips a.leaves.bits + 1) := by
      have : macroCost a b = 1 + inc (a.total - 1) + a.total.size + 1 + inc a.leaves := by
        simp [macroCost, hcap, hs]
      rw [this]
      unfold inc
      omega
    have hacc : accountStep a b = ⟨Elias.Scanner.finish k, a.forks, a.leaves + 1, 0⟩ := by
      simp [accountStep, hcap, hs, Elias.Scanner.step, leafEnds, nextTotal]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ a.total)] at hrep hstate
    have hcont : continuation 5 a.total a.total = stEraseLength := by
      unfold continuation
      rw [ite_eq_left rfl]
      rfl
    rw [hcont] at hstate
    have hp6 : cfg2.workTapePos 6 = lsb := hrep.firstPos
    have hp7 : cfg2.workTapePos 7 = lsb := hrep.secondPos
    have hp8 : cfg2.workTapePos 8 = 0 := by
      rw [show cfg2.workTapePos 8 = _ from hrep.mismatchPos,
        (Geb.BitTree.BinaryMachine.mismatchCount_eq_zero_iff_eq width _ _
          (fun _ _ ↦ rfl)).mpr rfl]
      rfl
    have hfull : ∀ j, j < a.total.size → cfg2.workTapes 6 (lsb - j) ≠ none := by
      intro j hj he
      rw [← cell_length] at he
      have := (hrep.firstBlank j).mp he
      omega
    have hblank6 : cfg2.workTapes 6 (lsb - a.total.size) = none := by
      rw [← cell_length]
      exact (hrep.firstBlank _).mpr (Nat.le_refl _)
    have hself := eraseCfg_self cfg2 lsb hstate hp6 hp7 hbeyond2
    obtain ⟨hc3, hout3⟩ := configs_erase_done cfg2 lsb a.total.size hfull hblank6
    rw [hself] at hc3 hout3
    have hhb3 := configs_erase_headBound cfg2 lsb width a.total.size hfull hblank6
      (hh2 _ (Nat.le_refl _)) (by omega) (by omega)
    rw [hself] at hhb3
    set cfg3 := erasedCfg cfg2 lsb a.total.size with hcfg3
    have hunt3 := erasedCfg_untouched cfg2 lsb a.total.size
    have hb3 : HeadBound width cfg3 := by
      rw [← hc3]
      exact hhb3 _ (Nat.le_refl _)
    have hidle : IdleLength cfg3 := by
      have hblank : ∀ z, cfg3.workTapes 6 z = none ∧ cfg3.workTapes 7 z = none := by
        intro z
        simp only [hcfg3, erasedCfg, eraseCfg, true_or, or_true, ↓reduceIte]
        by_cases hz : lsb - a.total.size < z
        · simp [hz]
        · rw [ite_eq_right hz, ite_eq_right hz]
          refine ⟨?_, hb7' z (by omega)⟩
          have hj : z = cell lsb (siteLayout 5).dir (lsb - z).toNat := by
            rw [cell_length]
            omega
          rw [hj]
          exact (hrep.firstBlank _).mpr (by omega)
      refine ⟨fun z ↦ (hblank z).1, ?_, fun z ↦ (hblank z).2, ?_, ?_, ?_⟩
      · simp only [hcfg3, erasedCfg, true_or, ↓reduceIte]
        omega
      · simp only [hcfg3, erasedCfg, or_true, ↓reduceIte]
        omega
      · rw [(hunt3 8 (by decide) (by decide)).1]
        exact hrep.marker
      · rw [(hunt3 8 (by decide) (by decide)).2]
        exact hp8
    have hsize3 : IdleSize cfg3 :=
      (hsize.congrTapes (hunt2 3 (by decide) (by decide) (by decide))
        (hunt2 4 (by decide) (by decide) (by decide))
        (hunt2 5 (by decide) (by decide) (by decide))).congrTapes
        (hunt3 3 (by decide) (by decide)) (hunt3 4 (by decide) (by decide))
        (hunt3 5 (by decide) (by decide))
    have hpend3 : PairRep (siteLayout 3) 0 width cfg3 a.forks a.leaves :=
      (hpend.congrTapes (hunt2 0 (by decide) (by decide) (by decide))
        (hunt2 1 (by decide) (by decide) (by decide))
        (hunt2 2 (by decide) (by decide) (by decide))).congrTapes
        (hunt3 0 (by decide) (by decide)) (hunt3 1 (by decide) (by decide))
        (hunt3 2 (by decide) (by decide))
    -- the leaves increment
    obtain ⟨hrep4, hstate4, hin4, hunt4, _, hout4⟩ :=
      configs_increment cfg3 3 0 width a.forks a.leaves a.leaves rfl hpend3 rfl hw3
    have hbounds4 := configs_increment_head_bounds cfg3 3 0 width a.forks a.leaves a.leaves
      rfl hpend3 rfl hw3 (by
        intro p hp
        have := Geb.BitTree.Counter.flips_bits_le_succ_size a.leaves
        simp only [cell, siteLayout, pendingLayout, SignType.coe_one, Int.one_mul]
        omega)
    simp only [incremented, siteSel, ↓reduceIte] at hrep4 hstate4
    set g := flips a.leaves.bits with hg
    set cfg4 := machine.configs cfg3 (2 * g + 1) with hcfg4
    have hhb4 : ∀ u ≤ 2 * g + 1, HeadBound width (machine.configs cfg3 u) := by
      intro u hu i
      obtain ⟨hin', hout'⟩ := hbounds4 u hu i
      by_cases hmem : i = (siteLayout 3).first ∨ i = (siteLayout 3).second ∨
          i = (siteLayout 3).mism
      · exact hin' hmem
      · rw [not_or, not_or] at hmem
        rw [hout' hmem.1 hmem.2.1 hmem.2.2]
        exact hb3 i
    have hcadd : machine.configs cfg (1 + (2 * f + 1) + (a.total.size + 1) + (2 * g + 1)) =
        cfg4 := by
      rw [configs_add cfg _ (2 * g + 1), configs_add cfg _ (a.total.size + 1), hcadd2, hc3]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcost, hcadd, hacc]
      refine Represents.ofLive (n := n) ?_ ⟨hrep4.toPairData, ?_, ?_, ?_⟩ (hacc ▸ hv') hw1
      · rw [hstate4]
        exact congrArg some (phaseState_finish k a.forks a.leaves hkl).symm
      · rw [rulerPos_finish]
        exact hrep4.firstPos
      · exact hrep4.secondPos
      · refine phaseRep_finish width cfg4 k a.forks (a.leaves + 1) 0 ⟨?_, ?_⟩
        · exact hsize3.congrTapes (hunt4 3 (by decide) (by decide) (by decide))
            (hunt4 4 (by decide) (by decide) (by decide))
            (hunt4 5 (by decide) (by decide) (by decide))
        · exact hidle.congrTapes (hunt4 6 (by decide) (by decide) (by decide))
            (hunt4 7 (by decide) (by decide) (by decide))
            (hunt4 8 (by decide) (by decide) (by decide))
    · rw [hcost, hcadd, hin4, hcfg3]
      exact hin2
    · rw [hcost]
      refine outputString_add_nil cfg _ _ (outputString_add_nil cfg _ _ hout2 ?_) ?_
      · rw [hcadd2]
        exact hout3
      · rw [configs_add, hcadd2, hc3]
        exact hout4
    · rw [hcost]
      refine headBound_add cfg width _ _ (headBound_add cfg width _ _ hhb2 ?_) ?_
      · rw [hcadd2]
        exact hhb3
      · rw [configs_add, hcadd2, hc3]
        exact hhb4
  · -- the counter remains below the register
    have hcost : macroCost a b = 1 + (2 * f + 1) := by
      have : macroCost a b = 1 + inc (a.total - r) := by simp [macroCost, hcap, hs, hr1]
      rw [this, inc]
    have hacc : accountStep a b = ⟨(.payload (r - 1), k), a.forks, a.leaves, a.total⟩ := by
      simp [accountStep, hcap, hs, Elias.Scanner.step, leafEnds, nextTotal, hr1]
    have hcont : continuation 5 a.total (a.total - r + 1) = stPayloadBit := by
      unfold continuation
      rw [ite_eq_right (by omega)]
      rfl
    rw [hcont] at hstate
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcost, hcadd2, hacc]
      refine Represents.ofLive (n := n) hstate ⟨?_, ?_, ?_, ?_⟩ (hacc ▸ hv') hw1
      · exact hpend.toPairData.congrTapes (hunt2 0 (by decide) (by decide) (by decide)).1
          (hunt2 1 (by decide) (by decide) (by decide)).1
          (hunt2 2 (by decide) (by decide) (by decide))
      · rw [(hunt2 0 (by decide) (by decide) (by decide)).2, hl.forksPos, hs]
        rfl
      · rw [(hunt2 1 (by decide) (by decide) (by decide)).2]
        exact hl.leavesPos
      · unfold PhaseRep
        dsimp only
        refine ⟨hsize.congrTapes (hunt2 3 (by decide) (by decide) (by decide))
          (hunt2 4 (by decide) (by decide) (by decide))
          (hunt2 5 (by decide) (by decide) (by decide)), ?_, ?_⟩
        · rw [show a.total - (r - 1) = a.total - r + 1 by omega]
          exact hrep
        · intro z hz
          rcases hz with hz | hz
          · refine ⟨?_, hb7' z hz⟩
            have hj : z = cell lsb (siteLayout 5).dir (lsb - z).toNat := by
              rw [cell_length]
              omega
            rw [hj]
            exact (hrep.firstBlank _).mpr (by omega)
          · exact hbeyond2 z hz
    · rw [hcost, hcadd2]
      exact hin2
    · rw [hcost]
      exact hout2
    · rw [hcost]
      exact hhb2

end Geb.BitTree.EliasBinary
