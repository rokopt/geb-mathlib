/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Simple

set_option doc.verso true

/-!
# The first pass

Initialization writes the tagged origins and the markers. The first pass then consumes every
input bit, incrementing the forks counter and the leaves counter in turn, so that both hold
the input length, offset by the pending root. The rewind returns the input head to the first
bit. The configuration reached is the boundary of the initial account of the second pass.

## Main definitions

* {lit}`startCfg` is the configuration after initialization.
* {lit}`CountRep` describes the configuration at each input boundary of the first pass.

## Main statements

* {lit}`configs_count` realizes the first pass up to any prefix.
* {lit}`configs_passOne` realizes initialization, the first pass and the rewind.

## Tags

Turing machine, simulation, binary counter, first pass
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb digit origin mismatchCount bitsAt)
open Geb.TreeScanner (step_of_state)

/-- The tapes after initialization: tagged origins on the forks, leaves and size register
tapes, markers on the mismatch tapes. -/
def startTape : Fin 9 → ℤ → Option (Fin 4)
  | 0, z => if z = 0 then some 3 else none
  | 1, z => if z = 0 then some 2 else none
  | 2, z => if z = 0 then some 0 else none
  | 3, z => if z = 0 then some 2 else none
  | 5, z => if z = 0 then some 0 else none
  | 8, z => if z = 0 then some 0 else none
  | _, _ => none

/-- The configuration after initialization, with the pending mismatch head at one. -/
def startCfg (input : List (Fin 4)) : Cfg 9 (Fin 4) Control input where
  state := some stCount
  inputPos := 1
  workTapes := startTape
  workTapePos i := if i = 2 then 1 else 0

/-- Initialization reaches the start configuration in one step. -/
theorem configs_init (input : List (Fin 4)) :
    machine.configs (machine.initCfg input) 1 = startCfg input := by
  rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero,
    step_of_state _ _ stInit rfl, tr_init]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos 1 initTr.inputMove = 1
    exact moveInputPos_zero _
  · funext i z
    fin_cases i <;> simp [initTr, act, Function.update_apply, startCfg, startTape, initCfg]
  · funext i
    fin_cases i <;> simp [initTr, act, startCfg, initCfg]

/-- Initialization emits nothing. -/
theorem outputString_init (input : List (Fin 4)) :
    machine.outputString (machine.initCfg input) 1 = [] := rfl

/-- The initialization step keeps every head within any positive width. -/
theorem headBound_init (input : List (Fin 4)) (width : ℕ) (hw : 1 ≤ width) :
    ∀ u ≤ 1, HeadBound width (machine.configs (machine.initCfg input) u) := by
  intro u hu i
  have hu' : u = 0 ∨ u = 1 := by omega
  rcases hu' with rfl | rfl
  · rw [configs_zero]
    change -1 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ width
    omega
  · rw [configs_init]
    fin_cases i <;> simp only [startCfg] <;> omega

/-- The start configuration holds the counters one and zero. -/
theorem startCfg_pairRep (input : List (Fin 4)) (width : ℕ) (hw : 1 ≤ width) :
    PairRep pendingLayout 0 width (startCfg input) 1 0 := by
  have hb1 : ∀ j, bitsAt 1 j = decide (j = 0) := by
    intro j
    cases j <;> simp [bitsAt]
  have hb0 : ∀ j, bitsAt 0 j = false := fun j ↦ by simp [bitsAt, Nat.zero_bits]
  have hcell : ∀ j : ℕ, cell 0 pendingLayout.dir j = j := fun j ↦ by
    simp [cell, pendingLayout, SignType.cast]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Nat.zero_le _⟩, rfl, rfl⟩
  · funext j
    rw [hb1]
    change digit (startTape 0 (cell 0 pendingLayout.dir j)) = _
    rw [hcell]
    by_cases hj : j = 0
    · subst hj
      rfl
    · simp only [startTape, show (j : ℤ) ≠ 0 by omega, ↓reduceIte, hj, decide_false]
      rfl
  · funext j
    rw [hb0]
    change digit (startTape 1 (cell 0 pendingLayout.dir j)) = _
    rw [hcell]
    simp only [startTape]
    split_ifs <;> rfl
  · intro z
    change origin (startTape 0 z) = _
    simp only [startTape]
    split_ifs with hz
    · rw [decide_eq_true hz]
      rfl
    · rw [decide_eq_false hz]
      rfl
  · intro j
    change startTape 0 (cell 0 pendingLayout.dir j) = none ↔ _
    rw [hcell, Nat.size_one]
    simp only [startTape]
    constructor
    · intro h
      split_ifs at h with hj
      omega
    · intro hj
      rw [ite_eq_right (by omega)]
  · intro z
    change startTape 2 z = _
    simp only [startTape]
  · change (1 : ℤ) = _
    rw [mismatchCount_bitsAt_zero 1 width (by rw [Nat.size_one]; exact hw), pop_one]
    rfl
  · rw [Nat.size_one]
    exact hw

/-- The start configuration has both header pairs idle. -/
theorem startCfg_idle (input : List (Fin 4)) :
    IdleSize (startCfg input) ∧ IdleLength (startCfg input) :=
  ⟨⟨fun _ ↦ rfl, rfl, fun _ ↦ rfl, rfl, fun _ ↦ rfl, rfl⟩,
   ⟨fun _ ↦ rfl, rfl, fun _ ↦ rfl, rfl, fun _ ↦ rfl, rfl⟩⟩

/-- The configuration at an input boundary of the first pass. -/
structure CountRep {input : List (Fin 4)} (width : ℕ) (cfg : Cfg 9 (Fin 4) Control input)
    (t : ℕ) : Prop where
  /-- Finite control in the counting state. -/
  state : cfg.state = some stCount
  /-- The input head is past the consumed prefix. -/
  inputPos : cfg.inputPos.val = t + 1
  /-- The pending pair holds the prefix length plus one and the prefix length. -/
  pending : PairRep pendingLayout 0 width cfg (t + 1) t
  /-- The size pair is idle. -/
  size : IdleSize cfg
  /-- The length pair is idle. -/
  length : IdleLength cfg

/-- The counting state consumes a bit into the forks increment. -/
theorem step_count {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (s : Fin 4)
    (hq : cfg.state = some stCount) (hi : cfg.inputSymbol = some s) :
    machine.step cfg = readCfg cfg (stCarry 0) := by
  rw [step_of_state _ _ _ hq, hi, tr_count_some]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    rfl
  · funext i
    simp [consume, readCfg]

/-- The counting state emits nothing. -/
theorem outputSymbol_count {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (hq : cfg.state = some stCount) : machine.outputSymbol cfg = none := by
  unfold outputSymbol
  rw [hq]
  dsimp only
  cases cfg.inputSymbol
  · rw [tr_count_none]
    rfl
  · rw [tr_count_some]
    rfl

/-- Header pairs untouched by an increment stay idle. -/
theorem idle_of_untouched {input : List (Fin 4)} {cfg cfg' : Cfg 9 (Fin 4) Control input}
    (hunt : ∀ i, i ≠ (siteLayout 0).first → i ≠ (siteLayout 0).second →
      i ≠ (siteLayout 0).mism → cfg'.workTapes i = cfg.workTapes i ∧
        cfg'.workTapePos i = cfg.workTapePos i)
    (h : IdleSize cfg ∧ IdleLength cfg) : IdleSize cfg' ∧ IdleLength cfg' := by
  obtain ⟨hs3, hs4, hs5, hs6, hs7, hs8⟩ :=
    And.intro (hunt 3 (by decide) (by decide) (by decide))
      (And.intro (hunt 4 (by decide) (by decide) (by decide))
        (And.intro (hunt 5 (by decide) (by decide) (by decide))
          (And.intro (hunt 6 (by decide) (by decide) (by decide))
            (And.intro (hunt 7 (by decide) (by decide) (by decide))
              (hunt 8 (by decide) (by decide) (by decide))))))
  obtain ⟨hsize, hlen⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hs3.1]; exact hsize.register
  · rw [hs3.2]; exact hsize.registerPos
  · rw [hs4.1]; exact hsize.counter
  · rw [hs4.2]; exact hsize.counterPos
  · rw [hs5.1]; exact hsize.marker
  · rw [hs5.2]; exact hsize.mismPos
  · rw [hs6.1]; exact hlen.register
  · rw [hs6.2]; exact hlen.registerPos
  · rw [hs7.1]; exact hlen.counter
  · rw [hs7.2]; exact hlen.counterPos
  · rw [hs8.1]; exact hlen.marker
  · rw [hs8.2]; exact hlen.mismPos

/-- The heads of the idle header pairs are within any width. -/
theorem idle_headBound {input : List (Fin 4)} {cfg : Cfg 9 (Fin 4) Control input} (width : ℕ)
    (h : IdleSize cfg ∧ IdleLength cfg) (i : Fin 9)
    (hi : i ≠ (siteLayout 0).first) (hi' : i ≠ (siteLayout 0).second)
    (hi'' : i ≠ (siteLayout 0).mism) :
    -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ width := by
  obtain ⟨hsize, hlen⟩ := h
  fin_cases i
  · exact absurd rfl hi
  · exact absurd rfl hi'
  · exact absurd rfl hi''
  · change -1 ≤ cfg.workTapePos 3 ∧ cfg.workTapePos 3 ≤ width
    rw [hsize.registerPos]
    omega
  · change -1 ≤ cfg.workTapePos 4 ∧ cfg.workTapePos 4 ≤ width
    rw [hsize.counterPos]
    omega
  · change -1 ≤ cfg.workTapePos 5 ∧ cfg.workTapePos 5 ≤ width
    rw [hsize.mismPos]
    omega
  · change -1 ≤ cfg.workTapePos 6 ∧ cfg.workTapePos 6 ≤ width
    rw [hlen.registerPos]
    omega
  · change -1 ≤ cfg.workTapePos 7 ∧ cfg.workTapePos 7 ≤ width
    rw [hlen.counterPos]
    omega
  · change -1 ≤ cfg.workTapePos 8 ∧ cfg.workTapePos 8 ≤ width
    rw [hlen.mismPos]
    omega

/-- A counting boundary bounds every head. -/
theorem CountRep.headBound {input : List (Fin 4)} {width t : ℕ}
    {cfg : Cfg 9 (Fin 4) Control input} (h : CountRep width cfg t) : HeadBound width cfg := by
  intro i
  by_cases hmem : i = (siteLayout 0).first ∨ i = (siteLayout 0).second ∨ i = (siteLayout 0).mism
  · rcases hmem with rfl | rfl | rfl
    · rw [show (siteLayout 0).first = 0 from rfl,
        show cfg.workTapePos 0 = 0 from h.pending.firstPos]
      omega
    · rw [show (siteLayout 0).second = 1 from rfl,
        show cfg.workTapePos 1 = 0 from h.pending.secondPos]
      omega
    · rw [show (siteLayout 0).mism = 2 from rfl]
      exact bounds_of_mismatch (show cfg.workTapePos 2 = _ from h.pending.mismatchPos)
  · rw [not_or, not_or] at hmem
    exact idle_headBound width ⟨h.size, h.length⟩ i hmem.1 hmem.2.1 hmem.2.2

/-- One bit of the first pass: consume it, increment the forks counter, increment the leaves
counter. The cost is the summand of {name}`passOneCost`. -/
theorem configs_count_step (w : List Bool) (t : ℕ) (ht : t < w.length)
    (cfg : Cfg 9 (Fin 4) Control (w.map boolEmb)) (width : ℕ) (h : CountRep width cfg t)
    (hw1 : (t + 1 + 1).size ≤ width) :
    let cost := 1 + inc (t + 1) + inc t
    CountRep width (machine.configs cfg cost) (t + 1) ∧ machine.outputString cfg cost = [] ∧
      ∀ u ≤ cost, HeadBound width (machine.configs cfg u) := by
  have hi := inputSymbol_at w t ht cfg h.inputPos
  have hstep := step_count cfg _ h.state hi
  have hc1 : machine.configs cfg 1 = readCfg cfg (stCarry 0) := by
    rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hstep]
  have ht0 := readCfg_workTapes cfg (stCarry 0)
  have hp0 := readCfg_workTapePos cfg (stCarry 0)
  have hpend1 : PairRep pendingLayout 0 width (readCfg cfg (stCarry 0)) (t + 1) t :=
    h.pending.congr ht0 hp0
  have hw2 : (t + 1).size ≤ width := (Geb.BitTree.Counter.size_mono (Nat.le_succ _)).trans hw1
  -- the forks increment
  obtain ⟨hrep1, hstate1, hin1, hunt1, _, hout1⟩ :=
    configs_increment (readCfg cfg (stCarry 0)) 0 0 width (t + 1) t (t + 1) rfl hpend1 rfl hw1
  have hbounds1 := configs_increment_head_bounds (readCfg cfg (stCarry 0)) 0 0 width (t + 1) t
    (t + 1) rfl hpend1 rfl hw1 (by
      intro p hp
      have := Geb.BitTree.Counter.flips_bits_le_succ_size (t + 1)
      simp only [cell, siteLayout, pendingLayout, SignType.cast, Int.one_mul]
      omega)
  have hcont1 : continuation 0 (incremented 0 (t + 1) t).1 (incremented 0 (t + 1) t).2 =
      stCarry 1 := by
    simp only [continuation, incremented, siteSel, Bool.false_eq_true, ↓reduceIte, siteNext]
    rw [ite_eq_right (by omega)]
  simp only [incremented, siteSel, Bool.false_eq_true, ↓reduceIte] at hrep1
  rw [hcont1] at hstate1
  set mid := machine.configs (readCfg cfg (stCarry 0))
    (2 * Geb.BitTree.Counter.flips (t + 1).bits + 1) with hmid
  -- the leaves increment
  obtain ⟨hrep2, hstate2, hin2, hunt2, _, hout2⟩ :=
    configs_increment mid 1 0 width (t + 2) t t rfl hrep1 hstate1 hw2
  have hbounds2 := configs_increment_head_bounds mid 1 0 width (t + 2) t t rfl hrep1 hstate1 hw2
    (by
      intro p hp
      have := Geb.BitTree.Counter.flips_bits_le_succ_size t
      simp only [cell, siteLayout, pendingLayout, SignType.cast, Int.one_mul]
      omega)
  have hcont2 : continuation 1 (incremented 1 (t + 2) t).1 (incremented 1 (t + 2) t).2 =
      stCount := by
    simp only [continuation, incremented, siteSel, ↓reduceIte, siteNext]
    rw [ite_eq_right (by omega)]
  simp only [incremented, siteSel, ↓reduceIte] at hrep2
  rw [hcont2] at hstate2
  have hidle1 : IdleSize mid ∧ IdleLength mid :=
    idle_of_untouched hunt1 ⟨h.size.congr ht0 hp0, h.length.congr ht0 hp0⟩
  have hunt2' : ∀ i, i ≠ (siteLayout 0).first → i ≠ (siteLayout 0).second →
      i ≠ (siteLayout 0).mism →
      (machine.configs mid (2 * Geb.BitTree.Counter.flips t.bits + 1)).workTapes i =
        mid.workTapes i ∧
      (machine.configs mid (2 * Geb.BitTree.Counter.flips t.bits + 1)).workTapePos i =
        mid.workTapePos i := hunt2
  have hidle2 := idle_of_untouched hunt2' hidle1
  have hcost : 1 + inc (t + 1) + inc t = 1 + (2 * Geb.BitTree.Counter.flips (t + 1).bits + 1) +
      (2 * Geb.BitTree.Counter.flips t.bits + 1) := rfl
  have hmid' : machine.configs cfg (1 + (2 * Geb.BitTree.Counter.flips (t + 1).bits + 1)) =
      mid := by
    rw [configs_add, hc1]
  have hsplit : machine.configs cfg (1 + inc (t + 1) + inc t) =
      machine.configs mid (2 * Geb.BitTree.Counter.flips t.bits + 1) := by
    rw [hcost, configs_add, hmid']
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit]
    refine ⟨hstate2, ?_, hrep2, hidle2.1, hidle2.2⟩
    rw [hin2, hmid, hin1]
    change (moveInputPos cfg.inputPos 1).val = t + 1 + 1
    rw [moveInputPos_pos_val _ (by rw [h.inputPos, List.length_map]; omega), h.inputPos]
  · rw [hcost]
    refine outputString_add_nil cfg _ _ (outputString_add_nil cfg 1 _ ?_ (by rw [hc1]; exact hout1))
      (by rw [configs_add, hc1]; exact hout2)
    rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero, outputSymbol_count cfg h.state]
    rfl
  · rw [hcost]
    have hb0 : ∀ u ≤ 1, HeadBound width (machine.configs cfg u) :=
      headBound_one cfg width h.headBound (by rw [hstep]; exact h.headBound)
    have hb1 : ∀ u ≤ 2 * Geb.BitTree.Counter.flips (t + 1).bits + 1,
        HeadBound width (machine.configs (machine.configs cfg 1) u) := by
      intro u hu i
      rw [hc1]
      obtain ⟨hin', hout'⟩ := hbounds1 u hu i
      by_cases hmem : i = (siteLayout 0).first ∨ i = (siteLayout 0).second ∨
          i = (siteLayout 0).mism
      · exact hin' hmem
      · rw [not_or, not_or] at hmem
        rw [hout' hmem.1 hmem.2.1 hmem.2.2]
        exact h.headBound i
    have hb2 : ∀ u ≤ 2 * Geb.BitTree.Counter.flips t.bits + 1,
        HeadBound width (machine.configs (machine.configs cfg
          (1 + (2 * Geb.BitTree.Counter.flips (t + 1).bits + 1))) u) := by
      intro u hu i
      rw [hmid']
      obtain ⟨hin', hout'⟩ := hbounds2 u hu i
      by_cases hmem : i = (siteLayout 0).first ∨ i = (siteLayout 0).second ∨
          i = (siteLayout 0).mism
      · exact hin' hmem
      · rw [not_or, not_or] at hmem
        rw [hout' hmem.1 hmem.2.1 hmem.2.2]
        exact idle_headBound width hidle1 i hmem.1 hmem.2.1 hmem.2.2
    exact headBound_add cfg width _ _ (headBound_add cfg width 1 _ hb0 hb1) hb2

/-- The first pass up to any prefix. -/
theorem configs_count (w : List Bool) : ∀ t, t ≤ w.length →
    let cost := 1 + passOneCost t
    let start := machine.initCfg (w.map boolEmb)
    CountRep (widthOf w.length) (machine.configs start cost) t ∧
      machine.outputString start cost = [] ∧
      ∀ u ≤ cost, HeadBound (widthOf w.length) (machine.configs start u) := by
  have hw1 : 1 ≤ widthOf w.length := by unfold widthOf; omega
  refine Nat.rec ?_ ?_
  · intro _
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · change (machine.configs _ 1).state = _
      rw [configs_init]
      rfl
    · change (machine.configs _ 1).inputPos.val = _
      rw [configs_init]
      rfl
    · change PairRep _ _ _ (machine.configs _ 1) _ _
      rw [configs_init]
      exact startCfg_pairRep _ _ hw1
    · change IdleSize (machine.configs _ 1)
      rw [configs_init]
      exact (startCfg_idle _).1
    · change IdleLength (machine.configs _ 1)
      rw [configs_init]
      exact (startCfg_idle _).2
    · exact outputString_init _
    · exact headBound_init _ _ hw1
  · intro t ih ht
    obtain ⟨hrep, hout, hb⟩ := ih (by omega)
    have hwt : (t + 1 + 1).size ≤ widthOf w.length := by
      unfold widthOf
      have := Geb.BitTree.Counter.size_mono (show t + 1 + 1 ≤ 2 * w.length + 2 by omega)
      omega
    obtain ⟨hrep', hout', hb'⟩ := configs_count_step w t (by omega) _ _ hrep hwt
    have hcost : 1 + passOneCost (t + 1) = 1 + passOneCost t + (1 + inc (t + 1) + inc t) := by
      change 1 + (passOneCost t + (1 + inc (t + 1) + inc t)) = _
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [hcost, configs_add]
      exact hrep'
    · rw [hcost]
      exact outputString_add_nil _ _ _ hout hout'
    · rw [hcost]
      exact headBound_add _ _ _ _ hb hb'

/-- A configuration differing from another only in control and input position. -/
def posCfg {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (q : Control)
    (p : Fin (input.length + 2)) : Cfg 9 (Fin 4) Control input :=
  { cfg with state := some q, inputPos := p }

/-- The rewind moves left over a bit. -/
theorem step_rewind_some {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (s : Fin 4) (hq : cfg.state = some stRewind) (hi : cfg.inputSymbol = some s) :
    machine.step cfg = posCfg cfg stRewind (moveInputPos cfg.inputPos (-1)) := by
  rw [step_of_state _ _ _ hq, hi, tr_rewind_some]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    rfl
  · funext i
    simp [rewindTr, posCfg]

/-- The rewind state emits nothing. -/
theorem outputSymbol_rewind {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (hq : cfg.state = some stRewind) : machine.outputSymbol cfg = none := by
  unfold outputSymbol
  rw [hq]
  dsimp only
  cases cfg.inputSymbol
  · rw [tr_rewind_none]
    rfl
  · rw [tr_rewind_some]
    rfl

/-- The rewind from the right end: after {lit}`t` steps the input head is at position
{lit}`n - t`. -/
theorem configs_rewind (w : List Bool) (base : Cfg 9 (Fin 4) Control (w.map boolEmb)) :
    ∀ t, ∀ h : t ≤ w.length,
      machine.configs (posCfg base stRewind ⟨w.length, by simp⟩) t =
          posCfg base stRewind ⟨w.length - t, by simp; omega⟩ ∧
        machine.outputString (posCfg base stRewind ⟨w.length, by simp⟩) t = [] := by
  refine Nat.rec ?_ ?_
  · intro _
    exact ⟨rfl, rfl⟩
  · intro t ih ht
    obtain ⟨hc, ho⟩ := ih (by omega)
    have hp : (posCfg base stRewind ⟨w.length - t, by simp; omega⟩).inputPos.val =
        (w.length - (t + 1)) + 1 := by
      simp only [posCfg, Fin.val_mk]
      omega
    have hi : (posCfg base stRewind ⟨w.length - t, by simp; omega⟩).inputSymbol =
        some (boolEmb w[w.length - (t + 1)]) :=
      inputSymbol_at w (w.length - (t + 1)) (by omega) _ hp
    have hstep := step_rewind_some _ _ rfl hi
    have hmove : moveInputPos (⟨w.length - t, by simp; omega⟩ : Fin ((w.map boolEmb).length + 2))
        (-1) = ⟨w.length - (t + 1), by simp; omega⟩ := by
      apply Fin.ext
      rw [moveInputPos_neg_val _ (by change 0 < w.length - t; omega)]
      change w.length - t - 1 = w.length - (t + 1)
      omega
    refine ⟨?_, ?_⟩
    · rw [configs_succ_eq_step', hc, hstep]
      simp only [posCfg, hmove]
    · rw [outputString_succ, ho, hc, outputSymbol_rewind _ rfl]
      rfl

/-- Initialization, the first pass and the rewind reach the boundary of the initial account
with the input head on the first bit. -/
theorem configs_passOne (w : List Bool) :
    let cost := 1 + passOneCost w.length + (w.length + 2)
    let start := machine.initCfg (w.map boolEmb)
    Represents (widthOf w.length) (machine.configs start cost) (initialAccount w.length) ∧
      (machine.configs start cost).inputPos.val = 1 ∧
      machine.outputString start cost = [] ∧
      ∀ u ≤ cost, HeadBound (widthOf w.length) (machine.configs start u) := by
  obtain ⟨hrep, hout, hb⟩ := configs_count w w.length (Nat.le_refl _)
  set base := machine.configs (machine.initCfg (w.map boolEmb)) (1 + passOneCost w.length)
    with hbase
  -- the step from the right end into the rewind
  have hend : base.inputSymbol = none :=
    inputSymbol_end base (by rw [hrep.inputPos, List.length_map])
  have hstep1 : machine.step base = posCfg base stRewind ⟨w.length, by simp⟩ := by
    rw [step_of_state _ _ _ hrep.state, hend, tr_count_none]
    refine Cfg.ext rfl ?_ ?_ ?_
    · apply Fin.ext
      change (moveInputPos base.inputPos (-1)).val = w.length
      rw [moveInputPos_neg_val _ (by rw [hrep.inputPos]; omega), hrep.inputPos]
      rfl
    · funext i
      rfl
    · funext i
      simp [rewindTr, posCfg]
  obtain ⟨hrw, hrwo⟩ := configs_rewind w base w.length (Nat.le_refl _)
  simp only [Nat.sub_self] at hrw
  have hb1 : machine.configs base 1 = posCfg base stRewind ⟨w.length, by simp⟩ := by
    change machine.configs base (0 + 1) = _
    rw [configs_succ_eq_step', configs_zero, hstep1]
  have ho1 : machine.outputString base 1 = [] := by
    change machine.outputString base (0 + 1) = []
    rw [outputString_succ, configs_zero, outputSymbol_count _ hrep.state]
    rfl
  -- the step from the left end onto the first bit
  have hleft : (posCfg base stRewind ⟨0, by simp⟩).inputSymbol = none :=
    inputSymbol_start _ rfl
  have hstep2 : machine.step (posCfg base stRewind ⟨0, by simp⟩) =
      posCfg base stTree ⟨1, by simp⟩ := by
    rw [step_of_state _ _ stRewind rfl, hleft, tr_rewind_none]
    refine Cfg.ext rfl ?_ ?_ ?_
    · apply Fin.ext
      change (moveInputPos (⟨0, _⟩ : Fin _) 1).val = 1
      rw [moveInputPos_pos_val _ (by simp)]
    · funext i
      rfl
    · funext i
      simp [consume, posCfg]
  have hb3 : machine.configs (posCfg base stRewind ⟨0, by simp⟩) 1 =
      posCfg base stTree ⟨1, by simp⟩ := by
    change machine.configs _ (0 + 1) = _
    rw [configs_succ_eq_step', configs_zero, hstep2]
  have ho3 : machine.outputString (posCfg base stRewind ⟨0, by simp⟩) 1 = [] := by
    change machine.outputString _ (0 + 1) = []
    rw [outputString_succ, configs_zero, outputSymbol_rewind _ rfl]
    rfl
  have hmid : machine.configs base (1 + w.length) = posCfg base stRewind ⟨0, by simp⟩ := by
    rw [configs_add, hb1, hrw]
  have hsplit : machine.configs (machine.initCfg (w.map boolEmb))
      (1 + passOneCost w.length + (w.length + 2)) = posCfg base stTree ⟨1, by simp⟩ := by
    rw [configs_add, ← hbase]
    conv_lhs => rw [show w.length + 2 = (1 + w.length) + 1 by omega]
    rw [configs_add, hmid, hb3]
  have hw : (initialAccount w.length).forks.size + 1 ≤ widthOf w.length := by
    change (w.length + 1).size + 1 ≤ (2 * w.length + 2).size + 1
    have := Geb.BitTree.Counter.size_mono (show w.length + 1 ≤ 2 * w.length + 2 by omega)
    omega
  have ht : ∀ i, (posCfg base stTree ⟨1, by simp⟩).workTapes i = base.workTapes i := fun _ ↦ rfl
  have hp : ∀ i, (posCfg base stTree ⟨1, by simp⟩).workTapePos i = base.workTapePos i :=
    fun _ ↦ rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsplit]
    refine Represents.ofLive (n := w.length) rfl
      ⟨(hrep.pending.congr ht hp).toPairData, ?_, ?_, ?_⟩ (initialAccount_valid _) hw
    · rw [hp]
      exact hrep.pending.firstPos
    · rw [hp]
      exact hrep.pending.secondPos
    · unfold PhaseRep
      exact ⟨hrep.size.congr ht hp, hrep.length.congr ht hp⟩
  · rw [hsplit]
    rfl
  · rw [outputString_add_eq_append, hout, ← hbase]
    conv_lhs => rw [show w.length + 2 = (1 + w.length) + 1 by omega]
    rw [outputString_add_eq_append, hmid, ho3, outputString_add_eq_append, ho1, hb1, hrwo]
    rfl
  · refine headBound_add _ _ _ _ hb ?_
    rw [← hbase]
    intro u hu i
    have hbb : HeadBound (widthOf w.length) base := hrep.headBound
    by_cases hu1 : u = 0
    · subst hu1
      rw [configs_zero]
      exact hbb i
    · by_cases hu2 : u ≤ 1 + w.length
      · rw [show u = 1 + (u - 1) by omega, configs_add, hb1,
          (configs_rewind w base (u - 1) (by omega)).1]
        exact hbb i
      · have hu3 : u = 1 + w.length + 1 := by omega
        subst hu3
        rw [configs_add, hmid, hb3]
        exact hbb i

end Geb.BitTree.EliasBinary
