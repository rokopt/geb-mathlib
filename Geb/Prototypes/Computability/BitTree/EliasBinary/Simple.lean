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
# The tree and terminal phases

A fork tag increments the forks counter; a leaf tag enters the zero run; a bit after
acceptance or rejection keeps the machine rejecting. Each of these bits is one read
transition, followed by an increment at the fork tag.

## Main statements

* {lit}`configs_bit_tree` realizes a bit read in the tree state.
* {lit}`configs_bit_done` and {lit}`configs_bit_dead` realize a bit read in a terminal state.

## Tags

Turing machine, simulation, binary tree
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb)
open Geb.TreeScanner (step_of_state)

/-- A read transition changing only the finite control and the input head. -/
def readCfg {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (q : Control) :
    Cfg 9 (Fin 4) Control input :=
  { cfg with state := some q, inputPos := moveInputPos cfg.inputPos 1 }

/-- A tape-preserving read step with the given next state. -/
theorem step_read_stay {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (q q' : Control) (b : Bool) (hq : cfg.state = some q)
    (hread : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨ q = stPayloadBit ∨
      q = stDone ∨ q = stDead)
    (hi : cfg.inputSymbol = some (boolEmb b))
    (htr : scanTr q b cfg.workTapeSymbols = (q', stay)) :
    machine.step cfg = readCfg cfg q' := by
  rw [step_of_state _ _ _ hq, hi, tr_scan q hread, htr]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    rfl
  · funext i
    simp [consumeAct, stay, readCfg]

/-- A read configuration has the same tapes. -/
theorem readCfg_workTapes {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (q : Control) (i : Fin 9) : (readCfg cfg q).workTapes i = cfg.workTapes i := rfl

/-- A read configuration has the same heads. -/
theorem readCfg_workTapePos {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (q : Control) (i : Fin 9) : (readCfg cfg q).workTapePos i = cfg.workTapePos i := rfl

/-- One step realizes its empty output. -/
theorem outputString_one_read {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (q : Control) (b : Bool) (hq : cfg.state = some q)
    (hread : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨ q = stPayloadBit ∨
      q = stDone ∨ q = stDead)
    (hi : cfg.inputSymbol = some (boolEmb b)) :
    machine.outputString cfg 1 = [] := by
  rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero,
    outputSymbol_scan cfg q hq hread b hi]
  rfl

/-- Head bounds over a single transition that preserves them. -/
theorem headBound_one {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (width : ℕ)
    (h0 : HeadBound width cfg) (h1 : HeadBound width (machine.step cfg)) :
    ∀ u ≤ 1, HeadBound width (machine.configs cfg u) := by
  intro u hu
  have hu' : u = 0 ∨ u = 1 := by omega
  rcases hu' with rfl | rfl
  · exact h0
  · rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero]
    exact h1

/-- A bit read in the tree state: a fork tag increments the forks counter, a leaf tag enters
the zero run. -/
theorem configs_bit_tree {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) (b : Bool) (n width : ℕ) (hv : AccountValid n a)
    (h : Represents width cfg a) (hi : cfg.inputSymbol = some (boolEmb b))
    (hw1 : a.forks.size + 1 ≤ width) (hw2 : (a.forks + 1).size + 1 ≤ width)
    (k : ℕ) (hs : a.state = (.tree, k)) : BitSpec cfg a b width := by
  have hl := h.live (by rw [hs]; simp)
  have hph := hl.phase
  unfold PhaseRep at hph
  rw [hs] at hph
  have hq : cfg.state = some stTree := by rw [h.state, hs]; rfl
  have hread : stTree = stTree ∨ stTree = stZeros ∨ stTree = stSizeBit ∨ stTree = stLengthBit ∨
      stTree = stPayloadBit ∨ stTree = stDone ∨ stTree = stDead := Or.inl rfl
  have hcap : capped a b = false := by simp [capped, hs]
  have hpend : PairRep pendingLayout 0 width cfg a.forks a.leaves :=
    hl.pendingRep (by rw [hs]; rfl)
  have hv' := accountStep_valid n a b hv
  have hout1 := outputString_one_read cfg stTree b hq hread hi
  cases b with
  | false =>
    have hstep := step_read_stay cfg stTree stZeros false hq hread hi (by rw [scanTr_tree]; rfl)
    have hcost : macroCost a false = 1 := by simp [macroCost, hcap, hs]
    have hacc : accountStep a false = ⟨(.zeros 0, k), a.forks, a.leaves, 0⟩ := by
      simp [accountStep, hcap, hs, Elias.Scanner.step, leafEnds, nextTotal]
    have hc1 : machine.configs cfg 1 = readCfg cfg stZeros := by
      rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hstep]
    have ht := readCfg_workTapes cfg stZeros
    have hp := readCfg_workTapePos cfg stZeros
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcost, hc1, hacc]
      refine Represents.ofLive (n := n) rfl ⟨hpend.toPairData.congr ht hp, ?_, ?_, ?_⟩
        (hacc ▸ hv') hw1
      · change cfg.workTapePos 0 = 0
        rw [hl.forksPos, hs]
        rfl
      · exact hl.leavesPos
      · exact PhaseRep.congr ht hp (a := ⟨(.zeros 0, k), a.forks, a.leaves, 0⟩) (by
          unfold PhaseRep
          exact hph)
    · rw [hcost, hc1]
      rfl
    · rw [hcost]
      exact hout1
    · rw [hcost]
      exact headBound_one cfg width h.bound (by rw [hstep]; exact h.bound)
  | true =>
    have hstep := step_read_stay cfg stTree (stCarry 2) true hq hread hi
      (by rw [scanTr_tree]; rfl)
    have hcost : macroCost a true = 1 + (2 * Geb.BitTree.Counter.flips a.forks.bits + 1) := by
      simp [macroCost, hcap, hs, inc]
    have hacc : accountStep a true = ⟨(.tree, k + 1), a.forks + 1, a.leaves, 0⟩ := by
      simp [accountStep, hcap, hs, Elias.Scanner.step, leafEnds, nextTotal]
    have hc1 : machine.configs cfg 1 = readCfg cfg (stCarry 2) := by
      rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hstep]
    have ht := readCfg_workTapes cfg (stCarry 2)
    have hp := readCfg_workTapePos cfg (stCarry 2)
    have hpend' : PairRep pendingLayout 0 width (readCfg cfg (stCarry 2)) a.forks a.leaves :=
      hpend.congr ht hp
    have hle := hv.leaves_le
    have hw2' : (a.forks + 1).size ≤ width := by omega
    obtain ⟨hrep, hstate, hin, hunt, _, hout⟩ := configs_increment (readCfg cfg (stCarry 2)) 2 0
      width a.forks a.leaves a.forks rfl hpend' rfl hw2'
    have hbounds := configs_increment_head_bounds (readCfg cfg (stCarry 2)) 2 0 width a.forks
      a.leaves a.forks rfl hpend' rfl hw2' (by
        intro p hp
        have := Geb.BitTree.Counter.flips_bits_le_succ_size a.forks
        simp only [cell, siteLayout, pendingLayout, SignType.cast, Int.one_mul]
        omega)
    have hcont : continuation 2 (incremented 2 a.forks a.leaves).1
        (incremented 2 a.forks a.leaves).2 = stTree := by
      simp only [continuation, incremented, siteSel, Bool.false_eq_true, ↓reduceIte, siteNext]
      rw [ite_eq_right (by omega)]
    simp only [incremented, siteSel, Bool.false_eq_true, ↓reduceIte] at hrep
    rw [hcont] at hstate
    have hcadd : machine.configs cfg (1 + (2 * Geb.BitTree.Counter.flips a.forks.bits + 1)) =
        machine.configs (readCfg cfg (stCarry 2))
          (2 * Geb.BitTree.Counter.flips a.forks.bits + 1) := by
      rw [configs_add, hc1]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcost, hcadd, hacc]
      refine Represents.ofLive (n := n) hstate ⟨hrep.toPairData, ?_, ?_, ?_⟩ (hacc ▸ hv') hw2
      · change _ = (0 : ℤ)
        exact hrep.firstPos
      · exact hrep.secondPos
      · unfold PhaseRep
        dsimp only
        obtain ⟨hs3, hs4, hs5, hs6, hs7, hs8⟩ :=
          And.intro (hunt 3 (by decide) (by decide) (by decide))
            (And.intro (hunt 4 (by decide) (by decide) (by decide))
              (And.intro (hunt 5 (by decide) (by decide) (by decide))
                (And.intro (hunt 6 (by decide) (by decide) (by decide))
                  (And.intro (hunt 7 (by decide) (by decide) (by decide))
                    (hunt 8 (by decide) (by decide) (by decide))))))
        obtain ⟨hsize, hlen⟩ := hph
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
    · rw [hcost, hcadd, hin]
      rfl
    · rw [hcost]
      exact outputString_add_nil cfg 1 _ hout1 (by rw [hc1]; exact hout)
    · rw [hcost]
      refine headBound_add cfg width 1 _ (headBound_one cfg width h.bound (by
        rw [hstep]; exact h.bound)) ?_
      intro u hu i
      rw [hc1]
      obtain ⟨hin', hout'⟩ := hbounds u hu i
      by_cases hmem : i = (siteLayout 2).first ∨ i = (siteLayout 2).second ∨
          i = (siteLayout 2).mism
      · exact hin' hmem
      · rw [not_or, not_or] at hmem
        rw [hout' hmem.1 hmem.2.1 hmem.2.2]
        exact h.bound i

/-- A bit read after acceptance rejects. -/
theorem configs_bit_done {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) (b : Bool) (width : ℕ)
    (h : Represents width cfg a) (hi : cfg.inputSymbol = some (boolEmb b))
    (k : ℕ) (hs : a.state = (.done, k)) : BitSpec cfg a b width := by
  have hq : cfg.state = some stDone := by rw [h.state, hs]; rfl
  have hread : stDone = stTree ∨ stDone = stZeros ∨ stDone = stSizeBit ∨ stDone = stLengthBit ∨
      stDone = stPayloadBit ∨ stDone = stDone ∨ stDone = stDead := by simp
  have hcap : capped a b = false := by simp [capped, hs]
  have hstep := step_read_stay cfg stDone stDead b hq hread hi (by rw [scanTr_done])
  have hcost : macroCost a b = 1 := by simp [macroCost, hcap, hs]
  have hacc : accountStep a b = ⟨(.dead, k), a.forks, a.leaves, 0⟩ := by
    simp [accountStep, hcap, hs, Elias.Scanner.step, leafEnds, nextTotal]
  have hc1 : machine.configs cfg 1 = readCfg cfg stDead := by
    rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hstep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcost, hc1, hacc]
    exact Represents.dead rfl rfl h.bound
  · rw [hcost, hc1]
    rfl
  · rw [hcost]
    exact outputString_one_read cfg stDone b hq hread hi
  · rw [hcost]
    exact headBound_one cfg width h.bound (by rw [hstep]; exact h.bound)

/-- A bit read after rejection keeps rejecting. -/
theorem configs_bit_dead {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) (b : Bool) (width : ℕ)
    (h : Represents width cfg a) (hi : cfg.inputSymbol = some (boolEmb b))
    (k : ℕ) (hs : a.state = (.dead, k)) : BitSpec cfg a b width := by
  have hq : cfg.state = some stDead := by rw [h.state, hs]; rfl
  have hread : stDead = stTree ∨ stDead = stZeros ∨ stDead = stSizeBit ∨ stDead = stLengthBit ∨
      stDead = stPayloadBit ∨ stDead = stDone ∨ stDead = stDead := by simp
  have hcap : capped a b = false := by simp [capped, hs]
  have hstep := step_read_stay cfg stDead stDead b hq hread hi (by rw [scanTr_dead])
  have hcost : macroCost a b = 1 := by simp [macroCost, hcap, hs]
  have hacc : accountStep a b = ⟨(.dead, k), a.forks, a.leaves, 0⟩ := by
    simp [accountStep, hcap, hs, Elias.Scanner.step, leafEnds, nextTotal]
  have hc1 : machine.configs cfg 1 = readCfg cfg stDead := by
    rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hstep]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcost, hc1, hacc]
    exact Represents.dead rfl rfl h.bound
  · rw [hcost, hc1]
    rfl
  · rw [hcost]
    exact outputString_one_read cfg stDead b hq hread hi
  · rw [hcost]
    exact headBound_one cfg width h.bound (by rw [hstep]; exact h.bound)

end Geb.BitTree.EliasBinary
