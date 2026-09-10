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
# The zero run of a delta header

In the zero-run state the forks head is the ruler: each zero moves it one cell up the forks
counter, and a zero beyond the counter's digits abandons the scan. A one at the origin ends a
leaf and increments the leaves counter; a one at cell {lit}`z` starts a size field, walking
the ruler head back to the origin while the size register head advances to cell {lit}`z`,
then writing the leading one of the register and the one of its counter.

## Main definitions

* {lit}`setupCfg` is the configuration during the size setup walk.
* {lit}`sizeStartCfg` is the configuration at the start of a size field.

## Main statements

* {lit}`configs_setup` describes the size setup walk.
* {lit}`configs_zeros_size` executes the start of a size field.
* {lit}`configs_bit_zeros` realizes one input bit of the zero-run phase.

## Tags

Turing machine, simulation, Elias delta code, zero run
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.Elias.Scanner
open Geb.BitTree.BinaryMachine (boolEmb digit origin mismatchCount flipAt bitsAt
  bitsAt_eq_testBit mismatchCount_flip_left mismatchCount_flip_right mismatchCount_eq_zero)
open Geb.BitTree.Counter (flips)
open Geb.TreeScanner (step_of_state)

/-! ## Single transitions -/

section Steps

variable {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)

/-- A zero over a blank ruler cell abandons the scan. -/
theorem step_zeros_dead (hq : cfg.state = some stZeros)
    (hi : cfg.inputSymbol = some (boolEmb false)) (hw : cfg.workTapeSymbols 0 = none) :
    machine.step cfg =
      { cfg with
        state := some stDead
        inputPos := moveInputPos cfg.inputPos 1 } := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stZeros (by simp), scanTr_zeros]
  simp only [Bool.false_eq_true, ↓reduceIte, hw]
  apply Cfg.ext <;> simp [consumeAct, stay]

/-- A zero over a digit of the ruler moves the forks head one cell up. -/
theorem step_zeros_next (hq : cfg.state = some stZeros)
    (hi : cfg.inputSymbol = some (boolEmb false)) (hw : cfg.workTapeSymbols 0 ≠ none) :
    machine.step cfg =
      { cfg with
        inputPos := moveInputPos cfg.inputPos 1
        workTapePos := Function.update cfg.workTapePos 0 (cfg.workTapePos 0 + 1) } := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stZeros (by simp), scanTr_zeros]
  simp only [Bool.false_eq_true, ↓reduceIte, hw]
  apply Cfg.ext
  · exact hq.symm
  · rfl
  · rfl
  · funext i
    simp only [consumeAct, Function.update_apply]
    split_ifs with h
    · subst h
      simp
    · simp

/-- A one at the tagged origin starts the leaves increment. -/
theorem step_zeros_carry (hq : cfg.state = some stZeros)
    (hi : cfg.inputSymbol = some (boolEmb true)) (ho : origin (cfg.workTapeSymbols 0) = true) :
    machine.step cfg =
      { cfg with
        state := some (stCarry 3)
        inputPos := moveInputPos cfg.inputPos 1 } := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stZeros (by simp), scanTr_zeros]
  simp only [↓reduceIte, ho]
  apply Cfg.ext <;> simp [consumeAct, stay]

/-- A one away from the origin starts the size setup. -/
theorem step_zeros_setup (hq : cfg.state = some stZeros)
    (hi : cfg.inputSymbol = some (boolEmb true)) (ho : origin (cfg.workTapeSymbols 0) = false) :
    machine.step cfg =
      { cfg with
        state := some stSizeSetup
        inputPos := moveInputPos cfg.inputPos 1 } := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stZeros (by simp), scanTr_zeros]
  simp only [↓reduceIte, ho, Bool.false_eq_true]
  apply Cfg.ext <;> simp [consumeAct, stay]

/-- Away from the origin, the size setup moves the forks head down and the size head up. -/
theorem step_setup_pos (hq : cfg.state = some stSizeSetup)
    (ho : origin (cfg.workTapeSymbols 0) = false) :
    machine.step cfg =
      { cfg with
        workTapePos := fun i ↦
          if i = 0 then cfg.workTapePos 0 - 1
          else if i = 3 then cfg.workTapePos 3 + 1 else cfg.workTapePos i } := by
  rw [step_of_state _ _ _ hq, tr_phase stSizeSetup (by simp), phaseTr_sizeSetup]
  simp only [ho, Bool.false_eq_true, ↓reduceIte]
  apply Cfg.ext
  · exact hq.symm
  · exact moveInputPos_zero _
  · rfl
  · funext i
    simp only [act]
    split_ifs with h0 h3
    · subst h0
      simp
      omega
    · subst h3
      simp
    · simp

/-- At the origin, the size setup writes the leading one of the size register, moving that
head down and the size mismatch head up. -/
theorem step_setup_zero (hq : cfg.state = some stSizeSetup)
    (ho : origin (cfg.workTapeSymbols 0) = true) :
    machine.step cfg =
      { cfg with
        state := some stSizeInit
        workTapes := Function.update cfg.workTapes 3
          (Function.update (cfg.workTapes 3) (cfg.workTapePos 3) (some 1))
        workTapePos := fun i ↦
          if i = 3 then cfg.workTapePos 3 - 1
          else if i = 5 then cfg.workTapePos 5 + 1 else cfg.workTapePos i } := by
  rw [step_of_state _ _ _ hq, tr_phase stSizeSetup (by simp), phaseTr_sizeSetup]
  simp only [ho, ↓reduceIte]
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    simp only [act, Function.update_apply]
    split_ifs with h3 h5
    · subst h3
      rfl
    · subst h5
      rfl
    · rfl
  · funext i
    simp only [act]
    split_ifs with h3 h5
    · subst h3
      simp
      omega
    · subst h5
      simp
    · simp

/-- The size initialization writes the one of the size counter and moves the size mismatch
head up. -/
theorem step_sizeInit (hq : cfg.state = some stSizeInit) :
    machine.step cfg =
      { cfg with
        state := some stSizeBit
        workTapes := Function.update cfg.workTapes 4
          (Function.update (cfg.workTapes 4) (cfg.workTapePos 4) (some 1))
        workTapePos := Function.update cfg.workTapePos 5 (cfg.workTapePos 5 + 1) } := by
  rw [step_of_state _ _ _ hq, tr_phase stSizeInit (by simp), phaseTr_sizeInit]
  apply Cfg.ext
  · rfl
  · exact moveInputPos_zero _
  · funext i
    simp only [act, Function.update_apply]
    split_ifs with h4 h5
    · subst h4
      rfl
    · subst h5
      rfl
    · rfl
  · funext i
    simp only [act, Function.update_apply]
    split_ifs with h4 h5 h5'
    · exact absurd (h4.symm.trans h5) (by decide)
    · simp
    · subst h5'
      simp
    · simp

end Steps

/-! ## The size setup -/

section Setup

variable {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)

/-- The configuration after {lit}`t` steps of the size setup from a forks head at cell
{lit}`z`: the forks head has moved {lit}`t` cells down and the size register head {lit}`t`
cells up from the origin. -/
def setupCfg (z t : ℕ) : Cfg 9 (Fin 4) Control input where
  state := some stSizeSetup
  inputPos := cfg.inputPos
  workTapes := cfg.workTapes
  workTapePos i := if i = 0 then ((z - t : ℕ) : ℤ) else if i = 3 then (t : ℤ) else cfg.workTapePos i

/-- The size setup walks the forks head to the origin and the size register head to the
zero count, emitting nothing. -/
theorem configs_setup (hq : cfg.state = some stSizeSetup)
    (ho : ∀ w, origin (cfg.workTapes 0 w) = decide (w = 0)) (z : ℕ)
    (hp0 : cfg.workTapePos 0 = z) (hp3 : cfg.workTapePos 3 = 0) (t : ℕ) (ht : t ≤ z) :
    machine.configs cfg t = setupCfg cfg z t ∧ machine.outputString cfg t = [] := by
  revert ht
  refine Nat.rec ?_ ?_ t
  · intro _
    refine ⟨?_, rfl⟩
    rw [configs_zero]
    refine Cfg.ext hq rfl rfl ?_
    funext i
    simp only [setupCfg]
    split_ifs with h0 h3
    · subst h0
      simp [hp0]
    · subst h3
      simp [hp3]
    · rfl
  · intro t ih ht
    obtain ⟨hc, hout⟩ := ih (by omega)
    have hor : origin ((setupCfg cfg z t).workTapeSymbols 0) = false := by
      simp only [Cfg.workTapeSymbols, setupCfg, ↓reduceIte, ho, decide_eq_false_iff_not]
      omega
    constructor
    · rw [configs_succ_eq_step', hc, step_setup_pos _ rfl hor]
      refine Cfg.ext rfl rfl rfl ?_
      funext i
      simp only [setupCfg]
      split_ifs with h0 h3 h30
      · omega
      · exact absurd h30 (by decide)
      · simp
      · rfl
    · rw [outputString_succ, hout, hc, outputSymbol_phase _ stSizeSetup rfl (by simp)]
      rfl

/-- The configuration at the start of a size field of zero count {lit}`z`: the forks head
at the origin, the leading one of the size register at cell {lit}`z` with its head one cell
below, the one of the size counter at the origin, and the size mismatch head at two. -/
def sizeStartCfg (z : ℕ) : Cfg 9 (Fin 4) Control input where
  state := some stSizeBit
  inputPos := moveInputPos cfg.inputPos 1
  workTapes i :=
    if i = 3 then Function.update (cfg.workTapes 3) z (some 1)
    else if i = 4 then Function.update (cfg.workTapes 4) 0 (some 1) else cfg.workTapes i
  workTapePos i :=
    if i = 0 then 0 else if i = 3 then (z : ℤ) - 1 else if i = 5 then 2 else cfg.workTapePos i

/-- From a one read at cell {lit}`z` of the ruler, the size setup and initialization reach
the start of the size field in {lit}`z + 3` steps, emitting nothing and keeping every head
within the width. -/
theorem configs_zeros_size (hq : cfg.state = some stZeros)
    (hi : cfg.inputSymbol = some (boolEmb true))
    (ho : ∀ w, origin (cfg.workTapes 0 w) = decide (w = 0)) (z : ℕ) (hz : z ≠ 0)
    (hp0 : cfg.workTapePos 0 = z) (hp3 : cfg.workTapePos 3 = 0) (hp4 : cfg.workTapePos 4 = 0)
    (hp5 : cfg.workTapePos 5 = 0) (width : ℕ) (hb : HeadBound width cfg) (hzw : z < width) :
    machine.configs cfg (z + 3) = sizeStartCfg cfg z ∧
      machine.outputString cfg (z + 3) = [] ∧
      ∀ u ≤ z + 3, HeadBound width (machine.configs cfg u) := by
  have hor : origin (cfg.workTapeSymbols 0) = false := by
    simp only [Cfg.workTapeSymbols, hp0, ho, decide_eq_false_iff_not]
    omega
  set cfg1 : Cfg 9 (Fin 4) Control input :=
    { cfg with
      state := some stSizeSetup
      inputPos := moveInputPos cfg.inputPos 1 } with hcfg1
  have hc1 : machine.configs cfg 1 = cfg1 := by
    rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero,
      step_zeros_setup cfg hq hi hor]
  have ho1 : machine.outputString cfg 1 = [] := by
    rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero,
      outputSymbol_scan cfg stZeros hq (by simp) true hi]
    rfl
  have hwalk := configs_setup cfg1 rfl ho z hp0 hp3
  obtain ⟨hc2, ho2⟩ := hwalk z (Nat.le_refl z)
  set cfg2 := setupCfg cfg1 z z with hcfg2
  have hor2 : origin (cfg2.workTapeSymbols 0) = true := by
    change origin (cfg.workTapes 0 ((z - z : ℕ) : ℤ)) = true
    rw [ho]
    simp
  have hc3 := step_setup_zero cfg2 rfl hor2
  set cfg3 := machine.step cfg2 with hcfg3
  have hc4 := step_sizeInit cfg3 (by rw [hc3])
  have hc2' : machine.configs cfg (1 + z) = cfg2 := by rw [configs_add, hc1, hc2]
  have hc3' : machine.configs cfg (1 + z + 1) = cfg3 := by rw [configs_succ_eq_step', hc2']
  have hfinal : machine.configs cfg (z + 3) = sizeStartCfg cfg z := by
    rw [show z + 3 = 1 + z + 1 + 1 by omega, configs_succ_eq_step', hc3', hc4, hc3]
    refine Cfg.ext rfl rfl ?_ ?_ <;> funext i <;> fin_cases i <;>
      simp [sizeStartCfg, hcfg2, setupCfg, hcfg1, hp4, hp5]
  have h23 : cfg2.workTapePos 3 = z := rfl
  have h25 : cfg2.workTapePos 5 = cfg.workTapePos 5 := rfl
  have h2i : ∀ i, cfg2.workTapePos i =
      if i = 0 then ((z - z : ℕ) : ℤ) else if i = 3 then (z : ℤ) else cfg.workTapePos i :=
    fun _ ↦ rfl
  refine ⟨hfinal, ?_, ?_⟩
  · rw [show z + 3 = 1 + z + 1 + 1 by omega, outputString_succ, outputString_succ, hc3', hc2',
      outputString_add_eq_append, ho1, hc1, ho2, outputSymbol_phase cfg2 stSizeSetup rfl (by simp),
      outputSymbol_phase cfg3 stSizeInit (by rw [hc3]) (by simp)]
    rfl
  · intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      rw [configs_zero]
      exact hb
    · by_cases hu1 : u ≤ z + 1
      · rw [show u = 1 + (u - 1) by omega, configs_add, hc1, (hwalk (u - 1) (by omega)).1]
        intro i
        simp only [setupCfg]
        split_ifs
        · omega
        · omega
        · exact hb i
      · have hu' : u = z + 2 ∨ u = z + 3 := by omega
        rcases hu' with rfl | rfl
        · rw [show z + 2 = 1 + z + 1 by omega, hc3', hc3]
          intro i
          dsimp only
          rw [h23, h25, h2i i, hp5]
          split_ifs
          · omega
          · omega
          · omega
          · exact hb i
        · rw [hfinal]
          intro i
          simp only [sizeStartCfg]
          split_ifs
          · omega
          · omega
          · omega
          · exact hb i

/-- The start of a size field represents the account entering the size phase. -/
theorem sizeStartCfg_represents (a : Account) (z k n width : ℕ)
    (hv : AccountValid n ⟨(.size z 1, k), a.forks, a.leaves, 0⟩) (hl : LiveRep width cfg a)
    (hs : a.state = (.zeros z, k)) (hz : z ≠ 0) (hzw : z < width)
    (hw1 : a.forks.size + 1 ≤ width) :
    Represents width (sizeStartCfg cfg z) ⟨(.size z 1, k), a.forks, a.leaves, 0⟩ := by
  have hph := hl.phase
  unfold PhaseRep at hph
  rw [hs] at hph
  obtain ⟨his, hil⟩ := hph
  have hp := hl.pending
  have hf0 : ∀ j, digitsFrom cfg 3 0 1 j = false := by
    intro j
    simp only [digitsFrom]
    rw [his.register]
    split_ifs <;> rfl
  have hg0 : ∀ j, digitsFrom cfg 4 0 1 j = false := by
    intro j
    simp only [digitsFrom]
    rw [his.counter]
    rfl
  have hcell : ∀ j : ℕ, cell 0 1 j = (j : ℤ) := fun j ↦ by simp [cell]
  have hf : digitsFrom (sizeStartCfg cfg z) 3 0 1 = flipAt (digitsFrom cfg 3 0 1) z := by
    funext j
    simp only [flipAt, Function.update_apply, hf0, Bool.not_false]
    change digit (Function.update (cfg.workTapes 3) z (some 1) (cell 0 1 j)) = _
    rw [Function.update_apply, hcell]
    by_cases hj : j = z
    · rw [ite_eq_left (by rw [hj]), ite_eq_left hj]
      rfl
    · rw [ite_eq_right (by exact_mod_cast hj), ite_eq_right hj, ← hcell]
      exact hf0 j
  have hg : digitsFrom (sizeStartCfg cfg z) 4 0 1 = flipAt (digitsFrom cfg 4 0 1) 0 := by
    funext j
    simp only [flipAt, Function.update_apply, hg0, Bool.not_false]
    change digit (Function.update (cfg.workTapes 4) 0 (some 1) (cell 0 1 j)) = _
    rw [Function.update_apply, hcell]
    by_cases hj : j = 0
    · rw [ite_eq_left (by rw [hj]; rfl), ite_eq_left hj]
      rfl
    · rw [ite_eq_right (by exact_mod_cast hj), ite_eq_right hj, ← hcell]
      exact hg0 j
  refine Represents.ofLive rfl ⟨?_, rfl, hl.leavesPos, ?_⟩ hv hw1
  · exact ⟨hp.firstDigits, hp.secondDigits, hp.originTag, hp.firstBlank, hp.marker,
      hp.mismatchPos, hp.firstSize, hp.secondSize⟩
  · change SizeRead width (sizeStartCfg cfg z) z 1 ∧ IdleLength (sizeStartCfg cfg z)
    refine ⟨⟨?_, rfl, ?_, his.counterPos, his.marker, ?_⟩,
      ⟨hil.register, hil.registerPos, hil.counter, hil.counterPos, hil.marker, hil.mismPos⟩⟩
    · intro w
      change Function.update (cfg.workTapes 3) z (some 1) w = _
      rw [Function.update_apply, Nat.size_one, Nat.cast_one]
      by_cases hw : w = z
      · rw [ite_eq_left hw, hw, ite_eq_right (by exact_mod_cast hz),
          ite_eq_left ⟨Int.le_refl _, by omega⟩, sub_self, Int.toNat_zero, bitsAt_eq_testBit]
        rfl
      · rw [ite_eq_right hw, his.register w]
        by_cases h0 : w = 0
        · rw [ite_eq_left h0, ite_eq_left h0]
        · rw [ite_eq_right h0, ite_eq_right h0, ite_eq_right (by omega)]
    · intro w
      change Function.update (cfg.workTapes 4) 0 (some 1) w = _
      rw [Function.update_apply, his.counter w]
    · change (2 : ℤ) = _
      rw [hf, hg, mismatchCount_flip_left width z _ _ hzw,
        mismatchCount_flip_right width 0 _ _ (by omega),
        (mismatchCount_eq_zero width _ _).mpr (fun i _ ↦ by rw [hf0, hg0])]
      simp only [hf0, hg0, flipAt, Function.update_apply, hz, ↓reduceIte, Bool.not_false,
        Nat.cast_zero]
      omega

end Setup

/-! ## One input bit -/

/-- One input bit in the zero-run phase realizes its account update in its macro cost. -/
theorem configs_bit_zeros {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) (b : Bool) (n width : ℕ) (hv : AccountValid n a)
    (h : Represents width cfg a) (hi : cfg.inputSymbol = some (boolEmb b))
    (hw1 : a.forks.size + 1 ≤ width) (hw3 : (a.leaves + 1).size ≤ width)
    (z k : ℕ) (hs : a.state = (.zeros z, k)) : BitSpec cfg a b width := by
  have hl : LiveRep width cfg a := h.live (by rw [hs]; simp)
  have hq : cfg.state = some stZeros := by rw [h.state, hs]; rfl
  have hph := hl.phase
  unfold PhaseRep at hph
  rw [hs] at hph
  obtain ⟨his, hil⟩ := hph
  have hp0 : cfg.workTapePos 0 = z := by rw [hl.forksPos, hs]; rfl
  have hrp : z ≤ a.forks.size := by
    have := hv.rulerPos_le
    rw [hs] at this
    exact this
  have ho : ∀ w, origin (cfg.workTapes 0 w) = decide (w = 0) := hl.pending.originTag
  have hblank : cfg.workTapes 0 z = none ↔ a.forks.size ≤ z := by
    have := hl.pending.firstBlank z
    simp only [cell, pendingLayout, SignType.coe_one, one_mul, zero_add] at this
    exact this
  have hk : k + a.leaves = a.forks := by
    have := hv.pending (by rw [hs]; simp)
    rw [hs] at this
    exact this
  have hc1 : machine.configs cfg 1 = machine.step cfg := by
    rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero]
  have ho1 : machine.outputString cfg 1 = [] := by
    rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero,
      outputSymbol_scan cfg stZeros hq (by simp) b hi]
    rfl
  cases b with
  | false =>
    by_cases hcap : a.forks.size ≤ z
    · have hc : capped a false = true := by simp [capped, hs, hcap]
      have hcost : macroCost a false = 1 := by simp [macroCost, hc]
      have hacc : accountStep a false = ⟨(.dead, 0), a.forks, a.leaves, 0⟩ := by
        simp [accountStep, hc]
      have hw : cfg.workTapeSymbols 0 = none := by
        change cfg.workTapes 0 (cfg.workTapePos 0) = none
        rw [hp0]
        exact hblank.mpr hcap
      unfold BitSpec
      rw [hcost, hacc, hc1, step_zeros_dead cfg hq hi hw]
      refine ⟨Represents.dead rfl rfl h.bound, rfl, ho1, ?_⟩
      intro u hu
      have hu' : u = 0 ∨ u = 1 := by omega
      rcases hu' with rfl | rfl
      · rw [configs_zero]
        exact h.bound
      · rw [hc1, step_zeros_dead cfg hq hi hw]
        exact h.bound
    · have hc : capped a false = false := by simp [capped, hs, hcap]
      have hcost : macroCost a false = 1 := by simp [macroCost, hc, hs]
      have hacc : accountStep a false = ⟨(.zeros (z + 1), k), a.forks, a.leaves, 0⟩ := by
        simp [accountStep, hc, hs, Elias.Scanner.step, leafEnds, nextTotal]
      have hw : cfg.workTapeSymbols 0 ≠ none := by
        change cfg.workTapes 0 (cfg.workTapePos 0) ≠ none
        rw [hp0]
        intro he
        exact hcap (hblank.mp he)
      have hv' := accountStep_valid n a false hv
      rw [hacc] at hv'
      have hpos : ∀ i, i ≠ 0 →
          Function.update cfg.workTapePos 0 (cfg.workTapePos 0 + 1) i = cfg.workTapePos i :=
        fun i hi ↦ Function.update_of_ne hi _ _
      have hstep := step_zeros_next cfg hq hi hw
      unfold BitSpec
      rw [hcost, hacc, hc1, hstep]
      refine ⟨Represents.ofLive hq ⟨?_, ?_, ?_, ?_⟩ hv' hw1, rfl, ho1, ?_⟩
      · have hp := hl.pending
        refine ⟨hp.firstDigits, hp.secondDigits, hp.originTag, hp.firstBlank, hp.marker, ?_,
          hp.firstSize, hp.secondSize⟩
        exact (hpos 2 (by decide)).trans hp.mismatchPos
      · change Function.update cfg.workTapePos 0 (cfg.workTapePos 0 + 1) 0 = _
        rw [Function.update_self, hp0]
        push_cast
        rfl
      · exact (hpos 1 (by decide)).trans hl.leavesPos
      · change IdleSize _ ∧ IdleLength _
        exact ⟨⟨his.register, (hpos 3 (by decide)).trans his.registerPos, his.counter,
          (hpos 4 (by decide)).trans his.counterPos, his.marker,
          (hpos 5 (by decide)).trans his.mismPos⟩,
          ⟨hil.register, (hpos 6 (by decide)).trans hil.registerPos, hil.counter,
          (hpos 7 (by decide)).trans hil.counterPos, hil.marker,
          (hpos 8 (by decide)).trans hil.mismPos⟩⟩
      · intro u hu
        have hu' : u = 0 ∨ u = 1 := by omega
        rcases hu' with rfl | rfl
        · rw [configs_zero]
          exact h.bound
        · rw [hc1, hstep]
          intro i
          dsimp only
          by_cases hi : i = 0
          · subst hi
            rw [Function.update_self, hp0]
            omega
          · rw [hpos i hi]
            exact h.bound i
  | true =>
    have hc : capped a true = false := by simp [capped, hs]
    by_cases hz : z = 0
    · subst hz
      have hcost : macroCost a true = 1 + (2 * flips a.leaves.bits + 1) := by
        simp [macroCost, hc, hs, inc]
      have hacc : accountStep a true = ⟨Elias.Scanner.finish k, a.forks, a.leaves + 1, 0⟩ := by
        simp [accountStep, hc, hs, Elias.Scanner.step, leafEnds, nextTotal]
      have hv' := accountStep_valid n a true hv
      rw [hacc] at hv'
      have hor : origin (cfg.workTapeSymbols 0) = true := by
        change origin (cfg.workTapes 0 (cfg.workTapePos 0)) = true
        rw [hp0, ho]
        simp
      set cfg1 : Cfg 9 (Fin 4) Control input :=
        { cfg with
          state := some (stCarry 3)
          inputPos := moveInputPos cfg.inputPos 1 } with hcfg1
      have hc1' : machine.configs cfg 1 = cfg1 := by rw [hc1, step_zeros_carry cfg hq hi hor]
      have hpair : PairRep pendingLayout 0 width cfg1 a.forks a.leaves := by
        have hp := hl.pendingRep (by rw [hs]; rfl)
        exact ⟨⟨hp.firstDigits, hp.secondDigits, hp.originTag, hp.firstBlank, hp.marker,
          hp.mismatchPos, hp.firstSize, hp.secondSize⟩, hp.firstPos, hp.secondPos⟩
      obtain ⟨hrep, hstate, hin, hunt, _, hout⟩ :=
        configs_increment cfg1 3 0 width a.forks a.leaves a.leaves rfl hpair rfl hw3
      set now := machine.configs cfg1 (2 * flips a.leaves.bits + 1) with hnow
      have hrep' : PairRep pendingLayout 0 width now a.forks (a.leaves + 1) := hrep
      have hst : continuation 3 a.forks (a.leaves + 1) =
          phaseState (Elias.Scanner.finish k) := by
        unfold continuation Elias.Scanner.finish
        by_cases hk1 : k = 1
        · rw [ite_eq_left (by omega), ite_eq_left hk1]
          rfl
        · rw [ite_eq_right (by omega), ite_eq_right hk1]
          rfl
      have hr : rulerPos (Elias.Scanner.finish k) = 0 := by
        unfold Elias.Scanner.finish
        split <;> rfl
      have hu : ∀ i : Fin 9, 3 ≤ i.val →
          now.workTapes i = cfg.workTapes i ∧ now.workTapePos i = cfg.workTapePos i := by
        intro i hi
        exact hunt i (fun he ↦ by subst he; exact absurd hi (by decide))
          (fun he ↦ by subst he; exact absurd hi (by decide))
          (fun he ↦ by subst he; exact absurd hi (by decide))
      have hph' : IdleSize now ∧ IdleLength now := by
        refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
        · rw [(hu 3 (by decide)).1]
          exact his.register
        · rw [(hu 3 (by decide)).2]
          exact his.registerPos
        · rw [(hu 4 (by decide)).1]
          exact his.counter
        · rw [(hu 4 (by decide)).2]
          exact his.counterPos
        · rw [(hu 5 (by decide)).1]
          exact his.marker
        · rw [(hu 5 (by decide)).2]
          exact his.mismPos
        · rw [(hu 6 (by decide)).1]
          exact hil.register
        · rw [(hu 6 (by decide)).2]
          exact hil.registerPos
        · rw [(hu 7 (by decide)).1]
          exact hil.counter
        · rw [(hu 7 (by decide)).2]
          exact hil.counterPos
        · rw [(hu 8 (by decide)).1]
          exact hil.marker
        · rw [(hu 8 (by decide)).2]
          exact hil.mismPos
      have hcell : ∀ p, p ≤ flips a.leaves.bits →
          -1 ≤ cell 0 (siteLayout 3).dir p ∧ cell 0 (siteLayout 3).dir p ≤ width := by
        intro p hp
        have := (Geb.BitTree.Counter.flips_bits_le_succ_size a.leaves).trans hw3
        change -1 ≤ cell 0 1 p ∧ cell 0 1 p ≤ width
        simp only [cell, SignType.coe_one, one_mul, zero_add]
        omega
      have hbounds : ∀ u ≤ 2 * flips a.leaves.bits + 1,
          HeadBound width (machine.configs cfg1 u) := by
        intro u hu i
        obtain ⟨hin', hout'⟩ := configs_increment_head_bounds cfg1 3 0 width a.forks a.leaves
          a.leaves rfl hpair rfl hw3 hcell u hu i
        by_cases hi : i = (siteLayout 3).first ∨ i = (siteLayout 3).second ∨
          i = (siteLayout 3).mism
        · exact hin' hi
        · push Not at hi
          rw [hout' hi.1 hi.2.1 hi.2.2]
          exact h.bound i
      have hh : ∀ u ≤ 1, HeadBound width (machine.configs cfg u) := by
        intro u hu
        have hu' : u = 0 ∨ u = 1 := by omega
        rcases hu' with rfl | rfl
        · rw [configs_zero]
          exact h.bound
        · rw [hc1']
          exact h.bound
      unfold BitSpec
      rw [hcost, hacc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [configs_add, hc1']
        refine Represents.ofLive (hstate.trans (congrArg some hst)) ⟨hrep'.toPairData, ?_, ?_, ?_⟩
          hv' hw1
        · change now.workTapePos 0 = _
          rw [hr, Nat.cast_zero]
          exact hrep'.firstPos
        · exact hrep'.secondPos
        · change PhaseRep width now ⟨Elias.Scanner.finish k, a.forks, a.leaves + 1, 0⟩
          by_cases hk1 : k = 1
          · rw [Elias.Scanner.finish, ite_eq_left hk1]
            exact hph'
          · rw [Elias.Scanner.finish, ite_eq_right hk1]
            exact hph'
      · rw [configs_add, hc1']
        exact hin
      · rw [outputString_add_eq_append, ho1, hc1', hout]
        rfl
      · refine headBound_add cfg width 1 _ hh ?_
        intro u hu
        rw [hc1']
        exact hbounds u hu
    · have hcost : macroCost a true = z + 3 := by simp [macroCost, hc, hs, hz]
      have hacc : accountStep a true = ⟨(.size z 1, k), a.forks, a.leaves, 0⟩ := by
        simp [accountStep, hc, hs, Elias.Scanner.step, hz, leafEnds, nextTotal]
      have hv' := accountStep_valid n a true hv
      rw [hacc] at hv'
      have hzw : z < width := by omega
      obtain ⟨hfinal, hout, hbounds⟩ := configs_zeros_size cfg hq hi ho z hz hp0 his.registerPos
        his.counterPos his.mismPos width h.bound hzw
      unfold BitSpec
      rw [hcost, hacc, hfinal]
      exact ⟨sizeStartCfg_represents cfg a z k n width hv' hl hs hz hzw hw1, rfl, hout, hbounds⟩

end Geb.BitTree.EliasBinary
