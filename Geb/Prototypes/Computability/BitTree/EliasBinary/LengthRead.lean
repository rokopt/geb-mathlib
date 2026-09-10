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
# One bit of the length field

A length-field bit is written to the length register at its eventual significance, the
forks head advances one cell as the ruler, and the size counter is incremented. When the
counter reaches the size register the field is complete: the length heads step back onto the
least significant digit, that digit is tagged and the payload counter started, the size pair
is erased and its heads returned, and the ruler head returns to the origin. A bit that would
move the ruler head past the forks counter abandons the scan.

## Main definitions

* {lit}`headsCfg` and {lit}`eraseSizeCfg` are the configuration families of the head-return and
  erasure walks.

## Main statements

* {lit}`configs_walk` iterates a one-step description of a family of configurations.
* {lit}`configs_returnWalk` and {lit}`configs_eraseSize` describe the three walks.
* {lit}`configs_bit_length` realizes one length-field bit in its macro cost.

## Tags

Turing machine, simulation, Elias delta code, length field
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb digit origin mismatchMove mismatchCount bitsAt
  bitsAt_eq_testBit)
open Geb.BitTree.Counter (flips)
open Geb.TreeScanner (step_of_state)

/-! ## Digits -/

/-- Appending a digit below a shifted value places it at the shift. -/
theorem bitsAt_bit_mul_pow (b : Bool) (v r j : ℕ) :
    bitsAt (Nat.bit b v * 2 ^ r) j = if j = r then b else bitsAt (v * 2 ^ (r + 1)) j := by
  rw [bitsAt_eq_testBit, bitsAt_eq_testBit, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j = r
  · subst hj
    simp
  · rw [ite_eq_right hj]
    by_cases hr : r ≤ j
    · have hj' : j - r = (j - (r + 1)).succ := by omega
      rw [hj', Nat.testBit_bit_succ, decide_eq_true hr, decide_eq_true (by omega : r + 1 ≤ j)]
    · rw [decide_eq_false hr, decide_eq_false (by omega : ¬ r + 1 ≤ j)]
      rfl

/-- A natural cell of a rightward layout is its own significance. -/
theorem cell_nat (j : ℕ) : cell 0 1 j = j := by simp [cell]

/-- A cell of a leftward layout lies below its least significant cell by its significance. -/
theorem cell_neg (lsb : ℤ) (j : ℕ) : cell lsb (-1) j = lsb - j := by
  simp only [cell, SignType.cast]
  omega

/-! ## Transfer of pair representations -/

/-- The contents of a pair transfer to a configuration agreeing on its tapes and mismatch
head. -/
theorem PairData.transfer {input : List (Fin 4)} {lay : Layout} {lsb : ℤ} {width a b : ℕ}
    {cfg cfg' : Cfg 9 (Fin 4) Control input} (h : PairData lay lsb width cfg a b)
    (h1 : cfg'.workTapes lay.first = cfg.workTapes lay.first)
    (h2 : cfg'.workTapes lay.second = cfg.workTapes lay.second)
    (h3 : cfg'.workTapes lay.mism = cfg.workTapes lay.mism)
    (h4 : cfg'.workTapePos lay.mism = cfg.workTapePos lay.mism) :
    PairData lay lsb width cfg' a b where
  firstDigits := by
    funext j
    simp only [digitsFrom, h1]
    exact congrFun h.firstDigits j
  secondDigits := by
    funext j
    simp only [digitsFrom, h2]
    exact congrFun h.secondDigits j
  originTag := by rw [h1]; exact h.originTag
  firstBlank := by rw [h1]; exact h.firstBlank
  marker := by rw [h3]; exact h.marker
  mismatchPos := by rw [h4]; exact h.mismatchPos
  firstSize := h.firstSize
  secondSize := h.secondSize

/-- A pair representation transfers to a configuration agreeing on its tapes and heads. -/
theorem PairRep.transfer {input : List (Fin 4)} {lay : Layout} {lsb : ℤ} {width a b : ℕ}
    {cfg cfg' : Cfg 9 (Fin 4) Control input} (h : PairRep lay lsb width cfg a b)
    (h1 : cfg'.workTapes lay.first = cfg.workTapes lay.first)
    (h2 : cfg'.workTapes lay.second = cfg.workTapes lay.second)
    (h3 : cfg'.workTapes lay.mism = cfg.workTapes lay.mism)
    (h4 : cfg'.workTapePos lay.first = cfg.workTapePos lay.first)
    (h5 : cfg'.workTapePos lay.second = cfg.workTapePos lay.second)
    (h6 : cfg'.workTapePos lay.mism = cfg.workTapePos lay.mism) :
    PairRep lay lsb width cfg' a b :=
  ⟨h.toPairData.transfer h1 h2 h3 h6, by rw [h4]; exact h.firstPos, by rw [h5]; exact h.secondPos⟩

/-! ## Walks -/

/-- A family of configurations closed under one step up to a bound is followed by the
machine, emitting nothing. -/
theorem configs_walk {input : List (Fin 4)} (F : ℕ → Cfg 9 (Fin 4) Control input) (n : ℕ)
    (hstep : ∀ p, p < n → machine.step (F p) = F (p + 1))
    (hout : ∀ p, p < n → machine.outputSymbol (F p) = none) (t : ℕ) (ht : t ≤ n) :
    machine.configs (F 0) t = F t ∧ machine.outputString (F 0) t = [] := by
  revert ht
  refine Nat.rec ?_ ?_ t
  · intro _
    exact ⟨configs_zero, rfl⟩
  · intro t ih ht
    obtain ⟨hc, ho⟩ := ih (by omega)
    constructor
    · rw [configs_succ_eq_step', hc, hstep t (by omega)]
    · rw [outputString_succ, ho, hc, hout t (by omega)]
      rfl

/-- The configuration with the selected heads at one cell and a given finite control, the
rest as in a base configuration. -/
def headsCfg {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input) (q : Control)
    (sel : Fin 9 → Prop) [DecidablePred sel] (z : ℤ) : Cfg 9 (Fin 4) Control input where
  state := some q
  inputPos := c.inputPos
  workTapes := c.workTapes
  workTapePos i := if sel i then z else c.workTapePos i

/-- Head bounds of a base configuration extend to the selected heads at a bounded cell. -/
theorem headsCfg_headBound {input : List (Fin 4)} {c : Cfg 9 (Fin 4) Control input}
    {q : Control} {sel : Fin 9 → Prop} [DecidablePred sel] {z : ℤ} {width : ℕ}
    (hb : HeadBound width c) (hz : -1 ≤ z ∧ z ≤ width) :
    HeadBound width (headsCfg c q sel z) := by
  intro i
  simp only [headsCfg]
  split_ifs
  · exact hz
  · exact hb i

/-- A configuration whose selected heads sit at a common cell is in its own family. -/
theorem headsCfg_self {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input) (q : Control)
    (sel : Fin 9 → Prop) [DecidablePred sel] (z : ℤ) (hq : c.state = some q)
    (hpos : ∀ i, sel i → c.workTapePos i = z) : headsCfg c q sel z = c := by
  refine Cfg.ext hq.symm rfl rfl ?_
  funext i
  simp only [headsCfg]
  split_ifs with h
  · exact (hpos i h).symm
  · rfl

/-- Away from the tag, a head-returning state moves its selected heads back. -/
theorem step_returnWalk {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (q q' : Control) (j : Fin 9) (sel : Fin 9 → Prop) [DecidablePred sel]
    (hph : q = stSizeSetup ∨ q = stSizeInit ∨ q = stLengthEnd ∨ q = stTagLsb ∨
      q = stEraseSize ∨ q = stReturnSize ∨ q = stReturnF ∨ q = stEraseLength)
    (htr : ∀ work, phaseTr q work =
      if origin (work j) then (q', stay) else (q, fun i ↦ (none, if sel i then -1 else 0)))
    (hj : sel j) (horig : ∀ z, origin (c.workTapes j z) = decide (z = 0)) (z : ℤ)
    (hz : z ≠ 0) : machine.step (headsCfg c q sel z) = headsCfg c q sel (z - 1) := by
  have hw : origin ((headsCfg c q sel z).workTapeSymbols j) = false := by
    simp only [Cfg.workTapeSymbols, headsCfg, hj, ↓reduceIte]
    rw [horig, decide_eq_false hz]
  rw [step_of_state _ _ q rfl, tr_phase q hph, htr, hw]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  simp only [headsCfg, act, Bool.false_eq_true, ↓reduceIte]
  split_ifs
  · change z + (-1 : ℤ) = z - 1
    omega
  · simp

/-- At the tag, a head-returning state changes only its finite control. -/
theorem step_returnWalk_end {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (q q' : Control) (j : Fin 9) (sel : Fin 9 → Prop) [DecidablePred sel]
    (hph : q = stSizeSetup ∨ q = stSizeInit ∨ q = stLengthEnd ∨ q = stTagLsb ∨
      q = stEraseSize ∨ q = stReturnSize ∨ q = stReturnF ∨ q = stEraseLength)
    (htr : ∀ work, phaseTr q work =
      if origin (work j) then (q', stay) else (q, fun i ↦ (none, if sel i then -1 else 0)))
    (hj : sel j) (horig : ∀ z, origin (c.workTapes j z) = decide (z = 0)) :
    machine.step (headsCfg c q sel 0) = headsCfg c q' sel 0 := by
  have hw : origin ((headsCfg c q sel 0).workTapeSymbols j) = true := by
    simp only [Cfg.workTapeSymbols, headsCfg, hj, ↓reduceIte]
    rw [horig]
    rfl
  rw [step_of_state _ _ q rfl, tr_phase q hph, htr, hw]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  simp [headsCfg, act, stay]

/-- A head-returning state walks its selected heads from a common cell to the tag and then
changes its finite control, emitting nothing and keeping every other head fixed. -/
theorem configs_returnWalk {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (q q' : Control) (j : Fin 9) (sel : Fin 9 → Prop) [DecidablePred sel]
    (hph : q = stSizeSetup ∨ q = stSizeInit ∨ q = stLengthEnd ∨ q = stTagLsb ∨
      q = stEraseSize ∨ q = stReturnSize ∨ q = stReturnF ∨ q = stEraseLength)
    (htr : ∀ work, phaseTr q work =
      if origin (work j) then (q', stay) else (q, fun i ↦ (none, if sel i then -1 else 0)))
    (hj : sel j) (horig : ∀ z, origin (c.workTapes j z) = decide (z = 0))
    (hq : c.state = some q) (S : ℕ) (hpos : ∀ i, sel i → c.workTapePos i = S) :
    machine.configs c (S + 1) = headsCfg c q' sel 0 ∧ machine.outputString c (S + 1) = [] ∧
      ∀ t ≤ S + 1, ∃ (q'' : Control) (z : ℤ), 0 ≤ z ∧ z ≤ (S : ℤ) ∧
        machine.configs c t = headsCfg c q'' sel z := by
  have hself := headsCfg_self c q sel S hq hpos
  have hstep : ∀ p, p < S → machine.step (headsCfg c q sel ((S : ℤ) - p)) =
      headsCfg c q sel ((S : ℤ) - (p + 1 : ℕ)) := by
    intro p hp
    rw [step_returnWalk c q q' j sel hph htr hj horig _ (by omega)]
    congr 1
    omega
  have hout : ∀ p, p < S → machine.outputSymbol (headsCfg c q sel ((S : ℤ) - p)) = none :=
    fun _ _ ↦ outputSymbol_phase _ q rfl hph
  have hw := configs_walk (fun p : ℕ ↦ headsCfg c q sel ((S : ℤ) - p)) S hstep hout
  simp only [Nat.cast_zero, Int.sub_zero, hself] at hw
  have hS := hw S (Nat.le_refl _)
  rw [Int.sub_self] at hS
  have hend : machine.configs c (S + 1) = headsCfg c q' sel 0 := by
    rw [configs_succ_eq_step', hS.1, step_returnWalk_end c q q' j sel hph htr hj horig]
  refine ⟨hend, ?_, ?_⟩
  · rw [outputString_succ, hS.2, hS.1, outputSymbol_phase _ q rfl hph]
    rfl
  · intro t ht
    by_cases hts : t ≤ S
    · exact ⟨q, (S : ℤ) - t, by omega, by omega, (hw t hts).1⟩
    · rw [show t = S + 1 by omega, hend]
      exact ⟨q', 0, Int.le_refl _, Int.natCast_nonneg _, rfl⟩

/-- The configuration of the size-pair erasure after a number of cells: the register keeps
its tagged origin and is blank below the heads, the counter is blank below the heads. -/
def eraseSizeCfg {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input) (q : Control) (p : ℕ) :
    Cfg 9 (Fin 4) Control input where
  state := some q
  inputPos := c.inputPos
  workTapes i :=
    if i = 3 then
      fun z ↦ if 0 ≤ z ∧ z < p then (if z = 0 then some 2 else none) else c.workTapes 3 z
    else if i = 4 then fun z ↦ if 0 ≤ z ∧ z < p then none else c.workTapes 4 z
    else c.workTapes i
  workTapePos i := if i = 3 ∨ i = 4 then p else c.workTapePos i

/-- Head bounds of a base configuration extend to the erasure family within the width. -/
theorem eraseSizeCfg_headBound {input : List (Fin 4)} {c : Cfg 9 (Fin 4) Control input}
    {q : Control} {p width : ℕ} (hb : HeadBound width c) (hp : p ≤ width) :
    HeadBound width (eraseSizeCfg c q p) := by
  intro i
  simp only [eraseSizeCfg]
  split_ifs
  · omega
  · exact hb i

/-- A configuration in the erasing state with both size heads at the origin starts the
erasure family. -/
theorem eraseSizeCfg_self {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (hq : c.state = some stEraseSize) (h3 : c.workTapePos 3 = 0) (h4 : c.workTapePos 4 = 0) :
    eraseSizeCfg c stEraseSize 0 = c := by
  refine Cfg.ext hq.symm rfl ?_ ?_
  · funext i z
    have hz : ¬(0 ≤ z ∧ z < ((0 : ℕ) : ℤ)) := by omega
    simp only [eraseSizeCfg]
    split_ifs with h3' h4'
    · subst h3'
      exact ite_eq_right hz
    · subst h4'
      exact ite_eq_right hz
    · rfl
  · funext i
    simp only [eraseSizeCfg]
    split_ifs with h
    · rcases h with rfl | rfl
      · exact h3.symm
      · exact h4.symm
    · rfl

/-- Over a written register cell, the erasing state clears both size tapes and advances. -/
theorem step_eraseSize {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (horig : ∀ z, origin (c.workTapes 3 z) = decide (z = 0)) (p : ℕ)
    (hp : c.workTapes 3 p ≠ none) :
    machine.step (eraseSizeCfg c stEraseSize p) = eraseSizeCfg c stEraseSize (p + 1) := by
  have hw : (eraseSizeCfg c stEraseSize p).workTapeSymbols 3 = c.workTapes 3 p := by
    simp [Cfg.workTapeSymbols, eraseSizeCfg]
  rw [step_of_state _ _ stEraseSize rfl, tr_phase stEraseSize (by simp), phaseTr_eraseSize, hw,
    ite_eq_right hp, horig]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext i z
    simp only [eraseSizeCfg, act]
    by_cases h3 : i = 3
    · subst h3
      by_cases hz : z = p
      · subst hz
        simp
      · have he : (0 ≤ z ∧ z < p) ↔ (0 ≤ z ∧ z < p + 1) := by omega
        simp [hz, he]
    · by_cases h4 : i = 4
      · subst h4
        by_cases hz : z = p
        · subst hz
          simp
        · have he : (0 ≤ z ∧ z < p) ↔ (0 ≤ z ∧ z < p + 1) := by omega
          simp [hz, he]
      · simp [h3, h4]
  · funext i
    simp only [eraseSizeCfg, act]
    split_ifs <;> simp_all [SignType.cast]

/-- Over the first blank register cell, the erasing state only changes its finite control. -/
theorem step_eraseSize_end {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (S : ℕ) (hS : c.workTapes 3 S = none) :
    machine.step (eraseSizeCfg c stEraseSize S) = eraseSizeCfg c stReturnSize S := by
  have hw : (eraseSizeCfg c stEraseSize S).workTapeSymbols 3 = none := by
    simp [Cfg.workTapeSymbols, eraseSizeCfg, hS]
  rw [step_of_state _ _ stEraseSize rfl, tr_phase stEraseSize (by simp), phaseTr_eraseSize, hw,
    ite_eq_left rfl]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  simp [eraseSizeCfg, act, stay]

/-- The erasure walk: from the origin, the size heads clear the written register cells and
their counter cells, the register keeping its tagged origin, then stop at the first blank
register cell, emitting nothing. -/
theorem configs_eraseSize {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input) (S : ℕ)
    (hq : c.state = some stEraseSize) (h3 : c.workTapePos 3 = 0) (h4 : c.workTapePos 4 = 0)
    (horig : ∀ z, origin (c.workTapes 3 z) = decide (z = 0))
    (hblank : ∀ j : ℕ, c.workTapes 3 j = none ↔ S ≤ j) :
    machine.configs c (S + 1) = eraseSizeCfg c stReturnSize S ∧
      machine.outputString c (S + 1) = [] ∧
      ∀ t ≤ S + 1, ∃ q p, p ≤ S ∧ machine.configs c t = eraseSizeCfg c q p := by
  have hself := eraseSizeCfg_self c hq h3 h4
  have hstep : ∀ p, p < S → machine.step (eraseSizeCfg c stEraseSize p) =
      eraseSizeCfg c stEraseSize (p + 1) :=
    fun p hp ↦ step_eraseSize c horig p (fun h ↦ by have := (hblank p).mp h; omega)
  have hout : ∀ p, p < S → machine.outputSymbol (eraseSizeCfg c stEraseSize p) = none :=
    fun _ _ ↦ outputSymbol_phase _ stEraseSize rfl (by simp)
  have hw := configs_walk (fun p ↦ eraseSizeCfg c stEraseSize p) S hstep hout
  simp only [hself] at hw
  have hS := hw S (Nat.le_refl _)
  have hend : machine.configs c (S + 1) = eraseSizeCfg c stReturnSize S := by
    rw [configs_succ_eq_step', hS.1, step_eraseSize_end c S ((hblank S).mpr (Nat.le_refl _))]
  refine ⟨hend, ?_, ?_⟩
  · rw [outputString_succ, hS.2, hS.1, outputSymbol_phase _ stEraseSize rfl (by simp)]
    rfl
  · intro t ht
    by_cases hts : t ≤ S
    · exact ⟨stEraseSize, t, hts, (hw t hts).1⟩
    · rw [show t = S + 1 by omega, hend]
      exact ⟨stReturnSize, S, Nat.le_refl _, rfl⟩

/-! ## Single transitions -/

/-- The configuration after the length-end step: both length heads move back one cell. -/
def lengthEndCfg {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input) :
    Cfg 9 (Fin 4) Control input where
  state := some stTagLsb
  inputPos := c.inputPos
  workTapes := c.workTapes
  workTapePos i := if i = 6 ∨ i = 7 then c.workTapePos i - 1 else c.workTapePos i

/-- The length-end state steps both length heads back. -/
theorem step_lengthEnd {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (hq : c.state = some stLengthEnd) : machine.step c = lengthEndCfg c := by
  rw [step_of_state _ _ _ hq, tr_phase stLengthEnd (by simp), phaseTr_lengthEnd]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  simp only [lengthEndCfg, act]
  split_ifs
  · change c.workTapePos i + (-1 : ℤ) = c.workTapePos i - 1
    omega
  · simp

/-- The configuration after the tagging step: the length register's current digit is tagged,
the payload counter's current cell holds one, and the length mismatch head moves by the
comparison of the two cells. -/
def tagLsbCfg {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input) :
    Cfg 9 (Fin 4) Control input where
  state := some stEraseSize
  inputPos := c.inputPos
  workTapes i :=
    if i = 6 then
      Function.update (c.workTapes 6) (c.workTapePos 6)
        (some (tagged (digit (c.workTapeSymbols 6))))
    else if i = 7 then Function.update (c.workTapes 7) (c.workTapePos 7) (some 1)
    else c.workTapes i
  workTapePos i :=
    if i = 8 then c.workTapePos 8 + (mismatchMove (c.workTapeSymbols 6) (c.workTapeSymbols 7) : ℤ)
    else c.workTapePos i

/-- The tagging state tags the length register's digit and starts the payload counter. -/
theorem step_tagLsb {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (hq : c.state = some stTagLsb) : machine.step c = tagLsbCfg c := by
  rw [step_of_state _ _ _ hq, tr_phase stTagLsb (by simp), phaseTr_tagLsb]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext i
    simp only [tagLsbCfg, act]
    split_ifs with h6 h7
    · subst h6
      rfl
    · subst h7
      rfl
    · rfl
    · rfl
  · funext i
    simp only [tagLsbCfg, act]
    split_ifs <;> simp_all

/-- The configuration after reading a length-field bit: the bit is written to the length
register, the forks head and both length heads advance, and the length mismatch head
advances by the bit. -/
def lengthBitCfg {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input) (b : Bool) :
    Cfg 9 (Fin 4) Control input where
  state := some (stCarry 4)
  inputPos := moveInputPos c.inputPos 1
  workTapes i :=
    if i = 6 then Function.update (c.workTapes 6) (c.workTapePos 6) (some (plain b))
    else c.workTapes i
  workTapePos i :=
    if i = 0 ∨ i = 6 ∨ i = 7 then c.workTapePos i + 1
    else if i = 8 then c.workTapePos 8 + b.toNat
    else c.workTapePos i

/-- Under a written ruler cell, the length-field state reads a bit and starts the size
increment. -/
theorem step_lengthBit {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input) (b : Bool)
    (hq : c.state = some stLengthBit) (hi : c.inputSymbol = some (boolEmb b))
    (h0 : c.workTapeSymbols 0 ≠ none) : machine.step c = lengthBitCfg c b := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stLengthBit (by simp), scanTr_length, ite_eq_right h0]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    simp only [lengthBitCfg, consumeAct]
    split_ifs <;> simp_all
  · funext i
    simp only [lengthBitCfg, consumeAct]
    split_ifs <;> simp_all [SignType.cast]

/-- Under a blank ruler cell, the length-field state abandons the scan. -/
theorem step_lengthBit_dead {input : List (Fin 4)} (c : Cfg 9 (Fin 4) Control input)
    (b : Bool) (hq : c.state = some stLengthBit) (hi : c.inputSymbol = some (boolEmb b))
    (h0 : c.workTapeSymbols 0 = none) :
    machine.step c = { c with state := some stDead, inputPos := moveInputPos c.inputPos 1 } := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stLengthBit (by simp), scanTr_length, ite_eq_left h0]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    rfl
  · funext i
    simp [consumeAct, stay]

/-! ## The increment's untouched cells -/

/-- The cells of the incremented tape at or beyond the bit-change count are unchanged by the
increment. -/
theorem configs_increment_beyond {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (k : Fin 6) (lsb : ℤ) (width a b n : ℕ) (hn : n = if siteSel k then b else a)
    (h : PairRep (siteLayout k) lsb width cfg a b) (hq : cfg.state = some (stCarry k))
    (j : ℕ) (hj : flips n.bits ≤ j) :
    (machine.configs cfg (2 * flips n.bits + 1)).workTapes (siteSelected k)
        (cell lsb (siteLayout k).dir j) =
      cfg.workTapes (siteSelected k) (cell lsb (siteLayout k).dir j) := by
  have hbits : ∀ j, digitsFrom cfg (siteSelected k) lsb (siteLayout k).dir j =
      n.bits[j]?.getD false := by
    intro j
    rcases hsel : siteSel k with _ | _
    · simp only [siteSelected, hsel, Bool.false_eq_true, ↓reduceIte, hn]
      exact congrFun h.firstDigits j
    · simp only [siteSelected, hsel, ↓reduceIte, hn]
      exact congrFun h.secondDigits j
  obtain ⟨hstate, hpos0, hpos1, -, -, -, -, hcells, -, horig, -, -⟩ :=
    configs_carry_bits cfg k lsb n.bits hq h.firstPos h.secondPos hbits
  set after := machine.configs cfg (flips n.bits) with hafter
  have ho : ∀ z, origin (after.workTapes (siteLayout k).first z) = decide (z = lsb) :=
    fun z ↦ (horig z).trans (h.originTag z)
  have hrep := returnCfg_self after k lsb (flips n.bits) hstate hpos0 hpos1
  have hc := (configs_return_done after k lsb ho (flips n.bits)).1
  rw [hrep] at hc
  rw [show 2 * flips n.bits + 1 = flips n.bits + (flips n.bits + 1) by omega, configs_add, hc]
  change after.workTapes (siteSelected k) _ = _
  exact hcells _ (fun i hi he ↦ by
    have := cell_injective _ _ (siteLayout_proper k).dir_ne_zero _ _ he
    omega)

set_option maxHeartbeats 400000 in
-- Six nested configuration families are unfolded through the tag, erasure and return walks.
/-- After the size counter reaches the size register: the length heads step back, the least
significant digit is tagged and the payload counter started, the size pair is erased and its
heads returned, and the ruler head returns, reaching the payload boundary without emitting. -/
theorem configs_lengthEnd {input : List (Fin 4)} (c2 cfg : Cfg 9 (Fin 4) Control input)
    (width v : ℕ) (b : Bool) (f l k : ℕ) (hv0 : 0 < v) (hnext : (v.size + 1).size ≤ width)
    (hvw : v.size + 1 ≤ width) (hst2 : c2.state = some stLengthEnd)
    (hp2 : PairRep sizeLayout 0 width c2 (1 + v.size) (v.size + 1))
    (hq0 : c2.workTapePos 0 = (v.size : ℤ)) (hq1 : c2.workTapePos 1 = 0)
    (hq6 : c2.workTapePos 6 = (v.size : ℤ) + 1) (hq7 : c2.workTapePos 7 = (v.size : ℤ) + 1)
    (hq8 : c2.workTapePos 8 = (pop v : ℤ) + b.toNat) (hlen : LengthRead cfg 1 v)
    (ht6' : c2.workTapes 6 = Function.update (cfg.workTapes 6) (v.size : ℤ) (some (plain b)))
    (ht7 : c2.workTapes 7 = cfg.workTapes 7) (ht8 : c2.workTapes 8 = cfg.workTapes 8)
    (hpend2 : PairData pendingLayout 0 width c2 f l)
    (hneg : ∀ z, z < 0 → c2.workTapes 3 z = none ∧ c2.workTapes 4 z = none)
    (hbeyond : ∀ j : ℕ, (v.size + 1).size ≤ j → c2.workTapes 4 j = none)
    (hb2 : HeadBound width c2) :
    let total := 1 + 1 + ((v.size + 1).size + 1) + ((v.size + 1).size + 1) + (v.size + 1)
    let now := machine.configs c2 total
    LiveRep width now ⟨(.payload (Nat.bit b v - 1), k), f, l, Nat.bit b v⟩ ∧
      now.state = some stPayloadBit ∧ now.inputPos = c2.inputPos ∧
      machine.outputString c2 total = [] ∧ ∀ t ≤ total, HeadBound width (machine.configs c2 t) := by
  have hsb := size_bit b v hv0
  have hN := size_pos_of_pos v hv0
  have hS := size_pos_of_pos (v.size + 1) (by omega)
  set S := (v.size + 1).size with hSdef
  have hT2 : 2 ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
  have hT1 : Nat.bit b v - (Nat.bit b v - 1) = 1 := by omega
  have hTs : (((Nat.bit b v).size - 1 : ℕ) : ℤ) = (v.size : ℤ) := by rw [hsb]; simp
  have hL : lengthLsb 1 v = (v.size : ℤ) := by unfold lengthLsb; omega
  have hbT : ∀ j, bitsAt (Nat.bit b v) j = if j = 0 then b else bitsAt (v * 2 ^ 1) j := by
    intro j
    have := bitsAt_bit_mul_pow b v 0 j
    rwa [Nat.pow_zero, Nat.mul_one, Nat.zero_add] at this
  have hpop := pop_le_size v
  have hq3 : c2.workTapePos 3 = 0 := hp2.firstPos
  have hq4 : c2.workTapePos 4 = 0 := hp2.secondPos
  have hq5 : c2.workTapePos 5 = 0 := hp2.mismatchPos_eq_zero_iff.mpr (by omega)
  -- the length heads step back
  have hc3 : machine.step c2 = lengthEndCfg c2 := step_lengthEnd c2 hst2
  set c3 := lengthEndCfg c2 with hc3def
  have hr6 : c3.workTapePos 6 = (v.size : ℤ) := by
    change c2.workTapePos 6 - 1 = _
    rw [hq6]
    omega
  have hr7 : c3.workTapePos 7 = (v.size : ℤ) := by
    change c2.workTapePos 7 - 1 = _
    rw [hq7]
    omega
  have hb3 : HeadBound width c3 := by
    intro i
    rw [hc3def]
    simp only [lengthEndCfg]
    split_ifs with h67
    · rcases h67 with rfl | rfl
      · rw [hq6]
        omega
      · rw [hq7]
        omega
    · exact hb2 i
  have hsym6 : c3.workTapeSymbols 6 = some (plain b) := by
    change c3.workTapes 6 (c3.workTapePos 6) = _
    rw [hr6]
    change c2.workTapes 6 _ = _
    rw [ht6', Function.update_self]
  have hsym7 : c3.workTapeSymbols 7 = none := by
    change c3.workTapes 7 (c3.workTapePos 7) = _
    rw [hr7]
    change c2.workTapes 7 _ = _
    rw [ht7]
    exact hlen.counter _
  -- the least significant digit is tagged
  have hc4 : machine.step c3 = tagLsbCfg c3 := step_tagLsb c3 rfl
  set c4 := tagLsbCfg c3 with hc4def
  have hmm : mismatchMove (some (plain b)) none = if b then -1 else 1 := by cases b <;> rfl
  have hs8 : c4.workTapePos 8 = (pop v : ℤ) + b.toNat + (if b then -1 else 1) := by
    change c3.workTapePos 8 +
      (mismatchMove (c3.workTapeSymbols 6) (c3.workTapeSymbols 7) : ℤ) = _
    rw [hsym6, hsym7, hmm]
    change c2.workTapePos 8 + _ = _
    rw [hq8]
    cases b <;> rfl
  have hs0 : c4.workTapePos 0 = (v.size : ℤ) := hq0
  have hs3 : c4.workTapePos 3 = 0 := hq3
  have hs4 : c4.workTapePos 4 = 0 := hq4
  have hs6 : c4.workTapePos 6 = (v.size : ℤ) := hr6
  have hs7 : c4.workTapePos 7 = (v.size : ℤ) := hr7
  have hw6 : c4.workTapes 6 =
      Function.update (cfg.workTapes 6) (v.size : ℤ) (some (tagged b)) := by
    change Function.update (c3.workTapes 6) (c3.workTapePos 6)
      (some (tagged (digit (c3.workTapeSymbols 6)))) = _
    rw [hsym6, digit_plain, hr6]
    change Function.update (c2.workTapes 6) _ _ = _
    rw [ht6', Function.update_idem]
  have hw7 : c4.workTapes 7 = Function.update (cfg.workTapes 7) (v.size : ℤ) (some 1) := by
    change Function.update (c3.workTapes 7) (c3.workTapePos 7) (some 1) = _
    rw [hr7]
    change Function.update (c2.workTapes 7) _ _ = _
    rw [ht7]
  have hw3 : c4.workTapes 3 = c2.workTapes 3 := rfl
  have hw4 : c4.workTapes 4 = c2.workTapes 4 := rfl
  have hw8 : c4.workTapes 8 = cfg.workTapes 8 := ht8
  have hb4 : HeadBound width c4 := by
    intro i
    by_cases hi : i = 8
    · subst hi
      rw [hs8]
      cases b
      · simp only [Bool.toNat_false, Bool.false_eq_true, ↓reduceIte]
        omega
      · simp only [Bool.toNat_true, ↓reduceIte]
        omega
    · have hci : c4.workTapePos i = c3.workTapePos i := by
        rw [hc4def]
        simp [tagLsbCfg, hi]
      rw [hci]
      exact hb3 i
  -- the size pair is erased
  have horig3 : ∀ z, origin (c4.workTapes 3 z) = decide (z = 0) := by
    rw [hw3]
    exact hp2.originTag
  have hblank3 : ∀ j : ℕ, c4.workTapes 3 j = none ↔ S ≤ j := by
    intro j
    rw [hw3]
    have this : c2.workTapes 3 (cell 0 1 j) = none ↔ (1 + v.size).size ≤ j := hp2.firstBlank j
    rw [cell_nat, Nat.add_comm] at this
    exact this
  obtain ⟨hc6, hout4, hbnd4⟩ := configs_eraseSize c4 S rfl hs3 hs4 horig3 hblank3
  set c6 := eraseSizeCfg c4 stReturnSize S with hc6def
  have hbC4 : ∀ t ≤ S + 1, HeadBound width (machine.configs c4 t) := by
    intro t ht
    obtain ⟨q, p, hp, hcp⟩ := hbnd4 t ht
    rw [hcp]
    exact eraseSizeCfg_headBound hb4 (by omega)
  -- the size heads return
  have horig6 : ∀ z, origin (c6.workTapes 3 z) = decide (z = 0) := by
    intro z
    change origin (if 0 ≤ z ∧ z < S then (if z = 0 then some 2 else none)
      else c4.workTapes 3 z) = _
    split_ifs with h1 h2
    · rw [decide_eq_true h2]
      rfl
    · rw [decide_eq_false h2]
      rfl
    · exact horig3 z
  have hpos6 : ∀ i, (i = 3 ∨ i = 4) → c6.workTapePos i = S := fun i hi ↦ by
    rw [hc6def]
    simp [eraseSizeCfg, hi]
  obtain ⟨hc8, hout6, hbnd6⟩ := configs_returnWalk c6 stReturnSize stReturnF 3
    (fun i ↦ i = 3 ∨ i = 4) (by simp) (fun w ↦ phaseTr_returnSize w) (Or.inl rfl) horig6 rfl
    S hpos6
  set c8 := headsCfg c6 stReturnF (fun i ↦ i = 3 ∨ i = 4) 0 with hc8def
  have hb6 : HeadBound width c6 := eraseSizeCfg_headBound hb4 (by omega)
  have hbC6 : ∀ t ≤ S + 1, HeadBound width (machine.configs c6 t) := by
    intro t ht
    obtain ⟨q, z, hz0, hzS, hcz⟩ := hbnd6 t ht
    rw [hcz]
    exact headsCfg_headBound hb6 ⟨by omega, by omega⟩
  -- the ruler head returns
  have horig8 : ∀ z, origin (c8.workTapes 0 z) = decide (z = 0) := by
    intro z
    change origin (c2.workTapes 0 z) = _
    exact hpend2.originTag z
  have hpos8 : ∀ i, i = 0 → c8.workTapePos i = v.size := by
    intro i hi
    subst hi
    exact hs0
  obtain ⟨hc10, hout8, hbnd8⟩ := configs_returnWalk c8 stReturnF stPayloadBit 0
    (fun i ↦ i = 0) (by simp) (fun w ↦ phaseTr_returnF w) rfl horig8 rfl v.size hpos8
  set c10 := headsCfg c8 stPayloadBit (fun i ↦ i = 0) 0 with hc10def
  have hb8 : HeadBound width c8 := headsCfg_headBound hb6 ⟨by omega, by omega⟩
  have hbC8 : ∀ t ≤ v.size + 1, HeadBound width (machine.configs c8 t) := by
    intro t ht
    obtain ⟨q, z, hz0, hzS, hcz⟩ := hbnd8 t ht
    rw [hcz]
    exact headsCfg_headBound hb8 ⟨by omega, by omega⟩
  -- the segments combine
  have e3 : machine.configs c2 1 = c3 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hc3]
  have e4 : machine.configs c2 (1 + 1) = c4 := by
    rw [configs_add, e3, show (1 : ℕ) = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hc4]
  have e6 : machine.configs c2 (1 + 1 + (S + 1)) = c6 := by rw [configs_add, e4, hc6]
  have e8 : machine.configs c2 (1 + 1 + (S + 1) + (S + 1)) = c8 := by rw [configs_add, e6, hc8]
  have e10 : machine.configs c2 (1 + 1 + (S + 1) + (S + 1) + (v.size + 1)) = c10 := by
    rw [configs_add, e8, hc10]
  have o3 : machine.outputString c2 1 = [] := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, outputString_succ, configs_zero,
      outputSymbol_phase c2 stLengthEnd hst2 (by simp)]
    rfl
  have o4 : machine.outputString c2 (1 + 1) = [] :=
    outputString_add_nil c2 1 1 o3 (by
      rw [e3, show (1 : ℕ) = 0 + 1 from rfl, outputString_succ, configs_zero,
        outputSymbol_phase c3 stTagLsb rfl (by simp)]
      rfl)
  have o6 := outputString_add_nil c2 _ (S + 1) o4 (by rw [e4]; exact hout4)
  have o8 := outputString_add_nil c2 _ (S + 1) o6 (by rw [e6]; exact hout6)
  have o10 := outputString_add_nil c2 _ (v.size + 1) o8 (by rw [e8]; exact hout8)
  have hbC : ∀ u ≤ 1, HeadBound width (machine.configs c2 u) := by
    intro u hu
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
    · exact hb2
    · rw [e3]
      exact hb3
  have hbD := headBound_add c2 width 1 1 hbC (by
    rw [e3]
    intro u hu
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
    · exact hb3
    · rw [show (1 : ℕ) = 0 + 1 from rfl, configs_succ_eq_step', configs_zero, hc4]
      exact hb4)
  have hbE := headBound_add c2 width _ (S + 1) hbD (by rw [e4]; exact hbC4)
  have hbF := headBound_add c2 width _ (S + 1) hbE (by rw [e6]; exact hbC6)
  have hbG := headBound_add c2 width _ (v.size + 1) hbF (by rw [e8]; exact hbC8)
  -- the payload boundary
  have hneg6 : ∀ z, z < 0 → cfg.workTapes 6 z = none := by
    intro z hz
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ (v.size : ℤ) - z by omega)
    have := (hlen.blank j).mpr (Or.inr (by omega))
    rw [cell_neg, hL] at this
    rw [show z = (v.size : ℤ) - j by omega]
    exact this
  have hlive : LiveRep width c10 ⟨(.payload (Nat.bit b v - 1), k), f, l, Nat.bit b v⟩ := by
    refine ⟨hpend2.transfer rfl rfl rfl rfl, rfl, hq1, ?_⟩
    change IdleSize c10 ∧
      PairRep lengthLayout (((Nat.bit b v).size - 1 : ℕ) : ℤ) width c10 (Nat.bit b v)
        (Nat.bit b v - (Nat.bit b v - 1)) ∧
      ∀ z, z < 0 ∨ (((Nat.bit b v).size - 1 : ℕ) : ℤ) < z →
        c10.workTapes 6 z = none ∧ c10.workTapes 7 z = none
    rw [hTs, hT1]
    refine ⟨⟨?_, rfl, ?_, rfl, hp2.marker, hq5⟩, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hs6, hs7⟩, ?_⟩
    · intro z
      change (if 0 ≤ z ∧ z < S then (if z = 0 then some 2 else none)
        else c2.workTapes 3 z) = _
      split_ifs with h1 h2 h2
      · rfl
      · rfl
      · subst h2
        exact (h1 ⟨Int.le_refl _, by omega⟩).elim
      · by_cases hz : z < 0
        · exact (hneg z hz).1
        · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ z by omega)
          have := (hblank3 j).mpr (by omega)
          rwa [hw3] at this
    · intro z
      change (if 0 ≤ z ∧ z < S then none else c2.workTapes 4 z) = _
      split_ifs with h1
      · rfl
      · by_cases hz : z < 0
        · exact (hneg z hz).2
        · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ z by omega)
          exact hbeyond j (by omega)
    · funext j
      change digit (c4.workTapes 6 (cell (v.size : ℤ) (-1) j)) = _
      rw [cell_neg, hw6, hbT]
      by_cases hj : j = 0
      · subst hj
        rw [ite_eq_left rfl]
        simp only [Nat.cast_zero, Int.sub_zero, Function.update_self]
        exact digit_tagged b
      · rw [ite_eq_right hj, Function.update_of_ne (by omega)]
        have := congrFun hlen.digits j
        simp only [digitsFrom, cell_neg, hL] at this
        exact this
    · funext j
      change digit (c4.workTapes 7 (cell (v.size : ℤ) (-1) j)) = _
      rw [cell_neg, hw7]
      by_cases hj : j = 0
      · subst hj
        simp only [Nat.cast_zero, Int.sub_zero, Function.update_self]
        rw [digit_one]
        simp [bitsAt]
      · rw [Function.update_of_ne (by omega), hlen.counter,
          Geb.BitTree.BinaryMachine.bitsAt_of_size_le 1 j (by rw [Nat.size_one]; omega)]
        rfl
    · intro z
      change origin (c4.workTapes 6 z) = _
      rw [hw6]
      by_cases hz : z = v.size
      · subst hz
        rw [Function.update_self, origin_tagged, decide_eq_true rfl]
      · rw [Function.update_of_ne hz, hlen.untagged z, decide_eq_false hz]
    · intro j
      change c4.workTapes 6 (cell (v.size : ℤ) (-1) j) = none ↔ (Nat.bit b v).size ≤ j
      rw [cell_neg, hsb, hw6]
      by_cases hj : j = 0
      · subst hj
        simp only [Nat.cast_zero, Int.sub_zero, Function.update_self, reduceCtorEq, false_iff]
        omega
      · rw [Function.update_of_ne (by omega)]
        have := hlen.blank j
        rw [cell_neg, hL] at this
        rw [this]
        constructor <;> intro h' <;> omega
    · intro z
      change c4.workTapes 8 z = _
      rw [hw8]
      exact hlen.marker z
    · change c4.workTapePos 8 = _
      rw [hs8, mismatchCount_bitsAt_one (Nat.bit b v) width (by rw [hsb]; exact hvw)
        (by omega), pop_bit b v hv0, hbT 0, ite_eq_left rfl, Nat.cast_add]
    · rw [hsb]
      exact hvw
    · rw [Nat.size_one]
      omega
    · intro z hz
      change c4.workTapes 6 z = none ∧ c4.workTapes 7 z = none
      have hz' : z ≠ (v.size : ℤ) := by omega
      rw [hw6, hw7, Function.update_of_ne hz', Function.update_of_ne hz']
      refine ⟨?_, hlen.counter z⟩
      rcases hz with hz | hz
      · exact hneg6 z hz
      · exact hlen.beyond z (by rw [hL]; exact hz)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e10]
    exact hlive
  · rw [e10]
    rfl
  · rw [e10]
    rfl
  · exact o10
  · exact hbG

/-! ## The main statement -/

/-- One length-field bit realizes its account update in its macro cost. -/
theorem configs_bit_length {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) (b : Bool) (n width : ℕ) (hv : AccountValid n a)
    (h : Represents width cfg a) (hi : cfg.inputSymbol = some (boolEmb b))
    (hw1 : a.forks.size + 1 ≤ width)
    (r v k : ℕ) (hs : a.state = (.length r v, k)) : BitSpec cfg a b width := by
  have hact := hv.active
  rw [hs] at hact
  obtain ⟨hk, hr, hv0⟩ := hact
  have hrp := hv.rulerPos_le
  rw [hs] at hrp
  simp only [rulerPos] at hrp
  have hl : LiveRep width cfg a := h.live (by rw [hs]; simp)
  have hph := hl.phase
  unfold PhaseRep at hph
  rw [hs] at hph
  obtain ⟨hpair, hlen⟩ := hph
  have hx := hlen.spare
  have hq : cfg.state = some stLengthBit := by rw [h.state, hs]; rfl
  have hN := size_pos_of_pos v hv0
  have hpos0 : cfg.workTapePos 0 = ((v.size - 1 : ℕ) : ℤ) := by rw [hl.forksPos, hs]; rfl
  have hfb : ∀ j : ℕ, cfg.workTapes 0 j = none ↔ a.forks.size ≤ j := by
    intro j
    have this : cfg.workTapes 0 (cell 0 1 j) = none ↔ a.forks.size ≤ j := hl.pending.firstBlank j
    rwa [cell_nat] at this
  have hsym0 : cfg.workTapeSymbols 0 = cfg.workTapes 0 ((v.size - 1 : ℕ) : ℤ) := by
    rw [Cfg.workTapeSymbols, hpos0]
  have hout1 : machine.outputString cfg 1 = [] := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, outputString_succ, configs_zero,
      outputSymbol_scan cfg stLengthBit hq (by simp) b hi]
    rfl
  by_cases hcap : a.forks.size ≤ v.size - 1
  · have hc : capped a b = true := by simp [capped, hs, hcap]
    have hm : macroCost a b = 1 := by simp [macroCost, hc]
    have ha : accountStep a b = ⟨(.dead, 0), a.forks, a.leaves, 0⟩ := by simp [accountStep, hc]
    have h0 : cfg.workTapeSymbols 0 = none := by rw [hsym0]; exact (hfb _).mpr hcap
    have hc1 : machine.configs cfg 1 =
        { cfg with state := some stDead, inputPos := moveInputPos cfg.inputPos 1 } := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, configs_succ_eq_step', configs_zero,
        step_lengthBit_dead cfg b hq hi h0]
    have hb1 : HeadBound width
        { cfg with state := some stDead, inputPos := moveInputPos cfg.inputPos 1 } := h.bound
    unfold BitSpec
    rw [hm, ha]
    refine ⟨Represents.dead rfl (by rw [hc1]) (by rw [hc1]; exact hb1), by rw [hc1], hout1, ?_⟩
    intro u hu
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
    · exact h.bound
    · rw [hc1]
      exact hb1
  · have hc : capped a b = false := by simp [capped, hs, hcap]
    have h0 : cfg.workTapeSymbols 0 ≠ none := by
      rw [hsym0]
      intro h0
      have := (hfb _).mp h0
      omega
    set c1 := lengthBitCfg cfg b with hc1def
    have hc1 : machine.configs cfg 1 = c1 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, configs_succ_eq_step', configs_zero,
        step_lengthBit cfg b hq hi h0]
    have hin1 : c1.inputPos = moveInputPos cfg.inputPos 1 := rfl
    have hp0 : c1.workTapePos 0 = (v.size : ℤ) := by
      change cfg.workTapePos 0 + 1 = _
      rw [hpos0]
      omega
    have hp6 : c1.workTapePos 6 = (v.size : ℤ) + 1 := by
      change cfg.workTapePos 6 + 1 = _
      rw [hlen.registerPos]
    have hp7 : c1.workTapePos 7 = (v.size : ℤ) + 1 := by
      change cfg.workTapePos 7 + 1 = _
      rw [hlen.counterPos]
    have hp8 : c1.workTapePos 8 = (pop v : ℤ) + b.toNat := by
      change cfg.workTapePos 8 + (b.toNat : ℤ) = _
      rw [hlen.mismPos]
    have ht6 : c1.workTapes 6 =
        Function.update (cfg.workTapes 6) (v.size : ℤ) (some (plain b)) := by
      change Function.update (cfg.workTapes 6) (cfg.workTapePos 6) (some (plain b)) = _
      rw [hlen.registerPos]
    have hpop := pop_le_size v
    have htoNat := Bool.toNat_le b
    have hb1 : HeadBound width c1 := by
      intro i
      rw [hc1def]
      simp only [lengthBitCfg]
      split_ifs with h1 h2
      · rcases h1 with rfl | rfl | rfl
        · rw [hpos0]
          omega
        · rw [hlen.registerPos]
          omega
        · rw [hlen.counterPos]
          omega
      · subst h2
        rw [hlen.mismPos]
        omega
      · exact h.bound i
    have hbA : ∀ u ≤ 1, HeadBound width (machine.configs cfg u) := by
      intro u hu
      rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
      · exact h.bound
      · rw [hc1]
        exact hb1
    -- the increment of the size counter
    have hpair1 : PairRep (siteLayout 4) 0 width c1 (r + v.size) v.size :=
      hpair.transfer rfl rfl rfl rfl rfl rfl
    have hnext : (v.size + 1).size ≤ width := by
      have := size_le_self (v.size + 1)
      omega
    have hflips := Geb.BitTree.Counter.flips_bits_le_succ_size v.size
    obtain ⟨hp2, hst2, hin2, hun2, hcells2, hout2⟩ :=
      configs_increment c1 4 0 width (r + v.size) v.size v.size rfl hpair1 rfl hnext
    set c2 := machine.configs c1 (2 * flips v.size.bits + 1) with hc2def
    clear_value c2
    change PairRep sizeLayout 0 width c2 (r + v.size) (v.size + 1) at hp2
    change c2.state = some (if r + v.size = v.size + 1 then stLengthEnd else stLengthBit) at hst2
    change ∀ i, i ≠ 3 → i ≠ 4 → i ≠ 5 →
      c2.workTapes i = c1.workTapes i ∧ c2.workTapePos i = c1.workTapePos i at hun2
    change ∀ z, (∀ j : ℕ, z ≠ cell 0 1 j) →
      c2.workTapes 3 z = c1.workTapes 3 z ∧ c2.workTapes 4 z = c1.workTapes 4 z at hcells2
    have hbeyond : ∀ j : ℕ, (v.size + 1).size ≤ j → c2.workTapes 4 j = none := by
      intro j hj
      have := configs_increment_beyond c1 4 0 width (r + v.size) v.size v.size rfl hpair1 rfl j
        (by omega)
      rw [← hc2def] at this
      change c2.workTapes 4 (cell 0 1 j) = c1.workTapes 4 (cell 0 1 j) at this
      rw [cell_nat] at this
      rw [this]
      exact hx.counterBeyond j
        (by have := Geb.BitTree.Counter.size_mono (Nat.le_add_right v.size 1); omega)
    have hbinc : ∀ t ≤ 2 * flips v.size.bits + 1, HeadBound width (machine.configs c1 t) := by
      intro t ht i
      have hcell : ∀ p, p ≤ flips v.size.bits →
          -1 ≤ cell 0 (siteLayout 4).dir p ∧ cell 0 (siteLayout 4).dir p ≤ width := by
        intro p hp
        change -1 ≤ cell 0 1 p ∧ cell 0 1 p ≤ width
        rw [cell_nat]
        omega
      obtain ⟨hin, hout⟩ := configs_increment_head_bounds c1 4 0 width (r + v.size) v.size
        v.size rfl hpair1 rfl hnext hcell t ht i
      by_cases hi3 : i = 3 ∨ i = 4 ∨ i = 5
      · exact hin hi3
      · rw [hout (fun h ↦ hi3 (Or.inl h)) (fun h ↦ hi3 (Or.inr (Or.inl h)))
          (fun h ↦ hi3 (Or.inr (Or.inr h)))]
        exact hb1 i
    have hbB : ∀ u ≤ 1 + (2 * flips v.size.bits + 1), HeadBound width (machine.configs cfg u) :=
      headBound_add cfg width 1 _ hbA (by rw [hc1]; exact hbinc)
    have hout12 : machine.outputString cfg (1 + (2 * flips v.size.bits + 1)) = [] :=
      outputString_add_nil cfg 1 _ hout1 (by rw [hc1]; exact hout2)
    have hsb := size_bit b v hv0
    have hvalid := accountStep_valid n a b hv
    have hu0 := hun2 0 (by decide) (by decide) (by decide)
    have hu1 := hun2 1 (by decide) (by decide) (by decide)
    have hu2 := hun2 2 (by decide) (by decide) (by decide)
    have hu6 := hun2 6 (by decide) (by decide) (by decide)
    have hu7 := hun2 7 (by decide) (by decide) (by decide)
    have hu8 := hun2 8 (by decide) (by decide) (by decide)
    have hpend2 : PairData pendingLayout 0 width c2 a.forks a.leaves :=
      hl.pending.transfer hu0.1 hu1.1 hu2.1 hu2.2
    have hneg : ∀ z, z < 0 → c2.workTapes 3 z = none ∧ c2.workTapes 4 z = none := by
      intro z hz
      have := hcells2 z (fun j ↦ by rw [cell_nat]; omega)
      rw [this.1, this.2]
      exact ⟨hx.registerNeg z hz, hx.counterNeg z hz⟩
    by_cases he : r = 1
    · subst he
      have hS := size_pos_of_pos (v.size + 1) (by omega)
      have hm : macroCost a b = 1 + (2 * flips v.size.bits + 1) +
          (1 + 1 + ((v.size + 1).size + 1) + ((v.size + 1).size + 1) + (v.size + 1)) := by
        simp only [macroCost, hc, hs, Bool.false_eq_true, ↓reduceIte, inc]
        omega
      have ha : accountStep a b =
          ⟨(.payload (Nat.bit b v - 1), k), a.forks, a.leaves, Nat.bit b v⟩ := by
        simp [accountStep, hc, hs, Geb.BitTree.Elias.Scanner.step, leafEnds, nextTotal]
      rw [ite_eq_left (by omega)] at hst2
      rw [ha] at hvalid
      have ht6' : c2.workTapes 6 =
          Function.update (cfg.workTapes 6) (v.size : ℤ) (some (plain b)) := by
        rw [hu6.1, ht6]
      obtain ⟨hlive, hst10, hin10, hout10, hb10⟩ := configs_lengthEnd c2 cfg width v b
        a.forks a.leaves k hv0 hnext (by omega) hst2 hp2 (by rw [hu0.2, hp0])
        (by rw [hu1.2]; exact hl.leavesPos) (by rw [hu6.2, hp6]) (by rw [hu7.2, hp7])
        (by rw [hu8.2, hp8]) hlen ht6' hu7.1 hu8.1 hpend2 hneg hbeyond
        (by have := hbinc _ (Nat.le_refl _); rwa [← hc2def] at this)
      have e2 : machine.configs cfg (1 + (2 * flips v.size.bits + 1)) = c2 := by
        rw [configs_add, hc1]
        exact hc2def.symm
      have hfin : machine.configs cfg (macroCost a b) = machine.configs c2
          (1 + 1 + ((v.size + 1).size + 1) + ((v.size + 1).size + 1) + (v.size + 1)) := by
        rw [hm, configs_add, e2]
      unfold BitSpec
      rw [hfin, hm, ha]
      refine ⟨Represents.ofLive hst10 hlive hvalid hw1, by rw [hin10, hin2, hin1], ?_, ?_⟩
      · exact outputString_add_nil cfg _ _ hout12 (by rw [e2]; exact hout10)
      · exact headBound_add cfg width _ _ hbB (by rw [e2]; exact hb10)
    · have hm : macroCost a b = 1 + (2 * flips v.size.bits + 1) := by
        simp [macroCost, hc, hs, he, inc]
      have ha : accountStep a b = ⟨(.length (r - 1) (Nat.bit b v), k), a.forks, a.leaves, 0⟩ := by
        simp [accountStep, hc, hs, Geb.BitTree.Elias.Scanner.step, he, leafEnds, nextTotal]
      have hfin : machine.configs cfg (macroCost a b) = c2 := by
        rw [hm, configs_add, hc1]
        exact hc2def.symm
      rw [ite_eq_right (by omega)] at hst2
      rw [ha] at hvalid
      have hL : lengthLsb (r - 1) (Nat.bit b v) = lengthLsb r v := by
        unfold lengthLsb
        rw [hsb]
        congr 1
        omega
      have hLv : lengthLsb r v - ((r - 1 : ℕ) : ℤ) = (v.size : ℤ) := by
        unfold lengthLsb
        omega
      have hlive : LiveRep width c2 ⟨(.length (r - 1) (Nat.bit b v), k), a.forks, a.leaves, 0⟩ := by
        refine ⟨hpend2, ?_, ?_, ?_⟩
        · change c2.workTapePos 0 = (((Nat.bit b v).size - 1 : ℕ) : ℤ)
          rw [hu0.2, hp0, hsb]
          simp
        · rw [hu1.2]
          exact hl.leavesPos
        · change PairRep sizeLayout 0 width c2 (r - 1 + (Nat.bit b v).size) (Nat.bit b v).size ∧
            LengthRead c2 (r - 1) (Nat.bit b v)
          rw [hsb, show r - 1 + (v.size + 1) = r + v.size by omega]
          refine ⟨hp2, ?_⟩
          have ht6' : c2.workTapes 6 =
              Function.update (cfg.workTapes 6) (v.size : ℤ) (some (plain b)) := by
            rw [hu6.1, ht6]
          have hne : ∀ j : ℕ, j ≠ r - 1 → lengthLsb r v - (j : ℤ) ≠ (v.size : ℤ) := by
            intro j hj
            unfold lengthLsb
            omega
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · funext j
            rw [bitsAt_bit_mul_pow, show r - 1 + 1 = r by omega]
            simp only [digitsFrom, ht6', hL, cell_neg]
            by_cases hj : j = r - 1
            · subst hj
              rw [hLv, Function.update_self, digit_plain, ite_eq_left rfl]
            · rw [ite_eq_right hj, Function.update_of_ne (hne j hj)]
              have := congrFun hlen.digits j
              simp only [digitsFrom, cell_neg] at this
              exact this
          · intro j
            rw [ht6', hL, cell_neg, hsb]
            by_cases hj : j = r - 1
            · subst hj
              rw [hLv, Function.update_self]
              simp only [reduceCtorEq, false_iff]
              omega
            · rw [Function.update_of_ne (hne j hj)]
              have := hlen.blank j
              rw [cell_neg] at this
              rw [this]
              constructor <;> intro h' <;> omega
          · intro z
            rw [ht6']
            by_cases hz : z = v.size
            · subst hz
              rw [Function.update_self, origin_plain]
            · rw [Function.update_of_ne hz]
              exact hlen.untagged z
          · intro z hz
            rw [hL] at hz
            have hz' : z ≠ (v.size : ℤ) := by
              unfold lengthLsb at hz
              omega
            rw [ht6', Function.update_of_ne hz']
            exact hlen.beyond z hz
          · rw [hu6.2, hp6, hsb]
            simp
          · rw [hu7.1]
            exact hlen.counter
          · rw [hu7.2, hp7, hsb]
            simp
          · rw [hu8.1]
            exact hlen.marker
          · rw [hu8.2, hp8, pop_bit b v hv0]
            simp
          · rw [hsb]
            exact ⟨fun z hz ↦ (hneg z hz).1, fun z hz ↦ (hneg z hz).2, hbeyond⟩
      unfold BitSpec
      rw [hfin, hm, ha]
      exact ⟨Represents.ofLive (by rw [hst2]; rfl) hlive hvalid hw1, by rw [hin2, hin1], hout12,
        hbB⟩

end Geb.BitTree.EliasBinary
