/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Steps

set_option doc.verso true

/-!
# One bit of the size field

During the size field the register head walks down from the zero count towards the tagged
origin, writing each bit read at the cell it leaves. The bit that reaches the origin is
written tagged, the length register receives its leading one, and the scan enters the
length field. Either way the transition costs one machine step.

## Main statements

* {lit}`step_sizeBit_plain` and {lit}`step_sizeBit_tagged` describe the two transitions
  field by field.
* {lit}`configs_bit_size` realizes the account update of a size-field bit.

## Tags

Turing machine, simulation, Elias delta code, size field
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb digit origin mismatchMove mismatchCount bitsAt flipAt
  bitsAt_eq_testBit bitsAt_of_size_le mismatchCount_flip_left)
open Geb.TreeScanner (step_of_state)

/-! ## Digit streams -/

/-- The least significant digit of a number with an appended bit. -/
theorem bitsAt_bit_zero (b : Bool) (v : ℕ) : bitsAt (Nat.bit b v) 0 = b := by
  rw [bitsAt_eq_testBit, Nat.testBit_bit_zero]

/-- The higher digits of a number with an appended bit are the digits of the number. -/
theorem bitsAt_bit_succ (b : Bool) (v j : ℕ) : bitsAt (Nat.bit b v) (j + 1) = bitsAt v j := by
  rw [bitsAt_eq_testBit, bitsAt_eq_testBit, Nat.testBit_bit_succ]

section Tapes

variable {input : List (Fin 4)} {cfg cfg' : Cfg 9 (Fin 4) Control input}

/-- A digit stream depends on its tape only. -/
theorem digitsFrom_eq_of_tape {i : Fin 9} (h : cfg'.workTapes i = cfg.workTapes i) (lsb : ℤ)
    (d : SignType) : digitsFrom cfg' i lsb d = digitsFrom cfg i lsb d := by
  funext j
  simp only [digitsFrom, h]

/-- Writing one cell of a rightward tape updates one position of its digit stream. -/
theorem digitsFrom_of_update {i : Fin 9} (p : ℕ) (s : Option (Fin 4))
    (h : cfg'.workTapes i = Function.update (cfg.workTapes i) (p : ℤ) s) :
    digitsFrom cfg' i 0 1 = Function.update (digitsFrom cfg i 0 1) p (digit s) := by
  funext j
  simp only [digitsFrom, h, cell, Int.zero_add, SignType.coe_one,
    Int.one_mul]
  by_cases hj : j = p
  · subst hj
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (by omega), Function.update_of_ne hj]
    simp only [digitsFrom, cell, Int.zero_add, SignType.coe_one, Int.one_mul]

/-- A counter pair transports along a configuration agreeing on its three tapes. -/
theorem PairData.of_layout {lay : Layout} {lsb : ℤ} {width a b : ℕ}
    (h : PairData lay lsb width cfg a b)
    (h1 : cfg'.workTapes lay.first = cfg.workTapes lay.first)
    (h2 : cfg'.workTapes lay.second = cfg.workTapes lay.second)
    (h3 : cfg'.workTapes lay.mism = cfg.workTapes lay.mism)
    (hp : cfg'.workTapePos lay.mism = cfg.workTapePos lay.mism) :
    PairData lay lsb width cfg' a b :=
  ⟨by rw [digitsFrom_eq_of_tape h1]; exact h.firstDigits,
    by rw [digitsFrom_eq_of_tape h2]; exact h.secondDigits,
    fun z ↦ by rw [h1]; exact h.originTag z, fun j ↦ by rw [h1]; exact h.firstBlank j,
    fun z ↦ by rw [h3]; exact h.marker z, by rw [hp]; exact h.mismatchPos, h.firstSize,
    h.secondSize⟩

/-- The size register reads as the value so far, shifted by the remaining count. -/
theorem SizeRead.digits_register {width r v : ℕ} (h : SizeRead width cfg r v) (hr : 0 < r) :
    digitsFrom cfg 3 0 1 = fun j ↦ if r ≤ j then bitsAt v (j - r) else false := by
  funext j
  simp only [digitsFrom, cell, Int.zero_add, SignType.coe_one, Int.one_mul,
    h.register]
  by_cases hj : r ≤ j
  · rw [ite_eq_right (by omega), ite_eq_left hj]
    by_cases hv : j < r + v.size
    · rw [ite_eq_left ⟨by omega, by omega⟩, digit_plain,
        show ((j : ℤ) - r).toNat = j - r by omega]
    · rw [ite_eq_right (fun hh ↦ hv (by omega)), bitsAt_of_size_le v _ (by omega)]
      rfl
  · rw [ite_eq_right hj]
    by_cases hz : j = 0
    · subst hz
      rfl
    · rw [ite_eq_right (by omega), ite_eq_right (fun hh ↦ hj (by omega))]
      rfl

/-- The size counter reads as one. -/
theorem SizeRead.digits_counter {width r v : ℕ} (h : SizeRead width cfg r v) :
    digitsFrom cfg 4 0 1 = bitsAt 1 := by
  funext j
  simp only [digitsFrom, cell, Int.zero_add, SignType.coe_one, Int.one_mul,
    h.counter]
  cases j with
  | zero => rfl
  | succ j =>
    rw [ite_eq_right (by omega), bitsAt_of_size_le 1 _ (by rw [Nat.size_one]; omega)]
    rfl

end Tapes

/-! ## The two transitions -/

section Step

variable {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (b : Bool)
  (hq : cfg.state = some stSizeBit) (hi : cfg.inputSymbol = some (boolEmb b))

include hq hi

/-- Away from the origin, the size-field transition writes the plain bit, steps the register
head down, and advances the mismatch head at a one. -/
theorem step_sizeBit_plain (ho : origin (cfg.workTapeSymbols 3) = false) :
    (machine.step cfg).state = some stSizeBit ∧
      (machine.step cfg).inputPos = moveInputPos cfg.inputPos 1 ∧
      (machine.step cfg).workTapes 3 =
        Function.update (cfg.workTapes 3) (cfg.workTapePos 3) (some (plain b)) ∧
      (∀ i, i ≠ 3 → (machine.step cfg).workTapes i = cfg.workTapes i) ∧
      (machine.step cfg).workTapePos 3 = cfg.workTapePos 3 - 1 ∧
      (machine.step cfg).workTapePos 5 = cfg.workTapePos 5 + (if b then 1 else 0) ∧
      ∀ i, i ≠ 3 → i ≠ 5 → (machine.step cfg).workTapePos i = cfg.workTapePos i := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stSizeBit (by simp), scanTr_size, ho]
  simp only [Bool.false_eq_true, ↓reduceIte, consumeAct]
  refine ⟨trivial, trivial, trivial, fun i h3 ↦ ?_, rfl, ?_, fun i h3 h5 ↦ ?_⟩
  · simp only [h3, ↓reduceIte]
    split_ifs <;> rfl
  · cases b <;> rfl
  · simp [h3, h5]

/-- At the origin, the size-field transition writes the tagged bit, moves the mismatch head
by the local comparison at a one, writes the leading one of the length register, and steps
the three length heads. -/
theorem step_sizeBit_tagged (ho : origin (cfg.workTapeSymbols 3) = true) :
    (machine.step cfg).state = some stLengthBit ∧
      (machine.step cfg).inputPos = moveInputPos cfg.inputPos 1 ∧
      (machine.step cfg).workTapes 3 =
        Function.update (cfg.workTapes 3) (cfg.workTapePos 3) (some (tagged b)) ∧
      (machine.step cfg).workTapes 6 =
        Function.update (cfg.workTapes 6) (cfg.workTapePos 6) (some 1) ∧
      (∀ i, i ≠ 3 → i ≠ 6 → (machine.step cfg).workTapes i = cfg.workTapes i) ∧
      (machine.step cfg).workTapePos 5 = cfg.workTapePos 5 +
        (if b then mismatchMove (cfg.workTapeSymbols 3) (cfg.workTapeSymbols 4) else 0).cast ∧
      (machine.step cfg).workTapePos 6 = cfg.workTapePos 6 + 1 ∧
      (machine.step cfg).workTapePos 7 = cfg.workTapePos 7 + 1 ∧
      (machine.step cfg).workTapePos 8 = cfg.workTapePos 8 + 1 ∧
      ∀ i, i ≠ 5 → i ≠ 6 → i ≠ 7 → i ≠ 8 →
        (machine.step cfg).workTapePos i = cfg.workTapePos i := by
  rw [step_of_state _ _ _ hq, hi, tr_scan stSizeBit (by simp), scanTr_size, ho]
  simp only [↓reduceIte, consumeAct]
  refine ⟨trivial, trivial, trivial, rfl, fun i h3 h6 ↦ ?_, rfl, rfl, rfl, rfl,
    fun i h5 h6 h7 h8 ↦ ?_⟩
  · simp only [h3, h6, ↓reduceIte]
    split_ifs <;> rfl
  · simp only [h5, h6, h7, h8, ↓reduceIte]
    split_ifs <;> simp

end Step

/-! ## The bit -/

/-- One bit of the size field realizes its account update in one step. -/
theorem configs_bit_size {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) (b : Bool) (n width : ℕ) (hv : AccountValid n a)
    (h : Represents width cfg a) (hi : cfg.inputSymbol = some (boolEmb b))
    (hw1 : a.forks.size + 1 ≤ width)
    (r v k : ℕ) (hs : a.state = (.size r v, k)) : BitSpec cfg a b width := by
  have hl : LiveRep width cfg a := h.live (by rw [hs]; simp)
  have hph := hl.phase
  unfold PhaseRep at hph
  rw [hs] at hph
  obtain ⟨hsr, hil⟩ := hph
  have hq : cfg.state = some stSizeBit := by rw [h.state, hs]; rfl
  have hact := hv.active
  rw [hs] at hact
  obtain ⟨hk, hr, hv0⟩ := hact
  have hsw := hv.sizeWidth_le
  rw [hs] at hsw
  simp only [sizeWidth] at hsw
  have hvs := size_pos_of_pos v hv0
  have hsb := size_bit b v hv0
  have hb2 : 2 ≤ Nat.bit b v := by rw [Nat.bit_val]; omega
  have hcap : capped a b = false := by simp [capped, hs]
  have hmc : macroCost a b = 1 := by simp [macroCost, hcap, hs]
  have hacc : accountStep a b = ⟨Elias.Scanner.step (.size r v, k) b, a.forks, a.leaves, 0⟩ := by
    simp [accountStep, hcap, hs, leafEnds, nextTotal]
  have hfp : cfg.workTapePos 0 = 0 := by rw [hl.forksPos, hs]; rfl
  have hvalid := accountStep_valid n a b hv
  rw [hacc] at hvalid
  have hc1 : machine.configs cfg 1 = machine.step cfg := by
    rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero]
  have ho1 : machine.outputString cfg 1 = [] := by
    rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero,
      outputSymbol_scan cfg stSizeBit hq (by simp) b hi]
    rfl
  have hd3 := hsr.digits_register hr
  have hd4 := hsr.digits_counter
  -- the boundary after the step
  have hrep : Represents width (machine.step cfg)
      ⟨Elias.Scanner.step (.size r v, k) b, a.forks, a.leaves, 0⟩ ∧
      (machine.step cfg).inputPos = moveInputPos cfg.inputPos 1 := by
    by_cases hr1 : r = 1
    · -- the bit reaching the origin
      subst hr1
      have hp3 : cfg.workTapePos 3 = 0 := by rw [hsr.registerPos]; simp
      have hs3 : cfg.workTapeSymbols 3 = some 2 := by
        rw [Cfg.workTapeSymbols, hp3, hsr.register, ite_eq_left rfl]
      have hs4 : cfg.workTapeSymbols 4 = some 1 := by
        rw [Cfg.workTapeSymbols, hsr.counterPos, hsr.counter, ite_eq_left rfl]
      have ho : origin (cfg.workTapeSymbols 3) = true := by rw [hs3]; rfl
      obtain ⟨hst, hip, ht3, ht6, htu, hp5, hp6, hp7, hp8, hpu⟩ :=
        step_sizeBit_tagged cfg b hq hi ho
      have hstep : Elias.Scanner.step (.size 1 v, k) b = (.length (Nat.bit b v - 1) 1, k) := by
        simp [Elias.Scanner.step]
      rw [hstep]
      rw [hstep] at hvalid
      refine ⟨Represents.ofLive hst ?_ hvalid hw1, hip⟩
      have hup : (machine.step cfg).workTapes 3 =
          Function.update (cfg.workTapes 3) 0 (some (tagged b)) := by
        rw [ht3, hp3]
      have hup' : (machine.step cfg).workTapes 3 =
          Function.update (cfg.workTapes 3) ((0 : ℕ) : ℤ) (some (tagged b)) := hup
      have h3 : ∀ z, (machine.step cfg).workTapes 3 z = if z = 0 then some (tagged b)
          else if (1 : ℤ) ≤ z ∧ z < 1 + v.size then some (plain (bitsAt v (z - 1).toNat))
          else none := by
        intro z
        rw [hup]
        by_cases hz : z = 0
        · subst hz
          rw [Function.update_self, ite_eq_left rfl]
        · rw [Function.update_of_ne hz, hsr.register, ite_eq_right hz, ite_eq_right hz,
            Nat.cast_one]
      have h6 : ∀ z, (machine.step cfg).workTapes 6 z = if z = 0 then some 1 else none := by
        intro z
        rw [ht6, hil.registerPos]
        by_cases hz : z = 0
        · subst hz
          rw [Function.update_self, ite_eq_left rfl]
        · rw [Function.update_of_ne hz, ite_eq_right hz]
          exact hil.register z
      have hd3' : digitsFrom (machine.step cfg) 3 0 1 = bitsAt (Nat.bit b v) := by
        rw [digitsFrom_of_update 0 (some (tagged b)) hup', hd3, digit_tagged]
        funext j
        cases j with
        | zero => rw [Function.update_self, bitsAt_bit_zero]
        | succ j =>
          rw [Function.update_of_ne (by omega), bitsAt_bit_succ, ite_eq_left (by omega),
            Nat.add_sub_cancel]
      have hd4' : digitsFrom (machine.step cfg) 4 0 1 = bitsAt 1 := by
        rw [digitsFrom_eq_of_tape (htu 4 (by decide) (by decide)), hd4]
      have hb10 : bitsAt 1 0 = true := by rw [bitsAt_eq_testBit]; decide
      have hold : digitsFrom cfg 3 0 1 0 = false := by
        rw [hd3]
        exact ite_eq_right (by omega)
      have hm5 : (machine.step cfg).workTapePos 5 =
          (mismatchCount width (bitsAt (Nat.bit b v)) (bitsAt 1) : ℤ) := by
        rw [hp5, hsr.mismPos, hd4, hs3, hs4, ← hd3', digitsFrom_of_update 0 (some (tagged b)) hup',
          digit_tagged]
        cases b
        · rw [Function.update_eq_self_iff.mpr hold.symm]
          simp
        · rw [show Function.update (digitsFrom cfg 3 0 1) 0 true = flipAt (digitsFrom cfg 3 0 1) 0
            by unfold flipAt; rw [hold]; rfl,
            mismatchCount_flip_left _ _ _ _ (show 0 < width by omega), hold, hb10]
          congr 1
      have hL : lengthLsb (Nat.bit b v - 1) 1 = ((Nat.bit b v - 1 : ℕ) : ℤ) := by
        simp only [lengthLsb, Nat.size_one, Nat.add_sub_cancel]
      have hcell : ∀ j, cell (lengthLsb (Nat.bit b v - 1) 1) (-1) j =
          ((Nat.bit b v - 1 : ℕ) : ℤ) - j := by
        intro j
        rw [hL]
        simp [cell, Int.sub_eq_add_neg]
      refine ⟨hl.pending.of_layout (htu 0 (by decide) (by decide)) (htu 1 (by decide) (by decide))
        (htu 2 (by decide) (by decide)) (hpu 2 (by decide) (by decide) (by decide) (by decide)),
        ?_, ?_, ?_⟩
      · change (machine.step cfg).workTapePos 0 = ((Nat.size 1 - 1 : ℕ) : ℤ)
        rw [hpu 0 (by decide) (by decide) (by decide) (by decide), hfp, Nat.size_one]
        rfl
      · rw [hpu 1 (by decide) (by decide) (by decide) (by decide), hl.leavesPos]
      change PairRep sizeLayout 0 width (machine.step cfg) (Nat.bit b v - 1 + Nat.size 1)
        (Nat.size 1) ∧ LengthRead (machine.step cfg) (Nat.bit b v - 1) 1
      rw [show Nat.bit b v - 1 + Nat.size 1 = Nat.bit b v by rw [Nat.size_one]; omega,
        Nat.size_one]
      refine ⟨⟨⟨hd3', hd4', ?_, ?_, ?_, hm5, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
      · intro z
        change origin ((machine.step cfg).workTapes 3 z) = decide (z = 0)
        rw [h3]
        split_ifs with hz <;> simp [hz, origin_tagged, origin_plain, origin_none]
      · intro j
        change (machine.step cfg).workTapes 3 (cell 0 1 j) = none ↔ _
        rw [hsb, h3]
        simp only [cell, Int.zero_add, SignType.coe_one, Int.one_mul]
        cases j with
        | zero => simp
        | succ j =>
          rw [ite_eq_right (by omega)]
          split_ifs with hc
          · simp only [false_iff]
            omega
          · simp only [true_iff]
            omega
      · intro z
        change (machine.step cfg).workTapes 5 z = _
        rw [htu 5 (by decide) (by decide)]
        exact hsr.marker z
      · rw [hsb]
        omega
      · rw [Nat.size_one]
        omega
      · change (machine.step cfg).workTapePos 3 = 0
        rw [hpu 3 (by decide) (by decide) (by decide) (by decide), hp3]
      · change (machine.step cfg).workTapePos 4 = 0
        rw [hpu 4 (by decide) (by decide) (by decide) (by decide), hsr.counterPos]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · funext j
        rw [bitsAt_eq_testBit, Nat.one_mul, Nat.testBit_two_pow]
        simp only [digitsFrom, hcell, h6]
        by_cases hj : j = Nat.bit b v - 1
        · subst hj
          rw [ite_eq_left (by omega), digit_one, decide_eq_true rfl]
        · rw [ite_eq_right (by omega), digit_none, decide_eq_false (fun hh ↦ hj hh.symm)]
      · intro j
        rw [hcell, h6, Nat.size_one]
        by_cases hj : j = Nat.bit b v - 1
        · subst hj
          rw [ite_eq_left (by omega)]
          simp only [reduceCtorEq, false_iff]
          omega
        · rw [ite_eq_right (by omega)]
          simp only [true_iff]
          omega
      · intro z
        rw [h6]
        split_ifs <;> rfl
      · intro z hz
        rw [hL] at hz
        rw [h6, ite_eq_right (by omega)]
      · rw [hp6, hil.registerPos, Nat.size_one]
        rfl
      · intro z
        rw [htu 7 (by decide) (by decide)]
        exact hil.counter z
      · rw [hp7, hil.counterPos, Nat.size_one]
        rfl
      · intro z
        rw [htu 8 (by decide) (by decide)]
        exact hil.marker z
      · rw [hp8, hil.mismPos, pop_one]
        rfl
      · refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_, fun j hj ↦ ?_⟩
        · rw [h3, ite_eq_right (by omega), ite_eq_right (by omega)]
        · rw [htu 4 (by decide) (by decide), hsr.counter, ite_eq_right (by omega)]
        · have hj' : (j : ℤ) ≠ 0 := by
            intro h0
            rw [Nat.cast_eq_zero] at h0
            subst h0
            simp at hj
          rw [htu 4 (by decide) (by decide), hsr.counter, ite_eq_right hj']
    · -- a bit away from the origin
      have hp3 : cfg.workTapePos 3 = (r : ℤ) - 1 := hsr.registerPos
      have hs3 : cfg.workTapeSymbols 3 = none := by
        rw [Cfg.workTapeSymbols, hp3, hsr.register, ite_eq_right (by omega),
          ite_eq_right (by omega)]
      have ho : origin (cfg.workTapeSymbols 3) = false := by rw [hs3]; rfl
      obtain ⟨hst, hip, ht3, htu, hp3', hp5, hpu⟩ := step_sizeBit_plain cfg b hq hi ho
      have hstep : Elias.Scanner.step (.size r v, k) b = (.size (r - 1) (Nat.bit b v), k) := by
        simp [Elias.Scanner.step, hr1]
      rw [hstep]
      rw [hstep] at hvalid
      refine ⟨Represents.ofLive hst ?_ hvalid hw1, hip⟩
      have hup : (machine.step cfg).workTapes 3 =
          Function.update (cfg.workTapes 3) ((r - 1 : ℕ) : ℤ) (some (plain b)) := by
        rw [ht3, hp3]
        congr 1
        omega
      have hold : digitsFrom cfg 3 0 1 (r - 1) = false := by
        rw [hd3]
        exact ite_eq_right (by omega)
      have hm5 : (machine.step cfg).workTapePos 5 = (mismatchCount width
          (digitsFrom (machine.step cfg) 3 0 1) (digitsFrom (machine.step cfg) 4 0 1) : ℤ) := by
        rw [hp5, hsr.mismPos, digitsFrom_of_update (r - 1) (some (plain b)) hup,
          digitsFrom_eq_of_tape (htu 4 (by decide)), digit_plain]
        cases b
        · rw [Function.update_eq_self_iff.mpr hold.symm]
          simp
        · rw [show Function.update (digitsFrom cfg 3 0 1) (r - 1) true =
              flipAt (digitsFrom cfg 3 0 1) (r - 1) by unfold flipAt; rw [hold]; rfl,
            mismatchCount_flip_left _ _ _ _ (show r - 1 < width by omega), hold, hd4,
            bitsAt_of_size_le 1 (r - 1) (by rw [Nat.size_one]; omega)]
          simp
      have h3 : ∀ z, (machine.step cfg).workTapes 3 z = if z = 0 then some 2
          else if ((r - 1 : ℕ) : ℤ) ≤ z ∧ z < ((r - 1 : ℕ) : ℤ) + (Nat.bit b v).size then
            some (plain (bitsAt (Nat.bit b v) (z - ((r - 1 : ℕ) : ℤ)).toNat))
          else none := by
        intro z
        rw [hup, hsb]
        by_cases hz : z = ((r - 1 : ℕ) : ℤ)
        · subst hz
          rw [Function.update_self, ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
            Int.sub_self, Int.toNat_zero, bitsAt_bit_zero]
        · rw [Function.update_of_ne hz, hsr.register]
          by_cases hz0 : z = 0
          · rw [ite_eq_left hz0, ite_eq_left hz0]
          · rw [ite_eq_right hz0, ite_eq_right hz0]
            by_cases hin : (r : ℤ) ≤ z ∧ z < r + v.size
            · rw [ite_eq_left hin, ite_eq_left ⟨by omega, by omega⟩,
                show (z - ((r - 1 : ℕ) : ℤ)).toNat = (z - r).toNat + 1 by omega, bitsAt_bit_succ]
            · rw [ite_eq_right hin, ite_eq_right (fun hh ↦ hin ⟨by omega, by omega⟩)]
      refine ⟨hl.pending.of_layout (htu 0 (by decide)) (htu 1 (by decide)) (htu 2 (by decide))
        (hpu 2 (by decide) (by decide)), ?_, ?_, ?_⟩
      · change (machine.step cfg).workTapePos 0 = 0
        rw [hpu 0 (by decide) (by decide), hfp]
      · rw [hpu 1 (by decide) (by decide), hl.leavesPos]
      change SizeRead width (machine.step cfg) (r - 1) (Nat.bit b v) ∧ IdleLength (machine.step cfg)
      refine ⟨⟨h3, ?_, fun z ↦ by rw [htu 4 (by decide)]; exact hsr.counter z,
        by rw [hpu 4 (by decide) (by decide)]; exact hsr.counterPos,
        by rw [htu 5 (by decide)]; exact hsr.marker, hm5⟩, ?_⟩
      · rw [hp3', hp3]
        omega
      · exact ⟨by rw [htu 6 (by decide)]; exact hil.register,
          by rw [hpu 6 (by decide) (by decide)]; exact hil.registerPos,
          by rw [htu 7 (by decide)]; exact hil.counter,
          by rw [hpu 7 (by decide) (by decide)]; exact hil.counterPos,
          by rw [htu 8 (by decide)]; exact hil.marker,
          by rw [hpu 8 (by decide) (by decide)]; exact hil.mismPos⟩
  unfold BitSpec
  rw [hmc, hacc, hc1]
  refine ⟨hrep.1, hrep.2, ho1, fun u hu ↦ ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hu with rfl | rfl
  · rw [configs_zero]
    exact h.bound
  · rw [hc1]
    exact hrep.1.bound

end Geb.BitTree.EliasBinary
