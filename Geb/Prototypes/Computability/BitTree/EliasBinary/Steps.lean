/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Represent
public import Geb.Prototypes.Computability.TreeScanner.Steps

set_option doc.verso true

/-!
# Single transitions of the scan

Reading a bit resolves through the scan table; a stationary state resolves through the phase
table. The lemmas here give the input symbol at an interior position and at either end, the
emission and input-movement facts of both tables, and the symbol-level facts about plain and
tagged digits that the phase proofs consume.

## Main statements

* {lit}`outputSymbol_scan` and {lit}`outputSymbol_phase` state that neither table emits.
* {lit}`step_end` and {lit}`outputSymbol_end` describe the halting transition.
* {lit}`headBound_add` combines bounds on consecutive execution segments.

## Tags

Turing machine, simulation, transition
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb digit origin mismatchMove)
open Geb.TreeScanner (step_of_state)

/-- A plain digit reads as its bit. -/
theorem digit_plain (b : Bool) : digit (some (plain b)) = b := by cases b <;> rfl

/-- A tagged digit reads as its bit. -/
theorem digit_tagged (b : Bool) : digit (some (tagged b)) = b := by cases b <;> rfl

/-- A plain digit carries no tag. -/
theorem origin_plain (b : Bool) : origin (some (plain b)) = false := by cases b <;> rfl

/-- A tagged digit carries the tag. -/
theorem origin_tagged (b : Bool) : origin (some (tagged b)) = true := by cases b <;> rfl

/-- The input embedding agrees with the plain digit. -/
theorem boolEmb_eq_plain (b : Bool) : boolEmb b = plain b := by cases b <;> rfl

/-- A blank reads as zero. -/
theorem digit_none : digit none = false := rfl

/-- A blank carries no tag. -/
theorem origin_none : origin none = false := rfl

/-- The marker reads as zero and carries no tag. -/
theorem digit_marker : digit (some 0) = false := rfl

/-- The tagged zero reads as zero. -/
theorem digit_two : digit (some 2) = false := rfl

/-- The tagged zero carries the tag. -/
theorem origin_two : origin (some 2) = true := rfl

/-- The plain one reads as one. -/
theorem digit_one : digit (some 1) = true := rfl

/-- The symbol at an interior input position is its next bit. -/
theorem inputSymbol_at (w : List Bool) (t : ℕ) (ht : t < w.length)
    (cfg : Cfg 9 (Fin 4) Control (w.map boolEmb)) (hp : cfg.inputPos.val = t + 1) :
    cfg.inputSymbol = some (boolEmb w[t]) := by
  rw [inputSymbolInner t (by omega) (by simpa only [List.length_map] using ht),
    List.getElem_map]

/-- The input symbol at the right end marker is blank. -/
theorem inputSymbol_end {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (hp : cfg.inputPos.val = input.length + 1) : cfg.inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs <;> rfl

/-- The input symbol at the left end marker is blank. -/
theorem inputSymbol_start {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (hp : cfg.inputPos.val = 0) : cfg.inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs with h1 h2 <;> first | rfl | exact absurd (Fin.ext hp) h1

/-- A reading state emits nothing at a bit. -/
theorem outputSymbol_scan {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (q : Control) (hq : cfg.state = some q) (hread : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨
      q = stLengthBit ∨ q = stPayloadBit ∨ q = stDone ∨ q = stDead)
    (b : Bool) (hi : cfg.inputSymbol = some (boolEmb b)) :
    machine.outputSymbol cfg = none := by
  unfold outputSymbol
  rw [hq]
  dsimp only
  rw [hi, tr_scan q hread]
  rfl

/-- A stationary state emits nothing. -/
theorem outputSymbol_phase {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (q : Control) (hq : cfg.state = some q) (hph : q = stSizeSetup ∨ q = stSizeInit ∨
      q = stLengthEnd ∨ q = stTagLsb ∨ q = stEraseSize ∨ q = stReturnSize ∨ q = stReturnF ∨
      q = stEraseLength) :
    machine.outputSymbol cfg = none := by
  unfold outputSymbol
  rw [hq]
  dsimp only
  rw [tr_phase q hph]
  rfl

/-- At the right end marker only the finite control changes to the halting state. -/
theorem step_end {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (q : Control)
    (hq : cfg.state = some q) (hread : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨
      q = stLengthBit ∨ q = stPayloadBit ∨ q = stDone ∨ q = stDead)
    (hi : cfg.inputSymbol = none) :
    machine.step cfg = { cfg with state := none } := by
  rw [step_of_state _ _ _ hq, hi, tr_end q hread]
  apply Cfg.ext <;> simp [finish]

/-- The final transition emits exactly the accepting-state decision. -/
theorem outputSymbol_end {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (q : Control) (hq : cfg.state = some q) (hread : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨
      q = stLengthBit ∨ q = stPayloadBit ∨ q = stDone ∨ q = stDead)
    (hi : cfg.inputSymbol = none) :
    machine.outputSymbol cfg = some (boolEmb (q == stDone)) := by
  unfold outputSymbol
  rw [hq]
  dsimp only
  rw [hi, tr_end q hread]
  rfl

/-- The input position advances by one when it is not the right end marker. -/
theorem moveInputPos_pos_val {n : ℕ} (p : Fin (n + 2)) (h : p.val < n + 1) :
    (moveInputPos p 1).val = p.val + 1 := by
  change (moveInputPos p SignType.pos).val = _
  unfold moveInputPos
  have hz : ((p.val : ℤ) + (SignType.pos.cast : ℤ)).toNat = p.val + 1 := by
    change ((p.val : ℤ) + 1).toNat = p.val + 1
    omega
  rw [hz]
  dsimp only
  split
  · rfl
  · omega

/-- The input position retreats by one when it is not the left end marker. -/
theorem moveInputPos_neg_val {n : ℕ} (p : Fin (n + 2)) (h : 0 < p.val) :
    (moveInputPos p (-1)).val = p.val - 1 := by
  change (moveInputPos p SignType.neg).val = _
  unfold moveInputPos
  have hz : ((p.val : ℤ) + (SignType.neg.cast : ℤ)).toNat = p.val - 1 := by
    change ((p.val : ℤ) + -1).toNat = p.val - 1
    omega
  rw [hz]
  dsimp only
  split
  · rfl
  · omega

/-! ## The tables at each state -/

/-- The scan table at the tree state. -/
theorem scanTr_tree (b : Bool) (work : Fin 9 → Option (Fin 4)) :
    scanTr stTree b work = (if b then stCarry 2 else stZeros, stay) := rfl

/-- The scan table at the zero-run state. -/
theorem scanTr_zeros (b : Bool) (work : Fin 9 → Option (Fin 4)) :
    scanTr stZeros b work =
      if b then (if origin (work 0) then stCarry 3 else stSizeSetup, stay)
      else if work 0 = none then (stDead, stay)
      else (stZeros, fun i ↦ (none, if i = 0 then 1 else 0)) := rfl

/-- The scan table at the size-field state. -/
theorem scanTr_size (b : Bool) (work : Fin 9 → Option (Fin 4)) :
    scanTr stSizeBit b work =
      if origin (work 3) then
        (stLengthBit, fun i ↦
          if i = 3 then (some (some (tagged b)), 0)
          else if i = 5 then (none, if b then mismatchMove (work 3) (work 4) else 0)
          else if i = 6 then (some (some 1), 1)
          else if i = 7 then (none, 1)
          else if i = 8 then (none, 1)
          else (none, 0))
      else
        (stSizeBit, fun i ↦
          if i = 3 then (some (some (plain b)), -1)
          else if i = 5 then (none, if b then 1 else 0)
          else (none, 0)) := rfl

/-- The scan table at the length-field state. -/
theorem scanTr_length (b : Bool) (work : Fin 9 → Option (Fin 4)) :
    scanTr stLengthBit b work =
      if work 0 = none then (stDead, stay)
      else (stCarry 4, fun i ↦
        if i = 0 then (none, 1)
        else if i = 6 then (some (some (plain b)), 1)
        else if i = 7 then (none, 1)
        else if i = 8 then (none, if b then 1 else 0)
        else (none, 0)) := rfl

/-- The scan table at the payload state. -/
theorem scanTr_payload (b : Bool) (work : Fin 9 → Option (Fin 4)) :
    scanTr stPayloadBit b work = (stCarry 5, stay) := rfl

/-- The scan table at the accepting state. -/
theorem scanTr_done (b : Bool) (work : Fin 9 → Option (Fin 4)) :
    scanTr stDone b work = (stDead, stay) := rfl

/-- The scan table at the rejecting state. -/
theorem scanTr_dead (b : Bool) (work : Fin 9 → Option (Fin 4)) :
    scanTr stDead b work = (stDead, stay) := rfl

/-- The phase table at the size-setup state. -/
theorem phaseTr_sizeSetup (work : Fin 9 → Option (Fin 4)) :
    phaseTr stSizeSetup work =
      if origin (work 0) then
        (stSizeInit, fun i ↦
          if i = 3 then (some (some 1), -1) else if i = 5 then (none, 1) else (none, 0))
      else (stSizeSetup, fun i ↦ (none, if i = 0 then -1 else if i = 3 then 1 else 0)) := rfl

/-- The phase table at the size-initialization state. -/
theorem phaseTr_sizeInit (work : Fin 9 → Option (Fin 4)) :
    phaseTr stSizeInit work =
      (stSizeBit, fun i ↦ if i = 4 then (some (some 1), 0)
        else if i = 5 then (none, 1) else (none, 0)) := rfl

/-- The phase table at the length-end state. -/
theorem phaseTr_lengthEnd (work : Fin 9 → Option (Fin 4)) :
    phaseTr stLengthEnd work =
      (stTagLsb, fun i ↦ (none, if i = 6 ∨ i = 7 then -1 else 0)) := rfl

/-- The phase table at the tagging state. -/
theorem phaseTr_tagLsb (work : Fin 9 → Option (Fin 4)) :
    phaseTr stTagLsb work =
      (stEraseSize, fun i ↦
        if i = 6 then (some (some (tagged (digit (work 6)))), 0)
        else if i = 7 then (some (some 1), 0)
        else if i = 8 then (none, mismatchMove (work 6) (work 7))
        else (none, 0)) := rfl

/-- The phase table at the size-erasing state. -/
theorem phaseTr_eraseSize (work : Fin 9 → Option (Fin 4)) :
    phaseTr stEraseSize work =
      if work 3 = none then (stReturnSize, stay)
      else (stEraseSize, fun i ↦
        if i = 3 then (some (if origin (work 3) then some 2 else none), 1)
        else if i = 4 then (some none, 1) else (none, 0)) := rfl

/-- The phase table at the size-returning state. -/
theorem phaseTr_returnSize (work : Fin 9 → Option (Fin 4)) :
    phaseTr stReturnSize work =
      if origin (work 3) then (stReturnF, stay)
      else (stReturnSize, fun i ↦ (none, if i = 3 ∨ i = 4 then -1 else 0)) := rfl

/-- The phase table at the ruler-returning state. -/
theorem phaseTr_returnF (work : Fin 9 → Option (Fin 4)) :
    phaseTr stReturnF work =
      if origin (work 0) then (stPayloadBit, stay)
      else (stReturnF, fun i ↦ (none, if i = 0 then -1 else 0)) := rfl

/-- The phase table at the length-erasing state. -/
theorem phaseTr_eraseLength (work : Fin 9 → Option (Fin 4)) :
    phaseTr stEraseLength work =
      if work 6 = none then (stCarry 3, fun i ↦ (none, if i = 6 ∨ i = 7 then 1 else 0))
      else (stEraseLength, fun i ↦ if i = 6 ∨ i = 7 then (some none, -1) else (none, 0)) := rfl

/-! ## The specification of one input bit -/

/-- One input bit at a boundary realizes its account update in its macro cost: the boundary
representation moves to the updated account, the input head advances by one, nothing is
emitted, and every head stays within the width throughout. -/
def BitSpec {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (a : Account)
    (b : Bool) (width : ℕ) : Prop :=
  Represents width (machine.configs cfg (macroCost a b)) (accountStep a b) ∧
    (machine.configs cfg (macroCost a b)).inputPos = moveInputPos cfg.inputPos 1 ∧
    machine.outputString cfg (macroCost a b) = [] ∧
    ∀ u ≤ macroCost a b, HeadBound width (machine.configs cfg u)

/-- Bounds on consecutive execution segments combine into a bound on their concatenation. -/
theorem headBound_add {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (width a b : ℕ)
    (ha : ∀ t ≤ a, HeadBound width (machine.configs cfg t))
    (hb : ∀ t ≤ b, HeadBound width (machine.configs (machine.configs cfg a) t)) :
    ∀ t ≤ a + b, HeadBound width (machine.configs cfg t) := by
  intro t ht
  by_cases h : t ≤ a
  · exact ha t h
  · rw [show t = a + (t - a) by omega, configs_add]
    exact hb (t - a) (by omega)

/-- Empty outputs of consecutive segments concatenate to an empty output. -/
theorem outputString_add_nil {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (a b : ℕ) (ha : machine.outputString cfg a = [])
    (hb : machine.outputString (machine.configs cfg a) b = []) :
    machine.outputString cfg (a + b) = [] := by
  rw [outputString_add_eq_append, ha, hb]
  rfl

end Geb.BitTree.EliasBinary
