/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineModel
public import Geb.Prototypes.Computability.BitTree.Elias.MachineConfig
public import Geb.Prototypes.Computability.TreeScanner.Steps
public import Mathlib.Tactic.FinCases

set_option doc.verso true

/-!
# Reading input at delta-decoder boundaries

Each external reading transition advances the input once and emits nothing.
The results below expose its writes as updates of the two finite binary words;
the countdown and cleanup proofs then compose with those boundaries directly.

## Main statements

* {lit}`step_read` resolves a reading transition on an arbitrary configuration.
* {lit}`step_tree`, {lit}`step_zeros`, {lit}`step_size` and {lit}`step_length`
  describe the four kinds of header input transitions.

## Implementation notes

These statements concern the Cslib execution functions and their input reader,
whose implementation uses {lit}`Classical.choice`.

## Tags

Elias delta code, Turing machine, input, simulation
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Resolve one external reading step while leaving its work actions explicit. -/
theorem step_read {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (q : Control) (b : Bool) (hq : cfg.state = some q)
    (hin : cfg.inputSymbol = some (boolEmb b))
    (hr : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨
      q = stPayloadBit ∨ q = stDone ∨ q = stDead) :
    machine.step cfg =
      { state := (read q (boolEmb b)).q'
        inputPos := moveInputPos cfg.inputPos 1
        workTapes := fun i ↦
          match ((read q (boolEmb b)).workActions i).1 with
          | none => cfg.workTapes i
          | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
        workTapePos := fun i ↦ cfg.workTapePos i +
          ((read q (boolEmb b)).workActions i).2 } := by
  rw [Geb.TreeScanner.step_of_state _ _ q hq, hin, tr_read q _ _ hr, read_inputMove]
  refine Cfg.ext rfl rfl ?_ rfl
  funext i z
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases b <;> fin_cases i <;> rfl

/-- Reading an external bit emits nothing. -/
theorem outputSymbol_read {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (q : Control) (b : Bool) (hq : cfg.state = some q)
    (hin : cfg.inputSymbol = some (boolEmb b))
    (hr : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨
      q = stPayloadBit ∨ q = stDone ∨ q = stDead) :
    machine.outputSymbol cfg = none := by
  unfold outputSymbol
  rw [hq]
  change (machine.tr q cfg.inputSymbol cfg.workTapeSymbols).outS = none
  rw [hin, tr_read q _ _ hr, read_outS]

/-- A fork increases pending trees; a leaf initializes its implicit leading length bit. -/
theorem step_tree (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) (b : Bool)
    (hin : (scanCfg input pos stTree pending zeros bs cs).inputSymbol = some (boolEmb b)) :
    machine.step (scanCfg input pos stTree pending zeros bs cs) =
      if b then scanCfg input (moveInputPos pos 1) stTree (pending + 1) zeros bs cs
      else scanCfg input (moveInputPos pos 1) stZeros pending zeros bs (true :: cs) := by
  rw [step_read _ stTree b rfl hin (Or.inl rfl)]
  cases b <;> refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    fin_cases i <;> first | rfl | exact wordTape_cons cs true
  · funext i
    fin_cases i <;> simp [read, stTree, boolEmb_apply, consume, jump, scanCfg, stZeros]
  · rfl
  · funext i
    fin_cases i <;> simp [read, stTree, boolEmb_apply, consume, jump, scanCfg]

/-- Zeros increase the unary header count; its first one initializes the width field. -/
theorem step_zeros (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) (b : Bool)
    (hin : (scanCfg input pos stZeros pending zeros bs cs).inputSymbol = some (boolEmb b)) :
    machine.step (scanCfg input pos stZeros pending zeros bs cs) =
      if b then scanCfg input (moveInputPos pos 1) stSizeCheck pending zeros (true :: bs) cs
      else scanCfg input (moveInputPos pos 1) stZeros pending (zeros + 1) bs cs := by
  rw [step_read _ stZeros b rfl hin (Or.inr (Or.inl rfl))]
  cases b <;> refine Cfg.ext rfl rfl ?_ ?_
  · rfl
  · funext i
    fin_cases i <;> simp [read, stTree, stZeros, boolEmb_apply, consume, jump, scanCfg]
  · funext i
    fin_cases i <;> first | rfl | exact wordTape_cons bs true
  · funext i
    fin_cases i <;> simp [read, stTree, stZeros, boolEmb_apply, consume, jump, scanCfg, stSizeCheck]

/-- A width-field bit appends one digit and consumes one unary count position. -/
theorem step_size (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) (b : Bool)
    (hin : (scanCfg input pos stSizeBit pending (zeros + 1) bs cs).inputSymbol =
      some (boolEmb b)) :
    machine.step (scanCfg input pos stSizeBit pending (zeros + 1) bs cs) =
      scanCfg input (moveInputPos pos 1) stSizeCheck pending zeros (b :: bs) cs := by
  rw [step_read _ stSizeBit b rfl hin (Or.inr (Or.inr (Or.inl rfl)))]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    fin_cases i <;> simp only [read, stTree, stZeros, stSizeBit, boolEmb_apply, consume,
      jump, scanCfg, stSizeCheck, ↓reduceIte, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq]
    exact wordTape_cons bs b
  · funext i
    fin_cases i <;> simp [read, stTree, stZeros, stSizeBit, boolEmb_apply, consume,
      jump, scanCfg, stSizeCheck]

/-- A payload-length bit appends one digit and enters the width countdown. -/
theorem step_length (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) (b : Bool)
    (hin : (scanCfg input pos stLengthBit pending zeros bs cs).inputSymbol = some (boolEmb b)) :
    machine.step (scanCfg input pos stLengthBit pending zeros bs cs) =
      scanCfg input (moveInputPos pos 1) (stDecrement false) pending zeros bs (b :: cs) := by
  rw [step_read _ stLengthBit b rfl hin (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
  refine Cfg.ext rfl rfl ?_ ?_
  · funext i
    fin_cases i <;> simp only [read, stTree, stZeros, stSizeBit, stLengthBit, boolEmb_apply,
      consume, jump, scanCfg, stDecrement, ↓reduceIte, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq]
    exact wordTape_cons cs b
  · funext i
    fin_cases i <;> simp [read, stTree, stZeros, stSizeBit, stLengthBit, boolEmb_apply,
      consume, jump, scanCfg, stDecrement]

/-- A raw payload bit enters the payload countdown without changing either field. -/
theorem step_payload (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) (b : Bool)
    (hin : (scanCfg input pos stPayloadBit pending zeros bs cs).inputSymbol = some (boolEmb b)) :
    machine.step (scanCfg input pos stPayloadBit pending zeros bs cs) =
      scanCfg input (moveInputPos pos 1) (stDecrement true) pending zeros bs cs := by
  rw [step_read _ stPayloadBit b rfl hin (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]
  refine Cfg.ext rfl rfl rfl ?_
  funext i
  change (scanCfg input pos stPayloadBit pending zeros bs cs).workTapePos i + 0 = _
  exact Int.add_zero _

/-- The unary origin test selects the next width bit or begins its countdown. -/
theorem step_sizeCheck (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) :
    machine.step (scanCfg input pos stSizeCheck pending zeros bs cs) =
      scanCfg input pos (if zeros = 0 then stDecrement false else stSizeBit)
        pending zeros bs cs := by
  have ht : machine.tr stSizeCheck (scanCfg input pos stSizeCheck pending zeros bs cs).inputSymbol
      (scanCfg input pos stSizeCheck pending zeros bs cs).workTapeSymbols =
      jump (if zeros = 0 then stDecrement false else stSizeBit) := by
    change jump (if wordTape [] zeros == some 2 then _ else _) = _
    cases zeros with
    | zero => rfl
    | succ zeros =>
      rw [wordTape_succ]
      simp
  rw [Geb.TreeScanner.step_of_state _ _ stSizeCheck rfl, ht]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  change (scanCfg input pos stSizeCheck pending zeros bs cs).workTapePos i + 0 = _
  exact Int.add_zero _

/-- Checking the unary header counter emits nothing. -/
theorem outputSymbol_sizeCheck (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) :
    machine.outputSymbol (scanCfg input pos stSizeCheck pending zeros bs cs) = none := by
  rfl

end Geb.BitTree.Elias.Machine
