/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineHeader
public import Geb.Prototypes.Computability.BitTree.Elias.MachineEmpty
public import Geb.Prototypes.Computability.BitTree.Elias.MachinePayload
public import Geb.Prototypes.Computability.BitTree.Elias.MachineSimpleBound
public import Geb.Prototypes.Computability.BitTree.Elias.MachineHeaderBound

set_option doc.verso true

/-!
# One complete scanner transition on the Turing machine

The read, countdown, and cleanup phases compose to exactly one transition of the
scalar scanner. Its binary-word model retains the physical field widths, so the
cost records every sweep even when a counter has acquired leading zeros.

## Main statements

* {lit}`configs_bit` proves the exact one-bit simulation and absence of output.
* {lit}`configs_bit_headBound` bounds every intermediate work-head position.

## Implementation notes

This module states correspondence with Cslib execution and consequently inherits
{lit}`Classical.choice` from the input reader.

## Tags

Elias delta code, Turing machine, scanner, simulation
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Additional input after a completed tree enters or remains in the rejecting state. -/
theorem step_terminal (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (q : Control) (pending zeros : ℕ) (bs cs : List Bool) (b : Bool)
    (hq : q = stDone ∨ q = stDead)
    (hin : (scanCfg input pos q pending zeros bs cs).inputSymbol = some (boolEmb b)) :
    machine.step (scanCfg input pos q pending zeros bs cs) =
      scanCfg input (moveInputPos pos 1) stDead pending zeros bs cs := by
  have hr : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨
      q = stPayloadBit ∨ q = stDone ∨ q = stDead :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq))))
  rw [step_read _ q b rfl hin hr]
  rcases hq with rfl | rfl <;> refine Cfg.ext rfl rfl rfl ?_
  all_goals
    funext i
    change _ + (0 : ℤ) = _
    exact Int.add_zero _

/-- A nonempty unary prefix enters the width-field reader after its first one. -/
theorem configs_zeros_positive (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (hz : 0 < zeros)
    (hin : (scanCfg input pos stZeros pending zeros [] [true]).inputSymbol =
      some (boolEmb true)) :
    machine.configs (scanCfg input pos stZeros pending zeros [] [true]) 2 =
      scanCfg input (moveInputPos pos 1) stSizeBit pending zeros [true] [true] ∧
    machine.outputString (scanCfg input pos stZeros pending zeros [] [true]) 2 = [] := by
  have hs := step_zeros input pos pending zeros [] [true] true hin
  simp only [↓reduceIte] at hs
  have hread := configs_output_one _ _ hs
    (outputSymbol_read _ stZeros true rfl hin (Or.inr (Or.inl rfl)))
  have hc := step_sizeCheck input (moveInputPos pos 1) pending zeros [true] [true]
  rw [ite_eq_right (by omega)] at hc
  have hcheck := configs_output_one _ _ hc
    (outputSymbol_sizeCheck input (moveInputPos pos 1) pending zeros [true] [true])
  exact configs_output_add _ _ _ 1 1 hread hcheck

/-- Every complete one-bit macro realizes the scalar scanner transition at its exact cost. -/
theorem configs_bit (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (s : Scanner.State) (bs cs : List Bool) (b : Bool)
    (hs : Scanner.Active s) (hw : Words s.1 bs cs)
    (hin : (modelCfg input pos s bs cs).inputSymbol = some (boolEmb b)) :
    machine.configs (modelCfg input pos s bs cs) (bitCost s.1 bs cs b) =
      modelCfg input (moveInputPos pos 1) (Scanner.step s b)
        (nextWords s.1 bs cs b).1 (nextWords s.1 bs cs b).2 ∧
    machine.outputString (modelCfg input pos s bs cs) (bitCost s.1 bs cs b) = [] := by
  rcases s with ⟨m, pending⟩
  cases m with
  | tree =>
    obtain ⟨rfl, rfl⟩ := hw
    have h := configs_output_one _ _ (step_tree input pos pending 0 [] [] b hin)
      (outputSymbol_read _ stTree b rfl hin (Or.inl rfl))
    cases b <;>
      simpa only [Scanner.step, nextWords, bitCost, modelCfg, modeState, zeroCount,
        Bool.false_eq_true, ↓reduceIte] using h
  | zeros zeros =>
    obtain ⟨rfl, rfl⟩ := hw
    cases b with
    | false =>
      have h := configs_output_one _ _ (step_zeros input pos pending zeros [] [true] false hin)
        (outputSymbol_read _ stZeros false rfl hin (Or.inr (Or.inl rfl)))
      simpa only [Scanner.step, nextWords, bitCost, modelCfg, modeState, zeroCount,
        Bool.false_eq_true, ↓reduceIte] using h
    | true =>
      by_cases hz : zeros = 0
      · subst zeros
        simpa only [Scanner.step, nextWords, bitCost, modelCfg, modeState, zeroCount,
          ↓reduceIte] using configs_empty_leaf input pos pending hs hin
      · simpa only [Scanner.step, nextWords, bitCost, modelCfg, modeState, zeroCount,
          hz, ↓reduceIte] using configs_zeros_positive input pos pending zeros (by omega) hin
  | size remaining v =>
    have h := configs_size input pos pending remaining bs cs b hs.2.1 (by rw [hw.1]; exact hs.2.2)
      hin
    by_cases he : remaining = 1 <;>
      simpa only [Scanner.step, nextWords, bitCost, modelCfg, modeState, zeroCount,
        he, ↓reduceIte, Nat.sub_self] using h
  | length remaining v =>
    have h := configs_length input pos pending remaining bs cs b hs.2.1 hw.1
      (by rw [hw.2]; exact hs.2.2) hin
    by_cases he : remaining = 1 <;>
      simpa only [Scanner.step, nextWords, bitCost, modelCfg, modeState, zeroCount,
        he, ↓reduceIte] using h
  | payload remaining =>
    have h := configs_payload input pos pending remaining bs cs b hs.1 hs.2 hw.2 hin
    by_cases he : remaining = 1 <;>
      simpa only [Scanner.step, nextWords, bitCost, modelCfg, modeState, zeroCount,
        he, ↓reduceIte] using h
  | done =>
    have h := configs_output_one _ _ (step_terminal input pos stDone pending 0 bs cs b
      (Or.inl rfl) hin)
      (outputSymbol_read _ stDone b rfl hin
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
    exact h
  | dead =>
    have h := configs_output_one _ _ (step_terminal input pos stDead pending 0 bs cs b
      (Or.inr rfl) hin)
      (outputSymbol_read _ stDead b rfl hin
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
    exact h

/-- One free cell beyond each growing field bounds every transition of a complete bit macro. -/
theorem configs_bit_headBound (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (s : Scanner.State) (bs cs : List Bool) (b : Bool)
    (hs : Scanner.Active s) (hw : Words s.1 bs cs)
    (hin : (modelCfg input pos s bs cs).inputSymbol = some (boolEmb b))
    (width : ℕ) (hp : s.2 + 1 ≤ width) (hz : zeroCount s.1 + 1 ≤ width)
    (hb : bs.length + 2 ≤ width) (hc : cs.length + 2 ≤ width)
    (t : ℕ) (ht : t ≤ bitCost s.1 bs cs b) :
    HeadBound width (machine.configs (modelCfg input pos s bs cs) t) := by
  rcases s with ⟨m, pending⟩
  cases m with
  | tree => exact configs_tree_headBound input pos pending bs cs b width hp hb hc hin t ht
  | zeros zeros =>
    obtain ⟨rfl, rfl⟩ := hw
    cases b with
    | false =>
      exact configs_zeros_false_headBound input pos pending zeros [] [true] width
        (by omega) hz (by simpa only [List.length_nil] using Nat.le_trans (by decide) hb)
        (by simpa only [List.length_cons, List.length_nil] using Nat.le_trans (by decide) hc)
        hin t ht
    | true =>
      by_cases he : zeros = 0
      · subst zeros
        exact configs_empty_leaf_headBound input pos pending width hs (by omega)
          (by simpa only [List.length_nil] using hb) hin t ht
      · have ht' : t ≤ 2 := by simpa only [bitCost, he, ↓reduceIte] using ht
        exact configs_zeros_true_headBound input pos pending zeros width (by omega)
          (by omega) (by change zeros + 1 ≤ width at hz; omega)
          (by simpa only [List.length_nil] using hb) hin t ht'
  | size remaining v =>
    exact configs_size_headBound input pos pending remaining bs cs b hs.2.1
      (by rw [hw.1]; exact hs.2.2) hin width hp hz hb hc t ht
  | length remaining v =>
    exact configs_length_headBound input pos pending remaining bs cs b hs.2.1 hw.1
      (by rw [hw.2]; exact hs.2.2) hin width hp hz hb hc t ht
  | payload remaining =>
    exact configs_payload_headBound input pos pending remaining bs cs b width hs.1 hs.2 hw.2
      (by omega) (by omega) (by omega) hin t ht
  | done =>
    exact configs_terminal_headBound _ stDone b width rfl (Or.inl rfl) hin
      (scanCfg_headBound input pos stDone pending 0 bs cs width
        (by omega) (by omega) (by omega) (by omega)) t ht
  | dead =>
    exact configs_terminal_headBound _ stDead b width rfl (Or.inr rfl) hin
      (scanCfg_headBound input pos stDead pending 0 bs cs width
        (by omega) (by omega) (by omega) (by omega)) t ht

end Geb.BitTree.Elias.Machine
