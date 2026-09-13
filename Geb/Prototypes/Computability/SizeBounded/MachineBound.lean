/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.WordMachine
public import Geb.Prototypes.Computability.SizeBounded.Combinators
meta import GebMeta -- shake: keep

set_option doc.verso true

/-!
# Machine bounds for word-algebra primitives

The constant and unary projection expressions have finite-state CSLib machine witnesses.
The bounds include the final halting transition and cover empty inputs and outputs.

## Main statements

* {lit}`computableInTimeAndSpace_const` bounds a constant word function.
* {lit}`computableInTimeAndSpace_id` bounds the unary projection.

## Implementation notes

This module relates the algebra to CSLib's machine execution predicates, which depend on
classical choice. It proves primitive cases, not a general compilation theorem for the algebra.

## Tags

Turing machine, time complexity, space complexity, bitstring
-/

public section

namespace Geb.SizeBounded

open Turing MultiTapeTM
open Geb.TreeScanner (boolEmb)

/-- Before the final transition, the constant machine's state is the number of bits emitted. -/
theorem constantMachine_state (v : List Bool) (input : List (Fin 2)) :
    ∀ t, (ht : t ≤ v.length) →
      ((constantMachine v).configs ((constantMachine v).initCfg input) t).state =
        some ⟨t, by omega⟩ := by
  refine Nat.rec (fun _ ↦ rfl) (fun t ih ht ↦ ?_)
  rw [configs_succ_eq_step']
  unfold step
  rw [ih (by omega)]
  simp only [constantMachine, show t < v.length by omega, ↓reduceDIte]

/-- The constant machine emits the next bit, or nothing at the final transition. -/
theorem constantMachine_emits (v : List Bool) (input : List (Fin 2)) (t : ℕ)
    (ht : t ≤ v.length) :
    (constantMachine v).outputSymbol
      ((constantMachine v).configs ((constantMachine v).initCfg input) t) =
        v[t]?.map boolEmb := by
  unfold outputSymbol
  rw [constantMachine_state v input t ht]
  rfl

/-- The first transitions emit the corresponding prefix of the constant word. -/
theorem constantMachine_output (v : List Bool) (input : List (Fin 2)) :
    ∀ t, t ≤ v.length + 1 →
      (constantMachine v).outputString ((constantMachine v).initCfg input) t =
        (v.take t).map boolEmb := by
  refine Nat.rec (fun _ ↦ rfl) (fun t ih ht ↦ ?_)
  rw [outputString_succ, ih (by omega), constantMachine_emits v input t (by omega)]
  simp only [List.take_add_one, List.map_append, Option.toList_map]

/-- The transition after emitting the last bit halts the constant machine. -/
theorem constantMachine_halts (v : List Bool) (input : List (Fin 2)) :
    ((constantMachine v).configs ((constantMachine v).initCfg input) (v.length + 1)).state =
      none := by
  rw [configs_succ_eq_step']
  unfold step
  rw [constantMachine_state v input v.length (Nat.le_refl _)]
  simp only [constantMachine, Nat.lt_irrefl, ↓reduceDIte]

/-- A constant word function takes its output length plus one transitions and no work cells. -/
theorem computableInTimeAndSpace_const (v : List Bool) :
    ComputableInTimeAndSpace (fun _ : List Bool ↦ v) (fun _ ↦ v.length + 1) (fun _ ↦ 0) := by
  refine ⟨0, 2, v.length + 1, boolEmb, constantMachine v, fun w ↦ ?_⟩
  refine ⟨v.length + 1, Nat.le_refl _, 0, Nat.le_refl _, constantMachine_halts v _, ?_, ?_⟩
  · rw [constantMachine_output v _ _ (Nat.le_refl _), List.take_of_length_le (by omega)]
  · exact spaceUsed_zero_tapes_eq_zero _ _ rfl

/-- Before its final transition, the copy machine is live at the next input position. -/
theorem identityMachine_state_pos (input : List (Fin 2)) :
    ∀ t, t ≤ input.length →
      (identityMachine.configs (identityMachine.initCfg input) t).state = some 0 ∧
      (identityMachine.configs (identityMachine.initCfg input) t).inputPos.val = t + 1 := by
  refine Nat.rec (fun _ ↦ by simp [identityMachine]) (fun t ih ht ↦ ?_)
  obtain ⟨hq, hp⟩ := ih (by omega)
  have hs := inputSymbolInner (cfg := identityMachine.configs (identityMachine.initCfg input) t)
    t (by omega) (by omega : t < input.length)
  simp only [configs_succ_eq_step']
  unfold step
  rw [hq]
  change (identityMachine.configs (identityMachine.initCfg input) t).inputSymbol.map
      (fun _ ↦ (0 : Fin 1)) = some 0 ∧
    (moveInputPos (identityMachine.configs (identityMachine.initCfg input) t).inputPos 1).val =
      t.succ + 1
  rw [hs]
  constructor
  · rfl
  · have hm := moveInputPos_pos_of_ne_right
      (identityMachine.configs (identityMachine.initCfg input) t).inputPos (by omega)
    exact (congrArg Fin.val hm).trans (by dsimp only; omega)

/-- The copy machine emits the next input bit, or nothing at the right boundary. -/
theorem identityMachine_emits (input : List (Fin 2)) (t : ℕ) (ht : t ≤ input.length) :
    identityMachine.outputSymbol (identityMachine.configs (identityMachine.initCfg input) t) =
      input[t]? := by
  obtain ⟨hq, hp⟩ := identityMachine_state_pos input t ht
  unfold outputSymbol
  rw [hq]
  change (identityMachine.configs (identityMachine.initCfg input) t).inputSymbol = input[t]?
  by_cases hlt : t < input.length
  · rw [inputSymbolInner t (by omega) hlt, List.getElem?_eq_getElem hlt]
  · have heq : (identityMachine.configs (identityMachine.initCfg input) t).inputPos.val =
        input.length + 1 := by omega
    unfold Cfg.inputSymbol
    split
    · exact (List.getElem?_eq_none (by omega)).symm
    · exact (List.getElem?_eq_none (by omega)).symm

/-- The first transitions of the copy machine emit the corresponding input prefix. -/
theorem identityMachine_output (input : List (Fin 2)) :
    ∀ t, t ≤ input.length + 1 →
      identityMachine.outputString (identityMachine.initCfg input) t = input.take t := by
  refine Nat.rec (fun _ ↦ rfl) (fun t ih ht ↦ ?_)
  rw [outputString_succ, ih (by omega), identityMachine_emits input t (by omega),
    List.take_add_one]

/-- The copy machine halts after the right input boundary is read. -/
theorem identityMachine_halts (input : List (Fin 2)) :
    (identityMachine.configs (identityMachine.initCfg input) (input.length + 1)).state =
      none := by
  have hq := (identityMachine_state_pos input input.length (Nat.le_refl _)).1
  have hs := identityMachine_emits input input.length (Nat.le_refl _)
  unfold outputSymbol at hs
  rw [hq] at hs
  change (identityMachine.configs (identityMachine.initCfg input) input.length).inputSymbol =
    input[input.length]? at hs
  rw [List.getElem?_length] at hs
  rw [configs_succ_eq_step']
  unfold step
  rw [hq]
  change Option.map (fun _ ↦ (0 : Fin 1))
    (identityMachine.configs (identityMachine.initCfg input) input.length).inputSymbol = none
  rw [hs]
  rfl

/-- The unary projection takes input length plus one transitions and no work cells. -/
theorem computableInTimeAndSpace_id :
    ComputableInTimeAndSpace (fun w : List Bool ↦ w) (fun n ↦ n + 1) (fun _ ↦ 0) := by
  refine ⟨0, 2, 1, boolEmb, identityMachine, fun w ↦ ?_⟩
  refine ⟨(w.map boolEmb).length + 1, by simp, 0, Nat.le_refl _,
    identityMachine_halts _, ?_, ?_⟩
  · rw [identityMachine_output _ _ (Nat.le_refl _), List.take_of_length_le (by omega)]
  · exact spaceUsed_zero_tapes_eq_zero _ _ rfl

/-- The unary constant expression has the constant machine's resource bounds. -/
theorem computableInTimeAndSpace_constOf (v : List Bool) :
    ComputableInTimeAndSpace (fun w ↦ (constOf 1 v).sem ![w])
      (fun _ ↦ v.length + 1) (fun _ ↦ 0) := by
  simpa only [sem_constOf] using computableInTimeAndSpace_const v

/-- The unary projection expression has the copy machine's resource bounds. -/
theorem computableInTimeAndSpace_projOf :
    ComputableInTimeAndSpace (fun w ↦ (projOf 1 0).sem ![w])
      (fun n ↦ n + 1) (fun _ ↦ 0) := by
  simpa only [sem_projOf, Matrix.cons_val_zero] using computableInTimeAndSpace_id

end Geb.SizeBounded
