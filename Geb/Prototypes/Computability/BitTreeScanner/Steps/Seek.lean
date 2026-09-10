/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Cost
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Transition

set_option doc.verso true

/-!
# The two-pass tree scanner's first pass

The counting pass: from the initial configuration, the first step writes the
base markers; each input bit increments the ordinary binary count on the
ruler tape, a carry running outward through the ones and back to the base
marker; at the input's end the machine turns back over the input to its
start, where the scan begins at the closed form
{name}`Geb.BitTreeScanner.cfgAt` of the initial scan state.

## Main statements

* {lit}`Geb.BitTreeScanner.run_seekInc` — one input bit's increment runs in
  {name}`Geb.BitTreeScanner.seekIncCost` steps.
* {lit}`Geb.BitTreeScanner.run_seek` — the counting pass runs in
  {name}`Geb.BitTreeScanner.seekTime` steps.
* {lit}`Geb.BitTreeScanner.run_first` — from the initial configuration to
  the scan's start, in the counting pass's steps and the input's length and
  three.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`, as
{lit}`Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic`'s
implementation notes explain.

## Tags

Turing machine, binary counter, carry, two passes
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

section Seek

variable (w : List Bool) (i : ℕ) (hi : i ≤ w.length)

/-- The step beginning a carry: at a one at the lowest digit, the digit
becomes a zero and the head moves outward. -/
theorem seekCfg_step_one (h : i < w.length) (hk : 0 < carryLengthB i.bits) :
    bitTreeScanner.step (seekCfg w i hi) = seekCarryCfg w i hi 1 ∧
      bitTreeScanner.outputSymbol (seekCfg w i hi) = none := by
  have hsym : (seekCfg w i hi).workTapeSymbols = ![tapeCount [] 1, tapeDigits [] 0, some 1] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount [] 1, tapeDigits [] 0, tapeDigits i.bits 1] = _
    rw [show (1 : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl,
      tapeDigits_of_lt i.bits 0 (by have := carryLengthB_le_length i.bits; omega)]
    rw [show i.bits.getD 0 false = true from getD_of_lt_carryLengthB i.bits 0 hk]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (seekCfg w i hi) stSeek stSeekCarry idle idle
    (some (some 0), 1) rfl
    (by rw [hsym, inputSymbol_of_inputPos w _ i h rfl]; exact tr_seek_one _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 => rfl
    | 2 =>
      change Function.update (tapeDigits i.bits) 1 (some 0) z =
        if 1 ≤ z ∧ z ≤ ((1 : ℕ) : ℤ) then some 0 else tapeDigits i.bits z
      rw [Function.update_apply]
      by_cases hz : z = 1
      · rw [ite_eq_left hz, ite_eq_left (by omega)]
      · rw [ite_eq_right hz, ite_eq_right (by omega)]
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 => exact add_zero _
    | 2 =>
      change (1 : ℤ) + ((1 : SignType) : ℤ) = ((1 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
      rfl

/-- One step of the carry over a one. -/
theorem seekCarryCfg_step (j : ℕ) (hjk : j < carryLengthB i.bits) :
    bitTreeScanner.step (seekCarryCfg w i hi j) = seekCarryCfg w i hi (j + 1) ∧
      bitTreeScanner.outputSymbol (seekCarryCfg w i hi j) = none := by
  have hk := carryLengthB_le_length i.bits
  have hsym : (seekCarryCfg w i hi j).workTapeSymbols =
      ![tapeCount [] 1, tapeDigits [] 0, some 1] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount [] 1, tapeDigits [] 0,
      if 1 ≤ ((j : ℤ) + 1) ∧ ((j : ℤ) + 1) ≤ j then some 0 else tapeDigits i.bits ((j : ℤ) + 1)] = _
    rw [ite_eq_right (by omega), tapeDigits_of_lt _ _ (by omega),
      getD_of_lt_carryLengthB i.bits j hjk]
    rfl
  obtain ⟨hstep, hout⟩ := step_stay (seekCarryCfg w i hi j) stSeekCarry stSeekCarry idle idle
    (some (some 0), 1) rfl (by rw [hsym]; exact tr_seekCarry_one _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j' z
    match j' with
    | 0 => rfl
    | 1 => rfl
    | 2 =>
      change Function.update (fun z ↦ if 1 ≤ z ∧ z ≤ (j : ℤ) then some 0 else tapeDigits i.bits z)
        ((j : ℤ) + 1) (some 0) z =
        if 1 ≤ z ∧ z ≤ ((j + 1 : ℕ) : ℤ) then some 0 else tapeDigits i.bits z
      rw [Function.update_apply]
      by_cases hz : z = (j : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_left (by omega)]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (j : ℤ)
        · rw [ite_eq_left h1, ite_eq_left (by omega)]
        · rw [ite_eq_right h1, ite_eq_right (by omega)]
  · funext j'
    match j' with
    | 0 => exact add_zero _
    | 1 => exact add_zero _
    | 2 =>
      change (j : ℤ) + 1 + ((1 : SignType) : ℤ) = ((j + 1 : ℕ) : ℤ) + 1
      rw [SignType.coe_one]
      omega

/-- The step absorbing the carry: at a zero or above the top, the cell
becomes a one and the return begins. -/
theorem seekCarryCfg_flip :
    bitTreeScanner.step (seekCarryCfg w i hi (carryLengthB i.bits)) =
        seekBackCfg w i hi (carryLengthB i.bits) ∧
      bitTreeScanner.outputSymbol (seekCarryCfg w i hi (carryLengthB i.bits)) = none := by
  have hk' := carryLengthB_le_length i.bits
  have hlow : tapeDigits i.bits ((carryLengthB i.bits : ℤ) + 1) = none ∨
      tapeDigits i.bits ((carryLengthB i.bits : ℤ) + 1) = some 0 := by
    by_cases hlt : carryLengthB i.bits < i.bits.length
    · rw [show (carryLengthB i.bits : ℤ) + 1 = ((carryLengthB i.bits : ℕ) : ℤ) + 1 from rfl,
        tapeDigits_of_lt _ _ hlt, getD_carryLengthB i.bits hlt]
      exact Or.inr rfl
    · exact Or.inl (tapeDigits_of_ge _ _ (by omega))
  have hsym : (seekCarryCfg w i hi (carryLengthB i.bits)).workTapeSymbols =
      ![tapeCount [] 1, tapeDigits [] 0, tapeDigits i.bits ((carryLengthB i.bits : ℤ) + 1)] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount [] 1, tapeDigits [] 0,
      if 1 ≤ ((carryLengthB i.bits : ℤ) + 1) ∧ ((carryLengthB i.bits : ℤ) + 1) ≤ carryLengthB i.bits
      then some 0 else tapeDigits i.bits ((carryLengthB i.bits : ℤ) + 1)] = _
    rw [ite_eq_right (by omega)]
  obtain ⟨hstep, hout⟩ := step_stay (seekCarryCfg w i hi (carryLengthB i.bits)) stSeekCarry
    stSeekBack idle idle (some (some 1), -1) rfl
    (by rw [hsym]; exact tr_seekCarry_low _ _ _ _ hlow)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext j z
    match j with
    | 0 => rfl
    | 1 => rfl
    | 2 =>
      change Function.update
        (fun z ↦ if 1 ≤ z ∧ z ≤ (carryLengthB i.bits : ℤ) then some 0 else tapeDigits i.bits z)
        ((carryLengthB i.bits : ℤ) + 1) (some 1) z = tapeDigits (i + 1).bits z
      rw [Function.update_apply, bits_succ, tapeDigits_incB]
      by_cases hz : z = (carryLengthB i.bits : ℤ) + 1
      · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_left hz]
      · rw [ite_eq_right hz]
        by_cases h1 : 1 ≤ z ∧ z ≤ (carryLengthB i.bits : ℤ)
        · rw [ite_eq_left h1, ite_eq_left h1]
        · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right hz]
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 => exact add_zero _
    | 2 =>
      change (carryLengthB i.bits : ℤ) + 1 + ((-1 : SignType) : ℤ) = (carryLengthB i.bits : ℤ)
      rw [SignType.coe_neg_one]
      omega

/-- One step of the return over a digit. -/
theorem seekBackCfg_step (j : ℕ) (hj : j < carryLengthB i.bits) :
    bitTreeScanner.step (seekBackCfg w i hi (j + 1)) = seekBackCfg w i hi j ∧
      bitTreeScanner.outputSymbol (seekBackCfg w i hi (j + 1)) = none := by
  have hk := carryLengthB_le_length i.bits
  have hsym : (seekBackCfg w i hi (j + 1)).workTapeSymbols =
      ![tapeCount [] 1, tapeDigits [] 0, some (boolEmb ((i + 1).bits.getD j false))] := by
    rw [workTapeSymbols_eq]
    change ![tapeCount [] 1, tapeDigits [] 0, tapeDigits (i + 1).bits ((j + 1 : ℕ) : ℤ)] = _
    rw [Nat.cast_succ, tapeDigits_of_lt (i + 1).bits j (by rw [bits_succ, length_incB]; omega)]
  obtain ⟨hstep, hout⟩ := step_stay (seekBackCfg w i hi (j + 1)) stSeekBack stSeekBack idle idle
    (none, -1) rfl (by rw [hsym]; exact tr_seekBack_digit _ _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · rfl
  · funext j'
    match j' with
    | 0 => exact add_zero _
    | 1 => exact add_zero _
    | 2 =>
      change ((j + 1 : ℕ) : ℤ) + ((-1 : SignType) : ℤ) = (j : ℤ)
      rw [SignType.coe_neg_one]
      omega

/-- The step ending a carry: at the base marker, the bit is consumed and the
head steps to the lowest digit. -/
theorem seekBackCfg_exit (h : i < w.length) :
    bitTreeScanner.step (seekBackCfg w i hi 0) = seekCfg w (i + 1) h ∧
      bitTreeScanner.outputSymbol (seekBackCfg w i hi 0) = none := by
  have hsym : (seekBackCfg w i hi 0).workTapeSymbols =
      ![tapeCount [] 1, tapeDigits [] 0, some 3] := by
    rw [workTapeSymbols_eq]
    rfl
  obtain ⟨hstep, hout⟩ := step_advance (seekBackCfg w i hi 0) stSeekBack stSeek idle idle
    (none, 1) rfl
    (by rw [hsym, inputSymbol_of_inputPos w _ i h rfl]; exact tr_seekBack_base _ _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (seekBackCfg w i hi 0).inputPos SignType.pos =
      (seekCfg w (i + 1) h).inputPos
    rw [moveInputPos_pos_of_ne_right _ (by change i + 1 ≠ _; rw [List.length_map]; omega)]
    exact Fin.ext rfl
  · rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 => exact add_zero _
    | 2 =>
      change ((0 : ℕ) : ℤ) + ((1 : SignType) : ℤ) = 1
      rw [SignType.coe_one]
      rfl

/-- The step of an increment without a carry: at a zero at the lowest digit
or an empty count, the cell becomes a one and the bit is consumed. -/
theorem seekCfg_step_low (h : i < w.length) (hk : carryLengthB i.bits = 0) :
    bitTreeScanner.step (seekCfg w i hi) = seekCfg w (i + 1) h ∧
      bitTreeScanner.outputSymbol (seekCfg w i hi) = none := by
  have hlow : tapeDigits i.bits 1 = none ∨ tapeDigits i.bits 1 = some 0 := by
    by_cases hlt : 0 < i.bits.length
    · have h0 := getD_carryLengthB i.bits (by rw [hk]; exact hlt)
      rw [hk] at h0
      rw [show (1 : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl, tapeDigits_of_lt _ _ hlt, h0]
      exact Or.inr rfl
    · exact Or.inl (tapeDigits_of_ge _ _ (by omega))
  have hsym : (seekCfg w i hi).workTapeSymbols =
      ![tapeCount [] 1, tapeDigits [] 0, tapeDigits i.bits 1] := by
    rw [workTapeSymbols_eq]
    rfl
  obtain ⟨hstep, hout⟩ := step_advance (seekCfg w i hi) stSeek stSeek idle idle
    (some (some 1), 0) rfl
    (by rw [hsym, inputSymbol_of_inputPos w _ i h rfl]; exact tr_seek_low _ _ _ _ hlow)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (seekCfg w i hi).inputPos SignType.pos = (seekCfg w (i + 1) h).inputPos
    rw [moveInputPos_pos_of_ne_right _ (by change i + 1 ≠ _; rw [List.length_map]; omega)]
    exact Fin.ext rfl
  · funext j z
    match j with
    | 0 => rfl
    | 1 => rfl
    | 2 =>
      change Function.update (tapeDigits i.bits) 1 (some 1) z = tapeDigits (i + 1).bits z
      rw [Function.update_apply, bits_succ, tapeDigits_incB, hk]
      by_cases hz : z = 1
      · rw [ite_eq_left hz, ite_eq_right (by omega), ite_eq_left (by omega)]
      · rw [ite_eq_right hz, ite_eq_right (by omega), ite_eq_right (by omega)]
  · exact vec3_ext (add_zero _) (add_zero _) (add_zero _)

/-- One input bit's increment: in {name}`Geb.BitTreeScanner.seekIncCost` steps, to
the counting pass's closed form at the next bit. -/
theorem run_seekInc (h : i < w.length) :
    Run w (seekCfg w i hi) (seekCfg w (i + 1) h) (seekIncCost i) := by
  rw [seekIncCost]
  by_cases hk : carryLengthB i.bits = 0
  · rw [ite_eq_left hk]
    exact run_step _ _ (seekCfg_step_low w i hi h hk) (headsLE_seekCfg w i hi)
      (headsLE_seekCfg w (i + 1) h)
  · rw [ite_eq_right hk]
    have hk' : 0 < carryLengthB i.bits := Nat.pos_of_ne_zero hk
    have hcarry : Run w (seekCarryCfg w i hi 1) (seekCarryCfg w i hi (carryLengthB i.bits))
        (carryLengthB i.bits - 1) := by
      have := run_family (fun j ↦ seekCarryCfg w i hi (j + 1)) (carryLengthB i.bits - 1)
        (fun j hj ↦ seekCarryCfg_step w i hi (j + 1) (by omega))
        (fun j hj ↦ headsLE_seekCarryCfg w i hi (j + 1) (by omega))
      rw [show carryLengthB i.bits - 1 + 1 = carryLengthB i.bits by omega] at this
      exact this
    have hback : Run w (seekBackCfg w i hi (carryLengthB i.bits)) (seekBackCfg w i hi 0)
        (carryLengthB i.bits) :=
      run_family_down (seekBackCfg w i hi) (carryLengthB i.bits)
        (fun j hj ↦ seekBackCfg_step w i hi j hj) (fun j hj ↦ headsLE_seekBackCfg w i hi j hj)
    rw [show 2 * carryLengthB i.bits + 2 =
      1 + (carryLengthB i.bits - 1) + 1 + carryLengthB i.bits + 1 by omega]
    exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _
      (run_step _ _ (seekCfg_step_one w i hi h hk') (headsLE_seekCfg w i hi)
        (headsLE_seekCarryCfg w i hi 1 hk'))
      hcarry)
      (run_step _ _ (seekCarryCfg_flip w i hi)
        (headsLE_seekCarryCfg w i hi _ le_rfl) (headsLE_seekBackCfg w i hi _ le_rfl)))
      hback)
      (run_step _ _ (seekBackCfg_exit w i hi h) (headsLE_seekBackCfg w i hi 0 (Nat.zero_le _))
        (headsLE_seekCfg w (i + 1) h))

/-- The counting pass over the input: in {name}`Geb.BitTreeScanner.seekTime` steps,
to the counting pass's closed form at the input's end. -/
theorem run_seek :
    ∀ i, ∀ hi : i ≤ w.length, Run w (seekCfg w 0 (Nat.zero_le _)) (seekCfg w i hi) (seekTime i) :=
  Nat.rec (fun _ ↦ run_zero _ (headsLE_seekCfg w 0 _))
    (fun i ih hi ↦ run_seq _ _ _ _ _ (ih (by omega)) (run_seekInc w i (by omega) (by omega)))

end Seek

section Back

variable (w : List Bool)

/-- The first step: from the initial configuration, the base markers are
written and the count and ruler heads step to the lowest digit cell. -/
theorem initCfg_step :
    bitTreeScanner.step (bitTreeScanner.initCfg (w.map boolEmb)) = seekCfg w 0 (Nat.zero_le _) ∧
      bitTreeScanner.outputSymbol (bitTreeScanner.initCfg (w.map boolEmb)) = none := by
  obtain ⟨hstep, hout⟩ := step_stay (bitTreeScanner.initCfg (w.map boolEmb)) stInit stSeek
    (some (some 3), 1) (some (some 3), 0) (some (some 3), 1) rfl (tr_init _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (bitTreeScanner.initCfg (w.map boolEmb)).inputPos 0 = _
    rw [moveInputPos_zero]
    exact Fin.ext (Fin.val_one _)
  · have hblank : ∀ z : ℤ, Function.update (fun _ : ℤ ↦ (none : Option (Fin 4))) 0 (some 3) z =
        if z = 0 then some 3 else none := fun z ↦ by
      rw [Function.update_apply]
    funext j z
    match j with
    | 0 =>
      change Function.update (fun _ : ℤ ↦ (none : Option (Fin 4))) 0 (some 3) z = tapeCount [] z
      rw [hblank, tapeCount]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left hz]
      · rw [ite_eq_right hz, ite_eq_right hz, ite_eq_right (by rw [List.length_nil]; omega)]
    | 1 =>
      change Function.update (fun _ : ℤ ↦ (none : Option (Fin 4))) 0 (some 3) z = tapeDigits [] z
      rw [hblank, tapeDigits]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left hz]
      · rw [ite_eq_right hz, ite_eq_right hz, digitsAt,
          ite_eq_right (by rw [List.length_nil]; omega)]
    | 2 =>
      change Function.update (fun _ : ℤ ↦ (none : Option (Fin 4))) 0 (some 3) z =
        tapeDigits (0 : ℕ).bits z
      rw [hblank, Nat.zero_bits, tapeDigits]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left hz]
      · rw [ite_eq_right hz, ite_eq_right hz, digitsAt,
          ite_eq_right (by rw [List.length_nil]; omega)]
  · funext j
    match j with
    | 0 =>
      change (0 : ℤ) + ((1 : SignType) : ℤ) = 1
      rw [SignType.coe_one, zero_add]
    | 1 => exact add_zero _
    | 2 =>
      change (0 : ℤ) + ((1 : SignType) : ℤ) = 1
      rw [SignType.coe_one, zero_add]

/-- The step at the input's end of the counting pass: the input head and the
ruler head turn back. -/
theorem seekCfg_exit :
    bitTreeScanner.step (seekCfg w w.length le_rfl) = backCfg w w.length le_rfl ∧
      bitTreeScanner.outputSymbol (seekCfg w w.length le_rfl) = none := by
  obtain ⟨hstep, hout⟩ := step_retreat (seekCfg w w.length le_rfl) stSeek stBack idle idle
    (none, -1) rfl (by rw [inputSymbol_end w _ rfl]; exact tr_seek_end _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (seekCfg w w.length le_rfl).inputPos SignType.neg =
      (backCfg w w.length le_rfl).inputPos
    rw [moveInputPos_neg_of_ne_left _ (fun h ↦ by
      have := congrArg Fin.val h
      change w.length + 1 = 0 at this
      omega)]
    exact Fin.ext rfl
  · rfl
  · funext j
    match j with
    | 0 => exact add_zero _
    | 1 => exact add_zero _
    | 2 =>
      change (1 : ℤ) + ((-1 : SignType) : ℤ) = 0
      rw [SignType.coe_neg_one]
      rfl

/-- One step of the return over a bit. -/
theorem backCfg_step (i : ℕ) (hi : i < w.length) :
    bitTreeScanner.step (backCfg w (i + 1) hi) = backCfg w i (by omega) ∧
      bitTreeScanner.outputSymbol (backCfg w (i + 1) hi) = none := by
  obtain ⟨hstep, hout⟩ := step_retreat (backCfg w (i + 1) hi) stBack stBack idle idle idle rfl
    (by rw [inputSymbol_of_inputPos w _ i hi rfl]; exact tr_back_bit _ _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (backCfg w (i + 1) hi).inputPos SignType.neg = (backCfg w i _).inputPos
    rw [moveInputPos_neg_of_ne_left _ (fun h ↦ by
      have := congrArg Fin.val h
      change i + 1 = 0 at this
      omega)]
    exact Fin.ext rfl
  · rfl
  · exact vec3_ext (add_zero _) (add_zero _) (add_zero _)

/-- The step at the input's start: the head steps to the first bit and the
scan begins at its initial state. -/
theorem backCfg_exit :
    bitTreeScanner.step (backCfg w 0 (Nat.zero_le _)) = cfgAt w 0 (Nat.zero_le _) init [] ∧
      bitTreeScanner.outputSymbol (backCfg w 0 (Nat.zero_le _)) = none := by
  obtain ⟨hstep, hout⟩ := step_advance (backCfg w 0 (Nat.zero_le _)) stBack stMain idle idle idle
    rfl (by rw [inputSymbol_start w _ rfl]; exact tr_back_start _)
  refine ⟨?_, hout⟩
  rw [hstep]
  refine Cfg.ext rfl ?_ ?_ ?_
  · change moveInputPos (backCfg w 0 (Nat.zero_le _)).inputPos SignType.pos =
      (cfgAt w 0 (Nat.zero_le _) init []).inputPos
    rw [moveInputPos_pos_of_ne_right _ (by change 0 ≠ _; rw [List.length_map]; omega)]
    exact Fin.ext rfl
  · funext j z
    match j with
    | 0 => rfl
    | 1 =>
      change tapeDigits [] z = tapeLeaf init z
      rw [tapeDigits, tapeLeaf]
      by_cases hz : z = 0
      · rw [ite_eq_left hz, ite_eq_left hz]
      · rw [ite_eq_right hz, ite_eq_right hz, digitsAt,
          ite_eq_right (by rw [List.length_nil]; omega)]
        rfl
    | 2 => rfl
  · exact vec3_ext (add_zero _) (add_zero _) (add_zero _)

/-- The return over the input from any position to its start. -/
theorem run_back :
    ∀ i, ∀ hi : i ≤ w.length, Run w (backCfg w i hi) (backCfg w 0 (Nat.zero_le _)) i :=
  Nat.rec (fun _ ↦ run_zero _ (headsLE_backCfg w 0 _))
    (fun i ih hi ↦ by
      have := run_seq _ _ _ _ _
        (run_step _ _ (backCfg_step w i hi) (headsLE_backCfg w _ _) (headsLE_backCfg w _ _))
        (ih (by omega))
      rw [show 1 + i = i + 1 from Nat.add_comm 1 i] at this
      exact this)

/-- From the initial configuration to the scan's start: the first step, the
counting pass, the step turning back, the return over the input and the step
to the first bit. -/
theorem run_first :
    Run w (bitTreeScanner.initCfg (w.map boolEmb)) (cfgAt w 0 (Nat.zero_le _) init [])
      (seekTime w.length + w.length + 3) := by
  rw [show seekTime w.length + w.length + 3 = 1 + seekTime w.length + 1 + w.length + 1 by omega]
  exact run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _ (run_seq _ _ _ _ _
    (run_step _ _ (initCfg_step w) (headsLE_initCfg w) (headsLE_seekCfg w 0 _))
    (run_seek w w.length le_rfl))
    (run_step _ _ (seekCfg_exit w) (headsLE_seekCfg w _ _) (headsLE_backCfg w _ _)))
    (run_back w w.length le_rfl))
    (run_step _ _ (backCfg_exit w) (headsLE_backCfg w 0 _) (headsLE_cfgAt_init w))

end Back

end Geb.BitTreeScanner
