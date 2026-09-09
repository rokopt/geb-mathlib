/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineRead
public import Geb.Prototypes.Computability.BitTree.Elias.MachineCounter
public import Geb.Prototypes.Computability.BitTree.Elias.MachineNormalize

set_option doc.verso true

/-!
# Executing the two binary delta-header fields

A width-field bit consumes one unary count position and, when that field ends,
starts the binary countdown. A length-field bit appends to the payload count and
decrements the width count. The last such bit also performs the initial payload
decrement, removing its implicit offset of one.

## Main statements

* {lit}`configs_size` executes one bit of the binary width field.
* {lit}`configs_length` executes one bit of the payload-length field.

## Implementation notes

These are correspondence statements for Cslib execution and inherit
{lit}`Classical.choice` from its input reader.

## Tags

Elias delta code, Turing machine, header, simulation
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Execute the width countdown in boundary configuration form. -/
theorem configs_decrement_false_scan (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) (hb : 0 < Counter.value bs) :
    machine.configs (scanCfg input pos (stDecrement false) pending zeros bs cs)
        (2 * bs.length + 3) =
      scanCfg input pos (afterDecrement false ((Counter.decrement bs).any id))
        pending zeros (Counter.decrement bs) cs ∧
    machine.outputString (scanCfg input pos (stDecrement false) pending zeros bs cs)
        (2 * bs.length + 3) = [] := by
  have h := configs_decrement (scanCfg input pos (stDecrement false) pending zeros bs cs)
    false bs hb
  have he := counterCfg_scanCfg_false input pos (stDecrement false)
    (afterDecrement false ((Counter.decrement bs).any id)) pending zeros bs cs
    (Counter.decrement bs)
  rw [Counter.length_decrement] at he
  rwa [counterCfg_scanCfg_false, he] at h

/-- Execute the payload countdown in boundary configuration form. -/
theorem configs_decrement_true_scan (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) (hc : 0 < Counter.value cs) :
    machine.configs (scanCfg input pos (stDecrement true) pending zeros bs cs)
        (2 * cs.length + 3) =
      scanCfg input pos (afterDecrement true ((Counter.decrement cs).any id))
        pending zeros bs (Counter.decrement cs) ∧
    machine.outputString (scanCfg input pos (stDecrement true) pending zeros bs cs)
        (2 * cs.length + 3) = [] := by
  have h := configs_decrement (scanCfg input pos (stDecrement true) pending zeros bs cs)
    true cs hc
  have he := counterCfg_scanCfg_true input pos (stDecrement true)
    (afterDecrement true ((Counter.decrement cs).any id)) pending zeros bs cs (Counter.decrement cs)
  rw [Counter.length_decrement] at he
  rwa [counterCfg_scanCfg_true, he] at h

/-- Read a width-field bit, including the unary test and any initial width decrement. -/
theorem configs_size (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending remaining : ℕ) (bs cs : List Bool) (b : Bool)
    (hr : 0 < remaining) (hb : 0 < Counter.value bs)
    (hin : (scanCfg input pos stSizeBit pending remaining bs cs).inputSymbol = some (boolEmb b)) :
    machine.configs (scanCfg input pos stSizeBit pending remaining bs cs)
        (if remaining = 1 then 2 * bs.length + 7 else 2) =
      scanCfg input (moveInputPos pos 1) (if remaining = 1 then stLengthBit else stSizeBit)
        pending (remaining - 1)
        (if remaining = 1 then Counter.decrement (b :: bs) else b :: bs) cs ∧
    machine.outputString (scanCfg input pos stSizeBit pending remaining bs cs)
        (if remaining = 1 then 2 * bs.length + 7 else 2) = [] := by
  have hs := step_size input pos pending (remaining - 1) bs cs b
  rw [show remaining - 1 + 1 = remaining by omega] at hs
  have hread := configs_output_one _ _ (hs hin)
    (outputSymbol_read _ stSizeBit b rfl hin (Or.inr (Or.inr (Or.inl rfl))))
  have hcheck := configs_output_one _ _
    (step_sizeCheck input (moveInputPos pos 1) pending (remaining - 1) (b :: bs) cs)
    (outputSymbol_sizeCheck input (moveInputPos pos 1) pending (remaining - 1) (b :: bs) cs)
  have hfirst := configs_output_add _ _ _ 1 1 hread hcheck
  by_cases he : remaining = 1
  · subst remaining
    simp only [Nat.sub_self, ↓reduceIte] at hfirst ⊢
    have hv : 1 < Counter.value (b :: bs) := by rw [Counter.value_cons]; omega
    have hseen : (Counter.decrement (b :: bs)).any id = true := by
      cases hx : (Counter.decrement (b :: bs)).any id with
      | false =>
        have hz := (Counter.any_eq_false_iff _).mp hx
        rw [Counter.value_decrement _ (by omega)] at hz
        omega
      | true => rfl
    have hdec := configs_decrement_false_scan input (moveInputPos pos 1) pending 0 (b :: bs) cs
      (by omega)
    rw [hseen] at hdec
    have h := configs_output_add _ _ _ 2 (2 * (b :: bs).length + 3) hfirst hdec
    simpa only [List.length_cons, afterDecrement, Bool.false_eq_true, ↓reduceIte,
      show 2 + (2 * (bs.length + 1) + 3) = 2 * bs.length + 7 by omega] using h
  · have hz : remaining - 1 ≠ 0 := by omega
    simpa only [he, hz, ↓reduceIte] using hfirst

/-- Read a length-field bit, decrementing the width and then any completed payload value. -/
theorem configs_length (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending remaining : ℕ) (bs cs : List Bool) (b : Bool)
    (hr : 0 < remaining) (hb : Counter.value bs = remaining) (hc : 0 < Counter.value cs)
    (hin : (scanCfg input pos stLengthBit pending 0 bs cs).inputSymbol = some (boolEmb b)) :
    machine.configs (scanCfg input pos stLengthBit pending 0 bs cs)
        (if remaining = 1 then 2 * bs.length + 2 * cs.length + 9 else 2 * bs.length + 4) =
      scanCfg input (moveInputPos pos 1) (if remaining = 1 then stPayloadBit else stLengthBit)
        pending 0 (Counter.decrement bs)
        (if remaining = 1 then Counter.decrement (b :: cs) else b :: cs) ∧
    machine.outputString (scanCfg input pos stLengthBit pending 0 bs cs)
        (if remaining = 1 then 2 * bs.length + 2 * cs.length + 9 else 2 * bs.length + 4) = [] := by
  have hread := configs_output_one _ _ (step_length input pos pending 0 bs cs b hin)
    (outputSymbol_read _ stLengthBit b rfl hin (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hdec := configs_decrement_false_scan input (moveInputPos pos 1) pending 0 bs (b :: cs)
    (by omega)
  have hfirst := configs_output_add _ _ _ 1 (2 * bs.length + 3) hread hdec
  by_cases he : remaining = 1
  · have hzero : (Counter.decrement bs).any id = false := by
      apply (Counter.any_eq_false_iff _).mpr
      rw [Counter.value_decrement _ (by omega), hb, he]
    rw [hzero] at hfirst
    have hv : 1 < Counter.value (b :: cs) := by rw [Counter.value_cons]; omega
    have hseen : (Counter.decrement (b :: cs)).any id = true := by
      cases hx : (Counter.decrement (b :: cs)).any id with
      | false =>
        have hz := (Counter.any_eq_false_iff _).mp hx
        rw [Counter.value_decrement _ (by omega)] at hz
        omega
      | true => rfl
    have hlast := configs_decrement_true_scan input (moveInputPos pos 1) pending 0
      (Counter.decrement bs) (b :: cs) (by omega)
    rw [hseen] at hlast
    have h := configs_output_add _ _ _ (1 + (2 * bs.length + 3))
      (2 * (b :: cs).length + 3) hfirst hlast
    simpa only [he, ↓reduceIte, List.length_cons, afterDecrement, Bool.false_eq_true,
      show 1 + (2 * bs.length + 3) + (2 * (cs.length + 1) + 3) =
        2 * bs.length + 2 * cs.length + 9 by omega] using h
  · have hseen : (Counter.decrement bs).any id = true := by
      cases hx : (Counter.decrement bs).any id with
      | false =>
        have hz := (Counter.any_eq_false_iff _).mp hx
        rw [Counter.value_decrement _ (by omega), hb] at hz
        omega
      | true => rfl
    rw [hseen] at hfirst
    simpa only [he, ↓reduceIte, afterDecrement, Bool.false_eq_true,
      show 1 + (2 * bs.length + 3) = 2 * bs.length + 4 by omega] using hfirst

end Geb.BitTree.Elias.Machine
