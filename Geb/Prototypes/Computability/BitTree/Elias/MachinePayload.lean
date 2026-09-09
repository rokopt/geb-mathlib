/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineHeader

set_option doc.verso true

/-!
# Executing raw leaf payloads

Each payload bit advances the input and decrements its remaining length. The final bit also
erases both binary fields and completes the leaf. These statements include the exact machine
transition count and the work-tape interval visited by every execution prefix.

## Main statements

* {lit}`configs_payload` executes one raw payload bit.
* {lit}`configs_payload_headBound` bounds all intermediate head positions.

## Tags

Elias delta code, Turing machine, payload, simulation
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Erasing complete binary fields returns to the scalar leaf-completion boundary. -/
theorem configs_clear_scan (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending : ℕ) (bs cs : List Bool) (hp : 0 < pending) :
    machine.configs (scanCfg input pos stClear pending 0 bs cs)
        (max bs.length cs.length + 3) =
      modelCfg input pos (Scanner.finish pending) [] [] ∧
    machine.outputString (scanCfg input pos stClear pending 0 bs cs)
        (max bs.length cs.length + 3) = [] := by
  have h := configs_clear_ready (scanCfg input pos stClear pending 0 bs cs)
    bs cs (bs.length + 1) (cs.length + 1)
  rw [clearingCfg_scanCfg, completedCfg_scanCfg _ _ _ _ _ _ hp] at h
  simpa only [show max (bs.length + 1) (cs.length + 1) + 2 =
    max bs.length cs.length + 3 by omega] using h

/-- Reading one payload bit includes cleanup exactly when its remaining count is one. -/
theorem configs_payload (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending remaining : ℕ) (bs cs : List Bool) (b : Bool)
    (hp : 0 < pending) (hr : 0 < remaining) (hc : Counter.value cs = remaining)
    (hin : (scanCfg input pos stPayloadBit pending 0 bs cs).inputSymbol = some (boolEmb b)) :
    machine.configs (scanCfg input pos stPayloadBit pending 0 bs cs)
        (if remaining = 1 then 2 * cs.length + max bs.length cs.length + 7
          else 2 * cs.length + 4) =
      (if remaining = 1 then modelCfg input (moveInputPos pos 1) (Scanner.finish pending) [] []
        else scanCfg input (moveInputPos pos 1) stPayloadBit pending 0 bs (Counter.decrement cs)) ∧
    machine.outputString (scanCfg input pos stPayloadBit pending 0 bs cs)
        (if remaining = 1 then 2 * cs.length + max bs.length cs.length + 7
          else 2 * cs.length + 4) = [] := by
  have hread := configs_output_one _ _ (step_payload input pos pending 0 bs cs b hin)
    (outputSymbol_read _ stPayloadBit b rfl hin
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hdec := configs_decrement_true_scan input (moveInputPos pos 1) pending 0 bs cs
    (by omega)
  by_cases he : remaining = 1
  · have hseen : (Counter.decrement cs).any id = false := by
      apply (Counter.any_eq_false_iff _).mpr
      rw [Counter.value_decrement _ (by omega), hc, he]
    rw [hseen] at hdec
    have hfirst := configs_output_add _ _ _ 1 (2 * cs.length + 3) hread hdec
    have hclear := configs_clear_scan input (moveInputPos pos 1) pending bs
      (Counter.decrement cs) hp
    rw [Counter.length_decrement] at hclear
    have hall := configs_output_add _ _ _ (1 + (2 * cs.length + 3))
      (max bs.length cs.length + 3) hfirst hclear
    simpa only [he, ↓reduceIte,
      show 1 + (2 * cs.length + 3) + (max bs.length cs.length + 3) =
        2 * cs.length + max bs.length cs.length + 7 by omega] using hall
  · have hseen : (Counter.decrement cs).any id = true := by
      cases hx : (Counter.decrement cs).any id with
      | false =>
        have hz := (Counter.any_eq_false_iff _).mp hx
        rw [Counter.value_decrement _ (by omega), hc] at hz
        omega
      | true => rfl
    rw [hseen] at hdec
    have hall := configs_output_add _ _ _ 1 (2 * cs.length + 3) hread hdec
    simpa only [he, ↓reduceIte, afterDecrement,
      show 1 + (2 * cs.length + 3) = 2 * cs.length + 4 by omega] using hall

/-- Every payload-bit execution prefix stays inside a bound containing the initial field blanks
and the positive pending count. -/
theorem configs_payload_headBound (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending remaining : ℕ) (bs cs : List Bool) (b : Bool) (width : ℕ)
    (hp : 0 < pending) (hr : 0 < remaining) (hc : Counter.value cs = remaining)
    (hpw : pending ≤ width) (hbw : bs.length + 1 ≤ width) (hcw : cs.length + 1 ≤ width)
    (hin : (scanCfg input pos stPayloadBit pending 0 bs cs).inputSymbol = some (boolEmb b))
    (t : ℕ) (ht : t ≤ if remaining = 1 then 2 * cs.length + max bs.length cs.length + 7
      else 2 * cs.length + 4) :
    HeadBound width (machine.configs (scanCfg input pos stPayloadBit pending 0 bs cs) t) := by
  have hb : ∀ q, HeadBound width
      (scanCfg input (moveInputPos pos 1) q pending 0 bs cs) := by
    intro q
    exact scanCfg_headBound _ _ _ _ _ _ _ _ hpw (by omega) hbw hcw
  have hdecbound : ∀ r ≤ 2 * cs.length + 3, HeadBound width (machine.configs
      (scanCfg input (moveInputPos pos 1) (stDecrement true) pending 0 bs cs) r) := by
    intro r hr'
    have h := configs_decrement_headBound
      (scanCfg input (moveInputPos pos 1) (stDecrement true) pending 0 bs cs)
      true cs width (hb _) hcw (by omega) r hr'
    rwa [counterCfg_scanCfg_true] at h
  have hstart : HeadBound width (scanCfg input pos stPayloadBit pending 0 bs cs) :=
    scanCfg_headBound _ _ _ _ _ _ _ _ hpw (by omega) hbw hcw
  have hs := step_payload input pos pending 0 bs cs b hin
  by_cases he : remaining = 1
  · have hseen : (Counter.decrement cs).any id = false := by
      apply (Counter.any_eq_false_iff _).mpr
      rw [Counter.value_decrement _ (by omega), hc, he]
    have hdec := (configs_decrement_true_scan input (moveInputPos pos 1) pending 0 bs cs
      (by omega)).1
    rw [hseen] at hdec
    have hclear : ∀ r ≤ max bs.length cs.length + 3, HeadBound width (machine.configs
        (scanCfg input (moveInputPos pos 1) stClear pending 0 bs (Counter.decrement cs)) r) := by
      intro r hr'
      have h := configs_clear_headBound
        (scanCfg input (moveInputPos pos 1) stClear pending 0 bs (Counter.decrement cs))
        bs (Counter.decrement cs) (bs.length + 1) ((Counter.decrement cs).length + 1) width
        (scanCfg_headBound _ _ _ _ _ _ _ _ hpw (by omega) hbw
          (by simpa only [Counter.length_decrement] using hcw)) hbw
        (by simpa only [Counter.length_decrement] using hcw)
        (by change (1 : ℤ) ≤ pending; omega) r (by rw [Counter.length_decrement]; omega)
      rwa [clearingCfg_scanCfg] at h
    apply headBound_succ _ ((2 * cs.length + 3) + (max bs.length cs.length + 3)) width
      hstart ?_ t (by simp only [he, ite_true] at ht; omega)
    rw [hs]
    apply headBound_add _ (2 * cs.length + 3) (max bs.length cs.length + 3) width hdecbound
    rw [hdec]
    exact hclear
  · apply headBound_succ _ (2 * cs.length + 3) width hstart ?_ t
      (by simp only [he, ite_false] at ht; omega)
    rw [hs]
    exact hdecbound

end Geb.BitTree.Elias.Machine
