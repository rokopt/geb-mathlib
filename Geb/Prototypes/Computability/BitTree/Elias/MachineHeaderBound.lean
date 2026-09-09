/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineHeader

set_option doc.verso true

/-!
# Work space throughout the delta-header macros

Appending a header bit needs one additional binary cell. The following countdown sweeps
stay between their marked origin and right-hand blank. Composing these bounds controls
every intermediate configuration of both header phases.

## Implementation notes

These Cslib execution statements inherit {lit}`Classical.choice` from its input reader.

## Tags

Elias delta code, Turing machine, space complexity
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- The first binary counter's decrement stays within a boundary configuration's head bound. -/
theorem decrement_false_scan_headBound (input : List (Fin 3))
    (pos : Fin (input.length + 2)) (pending zeros : ℕ) (bs cs : List Bool) (width : ℕ)
    (hcfg : HeadBound width (scanCfg input pos (stDecrement false) pending zeros bs cs))
    (hw : bs.length + 1 ≤ width) (hb : 0 < Counter.value bs)
    (t : ℕ) (ht : t ≤ 2 * bs.length + 3) :
    HeadBound width (machine.configs
      (scanCfg input pos (stDecrement false) pending zeros bs cs) t) := by
  have h := configs_decrement_headBound
    (scanCfg input pos (stDecrement false) pending zeros bs cs) false bs width hcfg hw hb t ht
  rwa [counterCfg_scanCfg_false] at h

/-- The second binary counter's decrement stays within its boundary head bound. -/
theorem decrement_true_scan_headBound (input : List (Fin 3))
    (pos : Fin (input.length + 2)) (pending zeros : ℕ) (bs cs : List Bool) (width : ℕ)
    (hcfg : HeadBound width (scanCfg input pos (stDecrement true) pending zeros bs cs))
    (hw : cs.length + 1 ≤ width) (hc : 0 < Counter.value cs)
    (t : ℕ) (ht : t ≤ 2 * cs.length + 3) :
    HeadBound width (machine.configs
      (scanCfg input pos (stDecrement true) pending zeros bs cs) t) := by
  have h := configs_decrement_headBound
    (scanCfg input pos (stDecrement true) pending zeros bs cs) true cs width hcfg hw hc t ht
  rwa [counterCfg_scanCfg_true] at h

/-- Every width-field macro prefix stays within the available unary and binary widths. -/
theorem configs_size_headBound (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending remaining : ℕ) (bs cs : List Bool) (b : Bool)
    (hr : 0 < remaining) (hb : 0 < Counter.value bs)
    (hin : (scanCfg input pos stSizeBit pending remaining bs cs).inputSymbol = some (boolEmb b))
    (width : ℕ) (hp : pending + 1 ≤ width) (hz : remaining + 1 ≤ width)
    (hbs : bs.length + 2 ≤ width) (hcs : cs.length + 2 ≤ width)
    (t : ℕ) (ht : t ≤ if remaining = 1 then 2 * bs.length + 7 else 2) :
    HeadBound width (machine.configs
      (scanCfg input pos stSizeBit pending remaining bs cs) t) := by
  have hs := step_size input pos pending (remaining - 1) bs cs b
  rw [show remaining - 1 + 1 = remaining by omega] at hs
  have hinit := scanCfg_headBound input pos stSizeBit pending remaining bs cs width
    (by omega) (by omega) (by omega) (by omega)
  have hcheck := scanCfg_headBound input (moveInputPos pos 1) stSizeCheck pending
    (remaining - 1) (b :: bs) cs width (by omega) (by omega)
    (by simp only [List.length_cons]; omega) (by omega)
  have htwo : machine.configs (scanCfg input pos stSizeBit pending remaining bs cs) 2 =
      scanCfg input (moveInputPos pos 1)
        (if remaining - 1 = 0 then stDecrement false else stSizeBit)
        pending (remaining - 1) (b :: bs) cs := by
    rw [configs_succ_eq_step, hs hin, configs_succ_eq_step, configs_zero, step_sizeCheck]
  have hfirst : ∀ u ≤ 2, HeadBound width (machine.configs
      (scanCfg input pos stSizeBit pending remaining bs cs) u) := by
    apply headBound_succ _ 1 width hinit
    rw [hs hin]
    intro u hu
    apply headBound_succ _ 0 width hcheck ?_ u hu
    intro v hv
    have he : v = 0 := by omega
    subst v
    rw [configs_zero, step_sizeCheck]
    exact scanCfg_headBound input (moveInputPos pos 1) _ pending (remaining - 1)
      (b :: bs) cs width (by omega) (by omega)
      (by simp only [List.length_cons]; omega) (by omega)
  by_cases he : remaining = 1
  · have hv : 0 < Counter.value (b :: bs) := by rw [Counter.value_cons]; omega
    apply headBound_add _ 2 (2 * (b :: bs).length + 3) width hfirst ?_ t
      (by simp only [he, ↓reduceIte, List.length_cons] at ht ⊢; omega)
    rw [htwo]
    simp only [he, Nat.sub_self, ↓reduceIte]
    intro u hu
    exact decrement_false_scan_headBound input (moveInputPos pos 1) pending 0 (b :: bs) cs
      width (scanCfg_headBound input (moveInputPos pos 1) _ pending 0 (b :: bs) cs width
        (by omega) (by omega) (by simp only [List.length_cons]; omega) (by omega))
      (by simp only [List.length_cons]; omega) hv u hu
  · exact hfirst t (by simpa only [he, ↓reduceIte] using ht)

/-- Every length-field macro prefix is bounded by word widths, regardless of decoded value. -/
theorem configs_length_headBound (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending remaining : ℕ) (bs cs : List Bool) (b : Bool)
    (hr : 0 < remaining) (hb : Counter.value bs = remaining) (hc : 0 < Counter.value cs)
    (hin : (scanCfg input pos stLengthBit pending 0 bs cs).inputSymbol = some (boolEmb b))
    (width : ℕ) (hp : pending + 1 ≤ width) (hz : 1 ≤ width)
    (hbs : bs.length + 2 ≤ width) (hcs : cs.length + 2 ≤ width)
    (t : ℕ)
    (ht : t ≤ if remaining = 1 then 2 * bs.length + 2 * cs.length + 9
      else 2 * bs.length + 4) :
    HeadBound width (machine.configs
      (scanCfg input pos stLengthBit pending 0 bs cs) t) := by
  have hinit := scanCfg_headBound input pos stLengthBit pending 0 bs cs width
    (by omega) (by omega) (by omega) (by omega)
  have hdec := scanCfg_headBound input (moveInputPos pos 1) (stDecrement false) pending
    0 bs (b :: cs) width (by omega) (by omega) (by omega)
    (by simp only [List.length_cons]; omega)
  have hbpos : 0 < Counter.value bs := by omega
  have hfirst : ∀ u ≤ 1 + (2 * bs.length + 3), HeadBound width (machine.configs
      (scanCfg input pos stLengthBit pending 0 bs cs) u) := by
    intro u hu
    apply headBound_succ _ (2 * bs.length + 3) width hinit ?_ u (by omega)
    rw [step_length input pos pending 0 bs cs b hin]
    exact decrement_false_scan_headBound input (moveInputPos pos 1) pending 0 bs (b :: cs)
      width hdec (by omega) hbpos
  by_cases he : remaining = 1
  · have hzero : (Counter.decrement bs).any id = false := by
      apply (Counter.any_eq_false_iff _).mpr
      rw [Counter.value_decrement _ hbpos, hb, he]
    have hend : machine.configs (scanCfg input pos stLengthBit pending 0 bs cs)
        (1 + (2 * bs.length + 3)) =
      scanCfg input (moveInputPos pos 1) (stDecrement true) pending 0
        (Counter.decrement bs) (b :: cs) := by
      rw [Nat.add_comm 1, configs_succ_eq_step, step_length input pos pending 0 bs cs b hin,
        (configs_decrement_false_scan input (moveInputPos pos 1) pending 0 bs (b :: cs) hbpos).1,
        hzero]
      rfl
    have hv : 0 < Counter.value (b :: cs) := by rw [Counter.value_cons]; omega
    apply headBound_add _ (1 + (2 * bs.length + 3)) (2 * (b :: cs).length + 3)
      width hfirst ?_ t (by simp only [he, ↓reduceIte, List.length_cons] at ht ⊢; omega)
    rw [hend]
    intro u hu
    exact decrement_true_scan_headBound input (moveInputPos pos 1) pending 0
      (Counter.decrement bs) (b :: cs) width
      (scanCfg_headBound input (moveInputPos pos 1) _ pending 0
        (Counter.decrement bs) (b :: cs) width (by omega) (by omega)
        (by rw [Counter.length_decrement]; omega) (by simp only [List.length_cons]; omega))
      (by simp only [List.length_cons]; omega) hv u hu
  · exact hfirst t (by simp only [he, ↓reduceIte] at ht; omega)

end Geb.BitTree.Elias.Machine
