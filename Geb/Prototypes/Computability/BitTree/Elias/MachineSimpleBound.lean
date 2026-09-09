/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineRead
public import Geb.Prototypes.Computability.BitTree.Elias.MachineCounter

set_option doc.verso true

/-!
# Head bounds for the simple decoder phases

Tree tags, unary header bits, and already completed or rejected scans take only one or two
transitions per input bit. Their direct configuration equations give bounds for every prefix.

## Tags

Elias delta code, Turing machine, space bound
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- One transition between bounded configurations stays bounded at both possible prefixes. -/
theorem configs_one_headBound {input : List (Fin 3)}
    (cfg next : Cfg 4 (Fin 3) Control input) (width : ℕ)
    (hs : machine.step cfg = next) (hcfg : HeadBound width cfg) (hnext : HeadBound width next)
    (t : ℕ) (ht : t ≤ 1) : HeadBound width (machine.configs cfg t) := by
  apply headBound_succ cfg 0 width hcfg ?_ t ht
  intro r hr
  have he : r = 0 := by omega
  subst r
  rw [configs_zero, hs]
  exact hnext

/-- A tree tag uses at most one additional pending position or payload-field cell. -/
theorem configs_tree_headBound (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending : ℕ) (bs cs : List Bool) (b : Bool) (width : ℕ)
    (hp : pending + 1 ≤ width) (hb : bs.length + 2 ≤ width) (hc : cs.length + 2 ≤ width)
    (hin : (scanCfg input pos stTree pending 0 bs cs).inputSymbol = some (boolEmb b))
    (t : ℕ) (ht : t ≤ 1) :
    HeadBound width (machine.configs (scanCfg input pos stTree pending 0 bs cs) t) := by
  apply configs_one_headBound _ _ width (step_tree input pos pending 0 bs cs b hin)
    (scanCfg_headBound _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)) ?_ t ht
  cases b
  · exact scanCfg_headBound _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by simpa only [List.length_cons] using hc)
  · exact scanCfg_headBound _ _ _ _ _ _ _ _ hp (by omega) (by omega) (by omega)

/-- A unary header zero uses one additional unary counter position. -/
theorem configs_zeros_false_headBound (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros : ℕ) (bs cs : List Bool) (width : ℕ)
    (hp : pending ≤ width) (hz : zeros + 1 ≤ width)
    (hb : bs.length + 1 ≤ width) (hc : cs.length + 1 ≤ width)
    (hin : (scanCfg input pos stZeros pending zeros bs cs).inputSymbol = some (boolEmb false))
    (t : ℕ) (ht : t ≤ 1) :
    HeadBound width (machine.configs (scanCfg input pos stZeros pending zeros bs cs) t) := by
  apply configs_one_headBound _ _ width (step_zeros input pos pending zeros bs cs false hin)
    (scanCfg_headBound _ _ _ _ _ _ _ _ hp (by omega) hb hc) ?_ t ht
  exact scanCfg_headBound _ _ _ _ _ _ _ _ hp hz hb hc

/-- A nonempty unary header ends by initializing the width field and testing its unary count. -/
theorem configs_zeros_true_headBound (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending zeros width : ℕ) (hz : 0 < zeros) (hpw : pending ≤ width)
    (hzw : zeros ≤ width) (hw : 2 ≤ width)
    (hin : (scanCfg input pos stZeros pending zeros [] [true]).inputSymbol = some (boolEmb true))
    (t : ℕ) (ht : t ≤ 2) :
    HeadBound width (machine.configs (scanCfg input pos stZeros pending zeros [] [true]) t) := by
  have hs := step_zeros input pos pending zeros [] [true] true hin
  simp only [ite_true] at hs
  have hc := step_sizeCheck input (moveInputPos pos 1) pending zeros [true] [true]
  rw [ite_eq_right (by omega : zeros ≠ 0)] at hc
  apply headBound_succ _ 1 width
    (scanCfg_headBound _ _ _ _ _ _ _ _ hpw hzw (by simp; omega) (by simpa using hw)) ?_ t ht
  rw [hs]
  intro r hr
  apply configs_one_headBound _ _ width hc
    (scanCfg_headBound _ _ _ _ _ _ _ _ hpw hzw (by simpa using hw) (by simpa using hw))
    (scanCfg_headBound _ _ _ _ _ _ _ _ hpw hzw (by simpa using hw) (by simpa using hw)) r hr

/-- Bits after completion or rejection leave all work-tape head positions unchanged. -/
theorem configs_terminal_headBound {input : List (Fin 3)}
    (cfg : Cfg 4 (Fin 3) Control input) (q : Control) (b : Bool) (width : ℕ)
    (hq : cfg.state = some q) (htm : q = stDone ∨ q = stDead)
    (hin : cfg.inputSymbol = some (boolEmb b)) (hcfg : HeadBound width cfg)
    (t : ℕ) (ht : t ≤ 1) : HeadBound width (machine.configs cfg t) := by
  apply configs_one_headBound cfg (machine.step cfg) width rfl hcfg ?_ t ht
  intro i
  have hread : q = stTree ∨ q = stZeros ∨ q = stSizeBit ∨ q = stLengthBit ∨
      q = stPayloadBit ∨ q = stDone ∨ q = stDead :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr htm))))
  rw [step_read cfg q b hq hin hread]
  rcases htm with rfl | rfl <;>
    simpa [read, stDone, stDead, stTree, stZeros, stSizeBit, stLengthBit, stPayloadBit,
      consume, jump] using hcfg i

end Geb.BitTree.Elias.Machine
