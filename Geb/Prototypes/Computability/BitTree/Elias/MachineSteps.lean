/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineConfig
public import Geb.Prototypes.Computability.TreeScanner.Steps
public import Mathlib.Tactic.FinCases

set_option doc.verso true

/-!
# Erasing completed delta fields

The cleanup subroutine moves both binary heads toward their marked origins,
erasing one cell per transition. The shorter field waits at its origin while
the longer field finishes. The pending-tree count is then decremented once.

## Main statements

* {lit}`step_clearing` describes one simultaneous erasure transition.
* {lit}`configs_clearing` describes all intermediate configurations.
* {lit}`configs_clear_done` gives the exact cleanup cost and empty output.

## Implementation notes

This module concerns Cslib execution. The underlying input reader introduces
{lit}`Classical.choice`, so these correspondence statements belong to the
execution layer rather than the pure tape representation.

## Tags

Elias delta code, Turing machine, cleanup, running time
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Two consecutive phases with no output compose by adding their exact costs. -/
theorem configs_output_add {input : List (Fin 3)}
    (cfg mid last : Cfg 4 (Fin 3) Control input) (a b : ℕ)
    (ha : machine.configs cfg a = mid ∧ machine.outputString cfg a = [])
    (hb : machine.configs mid b = last ∧ machine.outputString mid b = []) :
    machine.configs cfg (a + b) = last ∧ machine.outputString cfg (a + b) = [] := by
  constructor
  · rw [configs_add, ha.1, hb.1]
  · rw [outputString_add_eq_append, ha.1, ha.2, hb.2]
    rfl

/-- Bounds for consecutive execution intervals compose at their shared configuration. -/
theorem headBound_add {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (a b width : ℕ)
    (ha : ∀ t ≤ a, HeadBound width (machine.configs cfg t))
    (hb : ∀ t ≤ b, HeadBound width (machine.configs (machine.configs cfg a) t))
    (t : ℕ) (ht : t ≤ a + b) : HeadBound width (machine.configs cfg t) := by
  by_cases h : t ≤ a
  · exact ha t h
  · have he : t = a + (t - a) := by omega
    rw [he, configs_add]
    exact hb (t - a) (by omega)

/-- A nonempty cleanup phase takes the erasing branch of the transition table. -/
theorem tr_clearing {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (bs cs : List Bool) (p r : ℕ) (h : 0 < p + r) :
    machine.tr stClear (clearingCfg cfg bs cs p r).inputSymbol
        (clearingCfg cfg bs cs p r).workTapeSymbols =
      { jump stClear with
        workActions := fun i ↦
          if i = 2 then (if p = 0 then (none, 0) else (some none, -1))
          else if i = 3 then (if r = 0 then (none, 0) else (some none, -1))
          else (none, 0) } := by
  change clear _ = _
  have h2 : ((clearingCfg cfg bs cs p r).workTapeSymbols 2 == some 2) = decide (p = 0) :=
    prefixTape_marker bs p
  have h3 : ((clearingCfg cfg bs cs p r).workTapeSymbols 3 == some 2) = decide (r = 0) :=
    prefixTape_marker cs r
  have hm : ((clearingCfg cfg bs cs p r).workTapeSymbols 2 == some 2 &&
      (clearingCfg cfg bs cs p r).workTapeSymbols 3 == some 2) = false := by
    rw [h2, h3]
    cases p <;> cases r <;> first | rfl | omega
  unfold clear
  rw [hm, ite_eq_right Bool.false_ne_true]
  dsimp only
  congr 1
  funext i
  fin_cases i <;> cases p <;> cases r <;>
    simp only [Cfg.workTapeSymbols, clearingCfg, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq,
      ↓reduceIte, Nat.cast_zero,
      prefixTape_zero, prefixTape_succ_ne_marker, or_true, true_or, or_false, false_or,
      Nat.succ_ne_zero]

/-- One erasure transition lowers each positive binary head by one. -/
theorem step_clearing {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (bs cs : List Bool) (p r : ℕ) (h : 0 < p + r) :
    machine.step (clearingCfg cfg bs cs p r) = clearingCfg cfg bs cs (p - 1) (r - 1) := by
  rw [Geb.TreeScanner.step_of_state _ _ stClear rfl, tr_clearing cfg bs cs p r h]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext i
    fin_cases i <;> cases p <;> cases r <;>
      simp only [clearingCfg, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ↓reduceIte,
        Nat.add_eq_zero_iff, one_ne_zero, and_false, add_tsub_cancel_right, zero_tsub] <;> first
      | exact prefixTape_erase bs _
      | exact prefixTape_erase cs _
  · funext i
    fin_cases i <;> cases p <;> cases r <;> simp [clearingCfg]

/-- Erasing a cell emits nothing. -/
theorem outputSymbol_clearing {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (bs cs : List Bool) (p r : ℕ) (h : 0 < p + r) :
    machine.outputSymbol (clearingCfg cfg bs cs p r) = none := by
  change (machine.tr stClear _ _).outS = none
  rw [tr_clearing cfg bs cs p r h]
  rfl

/-- At every erasure step the heads are their initial positions minus elapsed time. -/
theorem configs_clearing {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (bs cs : List Bool) (p r t : ℕ) (ht : t ≤ max p r) :
    machine.configs (clearingCfg cfg bs cs p r) t =
        clearingCfg cfg bs cs (p - t) (r - t) ∧
      machine.outputString (clearingCfg cfg bs cs p r) t = [] := by
  revert ht
  apply Nat.rec (motive := fun t ↦ t ≤ max p r →
    machine.configs (clearingCfg cfg bs cs p r) t =
        clearingCfg cfg bs cs (p - t) (r - t) ∧
      machine.outputString (clearingCfg cfg bs cs p r) t = []) ?_ ?_ t
  · intro _
    exact ⟨rfl, rfl⟩
  · intro t ih ht
    obtain ⟨hc, hout⟩ := ih (by omega)
    have hp : 0 < p - t + (r - t) := by omega
    constructor
    · rw [configs_succ_eq_step', hc, step_clearing cfg bs cs _ _ hp]
      congr 1
    · rw [outputString_succ, hout, hc, outputSymbol_clearing cfg bs cs _ _ hp]
      rfl

/-- Once both origins are reached, cleanup resets the heads and decrements pending trees. -/
theorem step_clearing_zero {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (bs cs : List Bool) :
    machine.step (clearingCfg cfg bs cs 0 0) = clearedCfg cfg := by
  have ht : machine.tr stClear (clearingCfg cfg bs cs 0 0).inputSymbol
      (clearingCfg cfg bs cs 0 0).workTapeSymbols =
      { jump stLeaf with
        workActions := fun i ↦
          if i = 0 then (none, -1)
          else if i = 1 then (none, 0)
          else (none, 1) } := rfl
  rw [Geb.TreeScanner.step_of_state _ _ stClear rfl, ht]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> simp [clearingCfg, clearedCfg, sub_eq_add_neg]

/-- The final cleanup transition emits nothing. -/
theorem outputSymbol_clearing_zero {input : List (Fin 3)}
    (cfg : Cfg 4 (Fin 3) Control input) (bs cs : List Bool) :
    machine.outputSymbol (clearingCfg cfg bs cs 0 0) = none := rfl

/-- Both fields clear in the larger head position plus one transition. -/
theorem configs_clear_done {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (bs cs : List Bool) (p r : ℕ) :
    machine.configs (clearingCfg cfg bs cs p r) (max p r + 1) = clearedCfg cfg ∧
      machine.outputString (clearingCfg cfg bs cs p r) (max p r + 1) = [] := by
  obtain ⟨hc, hout⟩ := configs_clearing cfg bs cs p r (max p r) (Nat.le_refl _)
  have hp : p - max p r = 0 := by omega
  have hr : r - max p r = 0 := by omega
  rw [hp, hr] at hc
  constructor
  · rw [configs_succ_eq_step', hc, step_clearing_zero]
  · rw [outputString_succ, hout, hc, outputSymbol_clearing_zero]
    rfl

/-- Testing the decremented pending count changes only finite control. -/
theorem step_leaf {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input) :
    machine.step (clearedCfg cfg) = completedCfg cfg := by
  rw [Geb.TreeScanner.step_of_state _ _ stLeaf rfl]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  change (clearedCfg cfg).workTapePos i + 0 = _
  exact Int.add_zero _

/-- Testing the pending count emits nothing. -/
theorem outputSymbol_leaf {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input) :
    machine.outputSymbol (clearedCfg cfg) = none := rfl

/-- Erasing and completing a leaf takes two transitions beyond the larger head position. -/
theorem configs_clear_ready {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (bs cs : List Bool) (p r : ℕ) :
    machine.configs (clearingCfg cfg bs cs p r) (max p r + 2) = completedCfg cfg ∧
      machine.outputString (clearingCfg cfg bs cs p r) (max p r + 2) = [] := by
  obtain ⟨hc, hout⟩ := configs_clear_done cfg bs cs p r
  constructor
  · rw [show max p r + 2 = (max p r + 1) + 1 by omega,
      configs_succ_eq_step', hc, step_leaf]
  · rw [show max p r + 2 = (max p r + 1) + 1 by omega,
      outputString_succ, hout, hc, outputSymbol_leaf]
    rfl

/-- Cleanup visits only the initial nonnegative head interval. -/
theorem configs_clear_headBound {input : List (Fin 3)}
    (cfg : Cfg 4 (Fin 3) Control input) (bs cs : List Bool) (p r width : ℕ)
    (hcfg : HeadBound width cfg) (hp : p ≤ width) (hr : r ≤ width)
    (hpending : 1 ≤ cfg.workTapePos 0) (t : ℕ) (ht : t ≤ max p r + 2) :
    HeadBound width (machine.configs (clearingCfg cfg bs cs p r) t) := by
  have h0 := hcfg 0
  have h1 := hcfg 1
  intro i
  by_cases hfirst : t ≤ max p r
  · rw [(configs_clearing cfg bs cs p r t hfirst).1]
    fin_cases i <;> simp [clearingCfg] <;> omega
  · by_cases hlast : t = max p r + 2
    · rw [hlast, (configs_clear_ready cfg bs cs p r).1]
      fin_cases i <;> simp [completedCfg, clearedCfg] <;> omega
    · have he : t = max p r + 1 := by omega
      rw [he, (configs_clear_done cfg bs cs p r).1]
      fin_cases i <;> simp [clearedCfg] <;> omega

end Geb.BitTree.Elias.Machine
