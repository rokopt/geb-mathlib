/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Machine
public import Geb.Prototypes.Computability.TreeScanner.Steps
public import Mathlib.Tactic.FinCases

set_option doc.verso true

/-!
# Returning the binary heads to their origins

After carrying, the aligned binary heads move left to their tagged origins.
The mismatch head remains fixed. At the origin, one additional transition
selects the accepting or tree state according to counter equality.

## Main statements

* {lit}`configs_return`: exact configurations during the return.
* {lit}`configs_return_done`: the complete return, including its final state change.

## Tags

Turing machine, simulation, binary counter
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- The first binary tape's origin tag resolves a return transition away from zero. -/
theorem tr_return_pos {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (p : ℕ)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)) :
    machine.tr stReturn (returnCfg cfg (p + 1)).inputSymbol
        (returnCfg cfg (p + 1)).workTapeSymbols =
      { inputMove := 0, workActions := fun i ↦ (none, if i = 2 then 0 else -1),
        outS := none, q' := some stReturn } := by
  have h : origin ((returnCfg cfg (p + 1)).workTapeSymbols 0) = false := by
    change origin (cfg.workTapes 0 (p + 1)) = false
    rw [ho]
    simp
    omega
  change (if origin ((returnCfg cfg (p + 1)).workTapeSymbols 0) then _ else _) = _
  rw [h]
  rfl

/-- A positive return position decreases by one and changes no other data. -/
theorem step_return_pos {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (p : ℕ)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)) :
    machine.step (returnCfg cfg (p + 1)) = returnCfg cfg p := by
  rw [Geb.TreeScanner.step_of_state _ _ stReturn rfl, tr_return_pos cfg p ho]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  fin_cases i <;> simp [returnCfg]

/-- Returning from a positive position emits nothing. -/
theorem outputSymbol_return_pos {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (p : ℕ)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)) :
    machine.outputSymbol (returnCfg cfg (p + 1)) = none := by
  change (machine.tr stReturn _ _).outS = none
  rw [tr_return_pos cfg p ho]

/-- Every return configuration and its empty output, before the final state change. -/
theorem configs_return {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)) (t p : ℕ) :
    machine.configs (returnCfg cfg (p + t)) t = returnCfg cfg p ∧
      machine.outputString (returnCfg cfg (p + t)) t = [] := by
  revert p
  apply Nat.rec (motive := fun t ↦ ∀ p,
    machine.configs (returnCfg cfg (p + t)) t = returnCfg cfg p ∧
      machine.outputString (returnCfg cfg (p + t)) t = []) ?_ ?_ t
  · intro p
    exact ⟨rfl, rfl⟩
  · intro t ih p
    obtain ⟨hc, hout⟩ := ih (p + 1)
    rw [show p + (t + 1) = p + 1 + t by omega]
    constructor
    · rw [configs_succ_eq_step', hc, step_return_pos cfg p ho]
    · rw [outputString_succ, hout, hc, outputSymbol_return_pos cfg p ho]
      rfl

/-- The origin marker resolves the transition that finishes returning. -/
theorem tr_return_zero {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)) :
    machine.tr stReturn (returnCfg cfg 0).inputSymbol (returnCfg cfg 0).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none,
        q' := some (if cfg.workTapes 2 (cfg.workTapePos 2) == some 0
          then stDone else stTree) } := by
  have h : origin ((returnCfg cfg 0).workTapeSymbols 0) = true := by
    change origin (cfg.workTapes 0 0) = true
    rw [ho]
    rfl
  change (if origin ((returnCfg cfg 0).workTapeSymbols 0) then _ else _) = _
  rw [h]
  rfl

/-- The origin transition changes only the finite control. -/
theorem step_return_zero {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)) :
    machine.step (returnCfg cfg 0) = returnedCfg cfg := by
  rw [Geb.TreeScanner.step_of_state _ _ stReturn rfl, tr_return_zero cfg ho]
  refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_
  funext i
  simp [returnedCfg, returnCfg]

/-- Returning at the origin emits nothing. -/
theorem outputSymbol_return_zero {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)) :
    machine.outputSymbol (returnCfg cfg 0) = none := by
  change (machine.tr stReturn _ _).outS = none
  rw [tr_return_zero cfg ho]

/-- From position {lit}`p`, the complete return takes exactly {lit}`p + 1` transitions. -/
theorem configs_return_done {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0)) (p : ℕ) :
    machine.configs (returnCfg cfg p) (p + 1) = returnedCfg cfg ∧
      machine.outputString (returnCfg cfg p) (p + 1) = [] := by
  obtain ⟨hc, hout⟩ := configs_return cfg ho p 0
  simp only [Nat.zero_add] at hc hout
  constructor
  · rw [configs_succ_eq_step', hc, step_return_zero cfg ho]
  · rw [outputString_succ, hout, hc, outputSymbol_return_zero cfg ho]
    rfl

/-- Every return configuration stays within the initial binary and mismatch head bounds. -/
theorem configs_return_head_bounds {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (ho : ∀ z, origin (cfg.workTapes 0 z) = decide (z = 0))
    (p width : ℕ) (hp : p ≤ width)
    (hm0 : 0 ≤ cfg.workTapePos 2) (hmw : cfg.workTapePos 2 ≤ width)
    (t : ℕ) (ht : t ≤ p + 1) (i : Fin 3) :
    0 ≤ (machine.configs (returnCfg cfg p) t).workTapePos i ∧
      (machine.configs (returnCfg cfg p) t).workTapePos i ≤ width := by
  by_cases htp : t ≤ p
  · have hc := (configs_return cfg ho t (p - t)).1
    rw [show p - t + t = p by omega] at hc
    rw [hc]
    fin_cases i <;> simp only [returnCfg] <;> omega
  · have he : t = p + 1 := by omega
    subst t
    rw [(configs_return_done cfg ho p).1]
    fin_cases i <;> simp only [returnedCfg, returnCfg] <;> omega

end Geb.BitTree.BinaryMachine
