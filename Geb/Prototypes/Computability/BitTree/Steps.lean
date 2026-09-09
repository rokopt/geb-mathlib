/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Machine
public import Geb.Prototypes.Computability.TreeScanner.Steps

set_option doc.verso true

/-!
# Simulation of the bitstring-tree scanner

Each input bit takes one machine transition after initialization.
The simulation relates machine configurations to prefixes of the pure scan.

## Main statements

* {lit}`configs_scan` identifies every scanning configuration and its empty output.
* {lit}`halts_at` and {lit}`outputString_eq` give termination and the decision bit.

## Implementation notes

The correspondence uses CSLib's input-symbol and execution APIs, which depend
on classical choice. The scanner's data and transition function are constructive.

## Tags

Turing machine, simulation, binary tree, recognizer
-/

@[expose] public section

namespace Geb.BitTree

open Turing MultiTapeTM
open Geb.TreeScanner (boolEmb step_of_state)

/-- The first initialization step positions the counter head at one. -/
theorem init_step (w : List Bool) :
    unaryScanner.step (unaryScanner.initCfg (w.map boolEmb)) = plantCfg w := by
  rw [step_of_state _ _ 0 rfl]
  rfl

/-- The second initialization step installs the completion marker. -/
theorem plant_step (w : List Bool) :
    unaryScanner.step (plantCfg w) = scanCfg w 0 (by omega) (.tree, 1) := by
  rw [step_of_state _ _ 1 rfl]
  apply Cfg.ext
  · rfl
  · rfl
  · funext i z
    simp [unaryScanner, plantCfg, scanCfg, Function.update_apply]
  · rfl

/-- The scanned prefix determines the next input symbol. -/
theorem scanCfg_inputSymbol (w : List Bool) (t : ℕ) (h : t < w.length) (s : State) :
    (scanCfg w t (by omega) s).inputSymbol = some (boolEmb w[t]) := by
  rw [inputSymbolInner t (by simp [scanCfg, Nat.add_comm])
    (by simpa only [List.length_map] using h), List.getElem_map]

/-- A complete scan reads the right end marker. -/
theorem scanCfg_inputSymbol_end (w : List Bool) (s : State) :
    (scanCfg w w.length (by omega) s).inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs <;> simp_all [scanCfg]

/-- A scanning transition consumes one bit and updates exactly the pure state. -/
theorem scanCfg_step (w : List Bool) (t : ℕ) (h : t < w.length) (s : State)
    (hs : s.1 = .string → 0 < s.2) :
    unaryScanner.step (scanCfg w t (by omega) s) =
      scanCfg w (t + 1) h (step s w[t]) := by
  have hw : (scanCfg w t (by omega) s).workTapeSymbols =
      fun _ ↦ if s.2 = 1 then some 0 else none := by
    funext i
    simp [Cfg.workTapeSymbols, scanCfg]
  rw [step_of_state _ _ (modeState s.1) rfl, scanCfg_inputSymbol w t h,
    hw, tr_scan]
  apply Cfg.ext
  · rfl
  · change moveInputPos _ SignType.pos = _
    rw [moveInputPos_pos_of_ne_right (scanCfg w t (by omega) s).inputPos
      (by simp [scanCfg]; omega)]
    rfl
  · rfl
  · funext i
    exact counterMove_add s.1 s.2 w[t] hs

/-- Scanning a bit emits no output. -/
theorem outputSymbol_scanCfg (w : List Bool) (t : ℕ) (h : t < w.length) (s : State) :
    unaryScanner.outputSymbol (scanCfg w t (by omega) s) = none := by
  unfold outputSymbol
  change (unaryScanner.tr (modeState s.1) _ _).outS = none
  rw [scanCfg_inputSymbol w t h]
  rcases s with ⟨m, n⟩
  cases m <;> simp [unaryScanner, modeState, consume] <;> split_ifs <;> rfl

/-- At the right end marker the machine halts. -/
theorem scanCfg_halts (w : List Bool) (s : State) :
    (unaryScanner.step (scanCfg w w.length (by omega) s)).state = none := by
  rw [step_of_state _ _ (modeState s.1) rfl, scanCfg_inputSymbol_end]
  rcases s with ⟨m, n⟩
  cases m <;> rfl

/-- The right end marker emits the decision of the pure scanner state. -/
theorem outputSymbol_scanCfg_end (w : List Bool) (s : State) :
    unaryScanner.outputSymbol (scanCfg w w.length (by omega) s) =
      some (boolEmb (decide (s.1 = .done))) := by
  unfold outputSymbol
  change (unaryScanner.tr (modeState s.1) _ _).outS = _
  rw [scanCfg_inputSymbol_end]
  rcases s with ⟨m, n⟩
  cases m <;> rfl

/-- Initialization takes two steps and emits nothing. -/
theorem init_run (w : List Bool) :
    unaryScanner.configs (unaryScanner.initCfg (w.map boolEmb)) 2 =
        scanCfg w 0 (by omega) (.tree, 1) ∧
      unaryScanner.outputString (unaryScanner.initCfg (w.map boolEmb)) 2 = [] := by
  constructor
  · change unaryScanner.configs (unaryScanner.initCfg (w.map boolEmb)) (0 + 1 + 1) = _
    rw [configs_succ_eq_step', configs_succ_eq_step',
      configs_zero, init_step, plant_step]
  · rfl

/-- At every prefix boundary the machine realizes the pure scanner without output. -/
theorem configs_scan (w : List Bool) :
    ∀ t, ∀ h : t ≤ w.length,
      unaryScanner.configs (unaryScanner.initCfg (w.map boolEmb)) (t + 2) =
          scanCfg w t h (scan (w.take t)) ∧
        unaryScanner.outputString (unaryScanner.initCfg (w.map boolEmb)) (t + 2) = [] := by
  refine Nat.rec ?_ ?_
  · intro h
    exact init_run w
  · intro t ih h
    obtain ⟨hc, ho⟩ := ih (by omega)
    have ht : t < w.length := by omega
    rw [show t + 1 + 2 = (t + 2) + 1 by omega]
    constructor
    · rw [configs_succ_eq_step', hc, scanCfg_step w t ht _
        (fun hs ↦ scan_active_pos _ (Or.inr (Or.inl hs))), ← scan_take_succ w t ht]
    · rw [outputString_succ, ho, hc, outputSymbol_scanCfg w t ht]
      rfl

/-- The recognizer halts after one transition per bit and three fixed transitions. -/
theorem halts_at (w : List Bool) :
    (unaryScanner.configs (unaryScanner.initCfg (w.map boolEmb))
      (w.length + 3)).state = none := by
  rw [show w.length + 3 = (w.length + 2) + 1 by omega, configs_succ_eq_step',
    (configs_scan w w.length (by omega)).1]
  exact scanCfg_halts w _

/-- The sole output is the scanner's decision bit. -/
theorem outputString_eq (w : List Bool) :
    unaryScanner.outputString (unaryScanner.initCfg (w.map boolEmb)) (w.length + 3) =
      [boolEmb (validBool w)] := by
  rw [show w.length + 3 = (w.length + 2) + 1 by omega, outputString_succ,
    (configs_scan w w.length (by omega)).1, (configs_scan w w.length (by omega)).2,
    outputSymbol_scanCfg_end]
  simp [validBool]

end Geb.BitTree
