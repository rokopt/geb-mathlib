/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Seek
public import Geb.Prototypes.Computability.BitTreeScanner.Steps.Bit

set_option doc.verso true

/-!
# The two-pass tree scanner's run

The machine's whole computation: the first pass to the scan's start, the scan
of each prefix to the closed form {name}`Geb.BitTreeScanner.cfgOf` at the
scan's state after it, and at the input's end the steps to the halt, whose
emitted symbol is {name}`Geb.BitTreeScanner.validBool` at the input. Every
configuration along the way keeps its heads within the bound.

## Main statements

* {lit}`Geb.BitTreeScanner.run_cfgOf` — the scan of each prefix.
* {lit}`Geb.BitTreeScanner.run_total` — from the initial configuration to
  the closed form at the whole input.
* {lit}`Geb.BitTreeScanner.cfgOf_end` — the steps from the input's end to the
  halt, emitting the decision function's value.
* {lit}`Geb.BitTreeScanner.halts_at`, {lit}`Geb.BitTreeScanner.outputString_eq`,
  {lit}`Geb.BitTreeScanner.headsLE_configs` — the machine halts after
  {name}`Geb.BitTreeScanner.totalTime` steps having emitted the decision function's
  value, its heads within the bound throughout.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`, as
{lit}`Geb.Prototypes.Computability.BitTreeScanner.Steps.Basic`'s
implementation notes explain.

## Tags

Turing machine, tree, prefix code, Elias gamma code, two passes
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

variable (w : List Bool)

/-- The scan of each prefix: from the scan's start, the closed form at the
scan's state after the prefix, in the prefix's time. -/
theorem run_cfgOf :
    ∀ k, ∀ h : k ≤ w.length,
      Run w (cfgAt w 0 (Nat.zero_le _) init []) (cfgOf w k h) (time (bound w) (w.take k)) :=
  Nat.rec (fun _ ↦ by
      rw [List.take_zero, cfgOf_eq, List.take_zero, scanAt_nil]
      exact run_zero _ (headsLE_cfgAt_init w))
    (fun k ih h ↦ by
      rw [time_take_succ (bound w) w k (by omega), cfgOf_eq, scanAt_take_succ _ w k (by omega),
        treeAt_take_succ _ w k (by omega)]
      refine run_seq _ _ _ _ _ (ih (by omega)) ?_
      rw [cfgOf_eq]
      exact run_cfgAt_step w k h _ _ (good_scanAt _ _) (goodTree_treeAt _ _)
        (length_treeAt_le w k (by omega)))

/-- From the initial configuration to the closed form at the whole input. -/
theorem run_total :
    Run w (bitTreeScanner.initCfg (w.map boolEmb)) (cfgOf w w.length le_rfl)
      (seekTime w.length + w.length + 3 + time (bound w) w) := by
  have := run_cfgOf w w.length le_rfl
  rw [List.take_length] at this
  exact run_seq _ _ _ _ _ (run_first w) this

/-- A halting step from a configuration with heads within the bound: the
machine halts, emits the step's symbol, and keeps its heads within the
bound. -/
theorem halt_step (cfg : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) (q : Fin stateCount)
    (b : Fin 4) (hq : cfg.state = some q)
    (htr : bitTreeScanner.tr q cfg.inputSymbol cfg.workTapeSymbols = halt b)
    (hh : HeadsLE w cfg) :
    (bitTreeScanner.configs cfg 1).state = none ∧ bitTreeScanner.outputString cfg 1 = [b] ∧
      ∀ j ≤ 1, HeadsLE w (bitTreeScanner.configs cfg j) := by
  obtain ⟨h1, h2, h3⟩ := step_halt cfg q hq b htr
  refine ⟨h1, ?_, ?_⟩
  · change bitTreeScanner.outputString _ (0 + 1) = [b]
    rw [outputString_succ, configs_zero, h3]
    rfl
  · intro j hj
    match j with
    | 0 => rw [configs_zero]; exact hh
    | 1 =>
      intro i
      change 0 ≤ (bitTreeScanner.step cfg).workTapePos i ∧
        (bitTreeScanner.step cfg).workTapePos i ≤ headBound w
      rw [h2]
      exact hh i

/-- At the input's end, from the closed form at the whole input: the machine
halts after {name}`Geb.BitTreeScanner.endCost` steps, the symbol it emits is the
decision function's value, and its heads stay within the bound. -/
theorem cfgOf_end :
    (bitTreeScanner.configs (cfgOf w w.length le_rfl) (endCost (scanFinal w))).state = none ∧
      bitTreeScanner.outputString (cfgOf w w.length le_rfl) (endCost (scanFinal w)) =
        [boolEmb (validBool w)] ∧
      ∀ j ≤ endCost (scanFinal w),
        HeadsLE w (bitTreeScanner.configs (cfgOf w w.length le_rfl) j) := by
  have hgood : Good (bound w) (scanFinal w) := good_scanAt (bound w) w
  have htree : GoodTree (scanFinal w) (treeAt (bound w) w) := goodTree_treeAt (bound w) w
  have hl := length_treeAt_le w w.length le_rfl
  rw [List.take_length] at hl
  rw [cfgOf_eq, List.take_length, show scanAt (bound w) w = scanFinal w from rfl, validBool]
  generalize hs : scanFinal w = s at *
  generalize hl' : treeAt (bound w) w = l at *
  obtain ⟨m, c, wd, d⟩ := s
  obtain ⟨hn, hv⟩ := htree
  have hin := inputSymbol_end w (cfgAt w w.length le_rfl ⟨m, c, wd, d⟩ l)
    (cfgAt_inputPos_val _ _ _ _ _)
  have hone : ∀ (q : Fin stateCount) (b : Fin 4),
      (cfgAt w w.length le_rfl ⟨m, c, wd, d⟩ l).state = some q →
      bitTreeScanner.tr q none (cfgAt w w.length le_rfl ⟨m, c, wd, d⟩ l).workTapeSymbols =
        halt b →
      (bitTreeScanner.configs (cfgAt w w.length le_rfl ⟨m, c, wd, d⟩ l) 1).state = none ∧
        bitTreeScanner.outputString (cfgAt w w.length le_rfl ⟨m, c, wd, d⟩ l) 1 = [b] ∧
        ∀ j ≤ 1, HeadsLE w (bitTreeScanner.configs (cfgAt w w.length le_rfl ⟨m, c, wd, d⟩ l) j) :=
    fun q b hq htr ↦ halt_step w _ q b hq (by rw [hin]; exact htr)
      (headsLE_cfgAt w w.length le_rfl _ hgood l)
  cases m with
  | term =>
    obtain ⟨rfl, rfl⟩ := hgood
    exact hone stMain 0 rfl (tr_main_end _)
  | zeros => exact hone stZeros 0 rfl (tr_zeros_end _)
  | bits =>
    dsimp only [Good] at hgood
    obtain ⟨hlt, _, _⟩ := hgood
    refine hone stBits 0 rfl ?_
    rw [workTapeSymbols_eq]
    have hsym : tapeLeaf ⟨.bits, c, wd, d⟩ (headLeaf ⟨.bits, c, wd, d⟩) = some 2 := by
      rw [tapeLeaf, headLeaf_bits]
      change (if ((wd - d.length : ℕ) : ℤ) = 0 then some 3
        else if 1 ≤ ((wd - d.length : ℕ) : ℤ) ∧
            ((wd - d.length : ℕ) : ℤ) ≤ ((wd - d.length : ℕ) : ℤ) then some 2
        else digitsAt ((wd - d.length : ℕ) : ℤ) d ((wd - d.length : ℕ) : ℤ)) = some 2
      rw [ite_eq_right (show ¬((wd - d.length : ℕ) : ℤ) = 0 by omega),
        ite_eq_left ⟨by omega, le_rfl⟩]
    change bitTreeScanner.tr stBits none
      ![tapeCount l 1, tapeLeaf ⟨.bits, c, wd, d⟩ (headLeaf ⟨.bits, c, wd, d⟩),
        tapeDigits w.length.bits (headRuler ⟨.bits, c, wd, d⟩)] = halt 0
    rw [hsym]
    exact tr_bits_mark_end _ _
  | count =>
    dsimp only [Good] at hgood
    obtain ⟨hd, hlen, hw⟩ := hgood
    rw [show endCost ⟨.count, c, wd, d⟩ = 2 * borrowLength d + 1 + 1 from rfl,
      cfgAt_count w w.length le_rfl l c wd d]
    obtain ⟨hc, ho, hh⟩ := run_decrement w w.length le_rfl l false d hd (by omega)
    refine ⟨?_, ?_, ?_⟩
    · rw [configs_add, hc]
      exact (halt_step w (returnCfg w w.length le_rfl l false d 0) stReturn 0 rfl
        (by
          rw [inputSymbol_end w _ rfl, workTapeSymbols_eq]
          exact tr_return_base_end _ _)
        (headsLE_returnCfg w w.length le_rfl l false d (by omega) 0 (Nat.zero_le _))).1
    · rw [outputString_add_eq_append, ho, hc]
      exact (halt_step w (returnCfg w w.length le_rfl l false d 0) stReturn 0 rfl
        (by
          rw [inputSymbol_end w _ rfl, workTapeSymbols_eq]
          exact tr_return_base_end _ _)
        (headsLE_returnCfg w w.length le_rfl l false d (by omega) 0 (Nat.zero_le _))).2.1
    · intro j hj
      by_cases hjm : j ≤ 2 * borrowLength d + 1
      · exact hh j hjm
      · rw [show j = 2 * borrowLength d + 1 + (j - (2 * borrowLength d + 1)) by omega, configs_add,
          hc]
        exact (halt_step w (returnCfg w w.length le_rfl l false d 0) stReturn 0 rfl
          (by
            rw [inputSymbol_end w _ rfl, workTapeSymbols_eq]
            exact tr_return_base_end _ _)
          (headsLE_returnCfg w w.length le_rfl l false d (by omega) 0 (Nat.zero_le _))).2.2
          _ (by omega)
  | done =>
    obtain ⟨rfl, rfl⟩ := hgood
    exact hone stDone 1 rfl (tr_done_end _)
  | dead =>
    obtain ⟨rfl, hw⟩ := hgood
    exact hone stDead 0 rfl (tr_dead_end _)

/-- The machine halts after {lit}`totalTime w` steps. -/
theorem halts_at :
    (bitTreeScanner.configs (bitTreeScanner.initCfg (w.map boolEmb)) (totalTime w)).state =
      none := by
  rw [totalTime, configs_add, (run_total w).1]
  exact (cfgOf_end w).1

/-- Over the same steps the machine emits one symbol, the decision function's
value at the input. -/
theorem outputString_eq :
    bitTreeScanner.outputString (bitTreeScanner.initCfg (w.map boolEmb)) (totalTime w) =
      [boolEmb (validBool w)] := by
  rw [totalTime, outputString_add_eq_append, (run_total w).2.1, (run_total w).1,
    (cfgOf_end w).2.1]
  rfl

/-- Throughout the computation the heads stay within the bound. -/
theorem headsLE_configs :
    ∀ j ≤ totalTime w,
      HeadsLE w (bitTreeScanner.configs (bitTreeScanner.initCfg (w.map boolEmb)) j) := by
  intro j hj
  rw [totalTime] at hj
  by_cases hjm : j ≤ seekTime w.length + w.length + 3 + time (bound w) w
  · exact (run_total w).2.2 j hjm
  · rw [show j = seekTime w.length + w.length + 3 + time (bound w) w +
        (j - (seekTime w.length + w.length + 3 + time (bound w) w)) by omega,
      configs_add, (run_total w).1]
    exact (cfgOf_end w).2.2 _ (by omega)

end Geb.BitTreeScanner
