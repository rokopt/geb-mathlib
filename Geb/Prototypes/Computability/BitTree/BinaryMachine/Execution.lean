/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Simulation
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Accounting
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.BitStep
import Mathlib.Tactic.IntervalCases

set_option doc.verso true

/-!
# Executions of the binary-counter recognizer

The execution at a prefix boundary is indexed by the accumulated cost of the
input and counter transitions. A fixed binary width bounds all prefixes of an input.

## Main statements

* {lit}`configs_account` realizes every prefix account within its accumulated cost.
* {lit}`headBound_start` bounds the initialization transitions.

## Tags

binary tree, Turing machine, execution, amortized complexity
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- Initialization emits no symbols. -/
theorem outputString_start (input : List (Fin 4)) :
    machine.outputString (machine.initCfg input) 2 = [] := rfl

/-- The initialization steps visit only cells zero and one. -/
theorem headBound_start (input : List (Fin 4)) (width : ℕ) (hw : 1 ≤ width) :
    ∀ t ≤ 2, HeadBound width (machine.configs (machine.initCfg input) t) := by
  intro t ht i
  interval_cases t <;> fin_cases i
  all_goals first
    | (change 0 ≤ (0 : ℤ) ∧ 0 ≤ (width : ℤ); exact ⟨le_refl _, Int.natCast_nonneg _⟩)
    | (change 0 ≤ (1 : ℤ) ∧ 1 ≤ (width : ℤ); exact ⟨by decide, by exact_mod_cast hw⟩)

/-- Every prefix boundary realizes the pure account and bounds the whole execution so far. -/
theorem configs_account (w : List Bool) :
    ∀ t, t ≤ w.length →
      let cost := 2 + runCost (w.take t)
      let now := machine.configs (machine.initCfg (w.map boolEmb)) cost
      let s := account (w.take t)
      Represents (w.length + 2).size now (modeState s.mode) s.forks s.leaves ∧
        now.inputPos.val = t + 1 ∧
        machine.outputString (machine.initCfg (w.map boolEmb)) cost = [] ∧
        ∀ u ≤ cost, HeadBound (w.length + 2).size
          (machine.configs (machine.initCfg (w.map boolEmb)) u) := by
  refine Nat.rec ?_ ?_
  · intro ht
    change Represents (w.length + 2).size
      (machine.configs (machine.initCfg (w.map boolEmb)) 2) stTree 1 0 ∧ _
    rw [configs_start]
    exact ⟨represents_startCfg _ _ (width_pos w.length), rfl,
      outputString_start _, headBound_start _ _ (width_pos w.length)⟩
  · intro t ih ht
    obtain ⟨hr, hp, ho, hh⟩ := ih (by omega)
    have hlt : t < w.length := by omega
    have hs := prefix_size_le w (t + 1)
    rw [account_take_succ w t hlt] at hs
    let cfg := machine.configs (machine.initCfg (w.map boolEmb)) (2 + runCost (w.take t))
    have hstep := configs_bit w t hlt cfg hp (account (w.take t)) (w.length + 2).size
      (account_valid _) hr hs.1 hs.2
    have hbound := configs_bit_head_bounds w t hlt cfg hp (account (w.take t))
      (w.length + 2).size (account_valid _) hr hs.1 hs.2
    obtain ⟨hr', hp', ho'⟩ := hstep
    have he : 2 + runCost (w.take (t + 1)) =
        (2 + runCost (w.take t)) + macroCost (account (w.take t)) w[t] := by
      rw [runCost_take_succ w t hlt]
      omega
    have hc : machine.configs (machine.initCfg (w.map boolEmb))
        (2 + runCost (w.take (t + 1))) =
        machine.configs cfg (macroCost (account (w.take t)) w[t]) := by
      rw [he, configs_add]
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hc, account_take_succ w t hlt]
      exact hr'
    · rw [hc]
      exact hp'
    · rw [he, outputString_add_eq_append, ho, ho']
      rfl
    · rw [he]
      exact headBound_add _ _ _ _ hh hbound

end Geb.BitTree.BinaryMachine
