/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Accounting
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Simulation
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Macro

set_option doc.verso true

/-!
# One input bit of the binary-counter recognizer

An input transition is followed by a counter increment exactly at a fork tag or a
leaf terminator. The combined segment realizes one accounting update.

## Main statements

* {lit}`configs_bit` implements one bit without emitting output.
* {lit}`configs_bit_head_bounds` bounds the heads throughout that segment.

## Tags

Turing machine, simulation, binary counter
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- The complete segment for one bit preserves the representation and bounds its heads. -/
theorem configs_bit_aux {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (s : Account) (b : Bool) (width : ℕ)
    (hv : AccountValid s) (h : Represents width cfg (modeState s.mode) s.forks s.leaves)
    (hi : cfg.inputSymbol = some (boolEmb b))
    (ha : (accountStep s b).forks.size ≤ width)
    (hb : (accountStep s b).leaves.size ≤ width) :
    let cost := macroCost s b
    let next := accountStep s b
    Represents width (machine.configs cfg cost) (modeState next.mode) next.forks next.leaves ∧
      (machine.configs cfg cost).inputPos = moveInputPos cfg.inputPos 1 ∧
      machine.outputString cfg cost = [] ∧
      ∀ u ≤ cost, HeadBound width (machine.configs cfg u) := by
  let after := consumeCfg cfg (postReadState s.mode b)
  have hc : machine.configs cfg 1 = after := by
    rw [show 1 = 0 + 1 from rfl, configs_succ_eq_step', configs_zero,
      step_read cfg s.mode b h.state hi]
  have hr : Represents width after (postReadState s.mode b) s.forks s.leaves :=
    h.consume _
  have ho : machine.outputString cfg 1 = [] := by
    rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero,
      outputSymbol_read cfg s.mode b h.state hi]
    rfl
  have hh : ∀ u ≤ 1, HeadBound width (machine.configs cfg u) := by
    intro u hu
    have hu' : u = 0 ∨ u = 1 := by omega
    rcases hu' with rfl | rfl
    · exact h.headBound
    · rw [hc]
      exact hr.headBound
  rcases s with ⟨m, a, c⟩
  cases m <;> cases b
  case tree.true =>
    have hnext : (a + 1).size ≤ width := by simpa [accountStep] using ha
    obtain ⟨hr', hp', ho'⟩ := configs_increment after false width a c hr hnext
    simp only [Bool.false_eq_true, ↓reduceIte] at hr' hp' ho'
    have hne : a + 1 ≠ c := by
      change c ≤ a ∧ 0 < a ∧ c < a at hv
      omega
    have hc' : machine.configs cfg (macroCost ⟨.tree, a, c⟩ true) =
        machine.configs after (2 * Counter.flips a.bits + 1) := by
      change machine.configs cfg (1 + (2 * Counter.flips a.bits + 1)) = _
      rw [configs_add, hc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hc']
      simpa [accountStep, accountProject, Geb.BitTree.step, modeState, hne] using hr'
    · rw [hc', hp']
      rfl
    · change machine.outputString cfg (1 + (2 * Counter.flips a.bits + 1)) = []
      rw [outputString_add_eq_append, ho, hc, ho']
      rfl
    · apply headBound_add cfg width 1 (2 * Counter.flips a.bits + 1) hh
      intro u hu
      rw [hc]
      exact fun i ↦ configs_increment_head_bounds after false width a c hr hnext u hu i
  case string.false =>
    have hnext : (c + 1).size ≤ width := by simpa [accountStep] using hb
    obtain ⟨hr', hp', ho'⟩ := configs_increment after true width a c hr hnext
    simp only [↓reduceIte] at hr' hp' ho'
    have hmode : modeState (accountStep ⟨.string, a, c⟩ false).mode =
        if a = c + 1 then stDone else stTree := by
      change c ≤ a ∧ 0 < a ∧ c < a at hv
      dsimp [accountStep, accountProject, Geb.BitTree.step, Geb.BitTree.finish]
      by_cases he : a = c + 1
      · have he' : a - c = 1 := by omega
        rw [ite_eq_left he', ite_eq_left he]
        rfl
      · have he' : a - c ≠ 1 := by omega
        rw [ite_eq_right he', ite_eq_right he]
        rfl
    have hc' : machine.configs cfg (macroCost ⟨.string, a, c⟩ false) =
        machine.configs after (2 * Counter.flips c.bits + 1) := by
      change machine.configs cfg (1 + (2 * Counter.flips c.bits + 1)) = _
      rw [configs_add, hc]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hc', hmode]
      exact hr'
    · rw [hc', hp']
      rfl
    · change machine.outputString cfg (1 + (2 * Counter.flips c.bits + 1)) = []
      rw [outputString_add_eq_append, ho, hc, ho']
      rfl
    · apply headBound_add cfg width 1 (2 * Counter.flips c.bits + 1) hh
      intro u hu
      rw [hc]
      exact fun i ↦ configs_increment_head_bounds after true width a c hr hnext u hu i
  all_goals
    change Represents width (machine.configs cfg 1) _ a c ∧
      (machine.configs cfg 1).inputPos = moveInputPos cfg.inputPos 1 ∧
      machine.outputString cfg 1 = [] ∧ ∀ u ≤ 1, HeadBound width (machine.configs cfg u)
    refine ⟨?_, ?_, ho, hh⟩
    · rw [hc]
      exact hr
    · rw [hc]
      rfl

/-- One input bit realizes the accounting update in its prescribed macro cost. -/
theorem configs_bit (w : List Bool) (t : ℕ) (ht : t < w.length)
    (cfg : Cfg 3 (Fin 4) (Fin 10) (w.map boolEmb)) (hp : cfg.inputPos.val = t + 1)
    (s : Account) (width : ℕ) (hv : AccountValid s)
    (h : Represents width cfg (modeState s.mode) s.forks s.leaves)
    (ha : (accountStep s w[t]).forks.size ≤ width)
    (hb : (accountStep s w[t]).leaves.size ≤ width) :
    let cost := macroCost s w[t]
    let next := accountStep s w[t]
    Represents width (machine.configs cfg cost) (modeState next.mode) next.forks next.leaves ∧
      (machine.configs cfg cost).inputPos.val = t + 2 ∧ machine.outputString cfg cost = [] := by
  obtain ⟨hr, hp', ho, _⟩ := configs_bit_aux cfg s w[t] width hv h
    (inputSymbol_at w t ht cfg hp) ha hb
  refine ⟨hr, ?_, ho⟩
  rw [hp']
  have hm := consumeCfg_inputPos cfg (postReadState s.mode w[t]) (by
    rw [hp, List.length_map]
    omega)
  change (moveInputPos cfg.inputPos 1).val = _ at hm
  omega

/-- Every head remains within the chosen binary width during a complete input-bit segment. -/
theorem configs_bit_head_bounds (w : List Bool) (t : ℕ) (ht : t < w.length)
    (cfg : Cfg 3 (Fin 4) (Fin 10) (w.map boolEmb)) (hp : cfg.inputPos.val = t + 1)
    (s : Account) (width : ℕ) (hv : AccountValid s)
    (h : Represents width cfg (modeState s.mode) s.forks s.leaves)
    (ha : (accountStep s w[t]).forks.size ≤ width)
    (hb : (accountStep s w[t]).leaves.size ≤ width) :
    ∀ u ≤ macroCost s w[t], HeadBound width (machine.configs cfg u) :=
  (configs_bit_aux cfg s w[t] width hv h (inputSymbol_at w t ht cfg hp) ha hb).2.2.2

end Geb.BitTree.BinaryMachine
