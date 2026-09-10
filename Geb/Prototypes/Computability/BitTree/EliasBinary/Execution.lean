/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.BitStep
public import Geb.Prototypes.Computability.BitTree.EliasBinary.PassOne

set_option doc.verso true

/-!
# Executions of the binary-counter recognizer

After the first pass and the rewind, every boundary of the second pass is indexed by the
accumulated macro cost of the prefix consumed. The width fixed by the input length bounds
every head throughout.

## Main definitions

* {lit}`prefixCost` is the time to reach the boundary after a prefix.

## Main statements

* {lit}`configs_account` realizes every prefix account within its cost.

## Tags

Turing machine, execution, amortized complexity, Elias delta code
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb)

/-- The time to reach the boundary after a prefix of the second pass. -/
def prefixCost (n : ℕ) (w : List Bool) : ℕ :=
  1 + passOneCost n + (n + 2) + runCost n w

/-- Every prefix boundary realizes the account and bounds the whole execution so far. -/
theorem configs_account (w : List Bool) : ∀ t, t ≤ w.length →
    let cost := prefixCost w.length (w.take t)
    let start := machine.initCfg (w.map boolEmb)
    Represents (widthOf w.length) (machine.configs start cost) (account w.length (w.take t)) ∧
      (machine.configs start cost).inputPos.val = t + 1 ∧
      machine.outputString start cost = [] ∧
      ∀ u ≤ cost, HeadBound (widthOf w.length) (machine.configs start u) := by
  refine Nat.rec ?_ ?_
  · intro _
    have h := configs_passOne w
    simpa only [prefixCost, List.take_zero, runCost, List.foldl_nil, Nat.add_zero, account]
      using h
  · intro t ih ht
    obtain ⟨hr, hp, ho, hh⟩ := ih (by omega)
    have hlt : t < w.length := by omega
    obtain ⟨hw1, hw2, hw3⟩ := forks_size_lt_width w.length (w.take t) _ rfl
      (by simp only [List.length_take]; omega)
    have hstep := configs_bit w t hlt _ hp (account w.length (w.take t)) (account_valid _ _)
      hr hw1 hw2 hw3
    obtain ⟨hr', hp', ho', hb'⟩ := hstep
    have he : prefixCost w.length (w.take (t + 1)) =
        prefixCost w.length (w.take t) + macroCost (account w.length (w.take t)) w[t] := by
      unfold prefixCost
      rw [runCost_take_succ w.length w t hlt]
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [he, configs_add, account_take_succ w.length w t hlt]
      exact hr'
    · rw [he, configs_add]
      exact hp'
    · rw [he]
      exact outputString_add_nil _ _ _ ho ho'
    · rw [he]
      exact headBound_add _ _ _ _ hh hb'

end Geb.BitTree.EliasBinary
