/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineBit
public import Geb.Prototypes.Computability.BitTree.Elias.MachineAccounting
public import Geb.Prototypes.Computability.BitTree.Elias.MachineEnd

set_option doc.verso true

/-!
# Whole-input execution of the Elias recognizer

Each complete input transition realizes one step of the pure scanner account.
Composing those transitions bounds all intermediate head positions, including
the counter sweeps between successive input bits.

## Main statements

* {lit}`configs_account` realizes every input prefix and bounds its visited space.

## Tags

Elias delta code, Turing machine, execution, complexity
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Every prefix realizes its account at the exact accumulated transition cost. -/
theorem configs_account (w : List Bool) :
    ∀ t, (ht : t ≤ w.length) →
      let cost := 1 + runCost (w.take t)
      let a := account (w.take t)
      machine.configs (machine.initCfg (w.map boolEmb)) cost =
          modelCfg (w.map boolEmb) ⟨t + 1, by simp only [List.length_map]; omega⟩
            a.1 a.2.1 a.2.2 ∧
        machine.outputString (machine.initCfg (w.map boolEmb)) cost = [] ∧
        ∀ u ≤ cost, HeadBound (w.length + 1)
          (machine.configs (machine.initCfg (w.map boolEmb)) u) := by
  refine Nat.rec ?_ ?_
  · intro ht
    change machine.configs (machine.initCfg (w.map boolEmb)) 1 = _ ∧ _
    refine ⟨?_, outputString_start _, headBound_start _ _ (by omega)⟩
    rw [configs_start]
    congr 1
  · intro t ih ht
    have hlt : t < w.length := by omega
    obtain ⟨hc, ho, hh⟩ := ih (by omega)
    let a := account (w.take t)
    let pos : Fin ((w.map boolEmb).length + 2) :=
      ⟨t + 1, by simp only [List.length_map]; omega⟩
    have hin := inputSymbol_at w t hlt
      (modelCfg (w.map boolEmb) pos a.1 a.2.1 a.2.2) rfl
    obtain ⟨hs, hout⟩ := configs_bit (w.map boolEmb) pos a.1 a.2.1 a.2.2 w[t]
      (account_active _) (account_words _) hin
    have hp := account_pending_le (w.take t)
    have hz := account_zeros_le (w.take t)
    obtain ⟨hb, hd⟩ := account_lengths_le (w.take t)
    have hlen : (w.take t).length = t := List.length_take_of_le (by omega)
    have hbound := configs_bit_headBound (w.map boolEmb) pos a.1 a.2.1 a.2.2 w[t]
      (account_active _) (account_words _) hin (w.length + 1)
      (by dsimp only [a]; omega) (by dsimp only [a]; omega)
      (by dsimp only [a]; omega) (by dsimp only [a]; omega)
    have he : 1 + runCost (w.take (t + 1)) =
        (1 + runCost (w.take t)) + macroCost a w[t] := by
      dsimp only [a]
      rw [runCost_take_succ w t hlt]
      omega
    have hpos : moveInputPos pos 1 =
        (⟨t + 1 + 1, by simp only [List.length_map]; omega⟩ :
          Fin ((w.map boolEmb).length + 2)) := by
      exact moveInputPos_pos_of_ne_right pos (by
        dsimp only [pos]; simp only [List.length_map]; omega)
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · rw [he, configs_add, hc]
      change machine.configs (modelCfg (w.map boolEmb) pos a.1 a.2.1 a.2.2)
        (bitCost a.1.1 a.2.1 a.2.2 w[t]) = _
      rw [hs, hpos, account_take_succ w t hlt]
      rfl
    · rw [he, outputString_add_eq_append, ho, hc]
      change [] ++ machine.outputString (modelCfg (w.map boolEmb) pos a.1 a.2.1 a.2.2)
        (bitCost a.1.1 a.2.1 a.2.2 w[t]) = []
      rw [hout]
      rfl
    · rw [he]
      apply headBound_add _ _ _ _ hh
      rw [hc]
      exact hbound

end Geb.BitTree.Elias.Machine
