/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineRead
public import Geb.Prototypes.Computability.BitTree.Elias.MachineCounter
public import Geb.Prototypes.Computability.BitTree.Elias.MachineNormalize

set_option doc.verso true

/-!
# The empty-payload transition

The shortest delta header encodes length zero. Reading its terminating one initializes the
width counter; two binary countdowns then reach zero and erase both fields before completing
the leaf. The entire transition takes sixteen machine steps.

## Main statements

* {lit}`configs_empty_leaf` proves the exact result and cost of the empty-leaf transition.
* {lit}`configs_empty_leaf_headBound` bounds every intermediate work-tape head.

## Tags

Elias delta code, Turing machine, empty leaf, simulation
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Decrementing the one-bit width field reaches the payload countdown with a zero width. -/
theorem configs_empty_width (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending : ℕ) :
    machine.configs (scanCfg input pos (stDecrement false) pending 0 [true] [true]) 5 =
      scanCfg input pos (stDecrement true) pending 0 [false] [true] ∧
    machine.outputString (scanCfg input pos (stDecrement false) pending 0 [true] [true]) 5 =
      [] := by
  have h := configs_decrement
    (scanCfg input pos (stDecrement false) pending 0 [true] [true]) false [true]
    (by decide)
  change machine.configs (counterCfg _ false [true] (stDecrement false) 2) 5 =
    counterCfg _ false [false] (stDecrement true) 2 ∧ _ at h
  have hstart := counterCfg_scanCfg_false input pos (stDecrement false) (stDecrement false)
    pending 0 [true] [true] [true]
  have hend := counterCfg_scanCfg_false input pos (stDecrement false) (stDecrement true)
    pending 0 [true] [true] [false]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hstart hend
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at h
  rw [hstart, hend] at h
  exact h

/-- Decrementing the one-bit payload field reaches cleanup with both fields zero. -/
theorem configs_empty_payload (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending : ℕ) :
    machine.configs (scanCfg input pos (stDecrement true) pending 0 [false] [true]) 5 =
      scanCfg input pos stClear pending 0 [false] [false] ∧
    machine.outputString (scanCfg input pos (stDecrement true) pending 0 [false] [true]) 5 =
      [] := by
  have h := configs_decrement
    (scanCfg input pos (stDecrement true) pending 0 [false] [true]) true [true]
    (by decide)
  change machine.configs (counterCfg _ true [true] (stDecrement true) 2) 5 =
    counterCfg _ true [false] stClear 2 ∧ _ at h
  have hstart := counterCfg_scanCfg_true input pos (stDecrement true) (stDecrement true)
    pending 0 [false] [true] [true]
  have hend := counterCfg_scanCfg_true input pos (stDecrement true) stClear
    pending 0 [false] [true] [false]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hstart hend
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul] at h
  rw [hstart, hend] at h
  exact h

/-- Erasing the two zero fields completes an empty leaf in four transitions. -/
theorem configs_empty_clear (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending : ℕ) (hp : 0 < pending) :
    machine.configs (scanCfg input pos stClear pending 0 [false] [false]) 4 =
      modelCfg input pos (Scanner.finish pending) [] [] ∧
    machine.outputString (scanCfg input pos stClear pending 0 [false] [false]) 4 = [] := by
  have h := configs_clear_ready (scanCfg input pos stClear pending 0 [false] [false])
    [false] [false] 2 2
  have hn := clearingCfg_scanCfg input pos stClear pending 0 [false] [false]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hn
  rw [hn, completedCfg_scanCfg input pos stClear pending [false] [false] hp] at h
  exact h

/-- Reading the shortest delta header finishes its empty leaf in sixteen silent steps. -/
theorem configs_empty_leaf (input : List (Fin 3)) (pos : Fin (input.length + 2))
    (pending : ℕ) (hp : 0 < pending)
    (hin : (scanCfg input pos stZeros pending 0 [] [true]).inputSymbol =
      some (boolEmb true)) :
    machine.configs (scanCfg input pos stZeros pending 0 [] [true]) 16 =
      modelCfg input (moveInputPos pos 1) (Scanner.finish pending) [] [] ∧
    machine.outputString (scanCfg input pos stZeros pending 0 [] [true]) 16 = [] := by
  have hs := step_zeros input pos pending 0 [] [true] true hin
  simp only [↓reduceIte] at hs
  have hread := configs_output_one _ _ hs
    (outputSymbol_read _ stZeros true rfl hin (Or.inr (Or.inl rfl)))
  have hc := step_sizeCheck input (moveInputPos pos 1) pending 0 [true] [true]
  simp only [ite_true] at hc
  have hcheck := configs_output_one _ _ hc
    (outputSymbol_sizeCheck input (moveInputPos pos 1) pending 0 [true] [true])
  have h2 := configs_output_add _ _ _ 1 1 hread hcheck
  have h7 := configs_output_add _ _ _ 2 5 h2
    (configs_empty_width input (moveInputPos pos 1) pending)
  have h12 := configs_output_add _ _ _ 7 5 h7
    (configs_empty_payload input (moveInputPos pos 1) pending)
  exact configs_output_add _ _ _ 12 4 h12
    (configs_empty_clear input (moveInputPos pos 1) pending hp)

/-- Every prefix of the empty-leaf transition stays within the initial pending count and two
binary-field cells. -/
theorem configs_empty_leaf_headBound (input : List (Fin 3))
    (pos : Fin (input.length + 2)) (pending width : ℕ) (hp : 0 < pending)
    (hpw : pending ≤ width) (hw : 2 ≤ width)
    (hin : (scanCfg input pos stZeros pending 0 [] [true]).inputSymbol =
      some (boolEmb true)) (t : ℕ) (ht : t ≤ 16) :
    HeadBound width (machine.configs (scanCfg input pos stZeros pending 0 [] [true]) t) := by
  have hb : ∀ q bs cs, bs.length ≤ 1 → cs.length ≤ 1 →
      HeadBound width (scanCfg input (moveInputPos pos 1) q pending 0 bs cs) := by
    intro q bs cs hbs hcs
    exact scanCfg_headBound _ _ _ _ _ _ _ _ hpw (by omega) (by omega) (by omega)
  have hwdec : ∀ r ≤ 5, HeadBound width (machine.configs
      (scanCfg input (moveInputPos pos 1) (stDecrement false) pending 0 [true] [true]) r) := by
    intro r hr
    have h := configs_decrement_headBound
      (scanCfg input (moveInputPos pos 1) (stDecrement false) pending 0 [true] [true])
      false [true] width (hb _ _ _ (by decide) (by decide)) (by simpa using hw)
      (by decide) r hr
    rw [counterCfg_scanCfg_false input (moveInputPos pos 1) _ _ pending 0
      [true] [true] [true]] at h
    exact h
  have hpdec : ∀ r ≤ 5, HeadBound width (machine.configs
      (scanCfg input (moveInputPos pos 1) (stDecrement true) pending 0 [false] [true]) r) := by
    intro r hr
    have h := configs_decrement_headBound
      (scanCfg input (moveInputPos pos 1) (stDecrement true) pending 0 [false] [true])
      true [true] width (hb _ _ _ (by decide) (by decide)) (by simpa using hw)
      (by decide) r hr
    rw [counterCfg_scanCfg_true input (moveInputPos pos 1) _ _ pending 0
      [false] [true] [true]] at h
    exact h
  have hclear : ∀ r ≤ 4, HeadBound width (machine.configs
      (scanCfg input (moveInputPos pos 1) stClear pending 0 [false] [false]) r) := by
    intro r hr
    have h := configs_clear_headBound
      (scanCfg input (moveInputPos pos 1) stClear pending 0 [false] [false])
      [false] [false] 2 2 width (hb _ _ _ (by decide) (by decide)) hw hw
      (by change (1 : ℤ) ≤ pending; omega) r hr
    have hn := clearingCfg_scanCfg input (moveInputPos pos 1) stClear pending 0 [false] [false]
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at hn
    rw [hn] at h
    exact h
  have htail : ∀ r ≤ 14, HeadBound width (machine.configs
      (scanCfg input (moveInputPos pos 1) (stDecrement false) pending 0 [true] [true]) r) := by
    apply headBound_add _ 5 9 width hwdec
    rw [(configs_empty_width input (moveInputPos pos 1) pending).1]
    apply headBound_add _ 5 4 width hpdec
    rw [(configs_empty_payload input (moveInputPos pos 1) pending).1]
    exact hclear
  have hs := step_zeros input pos pending 0 [] [true] true hin
  simp only [↓reduceIte] at hs
  have hc := step_sizeCheck input (moveInputPos pos 1) pending 0 [true] [true]
  simp only [ite_true] at hc
  apply headBound_succ _ 15 width
    (scanCfg_headBound _ _ _ _ _ _ _ _ hpw (by omega) (by simp; omega) (by simpa using hw)) ?_ t ht
  rw [hs]
  intro r hr
  apply headBound_succ _ 14 width (hb _ _ _ (by decide) (by decide)) ?_ r hr
  rw [hc]
  exact htail

end Geb.BitTree.Elias.Machine
