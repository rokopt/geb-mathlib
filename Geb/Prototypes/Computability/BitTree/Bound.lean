/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Steps
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

set_option doc.verso true

/-!
# Time and space bounds for the single-pass bitstring-tree recognizer

The unary-counter machine takes one transition per input bit, two initialization
transitions and a final output transition. Its visited work cells lie between zero
and one plus the input length.

## Main statements

* {lit}`computableInTimeAndSpace_validBool` packages the recognizer in CSLib's
  finite-alphabet, finite-state machine complexity predicate.

## Implementation notes

The space bound counts visited work cells, including blank cells. It excludes
the read-only input tape, as specified by CSLib. The bound is for this unary
implementation and is not a lower bound on recognition space.

## Tags

binary tree, bitstring, time complexity, space complexity, Turing machine
-/

@[expose] public section

namespace Geb.BitTree

open Turing MultiTapeTM
open Geb.TreeScanner (boolEmb step_of_state)

/-- The final output transition leaves the work head in place. -/
theorem end_workTapePos (w : List Bool) (s : State) (i : Fin 1) :
    (unaryScanner.step (scanCfg w w.length (by omega) s)).workTapePos i = s.2 := by
  rw [step_of_state _ _ (modeState s.1) rfl, scanCfg_inputSymbol_end]
  rcases s with ⟨m, n⟩
  cases m <;> simp [unaryScanner, modeState, scanCfg]

/-- Every visited work-head position is between zero and the input length plus one. -/
theorem workTapePos_bounds (w : List Bool) (t : ℕ) (ht : t ≤ w.length + 3) (i : Fin 1) :
    0 ≤ (unaryScanner.configs (unaryScanner.initCfg (w.map boolEmb)) t).workTapePos i ∧
      (unaryScanner.configs (unaryScanner.initCfg (w.map boolEmb)) t).workTapePos i ≤
        (w.length + 1 : ℕ) := by
  rcases t with _ | t
  · simp
    omega
  rcases t with _ | t
  · rw [show unaryScanner.configs (unaryScanner.initCfg (w.map boolEmb)) 1 =
        plantCfg w by exact init_step w]
    simp [plantCfg]
  by_cases h : t ≤ w.length
  · rw [(configs_scan w t h).1]
    change 0 ≤ ((scan (w.take t)).2 : ℤ) ∧ _
    have hc := scan_counter_le (w.take t)
    simp only [List.length_take] at hc
    constructor
    · exact Int.natCast_nonneg _
    · simp only [scanCfg]
      omega
  · have he : t = w.length + 1 := by omega
    subst t
    rw [show w.length + 1 + 1 + 1 = (w.length + 2) + 1 by omega,
      configs_succ_eq_step', (configs_scan w w.length (by omega)).1, end_workTapePos]
    have hc := scan_counter_le w
    simp only [List.take_length]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast hc⟩

/-- The unary machine visits at most the input length plus two work cells. -/
theorem spaceUsed_le (w : List Bool) :
    unaryScanner.spaceUsed (unaryScanner.initCfg (w.map boolEmb)) (w.length + 3) ≤
      w.length + 2 := by
  have hsub (i : Fin 1) :
      unaryScanner.visitedByTapeHead (unaryScanner.initCfg (w.map boolEmb))
          (w.length + 3) i ⊆ (Finset.range (w.length + 2)).image (fun n : ℕ ↦ (n : ℤ)) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := unaryScanner.mem_visitedByTapeHead.mp hz
    obtain ⟨hlo, hhi⟩ := workTapePos_bounds w t (by omega) i
    apply Finset.mem_image.mpr
    refine ⟨_, Finset.mem_range.mpr ?_, Int.toNat_of_nonneg hlo⟩
    omega
  change ∑ i : Fin 1, _ ≤ _
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact (Finset.card_le_card (hsub 0)).trans
    (Finset.card_image_le.trans (by simp))

/-- The unified recognizer runs in input length plus three steps and input length plus two cells. -/
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace (fun w : List Bool ↦ [validBool w])
      (fun n ↦ n + 3) (fun n ↦ n + 2) := by
  refine ⟨1, 2, 7, boolEmb, unaryScanner, fun w ↦ ?_⟩
  exact ⟨w.length + 3, le_refl _,
    unaryScanner.spaceUsed (unaryScanner.initCfg (w.map boolEmb)) (w.length + 3),
    spaceUsed_le w, halts_at w, outputString_eq w, rfl⟩

end Geb.BitTree
