/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.Execution
public import Geb.Prototypes.Computability.BitTree.Elias.ScannerCorrect
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

set_option doc.verso true

/-!
# Resource bounds for the Elias-length recognizer

Work space counts all visited cells, including blank cells and marked origins.
The input tape is read-only and excluded from CSLib's work-space measure.

## Main statements

* {lit}`computableInTimeAndSpace_validBool` proves simultaneous quadratic time and linear space.
* {lit}`spaceUsed_le_of_headBound` converts the four head intervals to a work-space bound.

## Implementation notes

The machine consumes each input bit once. Binary countdowns sweep their entire
fixed-width words, including leading zeros, between input reads. Length fields
are kept in binary, so malformed inputs advertising enormous payloads still
halt within the same polynomial bound.

## Tags

Elias delta code, Turing machine, running time, work space
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- Four heads confined to the same interval visit at most four times its number of cells. -/
theorem spaceUsed_le_of_headBound {input : List (Fin 3)}
    (cfg : Cfg 4 (Fin 3) Control input) (width t : ℕ)
    (h : ∀ u ≤ t, HeadBound width (machine.configs cfg u)) :
    machine.spaceUsed cfg t ≤ 4 * (width + 1) := by
  have hsub (i : Fin 4) : machine.visitedByTapeHead cfg t i ⊆
      (Finset.range (width + 1)).image (fun n : ℕ ↦ (n : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := machine.mem_visitedByTapeHead.mp hz
    obtain ⟨hlo, hhi⟩ := h u (by omega) i
    apply Finset.mem_image.mpr
    refine ⟨_, Finset.mem_range.mpr ?_, Int.toNat_of_nonneg hlo⟩
    omega
  have hi (i : Fin 4) : machine.spaceUsedByTape cfg t i ≤ width + 1 :=
    (Finset.card_le_card (hsub i)).trans (Finset.card_image_le.trans (by simp))
  calc
    machine.spaceUsed cfg t ≤ ∑ _i : Fin 4, (width + 1) :=
      Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = 4 * (width + 1) := by simp

/-- After all input bits, one final transition halts. -/
theorem halts_at (w : List Bool) :
    (machine.configs (machine.initCfg (w.map boolEmb)) (1 + runCost w + 1)).state = none := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hc, _, _⟩ := h
  rw [configs_succ_eq_step', hc]
  rw [step_end _ (account w).1.1 rfl (inputSymbol_end _ (by
    simp only [modelCfg, scanCfg, List.length_map]))]

/-- The only output is the decision of the Elias tree decoder. -/
theorem outputString_eq (w : List Bool) :
    machine.outputString (machine.initCfg (w.map boolEmb)) (1 + runCost w + 1) =
      [boolEmb (Elias.validBool w)] := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hc, ho, _⟩ := h
  rw [outputString_succ, ho, hc,
    outputSymbol_end _ (account w).1.1 rfl (inputSymbol_end _ (by
      simp only [modelCfg, scanCfg, List.length_map])), account_project]
  change [boolEmb (Scanner.validBool w)] = _
  rw [Scanner.validBool_eq]

/-- The final halting transition preserves the work-head interval. -/
theorem headBound_run (w : List Bool) :
    ∀ u ≤ 1 + runCost w + 1, HeadBound (w.length + 1)
      (machine.configs (machine.initCfg (w.map boolEmb)) u) := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hc, _, hh⟩ := h
  intro u hu
  by_cases he : u ≤ 1 + runCost w
  · exact hh u he
  · have hu' : u = 1 + runCost w + 1 := by omega
    subst u
    have hlast := hh (1 + runCost w) (Nat.le_refl _)
    rw [hc] at hlast
    rw [configs_succ_eq_step', hc,
      step_end _ (account w).1.1 rfl (inputSymbol_end _ (by
        simp only [modelCfg, scanCfg, List.length_map]))]
    exact hlast

/-- The one-pass Elias recognizer has simultaneous quadratic-time and linear-space bounds. -/
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace (fun w : List Bool ↦ [Elias.validBool w])
      (fun n ↦ 5 * n ^ 2 + 16 * n + 2) (fun n ↦ 4 * (n + 2)) := by
  refine ⟨4, 3, 25, boolEmb, machine, fun w ↦ ?_⟩
  refine ⟨1 + runCost w + 1, ?_,
    machine.spaceUsed (machine.initCfg (w.map boolEmb)) (1 + runCost w + 1),
    spaceUsed_le_of_headBound _ _ _ (headBound_run w),
    halts_at w, outputString_eq w, rfl⟩
  change 1 + runCost w + 1 ≤ 5 * w.length ^ 2 + 16 * w.length + 2
  have h := runCost_le w
  omega

end Geb.BitTree.Elias.Machine
