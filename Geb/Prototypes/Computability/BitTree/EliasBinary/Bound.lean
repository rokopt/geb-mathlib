/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Execution
public import Geb.Prototypes.Computability.BitTree.Elias.ScannerCorrect
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

set_option doc.verso true

/-!
# Linear time and logarithmic work space on the Elias-length encoding

The two-pass binary-counter machine decides the Elias-length tree language in linear time
with work space bounded by a constant multiple of the binary size of the input length. The
first pass reads the input once to fix the counter width; the second pass reads it once more,
consuming each bit in constant amortized time.

## Main statements

* {lit}`computableInTimeAndSpace_validBool` gives the simultaneous bounds in CSLib's
  finite-state, finite-alphabet machine model.

## Implementation notes

Every head stays within the cells from minus one to the width, so each of the nine work tapes
visits at most the width plus two cells. The read-only input tape is excluded by CSLib's
space definition.

## Tags

Elias delta code, Turing machine, linear time, logarithmic space
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.BinaryMachine (boolEmb)

/-- The finite state of an account is the accepting state exactly at acceptance. -/
theorem phaseState_eq_done (s : Elias.Scanner.State) : phaseState s = stDone ↔ s.1 = .done := by
  rcases s with ⟨m, _⟩
  cases m <;> simp [phaseState, stDone, stTree, stZeros, stSizeBit, stLengthBit, stPayloadBit,
    stDead]

/-- The time of the whole run, before the halting step. -/
abbrev totalCost (w : List Bool) : ℕ := prefixCost w.length w

/-- After the second pass, one final transition halts the machine. -/
theorem halts_at (w : List Bool) :
    (machine.configs (machine.initCfg (w.map boolEmb)) (totalCost w + 1)).state = none := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, _, _⟩ := h
  have hi := inputSymbol_end (machine.configs (machine.initCfg (w.map boolEmb)) (totalCost w))
    (by simpa only [List.length_map] using hp)
  rw [configs_succ_eq_step', step_end _ _ hr.state (phaseState_read _) hi]

/-- The sole emitted bit is the decision of the Elias-length tree recognizer. -/
theorem outputString_eq (w : List Bool) :
    machine.outputString (machine.initCfg (w.map boolEmb)) (totalCost w + 1) =
      [boolEmb (Elias.validBool w)] := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, ho, _⟩ := h
  have hi := inputSymbol_end (machine.configs (machine.initCfg (w.map boolEmb)) (totalCost w))
    (by simpa only [List.length_map] using hp)
  have hq : (phaseState (account w.length w).state == stDone) = Elias.validBool w := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, phaseState_eq_done, account_done_iff, Elias.Scanner.validBool_eq]
  rw [outputString_succ, ho, outputSymbol_end _ _ hr.state (phaseState_read _) hi, hq]
  rfl

/-- Nine heads confined to the interval visit at most nine times its number of cells. -/
theorem spaceUsed_le_of_headBound {input : List (Fin 4)}
    (cfg : Cfg 9 (Fin 4) Control input) (width t : ℕ)
    (h : ∀ u ≤ t, HeadBound width (machine.configs cfg u)) :
    machine.spaceUsed cfg t ≤ 9 * (width + 2) := by
  have hsub (i : Fin 9) : machine.visitedByTapeHead cfg t i ⊆
      (Finset.range (width + 2)).image (fun n : ℕ ↦ (n : ℤ) - 1) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := machine.mem_visitedByTapeHead.mp hz
    obtain ⟨hlo, hhi⟩ := h u (by omega) i
    apply Finset.mem_image.mpr
    refine ⟨((machine.configs cfg u).workTapePos i + 1).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · omega
    · omega
  have hi (i : Fin 9) : machine.spaceUsedByTape cfg t i ≤ width + 2 :=
    (Finset.card_le_card (hsub i)).trans (Finset.card_image_le.trans (by simp))
  calc
    machine.spaceUsed cfg t ≤ ∑ _i : Fin 9, (width + 2) :=
      Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = 9 * (width + 2) := by simp

/-- Every head stays within the width throughout the run, including the halting step. -/
theorem headBound_run (w : List Bool) :
    ∀ u ≤ totalCost w + 1, HeadBound (widthOf w.length)
      (machine.configs (machine.initCfg (w.map boolEmb)) u) := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, _, hh⟩ := h
  intro u hu
  by_cases he : u ≤ totalCost w
  · exact hh u he
  · have hu' : u = totalCost w + 1 := by omega
    subst u
    have hi := inputSymbol_end (machine.configs (machine.initCfg (w.map boolEmb)) (totalCost w))
      (by simpa only [List.length_map] using hp)
    rw [configs_succ_eq_step', step_end _ _ hr.state (phaseState_read _) hi]
    exact hr.bound

/-- The whole run takes linear time. -/
theorem totalCost_le (w : List Bool) : totalCost w + 1 ≤ 25 * w.length + 6 := by
  have h1 := passOneCost_add w.length
  have h2 := runCost_le w.length w
  have h3 := potential_initial w.length
  unfold totalCost prefixCost
  omega

/-- Recognition of the Elias-length tree encoding takes linear time and logarithmic work
space simultaneously. -/
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace (fun w : List Bool ↦ [Elias.validBool w])
      (fun n ↦ 25 * n + 6) (fun n ↦ 9 * ((2 * n + 2).size + 3)) := by
  refine ⟨9, 4, 30, boolEmb, machine, fun w ↦ ?_⟩
  refine ⟨totalCost w + 1, totalCost_le w,
    machine.spaceUsed (machine.initCfg (w.map boolEmb)) (totalCost w + 1), ?_,
    halts_at w, outputString_eq w, rfl⟩
  have h := spaceUsed_le_of_headBound _ _ _ (headBound_run w)
  unfold widthOf at h
  omega

end Geb.BitTree.EliasBinary
