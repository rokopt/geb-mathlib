/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Execution
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

set_option doc.verso true

/-!
# Linear-time recognition with logarithmic work space

The binary-counter machine decides the unified tree-and-payload grammar using
linear time and work space bounded by a constant multiple of the input length's
binary size. Each input bit is consumed once. Carry and return steps leave the
input head stationary.

## Main statements

* {lit}`computableInTimeAndSpace_validBool` gives explicit simultaneous time
  and space bounds in CSLib's finite-state, finite-alphabet machine model.

## Implementation notes

The bound counts every visited work-tape cell, including blank cells. The
read-only input tape is excluded by CSLib's space definition. Binary size is
{name}`Nat.size`, the number of digits in the binary representation.

## Tags

binary tree, bitstring, Turing machine, linear time, logarithmic space
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- After all input macros, one final transition halts the machine. -/
theorem halts_at (w : List Bool) :
    (machine.configs (machine.initCfg (w.map boolEmb)) (2 + runCost w + 1)).state = none := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, _, _⟩ := h
  have hi := inputSymbol_end
    (machine.configs (machine.initCfg (w.map boolEmb)) (2 + runCost w))
    (by simpa only [List.length_map] using hp)
  rw [configs_succ_eq_step', step_end _ _ hr.state hi]

/-- The sole emitted bit is the decision of the unified scanner. -/
theorem outputString_eq (w : List Bool) :
    machine.outputString (machine.initCfg (w.map boolEmb)) (2 + runCost w + 1) =
      [boolEmb (validBool w)] := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, ho, _⟩ := h
  have hi := inputSymbol_end
    (machine.configs (machine.initCfg (w.map boolEmb)) (2 + runCost w))
    (by simpa only [List.length_map] using hp)
  have hm : (account w).mode = (scan w).1 := congrArg Prod.fst (account_project w)
  rw [outputString_succ, ho, outputSymbol_end _ _ hr.state hi, hm]
  rfl

/-- A bounded interval for every work head bounds the total visited work space. -/
theorem spaceUsed_le_of_headBound {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (width t : ℕ)
    (h : ∀ u ≤ t, HeadBound width (machine.configs cfg u)) :
    machine.spaceUsed cfg t ≤ 3 * (width + 1) := by
  have hsub (i : Fin 3) : machine.visitedByTapeHead cfg t i ⊆
      (Finset.range (width + 1)).image (fun n : ℕ ↦ (n : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := machine.mem_visitedByTapeHead.mp hz
    obtain ⟨hlo, hhi⟩ := h u (by omega) i
    apply Finset.mem_image.mpr
    refine ⟨_, Finset.mem_range.mpr ?_, Int.toNat_of_nonneg hlo⟩
    omega
  have hi (i : Fin 3) : machine.spaceUsedByTape cfg t i ≤ width + 1 :=
    (Finset.card_le_card (hsub i)).trans (Finset.card_image_le.trans (by simp))
  calc
    machine.spaceUsed cfg t ≤ ∑ _i : Fin 3, (width + 1) :=
      Finset.sum_le_sum (fun i _ ↦ hi i)
    _ = 3 * (width + 1) := by simp

/-- All work-head positions remain within the chosen binary width, including the halt step. -/
theorem headBound_run (w : List Bool) :
    ∀ u ≤ 2 + runCost w + 1, HeadBound (w.length + 2).size
      (machine.configs (machine.initCfg (w.map boolEmb)) u) := by
  have h := configs_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, _, hh⟩ := h
  intro u hu
  by_cases he : u ≤ 2 + runCost w
  · exact hh u he
  · have hu' : u = 2 + runCost w + 1 := by omega
    subst u
    have hi := inputSymbol_end
      (machine.configs (machine.initCfg (w.map boolEmb)) (2 + runCost w))
      (by simpa only [List.length_map] using hp)
    rw [configs_succ_eq_step', step_end _ _ hr.state hi]
    exact hr.headBound

/-- Recognition takes linear time and logarithmic work space simultaneously. -/
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace (fun w : List Bool ↦ [validBool w])
      (fun n ↦ 6 * n + 5) (fun n ↦ 3 * ((n + 2).size + 1)) := by
  refine ⟨3, 4, 10, boolEmb, machine, fun w ↦ ?_⟩
  refine ⟨2 + runCost w + 1, ?_,
    machine.spaceUsed (machine.initCfg (w.map boolEmb)) (2 + runCost w + 1),
    spaceUsed_le_of_headBound _ _ _ (headBound_run w),
    halts_at w, outputString_eq w, rfl⟩
  change 2 + runCost w + 1 ≤ 6 * w.length + 5
  have h := runCost_le w
  omega

end Geb.BitTree.BinaryMachine
