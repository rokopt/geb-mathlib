/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Execution
public import Geb.Prototypes.Computability.MultiTape.Rename

set_option doc.verso true in
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

The bound is stated as the machine-specific predicate
{name}`Turing.MultiTapeTM.ComputesFunInTimeAndSpace` rather than as
{name}`Turing.MultiTapeTM.ComputableInTimeAndSpace`, whose machines read and
write {lit}`Bool`: the alphabet here is {lit}`Fin 4`, and a binary re-encoding
of the work alphabet is the remaining step to CSLib's predicate.

## Tags

binary tree, bitstring, Turing machine, linear time, logarithmic space
-/

set_option doc.verso true

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM
open MultiTapeNTM (RunPath)

/-- After all input macros, one final transition halts the machine. -/
theorem halts_at (w : List Bool) :
    (machine.runFrom (machine.initCfg (w.map boolEmb)) (2 + runCost w + 1)).state = none := by
  have h := runFrom_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, _, _⟩ := h
  have hi := inputSymbol_end
    (machine.runFrom (machine.initCfg (w.map boolEmb)) (2 + runCost w))
    (by simpa only [List.length_map] using hp)
  rw [runFrom_succ_eq_step', step_end _ _ hr.state hi]

/-- The sole emitted bit is the decision of the unified scanner. -/
theorem outputString_eq (w : List Bool) :
    machine.outputString (machine.initCfg (w.map boolEmb)) (2 + runCost w + 1) =
      [boolEmb (validBool w)] := by
  have h := runFrom_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, ho, _⟩ := h
  have hi := inputSymbol_end
    (machine.runFrom (machine.initCfg (w.map boolEmb)) (2 + runCost w))
    (by simpa only [List.length_map] using hp)
  have hm : (account w).mode = (scan w).1 := congrArg Prod.fst (account_project w)
  rw [outputString_succ, ho, outputSymbol_end _ _ hr.state hi, hm]
  rfl

/-- A bounded interval for every work head bounds the total visited work space. -/
theorem space_le_of_headBound {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (width t : ℕ)
    (h : ∀ u ≤ t, HeadBound width (machine.runFrom cfg u)) :
    (RunPath.ofDeterministic machine cfg t).space ≤ 3 * (width + 1) := by
  refine le_trans (RunPath.space_le_sum_card _ (S := fun _ ↦ Finset.Icc (0 : ℤ) width) ?_) ?_
  · rintro _ ⟨u, rfl⟩ i
    exact Finset.mem_Icc.mpr (h u (Nat.le_of_lt_succ u.isLt) i)
  · simp [Int.card_Icc]

/-- All work-head positions remain within the chosen binary width, including the halt step. -/
theorem headBound_run (w : List Bool) :
    ∀ u ≤ 2 + runCost w + 1, HeadBound (w.length + 2).size
      (machine.runFrom (machine.initCfg (w.map boolEmb)) u) := by
  have h := runFrom_account w w.length (Nat.le_refl _)
  simp only [List.take_length] at h
  obtain ⟨hr, hp, _, hh⟩ := h
  intro u hu
  by_cases he : u ≤ 2 + runCost w
  · exact hh u he
  · have hu' : u = 2 + runCost w + 1 := by omega
    subst u
    have hi := inputSymbol_end
      (machine.runFrom (machine.initCfg (w.map boolEmb)) (2 + runCost w))
      (by simpa only [List.length_map] using hp)
    rw [runFrom_succ_eq_step', step_end _ _ hr.state hi]
    exact hr.headBound

/-- Recognition takes linear time and logarithmic work space simultaneously. The statement
is the machine-specific predicate, input and output embedded along {name}`boolEmb`, because
the alphabet is {lit}`Fin 4` rather than {lit}`Bool`; a binary re-encoding of the work
alphabet is the remaining step to {name}`Turing.MultiTapeTM.ComputableInTimeAndSpace`. -/
theorem computableInTimeAndSpace_validBool :
    machine.ComputesFunInTimeAndSpace (listEmb boolEmb) (listEmb boolEmb)
      (fun w : List Bool ↦ [validBool w])
      (fun w ↦ 6 * w.length + 5) (fun w ↦ 3 * ((w.length + 2).size + 1)) := by
  intro w
  refine computesInTimeAndSpace_of_halted (t' := 2 + runCost w + 1) (halts_at w)
    (by rw [initCfg_runFrom_output]; exact outputString_eq w) rfl ?_
    (space_le_of_headBound _ _ _ (headBound_run w))
  change 2 + runCost w + 1 ≤ 6 * w.length + 5
  have h := runCost_le w
  omega

end Geb.BitTree.BinaryMachine
