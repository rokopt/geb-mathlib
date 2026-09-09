/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.TreeScanner.Steps
public import Mathlib.Tactic.FinCases
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Difference
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Machine

set_option doc.verso true

/-!
# Binary-machine transition invariants

The two binary heads remain aligned throughout execution, and the input head
never moves left. Initialization produces the counter values one and zero and
places the mismatch head at one. These statements concern the actual CSLib
configuration sequence.

## Main statements

* {lit}`configs_binaryHeads_eq`: the binary heads are aligned at every time.
* {lit}`configs_inputPos_mono`: the input positions form a monotone sequence.
* {lit}`configs_start`: the two initialization transitions.

## Tags

Turing machine, simulation, binary counter
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- A transition preserves alignment of the two binary heads. -/
theorem step_binaryHeads_eq {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (h : cfg.workTapePos 0 = cfg.workTapePos 1) :
    (machine.step cfg).workTapePos 0 = (machine.step cfg).workTapePos 1 := by
  unfold MultiTapeTM.step
  cases cfg.state with
  | none => exact h
  | some q =>
    dsimp only
    rw [h, binaryHeads_move_eq]

/-- Both binary heads are aligned at every time in the execution. -/
theorem configs_binaryHeads_eq (input : List (Fin 4)) (t : ℕ) :
    (machine.configs (machine.initCfg input) t).workTapePos 0 =
      (machine.configs (machine.initCfg input) t).workTapePos 1 := by
  apply Nat.rec (motive := fun t ↦
    (machine.configs (machine.initCfg input) t).workTapePos 0 =
      (machine.configs (machine.initCfg input) t).workTapePos 1) ?_ ?_ t
  · rfl
  · intro t ih
    rw [configs_succ_eq_step']
    exact step_binaryHeads_eq _ ih

/-- The input head never moves left in one machine step. -/
theorem step_inputPos_le {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) :
    cfg.inputPos.val ≤ (machine.step cfg).inputPos.val := by
  unfold MultiTapeTM.step
  cases cfg.state with
  | none => exact Nat.le_refl _
  | some q => exact le_moveInputPos _ _ (inputMove_ne_neg q _ _)

/-- The input positions form a monotone sequence throughout execution. -/
theorem configs_inputPos_mono (input : List (Fin 4)) :
    Monotone (fun t ↦ (machine.configs (machine.initCfg input) t).inputPos.val) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [configs_succ_eq_step']
  exact step_inputPos_le _

/-- After two transitions, scanning starts with one pending tree. -/
theorem configs_start (input : List (Fin 4)) :
    machine.configs (machine.initCfg input) 2 = startCfg input := by
  rw [show 2 = 0 + 1 + 1 from rfl, configs_succ_eq_step', configs_succ_eq_step',
    configs_zero]
  dsimp [MultiTapeTM.step, initCfg, machine, stInit, stStart]
  refine Cfg.ext ?_ ?_ ?_ ?_
  · rfl
  · simp [startCfg]
  · funext i z
    fin_cases i <;> simp [Function.update_apply, startCfg]
  · funext i
    fin_cases i <;> rfl

/-- A carry flips exactly the selected binary tape's current digit. -/
theorem step_carry_digits {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (p : ℕ)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp : cfg.workTapePos (if leaf then 1 else 0) = p) :
    digits (machine.step cfg) (if leaf then 1 else 0) =
      Function.update (digits cfg (if leaf then 1 else 0)) p
        (!(digits cfg (if leaf then 1 else 0) p)) := by
  funext j
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, tr_carry]
  cases leaf
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hp
    dsimp [digits, carry]
    rw [hp]
    simp only [Function.update_apply]
    by_cases h : j = p
    · subst j
      simp only [ite_true, Cfg.workTapeSymbols, hp]
      exact digit_flipped _
    · have hz : (j : ℤ) ≠ p := by omega
      simp only [h, hz, ↓reduceIte]
      rfl

/-- The other binary tape is unchanged by a carry. -/
theorem step_carry_other_digits {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork)) :
    digits (machine.step cfg) (if leaf then 0 else 1) =
      digits cfg (if leaf then 0 else 1) := by
  funext j
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, tr_carry]
  cases leaf <;> rfl

/-- A carry updates the mismatch head by the displacement of its local digit comparison. -/
theorem step_carry_mismatchPos {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork)) :
    (machine.step cfg).workTapePos 2 = cfg.workTapePos 2 +
      (mismatchMove (cfg.workTapeSymbols 0) (cfg.workTapeSymbols 1)).cast := by
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, tr_carry]
  cases leaf <;> rfl

/-- Every carry advances each binary head by one cell. -/
theorem step_carry_binaryPos {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (i : Fin 3) (hi : i ≠ 2)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork)) :
    (machine.step cfg).workTapePos i = cfg.workTapePos i + 1 := by
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, tr_carry]
  simp [carry, hi]

/-- Carry propagation does not move the input head. -/
theorem step_carry_inputPos {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork)) :
    (machine.step cfg).inputPos = cfg.inputPos := by
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, tr_carry]
  exact moveInputPos_zero _

/-- A carry continues through ones and ends at the first zero. -/
theorem step_carry_state {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork)) :
    (machine.step cfg).state = some (if digit (cfg.workTapeSymbols (if leaf then 1 else 0))
      then (if leaf then stCarryLeaf else stCarryFork) else stReturn) := by
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, tr_carry]
  rfl

/-- Carry propagation emits no output symbols. -/
theorem outputSymbol_carry {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork)) :
    machine.outputSymbol cfg = none := by
  simp only [outputSymbol, hq, tr_carry]
  cases leaf <;> rfl

/-- A carry preserves every origin tag on the first binary tape. -/
theorem step_carry_origin {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (z : ℤ)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork)) :
    origin ((machine.step cfg).workTapes 0 z) = origin (cfg.workTapes 0 z) := by
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, tr_carry]
  cases leaf with
  | true => rfl
  | false =>
    change origin (Function.update (cfg.workTapes 0) (cfg.workTapePos 0)
      (some (flipped (cfg.workTapeSymbols 0))) z) = _
    by_cases hz : z = cfg.workTapePos 0
    · subst z
      rw [Function.update_self]
      exact origin_flipped _
    · rw [Function.update_of_ne hz]

/-- Carry propagation never writes on the mismatch tape. -/
theorem step_carry_marker {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork)) :
    (machine.step cfg).workTapes 2 = cfg.workTapes 2 := by
  rw [Geb.TreeScanner.step_of_state _ _ _ hq, tr_carry]
  cases leaf <;> rfl

/-- One carry transition preserves the mismatch-count invariant. -/
theorem step_carry_mismatch {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (width p : ℕ)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = p) (hp1 : cfg.workTapePos 1 = p) (hp : p < width)
    (hm : cfg.workTapePos 2 = (mismatchCount width (digits cfg 0) (digits cfg 1) : ℤ)) :
    (machine.step cfg).workTapePos 2 =
      (mismatchCount width (digits (machine.step cfg) 0)
        (digits (machine.step cfg) 1) : ℤ) := by
  have hd := step_carry_digits cfg leaf p hq (by cases leaf <;> assumption)
  have he := step_carry_other_digits cfg leaf hq
  rw [step_carry_mismatchPos cfg leaf hq, hm]
  cases leaf <;> simp only [Bool.false_eq_true, ↓reduceIte] at hd he
  · rw [hd, he]
    rw [← flipAt, mismatchCount_flip_left width p _ _ hp]
    congr 1
    simp only [mismatchMove, Cfg.workTapeSymbols, hp0, hp1, digits, beq_iff_eq]
    split_ifs <;> simp_all
  · rw [he, hd]
    rw [← flipAt, mismatchCount_flip_right width p _ _ hp]
    congr 1
    simp only [mismatchMove, Cfg.workTapeSymbols, hp0, hp1, digits, beq_iff_eq]
    split_ifs <;> simp_all

end Geb.BitTree.BinaryMachine
