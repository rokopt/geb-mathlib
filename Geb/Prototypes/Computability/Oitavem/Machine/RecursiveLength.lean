/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Recursion
public import Geb.Prototypes.Computability.Oitavem.Machine.Repeat
import Mathlib.Tactic.FinCases

set_option doc.verso true in
/-!
# Safe recursion over a generated quadratic word

The machine computes {name}`Geb.Oitavem.lengthByRec` after
{name}`Geb.Oitavem.squareWord` using a saved-prefix loop. Each iteration queries the
next digit of the generated square in reverse index order and regenerates the
successor of the saved shortlex value. Prefix capture retains the next value while
the old value remains available to the step generator.

The eight tapes hold the mask, capture buffer, reader countdown, digit result,
recursion countdown, saved word, digit query, and square-generator scratch.
Initialization computes a length for the loop countdown and the logarithmic mask.
The recursive value starts empty and is computed by the loop. All tapes are cleared
after the final saved word has been emitted.

## Main definitions

* {lit}`squareRecLengthFromHome` is the reusable eight-tape subroutine.
* {lit}`squareRecLengthMachine` homes the input head before calling it.

## Main statements

* {lit}`squareRecLengthFromHome_emitsIn` proves the output and scratch cleanup.
* {lit}`squareRecLengthMachine_computes` proves simultaneous polynomial time and
  logarithmic space on the machine that runs the recursion.

## Implementation notes

The loop's invariant is {name}`Geb.Oitavem.prefixLoop_lengthByRec`. Its number of
tapes is constant across iterations. The contracts inherit CSLib's
{lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, safe recursion, generated input, example
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Ports of the recursive length step within the generated reader's six tapes. -/
@[expose] def squareRecLayout : Fin 4 → Fin 6 := ![2, 3, 4, 1]

/-- The four recursion ports occupy distinct tapes. -/
theorem squareRecLayout_injective : Function.Injective squareRecLayout := by decide

/-- Initialize the recursion countdown and a mask whose length bounds every saved value. -/
@[expose] def squareRecLengthSetup :=
  seq (generatedLength (squareFromHome (6 : Fin 7)))
    (seq (copy (0 : Fin 8) 4) (inc 0))

/-- Initialization starts from blank registers, obtains the generated length,
and keeps its successor's binary digits as a logarithmic mask. -/
theorem squareRecLengthSetup_transformsIn :
    TransformsIn squareRecLengthSetup (fun _ σ ↦ ∀ i, σ i = [])
      (fun input _ ↦ ![counterWord (input.length * input.length + 1), [], [], [],
        counterWord (input.length * input.length), [], [], []])
      (fun n ↦ (4 * (2 * n.size + 1) + 9 +
        squareFromHomeTime (2 * n.size + 1) n * (2 * (2 * n.size + 1) + 5)) +
        ((5 * (2 * n.size + 1) + 12) + (2 * (2 * n.size + 1) + 4)))
      (fun n ↦ 2 * n.size + 1) := by
  let B := fun n : ℕ ↦ 2 * n.size + 1
  have hl := squareLength_transformsIn (6 : Fin 7) B (fun n ↦ by dsimp [B]; omega)
    size_square_add_one_le
  have hc := Transforms.toIn_of (fun n ↦ copy_transforms (0 : Fin 8) 4 (by decide) (B n))
    (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (hb 0))
  have hi := Transforms.toIn_of (fun n ↦ inc_transforms (0 : Fin 8) (B n))
    (fun input σ ↦ σ 0 = counterWord (input.length * input.length)) (by
      intro input σ hb hp
      apply hb.update
      rw [hp, incL_counterWord, length_counterWord]
      exact size_square_add_one_le _)
  have hs := (hl.seq (hc.seq hi)).mono_pre
    (Pre' := fun _ σ ↦ ∀ i, σ i = []) (by intro _ _ _ _; exact ⟨trivial, trivial, rfl⟩)
  refine hs.congr ?_
  intro input σ hp
  funext i
  fin_cases i <;> simp [hp, incL_counterWord] <;> rfl

/-- Run the saved-prefix loop and emit its final value, clearing the remaining live tapes. -/
@[expose] def squareRecLengthFromHome :=
  seq squareRecLengthSetup
    (seq (lengthRecLoop (generatedAt (squareFromHome (3 : Fin 4)) 2) squareRecLayout)
      (seq (emitStored (5 : Fin 8)) (seq (const [] 0) (const [] 5))))

/-- The termination bound inherited from initialization, generated queries, and prefix capture. -/
@[expose] def squareRecLengthTime (n : ℕ) : ℕ :=
  let B := 2 * n.size + 1
  let T := squareFromHomeTime B n
  let A := T * (2 * B + 8) + 13 * B + 30
  ((4 * B + 9 + T * (2 * B + 5)) + ((5 * B + 12) + (2 * B + 4))) +
    ((n * n * (A + 34 * B + 82) + 1) + ((2 * B + 4) + ((4 * B + 9) + (4 * B + 9))))

/-- The saved-prefix recursion computes numerical length of the generated square,
and returns all eight work tapes blank. -/
theorem squareRecLengthFromHome_emitsIn :
    EmitsIn squareRecLengthFromHome (fun _ σ ↦ ∀ i, σ i = []) (fun _ _ _ ↦ [])
      (fun input _ ↦ (Expr.comp (safe := false) lengthByRec ![squareWord]).eval ![input] Fin.elim0)
      squareRecLengthTime (fun n ↦ 2 * n.size + 1) := by
  let B := fun n : ℕ ↦ 2 * n.size + 1
  have hr := squareAt_readsAt (3 : Fin 4) 2 B (fun n ↦ by dsimp [B]; omega)
    (fun n ↦ by dsimp [B]; omega)
  have hl := lengthRecLoop_transformsIn squareRecLayout squareRecLayout_injective hr
    (by intro input σ q d hp; simpa [squareRecLayout, oldTape, countTape, resultTape] using hp)
    (fun _ _ _ _ ↦ rfl)
    (by intro input σ c v hp; simpa [retainedVal, squareRecLayout,
          oldTape, countTape, resultTape] using hp)
    (fun _ _ _ _ ↦ rfl)
    (N := fun n ↦ n * n) (fun input _ _ ↦ (length_squareWord input).le)
  have hz (i : Fin 8) := Transforms.toIn_of (fun n ↦ const_transforms [] i (B n))
    (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (Nat.zero_le _))
  have he := (emitStored_emitsIn (5 : Fin 8) B).seqTransformsIn ((hz 0).seq (hz 5))
  have hall := squareRecLengthSetup_transformsIn.seqEmitsIn (hl.seqEmitsIn he)
  have hm := hall.mono_pre (Pre' := fun _ σ ↦ ∀ i, σ i = []) (by
    intro input σ _ hp
    have hk : (unrank (input.length * input.length)).length ≤
        (input.length * input.length + 1).size := length_unrank_le le_rfl
    refine ⟨hp, ⟨?_, trivial, trivial, trivial⟩⟩
    simpa [squareRecLayout, oldTape, countTape, resultTape, length_squareWord,
      length_counterWord] using hk)
  have hf := hm.congr (F' := fun _ _ _ ↦ []) (by
    intro input σ _
    funext i
    fin_cases i <;>
      simp [retainedVal, squareRecLayout, oldTape, countTape, tapeCase] <;> rfl)
  refine hf.congr_output ?_
  intro input σ _
  rw [Expr.eval_comp]
  have heq := eval_lengthByRec (squareWord.eval ![input] Fin.elim0)
  simp only [Matrix.cons_fin_one] at heq ⊢
  rw [heq]
  simp [retainedVal, squareRecLayout, oldTape, countTape, tapeCase]
  rfl

/-- Home the physical input before the eight-tape recursive length subroutine. -/
@[expose] def squareRecLengthMachine := seq inBack squareRecLengthFromHome

/-- The saved-prefix implementation has polynomial time and logarithmic work space,
with the same machine witnessing both bounds. -/
theorem squareRecLengthMachine_computes :
    ∃ C d : ℕ, ComputesFunInTimeAndSpace squareRecLengthMachine (.refl _) (.refl _)
      (fun input ↦ (Expr.comp (safe := false) lengthByRec ![squareWord]).eval ![input] Fin.elim0)
      (fun input ↦ C * (input.length + 1) ^ d)
      (fun input ↦ C * (input.length.size + 1)) := by
  let : Fintype (StateOf (squareFromHome (3 : Fin 4))) := inferInstance
  let : Fintype (StateOf (generatedAt (squareFromHome (3 : Fin 4)) 2)) := inferInstance
  let : Fintype (StateOf (squareFromHome (6 : Fin 7))) := inferInstance
  let : Fintype (StateOf (generatedLength (squareFromHome (6 : Fin 7)))) := inferInstance
  let : Fintype (StateOf (lengthRecStep (generatedAt (squareFromHome (3 : Fin 4)) 2)
      (squareRecLayout 0) (squareRecLayout 1) (squareRecLayout 2) (squareRecLayout 3))) :=
    inferInstance
  let : Fintype (StateOf squareRecLengthFromHome) := by
    unfold squareRecLengthFromHome squareRecLengthSetup lengthRecLoop retainedLoop
      lengthRecStep readPrevious generatedPrefix capturePrefix numericSuccGenerator emitStored
    infer_instance
  exact squareRecLengthFromHome_emitsIn.computes_polytime_logspace
    (fun _ _ ↦ rfl) 2 (fun n ↦ by omega)

end

end Geb.Oitavem.Machine
