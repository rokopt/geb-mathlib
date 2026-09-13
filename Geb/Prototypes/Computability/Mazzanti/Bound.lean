/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Mazzanti.Words
public import Geb.Prototypes.Computability.BitTree.Bound

set_option doc.verso true

/-!
# Machine bounds for the algebra's bit-tree recognizer

The extensional correctness theorem transfers the existing machine witness to
the bitstring function defined by the algebra expression.

## Main statements

* {lit}`computableInTimeAndSpace_recognize` supplies simultaneous linear bounds.
* {lit}`recognize_resources` conjoins those bounds with non-size-increase.

## Implementation notes

These theorems reuse the unary scanner's machine. They do not bound the Lean
interpreter's evaluation and do not assume or prove the general machine
characterization of the function algebra.

## Tags

function algebra, Turing machine, time complexity, space complexity
-/

public section

namespace Geb.Mazzanti.BitTree

open Turing.MultiTapeTM

/-- One machine computes the algebra recognizer in input length plus three transitions
and input length plus two visited work cells. -/
theorem computableInTimeAndSpace_recognize :
    ComputableInTimeAndSpace recognize (fun n ↦ n + 3) (fun n ↦ n + 2) := by
  have he : recognize = fun w ↦ [Geb.BitTree.validBool w] := funext recognize_eq
  rw [he]
  exact Geb.BitTree.computableInTimeAndSpace_validBool

/-- The algebra recognizer is non-size-increasing and has simultaneous linear time and space. -/
theorem recognize_resources : WordNonSizeIncreasing recognize ∧
    ComputableInTimeAndSpace recognize (fun n ↦ n + 3) (fun n ↦ n + 2) :=
  ⟨nonSizeIncreasing_recognize, computableInTimeAndSpace_recognize⟩

end Geb.Mazzanti.BitTree
