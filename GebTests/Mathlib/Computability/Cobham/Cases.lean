/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Computability.Cobham.Cases

/-!
# Definition by cases over Cobham's class, exercised

Fixtures for `Geb/Mathlib/Computability/Cobham/Cases.lean`: a branch family
distinct at every index, and the combinators the branches are built from.
`combinators_apply` names `casesOf`, which is the constant `lake shake` infers
the import from.

## Main definitions

* `sampleBranches`, `sampleBranchesOneBit` — branch families over two bits and
  over one.

## Main statements

* `sampleCases_dispatch` — each branch is selected by its own scrutinee.
* `sampleCases_padding` — a short scrutinee reads as zero-padded and a long one
  ignores its high bits.
* `combinators_apply` — the iterated predecessor, the prepended and constant
  words, and the diagonal, at literal arguments.

## Tags

Cobham, bounded recursion on notation, definition by cases
-/

set_option linter.privateModule false

open Cobham

/-- A branch family over two bits, distinct at every index. -/
def sampleBranches : (Fin 2 → Bool) → COf 1 := fun v ↦
  constAtOf 1 (if v 0 then if v 1 then [true, true] else [true] else
    if v 1 then [false] else [])

/-- A one-bit branch family, for the diagonal. -/
def sampleBranchesOneBit : (Fin 1 → Bool) → COf 1 := fun v ↦
  constAtOf 1 (if v 0 then [true] else [])

/-- Each of the four branches is selected by its own scrutinee. -/
theorem sampleCases_dispatch :
    casesSem 2 sampleBranches ![[false, false], []] = [] ∧
      casesSem 2 sampleBranches ![[true, false], []] = [true] ∧
      casesSem 2 sampleBranches ![[false, true], []] = [false] ∧
      casesSem 2 sampleBranches ![[true, true], []] = [true, true] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [casesSem_eq] <;> rfl

/-- A scrutinee shorter than the dispatch width reads as zero-padded, and one
longer than it ignores the high bits. -/
theorem sampleCases_padding :
    casesSem 2 sampleBranches ![[], []] = [] ∧
      casesSem 2 sampleBranches ![[true], []] = [true] ∧
      casesSem 2 sampleBranches ![[true, true, true], []] = [true, true] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [casesSem_eq] <;> rfl

/-- The combinators the branches are built from. The first two need an explicit
`rfl` after the rewrite: `rw` closes only by its own `rfl` at reducible
transparency, which leaves the list computation standing. -/
theorem combinators_apply :
    stepWord (predIterOf 2) [true, false, true] = [true] ∧
      stepWord (prependOf [false, true] (predIterOf 1)) [true, false] =
        [false, true, false] ∧
      stepWord (constAtOf 1 [true]) [false, false] = [true] ∧
      baseWord (constAtOf 0 [true, false]) = [true, false] ∧
      stepWord (diagOf (casesOf 1 sampleBranchesOneBit)) [true] = [true] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [stepWord_predIterOf]
    rfl
  · rw [stepWord_prependOf, stepWord_predIterOf]
    rfl
  · rw [stepWord_constAtOf]
  · rw [baseWord_constAtOf]
  · rw [stepWord_diagOf]
    rfl
