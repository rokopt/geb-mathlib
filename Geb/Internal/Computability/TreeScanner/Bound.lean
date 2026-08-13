/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.TreeScanner.Steps
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# The tree scanner's time and space bound

`treeScanner` decides `RankedAlphabet.Binary.binRanked.validBool` in time and space affine in
the input length: `halts_at` and `outputString_eq` supply the time bound and the correctness of
the output, and `spaceUsed_linear` supplies the space bound at one work tape.

## Main statements

- `computableInTimeAndSpace_validBool` — the branch's headline theorem: `binRanked.validBool`,
  singleton-listed, is `Turing.MultiTapeTM.ComputableInTimeAndSpace` in `fun n ↦ 2 * n + 3` steps
  and `fun n ↦ 2 * n + 4` cells.

## Implementation notes

The module is admitted to `GebMeta.classicalAllowedModules`. Its subject is the correspondence
between `treeScanner` and Cslib's `Turing.MultiTapeTM.ComputableInTimeAndSpace`, whose space
conjunct rests on `Turing.MultiTapeTM.spaceUsed`, a `Finset.image` through
`Turing.MultiTapeTM.visitedByTapeHead`; mathlib's `Finset.image` depends on `Classical.choice`,
a root neither this repository nor Cslib can remove without redefining the space measure.

## Tags

Turing machine, time complexity, space complexity, tree, preorder encoding
-/

@[expose] public section

namespace Geb.TreeScanner

open Turing MultiTapeTM RankedAlphabet.Binary

/-- The tree scanner computes `binRanked.validBool`, singleton-listed, in `2 * n + 3` steps and
`2 * n + 4` cells of space: the seek, plant and sweep phases give the step count exactly, and
`spaceUsed_linear` at one work tape gives the space bound from it. -/
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace
      (fun w : List Bool ↦ [binRanked.validBool w])
      (fun n ↦ 2 * n + 3) (fun n ↦ 2 * n + 4) := by
  refine ⟨1, 2, 4, boolEmb, treeScanner, fun w ↦ ?_⟩
  refine ⟨2 * w.length + 3, le_refl _,
    treeScanner.spaceUsed (treeScanner.initCfg (w.map boolEmb)) (2 * w.length + 3),
    le_trans (spaceUsed_linear _ _) (by simp), halts_at w, ?_, rfl⟩
  exact outputString_eq w

end Geb.TreeScanner
