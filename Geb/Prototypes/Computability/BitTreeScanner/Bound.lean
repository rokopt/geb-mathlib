/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Steps
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

set_option doc.verso true

/-!
# The one-pass tree scanner's time and space bound

{name}`Geb.BitTreeScanner.bitTreeScanner` decides {name}`Geb.BitTreeScanner.validBool`
in time and space affine in the input length: {name}`Geb.BitTreeScanner.halts_at`
and {name}`Geb.BitTreeScanner.outputString_eq` supply the time bound and the
correctness of the output, and Cslib's
{name}`Turing.MultiTapeTM.spaceUsed_linear` supplies the space bound at one work
tape.

The time bound is one step per input bit and one emitting step, against the
{lit}`2 * n + 3` of the ranked-term scanner
{lit}`Geb.TreeScanner.computableInTimeAndSpace_validBool`, which seeks to the
input's end before scanning it. The space bound is the trivial one, every
step visiting at most one new cell; the cells the machine visits are the
pending counts it reaches, at most a third of the input's length, since
each unit of count is a pair bit and each pair needs two leaves of at least
two bits, so the bound is linear either way.

## Main statements

* {lit}`Geb.BitTreeScanner.computableInTimeAndSpace_validBool` —
  {name}`Geb.BitTreeScanner.validBool`, singleton-listed, is
  {name}`Turing.MultiTapeTM.ComputableInTimeAndSpace` in {lit}`n + 1` steps and
  {lit}`n + 2` cells.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`. Its subject
is the correspondence between the machine and Cslib's
{name}`Turing.MultiTapeTM.ComputableInTimeAndSpace`, whose space conjunct rests
on {name}`Turing.MultiTapeTM.spaceUsed`, a {name}`Finset.image` through
{name}`Turing.MultiTapeTM.visitedByTapeHead`; mathlib's {name}`Finset.image`
depends on {lit}`Classical.choice`, a root neither this repository nor Cslib
can remove without redefining the space measure.

## Tags

Turing machine, time complexity, space complexity, tree, prefix code
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner
open Geb.TreeScanner (boolEmb)

/-- The one-pass tree scanner computes {name}`Geb.BitTreeScanner.validBool`,
singleton-listed, in {lit}`n + 1` steps and {lit}`n + 2` cells of space: one
step per bit and the emitting step give the step count exactly, and
{name}`Turing.MultiTapeTM.spaceUsed_linear` at one work tape gives the space
bound from it. -/
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace (fun w : List Bool ↦ [validBool w])
      (fun n ↦ n + 1) (fun n ↦ n + 2) := by
  refine ⟨1, 2, 6, boolEmb, bitTreeScanner, fun w ↦ ?_⟩
  refine ⟨w.length + 1, le_refl _,
    bitTreeScanner.spaceUsed (bitTreeScanner.initCfg (w.map boolEmb)) (w.length + 1),
    le_trans (spaceUsed_linear _ _) (by simp), halts_at w, ?_, rfl⟩
  exact outputString_eq w

end Geb.BitTreeScanner
