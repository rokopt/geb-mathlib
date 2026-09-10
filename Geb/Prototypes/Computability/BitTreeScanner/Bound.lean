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
and {name}`Geb.BitTreeScanner.outputString_eq` give the halting time as
{name}`Geb.BitTreeScanner.time` and {name}`Geb.BitTreeScanner.endCost` at the input,
{name}`Geb.BitTreeScanner.time_add_endCost_le` bounds that by {lit}`5 * n + 1`, and
Cslib's {name}`Turing.MultiTapeTM.spaceUsed_linear` gives the space bound at
two work tapes.

The time bound is amortised: a payload bit's decrement borrows through the
zeros below the lowest one of the remaining count, {lit}`2 * borrowLength + 2`
steps at a borrow no longer than the count's digits, but the borrows over a
leaf sum to a constant per bit, which the potential of
{name}`Geb.BitTreeScanner.cost_add_potential_le` accounts.
The space bound is the trivial one, every step visiting at most one new cell;
the second tape holds a count of at most {lit}`log₂ n` digits, but the first
holds the pending count in unary, so the total stays linear.

## Main statements

* {lit}`Geb.BitTreeScanner.computableInTimeAndSpace_validBool` —
  {name}`Geb.BitTreeScanner.validBool`, singleton-listed, is
  {name}`Turing.MultiTapeTM.ComputableInTimeAndSpace` in {lit}`5 * n + 1`
  steps and {lit}`10 * n + 4` cells.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`. Its subject
is the correspondence between the machine and Cslib's
{name}`Turing.MultiTapeTM.ComputableInTimeAndSpace`, whose space conjunct rests
on {name}`Turing.MultiTapeTM.spaceUsed`, a {name}`Finset.image` through
{name}`Turing.MultiTapeTM.visitedByTapeHead`; mathlib's {name}`Finset.image`
depends on {lit}`Classical.choice`, a root neither this repository nor Cslib
can remove without redefining the space measure.

## Tags

Turing machine, time complexity, space complexity, tree, Elias gamma code,
amortised analysis
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

/-- The one-pass tree scanner computes {name}`Geb.BitTreeScanner.validBool`,
singleton-listed, in {lit}`5 * n + 1` steps and {lit}`10 * n + 4` cells of
space: the bits' amortised costs and the steps to the halt give the step
count, and {name}`Turing.MultiTapeTM.spaceUsed_linear` at two work tapes gives
the space bound from it. -/
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace (fun w : List Bool ↦ [validBool w])
      (fun n ↦ 5 * n + 1) (fun n ↦ 10 * n + 4) := by
  refine ⟨2, 4, 11, boolEmb, bitTreeScanner, fun w ↦ ?_⟩
  refine ⟨time w + endCost (scanFinal w), time_add_endCost_le w,
    bitTreeScanner.spaceUsed (bitTreeScanner.initCfg (w.map boolEmb))
      (time w + endCost (scanFinal w)),
    le_trans (spaceUsed_linear _ _) (by
      have := time_add_endCost_le w
      change 2 * (time w + endCost (scanFinal w)) + 2 ≤ 10 * w.length + 4
      omega),
    halts_at w, ?_, rfl⟩
  exact outputString_eq w

end Geb.BitTreeScanner
