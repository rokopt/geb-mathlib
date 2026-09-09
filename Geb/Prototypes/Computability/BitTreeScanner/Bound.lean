/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTreeScanner.Steps
public import Mathlib.Data.Int.Interval

set_option doc.verso true

/-!
# The two-pass tree scanner's time and space bound

{name}`Geb.BitTreeScanner.bitTreeScanner` decides {name}`Geb.BitTreeScanner.validBool`
in time affine in the input length and space logarithmic in it:
{name}`Geb.BitTreeScanner.halts_at` and
{name}`Geb.BitTreeScanner.outputString_eq` give the halting time as
{name}`Geb.BitTreeScanner.totalTime`, which {name}`Geb.BitTreeScanner.totalTime_le` bounds
by {lit}`14 * n + 4`, and {name}`Geb.BitTreeScanner.headsLE_configs` keeps
every head within {name}`Geb.BitTreeScanner.headBound`, three cells above the
input length's digit count, so each tape visits at most that many cells and
one.

The time bound is amortised: a chain of either counter runs outward through
the digits it absorbs at and back, but the chains sum to a constant per bit,
which the potentials of {name}`Geb.BitTreeScanner.cost_add_potential_le` and
{name}`Geb.BitTreeScanner.seekTime_add_le` account. The space bound is what the
counting pass buys: the leaf count and the ruler hold at most the input
length's digit count and two, the pending count at most that digit count
without leading zero, and no chain runs more than one cell past a count's
top.

## Main statements

* {lit}`Geb.BitTreeScanner.spaceUsed_le` — the space used over the whole
  computation is at most {lit}`3 * (bound w + 4)`.
* {lit}`Geb.BitTreeScanner.computableInTimeAndSpace_validBool` —
  {name}`Geb.BitTreeScanner.validBool`, singleton-listed, is
  {name}`Turing.MultiTapeTM.ComputableInTimeAndSpace` in {lit}`14 * n + 4`
  steps and {lit}`3 * (n.bits.length + 4)` cells.

## Implementation notes

The module is admitted to {lit}`GebMeta.classicalAllowedModules`. Its subject
is the correspondence between the machine and Cslib's
{name}`Turing.MultiTapeTM.ComputableInTimeAndSpace`, whose space conjunct rests
on {name}`Turing.MultiTapeTM.spaceUsed`, a {name}`Finset.image` through
{name}`Turing.MultiTapeTM.visitedByTapeHead`; mathlib's {name}`Finset.image`
depends on {lit}`Classical.choice`, a root neither this repository nor Cslib
can remove without redefining the space measure.

## Tags

Turing machine, time complexity, space complexity, logarithmic space, tree,
Elias gamma code, amortised analysis
-/

@[expose] public section

namespace Geb.BitTreeScanner

open Turing MultiTapeTM Geb.BitTreeScanner

variable (w : List Bool)

/-- A tape whose head stays within the bound over a run visits at most the
cells from {lit}`0` to the bound. -/
theorem spaceUsedByTape_le (cfg : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) (t : ℕ)
    (h : ∀ j ≤ t, HeadsLE w (bitTreeScanner.configs cfg j)) (i : Fin 3) :
    bitTreeScanner.spaceUsedByTape cfg t i ≤ bound w + 4 := by
  rw [spaceUsedByTape]
  refine le_trans (Finset.card_le_card (t := Finset.Icc 0 (headBound w)) ?_) ?_
  · intro z hz
    rw [visitedByTapeHead, Finset.mem_image] at hz
    obtain ⟨t', ht', rfl⟩ := hz
    rw [Finset.mem_range] at ht'
    rw [Finset.mem_Icc]
    exact h t' (by omega) i
  · rw [Int.card_Icc, headBound]
    omega

/-- The space used over a run whose heads stay within the bound is at most
{lit}`3 * (bound w + 4)`. -/
theorem spaceUsed_le (cfg : Cfg 3 (Fin 4) (Fin stateCount) (w.map boolEmb)) (t : ℕ)
    (h : ∀ j ≤ t, HeadsLE w (bitTreeScanner.configs cfg j)) :
    bitTreeScanner.spaceUsed cfg t ≤ 3 * (bound w + 4) := by
  rw [spaceUsed]
  refine le_trans (Finset.sum_le_sum fun i _ ↦ spaceUsedByTape_le w cfg t h i) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact le_of_eq rfl

/-- The two-pass tree scanner computes {name}`Geb.BitTreeScanner.validBool`,
singleton-listed, in {lit}`14 * n + 4` steps and {lit}`3 * (n.bits.length + 4)`
cells of space. -/
theorem computableInTimeAndSpace_validBool :
    ComputableInTimeAndSpace (fun w : List Bool ↦ [validBool w])
      (fun n ↦ 14 * n + 4) (fun n ↦ 3 * (n.bits.length + 4)) := by
  refine ⟨3, 4, stateCount, boolEmb, bitTreeScanner, fun w ↦ ?_⟩
  refine ⟨totalTime w, totalTime_le w,
    bitTreeScanner.spaceUsed (bitTreeScanner.initCfg (w.map boolEmb)) (totalTime w),
    spaceUsed_le w _ _ (headsLE_configs w), halts_at w, ?_, rfl⟩
  exact outputString_eq w

end Geb.BitTreeScanner
