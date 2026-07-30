/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Limits

/-!
# Tests for the equalizer cone of `FinSetSkel`

The cone of a sample morphism against itself, whose point is the whole
domain.

## Tags

category, finite set, skeleton, equalizer, limit cone
-/

@[expose] public section

open CategoryTheory Limits FinSetSkel

/-- A sample morphism, constant at index `0`. -/
def sampleSkelEqualizerConst : (mk 5 : FinSetSkel.{0}) ⟶ mk 2 :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ 0)

/-- The equalizer cone of the sample morphism against itself. Permanent
monomorphic witness for this module's axiom set. -/
def sampleSkelEqualizerCone :
    LimitCone (parallelPair sampleSkelEqualizerConst sampleSkelEqualizerConst) :=
  equalizerCone sampleSkelEqualizerConst sampleSkelEqualizerConst

/-- The equalizer of a morphism with itself is its whole domain. -/
theorem sampleSkelEqualizerCone_pt : sampleSkelEqualizerCone.cone.pt = mk 5 := by
  rfl
