/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core

/-!
# Tests for the shapes core of `FinSetSkel`

A sample point of a three-element object at a fixed universe, the
index it looks up, its round trip through the index-function
correspondence, and terminality of the one-element object.

## Tags

category, finite set, skeleton, terminal, point
-/

@[expose] public section

open FinSetSkel

/-- A sample point of the three-element object. -/
def sampleSkelPoint : (mk 1 : FinSetSkel.{0}) ⟶ mk 3 := point (2 : Fin 3)

/-- The sample point picks the index it names. -/
theorem sampleSkelPoint_get (t : Fin (mk 1 : FinSetSkel.{0}).len) :
    sampleSkelPoint.toVec.get t = 2 := point_get _ _

/-- The index-function correspondence round-trips the sample
point. -/
theorem sampleSkelPoint_roundtrip :
    (homEquivIdxFun (mk 1) (mk 3)).symm
      (homEquivIdxFun (mk 1) (mk 3) sampleSkelPoint) = sampleSkelPoint :=
  (homEquivIdxFun (mk 1) (mk 3)).symm_apply_apply sampleSkelPoint

/-- Every morphism into the one-element object is the canonical
one. -/
theorem sampleToOne (f : (mk 3 : FinSetSkel.{0}) ⟶ mk 1) : f = toOne (mk 3) :=
  toOne_uniq f
