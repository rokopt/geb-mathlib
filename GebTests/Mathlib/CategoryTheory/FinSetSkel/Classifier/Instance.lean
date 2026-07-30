/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Instance

/-!
# Tests for the subobject classifier of `FinSetSkel`

The classifier at `Type 0`, its classifying object and its terminal
object.

## Tags

category, finite set, skeleton, subobject classifier
-/

@[expose] public section

open CategoryTheory FinSetSkel

/-- The subobject classifier at `Type 0`. Naming it gives the
`GebMeta` axiom linter a declaration to inspect. -/
def sampleSkelClassifier : Subobject.Classifier FinSetSkel.{0} := classifier

/-- Its classifying object is the two-element object. -/
theorem sampleSkelClassifier_Ω : sampleSkelClassifier.Ω = mk 2 := rfl

/-- Its terminal object is the one-element object. -/
theorem sampleSkelClassifier_Ω₀ : sampleSkelClassifier.Ω₀ = mk 1 := rfl
