/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Coequalizer  -- shake: keep

/-!
# Tests for `HasCoequalizers FinSetSkel`

That the instances resolve is the whole of what is checked here; the
sibling test modules exercise the algorithm.

## Tags

category, finite set, coequalizer, test
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- The category has binary coequalizers. -/
example : HasCoequalizers FinSetSkel.{0} := inferInstance

/-- A concrete parallel pair has a colimit. -/
example (f g : (⟨3⟩ : FinSetSkel.{0}) ⟶ (⟨4⟩ : FinSetSkel.{0})) :
    HasColimit (parallelPair f g) := inferInstance
