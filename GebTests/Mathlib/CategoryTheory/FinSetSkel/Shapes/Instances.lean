/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Instances

/-!
# Tests for the shapes instances of `FinSetSkel`

The chosen cones, the cartesian structure and the coproduct
structure they package: the resolution of the registered limit and
colimit classes, and the length of a tensor product.

## Tags

category, finite set, skeleton, cartesian, coproduct
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory FinSetSkel

/-- The registered instances resolve. -/
theorem sampleSkelInstances :
    HasInitial FinSetSkel.{0} ∧ HasBinaryCoproducts FinSetSkel.{0} ∧
      HasFiniteCoproducts FinSetSkel.{0} ∧ HasFiniteProducts FinSetSkel.{0} ∧
      HasTerminal FinSetSkel.{0} ∧ HasBinaryProducts FinSetSkel.{0} :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance⟩

/-- The tensor product of two objects has the product's length. -/
theorem sampleSkelTensorObj :
    ((mk 2 : FinSetSkel.{0}) ⊗ mk 3) = mk 6 := rfl
