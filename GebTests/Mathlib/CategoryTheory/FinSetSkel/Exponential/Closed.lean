/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Exponential.Closed

/-!
# Tests for the monoidal closed structure of `FinSetSkel`

The internal hom functor resolved through the monoidal closed
structure at a fixed universe, the length of a sample exponential
object, and a sample hom-level equivalence with its naturality.

## Tags

category, finite set, skeleton, exponential, monoidal closed
-/

@[expose] public section

open CategoryTheory MonoidalCategory FinSetSkel

/-- The internal hom functor out of the two-element object, resolved
through the monoidal closed structure at a fixed universe. Naming it
gives the `GebMeta` axiom linter a declaration to inspect. -/
def sampleSkelIhom : FinSetSkel.{0} ⥤ FinSetSkel.{0} := ihom (mk 2)

/-- The exponential of the two-element object into the three-element
object is the nine-element object. -/
theorem sampleSkelIhom_obj : sampleSkelIhom.obj (mk 3) = mk 9 := rfl

/-- The exponential's hom-level equivalence at sample lengths. -/
def sampleSkelExpHomEquiv :
    ((tensorLeft (mk 2 : FinSetSkel.{0})).obj (mk 3) ⟶ mk 4) ≃
      ((mk 3 : FinSetSkel.{0}) ⟶ mk (4 ^ 2)) :=
  expHomEquiv (mk 2) (mk 3) (mk 4)

/-- Naturality of the exponential's equivalence at sample lengths. -/
theorem sampleSkelExpHomEquiv_naturality
    (f : (mk 1 : FinSetSkel.{0}) ⟶ mk 3)
    (g : (tensorLeft (mk 2 : FinSetSkel.{0})).obj (mk 3) ⟶ mk 4) :
    expHomEquiv (mk 2) (mk 1) (mk 4) ((tensorLeft (mk 2)).map f ≫ g) =
      f ≫ expHomEquiv (mk 2) (mk 3) (mk 4) g :=
  expHomEquiv_naturality (mk 2) (mk 1) (mk 3) (mk 4) f g
