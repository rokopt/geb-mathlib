/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.LargeIR.Morphism
public import Geb.Prototypes.LargeIR.Grothendieck -- shake: keep

/-!
# Tests for the free coproduct completion as a Grothendieck construction

Exercises `Geb.Prototypes.LargeIR.Grothendieck` on the family of the object
`Fin 3 → Bool` of `GebTests.Prototypes.LargeIR.Basic` and the square over
`not` of `GebTests.Prototypes.LargeIR.Morphism`: the object and morphism
correspondences compute, and the code's endofunctor acts on the square by
the code's action on its morphism of families. This module depends on
`Classical.choice` through the module under test and is listed in
`GebMeta.classicalAllowedModules`.

## Tags

prototype, free coproduct completion, Grothendieck construction, reduction
test
-/

@[expose] public section

open CategoryTheory IndRec GebProto.LargeIR

namespace LargeIRTest

/-- The family of the object as an object of the construction. -/
def famP3 : FamGr := toGr (famOfPsh (ofSlice p3))

-- Its base is the index type `Bool` and its fibre the family.
example : famP3.base = Bool := rfl
example : famP3.fiber = (famOfPsh (ofSlice p3)).2 := rfl

-- The object correspondence is inverse to the family.
example : ofGr famP3 = famOfPsh (ofSlice p3) := rfl

/-- The square over `not` as a morphism of the construction. -/
def flipGr : toGr (famOfPsh (ofSlice p3)) ⟶ toGr (famOfPsh (ofSlice (not ∘ p3))) :=
  homGrEquiv _ _ (famHomOfNatTrans flipHom)

-- Its base morphism is `not`.
example : CoGrothendieck.homBase flipGr = ↾ not := rfl

-- The morphism correspondence is inverse to the morphism of families.
example : (homGrEquiv _ _).symm flipGr = famHomOfNatTrans flipHom := rfl

-- The code's endofunctor sends the object to the family of the code's
-- interpretation.
example : (codeFunctor piBool).obj famP3 =
    toGr (IR.interpObj Type Type (code piBool) (famOfPsh (ofSlice p3))) :=
  rfl

-- And acts on the square by the code's action on its morphism of families.
example : (homGrEquiv _ _).symm ((codeFunctor piBool).map flipGr) =
    codeMap piBool (famHomOfNatTrans flipHom) :=
  rfl

end LargeIRTest
