/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.LargeIR.Basic
public import Geb.Prototypes.LargeIR.General -- shake: keep

/-!
# Tests for the general code of a base-cartesian functor

Exercises `Geb.Prototypes.LargeIR.General` at the transcription of the functor
`A ↦ A true × A false`, which `arrowPshBaseCartesian` exhibits as
base-cartesian, on the elements of `GebTests.Prototypes.LargeIR.Basic`: the
value computes in dependent-type terms, and the general isomorphism reads the
comparison map's element as a level-`0` element with the identity base
assignment and a fibre element at the level-`1` shape, and the element over
`not` as one whose base assignment is `not`.

## Tags

prototype, inductive-recursive, code, walking arrow, cartesian, reduction
test
-/

@[expose] public section

open CategoryTheory PresheafIRUniv IndRec GebProto.LargeIR

namespace LargeIRTest

/-! ## The value in dependent-type terms -/

-- The comparison map's element: the level-`1` shape, the identity base
-- assignment on the level-`0` directions, and the assignment `true ↦ 0`,
-- `false ↦ 1` on the level-`1` directions.
example : (elemEquiv (arrowPsh piBool) (ofSlice p3) sample).1 = .inr () := rfl
example : (elemEquiv (arrowPsh piBool) (ofSlice p3) sample).2.1 ⟨.inl true, rfl⟩ = true := rfl
example : ((elemEquiv (arrowPsh piBool) (ofSlice p3) sample).2.2 ⟨.inr false, rfl⟩).1 =
    (1 : Fin 3) :=
  rfl

/-! ## The general isomorphism at the transcription -/

/-- The comparison map's element read through the general isomorphism. -/
def sampleGen :=
  (genCodeEquiv (ofSlice p3) (arrowPshBaseCartesian piBool)).total ⟨sample, rfl⟩

-- The level-`0` element below: the level-`0` shape with the identity base
-- assignment.
example : sampleGen.1.1 = ⟨.inl (), rfl⟩ := rfl
example : sampleGen.1.2.1 ⟨.inl false, rfl⟩ = false := rfl

-- The fibre element: the level-`1` shape over it, with its assignment.
example : sampleGen.2.1.1 = ⟨.inr (), rfl⟩ := rfl
example : (sampleGen.2.2.1 ⟨.inr true, rfl⟩).1 = (0 : Fin 3) := rfl

/-- The element over `not` read through the general isomorphism. -/
def sampleNotGen :=
  (genCodeEquiv (ofSlice p3) (arrowPshBaseCartesian piBool)).total ⟨sampleNot, rfl⟩

-- Its base assignment is `not`.
example : sampleNotGen.1.2.1 ⟨.inl true, rfl⟩ = false := rfl
example : sampleNotGen.1.2.1 ⟨.inl false, rfl⟩ = true := rfl

-- The isomorphism commutes with the restriction: the level-`0` element below
-- is the image of the restriction.
example : (genCodeEquiv (ofSlice p3) (arrowPshBaseCartesian piBool)).base
    (((arrowPsh piBool).objPresheaf (ofSlice p3)).map waHom.op ⟨sampleNot, rfl⟩) =
      sampleNotGen.1 :=
  ((genCodeEquiv (ofSlice p3) (arrowPshBaseCartesian piBool)).map_total ⟨sampleNot, rfl⟩).symm

end LargeIRTest
