/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc

/-!
# Tests for the free coproduct completion

A sample object and endomorphism exercise `FreeCoprodCompDisc.Hom.comp`,
checking that composing the sample endomorphism with itself returns
the same endomorphism.

A binary coproduct across index universes exercises the injections
and the cotuple `coprodPairDesc` (via `coprodPair_inl_desc`). A sample
isomorphism between an object and its `ULift` renaming exercises the
`Iso` family, checking that a round trip through `Iso.trans` and
`Iso.symm` is the identity. A sample copower exercises `copower` and
the inverse direction of `copowerEquiv`. A sample lifted object
exercises `lift` and `homLiftEquiv`.

The identity morphism and the category laws are exercised at the
sample endomorphism; the functoriality of `coprodMor` at constant
families over the sample object; composition and the identity laws
additionally across three distinct objects with non-identity
morphisms, pinning composition order by type.

The initial object, the indexed-coproduct universal property,
`coprodPairMor`, the singleton fiber description, and the
underlying morphisms of isomorphisms are exercised at the sample
objects. The coproduct-pair injections are exercised across two
index universes.

## Tags

free coproduct completion, family, discrete category
-/

@[expose] public section

open CategoryTheory

/-- A sample object: two names decoding into `Bool` by the
identity assignment. -/
def sampleX : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨Bool, id⟩

/-- A sample endomorphism of `sampleX`: the identity index
function, a hom because the decodings agree definitionally. -/
def sampleHom : FreeCoprodCompDisc.Hom Bool sampleX sampleX :=
  ⟨id, rfl⟩

/-- Composition of the sample endomorphism with itself is
itself. -/
theorem sampleHom_comp :
    FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom = sampleHom :=
  Subtype.ext rfl

/-- A binary coproduct across index universes. -/
def samplePair : FreeCoprodCompDisc.{1, 0} Bool :=
  FreeCoprodCompDisc.coprodPair Bool ⟨PUnit.{2}, fun _ ↦ true⟩ sampleX

/-- The left name of `samplePair` decodes through the left
component. -/
theorem samplePair_inl_decode :
    samplePair.2 (Sum.inl PUnit.unit) = true :=
  rfl

/-- The cotuple restricted along the left injection is the left
component. -/
theorem sample_inl_desc :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.coprodPairInl Bool sampleX sampleX)
        (FreeCoprodCompDisc.coprodPairDesc Bool sampleHom sampleHom) =
      sampleHom :=
  FreeCoprodCompDisc.coprodPair_inl_desc Bool sampleX sampleX sampleX sampleHom sampleHom

/-- A renamed copy of `sampleX`: lifted names, the same
decodings. -/
def sampleXLift : FreeCoprodCompDisc.{1, 0} Bool :=
  ⟨ULift.{1} Bool, id ∘ ULift.down⟩

/-- A sample isomorphism: the `ULift` renaming commutes with the
decodings. -/
def sampleIso : FreeCoprodCompDisc.Iso.{0, 1, 0} Bool sampleXLift sampleX :=
  ⟨Equiv.ulift.{1, 0}, rfl⟩

/-- Round-tripping a name through the sample isomorphism and its
inverse is the identity. -/
theorem sampleIso_symm_trans_apply :
    (FreeCoprodCompDisc.Iso.trans Bool sampleIso
      (FreeCoprodCompDisc.Iso.symm Bool sampleIso)).1 (ULift.up true) =
      ULift.up true :=
  rfl

/-- The copower of `sampleX` by `Bool`: names are pairs
decoding through the second component. -/
def sampleCopower : FreeCoprodCompDisc.{0, 0} Bool :=
  FreeCoprodCompDisc.copower.{0, 0, 0} Bool Bool sampleX

/-- A copower name decodes through its second component. -/
theorem sampleCopower_decode : sampleCopower.2 ⟨true, false⟩ = false :=
  rfl

/-- The copower cotuple evaluates componentwise: the inverse
direction of `copowerEquiv` at a constant family applies the
component morphism. -/
theorem sampleCopower_desc_apply (b : Bool) :
    ((FreeCoprodCompDisc.copowerEquiv.{0, 0, 0} Bool Bool
      sampleX sampleX).symm (fun _ ↦ sampleHom)).1 ⟨true, b⟩ = b :=
  rfl

/-- A lifted object decodes through `ULift.down`. -/
theorem sampleLift_decode :
    (FreeCoprodCompDisc.lift.{0, 0, 1} Bool sampleX).2 (ULift.up true) =
      true :=
  rfl

/-- `homLiftEquiv` strips the lift from a morphism's domain:
applying the image of the identity index function evaluates by
`ULift.up`. -/
theorem sampleHomLift_apply :
    ((FreeCoprodCompDisc.homLiftEquiv.{0, 0, 1} Bool sampleX
        (FreeCoprodCompDisc.lift.{0, 0, 1} Bool sampleX))
      ⟨_root_.id, rfl⟩).1 true = ULift.up true :=
  rfl

/-- The identity morphism of `sampleX` is the sample endomorphism. -/
theorem sampleHom_id :
    FreeCoprodCompDisc.Hom.id Bool sampleX = sampleHom :=
  Subtype.ext rfl

/-- Left identity at the sample endomorphism. -/
theorem sampleHom_id_comp :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.Hom.id Bool sampleX) sampleHom =
      sampleHom :=
  FreeCoprodCompDisc.Hom.id_comp Bool sampleHom

/-- Right identity at the sample endomorphism. -/
theorem sampleHom_comp_id :
    FreeCoprodCompDisc.Hom.comp Bool sampleHom
        (FreeCoprodCompDisc.Hom.id Bool sampleX) =
      sampleHom :=
  FreeCoprodCompDisc.Hom.comp_id Bool sampleHom

/-- Associativity at the sample endomorphism. -/
theorem sampleHom_comp_assoc :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom)
        sampleHom =
      FreeCoprodCompDisc.Hom.comp Bool sampleHom
        (FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom) :=
  FreeCoprodCompDisc.Hom.comp_assoc Bool sampleHom sampleHom sampleHom

/-- The identity-family coproduct morphism over a constant family is
the identity. -/
theorem sampleCoprodMor_id :
    FreeCoprodCompDisc.coprodMor Bool PUnit PUnit _root_.id
        (fun _ ↦ sampleX) (fun _ ↦ sampleX)
        (fun _ ↦ FreeCoprodCompDisc.Hom.id Bool sampleX) =
      FreeCoprodCompDisc.Hom.id Bool
        (FreeCoprodCompDisc.coprod Bool PUnit (fun _ ↦ sampleX)) :=
  FreeCoprodCompDisc.coprodMor_id Bool PUnit (fun _ ↦ sampleX)

/-- Composition of identity-reindexed coproduct morphisms composes
componentwise. -/
theorem sampleCoprodMor_comp :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.coprodMor Bool PUnit PUnit _root_.id
          (fun _ ↦ sampleX) (fun _ ↦ sampleX) (fun _ ↦ sampleHom))
        (FreeCoprodCompDisc.coprodMor Bool PUnit PUnit _root_.id
          (fun _ ↦ sampleX) (fun _ ↦ sampleX) (fun _ ↦ sampleHom)) =
      FreeCoprodCompDisc.coprodMor Bool PUnit PUnit
        (_root_.id ∘ _root_.id) (fun _ ↦ sampleX) (fun _ ↦ sampleX)
        (fun _ ↦ FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleHom) :=
  FreeCoprodCompDisc.coprodMor_comp Bool PUnit PUnit PUnit
    _root_.id _root_.id (fun _ ↦ sampleX) (fun _ ↦ sampleX)
    (fun _ ↦ sampleX) (fun _ ↦ sampleHom) (fun _ ↦ sampleHom)

/-- A sample object distinct from `sampleX`: a single name decoding
to `true`. -/
def sampleW : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨PUnit, fun _ ↦ true⟩

/-- A sample object distinct from both `sampleW` and `sampleX`: names
from `Bool ⊕ PUnit`, the left summand decoding by the identity and the
right summand decoding to `true`. -/
def sampleZ : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨Bool ⊕ PUnit, Sum.elim id (fun _ ↦ true)⟩

/-- A non-identity morphism from `sampleW` to `sampleX`. -/
def sampleWtoX : FreeCoprodCompDisc.Hom Bool sampleW sampleX :=
  ⟨fun _ ↦ true, rfl⟩

/-- A non-identity morphism from `sampleX` to `sampleZ`. -/
def sampleXtoZ : FreeCoprodCompDisc.Hom Bool sampleX sampleZ :=
  ⟨Sum.inl, rfl⟩

/-- The composite of `sampleWtoX` and `sampleXtoZ`. -/
def sampleWtoZ : FreeCoprodCompDisc.Hom Bool sampleW sampleZ :=
  ⟨fun _ ↦ Sum.inl true, rfl⟩

/-- Composition across three distinct objects: the composite of
`sampleWtoX` and `sampleXtoZ` is `sampleWtoZ`, pinning composition
order by the distinct types of `sampleW`, `sampleX`, and `sampleZ`. -/
theorem sampleWtoX_comp_sampleXtoZ :
    FreeCoprodCompDisc.Hom.comp Bool sampleWtoX sampleXtoZ = sampleWtoZ :=
  Subtype.ext rfl

/-- Left identity at the non-identity morphism `sampleWtoX`. -/
theorem sampleWtoX_id_comp :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.Hom.id Bool sampleW) sampleWtoX =
      sampleWtoX :=
  FreeCoprodCompDisc.Hom.id_comp Bool sampleWtoX

/-- Right identity at the non-identity morphism `sampleWtoX`. -/
theorem sampleWtoX_comp_id :
    FreeCoprodCompDisc.Hom.comp Bool sampleWtoX
        (FreeCoprodCompDisc.Hom.id Bool sampleX) =
      sampleWtoX :=
  FreeCoprodCompDisc.Hom.comp_id Bool sampleWtoX

/-- Uniqueness of the morphism out of the initial object at `sampleX`. -/
theorem sampleEmptyDesc_unique
    (f : FreeCoprodCompDisc.Hom Bool (FreeCoprodCompDisc.emptyObj Bool) sampleX) :
    f = FreeCoprodCompDisc.emptyDesc Bool sampleX :=
  FreeCoprodCompDisc.emptyDesc_unique Bool sampleX f

/-- Restricting the cotuple along an injection recovers the component. -/
theorem sampleCoprodInj_desc (b : Bool) :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.coprodInj Bool Bool (fun _ ↦ sampleX) b)
        (FreeCoprodCompDisc.coprodDesc Bool Bool (fun _ ↦ sampleX) sampleX
          (fun _ ↦ sampleHom)) =
      sampleHom :=
  FreeCoprodCompDisc.coprodInj_desc Bool Bool (fun _ ↦ sampleX) sampleX
    (fun _ ↦ sampleHom) b

/-- The inverse direction of the coproduct universal property evaluates
componentwise. -/
theorem sampleCoprodHomEquiv_symm_apply :
    ((FreeCoprodCompDisc.coprodHomEquiv Bool Bool (fun _ ↦ sampleX)
        sampleX).symm (fun _ ↦ sampleHom)).1 ⟨true, false⟩ = false :=
  rfl

/-- A cotuple followed by a morphism is the cotuple of the composites. -/
theorem sampleCoprodDesc_comp :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.coprodDesc Bool Bool (fun _ ↦ sampleX) sampleX
          (fun _ ↦ sampleHom))
        sampleXtoZ =
      FreeCoprodCompDisc.coprodDesc Bool Bool (fun _ ↦ sampleX) sampleZ
        (fun _ ↦ FreeCoprodCompDisc.Hom.comp Bool sampleHom sampleXtoZ) :=
  FreeCoprodCompDisc.coprodDesc_comp Bool Bool (fun _ ↦ sampleX) sampleX
    sampleZ (fun _ ↦ sampleHom) sampleXtoZ

/-- `coprodPairMor` preserves identities at the sample objects. -/
theorem sampleCoprodPairMor_id :
    FreeCoprodCompDisc.coprodPairMor Bool
        (FreeCoprodCompDisc.Hom.id Bool sampleW)
        (FreeCoprodCompDisc.Hom.id Bool sampleX) =
      FreeCoprodCompDisc.Hom.id Bool
        (FreeCoprodCompDisc.coprodPair Bool sampleW sampleX) :=
  FreeCoprodCompDisc.coprodPairMor_id Bool sampleW sampleX

/-- `coprodPairMor` preserves composition at the sample morphisms. -/
theorem sampleCoprodPairMor_comp :
    FreeCoprodCompDisc.coprodPairMor Bool
        (FreeCoprodCompDisc.Hom.comp Bool sampleWtoX sampleXtoZ)
        (FreeCoprodCompDisc.Hom.comp Bool sampleWtoX sampleXtoZ) =
      FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.coprodPairMor Bool sampleWtoX sampleWtoX)
        (FreeCoprodCompDisc.coprodPairMor Bool sampleXtoZ sampleXtoZ) :=
  FreeCoprodCompDisc.coprodPairMor_comp Bool sampleWtoX sampleXtoZ
    sampleWtoX sampleXtoZ

/-- Reindexing along the right injection then cotupling the left
injection against the identity is the identity. -/
theorem sampleCoprodPairMor_inr_desc_inl :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.coprodPairMor Bool
          (FreeCoprodCompDisc.Hom.id Bool sampleW)
          (FreeCoprodCompDisc.coprodPairInr Bool sampleW sampleX))
        (FreeCoprodCompDisc.coprodPairDesc Bool
          (FreeCoprodCompDisc.coprodPairInl Bool sampleW sampleX)
          (FreeCoprodCompDisc.Hom.id Bool
            (FreeCoprodCompDisc.coprodPair.{0, 0, 0} Bool sampleW sampleX))) =
      FreeCoprodCompDisc.Hom.id Bool
        (FreeCoprodCompDisc.coprodPair.{0, 0, 0} Bool sampleW sampleX) :=
  FreeCoprodCompDisc.coprodPairMor_inr_desc_inl Bool

/-- The singleton fiber description evaluates its inverse direction at a
fiber element. -/
theorem sampleHomSingletonEquiv_symm_apply :
    ((FreeCoprodCompDisc.homSingletonEquiv Bool true sampleX).symm
        ⟨true, rfl⟩).1 (ULift.up Unit.unit) = true :=
  rfl

/-- A sample object with constant decoding, carrying a non-identity
isomorphism. -/
def sampleC : FreeCoprodCompDisc.{0, 0} Bool :=
  ⟨Bool, fun _ ↦ true⟩

/-- A sample non-identity isomorphism: Boolean negation on `sampleC`. -/
def sampleIsoNot : FreeCoprodCompDisc.Iso.{0, 0, 0} Bool sampleC sampleC :=
  ⟨⟨Bool.not, Bool.not, Bool.not_not, Bool.not_not⟩, rfl⟩

/-- The underlying morphisms of the sample isomorphism compose to the
identity. -/
theorem sampleIsoNot_hom_invHom :
    FreeCoprodCompDisc.Hom.comp Bool
        (FreeCoprodCompDisc.Iso.hom Bool sampleIsoNot)
        (FreeCoprodCompDisc.Iso.invHom Bool sampleIsoNot) =
      FreeCoprodCompDisc.Hom.id Bool sampleC :=
  FreeCoprodCompDisc.Iso.hom_invHom Bool sampleIsoNot

/-- The left injection into a coproduct pair whose summands sit at
different index universes. -/
theorem sampleCoprodPairInl_hetero_apply :
    (FreeCoprodCompDisc.coprodPairInl.{0, 0, 1} Bool sampleX sampleXLift).1
        true =
      Sum.inl true :=
  rfl

/-- The right injection into a coproduct pair whose summands sit at
different index universes. -/
theorem sampleCoprodPairInr_hetero_apply :
    (FreeCoprodCompDisc.coprodPairInr.{0, 0, 1} Bool sampleX sampleXLift).1
        (ULift.up true) =
      Sum.inr (ULift.up true) :=
  rfl
