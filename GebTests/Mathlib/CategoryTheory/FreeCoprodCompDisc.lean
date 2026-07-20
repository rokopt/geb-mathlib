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
