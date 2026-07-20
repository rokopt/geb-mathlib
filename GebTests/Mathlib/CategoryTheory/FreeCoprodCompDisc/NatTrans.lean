/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FreeCoprodCompDisc.NatTrans

/-!
# Tests for natural transformations between completion maps

The identity and doubling object maps over `Bool`, with their
morphism maps and functor-law witnesses, exercise the
transformation space: the identity transformation, a non-identity
left-injection transformation, and the vertical category laws at
both. Named theorems give the `GebMeta` axiom linter declarations
to inspect. Whiskering, horizontal composition, and the coherence
and interchange laws are exercised at the sample transformations.
The identity isomorphism family packages into an inverse pair of
transformations; the transport equivalences, the source-map
rewrite, and the coproduct decomposition round-trip sample
transformations.

## Tags

free coproduct completion, natural transformation
-/

@[expose] public section

open CategoryTheory

/-- The identity object map on the completion over `Bool`. -/
def sampleMap : FreeCoprodCompDisc.Map.{0, 0, 0} Bool Bool :=
  fun X ↦ X

/-- The identity morphism map over `sampleMap`. -/
def sampleMapMor : FreeCoprodCompDisc.MapMor Bool Bool sampleMap :=
  fun _ _ h ↦ h

/-- `sampleMapMor` preserves identities. -/
theorem sampleMapMor_preservesId :
    FreeCoprodCompDisc.PreservesId sampleMap sampleMapMor :=
  fun _ ↦ rfl

/-- `sampleMapMor` preserves composition. -/
theorem sampleMapMor_preservesComp :
    FreeCoprodCompDisc.PreservesComp sampleMap sampleMapMor :=
  fun _ _ _ _ _ ↦ rfl

/-- A non-identity object map: the binary coproduct of the argument
with itself. -/
def sampleMapDouble : FreeCoprodCompDisc.Map.{0, 0, 0} Bool Bool :=
  fun X ↦ FreeCoprodCompDisc.coprodPair Bool X X

/-- The morphism map of `sampleMapDouble`, from `coprodPairMor`. -/
def sampleMapDoubleMor :
    FreeCoprodCompDisc.MapMor Bool Bool sampleMapDouble :=
  fun _ _ h ↦ FreeCoprodCompDisc.coprodPairMor Bool h h

/-- `sampleMapDoubleMor` preserves identities. -/
theorem sampleMapDoubleMor_preservesId :
    FreeCoprodCompDisc.PreservesId sampleMapDouble sampleMapDoubleMor :=
  fun X ↦ FreeCoprodCompDisc.coprodPairMor_id Bool X X

/-- `sampleMapDoubleMor` preserves composition. -/
theorem sampleMapDoubleMor_preservesComp :
    FreeCoprodCompDisc.PreservesComp sampleMapDouble sampleMapDoubleMor :=
  fun _ _ _ f g ↦ FreeCoprodCompDisc.coprodPairMor_comp Bool f g f g

/-- The identity natural transformation on the identity map. -/
def sampleNatId :
    FreeCoprodCompDisc.NatTrans Bool Bool sampleMap sampleMap
      sampleMapMor sampleMapMor :=
  FreeCoprodCompDisc.NatTrans.id sampleMap sampleMapMor

/-- A non-identity natural transformation: the left injection into the
doubled map. -/
def sampleNatInl :
    FreeCoprodCompDisc.NatTrans Bool Bool sampleMap sampleMapDouble
      sampleMapMor sampleMapDoubleMor :=
  ⟨fun X ↦ FreeCoprodCompDisc.coprodPairInl Bool X X,
    fun _ _ _ ↦ Subtype.ext rfl⟩

/-- Vertical left identity at the sample transformation. -/
theorem sampleNatInl_id_vcomp :
    FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatInl =
      sampleNatInl :=
  FreeCoprodCompDisc.NatTrans.id_vcomp sampleNatInl

/-- Vertical right identity at the sample transformation. -/
theorem sampleNatInl_vcomp_id :
    FreeCoprodCompDisc.NatTrans.vcomp sampleNatInl
        (FreeCoprodCompDisc.NatTrans.id sampleMapDouble sampleMapDoubleMor) =
      sampleNatInl :=
  FreeCoprodCompDisc.NatTrans.vcomp_id sampleNatInl

/-- Vertical associativity at the sample transformations. -/
theorem sampleNat_vcomp_assoc :
    FreeCoprodCompDisc.NatTrans.vcomp
        (FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatId)
        sampleNatInl =
      FreeCoprodCompDisc.NatTrans.vcomp sampleNatId
        (FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatInl) :=
  FreeCoprodCompDisc.NatTrans.vcomp_assoc sampleNatId sampleNatId sampleNatInl

/-- The composite of the identity map with itself. -/
def sampleMapComp : FreeCoprodCompDisc.Map.{0, 0, 0} Bool Bool :=
  FreeCoprodCompDisc.mapComp sampleMap sampleMap

/-- The composite morphism map over `sampleMapComp`. -/
def sampleMapCompMor : FreeCoprodCompDisc.MapMor Bool Bool sampleMapComp :=
  FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapMor

/-- Right whiskering of the sample transformation by the identity
map. -/
def sampleWhiskerRight :
    FreeCoprodCompDisc.NatTrans Bool Bool
      (FreeCoprodCompDisc.mapComp sampleMap sampleMap)
      (FreeCoprodCompDisc.mapComp sampleMap sampleMapDouble)
      (FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapMor)
      (FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapDoubleMor) :=
  FreeCoprodCompDisc.NatTrans.whiskerRight sampleMap sampleMapMor sampleNatInl

/-- Left whiskering of the sample transformation by the identity map. -/
def sampleWhiskerLeft :
    FreeCoprodCompDisc.NatTrans Bool Bool
      (FreeCoprodCompDisc.mapComp sampleMap sampleMap)
      (FreeCoprodCompDisc.mapComp sampleMapDouble sampleMap)
      (FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapMor)
      (FreeCoprodCompDisc.mapMorComp sampleMapDoubleMor sampleMapMor) :=
  FreeCoprodCompDisc.NatTrans.whiskerLeft sampleNatInl sampleMap sampleMapMor
    sampleMapMor_preservesComp

/-- The two orientations of the horizontal composite agree at the
sample transformations. -/
theorem sampleHcomp_eq_vcomp_whisker :
    FreeCoprodCompDisc.NatTrans.hcomp sampleNatInl sampleNatInl
        sampleMapMor_preservesComp =
      FreeCoprodCompDisc.NatTrans.vcomp
        (FreeCoprodCompDisc.NatTrans.whiskerRight sampleMap sampleMapMor
          sampleNatInl)
        (FreeCoprodCompDisc.NatTrans.whiskerLeft sampleNatInl sampleMapDouble
          sampleMapDoubleMor sampleMapDoubleMor_preservesComp) :=
  FreeCoprodCompDisc.NatTrans.hcomp_eq_vcomp_whisker sampleNatInl sampleNatInl
    sampleMapMor_preservesComp sampleMapDoubleMor_preservesComp

/-- The horizontal composite of identity transformations is the
identity. -/
theorem sampleHcomp_id :
    FreeCoprodCompDisc.NatTrans.hcomp sampleNatId sampleNatId
        sampleMapMor_preservesComp =
      FreeCoprodCompDisc.NatTrans.id
        (FreeCoprodCompDisc.mapComp sampleMap sampleMap)
        (FreeCoprodCompDisc.mapMorComp sampleMapMor sampleMapMor) :=
  FreeCoprodCompDisc.NatTrans.hcomp_id sampleMapMor_preservesComp
    sampleMapMor_preservesId

/-- The interchange law at the sample transformations. -/
theorem sampleHcomp_vcomp :
    FreeCoprodCompDisc.NatTrans.hcomp
        (FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatInl)
        (FreeCoprodCompDisc.NatTrans.vcomp sampleNatId sampleNatInl)
        sampleMapMor_preservesComp =
      FreeCoprodCompDisc.NatTrans.vcomp
        (FreeCoprodCompDisc.NatTrans.hcomp sampleNatId sampleNatId
          sampleMapMor_preservesComp)
        (FreeCoprodCompDisc.NatTrans.hcomp sampleNatInl sampleNatInl
          sampleMapMor_preservesComp) :=
  FreeCoprodCompDisc.NatTrans.hcomp_vcomp sampleNatId sampleNatInl
    sampleNatId sampleNatInl sampleMapMor_preservesComp
    sampleMapMor_preservesComp

/-- Right whiskering by the identity object map is the identity
operation at the sample transformation. -/
theorem sampleWhiskerRight_idMap :
    FreeCoprodCompDisc.NatTrans.whiskerRight FreeCoprodCompDisc.idMap
        FreeCoprodCompDisc.idMapMor sampleNatInl =
      sampleNatInl :=
  FreeCoprodCompDisc.NatTrans.whiskerRight_idMap sampleNatInl

/-- Left whiskering by the identity object map is the identity
operation at the sample transformation. -/
theorem sampleWhiskerLeft_idMap :
    FreeCoprodCompDisc.NatTrans.whiskerLeft sampleNatInl
        FreeCoprodCompDisc.idMap FreeCoprodCompDisc.idMapMor
        FreeCoprodCompDisc.idMapMor_preservesComp =
      sampleNatInl :=
  FreeCoprodCompDisc.NatTrans.whiskerLeft_idMap sampleNatInl

/-- The identity isomorphism family on the identity map is natural. -/
theorem sampleIsoFamily_isNatTrans :
    FreeCoprodCompDisc.IsNatTrans Bool Bool sampleMap sampleMap
      sampleMapMor sampleMapMor
      (fun X ↦ FreeCoprodCompDisc.Iso.hom Bool
        (FreeCoprodCompDisc.Iso.refl Bool X)) :=
  fun _ _ _ ↦ Subtype.ext rfl

/-- The transformation packaged from the identity isomorphism family. -/
def sampleOfIsoFamily :
    FreeCoprodCompDisc.NatTrans Bool Bool sampleMap sampleMap
      sampleMapMor sampleMapMor :=
  FreeCoprodCompDisc.NatTrans.ofIsoFamily
    (fun X ↦ FreeCoprodCompDisc.Iso.refl Bool X) sampleIsoFamily_isNatTrans

/-- The inverse transformation packaged from the identity isomorphism
family. -/
def sampleInvOfIsoFamily :
    FreeCoprodCompDisc.NatTrans Bool Bool sampleMap sampleMap
      sampleMapMor sampleMapMor :=
  FreeCoprodCompDisc.NatTrans.invOfIsoFamily
    (fun X ↦ FreeCoprodCompDisc.Iso.refl Bool X) sampleIsoFamily_isNatTrans

/-- The two packaged transformations are inverse. -/
theorem sampleOfIsoFamily_isInverse :
    FreeCoprodCompDisc.NatTrans.IsInverse sampleOfIsoFamily
      sampleInvOfIsoFamily :=
  FreeCoprodCompDisc.NatTrans.ofIsoFamily_isInverse
    (fun X ↦ FreeCoprodCompDisc.Iso.refl Bool X) sampleIsoFamily_isNatTrans

/-- Postcomposition with the sample inverse pair round-trips a
transformation. -/
theorem sampleEquivOfInverseTarget_roundtrip :
    (FreeCoprodCompDisc.NatTrans.equivOfInverseTarget sampleOfIsoFamily
          sampleInvOfIsoFamily sampleOfIsoFamily_isInverse).symm
        ((FreeCoprodCompDisc.NatTrans.equivOfInverseTarget sampleOfIsoFamily
          sampleInvOfIsoFamily sampleOfIsoFamily_isInverse) sampleNatId) =
      sampleNatId :=
  (FreeCoprodCompDisc.NatTrans.equivOfInverseTarget sampleOfIsoFamily
    sampleInvOfIsoFamily sampleOfIsoFamily_isInverse).symm_apply_apply
    sampleNatId

/-- Rewriting the source morphism map along reflexivity is the
identity. -/
theorem sampleCongrSource_apply :
    FreeCoprodCompDisc.NatTrans.congrSource
        (rfl : sampleMapMor = sampleMapMor) sampleMapDoubleMor sampleNatInl =
      sampleNatInl :=
  rfl

/-- The coproduct decomposition round-trips a family of
transformations. -/
theorem sampleNatCoprodEquiv_roundtrip :
    (FreeCoprodCompDisc.natCoprodEquiv Bool (fun _ ↦ sampleMap)
        (fun _ ↦ sampleMapMor) sampleMapDouble sampleMapDoubleMor)
        ((FreeCoprodCompDisc.natCoprodEquiv Bool (fun _ ↦ sampleMap)
          (fun _ ↦ sampleMapMor) sampleMapDouble sampleMapDoubleMor).symm
          (fun _ ↦ sampleNatInl)) =
      fun _ ↦ sampleNatInl :=
  (FreeCoprodCompDisc.natCoprodEquiv Bool (fun _ ↦ sampleMap)
    (fun _ ↦ sampleMapMor) sampleMapDouble
    sampleMapDoubleMor).apply_symm_apply (fun _ ↦ sampleNatInl)
