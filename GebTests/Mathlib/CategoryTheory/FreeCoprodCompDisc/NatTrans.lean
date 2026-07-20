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
to inspect.

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
