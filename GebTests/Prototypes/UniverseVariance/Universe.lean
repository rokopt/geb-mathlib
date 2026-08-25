/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.UniverseVariance.Universe

/-!
# Tests for the two universe examples over the split-epimorphism base

A morphism of families whose embedding-projection pair is not invertible, and
the two universes' morphism maps computed at it. The dependent-product map is
the one Example 3.6 of [GhaniNordvallForsbergMalatesta2015] shows cannot be
given over `Set`.

## Tags

prototype, universe, variance, embedding-projection pair, reduction test
-/

set_option linter.privateModule false

open GebProto.UniverseVariance

/-! ## A morphism of families that is not invertible -/

/-- One code, decoding to the singleton. -/
def famUnit : Fam where
  Code := Unit
  dec _ := Unit

/-- One code, decoding to the booleans. -/
def famBool : Fam where
  Code := Unit
  dec _ := Bool

/-- The embedding-projection pair sending the singleton to `true`. Its embedding
is not surjective, so it is not an isomorphism. -/
def epUnitBool : FamHom famUnit famBool where
  code := id
  ep _ :=
    { toFun := fun _ ↦ ()
      sect := fun _ ↦ true
      toFun_sect := fun _ ↦ rfl }

example : ¬ Function.Surjective (epUnitBool.emb ()) :=
  fun h ↦ (h false).elim fun _ hx ↦ Bool.noConfusion hx

/-- The binder code at the single code of `famUnit`. -/
def unitBinder : UnivCode famUnit := .inr ⟨(), fun _ ↦ ()⟩

/-! ## The dependent-product universe

Its embedding evaluates the given section family at the projection; its
projection runs the reindexing backwards along the embedding. -/

example : (piUnivHom Nat epUnitBool).code unitBinder = .inr ⟨(), fun _ ↦ ()⟩ := rfl

-- The embedded section is defined at every element of the larger decoding,
-- including the one outside the image of the embedding.
example : (piUnivHom Nat epUnitBool).emb unitBinder (fun _ ↦ ()) false = true := rfl
example : (piUnivHom Nat epUnitBool).emb unitBinder (fun _ ↦ ()) true = true := rfl

/-! ## The dependent-sum universe -/

example : (sigmaUnivHom Nat epUnitBool).emb unitBinder ⟨(), ()⟩ = ⟨true, true⟩ := rfl

example : (sigmaUnivHom Nat epUnitBool).proj unitBinder ⟨false, false⟩ = ⟨(), ()⟩ := rfl

/-! ## Functoriality of the action on codes -/

example : univCodeMap (FamHom.id famUnit) unitBinder = unitBinder :=
  congrFun (univCodeMap_id famUnit) unitBinder

example : univCodeMap (epUnitBool.comp (FamHom.id famBool)) unitBinder
    = univCodeMap (FamHom.id famBool) (univCodeMap epUnitBool unitBinder) :=
  congrFun (univCodeMap_comp epUnitBool (FamHom.id famBool)) unitBinder
