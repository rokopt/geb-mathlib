/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Classifier.Core

/-!
# Tests for the subobject-classifier core of `FinSetSkel`

A monomorphism of the two-element into the four-element object, its
characteristic vector, and the factorisation through it of a morphism
whose image it contains.

## Tags

category, finite set, skeleton, subobject classifier
-/

@[expose] public section

open CategoryTheory FinSetSkel

/-- A sample monomorphism of the two-element into the four-element
object, with image the indices `1` and `3`. -/
def sampleSkelMono : (mk 2 : FinSetSkel.{0}) ⟶ mk 4 :=
  Hom.ofVec (⟨#[1, 3], rfl⟩ : Vector (Fin 4) 2)

/-- Its vector is injective, decided at `Fin 2`. -/
theorem sampleSkelMono_injective : Function.Injective sampleSkelMono.toVec.get := by
  intro i j hij
  revert hij
  revert i j
  decide

/-- The characteristic vector of the sample monomorphism. -/
def sampleSkelChiVec : Vector (Fin 2) 4 := Classifier.chiVec sampleSkelMono

/-- It is the indicator of the image. -/
theorem sampleSkelChiVec_eq : sampleSkelChiVec = ⟨#[0, 1, 0, 1], rfl⟩ := rfl

/-- A sample morphism of the three-element object whose image the
sample monomorphism contains. -/
def sampleSkelChiSection : (mk 3 : FinSetSkel.{0}) ⟶ mk 4 :=
  Hom.ofVec (⟨#[3, 1, 3], rfl⟩ : Vector (Fin 4) 3)

/-- Every value of the sample morphism lies in the monomorphism's
image, read off the characteristic vector. -/
theorem sampleSkelChiSection_mem (t : Fin 3) :
    sampleSkelChiSection.toVec.get t ∈ sampleSkelMono.toVec.toList :=
  (Classifier.chiVec_get_eq_one_iff sampleSkelMono _).mp (by revert t; decide)

/-- The sample morphism's factorisation through the monomorphism
recovers it. -/
theorem sampleSkelPullbackLift_comp :
    Classifier.pullbackLift sampleSkelMono sampleSkelMono_injective
        sampleSkelChiSection sampleSkelChiSection_mem ≫ sampleSkelMono =
      sampleSkelChiSection :=
  Classifier.pullbackLift_comp _ _ _ _

