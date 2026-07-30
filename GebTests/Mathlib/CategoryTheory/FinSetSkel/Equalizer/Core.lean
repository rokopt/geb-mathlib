/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Equalizer.Core

/-!
# Tests for the equalizer core of `FinSetSkel`

A parallel pair of the five-element into the two-element object
agreeing at three indices, the length of its equalizer, the entries of
the injection, and the factorisation of a sample morphism equalising
the pair.

## Tags

category, finite set, skeleton, equalizer
-/

@[expose] public section

open CategoryTheory FinSetSkel

/-- The left member of a sample parallel pair. -/
def sampleSkelEqualizerLeft : (mk 5 : FinSetSkel.{0}) ⟶ mk 2 :=
  Hom.ofVec (⟨#[0, 1, 0, 1, 0], rfl⟩ : Vector (Fin 2) 5)

/-- The right member of a sample parallel pair; it agrees with the
left member at the indices `0`, `2` and `3`. -/
def sampleSkelEqualizerRight : (mk 5 : FinSetSkel.{0}) ⟶ mk 2 :=
  Hom.ofVec (⟨#[0, 0, 0, 1, 1], rfl⟩ : Vector (Fin 2) 5)

/-- The equalizer of the sample pair has three elements. -/
theorem sampleSkelEqualizerObj_len :
    (Equalizer.obj sampleSkelEqualizerLeft sampleSkelEqualizerRight).len = 3 := by
  decide

/-- The injection of the sample pair's equalizer. -/
def sampleSkelEqualizerInj :
    Equalizer.obj sampleSkelEqualizerLeft sampleSkelEqualizerRight ⟶ mk 5 :=
  Equalizer.ι sampleSkelEqualizerLeft sampleSkelEqualizerRight

/-- The injection lists the agreeing indices in order. -/
theorem sampleSkelEqualizerInj_toList :
    sampleSkelEqualizerInj.toVec.toList = [0, 2, 3] := by
  decide

/-- A sample morphism of the two-element object into the pair's
domain. -/
def sampleSkelEqualizerSection : (mk 2 : FinSetSkel.{0}) ⟶ mk 5 :=
  Hom.ofVec (⟨#[0, 3], rfl⟩ : Vector (Fin 5) 2)

/-- The sample morphism equalises the pair. -/
theorem sampleSkelEqualizerSection_eq :
    sampleSkelEqualizerSection ≫ sampleSkelEqualizerLeft =
      sampleSkelEqualizerSection ≫ sampleSkelEqualizerRight :=
  hom_ext (by decide)

/-- The sample morphism's factorisation through the injection recovers
it. -/
theorem sampleSkelEqualizerLift_ι :
    Equalizer.lift sampleSkelEqualizerLeft sampleSkelEqualizerRight
        sampleSkelEqualizerSection sampleSkelEqualizerSection_eq ≫
      sampleSkelEqualizerInj = sampleSkelEqualizerSection :=
  Equalizer.lift_ι _ _ _ _

/-- The factorisation sends each index to the position of its value in
the agreement list; its entries are read as naturals, the equalizer
object's length not being a literal. -/
theorem sampleSkelEqualizerLift_toList :
    (Equalizer.lift sampleSkelEqualizerLeft sampleSkelEqualizerRight
        sampleSkelEqualizerSection
        sampleSkelEqualizerSection_eq).toVec.toList.map Fin.val = [0, 2] := by
  decide

