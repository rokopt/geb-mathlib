/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Mono

/-!
# Tests for the monomorphisms of `FinSetSkel`

A sample morphism of the two-element into the three-element object,
the decision that its vector is injective, and the monomorphism it
therefore is.

## Tags

category, finite set, skeleton, monomorphism, injective
-/

@[expose] public section

open CategoryTheory FinSetSkel

/-- A sample injective morphism. -/
def sampleSkelInj : (mk 2 : FinSetSkel.{0}) ⟶ mk 3 :=
  Hom.ofVec (Vector.ofFnC fun i : Fin 2 ↦ (⟨i.val, by omega⟩ : Fin 3))

/-- Its vector is injective, decided at `Fin 2`. -/
theorem sampleSkelInj_injective : Function.Injective sampleSkelInj.toVec.get := by
  intro i j hij
  revert hij
  revert i j
  decide

/-- The sample morphism is therefore a monomorphism. -/
theorem sampleSkelInj_mono : Mono sampleSkelInj :=
  mono_iff_injective.mpr sampleSkelInj_injective
