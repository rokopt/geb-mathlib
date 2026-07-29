/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Skeleton

/-!
# Tests for the skeleton comparison

The comparison functors agree on a sample object, and the isomorphism
in `Cat` has the comparison functors as its components.

## Tags

category, skeleton
-/

@[expose] public section

open CategoryTheory

/-- The comparison functors are mutually inverse on a sample object. -/
theorem sampleObj_roundtrip :
    FinSetSkel.ofSkeleton.obj (FinSetSkel.toSkeleton.obj ⟨4⟩) =
      (⟨4⟩ : FinSetSkel.{0}) :=
  rfl

/-- The isomorphism's forward component is the comparison functor. -/
theorem sampleCatIso_hom :
    FinSetSkel.catIso.{0}.hom = FinSetSkel.toSkeleton.toCatHom :=
  rfl

/-- A sample domain object for the morphism-level round trip below. -/
def sampleMorDom : FinSetSkel.{0} := ⟨3⟩

/-- A sample codomain object for the morphism-level round trip below. -/
def sampleMorCod : FinSetSkel.{0} := ⟨2⟩

/-- A sample morphism, exercising the comparison functors' action on
morphisms rather than only on objects. -/
def sampleMor : sampleMorDom ⟶ sampleMorCod :=
  FinSetSkel.Hom.ofVec (Vector.ofFnC (fun i ↦ ⟨i.1 % 2, Nat.mod_lt _ (by decide)⟩))

/-- The comparison functors are mutually inverse on a sample morphism. -/
theorem sampleMor_toSkeleton_ofSkeleton_roundtrip :
    FinSetSkel.ofSkeleton.map (FinSetSkel.toSkeleton.map sampleMor) = sampleMor :=
  rfl
