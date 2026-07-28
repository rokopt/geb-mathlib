/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic

/-!
# Tests for `FinSetSkel`

Every assertion below but the index-function round trip is a closed
computation: the sample morphisms
reduce to concrete vectors, decidable equality separates two distinct
morphisms rather than merely accepting one, composition with the
identity reduces to the morphism, and `Repr` agrees with the vector's.
A failure to reduce is caught, which is the point of a category whose
morphisms are data.

## Tags

category, finite set, skeleton
-/

@[expose] public section

open CategoryTheory

/-- A sample object. -/
def objThree : FinSetSkel.{0} := ⟨3⟩

/-- A second sample object. -/
def objTwo : FinSetSkel.{0} := ⟨2⟩

/-- A sample morphism collapsing three indices onto two. -/
def sampleSkelHom : objThree ⟶ objTwo :=
  FinSetSkel.Hom.ofVec (Vector.ofFnC (fun i ↦ ⟨i.1 % 2, Nat.mod_lt _ (by decide)⟩))

/-- A second sample morphism, constant at the first index. -/
def constZeroHom : objThree ⟶ objTwo :=
  FinSetSkel.Hom.ofVec (Vector.ofFnC (fun _ ↦ ⟨0, by decide⟩))

/-- A third sample morphism, swapping the two indices of `objTwo`. -/
def swapHom : objTwo ⟶ objTwo :=
  FinSetSkel.Hom.ofVec (Vector.ofFnC (fun i ↦ ⟨(i.1 + 1) % 2, Nat.mod_lt _ (by decide)⟩))

/-- The sample morphism takes a concrete value at a concrete index. -/
theorem sampleSkelHom_value :
    sampleSkelHom.toVec.get ⟨1, by decide⟩ = ⟨1, by decide⟩ := by decide

/-- Decidable equality separates two distinct morphisms. -/
theorem sampleSkelHom_ne_constZero : sampleSkelHom ≠ constZeroHom := fun h ↦ by
  have := congrArg (fun f ↦ (FinSetSkel.Hom.toVec f).get ⟨1, by decide⟩) h
  exact absurd this (by decide)

/-- Composition with the identity reduces to the morphism. -/
theorem constZeroHom_comp_id : constZeroHom ≫ 𝟙 objTwo = constZeroHom := rfl

/-- Composition with the identity preserves the underlying vector. -/
theorem sampleSkelHom_comp_id_toVec :
    (sampleSkelHom ≫ 𝟙 objTwo).toVec = sampleSkelHom.toVec := rfl

/-- `Repr` on a morphism is `Repr` on its vector. -/
theorem sampleSkelHom_repr :
    reprStr sampleSkelHom = reprStr sampleSkelHom.toVec := rfl

/-- The index-function correspondence round-trips the sample. -/
theorem sampleSkelHom_idxFun_roundtrip :
    FinSetSkel.ofIdxFun (FinSetSkel.toIdxFun sampleSkelHom) = sampleSkelHom :=
  FinSetSkel.ofIdxFun_toIdxFun sampleSkelHom

/-- The lifted index function of the sample morphism takes a concrete
value at a concrete lifted index. -/
theorem sampleSkelHom_toIdxFun_value :
    FinSetSkel.toIdxFun sampleSkelHom (ULift.up (⟨2, by decide⟩ : Fin objThree.len)) =
      ULift.up (⟨0, by decide⟩ : Fin objTwo.len) := rfl

/-- Composing the sample morphism with a non-identity morphism
computes by composing the underlying vectors' entries. -/
theorem sampleSkelHom_comp_swapHom_value :
    (sampleSkelHom ≫ swapHom).toVec.get ⟨2, by decide⟩ = ⟨1, by decide⟩ := rfl
