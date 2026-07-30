/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Shapes.Core

/-!
# Tests for the shapes core of `FinSetSkel`

A sample point of a three-element object at a fixed universe, the
index it looks up, its round trip through the index-function
correspondence, terminality of the one-element object, a computed
binary coproduct with its descent morphism, and a computed binary
product with its lift and the two factorisations.

## Tags

category, finite set, skeleton, terminal, point, coproduct, product
-/

@[expose] public section

open CategoryTheory FinSetSkel

/-- A sample point of the three-element object. -/
def sampleSkelPoint : (mk 1 : FinSetSkel.{0}) ⟶ mk 3 := point (2 : Fin 3)

/-- The sample point picks the index it names. -/
theorem sampleSkelPoint_get (t : Fin (mk 1 : FinSetSkel.{0}).len) :
    sampleSkelPoint.toVec.get t = 2 := point_get _ _

/-- The index-function correspondence round-trips the sample
point. -/
theorem sampleSkelPoint_roundtrip :
    (homEquivIdxFun (mk 1) (mk 3)).symm
      (homEquivIdxFun (mk 1) (mk 3) sampleSkelPoint) = sampleSkelPoint :=
  (homEquivIdxFun (mk 1) (mk 3)).symm_apply_apply sampleSkelPoint

/-- Every morphism into the one-element object is the canonical
one. -/
theorem sampleToOne (f : (mk 3 : FinSetSkel.{0}) ⟶ mk 1) : f = toOne (mk 3) :=
  toOne_uniq f

/-- A sample morphism out of the two-element object. -/
def sampleSkelLeftLeg : (mk 2 : FinSetSkel.{0}) ⟶ mk 4 :=
  Hom.ofVec (Vector.ofFnC (fun i ↦ ⟨(i.1 + 1) % 4, Nat.mod_lt _ (by decide)⟩))

/-- A sample morphism out of the three-element object. -/
def sampleSkelRightLeg : (mk 3 : FinSetSkel.{0}) ⟶ mk 4 :=
  Hom.ofVec (Vector.ofFnC (fun i ↦ ⟨2 * i.1 % 4, Nat.mod_lt _ (by decide)⟩))

/-- The descent of the two sample morphisms out of their coproduct. -/
def sampleSkelDesc : coprodObj (mk 2) (mk 3) ⟶ (mk 4 : FinSetSkel.{0}) :=
  coprodDesc sampleSkelLeftLeg sampleSkelRightLeg

/-- The descent's vector concatenates its two components' vectors. -/
theorem sampleSkelDesc_toVec :
    sampleSkelDesc.toVec.toList = [1, 2, 0, 2, 0] := rfl

/-- The descent agrees with its left component at a sample index. -/
theorem sampleSkelDesc_inl_get :
    (coprodInl (mk 2) (mk 3) ≫ sampleSkelDesc).toVec.get ⟨1, by decide⟩ =
      sampleSkelLeftLeg.toVec.get ⟨1, by decide⟩ := rfl

/-- The descent agrees with its right component at a sample index. -/
theorem sampleSkelDesc_inr_get :
    (coprodInr (mk 2) (mk 3) ≫ sampleSkelDesc).toVec.get ⟨1, by decide⟩ =
      sampleSkelRightLeg.toVec.get ⟨1, by decide⟩ := rfl

/-- A sample morphism into the two-element object. -/
def sampleToTwo : (mk 5 : FinSetSkel.{0}) ⟶ mk 2 :=
  Hom.ofVec (Vector.ofFnC (fun i ↦ ⟨i.1 % 2, Nat.mod_lt _ (by decide)⟩))

/-- A sample morphism into the three-element object. -/
def sampleToThree : (mk 5 : FinSetSkel.{0}) ⟶ mk 3 :=
  Hom.ofVec (Vector.ofFnC (fun i ↦ ⟨i.1 % 3, Nat.mod_lt _ (by decide)⟩))

/-- A sample lift into the binary product. -/
def sampleProdLift : (mk 5 : FinSetSkel.{0}) ⟶ prodObj (mk 2) (mk 3) :=
  prodLift sampleToTwo sampleToThree

/-- The lift's vector pairs its two components' vectors index by
index, `Fin.pairC a b` being `a * 3 + b`. -/
theorem sampleProdLift_toVec :
    sampleProdLift.toVec.toList = [0, 4, 2, 3, 1] := rfl

/-- The first factorisation holds at the sample. -/
theorem sampleProdLift_fst : sampleProdLift ≫ prodFst (mk 2) (mk 3) = sampleToTwo :=
  prodLift_fst _ _

/-- The second factorisation holds at the sample. -/
theorem sampleProdLift_snd : sampleProdLift ≫ prodSnd (mk 2) (mk 3) = sampleToThree :=
  prodLift_snd _ _
