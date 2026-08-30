/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.Grothendieck.Functor

/-!
# Tests for functors to and from the Grothendieck construction

Concrete data over the constant `Cat`-valued functor on `Type` exercises the
correspondence between functors into a Grothendieck construction and their
determining data, and the correspondence between functors out of one and theirs,
mostly by `rfl`.

## Tags

Grothendieck construction, functor category
-/

@[expose] public section

set_option linter.privateModule false

open CategoryTheory

/-- A concrete covariant `Cat`-valued functor: constant at `Type`. -/
def constType : Type ⥤ Cat.{0, 1} :=
  (Functor.const (Type : Type 1)).obj (Cat.of Type)

/-! ### Functors into a Grothendieck construction -/

/-- Data determining the functor sending each type to the pair of that type with
the one-point type. -/
def punitToData : Grothendieck.FunctorToData constType Type where
  baseFunc := 𝟭 Type
  fib _ := PUnit
  hom _ := 𝟙 _
  hom_id _ := by cat_disch
  hom_comp _ _ := by cat_disch

/-- The functor determined by `punitToData` pairs a type with the one-point
type. -/
theorem functorTo_punitToData_obj (X : Type) :
    (Grothendieck.functorTo punitToData).obj X = ⟨X, PUnit⟩ :=
  rfl

/-- Extracting the data from the functor determined by `punitToData` recovers
it. -/
theorem ofFunctor_functorTo_punitToData :
    Grothendieck.ofFunctor (Grothendieck.functorTo punitToData) = punitToData :=
  rfl

/-- The base functor of the extracted data is the projection to the base. -/
theorem ofFunctor_baseFunc (K : Type ⥤ Grothendieck constType) :
    (Grothendieck.ofFunctor K).baseFunc = K ⋙ Grothendieck.forget _ :=
  rfl

/-- The correspondence between functors into a Grothendieck construction and
their determining data is an isomorphism of categories on the nose. -/
theorem functorToDataIsoCat_hom_obj (data : Grothendieck.FunctorToData
    constType Type) :
    (Grothendieck.functorToDataToFunctorCat constType Type).obj data =
      Grothendieck.functorTo data :=
  rfl

/-! ### Functors out of a Grothendieck construction -/

/-- Data determining the functor sending each object of the Grothendieck
construction to its fiber component. -/
def fiberFromData : Grothendieck.FunctorFromData constType Type where
  fib _ := 𝟭 Type
  hom _ := 𝟙 _
  hom_id _ := by cat_disch
  hom_comp _ _ _ _ _ := by cat_disch

/-- The functor determined by `fiberFromData` returns the fiber component. -/
theorem functorFromData_fiberFromData_obj
    (X : Grothendieck constType) :
    (Grothendieck.functorFromData fiberFromData).obj X = X.fiber :=
  rfl

/-- Restricting the functor determined by `fiberFromData` along a fiber
inclusion recovers the identity functor. -/
theorem ofFunctorFrom_functorFromData_fiberFromData_fib (c : Type) :
    (Grothendieck.ofFunctorFrom
        (Grothendieck.functorFromData fiberFromData)).fib c =
      Grothendieck.ι constType c ⋙
        Grothendieck.functorFromData fiberFromData :=
  rfl

/-! ### Functors into a contravariant Grothendieck construction -/

/-- A concrete contravariant `Cat`-valued functor: constant at `Type`. -/
def constTypeOp : Typeᵒᵖ ⥤ Cat.{0, 1} :=
  (Functor.const (Typeᵒᵖ : Type 1)).obj (Cat.of Type)

/-- Data determining the functor sending each type to the pair of that type with
the one-point type, into the contravariant construction. -/
def punitCoToData : CoGrothendieck.FunctorToData constTypeOp Type :=
  CoGrothendieck.FunctorToData.mk (𝟭 Type) (fun _ ↦ PUnit) (fun _ ↦ 𝟙 _)
    (fun _ ↦ by cat_disch) (fun _ _ ↦ by cat_disch)

/-- The constructor recovers the base functor on the nose. -/
theorem punitCoToData_baseFunc : punitCoToData.baseFunc = 𝟭 Type :=
  rfl

/-- The constructor recovers the fiber objects on the nose. -/
theorem punitCoToData_fib (X : Type) : punitCoToData.fib X = PUnit :=
  rfl

/-- The functor determined by `punitCoToData` pairs a type with the one-point
type. -/
theorem functorTo_punitCoToData_obj (X : Type) :
    (CoGrothendieck.functorTo punitCoToData).obj X = CoGrothendieck.mk X PUnit :=
  rfl

/-- Extracting the data from the functor determined by `punitCoToData` recovers
it. -/
theorem ofFunctor_functorTo_punitCoToData :
    CoGrothendieck.ofFunctor (CoGrothendieck.functorTo punitCoToData) =
      punitCoToData :=
  rfl

/-! ### Functors out of a contravariant Grothendieck construction -/

/-- Data determining the functor sending each object of the contravariant
construction to its fiber component. -/
def fiberCoFromData : CoGrothendieck.FunctorFromData constTypeOp Type :=
  CoGrothendieck.FunctorFromData.mk (fun _ ↦ 𝟭 Type) (fun _ ↦ 𝟙 _)
    (fun _ ↦ by cat_disch) (fun _ _ _ _ _ ↦ by cat_disch)

/-- The constructor recovers the fiber functors on the nose. -/
theorem fiberCoFromData_fib (X : Type) : fiberCoFromData.fib X = 𝟭 Type :=
  rfl

/-- The functor determined by `fiberCoFromData` returns the fiber component. -/
theorem functorFromData_fiberCoFromData_obj (X : CoGrothendieck constTypeOp) :
    (CoGrothendieck.functorFromData fiberCoFromData).obj X = X.fiber :=
  rfl

/-! ### Functors between Grothendieck constructions -/

/-- Data determining a functor `Grothendieck constType ⥤ Grothendieck constType`
by fiberwise data throughout. -/
def punitBetweenData : FunctorCovToCovData constType constType where
  fibTo _ := punitToData
  homNat _ := 𝟙 _
  homNat_id _ := by cat_disch
  homNat_comp _ _ _ _ _ := by cat_disch

/-- The fibrewise component is the data it was built from. -/
theorem punitBetweenData_fibTo (X : Type) :
    punitBetweenData.fibTo X = punitToData :=
  rfl

/-- Coarsening the data determining a functor between two Grothendieck
constructions and refining it back is the identity. -/
theorem ofFromData_toFromData_punitBetweenData :
    FunctorCovToCovData.ofFromData punitBetweenData.toFromData =
      punitBetweenData :=
  rfl

/-- Refining the data determining a functor out of a Grothendieck construction
and coarsening it back is the identity. -/
theorem toFromData_ofFromData_covToCov
    (data : Grothendieck.FunctorFromData constType (Grothendieck constType)) :
    (FunctorCovToCovData.ofFromData data).toFromData = data :=
  rfl

/-- The equivalence with the functor category factors through the category of
data determining a functor out of the domain. -/
theorem functorCovToCovDataEquivCat_functor :
    (functorCovToCovDataEquivCat constType constType).functor =
      functorCovToCovDataToFromData constType constType ⋙
        Grothendieck.functorFromDataToFunctorCat constType
          (Grothendieck constType) :=
  rfl

/-- Data determining a functor
`CoGrothendieck constTypeOp ⥤ CoGrothendieck constTypeOp` by fiberwise data
throughout. -/
def punitCoBetweenData : FunctorContraToContraData constTypeOp constTypeOp where
  fibTo _ := punitCoToData
  homNat _ := 𝟙 _
  homNat_id _ := by cat_disch
  homNat_comp _ _ _ _ _ := by cat_disch

/-- The fibrewise component is the data it was built from. -/
theorem punitCoBetweenData_fibTo (X : Type) :
    punitCoBetweenData.fibTo X = punitCoToData :=
  rfl

/-- Coarsening the contravariant data and refining it back is the identity. -/
theorem ofFromData_toFromData_punitCoBetweenData :
    FunctorContraToContraData.ofFromData punitCoBetweenData.toFromData =
      punitCoBetweenData :=
  rfl
