/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.CategoryTheory.Grothendieck

/-!
# Tests for the covariant and contravariant Grothendieck constructions
-/

set_option linter.privateModule false

open CategoryTheory

/-! ## Covariant `functorToCat` -/

/-- A concrete covariant `Cat`-valued functor: constant at `Type`. -/
def constTypeCovariant : Type ⥤ Cat.{0, 1} :=
  (Functor.const (Type : Type 1)).obj (Cat.of Type)

/-- `functorToCat` applied to a constant functor yields the
Grothendieck construction on the nose. -/
theorem functorToCat_obj_constTypeCovariant :
    (Grothendieck.functorToCat (E := Cat.of (Type : Type 1))).obj
        constTypeCovariant =
      Cat.of (Grothendieck constTypeCovariant) :=
  rfl

/-! ## `GrothendieckOp` objects -/

/-- A constant `Cat`-valued functor on `Type` for exercising
`GrothendieckOp`. -/
def constTypeOp : Type ⥤ Cat.{0, 1} :=
  (Functor.const (Type : Type 1)).obj (Cat.of Type)

/-- A sample object: base `Bool`, fiber `Nat`. -/
def gOpObj : GrothendieckOp constTypeOp :=
  GrothendieckOp.mk Bool Nat

/-- `gOpObj.base` reduces to `Bool`. -/
theorem gOpObj_base : gOpObj.base = Bool := rfl

/-- `gOpObj.fiber` reduces to `Nat`. -/
theorem gOpObj_fiber : gOpObj.fiber = Nat := rfl

/-- `gOpObj` is its own `mk` round-trip. -/
theorem gOpObj_eta :
    GrothendieckOp.mk gOpObj.base gOpObj.fiber = gOpObj := rfl

/-! ## `GrothendieckOp` morphisms -/

/-- A second object: base `Nat`, fiber `String`. -/
def gOpObj' : GrothendieckOp constTypeOp :=
  GrothendieckOp.mk Nat String

/-- A sample morphism `gOpObj ⟶ gOpObj'`. Its fiber component runs
`String ⟶ Nat` (target fiber to source fiber) because the fiber
direction is reversed. -/
def gOpHom : gOpObj ⟶ gOpObj' :=
  GrothendieckOp.homMk (↾fun b ↦ (cond b 1 0 : Nat)) (↾String.length)

/-- `gOpHom`'s base component reduces to the base function on the
nose. -/
theorem gOpHom_base :
    GrothendieckOp.homBase gOpHom = ↾fun b ↦ (cond b 1 0 : Nat) :=
  rfl

/-- `gOpHom`'s fiber component reduces to the fiber function on the
nose. -/
theorem gOpHom_fiber :
    GrothendieckOp.homFiber gOpHom = ↾String.length :=
  rfl

/-- `gOpHom` is its own `homMk` round-trip. -/
theorem gOpHom_eta :
    GrothendieckOp.homMk (GrothendieckOp.homBase gOpHom)
      (GrothendieckOp.homFiber gOpHom) = gOpHom :=
  rfl

/-- `homBase` sends composition with the identity to the original base
component. -/
theorem gOpComp_base :
    GrothendieckOp.homBase (𝟙 gOpObj ≫ gOpHom) =
      GrothendieckOp.homBase gOpHom := by
  simp

/-! ## `CoGrothendieck` objects -/

/-- The running contravariant example: constant at `Type` on
`(Type)ᵒᵖ`. -/
def constTypeContra : (Type : Type 1)ᵒᵖ ⥤ Cat.{0, 1} :=
  (Functor.const (Type : Type 1)ᵒᵖ).obj (Cat.of Type)

/-- A sample object: base `Bool`, fiber `Nat`. -/
def coObj : CoGrothendieck constTypeContra :=
  CoGrothendieck.mk Bool Nat

/-- A second object: base `Nat`, fiber `String`. -/
def coObj' : CoGrothendieck constTypeContra :=
  CoGrothendieck.mk Nat String

/-- `coObj.base` reduces to `Bool`. -/
theorem coObj_base : coObj.base = Bool := rfl

/-- `coObj.fiber` reduces to `Nat`. -/
theorem coObj_fiber : coObj.fiber = Nat := rfl

/-- `coObj` is its own `mk` round-trip. -/
theorem coObj_eta :
    CoGrothendieck.mk coObj.base coObj.fiber = coObj := rfl

/-! ## `CoGrothendieck` morphisms -/

/-- A sample morphism `coObj ⟶ coObj'`: base `Bool → Nat`, fiber
`Nat → String` (source fiber to target fiber — contravariant hom
direction with a constant functor). -/
def coHom : coObj ⟶ coObj' :=
  CoGrothendieck.homMk (↾fun b ↦ (cond b 1 0 : Nat))
    (↾fun n : Nat ↦ toString n)

/-- A third object, for composition tests. -/
def coObj'' : CoGrothendieck constTypeContra :=
  CoGrothendieck.mk Unit Bool

/-- A second morphism, composable after `coHom`. -/
def coHom' : coObj' ⟶ coObj'' :=
  CoGrothendieck.homMk (↾fun _ ↦ ()) (↾String.isEmpty)

/-- `coHom`'s base component reduces to the base function on the
nose. -/
theorem coHom_base :
    CoGrothendieck.homBase coHom = ↾fun b ↦ (cond b 1 0 : Nat) :=
  rfl

/-- `coHom`'s fiber component reduces to the fiber function on the
nose. -/
theorem coHom_fiber :
    CoGrothendieck.homFiber coHom = ↾fun n : Nat ↦ toString n :=
  rfl

/-- `coHom` is its own `homMk` round-trip. -/
theorem coHom_eta :
    CoGrothendieck.homMk (CoGrothendieck.homBase coHom)
      (CoGrothendieck.homFiber coHom) = coHom :=
  rfl

/-- `homBase` sends composition to composition of base components. -/
theorem coComp_base :
    CoGrothendieck.homBase (coHom ≫ coHom') =
      CoGrothendieck.homBase coHom ≫ CoGrothendieck.homBase coHom' :=
  rfl

/-- `homFiber` of the composite reduces to the composite fiber
function on the nose. -/
theorem coComp_fiber :
    CoGrothendieck.homFiber (coHom ≫ coHom') =
      ↾fun n : Nat ↦ (toString n).isEmpty :=
  rfl

/-! ## Projections -/

/-- `CoGrothendieck.forget` applied to `coObj` reduces to its base object. -/
theorem coForget_obj :
    (CoGrothendieck.forget constTypeContra).obj coObj = Bool := rfl

/-- `CoGrothendieck.forget` applied to `coHom` reduces to its base morphism. -/
theorem coForget_map :
    (CoGrothendieck.forget constTypeContra).map coHom =
      CoGrothendieck.homBase coHom :=
  rfl

/-! ## Functoriality in the functor -/

/-- The `List` endofunctor on the category of types, with bundled
morphisms. -/
def listFunctor : Type ⥤ Type where
  obj X := List X
  map f := ↾(List.map (ConcreteCategory.hom f))

/-- A natural transformation between constant functors, induced by
`listFunctor` via `Functor.const`. -/
def constListNatTrans : constTypeContra ⟶ constTypeContra :=
  (Functor.const (Type : Type 1)ᵒᵖ).map listFunctor.toCatHom

/-- `CoGrothendieck.map` applied to `constListNatTrans` sends `coObj` to
the object with fiber `List Nat`. -/
theorem coMap_obj :
    (CoGrothendieck.map constListNatTrans).obj coObj =
      CoGrothendieck.mk Bool (List Nat) :=
  rfl

/-- `CoGrothendieck.map` leaves the base component of a morphism
unchanged. -/
theorem coMap_map_base :
    CoGrothendieck.homBase
        ((CoGrothendieck.map constListNatTrans).map coHom) =
      CoGrothendieck.homBase coHom :=
  rfl

/-! ## Packaged functors -/

/-- `CoGrothendieck.functorToCat` applied to `constTypeContra` reduces to
the `CoGrothendieck` construction on it, on the nose. -/
theorem coFunctorToCat_obj :
    (CoGrothendieck.functorToCat (E := Cat.of (Type : Type 1))).obj
        constTypeContra =
      Cat.of (CoGrothendieck constTypeContra) :=
  rfl

/-- `CoGrothendieck.functor` applied to `constTypeContra` has hom
component `CoGrothendieck.forget constTypeContra`. -/
theorem coFunctor_obj_hom :
    ((CoGrothendieck.functor (E := Cat.of (Type : Type 1))).obj
        constTypeContra).hom =
      (CoGrothendieck.forget constTypeContra).toCatHom :=
  rfl
