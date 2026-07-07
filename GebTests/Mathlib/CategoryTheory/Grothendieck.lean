/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.CategoryTheory.Grothendieck

set_option linter.privateModule false

/-!
# Tests for the covariant and contravariant Grothendieck constructions
-/

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
  GrothendieckOp.homMk (↾fun b => (cond b 1 0 : Nat)) (↾String.length)

/-- `gOpHom`'s base component reduces to the base function on the
nose. -/
theorem gOpHom_base :
    GrothendieckOp.homBase gOpHom = ↾fun b => (cond b 1 0 : Nat) :=
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
