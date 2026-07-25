/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebTests.Mathlib.Data.PFunctor.Presheaf.Fixtures

/-!
# Tests for the finite presheaf polynomial functor forwarding instances

Reduction tests for the general-tier forwarding instances on
`FinitePresheafPFunctor`. The shared `finiteWFixture` supplies the bundled
finiteness evidence, and `decide` verifies that the forwarding instances reduce
correctly for shape-fiber membership, direction-fiber membership, naturality,
and compatibility. A resolution test confirms that the instances are also
reachable by inference against a variable of the structure type, which is how
downstream code meets them.

## Tags

polynomial functor, presheaf, finite, FinEnum, decidability, reduction test
-/

set_option linter.privateModule false

open CategoryTheory PresheafDomPFunctorData PresheafFixture

universe uI uJ uA uB vI vJ

/-! ## Resolution tests

The forwarding instances are found by inference when the subject is a variable
of the structure type. The reduction tests below apply them explicitly instead,
since instance resolution cannot recover `F = finiteWFixture` from the
projection chain in a goal stated at the concrete fixture. -/

/-- `decidableShapeOver` is reachable by inference. -/
example {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : FinitePresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (j : J)
    (a : F.toPresheafPFunctor.A) :
    Decidable (F.toPresheafPFunctor.toSlicePFunctor.ShapeOver j a) := inferInstance

/-- `decidableDirectionOver` is reachable by inference. -/
example {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : FinitePresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (a : F.toPresheafPFunctor.A) (i : I)
    (b : F.toPresheafPFunctor.B a) :
    Decidable (F.toPresheafPFunctor.toSliceDomPFunctor.DirectionOver a i b) :=
  inferInstance

/-! ## Direction assignments for the naturality test -/

/-- A natural direction assignment for shape `.R`: the constant `Fin 2`-value
`0` on both directions. Over `0 ⟶ 1` the two directions receive equal values,
so naturality holds. -/
def xGood : finiteWFixture.toPresheafPFunctor.toSliceDomPFunctor.Obj
    (elemProj zFix) :=
  ⟨⟨.R, fun b ↦ ⟨b, (0 : Fin 2)⟩⟩,
    (wFixture.toSliceDomPFunctor.compatible_iff (elemProj zFix) .R _).mpr
      fun _ ↦ rfl⟩

/-- An unnatural direction assignment for shape `.R`: recording each direction's
own index as its `Fin 2`-value. Over `0 ⟶ 1` the two directions receive the
distinct values `0` and `1`, refuting naturality. -/
def xBad : finiteWFixture.toPresheafPFunctor.toSliceDomPFunctor.Obj
    (elemProj zFix) :=
  ⟨⟨.R, fun b ↦ ⟨b, b⟩⟩,
    (wFixture.toSliceDomPFunctor.compatible_iff (elemProj zFix) .R _).mpr
      fun _ ↦ rfl⟩

/-! ## Shape-fiber membership tests -/

/-- Shape-fiber membership: `R` is over index `1`. -/
def shapeOverTrue : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableShapeOver finiteWFixture 1 Shp.R)

/-- Shape-fiber membership: `R` is not over index `0`. -/
def shapeOverFalse : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableShapeOver finiteWFixture 0 Shp.R)

example : shapeOverTrue = true := by decide
example : shapeOverFalse = false := by decide

/-! ## Direction-fiber membership tests -/

/-- Direction-fiber membership: direction `0` of shape `R` is over index `0`. -/
def directionOverTrue : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableDirectionOver finiteWFixture
    Shp.R 0 (0 : Fin 2))

/-- Direction-fiber membership: direction `1` of shape `R` is not over
index `0`. -/
def directionOverFalse : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableDirectionOver finiteWFixture
    Shp.R 0 (1 : Fin 2))

example : directionOverTrue = true := by decide
example : directionOverFalse = false := by decide

/-! ## Naturality tests -/

/-- Naturality of the good assignment. -/
def isNaturalTrue : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableIsNatural finiteWFixture
    (x := xGood))

/-- Naturality of the bad assignment. -/
def isNaturalFalse : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableIsNatural finiteWFixture
    (x := xBad))

example : isNaturalTrue = true := by decide
example : isNaturalFalse = false := by decide

/-! ## Compatibility tests -/

/-- A compatible direction assignment: `v b = b` satisfies
`id ∘ v = rFix ∘ Sigma.mk .R`. -/
def compatibleTrue : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableCompatible finiteWFixture
    (fun x : Fin 2 ↦ x) Shp.R (fun b ↦ b))

/-- An incompatible direction assignment: the constant `1` violates
`id ∘ v = rFix ∘ Sigma.mk .R` at direction `0`. -/
def compatibleFalse : Bool :=
  @decide _ (FinitePresheafPFunctor.decidableCompatible finiteWFixture
    (fun x : Fin 2 ↦ x) Shp.R (fun _ ↦ (1 : Fin 2)))

example : compatibleTrue = true := by decide
example : compatibleFalse = false := by decide
