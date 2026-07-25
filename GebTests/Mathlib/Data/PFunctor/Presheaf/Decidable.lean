/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable
import GebTests.Mathlib.Data.PFunctor.Presheaf.Fixtures

/-!
# Tests for the presheaf naturality decidability instance

A presheaf-domain polynomial functor over the preorder category on `Fin 2`,
paired with the constant `Fin 2` input presheaf `zFix`, makes `IsNatural`
falsifiable: over the non-identity morphism `0 ⟶ 1` the naturality equation
forces the direction assignment to give equal values to the two directions.
A constant assignment satisfies it; an assignment recording each direction's
index refutes it.

The shared `wFixture` is a presheaf polynomial endofunctor over the same
category, built so that `PresheafPFunctor.IsHereditarilyNatural` is both
inhabited and falsifiable, and exercises
`PresheafPFunctor.decidableIsHereditarilyNatural` by reduction: `hereditaryTrue`
and `hereditaryFalse` reduce to `true` and `false` respectively.

## Tags

polynomial functor, presheaf, naturality, hereditary naturality, decidability,
W-type, FinEnum
-/

set_option linter.privateModule false

open CategoryTheory PresheafDomPFunctorData PresheafFixture

/-! ## The direction-only fixture -/

/-- In `Fin 2`, the unique direction of shape `x` over base point `i` has
underlying value `i + x`: `x + (i + x) = i`. -/
private theorem fin2_add_idx (x i : Fin 2) : x + (i + x) = i := by omega

/-- The direction-only fixture over the preorder category on `Fin 2`: two
shapes, two directions per shape, constraint `r ⟨a, b⟩ = a + b`, and
`directionRestr` picking the unique direction of the target fiber. Only the
domain-side data is needed to state and decide `IsNatural`. -/
@[reducible] def presheafWitness : PresheafDomPFunctorData (Fin 2) where
  A := Fin 2
  B := fun _ ↦ Fin 2
  r := fun x ↦ x.1 + x.2
  directionRestr := fun a {_i i'} _f _b ↦ ⟨i' + a, fin2_add_idx a i'⟩

/-- The fixture is finitary: each shape has the two directions of `Fin 2`. -/
instance finitaryPresheafWitness : presheafWitness.Finitary := fun _ ↦ finEnumFin2

/-- A natural direction assignment: shape `0` with the constant `Fin 2`-value
`0` on both directions. Over `0 ⟶ 1` the two directions receive equal values,
so naturality holds. -/
def xGood : presheafWitness.toSliceDomPFunctor.Obj (elemProj zFix) :=
  ⟨⟨(0 : Fin 2), fun b ↦ ⟨(0 : Fin 2) + b, (0 : Fin 2)⟩⟩,
    (presheafWitness.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ ↦ rfl⟩

/-- An unnatural direction assignment: shape `0` recording each direction's
own index as its `Fin 2`-value. Over `0 ⟶ 1` the two directions receive the
distinct values `0` and `1`, refuting naturality. -/
def xBad : presheafWitness.toSliceDomPFunctor.Obj (elemProj zFix) :=
  ⟨⟨(0 : Fin 2), fun b ↦ ⟨(0 : Fin 2) + b, b⟩⟩,
    (presheafWitness.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ ↦ rfl⟩

/-- A natural direction assignment. -/
def isNaturalTrue : Bool := decide (presheafWitness.IsNatural xGood)

/-- An unnatural direction assignment. -/
def isNaturalFalse : Bool := decide (presheafWitness.IsNatural xBad)

example : isNaturalTrue = true := by decide
example : isNaturalFalse = false := by decide

/-! ## Hereditary-naturality reduction test

The shared `finitaryWFixture` is a `def`, so that the `Finite` test modules
exercise the forwarding instances on `FinitePresheafPFunctor`. This module wants
the general-tier instance instead, so it installs the evidence locally. -/

/-- The fixture's finitary evidence, as an instance, supplying
`PresheafPFunctor.decidableIsHereditarilyNatural`. -/
instance finitaryWFixtureInst : wFixture.Finitary := finitaryWFixture

/-- A hereditarily natural tree. -/
def hereditaryTrue : Bool := decide (wFixture.IsHereditarilyNatural goodTree)

/-- A tree failing naturality at one node. -/
def hereditaryFalse : Bool := decide (wFixture.IsHereditarilyNatural badTree)

example : hereditaryTrue = true := by decide
example : hereditaryFalse = false := by decide
