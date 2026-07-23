/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Decidable
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Fin.Basic

/-!
# Tests for the presheaf naturality decidability instance

A presheaf-domain polynomial functor over the preorder category on `Fin 2`,
paired with the constant `Fin 2` input presheaf, makes `IsNatural`
falsifiable: over the non-identity morphism `0 ⟶ 1` the naturality equation
forces the direction assignment to give equal values to the two directions.
A constant assignment satisfies it; an assignment recording each direction's
index refutes it.

The finite enumerations the instance consumes are supplied choice-free: a
`FinEnum (Fin 2)` from an explicit equivalence, and a `FinEnum` of the
preorder hom-sets built from a `FinEnum (PLift p)` for a decidable `p` and
stated at the `⟶` head (instance resolution does not unfold `Quiver.Hom`).

## Tags

polynomial functor, presheaf, naturality, decidability, FinEnum
-/

set_option linter.privateModule false

open CategoryTheory PresheafDomPFunctorData

/-- A choice-free `FinEnum (Fin 2)` for the index objects, from the identity
equivalence rather than `FinEnum.fin` (which routes through `Classical.choice`). -/
instance finEnumFin2 : FinEnum (Fin 2) where
  card := 2
  equiv := Equiv.refl (Fin 2)
  decEq := inferInstance

/-- A choice-free `FinEnum (PLift p)` for a decidable proposition `p`: one
element when `p` holds, none otherwise. The equivalence laws are discharged
by case analysis (`PLift p` is a subsingleton), not `decide`. -/
instance finEnumPLift {p : Prop} [Decidable p] : FinEnum (PLift p) :=
  if h : p then
    { card := 1
      equiv :=
        { toFun := fun _ => 0
          invFun := fun _ => ⟨h⟩
          left_inv := fun x => by cases x; rfl
          right_inv := fun i => Fin.cases rfl (fun j => j.elim0) i }
      decEq := fun a b => isTrue (by cases a; cases b; rfl) }
  else
    { card := 0
      equiv :=
        { toFun := fun x => absurd x.down h
          invFun := fun i => i.elim0
          left_inv := fun x => absurd x.down h
          right_inv := fun i => i.elim0 }
      decEq := fun a _ => absurd a.down h }

/-- A choice-free `FinEnum` of a preorder hom-set, stated at the `⟶` head and
delegating to the `ULift`/`PLift` enumeration. An instance at `PLift` alone
does not fire on a goal headed by `⟶`, since `Quiver.Hom` is a `def` that
instance resolution does not unfold. -/
instance finEnumHom (i i' : Fin 2) : FinEnum (i' ⟶ i) :=
  inferInstanceAs (FinEnum (ULift (PLift (i' ≤ i))))

/-- The constant input presheaf on `(Fin 2)ᵒᵖ` at `Fin 2`, every restriction
the identity. Its two-element fiber is what makes `IsNatural` falsifiable.
Reducible so `Zfix.obj ⟨i⟩` unfolds to `Fin 2`. -/
@[reducible] def Zfix : (Fin 2)ᵒᵖ ⥤ Type where
  obj _ := Fin 2
  map _ := 𝟙 _

/-- Decidable equality of the input presheaf's fibers, needed to decide the
naturality equation. -/
instance : ∀ i : Fin 2, DecidableEq (Zfix.obj ⟨i⟩) :=
  fun _ => inferInstanceAs (DecidableEq (Fin 2))

/-- In `Fin 2`, the unique direction of shape `x` over base point `i` has
underlying value `i + x`: `x + (i + x) = i`. -/
private theorem fin2_add_idx (x i : Fin 2) : x + (i + x) = i := by omega

/-- The direction-only fixture over the preorder category on `Fin 2`: two
shapes, two directions per shape, constraint `r ⟨a, b⟩ = a + b`, and
`directionRestr` picking the unique direction of the target fiber. Only the
domain-side data is needed to state and decide `IsNatural`. -/
@[reducible] def presheafWitness : PresheafDomPFunctorData (Fin 2) where
  A := Fin 2
  B := fun _ => Fin 2
  r := fun x => x.1 + x.2
  directionRestr := fun a {_i i'} _f _b => ⟨i' + a, fin2_add_idx a i'⟩

/-- The fixture is finitary: each shape has the two directions of `Fin 2`. -/
instance finitaryPresheafWitness : presheafWitness.Finitary := fun _ => finEnumFin2

/-- A natural direction assignment: shape `0` with the constant `Fin 2`-value
`0` on both directions. Over `0 ⟶ 1` the two directions receive equal values,
so naturality holds. -/
def xGood : presheafWitness.toSliceDomPFunctor.Obj (elemProj Zfix) :=
  ⟨⟨(0 : Fin 2), fun b => ⟨(0 : Fin 2) + b, (0 : Fin 2)⟩⟩,
    (presheafWitness.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ => rfl⟩

/-- An unnatural direction assignment: shape `0` recording each direction's
own index as its `Fin 2`-value. Over `0 ⟶ 1` the two directions receive the
distinct values `0` and `1`, refuting naturality. -/
def xBad : presheafWitness.toSliceDomPFunctor.Obj (elemProj Zfix) :=
  ⟨⟨(0 : Fin 2), fun b => ⟨(0 : Fin 2) + b, b⟩⟩,
    (presheafWitness.toSliceDomPFunctor.compatible_iff _ _ _).mpr fun _ => rfl⟩

/-- A natural direction assignment. -/
def isNaturalTrue : Bool := decide (presheafWitness.IsNatural xGood)

/-- An unnatural direction assignment. -/
def isNaturalFalse : Bool := decide (presheafWitness.IsNatural xBad)

example : isNaturalTrue = true := by decide
example : isNaturalFalse = false := by decide
