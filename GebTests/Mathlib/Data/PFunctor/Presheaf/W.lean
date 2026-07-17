/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.W
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Fin.Basic

-- Test files keep their declarations private; silence the
-- only-private-declarations lint.
set_option linter.privateModule false

/-!
# Tests for the presheaf W-type hereditary-naturality predicate
-/

open CategoryTheory

/-- In `Fin 2`, the unique direction of shape `x` over base point `i` has
underlying value `i + x`: `x + (i + x) = i`. -/
private theorem fin2_add_idx (x i : Fin 2) : x + (i + x) = i := by omega

/-- A concrete presheaf polynomial functor over the preorder category on
`Fin 2` (for both index categories), reused as the fixture from the
Presheaf/Basic test module (its `presheafWitness` is module-private, so it is
redefined here). -/
@[reducible] def presheafWitnessData : PresheafPFunctorData (Fin 2) (Fin 2) where
  A := Fin 2
  B := fun _ ↦ Fin 2
  r := fun x ↦ x.1 + x.2
  q := id
  directionRestr := fun a {_i i'} _f _b ↦ ⟨i' + a, fin2_add_idx a i'⟩
  shapeRestr := fun {_j j'} _g _s ↦ ⟨j', rfl⟩
  reindex := fun {_j _j'} _g a {i} _b ↦ ⟨i + a.1, fin2_add_idx a.1 i⟩

/-- The constraint `r ⟨a, ·⟩ = a + ·` is injective, so each fibre
`Direction a i` has at most one element. -/
private theorem fin2_direction_cancel (a x y i : Fin 2) (hx : a + x = i) (hy : a + y = i) :
    x = y := by omega

/-- Each direction fibre of the witness is a singleton. -/
private instance subsingleton_direction (a i : Fin 2) :
    Subsingleton (presheafWitnessData.toSliceDomPFunctor.Direction a i) :=
  ⟨fun x y ↦ Subtype.ext (fin2_direction_cancel a x.1 y.1 i x.2 y.2)⟩

/-- Each shape fibre of the witness is a singleton (the shape-output map
`q = id` separates the two shapes). -/
private instance subsingleton_shape (j : Fin 2) :
    Subsingleton (presheafWitnessData.toSlicePFunctor.Shape j) :=
  ⟨fun x y ↦ Subtype.ext (by
    have hx : (x.1 : Fin 2) = j := x.2
    have hy : (y.1 : Fin 2) = j := y.2
    exact hx.trans hy.symm)⟩

/-- The witness, with all seven functor laws discharged by `Subsingleton.elim`. -/
def presheafWitness : PresheafPFunctor (Fin 2) (Fin 2) where
  toPresheafPFunctorData := presheafWitnessData
  isFunctorial :=
    { directionRestr_id := by intro a i; funext b; exact Subsingleton.elim _ _
      directionRestr_comp := by intro a i i' i'' f g; funext b; exact Subsingleton.elim _ _
      shapeRestr_id := by intro j; funext s; exact Subsingleton.elim _ _
      shapeRestr_comp := by intro j j' j'' g h; funext s; exact Subsingleton.elim _ _
      reindex_naturality := by intro j j' g a i i' f; funext b; exact Subsingleton.elim _ _
      reindex_id := by intro j a i b; exact Subsingleton.elim _ _
      reindex_comp := by intro j j' j'' g h a i b; exact Subsingleton.elim _ _ }

-- `IsHereditarilyNatural` unfolds one level via `isHereditarilyNatural_mk`:
-- local naturality at the root together with hereditary naturality of every
-- child subtree.
example (x : presheafWitness.toSliceDomPFunctor.Obj presheafWitness.toSlicePFunctor.wIndex) :
    presheafWitness.IsHereditarilyNatural (SlicePFunctor.W.mk x) ↔
      (∀ ⦃i i' : Fin 2⦄ (g : i' ⟶ i)
          (b : presheafWitness.toSliceDomPFunctor.Direction x.1.1 i),
          x.1.2 (presheafWitness.directionRestr x.1.1 g b).1
            = presheafWitness.wRestrTree g (x.1.2 b.1)
                (((presheafWitness.toSliceDomPFunctor.compatible_iff
                  presheafWitness.toSlicePFunctor.wIndex x.1.1 x.1.2).mp x.2 b.1).trans b.2)) ∧
        ∀ b, presheafWitness.IsHereditarilyNatural (x.1.2 b) :=
  presheafWitness.isHereditarilyNatural_mk x

-- Restriction of the carrier presheaf `W` along an identity is the identity map.
example (w : (presheafWitness.W).obj ⟨(1 : Fin 2)⟩) :
    (presheafWitness.W).map (𝟙 ⟨(1 : Fin 2)⟩) w = w :=
  presheafWitness.W.map_id_apply ⟨(1 : Fin 2)⟩ w

-- `dest` is a left inverse of `mk`: the fixed-point round trip on a node over
-- the carrier presheaf `F.W` returns the node.
example (x : (presheafWitness.objPresheaf presheafWitness.W).obj ⟨(1 : Fin 2)⟩) :
    PresheafPFunctor.W.dest (PresheafPFunctor.W.mk x) = x :=
  PresheafPFunctor.W.dest_mk x

/-- A concrete choice-free target presheaf algebra: the constant presheaf on
`(Fin 2)ᵒᵖ` at `PUnit`, every fibre `PUnit` and every restriction the identity. -/
@[reducible] def constPUnit : (Fin 2)ᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := 𝟙 _

/-- The presheaf algebra on `constPUnit`: its structure map sends every node to
the unique element of `PUnit`. Naturality holds since `PUnit` is a subsingleton. -/
def constPUnitAlg : NatTrans (presheafWitness.objPresheaf constPUnit) constPUnit where
  app _ := ↾ fun _ ↦ PUnit.unit
  naturality _ _ _ := rfl

/-- The eliminator of the presheaf W-type into the constant-`PUnit` algebra. The
carrier `presheafWitness.W` admits no elements (its functor has no leaf shape),
so this eliminator is the concrete W-value the property test below asserts
about. -/
def elimConstPUnit : NatTrans presheafWitness.W constPUnit :=
  PresheafPFunctor.W.elim presheafWitness constPUnit constPUnitAlg

-- The computation rule `elim_mk`: `elim` composed with `mk` is the algebra step
-- one level, `elim` applied to the children through `mapPresheaf`.
example (x : (presheafWitness.objPresheaf presheafWitness.W).obj ⟨(1 : Fin 2)⟩) :
    elimConstPUnit.app ⟨(1 : Fin 2)⟩ (PresheafPFunctor.W.mk x) =
      constPUnitAlg.app ⟨(1 : Fin 2)⟩
        ((presheafWitness.mapPresheaf elimConstPUnit).app ⟨(1 : Fin 2)⟩ x) :=
  PresheafPFunctor.W.elim_mk presheafWitness constPUnit constPUnitAlg x
