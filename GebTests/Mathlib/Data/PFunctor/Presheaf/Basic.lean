/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

import Geb.Mathlib.Data.PFunctor.Presheaf.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Fin.Basic

-- Test files keep their declarations private; silence the
-- only-private-declarations lint.
set_option linter.privateModule false

/-!
# Tests for the presheaf-domain polynomial functor core
-/

open CategoryTheory PresheafDomPFunctorData

-- A caller can name the law condition to state things of that type.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) : F.RestrComp :=
  F.isFunctorial.restr_comp

-- `obj` is the `IsNatural` subtype of the slice object on `pZ Z`.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) (Z : Iᵒᵖ ⥤ Type) :
    F.obj Z = { x : F.toSliceDomPFunctor.obj (PresheafDomPFunctorData.pZ Z)
      // F.IsNatural x } := rfl

-- `map` of the hand-built identity transformation is the identity, by
-- `map_id`. The identity transformation is hand-built (not `NatTrans.id`)
-- to stay choice-free.
example {I : Type} [Category I] (F : PresheafDomPFunctor I) (Z : Iᵒᵖ ⥤ Type) :
    F.map { app := fun i => 𝟙 (Z.obj i), naturality := fun _ _ _ => rfl } =
      (id : F.obj Z → F.obj Z) := F.map_id Z

-- The full bundle projects the inherited dom law and names a `J`-side law.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.RestrComp := F.isFunctorial.restr_comp
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J) :
    F.TagRestrComp := F.isFunctorial.tagRestr_comp

-- The output presheaf's fibre over `j` is the `t`-tagged subtype of the dom
-- functor's value on `Z`.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    (Z : Iᵒᵖ ⥤ Type) (j : J) :
    (F.objPresheaf Z).obj ⟨j⟩ =
      { z : F.toPresheafDomPFunctorData.obj Z // F.t z.1.1.1 = j } := rfl

-- The dom morphism map is natural with respect to `objPresheaf`'s
-- `J`-restriction: `map α` commutes with `objRestr g`, preserving the `t`-tag.
example {I J : Type} [Category I] [Category J] (F : PresheafPFunctor I J)
    {Z Z' : Iᵒᵖ ⥤ Type} (α : NatTrans Z Z') ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : F.toPresheafDomPFunctorData.obj Z) (htag : F.t x.1.1.1 = j) :
    F.toPresheafDomPFunctorData.map α (F.objRestr g x htag) =
      F.objRestr g (F.toPresheafDomPFunctorData.map α x) htag :=
  F.map_objRestr α g x htag

-- The preorder category on `Fin 2` has a genuine non-identity morphism.
example : ((0 : Fin 2) ⟶ 1) := homOfLE (by decide)

/-- In `Fin 2`, the unique position of shape `x` over base point `i` has
underlying value `i + x`: `x + (i + x) = i`. -/
private theorem fin2_add_idx (x i : Fin 2) : x + (i + x) = i := by omega

/-- A concrete presheaf polynomial functor over the preorder category on
`Fin 2` (for both index categories). Two shapes (`A := Fin 2`), tagged by
`t := id` so each shape lies over its own object, two positions per shape
(`B _ := Fin 2`), and constraint `s ⟨a, b⟩ = a + b`. Each fibre
`Position a i` is the singleton `{a + i}`, so `restr`, `tagRestr`, and
`reindex` each pick out the unique element of the target fibre.
`reindex` along the non-identity `0 ⟶ 1` retags shape `1` to shape `0` and
moves the underlying position value by `+1` (it is not value-preserving). -/
def presheafWitnessData : PresheafPFunctorData (Fin 2) (Fin 2) where
  A := Fin 2
  B := fun _ => Fin 2
  s := fun x => x.1 + x.2
  t := id
  restr := fun a {_i i'} _f _b => ⟨i' + a, fin2_add_idx a i'⟩
  tagRestr := fun {_j j'} _g _s => ⟨j', rfl⟩
  reindex := fun {_j _j'} _g a {i} _b => ⟨i + a.1, fin2_add_idx a.1 i⟩

/-- The constraint `s ⟨a, ·⟩ = a + ·` is injective, so each fibre
`Position a i` has at most one element. -/
private theorem fin2_pos_cancel (a x y i : Fin 2) (hx : a + x = i) (hy : a + y = i) :
    x = y := by omega

/-- Each position fibre of the witness is a singleton. -/
private instance posSubsingleton (a i : Fin 2) :
    Subsingleton (presheafWitnessData.toSliceDomPFunctor.Position a i) :=
  ⟨fun x y => Subtype.ext (fin2_pos_cancel a x.1 y.1 i x.2 y.2)⟩

/-- Each shape fibre of the witness is a singleton (the tag `t = id`
separates the two shapes). -/
private instance shapeSubsingleton (j : Fin 2) :
    Subsingleton (presheafWitnessData.toSlicePFunctor.Shape j) :=
  ⟨fun x y => Subtype.ext (by
    have hx : (x.1 : Fin 2) = j := x.2
    have hy : (y.1 : Fin 2) = j := y.2
    exact hx.trans hy.symm)⟩

/-- The witness, with all seven functor laws discharged. Because every
position fibre and shape fibre is a singleton, each law equates elements of
(functions into) a subsingleton, so `Subsingleton.elim` closes every goal;
in particular the `cast`-transport laws `reindex_id` / `reindex_comp` hold
without computing the transports. -/
def presheafWitness : PresheafPFunctor (Fin 2) (Fin 2) where
  toPresheafPFunctorData := presheafWitnessData
  isFunctorial :=
    { restr_id := by intro a i; funext b; exact Subsingleton.elim _ _
      restr_comp := by intro a i i' i'' f g; funext b; exact Subsingleton.elim _ _
      tagRestr_id := by intro j; funext s; exact Subsingleton.elim _ _
      tagRestr_comp := by intro j j' j'' g h; funext s; exact Subsingleton.elim _ _
      reindex_naturality := by intro j j' g a i i' f; funext b; exact Subsingleton.elim _ _
      reindex_id := by intro j a i b; exact Subsingleton.elim _ _
      reindex_comp := by intro j j' j'' g h a i b; exact Subsingleton.elim _ _ }

/-- The non-identity morphism `0 ⟶ 1` in the preorder category on `Fin 2`,
used by the computational examples. -/
private def h01 : (0 : Fin 2) ⟶ 1 := homOfLE (by decide)

-- The constraint leg computes as `a + b`.
example : presheafWitness.s ⟨(0 : Fin 2), (1 : Fin 2)⟩ = 1 := rfl
example : presheafWitness.s ⟨(1 : Fin 2), (1 : Fin 2)⟩ = 0 := rfl

-- The tag leg is the identity, so each shape lies over its own object.
example : presheafWitness.t (0 : Fin 2) = 0 := rfl
example : presheafWitness.t (1 : Fin 2) = 1 := rfl

-- `tagRestr` along the non-identity `0 ⟶ 1` retags shape `1` to shape `0`.
example : (presheafWitness.tagRestr h01 ⟨(1 : Fin 2), rfl⟩).1 = (0 : Fin 2) := rfl

-- `restr` along `0 ⟶ 1` sends the unique position of shape `0` over `1` to the
-- unique position over `0`.
example : (presheafWitness.restr (0 : Fin 2) h01 ⟨(1 : Fin 2), rfl⟩).1 = (0 : Fin 2) := rfl

-- `reindex` along `0 ⟶ 1` genuinely moves the underlying position value: the
-- position of value `0` over `i = 0` (for the retagged shape `0`) is reindexed
-- to the position of value `1` over `i = 0` (for shape `1`).
example :
    (presheafWitness.reindex h01 ⟨(1 : Fin 2), rfl⟩ (i := (0 : Fin 2)) ⟨(0 : Fin 2), rfl⟩).1 =
      (1 : Fin 2) := rfl

-- The output presheaf's fibre over `j` is the `t`-tagged subtype of `obj Z`.
example (Z : (Fin 2)ᵒᵖ ⥤ Type) :
    (presheafWitness.objPresheaf Z).obj ⟨(0 : Fin 2)⟩ =
      { z : presheafWitness.toPresheafDomPFunctorData.obj Z //
        presheafWitness.t z.1.1.1 = (0 : Fin 2) } :=
  rfl
