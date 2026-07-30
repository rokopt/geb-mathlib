/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinSetSkel.Basic
public import Geb.Mathlib.Logic.Equiv.Basic

/-!
# The initial and terminal objects, coproducts and products of `FinSetSkel`

The constructions of rows a, b, c and d over `Fin` and vectors,
together with the content of their universal properties, stated in
W1's application-normal form `f.toVec.get i`. The mathlib cones and
`Prop` instances built from them are in `Shapes/Instances.lean`; this
module is choice-free.

W1 exports the correspondence between morphisms and index functions
as the pair `ofIdxFun` / `toIdxFun` over
`ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)`, not as an `Equiv`
and not over bare index functions. `homEquivIdxFun` packages the two
round trips and removes both `ULift`s, so that a universal property
stated over index functions can be transported to one over morphisms.
Its domain transport is `Equiv.arrowCongrLeftC`; mathlib's
`Equiv.arrowCongr` and the `Equiv.piCongrLeft` family all depend on
`Classical.choice`.

## Main definitions

* `FinSetSkel.homEquivIdxFun` — morphisms as index functions.
* `FinSetSkel.point` — the morphism out of the one-element object
  picking a given index.
* `FinSetSkel.fromZero`, `FinSetSkel.toOne` — the canonical
  morphisms out of the empty and into the one-element object.
* `FinSetSkel.coprodObj`, `FinSetSkel.coprodInl`,
  `FinSetSkel.coprodInr`, `FinSetSkel.coprodDesc` — binary
  coproducts.
* `FinSetSkel.prodObj`, `FinSetSkel.prodFst`, `FinSetSkel.prodSnd`,
  `FinSetSkel.prodLift` — binary products.

## Main statements

* `FinSetSkel.fromZero_uniq`, `FinSetSkel.toOne_uniq` — initiality
  and terminality.
* `FinSetSkel.coprodInl_desc`, `FinSetSkel.coprodInr_desc`,
  `FinSetSkel.coprodDesc_uniq` — the coproduct's universal property.
* `FinSetSkel.prodLift_fst`, `FinSetSkel.prodLift_snd`,
  `FinSetSkel.prodLift_uniq` — the product's universal property.

## References

* [Freyd1972]

## Tags

finite sets, skeleton, coproduct, product, terminal, choice-free
-/

@[expose] public section

universe u

namespace FinSetSkel

variable {X Y : FinSetSkel.{u}}

/-- Morphisms as lifted index functions: W1's `ofIdxFun` and
`toIdxFun` as an equivalence. -/
def homEquivIdxFunU (X Y : FinSetSkel.{u}) :
    (X ⟶ Y) ≃ (ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)) where
  toFun := toIdxFun
  invFun := ofIdxFun
  left_inv := ofIdxFun_toIdxFun
  right_inv := toIdxFun_ofIdxFun

/-- Morphisms as index functions. -/
def homEquivIdxFun (X Y : FinSetSkel.{u}) :
    (X ⟶ Y) ≃ (Fin X.len → Fin Y.len) :=
  (homEquivIdxFunU X Y).trans
    ((Equiv.arrowCongrLeftC Equiv.ulift).trans
      (Equiv.piCongrRight fun _ ↦ Equiv.ulift))

/-- The index function of a morphism is its normal-form lookup. -/
@[simp] theorem homEquivIdxFun_apply (f : X ⟶ Y) (i : Fin X.len) :
    homEquivIdxFun X Y f i = f.toVec.get i := rfl

/-- The morphism of an index function looks up by that function. -/
@[simp] theorem homEquivIdxFun_symm_get
    (g : Fin X.len → Fin Y.len) (i : Fin X.len) :
    ((homEquivIdxFun X Y).symm g).toVec.get i = g i := by
  simp [homEquivIdxFun, homEquivIdxFunU, ofIdxFun_get, Equiv.arrowCongrLeftC]

/-- The unique morphism out of the empty object. -/
def fromZero (Y : FinSetSkel.{u}) : mk 0 ⟶ Y :=
  Hom.ofVec (Vector.ofFnC fun i ↦ i.elim0)

/-- Any morphism out of the empty object is the canonical one. -/
theorem fromZero_uniq {Y : FinSetSkel.{u}} (f : mk 0 ⟶ Y) :
    f = fromZero Y :=
  hom_ext fun i ↦ i.elim0

/-- The unique morphism into the one-element object. -/
def toOne (X : FinSetSkel.{u}) : X ⟶ mk 1 :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ 0)

/-- Any morphism into the one-element object is the canonical one. -/
theorem toOne_uniq {X : FinSetSkel.{u}} (f : X ⟶ mk 1) :
    f = toOne X :=
  hom_ext fun _ ↦ Subsingleton.elim _ _

/-- The morphism out of the one-element object picking an index. -/
def point {X : FinSetSkel.{u}} (i : Fin X.len) : mk 1 ⟶ X :=
  Hom.ofVec (Vector.ofFnC fun _ ↦ i)

/-- A point looks up the index it picks. -/
@[simp] theorem point_get {X : FinSetSkel.{u}} (i : Fin X.len)
    (t : Fin (mk 1 : FinSetSkel.{u}).len) : (point i).toVec.get t = i := by
  simp [point]

end FinSetSkel
