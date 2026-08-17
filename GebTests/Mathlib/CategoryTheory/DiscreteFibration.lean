/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.DiscreteFibration
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Tests for discrete fibrations

A presheaf on the walking arrow (`Bool` as a preorder, `false ≤ true`)
exercises the category of elements over the base, the lifting data on its
projection, the fibre presheaf of that projection, and the round trips
between a discrete fibration and the category of elements of its fibre
presheaf.  The presheaf is constant, so restriction is the identity and
every equation below holds by `rfl`.

## Tags

discrete fibration, category of elements, fibre presheaf
-/

@[expose] public section

open CategoryTheory Opposite

/-- A presheaf on the walking arrow, constant at `Fin 3`.  Written out
rather than built with `Functor.const`, whose functor laws mathlib
discharges by classical automation. -/
def constPsh : Boolᵒᵖ ⥤ Type where
  obj _ := Fin 3
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A sample element over `true`. -/
def eltTrue : constPsh.CoElements := Functor.CoElements.mk true (2 : Fin 3)

/-- The base of `eltTrue`. -/
theorem eltTrue_base : eltTrue.base = true := rfl

/-- The element carried by `eltTrue`. -/
theorem eltTrue_elt : eltTrue.elt = (2 : Fin 3) := rfl

/-- The unique morphism `false ⟶ true` of the walking arrow. -/
def arrow : (false : Bool) ⟶ true := homOfLE (by decide)

/-- The lifting data on the projection computes the source of the lift of
`arrow` with codomain `eltTrue`: the element restricts to itself, so the
source is `2` over `false`. -/
theorem src_arrow :
    (Functor.CoElements.discreteFibration constPsh).src
        (C := constPsh.CoElements) (c := eltTrue) arrow =
      Functor.CoElements.mk false (2 : Fin 3) :=
  rfl

/-- The projection sends the lift of `arrow` back to `arrow`. -/
theorem homBase_hom_arrow :
    Functor.CoElements.homBase
        ((Functor.CoElements.discreteFibration constPsh).hom
          (c := eltTrue) arrow) =
      arrow :=
  rfl

/-- The lifting data of the projection, named for reuse below. -/
def constDisc : DiscreteFibration (Functor.CoElements.π constPsh) :=
  Functor.CoElements.discreteFibration constPsh

/-- Restriction in the fibre presheaf of the projection is the identity on
the underlying element, the presheaf being constant. -/
theorem restrict_arrow (c : (Functor.CoElements.π constPsh).Fiber true) :
    (constDisc.restrict arrow c).1 =
      Functor.CoElements.mk false c.1.elt :=
  rfl

/-- The fibre of the projection over `b` is in bijection with the value of
the presheaf at `b`, and the bijection reads off the element. -/
theorem fiberPresheafEquiv_apply
    (c : (Functor.CoElements.π constPsh).Fiber true) :
    Functor.CoElements.fiberPresheafEquiv constPsh true c = c.1.elt :=
  rfl

/-- `toElements` records an object of the total category together with its
image in the base. -/
theorem toElements_obj_eltTrue :
    constDisc.toElements.obj eltTrue =
      Functor.CoElements.mk (F := constDisc.fiberPresheaf) eltTrue.base
        ⟨eltTrue, rfl⟩ :=
  rfl

/-- `ofElements` undoes `toElements` on objects. -/
theorem ofElements_obj_toElements_obj_eltTrue :
    constDisc.ofElements.obj (constDisc.toElements.obj eltTrue) = eltTrue :=
  rfl

/-- Both functors lie over the base. -/
theorem π_toElements_obj_eltTrue :
    (Functor.CoElements.π constDisc.fiberPresheaf).obj
        (constDisc.toElements.obj eltTrue) =
      (Functor.CoElements.π constPsh).obj eltTrue :=
  rfl

/-- The lift of `arrow` is cartesian, so the projection is a fibred
category in mathlib's sense. -/
theorem isFibered_π : (Functor.CoElements.π constPsh).IsFibered :=
  constDisc.isFibered

/-- The projection is a discrete fibration in the pullback sense too. -/
theorem isDiscreteFibration_π_constPsh :
    IsDiscreteFibration (Functor.CoElements.π constPsh) :=
  Functor.CoElements.isDiscreteFibration_π constPsh
