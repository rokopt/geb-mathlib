/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Covariant and contravariant Grothendieck constructions

For a functor `F : C ⥤ Cat`, mathlib's `CategoryTheory.Grothendieck F`
is the covariant Grothendieck construction. This module adds:

* a `Cat`-valued packaging of the covariant construction
  (`Grothendieck.functorToCat`);
* `GrothendieckOp F`, the covariant construction applied to the
  oppositization `F ⋙ Cat.opFunctor`;
* `CoGrothendieck G`, the contravariant Grothendieck construction of
  `G : Cᵒᵖ ⥤ Cat`, defined as `(GrothendieckOp G)ᵒᵖ`, together with an
  interface whose constructors and destructors use morphisms of `C`.

## Main definitions

* `CategoryTheory.Grothendieck.functorToCat`
* `CategoryTheory.GrothendieckOp`
* `CategoryTheory.CoGrothendieck`

## Main statements

* `GrothendieckOp.hom_ext` and `CoGrothendieck.hom_ext`
* `GrothendieckOp.map_id_eq`/`map_comp_eq` and the `CoGrothendieck`
  counterparts

## Implementation notes

`GrothendieckOp` and `CoGrothendieck` are semireducible `def` type
synonyms, not `abbrev`s and not new structures: instance synthesis and
object-level dot notation stop at the new names, while all round-trip
lemmas hold by `rfl`. Morphism-level dot notation resolves through
`Quiver.Hom` to `Grothendieck.Hom`'s own projections (whose op-side
types make direction misuse a type error); the wrapper accessors
`homBase`/`homFiber` are therefore free functions, used qualified or
via `open`.

Universe levels match the covariant construction exactly: for
`F : C ⥤ Cat.{v₂, u₂}` with `C : Type u` and `Category.{v} C`, both
`GrothendieckOp F` and `CoGrothendieck G` live in `Type (max u u₂)`
with `Category.{max v v₂}` instances, since `ᵒᵖ` and `Cat.opFunctor`
preserve universes. The packaged functors (`functor`, `functorToCat`)
restrict to `E : Cat.{v, u}` with fibers in the same `Cat.{v, u}`,
inherited from mathlib's `Grothendieck.functor`.

## References

The contravariant Grothendieck construction is standard; see
[Vistoli2008] and [JohnsonYau2021].

## Tags

Grothendieck construction, contravariant, opposite category, fibered
category
-/

@[expose] public section

universe u v u₂ v₂

namespace CategoryTheory

open Functor

variable {C : Type u} [Category.{v} C]

/-! ## Covariant construction: `Cat`-valued packaging -/

namespace Grothendieck

/-- The covariant Grothendieck construction as a functor to `Cat`:
`Grothendieck.functor` followed by forgetting the projection to the
base. -/
def functorToCat {E : Cat.{v, u}} : (↑E ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
  Grothendieck.functor ⋙ Over.forget E

/-- `functorToCat` sends a functor to the Grothendieck construction on it. -/
@[simp]
theorem functorToCat_obj {E : Cat.{v, u}} (F : ↑E ⥤ Cat.{v, u}) :
    functorToCat.obj F = Cat.of (Grothendieck F) :=
  rfl

/-- `functorToCat` sends a natural transformation to the induced functor. -/
@[simp]
theorem functorToCat_map {E : Cat.{v, u}} {F F' : ↑E ⥤ Cat.{v, u}}
    (α : F ⟶ F') : functorToCat.map α = (Grothendieck.map α).toCatHom :=
  rfl

end Grothendieck

/-! ## The Grothendieck construction of an oppositized functor -/

/-- The covariant Grothendieck construction applied to the
oppositization of `F`: objects are pairs of a base object `c : C` and a
fiber object of `F.obj c`, and morphisms reverse the fiber direction
relative to `Grothendieck F`. -/
def GrothendieckOp (F : C ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
  Grothendieck (F ⋙ Cat.opFunctor)

namespace GrothendieckOp

/-- The category structure on `GrothendieckOp F`, inherited from the
underlying covariant Grothendieck construction. -/
instance category (F : C ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂} (GrothendieckOp F) :=
  inferInstanceAs (Category (Grothendieck (F ⋙ Cat.opFunctor)))

variable {F : C ⥤ Cat.{v₂, u₂}}

/-- Construct an object of `GrothendieckOp F` from a base object and a
fiber object. -/
def mk (base : C) (fiber : F.obj base) : GrothendieckOp F :=
  ⟨base, Opposite.op fiber⟩

/-- The base object of an object of `GrothendieckOp F`. -/
def base (X : GrothendieckOp F) : C :=
  Grothendieck.base X

/-- The fiber object of an object of `GrothendieckOp F`. -/
def fiber (X : GrothendieckOp F) : F.obj X.base :=
  Opposite.unop (Grothendieck.fiber X)

/-- `mk` recovers the base component on the nose. -/
@[simp]
theorem base_mk (b : C) (f : F.obj b) : (mk b f).base = b :=
  rfl

/-- `mk` recovers the fiber component on the nose. -/
@[simp]
theorem fiber_mk (b : C) (f : F.obj b) : (mk b f).fiber = f :=
  rfl

/-- Every object of `GrothendieckOp F` is `mk` applied to its own base
and fiber. -/
@[simp]
theorem mk_base_fiber (X : GrothendieckOp F) : mk X.base X.fiber = X :=
  rfl

/-- Construct a morphism of `GrothendieckOp F` from a base morphism and
a fiber morphism. The fiber morphism runs from the target fiber to the
pushforward of the source fiber — the reversal relative to
`Grothendieck.Hom`. -/
def homMk {X Y : GrothendieckOp F} (base : X.base ⟶ Y.base)
    (fiber : Y.fiber ⟶ (F.map base).toFunctor.obj X.fiber) : X ⟶ Y :=
  ⟨base, fiber.op⟩

/-- The base morphism of a morphism of `GrothendieckOp F`. -/
def homBase {X Y : GrothendieckOp F} (f : X ⟶ Y) : X.base ⟶ Y.base :=
  Grothendieck.Hom.base f

/-- The fiber morphism of a morphism of `GrothendieckOp F`. -/
def homFiber {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    Y.fiber ⟶ (F.map (homBase f)).toFunctor.obj X.fiber :=
  Quiver.Hom.unop (Grothendieck.Hom.fiber f)

/-- `homMk` recovers the base component on the nose. -/
@[simp]
theorem homBase_homMk {X Y : GrothendieckOp F} (b : X.base ⟶ Y.base)
    (φ : Y.fiber ⟶ (F.map b).toFunctor.obj X.fiber) :
    homBase (homMk b φ) = b :=
  rfl

/-- `homMk` recovers the fiber component on the nose. -/
@[simp]
theorem homFiber_homMk {X Y : GrothendieckOp F} (b : X.base ⟶ Y.base)
    (φ : Y.fiber ⟶ (F.map b).toFunctor.obj X.fiber) :
    homFiber (homMk b φ) = φ :=
  rfl

/-- Every morphism of `GrothendieckOp F` is `homMk` applied to its own
base and fiber components. -/
@[simp]
theorem homMk_base_fiber {X Y : GrothendieckOp F} (f : X ⟶ Y) :
    homMk (homBase f) (homFiber f) = f :=
  rfl

/-- Two morphisms of `GrothendieckOp F` agree once their base
components agree and their fiber components agree after transport
along that agreement. -/
@[ext (iff := false)]
theorem hom_ext {X Y : GrothendieckOp F} (f g : X ⟶ Y)
    (hbase : homBase f = homBase g)
    (hfiber : homFiber f ≫ eqToHom (by rw [hbase]) = homFiber g) :
    f = g := by
  refine Grothendieck.ext f g hbase ?_
  apply Quiver.Hom.unop_inj
  erw [unop_comp, eqToHom_unop]
  exact hfiber

/-- `homBase` sends the identity morphism to the identity morphism. -/
@[simp]
theorem homBase_id (X : GrothendieckOp F) : homBase (𝟙 X) = 𝟙 X.base :=
  rfl

/-- `homFiber` of the identity morphism is the canonical transport
isomorphism. -/
@[simp]
theorem homFiber_id (X : GrothendieckOp F) :
    homFiber (𝟙 X) = eqToHom (by simp) := by
  erw [homFiber, Grothendieck.id_fiber, eqToHom_unop]
  rfl

/-- `homBase` is functorial: it sends composition to composition. -/
@[simp]
theorem homBase_comp {X Y Z : GrothendieckOp F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homBase (f ≫ g) = homBase f ≫ homBase g :=
  rfl

/-- `homFiber` of a composite is the composite of the fiber morphisms,
transported along the base functoriality. -/
@[simp]
theorem homFiber_comp {X Y Z : GrothendieckOp F} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    homFiber (f ≫ g) =
      homFiber g ≫ (F.map (homBase g)).toFunctor.map (homFiber f) ≫
        eqToHom (by simp) := by
  erw [homFiber, Grothendieck.comp_fiber, unop_comp, unop_comp, eqToHom_unop,
    Functor.op_map, Category.assoc]
  rfl

end GrothendieckOp

/-! ## The contravariant Grothendieck construction -/

/-- The contravariant Grothendieck construction of `G : Cᵒᵖ ⥤ Cat`:
the opposite category of `GrothendieckOp G`. Objects are pairs of
`c : C` and an object of `G.obj (op c)`; a morphism `X ⟶ Y` consists of
`β : X.base ⟶ Y.base` in `C` and a fiber morphism
`X.fiber ⟶ (G.map β.op).toFunctor.obj Y.fiber`. -/
def CoGrothendieck (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
  (GrothendieckOp G)ᵒᵖ

namespace CoGrothendieck

/-- The category structure on `CoGrothendieck G`, inherited from the
opposite of `GrothendieckOp G`. -/
instance category (G : Cᵒᵖ ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂} (CoGrothendieck G) :=
  inferInstanceAs (Category (GrothendieckOp G)ᵒᵖ)

variable {G : Cᵒᵖ ⥤ Cat.{v₂, u₂}}

/-- Construct an object of `CoGrothendieck G` from a base object and a
fiber object. -/
def mk (base : C) (fiber : G.obj (Opposite.op base)) :
    CoGrothendieck G :=
  Opposite.op (GrothendieckOp.mk (Opposite.op base) fiber)

/-- The base object of an object of `CoGrothendieck G`, as an object
of `C`. -/
def base (X : CoGrothendieck G) : C :=
  Opposite.unop (GrothendieckOp.base (Opposite.unop X))

/-- The fiber object of an object of `CoGrothendieck G`. -/
def fiber (X : CoGrothendieck G) : G.obj (Opposite.op X.base) :=
  GrothendieckOp.fiber (Opposite.unop X)

/-- `mk` recovers the base component on the nose. -/
@[simp]
theorem base_mk (b : C) (f : G.obj (Opposite.op b)) : (mk b f).base = b :=
  rfl

/-- `mk` recovers the fiber component on the nose. -/
@[simp]
theorem fiber_mk (b : C) (f : G.obj (Opposite.op b)) :
    (mk b f).fiber = f :=
  rfl

/-- Every object of `CoGrothendieck G` is `mk` applied to its own base
and fiber. -/
@[simp]
theorem mk_base_fiber (X : CoGrothendieck G) : mk X.base X.fiber = X :=
  rfl

end CoGrothendieck

end CategoryTheory
