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

end CategoryTheory
