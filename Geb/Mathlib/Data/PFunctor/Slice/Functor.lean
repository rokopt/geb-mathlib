/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Slice polynomial functors: categorical wrapper

Packages the constructive core (`Slice.Basic`) as a
`CategoryTheory.Functor` between `Over` categories. mathlib's `Over` is
`Classical.choice`-dependent at the type level, so this categorical
packaging is kept in a separate module from the choice-free core.

## Main definitions

* `SliceDomPFunctor.domFunctor` — the functor `Over dom ⥤ Type`.
* `SlicePFunctor.functor` — the functor `Over dom ⥤ Over cod`.

## Implementation notes

`domFunctor` reuses the core `obj`/`map`; `Over` structure maps are
read through `ConcreteCategory.hom`, the slice-morphism hypothesis is
derived from `Over.w`, results promoted with `↾`, and the `TypeCat.Hom`
laws discharged by `ext` plus the core `map_id`/`map_comp`. `functor`
is the `Functor.toOver` lift along the tag `t`.

## References

* N. Gambino and M. Hyland, *Wellfounded trees and dependent
  polynomial functors*, TYPES 2003.
* J. Kock, *Polynomial functors and polynomial monads*.

## Tags

polynomial functor, slice category, Over, container, PFunctor
-/

public section

universe uA uB uD

open CategoryTheory

namespace SliceDomPFunctor

/-- The functor `Over dom ⥤ Type` restricting the `PFunctor`
interpretation to `s`-compatible assignments; the core maps packaged
over `Over dom`. -/
@[expose] def domFunctor {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) :
    CategoryTheory.Functor (Over dom) (Type (max uA uB uD)) where
  obj Y := F.obj (ConcreteCategory.hom Y.hom)
  map {Y Z} h := ↾(F.map (ConcreteCategory.hom h.left) (by
    funext z
    rw [Function.comp_apply, ← ConcreteCategory.comp_apply, Over.w h]))
  map_id Y := by
    ext z
    exact congrFun (F.map_id _) z
  map_comp f g := by
    ext z
    rfl

end SliceDomPFunctor

namespace SlicePFunctor

/-- Tag naturality: `domFunctor.map g` fixes the shape component, so
post-composing with the `t`-tag is preserved. This is the
`Functor.toOver` triangle obligation for `functor`, shared with
`functor_comp_forget`. -/
private theorem tagTriangle {dom : Type uD} {cod : Type (max uA uB uD)}
    (F : SlicePFunctor.{uA, uB, uD, max uA uB uD} dom cod)
    {Y Z : Over dom} (g : Y ⟶ Z) :
    F.toSliceDomPFunctor.domFunctor.map g ≫ (↾fun z => F.t z.1.1) =
      (↾fun z => F.t z.1.1) := by
  ext z
  exact congrArg F.t (F.toSliceDomPFunctor.map_fst (ConcreteCategory.hom g.left)
    (by funext w; rw [Function.comp_apply, ← ConcreteCategory.comp_apply,
      Over.w g]) z)

/-- The slice polynomial functor `Over dom ⥤ Over cod`: the
`Functor.toOver` lift of `domFunctor` along the tag leg `t`. -/
def functor {dom : Type uD} {cod : Type (max uA uB uD)}
    (F : SlicePFunctor.{uA, uB, uD, max uA uB uD} dom cod) :
    CategoryTheory.Functor (Over dom) (Over cod) :=
  Functor.toOver F.toSliceDomPFunctor.domFunctor cod
    (fun _ => ↾(fun z => F.t z.1.1))
    (by intro Y Z g; exact F.tagTriangle g)

/-- The wrapper forgets back to `domFunctor`. -/
theorem functor_comp_forget {dom : Type uD} {cod : Type (max uA uB uD)}
    (F : SlicePFunctor.{uA, uB, uD, max uA uB uD} dom cod) :
    F.functor ⋙ Over.forget cod = F.toSliceDomPFunctor.domFunctor := by
  rw [functor]
  apply Functor.toOver_comp_forget

end SlicePFunctor
