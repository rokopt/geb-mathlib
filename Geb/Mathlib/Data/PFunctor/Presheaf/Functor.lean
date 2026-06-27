/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic

/-!
# Presheaf-domain polynomial functors: categorical wrapper

Packages the constructive core (`Presheaf.Basic`) as a
`CategoryTheory.Functor` on the presheaf category `Iᵒᵖ ⥤ Type`. The
functor-category instance and the morphism-promotion notation `↾` are
`Classical.choice`-dependent, so this categorical packaging is kept in a
separate module from the choice-free core; the module
`Geb.Mathlib.Data.PFunctor.Presheaf.Functor` is on
`GebMeta.classicalAllowedModules`.

## Main definitions

* `PresheafDomPFunctorData.domFunctor` — the functor `(Iᵒᵖ ⥤ Type) ⥤ Type`.

## Implementation notes

`domFunctor` reuses the core `obj`/`map`. A functor-category hom
`h : Z ⟶ Z'` is definitionally a `CategoryTheory.NatTrans Z Z'`, the input
the core `map` expects, so `map` promotes the core `map` with `↾`; the
functor laws discharge by `ext` plus the core `map_id`/`map_comp`. Unlike
the slice wrapper there is no `Functor.toOver` shortcut: the codomain is a
plain type category, not an `Over` category.

## References

* M. Weber, *Familial 2-functors and parametric right adjoints*, 2007.
* N. Gambino and M. Hyland, *Wellfounded trees and dependent
  polynomial functors*, TYPES 2003.
* J. Kock, *Polynomial functors and polynomial monads*.

## Tags

polynomial functor, presheaf, parametric right adjoint, p.r.a.,
PFunctor, functor category
-/

public section

open CategoryTheory

universe uI uA uB uZ

namespace PresheafDomPFunctorData

/-- The functor `(Iᵒᵖ ⥤ Type) ⥤ Type` of a presheaf-domain polynomial
functor: the core `obj`/`map` packaged on the presheaf category. A
functor-category hom is definitionally the bare `NatTrans` the core `map`
consumes, and the functor laws come from the core `map_id`/`map_comp`. -/
@[expose] def domFunctor {I : Type uI} [Category I]
    (F : PresheafDomPFunctorData.{uI, uA, uB} I) :
    CategoryTheory.Functor (Iᵒᵖ ⥤ Type uZ) (Type (max uA uB uI uZ)) where
  obj Z := F.obj Z
  map {Z Z'} h := ↾(F.map h)
  map_id Z := by
    ext z
    exact congrFun (F.map_id Z) z
  map_comp f g := by
    ext z
    rfl

end PresheafDomPFunctorData
