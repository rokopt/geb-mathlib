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
`Data.PFunctor.Presheaf.Functor` is on
`GebMeta.classicalAllowedModules`.

## Main definitions

* `PresheafDomPFunctorData.domFunctor` — the functor `(Iᵒᵖ ⥤ Type) ⥤ Type`.
* `PresheafPFunctor.functor` — the functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`.

## Main statements

* `PresheafPFunctor.functor_obj` / `functor_map` — the categorical functor's
  object and morphism maps are the choice-free core `objPresheaf` and dom
  `map`.

## Implementation notes

`domFunctor` reuses the core `obj`/`map`. A functor-category hom
`h : Z ⟶ Z'` is definitionally a `CategoryTheory.NatTrans Z Z'`, the input
the core `map` expects, so `map` promotes the core `map` with `↾`; the
functor laws discharge by `ext` plus the core `map_id`/`map_comp`. Unlike
the slice wrapper there is no `Functor.toOver` shortcut: the codomain is a
plain type category, not an `Over` category.

`functor` assembles directly: its object map is `objPresheaf`, and its
morphism map carries a functor-category hom `α` to the natural transformation
whose component over `j` is the dom `map α` restricted to the `t`-tagged fibre
(the dom map preserves the tag, so it restricts). Each component's naturality
with respect to `objPresheaf`'s restriction maps is `map_objRestr`; the outer
functor laws come from the dom `map_id` / `map_comp`. There is no `Functor.toOver`
analogue for presheaf codomains. The morphism universes of `I` and `J` are
named so the input presheaf's value universe and the `PresheafPFunctor` arity
universes pin the output presheaf's value universe explicitly.

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

universe uI uJ uA uB uZ vI vJ

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

namespace PresheafPFunctor

/-- The presheaf polynomial functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)` of `F`: its
object map is the choice-free output presheaf `objPresheaf`, and its morphism
map carries a functor-category hom `α` to the natural transformation whose
component over `j` is the dom `map α` restricted to the `t`-tagged fibre. Each
component's naturality is `map_objRestr`; the functor laws come from the dom
`map_id` / `map_comp`. -/
@[expose] def functor {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, vI, vJ, uA, uB} I J) :
    CategoryTheory.Functor (Iᵒᵖ ⥤ Type uZ) (Jᵒᵖ ⥤ Type (max uI uZ uA uB)) where
  obj Z := F.objPresheaf Z
  map {Z Z'} α :=
    { app := fun X => ↾ (fun w => (⟨F.toPresheafDomPFunctorData.map α w.1, w.2⟩ :
        (F.objPresheaf Z').obj X))
      naturality := fun _ _ g => by
        ext w
        exact Subtype.ext (F.map_objRestr α g.unop w.1 w.2) }
  map_id Z := by
    ext j w
    exact Subtype.ext (congrFun (F.toPresheafDomPFunctorData.map_id Z) w.1)
  map_comp α β := by
    ext j w
    exact Subtype.ext (congrFun (F.toPresheafDomPFunctorData.map_comp α β) w.1)

/-- `functor.obj` is the choice-free output presheaf `objPresheaf`. The
categorical object map carries no data beyond the constructive core. -/
theorem functor_obj {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, vI, vJ, uA, uB} I J) (Z : Iᵒᵖ ⥤ Type uZ) :
    F.functor.obj Z = F.objPresheaf Z :=
  rfl

/-- `functor.map`'s component over `j`, applied to a `t`-tagged fibre element,
retags the dom `map` of the underlying element: its underlying dom value is the
dom `map α` of the input's. -/
theorem functor_map {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, vI, vJ, uA, uB} I J) {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (α : Z ⟶ Z') (X : Jᵒᵖ) (w : (F.functor.obj Z).obj X) :
    (F.functor.map α).app X w =
      (⟨F.toPresheafDomPFunctorData.map α w.1, w.2⟩ : (F.functor.obj Z').obj X) :=
  rfl

end PresheafPFunctor
