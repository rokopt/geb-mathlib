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
functor-category packaging — constructing `CategoryTheory.Functor` objects
over presheaf categories and discharging their laws — is
`Classical.choice`-dependent, so this packaging is kept in a separate
module from the choice-free core; the module
`Data.PFunctor.Presheaf.Functor` is on
`GebMeta.classicalAllowedModules`. The notation `↾` (`TypeCat.ofHom`) is
choice-free: `objPresheaf` uses `↾` and is `{propext, Quot.sound}`.

## Main definitions

* `PresheafDomPFunctorData.domFunctor` — the functor `(Iᵒᵖ ⥤ Type) ⥤ Type`.
* `PresheafPFunctor.functor` — the functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`.

## Main statements

* `PresheafPFunctor.functor_obj` / `functor_map` — the categorical functor's
  object map is the core `objPresheaf`, and its morphism map is the
  dom `map` retagged onto the `t`-tagged fibre.

## Implementation notes

`domFunctor` reuses the core `obj`/`map`. A functor-category hom
`h : Z ⟶ Z'` is definitionally a `CategoryTheory.NatTrans Z Z'`, the input
the core `map` expects, so `map` promotes the core `map` with `↾`; the
identity law discharges by `ext` and the core `map_id`, and the composition
law by `ext` and `rfl`. Unlike the slice wrapper there is no `Functor.toOver`
shortcut: the codomain is a plain type category, not an `Over` category.

`functor` assembles directly: its object map is `objPresheaf`, and its morphism
map is the core `mapPresheaf` — the natural transformation a
functor-category hom `α` induces, whose component is the dom `map α` restricted
to the `t`-tagged fibre (the dom map preserves the tag, so it restricts), with
naturality `map_objRestr`. The outer functor laws come from the dom
`map_id` / `map_comp`. There is no `Functor.toOver`
analogue for presheaf codomains. The morphism universes of `I` and `J` are
named (`vI`, `vJ`) so the input presheaf's value universe `uZ` and the
`PresheafPFunctor` arity universes `uA` / `uB` pin the output presheaf's value
universe `max uI uZ uA uB` explicitly.

## References

* [Weber2007]
* [GambinoHyland2004]
* [GambinoKock2013]

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
consumes; the identity law comes from the core `map_id`, the composition law
by `rfl`. -/
@[expose] def domFunctor {I : Type uI} [Category I]
    (F : PresheafDomPFunctorData.{uI, uA, uB} I) :
    CategoryTheory.Functor (Iᵒᵖ ⥤ Type uZ) (Type (max uI uZ uA uB)) where
  obj Z := F.obj Z
  map {Z Z'} h := ↾(F.map h)
  map_id Z := by
    ext z
    exact congrFun (F.map_id Z) z
  map_comp _ _ := rfl

end PresheafDomPFunctorData

namespace PresheafPFunctor

/-- The presheaf polynomial functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)` of `F`: its
object map is the output presheaf `objPresheaf`, and its morphism map
is `mapPresheaf` (the induced presheaf morphism). The functor
laws come from the dom `map_id` / `map_comp`. -/
@[expose] def functor {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    CategoryTheory.Functor (Iᵒᵖ ⥤ Type uZ) (Jᵒᵖ ⥤ Type (max uI uZ uA uB)) where
  obj Z := F.objPresheaf Z
  map {Z Z'} α := F.mapPresheaf α
  map_id Z := by
    ext j w
    exact Subtype.ext (congrFun (F.toPresheafDomPFunctorData.map_id Z) w.1)
  map_comp α β := by
    ext j w
    exact Subtype.ext (congrFun (F.toPresheafDomPFunctorData.map_comp α β) w.1)

/-- `functor.obj` is the output presheaf `objPresheaf`. The
categorical object map carries no data beyond the core. -/
theorem functor_obj {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (Z : Iᵒᵖ ⥤ Type uZ) :
    F.functor.obj Z = F.objPresheaf Z :=
  rfl

/-- `functor.map`'s component over `j`, applied to a `t`-tagged fibre element,
retags the dom `map` of the underlying element: its underlying dom value is the
dom `map α` of the input's. -/
theorem functor_map {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (α : Z ⟶ Z') (X : Jᵒᵖ) (w : (F.functor.obj Z).obj X) :
    (F.functor.map α).app X w =
      (⟨F.toPresheafDomPFunctorData.map α w.1, w.2⟩ : (F.functor.obj Z').obj X) :=
  rfl

end PresheafPFunctor
