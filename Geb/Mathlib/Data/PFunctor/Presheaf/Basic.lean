/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Presheaf-domain polynomial functors (constructive core)

A presheaf-domain polynomial functor extends a `SliceDomPFunctor` on the
objects of a category `I` with a contravariant `I`-action on arities: for
each shape `a`, the assignment `i ↦ Position a i` extends to a presheaf on
`I` via a restriction map `restr a f`. This file is the p.r.a. (parametric
right adjoint) construction restricted to the domain side; the full
categorical packaging appears in sibling modules.

The design uses the option-(A) fibre encoding: positions over `i` are
`SliceDomPFunctor.Position a i = Subtype (PositionOver a i)`, the fibre of
the constraint leg `sCurried a` over `i`. The `restr` field reindexes these
fibres contravariantly.

## Main definitions

* `PresheafDomPFunctorData` — the operations: a `SliceDomPFunctor` with a
  restriction map `restr`.
* `PresheafDomPFunctorData.RestrId` / `RestrComp` — named law `Prop`s.
* `PresheafDomPFunctorData.IsFunctorial` — the functor laws bundled.
* `PresheafDomPFunctorData.pZ` — the total-space projection of a presheaf.
* `PresheafDomPFunctorData.comp` — the cast `Z`-component a slice element
  assigns to a position over `i`.
* `PresheafDomPFunctorData.IsNatural` — naturality of the position
  assignment with respect to `restr` and `Z.map`.
* `PresheafDomPFunctorData.obj` — the functor's value on a presheaf `Z`.
* `PresheafDomPFunctor` — the bundle: operations with a functoriality proof.

## Implementation notes

`PresheafDomPFunctorData` uses `extends SliceDomPFunctor.{uA, uB} I` with
pinned universes (load-bearing for a later diamond via `PresheafDomPFunctor`
and `SlicePFunctor`). The `linter.checkUnivs false` option and
`@[nolint checkUnivs]` suppress the auto-bound morphism-universe warning
that arises from `[Category I]`.

## References

* M. Weber, *Familial 2-functors and parametric right adjoints*, 2007.
* nLab, *Parametric right adjoint*.
* N. Gambino and M. Hyland, *Wellfounded trees and dependent
  polynomial functors*, TYPES 2003.
* J. Kock, *Polynomial functors and polynomial monads*.

## Tags

polynomial functor, presheaf, parametric right adjoint, p.r.a.,
PFunctor, restriction map
-/

public section

open CategoryTheory

universe uI uA uB uZ

set_option linter.checkUnivs false in
/-- Operations of a presheaf-domain polynomial functor over `I`: a
`SliceDomPFunctor` on `I`'s objects, with the contravariant `I`-action
`restr` making each arity a presheaf on `I`. -/
@[nolint checkUnivs]
structure PresheafDomPFunctorData (I : Type uI) [Category I] : Type _
    extends SliceDomPFunctor.{uA, uB} I where
  /-- The arity-presheaf restriction: for `f : i' ⟶ i`, reindex
  positions of shape `a` over `i` to positions over `i'`. -/
  restr : ∀ (a : toPFunctor.A) ⦃i i' : I⦄, (i' ⟶ i) →
      toSliceDomPFunctor.Position a i → toSliceDomPFunctor.Position a i'

namespace PresheafDomPFunctorData

/-- `restr` preserves identities. -/
def RestrId {I : Type uI} [Category I] (F : PresheafDomPFunctorData I) : Prop :=
  ∀ (a : F.A) (i : I), F.restr a (𝟙 i) = id

/-- `restr` is contravariant in `I`. -/
def RestrComp {I : Type uI} [Category I] (F : PresheafDomPFunctorData I) : Prop :=
  ∀ (a : F.A) ⦃i i' i'' : I⦄ (f : i' ⟶ i) (g : i'' ⟶ i'),
      F.restr a (g ≫ f) = F.restr a g ∘ F.restr a f

/-- The arities form presheaves on `I`: `restr` satisfies the functor
laws. -/
structure IsFunctorial {I : Type uI} [Category I]
    (F : PresheafDomPFunctorData I) : Prop where
  /-- Identity law for `restr`. -/
  restr_id : F.RestrId
  /-- Composition law for `restr`. -/
  restr_comp : F.RestrComp

/-- Total-space projection of a presheaf `Z` on `I` to objects of `I`. -/
@[expose] def pZ {I : Type uI} [Category I] (Z : Iᵒᵖ ⥤ Type uZ) :
    (Σ i : I, Z.obj ⟨i⟩) → I :=
  Sigma.fst

/-- The `Z`-component a slice element `x` over `pZ Z` assigns to a position
`b` of shape `x.1.1` over `i`: the `Z`-value `(x.1.2 b.1).2`, cast along the
compatibility of `x` and the constraint condition on `b` to `Z.obj ⟨i⟩`. -/
@[expose] def comp {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    {Z : Iᵒᵖ ⥤ Type uZ} (x : F.toSliceDomPFunctor.obj (pZ Z)) ⦃i : I⦄
    (b : F.toSliceDomPFunctor.Position x.1.1 i) : Z.obj ⟨i⟩ :=
  cast (congrArg (fun k : I => Z.obj ⟨k⟩)
    (((F.compatible_iff (pZ Z) x.1.1 x.1.2).mp x.2 b.1).trans b.2)) (x.1.2 b.1).2

/-- The position-assignment of `x` is a natural transformation `E_T(a) ⟶ Z`:
for every `f : i' ⟶ i` and position `b` over `i`, the component assigned to
`restr a f b` equals `Z.map f.op` applied to the component assigned to `b`. -/
@[expose] def IsNatural {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    {Z : Iᵒᵖ ⥤ Type uZ} (x : F.toSliceDomPFunctor.obj (pZ Z)) : Prop :=
  ∀ ⦃i i' : I⦄ (f : i' ⟶ i) (b : F.toSliceDomPFunctor.Position x.1.1 i),
    F.comp x (F.restr x.1.1 f b) = Z.map f.op (F.comp x b)

/-- The value of the presheaf-domain functor on `Z`: the `IsNatural` subtype
of the slice object on the total-space projection `pZ Z`. -/
@[expose] def obj {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    (Z : Iᵒᵖ ⥤ Type uZ) : Type _ :=
  { x : F.toSliceDomPFunctor.obj (pZ Z) // F.IsNatural x }

/-- A component of a natural transformation commutes with the reindexing
`cast` along an equality of base points. -/
private theorem app_cast {I : Type uI} [Category I] {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (α : CategoryTheory.NatTrans Z Z') {k i : I} (e : k = i) (z : Z.obj ⟨k⟩) :
    cast (congrArg (fun k : I => Z'.obj ⟨k⟩) e) (α.app ⟨k⟩ z) =
      α.app ⟨i⟩ (cast (congrArg (fun k : I => Z.obj ⟨k⟩) e) z) := by
  cases e
  rfl

/-- The `Z'`-component the image under `α` of a slice element assigns to a
position is `α.app` of the `Z`-component the original assigns to it. -/
private theorem comp_map {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    {Z Z' : Iᵒᵖ ⥤ Type uZ} (α : CategoryTheory.NatTrans Z Z')
    (x : F.toSliceDomPFunctor.obj (pZ Z)) ⦃i : I⦄
    (b : F.toSliceDomPFunctor.Position (F.toSliceDomPFunctor.map (p' := pZ Z')
      (fun p : Σ i : I, Z.obj ⟨i⟩ => (⟨p.1, α.app ⟨p.1⟩ p.2⟩ : Σ i : I, Z'.obj ⟨i⟩)) rfl x).1.1 i) :
    F.comp (F.toSliceDomPFunctor.map (p' := pZ Z')
      (fun p : Σ i : I, Z.obj ⟨i⟩ => (⟨p.1, α.app ⟨p.1⟩ p.2⟩ : Σ i : I, Z'.obj ⟨i⟩)) rfl x) b =
      α.app ⟨i⟩ (F.comp x b) :=
  app_cast α (((F.compatible_iff (pZ Z) x.1.1 x.1.2).mp x.2 b.1).trans b.2) _

/-- Action on a morphism of input presheaves (the bare `NatTrans`, not
the functor-category hom, to stay choice-free). -/
@[expose] def map {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    {Z Z' : Iᵒᵖ ⥤ Type uZ} (α : CategoryTheory.NatTrans Z Z') :
    F.obj Z → F.obj Z' :=
  fun x => ⟨F.toSliceDomPFunctor.map
    (fun p : Σ i : I, Z.obj ⟨i⟩ => (⟨p.1, α.app ⟨p.1⟩ p.2⟩ : Σ i : I, Z'.obj ⟨i⟩)) rfl x.1, by
    intro i i' f b
    rw [comp_map F α x.1, comp_map F α x.1]
    refine (congrArg (fun w => α.app ⟨i'⟩ w) (x.2 f b)).trans ?_
    simp only [← ConcreteCategory.comp_apply]
    rw [α.naturality f.op]⟩

/-- Functoriality in the input presheaf: the identity transformation acts as
the identity. -/
theorem map_id {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    (Z : Iᵒᵖ ⥤ Type uZ) :
    F.map { app := fun i => 𝟙 (Z.obj i), naturality := fun _ _ _ => rfl } =
      (id : F.obj Z → F.obj Z) := by
  funext x
  exact Subtype.ext (congrFun (F.toSliceDomPFunctor.map_id (pZ Z)) x.1)

/-- Functoriality in the input presheaf: the vertical composite of
transformations acts as the composite of the actions. -/
theorem map_comp {I : Type uI} [Category I] (F : PresheafDomPFunctorData I)
    {Z Z' Z'' : Iᵒᵖ ⥤ Type uZ} (α : CategoryTheory.NatTrans Z Z')
    (β : CategoryTheory.NatTrans Z' Z'') :
    F.map { app := fun i => α.app i ≫ β.app i, naturality := fun _ _ g =>
        (by rw [← Category.assoc, α.naturality, Category.assoc, β.naturality,
          ← Category.assoc]) } =
      F.map β ∘ F.map α := by
  funext x
  exact Subtype.ext (congrFun (F.toSliceDomPFunctor.map_comp (p := pZ Z) (q := pZ Z')
    (r := pZ Z'')
    (fun p : Σ i : I, Z.obj ⟨i⟩ => (⟨p.1, α.app ⟨p.1⟩ p.2⟩ : Σ i : I, Z'.obj ⟨i⟩))
    (fun p : Σ i : I, Z'.obj ⟨i⟩ => (⟨p.1, β.app ⟨p.1⟩ p.2⟩ : Σ i : I, Z''.obj ⟨i⟩))
    rfl rfl) x.1)

end PresheafDomPFunctorData

set_option linter.checkUnivs false in
/-- A presheaf-domain polynomial functor: operations together with a
proof they are functorial. Its action is a functor `(Iᵒᵖ ⥤ Type) ⥤ Type`
(packaged in `Presheaf.Functor`). -/
@[nolint checkUnivs]
structure PresheafDomPFunctor (I : Type uI) [Category I] : Type _
    extends PresheafDomPFunctorData I where
  /-- Proof the operations are functorial. -/
  isFunctorial : toPresheafDomPFunctorData.IsFunctorial

attribute [ext] PresheafDomPFunctorData PresheafDomPFunctor
