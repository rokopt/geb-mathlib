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
* `PresheafPFunctorData` — the full operations: the dom operations and the
  tag leg, with the `J`-action `tagRestr` on shapes and the arity reindexing
  `reindex`.
* `PresheafPFunctorData.TagRestrId` / `TagRestrComp` / `ReindexNaturality` /
  `ReindexId` / `ReindexComp` — the named `J`-side law `Prop`s. `ReindexId`
  and `ReindexComp` are parameterized on the relevant `tagRestr` law, whose
  content supplies the non-definitional source-type transport.
* `PresheafPFunctorData.IsFunctorial` — the full functor laws bundled.
* `PresheafPFunctor` — the full bundle: operations with a functoriality proof.

## Implementation notes

`PresheafDomPFunctorData` uses `extends SliceDomPFunctor.{uA, uB} I` with
pinned universes (load-bearing for a later diamond via `PresheafDomPFunctor`
and `SlicePFunctor`). The `linter.checkUnivs false` option and
`@[nolint checkUnivs]` suppress the auto-bound morphism-universe warning
that arises from `[Category I]`.

`PresheafPFunctorData` is the diamond
`extends PresheafDomPFunctorData.{uI, uA, uB} I, SlicePFunctor.{uA, uB} I J`,
which shares the single `SliceDomPFunctor` parent. The `reindex` laws
`ReindexId` / `ReindexComp` cannot be bare `Prop`s: comparing `reindex` along
`𝟙` (resp. a composite) with the identity (resp. the composite of `reindex`es)
requires a source-type transport whose target equality
(`tagRestr (𝟙 j) a = a`, resp. `tagRestr (h ≫ g) a = tagRestr h (tagRestr g a)`)
is `TagRestrId` (resp. `TagRestrComp`) content, not definitional. They are
therefore parameterized on that law and apply it via `cast`; `IsFunctorial`
supplies the proof from its earlier `tagRestr_id` / `tagRestr_comp` fields.

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

universe uI uJ uA uB uZ

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

set_option linter.checkUnivs false in
/-- Operations of a presheaf polynomial functor `(Iᵒᵖ ⥤ Type) → (Jᵒᵖ ⥤ Type)`:
the dom operations plus the tag leg `t` (via `SlicePFunctor`), the `J`-action
`tagRestr` on shapes, and the arity reindexing `reindex`. -/
@[nolint checkUnivs]
structure PresheafPFunctorData (I : Type uI) [Category I]
    (J : Type uJ) [Category J] : Type _
    extends PresheafDomPFunctorData.{uI, uA, uB} I, SlicePFunctor.{uA, uB} I J where
  /-- The shape-presheaf restriction: for `g : j' ⟶ j`, reindex shapes over
  `j` to shapes over `j'`. -/
  tagRestr : ∀ ⦃j j' : J⦄ (_g : j' ⟶ j),
      toSlicePFunctor.Shape j → toSlicePFunctor.Shape j'
  /-- The arity reindexing along a `J`-morphism: a presheaf morphism
  `E_T(tagRestr g a) ⟶ E_T(a)`. -/
  reindex : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : toSlicePFunctor.Shape j) ⦃i : I⦄,
      toSliceDomPFunctor.Position (tagRestr g a).1 i →
        toSliceDomPFunctor.Position a.1 i

/-- The tag-leg view of the operations: the shared `SliceDomPFunctor` together
with the tag leg `t`. The diamond merges the `SliceDomPFunctor` parent, so this
view shares its components with `toPresheafDomPFunctorData`. -/
add_decl_doc PresheafPFunctorData.toSlicePFunctor

namespace PresheafPFunctorData

/-- `tagRestr` preserves identities. -/
def TagRestrId {I : Type uI} [Category I] {J : Type uJ} [Category J]
    (F : PresheafPFunctorData I J) : Prop :=
  ∀ (j : J), F.tagRestr (𝟙 j) = id

/-- `tagRestr` is contravariant in `J`. -/
def TagRestrComp {I : Type uI} [Category I] {J : Type uJ} [Category J]
    (F : PresheafPFunctorData I J) : Prop :=
  ∀ ⦃j j' j'' : J⦄ (g : j' ⟶ j) (h : j'' ⟶ j'),
      F.tagRestr (h ≫ g) = F.tagRestr h ∘ F.tagRestr g

/-- Each `reindex g a` commutes with `restr` (a presheaf morphism
`E_T(tagRestr g a) ⟶ E_T(a)`): for `f : i' ⟶ i`,
`restr a.1 f ∘ reindex g a = reindex g a ∘ restr (tagRestr g a).1 f`.
Ordinary fibre maps only; no `tagRestr` transport. -/
def ReindexNaturality {I : Type uI} [Category I] {J : Type uJ} [Category J]
    (F : PresheafPFunctorData I J) : Prop :=
  ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j) ⦃i i' : I⦄ (f : i' ⟶ i),
    F.restr a.1 f ∘ F.reindex g a (i := i) =
      F.reindex g a (i := i') ∘ F.restr (F.tagRestr g a).1 f

/-- `reindex (𝟙 j) a` is the identity, modulo the transport of its source
along `TagRestrId` at `j` (`tagRestr (𝟙 j) a = a`). The transport is the
`cast` of `b` along `congrArg (fun s => Position s.1 i) (congrFun (hti j) a)`.
Parameterized on the identity law `hti` because that source-type equality is
not definitional. -/
def ReindexId {I : Type uI} [Category I] {J : Type uJ} [Category J]
    (F : PresheafPFunctorData I J) (hti : F.TagRestrId) : Prop :=
  ∀ ⦃j : J⦄ (a : F.Shape j) ⦃i : I⦄ (b : F.Position (F.tagRestr (𝟙 j) a).1 i),
    F.reindex (𝟙 j) a b =
      cast (congrArg (fun s : F.Shape j => F.Position s.1 i) (congrFun (hti j) a)) b

/-- For `g : j' ⟶ j`, `h : j'' ⟶ j'`,
`reindex (h ≫ g) a = reindex g a ∘ reindex h (tagRestr g a)` (outer factor the
`g` leg), modulo the transport of the source along `TagRestrComp`
(`tagRestr (h ≫ g) a = tagRestr h (tagRestr g a)`). The transport is the `cast`
of `b` along `congrArg (fun s => Position s.1 i) (congrFun (htc g h) a)`.
Parameterized on the composition law `htc` because that source-type equality is
not definitional. -/
def ReindexComp {I : Type uI} [Category I] {J : Type uJ} [Category J]
    (F : PresheafPFunctorData I J) (htc : F.TagRestrComp) : Prop :=
  ∀ ⦃j j' j'' : J⦄ (g : j' ⟶ j) (h : j'' ⟶ j') (a : F.Shape j) ⦃i : I⦄
    (b : F.Position (F.tagRestr (h ≫ g) a).1 i),
    F.reindex (h ≫ g) a b =
      F.reindex g a (F.reindex h (F.tagRestr g a)
        (cast (congrArg (fun s : F.Shape j'' => F.Position s.1 i)
          (congrFun (htc g h) a)) b))

/-- All functor laws: the dom laws plus the `J`-side laws making `T1` a
presheaf and `E_T` a functor on `el(T1)`. The `tagRestr` laws precede the
`reindex` laws because `reindex_id` / `reindex_comp` are stated relative to
`tagRestr_id` / `tagRestr_comp`. -/
structure IsFunctorial {I : Type uI} [Category I] {J : Type uJ} [Category J]
    (F : PresheafPFunctorData I J) : Prop
    extends F.toPresheafDomPFunctorData.IsFunctorial where
  /-- Identity law for `tagRestr`. -/
  tagRestr_id : F.TagRestrId
  /-- Composition law for `tagRestr`. -/
  tagRestr_comp : F.TagRestrComp
  /-- `reindex` is a presheaf morphism (commutes with `restr`). -/
  reindex_naturality : F.ReindexNaturality
  /-- Identity law for `reindex`, relative to `tagRestr_id`. -/
  reindex_id : F.ReindexId tagRestr_id
  /-- Composition law for `reindex`, relative to `tagRestr_comp`. -/
  reindex_comp : F.ReindexComp tagRestr_comp

end PresheafPFunctorData

set_option linter.checkUnivs false in
/-- A presheaf polynomial functor: operations together with a proof they are
functorial. Its action is a functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`. -/
@[nolint checkUnivs]
structure PresheafPFunctor (I : Type uI) [Category I]
    (J : Type uJ) [Category J] : Type _
    extends PresheafPFunctorData I J where
  /-- Proof the operations are functorial. -/
  isFunctorial : toPresheafPFunctorData.IsFunctorial

attribute [ext] PresheafPFunctorData PresheafPFunctorData.IsFunctorial
  PresheafPFunctor
