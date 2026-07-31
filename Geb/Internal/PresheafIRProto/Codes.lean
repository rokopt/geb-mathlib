/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.PresheafIRProto.Basic

/-!
# Prototype: code combinators at the presheaf p.r.a. level

Throwaway exploration, not upstream-eligible content. Continues
`PresheafIRProto.Basic` with the semantic counterparts of the code
constructors of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013],
generalized from families to presheaves. `Basic` supplies the `ι` case
(`iotaPresheaf`, `iotaConst`); this module supplies `σ` and `δ`.

## Main definitions

* `GebProto.coprodData` / `GebProto.coprod` — the `σ` case: the coproduct of a
  family of presheaf p.r.a. functors indexed by a type.
* `GebProto.DomArity` — a presheaf on `I` unbundled, in the presentation
  `PresheafDomPFunctorData` uses for its arities.
* `GebProto.ShapeArity` / `GebProto.ShapeArity.const` — the arity a `δ` adjoins,
  varying over the shape presheaf, and the constant one.
* `GebProto.deltaData` / `GebProto.delta` — the `δ` case: adjoin a `ShapeArity`
  to every arity of a functor.
* `GebProto.BaseArity` / `GebProto.BaseArity.pullback` — the arity a code's `δ`
  carries, indexed by output objects rather than by shapes, and its pullback
  along a functor's shape-output map to the `ShapeArity` that `delta` consumes.
* `GebProto.HasBijectiveReindex` — the property that every reindexing map is a
  bijection.
* `GebProto.ElObj` / `GebProto.elCategory` — the category of elements of a
  presheaf on `J`, as a base category; presheaves on it are the slice
  `PSh(J)/S`.
* `GebProto.sigmaLiftHom` / `GebProto.sigmaPshData` — the `σ` case: push a
  functor over the base `ElObj S` forward along the projection to `J`.
* `GebProto.unitPsh` — the unit for `δ`: terminal shape presheaf, no directions.
* `GebProto.arityVariesShapeArity` / `GebProto.deltaVarying` — the arity of
  `arityVaries` as a `ShapeArity` over `unitPsh`, and the `δ` at it.

## Main statements

* `GebProto.hasBijectiveReindex_iotaPresheaf`,
  `GebProto.hasBijectiveReindex_iotaConst`,
  `GebProto.hasBijectiveReindex_coprod`,
  `GebProto.hasBijectiveReindex_deltaConst` — the presheaf reading of the
  `ι` / `σ` / `δ` rules generates only functors with bijective reindexing.
* `GebProto.hasBijectiveReindex_delta` — the sharp form: a `δ`'s reindexing is
  bijective exactly when the adjoined arity's is.
* `GebProto.not_hasBijectiveReindex_arityVaries` — `arityVaries` is not such a
  functor, so those rules do not generate it.
* `GebProto.not_hasBijectiveReindex_deltaVarying` — a `δ` at an arity that does
  vary over the shape presheaf is not such a functor either, so the extended
  rule reaches past the bound.
* `GebProto.BaseArity.isFunctorial_pullback` — the pullback of a functorial
  `BaseArity` is functorial, so a code's `δ` need not mention its subcode's
  shapes.
* `GebProto.sigmaPsh_shapeRestr_id` — the `σ` case preserves the
  shape-restriction identity law.
* `GebProto.elObj_eq_of_hom` / `GebProto.elHom_eq_eqToHom_comp` — the source of
  a morphism of elements is determined by its base and its underlying
  `J`-morphism, and two morphisms with equal underlying `J`-morphisms differ by
  that transport.

## Implementation notes

`ShapeArity` indexes the adjoined arity by `F`'s shapes rather than by output
objects, which is what keeps `deltaData` free of transports: the arity of the
shape `a` is `fam a`, not `fam (F.q a)` transported along `a`'s membership
proof. Its `IsFunctorial` mirrors `PresheafPFunctorData.IsFunctorial` clause for
clause, so `delta`'s law proofs split over the two direction summands into the
arity's law and `F`'s.

`BaseArity.pullback` is where the transport `ShapeArity` avoids reappears: its
reindexing runs along `g` conjugated by the two shape-membership proofs, so its
two transported laws reduce to equalities of `J`-morphisms built from
`eqToHom`s. `BaseArity.reindex_eqToHom`, `BaseArity.reindex_cast_shape` and
`BaseArity.reindex_comp_apply` are the three lemmas that reduction needs.

The `σ` case is carried to the point where its operations are defined and its
first shape-restriction law holds. Its remaining four laws are the same
`eqToHom` bookkeeping over `ElObj S`, for which `elObj_eq_of_hom`,
`elHom_eq_eqToHom_comp`, `shapeRestr_val_eqToHom_comp`, `shapeRestr_eqToHom` and
`cast_shape_val` are the intended tools.

## Tags

prototype, inductive-recursive, presheaf, parametric right adjoint
-/

@[expose] public section

universe uI uJ uA uB uS vI vJ

open CategoryTheory

namespace GebProto

section Coprod

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

set_option linter.checkUnivs false in
/-- Operations of the `σ` case: the coproduct of an `S`-indexed family of
presheaf p.r.a. functors. A shape is a shape of one summand tagged with its
index; the directions, both restrictions and the reindexing are that summand's.
The `J`-action never changes the tag, which is what makes each summand's laws
suffice. -/
def coprodData (S : Type uS) (sub : S → PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) :
    PresheafPFunctorData.{uI, uJ, max uS uA, uB, vI, vJ} I J where
  A := Σ s : S, (sub s).A
  B := fun x ↦ (sub x.1).B x.2
  r := fun x ↦ (sub x.1.1).r ⟨x.1.2, x.2⟩
  q := fun x ↦ (sub x.1).q x.2
  directionRestr := fun a _ _ g d ↦ (sub a.1).directionRestr a.2 g d
  shapeRestr := fun {_ _} g s ↦
    ⟨⟨s.1.1, ((sub s.1.1).shapeRestr g ⟨s.1.2, s.2⟩).1⟩,
      ((sub s.1.1).shapeRestr g ⟨s.1.2, s.2⟩).2⟩
  reindex := fun {_ _} g s _ d ↦ (sub s.1.1).reindex g ⟨s.1.2, s.2⟩ d

set_option linter.checkUnivs false in
/-- The coproduct is a genuine `PresheafPFunctor`: every law is the
corresponding law of the summand a shape came from, the tag being inert under
both restrictions. The two transported laws hold by `rfl` because the
coproduct's `cast` and the summand's `cast` run between definitionally equal
types, so proof irrelevance identifies them. -/
def coprod (S : Type uS) (sub : S → PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    PresheafPFunctor.{uI, uJ, max uS uA, uB, vI, vJ} I J where
  toPresheafPFunctorData := coprodData S fun s ↦ (sub s).toPresheafPFunctorData
  isFunctorial :=
    { directionRestr_id := fun a i ↦ (sub a.1).isFunctorial.directionRestr_id a.2 i
      directionRestr_comp := by
        intro a i i' i'' f g
        exact (sub a.1).isFunctorial.directionRestr_comp a.2 f g
      shapeRestr_id := by
        intro j
        funext s
        exact Subtype.ext (Sigma.ext rfl (heq_of_eq (congrArg Subtype.val
          (congrFun ((sub s.1.1).isFunctorial.shapeRestr_id j) ⟨s.1.2, s.2⟩))))
      shapeRestr_comp := by
        intro j j' j'' g h
        funext s
        exact Subtype.ext (Sigma.ext rfl (heq_of_eq (congrArg Subtype.val
          (congrFun ((sub s.1.1).isFunctorial.shapeRestr_comp g h) ⟨s.1.2, s.2⟩))))
      reindex_naturality := by
        intro j j' g a i i' f
        exact (sub a.1.1).isFunctorial.reindex_naturality g ⟨a.1.2, a.2⟩ f
      reindex_id := by
        intro j a i b
        exact (sub a.1.1).isFunctorial.reindex_id ⟨a.1.2, a.2⟩ b
      reindex_comp := by
        intro j j' j'' g h a i b
        exact (sub a.1.1).isFunctorial.reindex_comp g h ⟨a.1.2, a.2⟩ b }

end Coprod

section Arity

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

set_option linter.checkUnivs false in
/-- A presheaf on `I`, unbundled: a carrier with a base-point map `proj`, the
directions over `i` being the fiber of `proj`, and the contravariant action
`restr` on those fibers. Presented the way `PresheafDomPFunctorData` presents
its arities, so that these directions plug into a `PresheafPFunctorData`'s
without transport.

Writing this as `Iᵒᵖ ⥤ Type uB` and its morphisms with `⟶` would draw in
`Classical.choice` through `CategoryTheory.Functor.category`. -/
structure DomArity (I : Type uI) [Category.{vI} I] : Type (max (uB + 1) uI vI) where
  /-- The total space of the arity. -/
  carrier : Type uB
  /-- The base-point map assigning each element of the carrier an input object. -/
  proj : carrier → I
  /-- The contravariant `I`-action on the fibers of `proj`. -/
  restr : ∀ ⦃i i' : I⦄, (i' ⟶ i) → {c : carrier // proj c = i} → {c : carrier // proj c = i'}

namespace DomArity

/-- The directions lying over the input object `i`: the fiber of `proj`. -/
@[reducible] def Dir (G : DomArity.{uI, uB, vI} I) (i : I) : Type uB :=
  {c : G.carrier // G.proj c = i}

/-- The presheaf laws of a `DomArity`. -/
structure IsFunctorial (G : DomArity.{uI, uB, vI} I) : Prop where
  /-- `restr` preserves identities. -/
  restr_id : ∀ i : I, G.restr (𝟙 i) = id
  /-- `restr` reverses composition. -/
  restr_comp : ∀ ⦃i i' i'' : I⦄ (f : i' ⟶ i) (g : i'' ⟶ i'),
    G.restr (g ≫ f) = G.restr g ∘ G.restr f

end DomArity

end Arity

section Delta

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

set_option linter.checkUnivs false in
/-- The arity adjoined by a `δ`, varying over `F`'s shape presheaf: a presheaf
on `I` for each shape, together with a reindexing along shape restriction. This
is the data of a functor `el(T₁)ᵒᵖ ⥤ (Iᵒᵖ ⥤ Type)`, unbundled — the same data
`PresheafPFunctorData` carries in its `directionRestr` and `reindex` fields.

Indexing by shapes rather than by output objects is what keeps the `δ`
operation transport-free: the arity of the shape `a` is `fam a`, not
`fam (F.q a)` transported along `a`'s membership proof. -/
structure ShapeArity (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) :
    Type (max (uB + 1) uA uI uJ vI vJ) where
  /-- The presheaf on `I` adjoined over each shape. -/
  fam : F.A → DomArity.{uI, uB, vI} I
  /-- Reindexing along shape restriction, in the direction of
  `PresheafPFunctorData.reindex`. -/
  reindex : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (s : F.Shape j) ⦃i : I⦄,
    (fam (F.shapeRestr g s).1).Dir i → (fam s.1).Dir i

namespace ShapeArity

set_option linter.checkUnivs false in
/-- The functor laws of a `ShapeArity`, mirroring those of
`PresheafPFunctorData` clause for clause: `reindex_id` and `reindex_comp` carry
the same `cast` along `F`'s shape-restriction laws. -/
structure IsFunctorial (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (P : ShapeArity F.toPresheafPFunctorData) : Prop where
  /-- Each adjoined presheaf preserves identities. -/
  restr_id : ∀ (a : F.A) (i : I), (P.fam a).restr (𝟙 i) = id
  /-- Each adjoined presheaf reverses composition. -/
  restr_comp : ∀ (a : F.A) ⦃i i' i'' : I⦄ (f : i' ⟶ i) (g : i'' ⟶ i'),
    (P.fam a).restr (g ≫ f) = (P.fam a).restr g ∘ (P.fam a).restr f
  /-- Reindexing is a morphism of presheaves on `I`. -/
  reindex_naturality : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (s : F.Shape j) ⦃i i' : I⦄ (f : i' ⟶ i),
    (P.fam s.1).restr f ∘ P.reindex g s (i := i) =
      P.reindex g s (i := i') ∘ (P.fam (F.shapeRestr g s).1).restr f
  /-- Reindexing along an identity is the transport along `F.shapeRestr_id`. -/
  reindex_id : ∀ ⦃j : J⦄ (s : F.Shape j) ⦃i : I⦄
      (d : (P.fam (F.shapeRestr (𝟙 j) s).1).Dir i),
    P.reindex (𝟙 j) s d =
      cast (congrArg (fun u : F.Shape j ↦ (P.fam u.1).Dir i)
        (congrFun (F.isFunctorial.shapeRestr_id j) s)) d
  /-- Reindexing along a composite factors, modulo the transport along
  `F.shapeRestr_comp`. -/
  reindex_comp : ∀ ⦃j j' j'' : J⦄ (g : j' ⟶ j) (h : j'' ⟶ j') (s : F.Shape j) ⦃i : I⦄
      (d : (P.fam (F.shapeRestr (h ≫ g) s).1).Dir i),
    P.reindex (h ≫ g) s d =
      P.reindex g s (P.reindex h (F.shapeRestr g s)
        (cast (congrArg (fun u : F.Shape j'' ↦ (P.fam u.1).Dir i)
          (congrFun (F.isFunctorial.shapeRestr_comp g h) s)) d))

set_option linter.checkUnivs false in
/-- The arity that adjoins the same presheaf `G` over every shape, its
reindexing the identity. This is the presheaf reading of the `δ` rule of
Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013], whose arity is a set
`P` labelled by `i : P → I` — an object of `Set/I`, which is a presheaf on a
discrete `I`, and which carries no dependence on the output object. -/
def const (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J)
    (G : DomArity.{uI, uB, vI} I) : ShapeArity F where
  fam := fun _ ↦ G
  reindex := fun {_ _} _g _s {_} d ↦ d

/-- A constant arity is functorial as soon as `G` is: its reindexing is the
identity, and the two transported laws hold by proof irrelevance. -/
theorem isFunctorial_const (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (G : DomArity.{uI, uB, vI} I) (hG : G.IsFunctorial) :
    IsFunctorial F (const F.toPresheafPFunctorData G) where
  restr_id := fun _ i ↦ hG.restr_id i
  restr_comp := by intro a i i' i'' f g; exact hG.restr_comp f g
  reindex_naturality := by intro j j' g s i i' f; rfl
  reindex_id := by intro j s i d; exact (cast_eq _ d).symm
  reindex_comp := by
    intro j j' j'' g h s i d
    exact (cast_eq (congrArg (fun u : F.Shape j'' ↦ G.Dir i)
      (congrFun (F.isFunctorial.shapeRestr_comp g h) s)) d).symm

end ShapeArity

set_option linter.checkUnivs false in
/-- Operations of the `δ` case: adjoin the arity `P` to every arity of `F`,
leaving the shapes untouched. -/
def deltaData (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) (P : ShapeArity F) :
    PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J where
  A := F.A
  B := fun a ↦ (P.fam a).carrier ⊕ F.B a
  r := fun x ↦ Sum.elim (P.fam x.1).proj (fun b ↦ F.r ⟨x.1, b⟩) x.2
  q := F.q
  directionRestr := fun a _ _ g d ↦
    match d with
    | ⟨Sum.inl c, h⟩ => ⟨Sum.inl ((P.fam a).restr g ⟨c, h⟩).1, ((P.fam a).restr g ⟨c, h⟩).2⟩
    | ⟨Sum.inr b, h⟩ => ⟨Sum.inr (F.directionRestr a g ⟨b, h⟩).1, (F.directionRestr a g ⟨b, h⟩).2⟩
  shapeRestr := fun {_ _} g s ↦ F.shapeRestr g s
  reindex := fun {_ _} g s _ d ↦
    match d with
    | ⟨Sum.inl c, h⟩ => ⟨Sum.inl (P.reindex g s ⟨c, h⟩).1, (P.reindex g s ⟨c, h⟩).2⟩
    | ⟨Sum.inr b, h⟩ => ⟨Sum.inr (F.reindex g s ⟨b, h⟩).1, (F.reindex g s ⟨b, h⟩).2⟩

variable (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) (P : ShapeArity F)

/-- Transport of an adjoined direction along an equality of shapes is the
transport of that direction inside the arity. -/
theorem delta_cast_inl {j : J} {i : I} {t t' : F.Shape j} (e : t = t')
    (d : (P.fam t.1).Dir i) :
    cast (congrArg (fun u : F.Shape j ↦ (deltaData F P).Direction u.1 i) e)
        (⟨Sum.inl d.1, d.2⟩ : (deltaData F P).Direction t.1 i) =
      ⟨Sum.inl (cast (congrArg (fun u : F.Shape j ↦ (P.fam u.1).Dir i) e) d).1,
        (cast (congrArg (fun u : F.Shape j ↦ (P.fam u.1).Dir i) e) d).2⟩ := by
  cases e
  rfl

/-- Transport of an original direction along an equality of shapes is the
transport of that direction inside `F`. -/
theorem delta_cast_inr {j : J} {i : I} {t t' : F.Shape j} (e : t = t')
    (d : F.Direction t.1 i) :
    cast (congrArg (fun u : F.Shape j ↦ (deltaData F P).Direction u.1 i) e)
        (⟨Sum.inr d.1, d.2⟩ : (deltaData F P).Direction t.1 i) =
      ⟨Sum.inr (cast (congrArg (fun u : F.Shape j ↦ F.Direction u.1 i) e) d).1,
        (cast (congrArg (fun u : F.Shape j ↦ F.Direction u.1 i) e) d).2⟩ := by
  cases e
  rfl

set_option linter.checkUnivs false in
/-- Adjoining an arity to a presheaf p.r.a. functor yields one: the shape-side
laws are `F`'s unchanged, and each direction-side law splits over the two
summands into the arity's law and `F`'s. -/
def delta (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (P : ShapeArity F.toPresheafPFunctorData) (hP : P.IsFunctorial F) :
    PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J where
  toPresheafPFunctorData := deltaData F.toPresheafPFunctorData P
  isFunctorial :=
    { directionRestr_id := by
        intro a i
        funext d
        obtain ⟨b, h⟩ := d
        cases b with
        | inl c =>
            exact Subtype.ext (congrArg (fun x : (P.fam a).Dir i ↦ Sum.inl x.1)
              (congrFun (hP.restr_id a i) ⟨c, h⟩))
        | inr b =>
            exact Subtype.ext (congrArg (fun x : F.Direction a i ↦ Sum.inr x.1)
              (congrFun (F.isFunctorial.directionRestr_id a i) ⟨b, h⟩))
      directionRestr_comp := by
        intro a i i' i'' f g
        funext d
        obtain ⟨b, h⟩ := d
        cases b with
        | inl c =>
            exact Subtype.ext (congrArg (fun x : (P.fam a).Dir i'' ↦ Sum.inl x.1)
              (congrFun (hP.restr_comp a f g) ⟨c, h⟩))
        | inr b =>
            exact Subtype.ext (congrArg (fun x : F.Direction a i'' ↦ Sum.inr x.1)
              (congrFun (F.isFunctorial.directionRestr_comp a f g) ⟨b, h⟩))
      shapeRestr_id := F.isFunctorial.shapeRestr_id
      shapeRestr_comp := F.isFunctorial.shapeRestr_comp
      reindex_naturality := by
        intro j j' g a i i' f
        funext d
        obtain ⟨b, h⟩ := d
        cases b with
        | inl c =>
            exact Subtype.ext (congrArg (fun x : (P.fam a.1).Dir i' ↦ Sum.inl x.1)
              (congrFun (hP.reindex_naturality g a f) ⟨c, h⟩))
        | inr b =>
            exact Subtype.ext (congrArg (fun x : F.Direction a.1 i' ↦ Sum.inr x.1)
              (congrFun (F.isFunctorial.reindex_naturality g a f) ⟨b, h⟩))
      reindex_id := by
        intro j a i d
        obtain ⟨b, h⟩ := d
        cases b with
        | inl c =>
            refine Eq.trans ?_ (delta_cast_inl F.toPresheafPFunctorData P
              (congrFun (F.isFunctorial.shapeRestr_id j) a) ⟨c, h⟩).symm
            exact Subtype.ext (congrArg (fun x : (P.fam a.1).Dir i ↦ Sum.inl x.1)
              (hP.reindex_id a ⟨c, h⟩))
        | inr b =>
            refine Eq.trans ?_ (delta_cast_inr F.toPresheafPFunctorData P
              (congrFun (F.isFunctorial.shapeRestr_id j) a) ⟨b, h⟩).symm
            exact Subtype.ext (congrArg (fun x : F.Direction a.1 i ↦ Sum.inr x.1)
              (F.isFunctorial.reindex_id a ⟨b, h⟩))
      reindex_comp := by
        intro j j' j'' g h a i d
        obtain ⟨b, hb⟩ := d
        cases b with
        | inl c =>
            refine Eq.trans ?_ (congrArg (fun z ↦
              (deltaData F.toPresheafPFunctorData P).reindex g a
                ((deltaData F.toPresheafPFunctorData P).reindex h
                  ((deltaData F.toPresheafPFunctorData P).shapeRestr g a) z))
              (delta_cast_inl F.toPresheafPFunctorData P
                (congrFun (F.isFunctorial.shapeRestr_comp g h) a) ⟨c, hb⟩)).symm
            exact Subtype.ext (congrArg (fun x : (P.fam a.1).Dir i ↦ Sum.inl x.1)
              (hP.reindex_comp g h a ⟨c, hb⟩))
        | inr b =>
            refine Eq.trans ?_ (congrArg (fun z ↦
              (deltaData F.toPresheafPFunctorData P).reindex g a
                ((deltaData F.toPresheafPFunctorData P).reindex h
                  ((deltaData F.toPresheafPFunctorData P).shapeRestr g a) z))
              (delta_cast_inr F.toPresheafPFunctorData P
                (congrFun (F.isFunctorial.shapeRestr_comp g h) a) ⟨b, hb⟩)).symm
            exact Subtype.ext (congrArg (fun x : F.Direction a.1 i ↦ Sum.inr x.1)
              (F.isFunctorial.reindex_comp g h a ⟨b, hb⟩)) }


section Base

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

set_option linter.checkUnivs false in
/-- The arity a code's `δ` carries: a presheaf on `I` for each *output object*,
with a reindexing along `J`-morphisms. This is the data of a functor
`J ⥤ (Iᵒᵖ ⥤ Type)`, unbundled.

A code's `δ` must be indexed this way rather than by shapes: the shapes belong
to the subcode's interpretation, which a code cannot mention. `pullback`
converts it to the shape-indexed `ShapeArity` that `delta` consumes. -/
structure BaseArity (I : Type uI) [Category.{vI} I] (J : Type uJ) [Category.{vJ} J] :
    Type (max (uB + 1) uI uJ vI vJ) where
  /-- The presheaf on `I` carried over each output object. -/
  fam : J → DomArity.{uI, uB, vI} I
  /-- Reindexing along a `J`-morphism, covariant, matching the direction of
  `PresheafPFunctorData.reindex`. -/
  reindex : ∀ ⦃j j' : J⦄, (j' ⟶ j) → ∀ ⦃i : I⦄, (fam j').Dir i → (fam j).Dir i

namespace BaseArity

set_option linter.checkUnivs false in
/-- The functor laws of a `BaseArity`. No `cast` appears: there is no shape
presheaf to transport along. -/
structure IsFunctorial (P : BaseArity.{uI, uJ, uB, vI, vJ} I J) : Prop where
  /-- Each presheaf preserves identities. -/
  restr_id : ∀ (j : J) (i : I), (P.fam j).restr (𝟙 i) = id
  /-- Each presheaf reverses composition. -/
  restr_comp : ∀ (j : J) ⦃i i' i'' : I⦄ (f : i' ⟶ i) (g : i'' ⟶ i'),
    (P.fam j).restr (g ≫ f) = (P.fam j).restr g ∘ (P.fam j).restr f
  /-- Reindexing preserves identities. -/
  reindex_id : ∀ (j : J) (i : I), P.reindex (𝟙 j) (i := i) = id
  /-- Reindexing preserves composition, `g` being the outer factor. -/
  reindex_comp : ∀ ⦃j j' j'' : J⦄ (g : j' ⟶ j) (h : j'' ⟶ j') (i : I),
    P.reindex (h ≫ g) (i := i) = P.reindex g (i := i) ∘ P.reindex h (i := i)
  /-- Reindexing is a morphism of presheaves on `I`. -/
  reindex_naturality : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) ⦃i i' : I⦄ (f : i' ⟶ i),
    (P.fam j).restr f ∘ P.reindex g (i := i) = P.reindex g (i := i') ∘ (P.fam j').restr f

variable (P : BaseArity.{uI, uJ, uB, vI, vJ} I J)

/-- Reindexing along an `eqToHom` is the transport along the underlying
equality. -/
theorem reindex_eqToHom (hP : P.IsFunctorial) {x y : J} (hh : x = y) {i : I}
    (d : (P.fam x).Dir i) :
    P.reindex (eqToHom hh) d = cast (congrArg (fun w : J ↦ (P.fam w).Dir i) hh) d := by
  cases hh
  simpa using congrFun (hP.reindex_id x i) d

/-- Reindexing along a composite, applied pointwise. -/
theorem reindex_comp_apply (hP : P.IsFunctorial) {x y z : J} (k₁ : x ⟶ y) (k₂ : y ⟶ z)
    {i : I} (d : (P.fam x).Dir i) :
    P.reindex (k₁ ≫ k₂) d = P.reindex k₂ (P.reindex k₁ d) :=
  congrFun (hP.reindex_comp k₂ k₁ i) d

/-- Reindexing after a transport is reindexing along the composite with the
transport's `eqToHom`. -/
theorem reindex_cast {x y z : J} (k : y ⟶ z) (hh : x = y) {i : I} (d : (P.fam x).Dir i) :
    P.reindex k (cast (congrArg (fun w : J ↦ (P.fam w).Dir i) hh) d) =
      P.reindex (eqToHom hh ≫ k) d := by
  cases hh
  simp

/-- Reindexing after a transport along an equality of *shapes* is reindexing
along the composite with that equality's `eqToHom`. -/
theorem reindex_cast_shape (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J)
    {j : J} {t t' : F.Shape j} (hh : t = t') {x : J} (k : F.q t'.1 ⟶ x) {i : I}
    (d : (P.fam (F.q t.1)).Dir i) :
    P.reindex k (cast (congrArg (fun u : F.Shape j ↦ (P.fam (F.q u.1)).Dir i) hh) d) =
      P.reindex (eqToHom (congrArg (fun u : F.Shape j ↦ F.q u.1) hh) ≫ k) d := by
  cases hh
  simp

set_option linter.checkUnivs false in
/-- Pull a `BaseArity` back along a functor's shape-output map: the arity over
the shape `a` is the arity over `F.q a`, reindexed along the `J`-morphism `g`
transported by the two shape-membership proofs. -/
def pullback (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) : ShapeArity F where
  fam := fun a ↦ P.fam (F.q a)
  reindex := fun {_ _} g s {_} d ↦
    P.reindex (eqToHom (F.shapeRestr g s).2 ≫ g ≫ eqToHom s.2.symm) d

/-- The transported morphism a pullback reindexes along, named so the two
transported laws can rewrite it. -/
theorem pullback_reindex (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J)
    {j j' : J} (g : j' ⟶ j) (s : F.Shape j) {i : I}
    (d : ((P.pullback F).fam (F.shapeRestr g s).1).Dir i) :
    (P.pullback F).reindex g s d =
      P.reindex (eqToHom (F.shapeRestr g s).2 ≫ g ≫ eqToHom s.2.symm) d :=
  rfl

set_option linter.checkUnivs false in
/-- The pullback of a functorial `BaseArity` is functorial. The two transported
laws reduce, via `reindex_eqToHom` and `reindex_cast`, to equalities of
`J`-morphisms built from `eqToHom`s, which cancel. -/
theorem isFunctorial_pullback (hP : P.IsFunctorial)
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    (P.pullback F.toPresheafPFunctorData).IsFunctorial F where
  restr_id := fun a i ↦ hP.restr_id (F.q a) i
  restr_comp := by intro a i i' i'' f g; exact hP.restr_comp (F.q a) f g
  reindex_naturality := by
    intro j j' g s i i' f
    exact hP.reindex_naturality (eqToHom (F.shapeRestr g s).2 ≫ g ≫ eqToHom s.2.symm) f
  reindex_id := by
    intro j s i d
    simp only [pullback] at d ⊢
    rw [show
      (eqToHom (F.shapeRestr (𝟙 j) s).2 ≫ (𝟙 j) ≫ eqToHom s.2.symm) =
        eqToHom (((F.shapeRestr (𝟙 j) s).2).trans s.2.symm) by simp,
      reindex_eqToHom P hP]
  reindex_comp := by
    intro j j' j'' g h s i d
    simp only [pullback] at d ⊢
    rw [reindex_cast_shape (hh := congrFun (F.isFunctorial.shapeRestr_comp g h) s),
      ← reindex_comp_apply P hP]
    congr 1
    simp

end BaseArity

end Base

end Delta

section Sigma

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- Objects of the base category of elements of a presheaf `S` on `J`. -/
abbrev ElObj (S : Jᵒᵖ ⥤ Type uS) : Type (max uJ uS) := Σ j : J, S.obj ⟨j⟩

/-- The base category of elements of `S`: a morphism `x ⟶ y` is a `J`-morphism
carrying `y`'s element to `x`'s. Presheaves on it are the slice `PSh(J)/S`, and
this is `S.Elementsᵒᵖ`; it is written out here rather than reused so that the
`σ` operation below is free of `Opposite` transport. -/
instance elCategory (S : Jᵒᵖ ⥤ Type uS) : Category.{vJ} (ElObj.{uJ, uS, vJ} S) where
  Hom x y := {g : x.1 ⟶ y.1 // S.map g.op y.2 = x.2}
  id x := ⟨𝟙 x.1, by simp⟩
  comp {x y z} f g := ⟨f.1 ≫ g.1, by
    rw [op_comp, S.map_comp, types_comp_apply, g.2, f.2]⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

/-- The `J`-morphism a shape's membership proof turns `g` into: `g` followed by
the transport identifying `j` with the base of the shape's output object. -/
def sigmaLiftHom (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctorData.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S))
    {j j' : J} (g : j' ⟶ j) (s : {a : F.A // (F.q a).1 = j}) :
    (⟨j', S.map (g ≫ eqToHom s.2.symm).op (F.q s.1).2⟩ : ElObj S) ⟶ F.q s.1 :=
  ⟨g ≫ eqToHom s.2.symm, rfl⟩

set_option linter.checkUnivs false in
/-- Operations of the `σ` case: push a functor over the base `ElObj S` forward
to one over `J`. The shapes and arities are unchanged; only the shape-output map
drops the `S`-component, so the shape presheaf becomes the total space of `S`
paired with the subfunctor's shapes. -/
def sigmaPshData (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctorData.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S)) :
    PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J where
  A := F.A
  B := F.B
  r := F.r
  q := fun a ↦ (F.q a).1
  directionRestr := F.directionRestr
  shapeRestr := fun {_ _} g s ↦
    ⟨(F.shapeRestr (sigmaLiftHom S F g s) ⟨s.1, rfl⟩).1,
      congrArg Sigma.fst (F.shapeRestr (sigmaLiftHom S F g s) ⟨s.1, rfl⟩).2⟩
  reindex := fun {_ _} g s {_} d ↦ F.reindex (sigmaLiftHom S F g s) ⟨s.1, rfl⟩ d


universe uK vK

/-- The underlying `J`-morphism of a composite in the category of elements. -/
@[simp] theorem elCategory_comp_val (S : Jᵒᵖ ⥤ Type uS) {x y z : ElObj.{uJ, uS, vJ} S}
    (f : x ⟶ y) (g : y ⟶ z) : (f ≫ g).1 = f.1 ≫ g.1 := rfl

/-- The underlying `J`-morphism of a transport in the category of elements is
the transport of the underlying objects. -/
@[simp]
theorem elCategory_eqToHom_val (S : Jᵒᵖ ⥤ Type uS) {x y : ElObj.{uJ, uS, vJ} S} (h : x = y) :
    (eqToHom h : x ⟶ y).1 = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

/-- Restricting a shape along a transport is the transport of the shape. -/
theorem shapeRestr_eqToHom {K : Type uK} [Category.{vK} K]
    (F : PresheafPFunctor.{uI, uK, uA, uB, vI, vK} I K) {x y : K} (h : x = y) (s : F.Shape y) :
    F.shapeRestr (eqToHom h) s = cast (congrArg F.Shape h.symm) s := by
  cases h
  simpa using congrFun (F.isFunctorial.shapeRestr_id x) s

/-- A transport of shapes leaves the underlying shape alone. -/
theorem cast_shape_val {K : Type uK} [Category.{vK} K]
    (F : PresheafPFunctorData.{uI, uK, uA, uB, vI, vK} I K) {x y : K} (h : x = y)
    (s : F.Shape x) : (cast (congrArg F.Shape h) s).1 = s.1 := by
  cases h
  rfl


/-- Restricting along a morphism with a transport prefix leaves the underlying
shape where restricting along the morphism alone leaves it. -/
theorem shapeRestr_val_eqToHom_comp {K : Type uK} [Category.{vK} K]
    (F : PresheafPFunctor.{uI, uK, uA, uB, vI, vK} I K) {x x' y : K} (hx : x = x')
    (m : x' ⟶ y) (s : F.Shape y) :
    (F.shapeRestr (eqToHom hx ≫ m) s).1 = (F.shapeRestr m s).1 := by
  rw [F.isFunctorial.shapeRestr_comp, Function.comp_apply, shapeRestr_eqToHom]
  exact cast_shape_val F.toPresheafPFunctorData hx.symm _


/-- The source of a morphism in the category of elements is determined by its
base and its underlying `J`-morphism: the element is forced to be the
restriction of the target's. -/
theorem elObj_eq_of_hom (S : Jᵒᵖ ⥤ Type uS) {x x' y : ElObj.{uJ, uS, vJ} S}
    (m : x ⟶ y) (m' : x' ⟶ y) (hb : x.1 = x'.1) (hm : m.1 = eqToHom hb ≫ m'.1) : x = x' := by
  cases x with
  | mk xb xe =>
    cases x' with
    | mk xb' xe' =>
      cases hb
      refine Sigma.ext rfl (heq_of_eq ?_)
      rw [← m.2, ← m'.2, hm]
      simp

/-- Two morphisms into the same object with equal underlying `J`-morphisms
differ by the transport identifying their sources. -/
theorem elHom_eq_eqToHom_comp (S : Jᵒᵖ ⥤ Type uS) {x x' y : ElObj.{uJ, uS, vJ} S}
    (m : x ⟶ y) (m' : x' ⟶ y) (hb : x.1 = x'.1) (hm : m.1 = eqToHom hb ≫ m'.1) :
    m = eqToHom (elObj_eq_of_hom S m m' hb hm) ≫ m' := by
  refine Subtype.ext ?_
  rw [hm]
  change _ = (eqToHom (elObj_eq_of_hom S m m' hb hm) : x ⟶ x').1 ≫ m'.1
  rw [elCategory_eqToHom_val]

/-- The `σ` operation preserves the shape-restriction identity law. -/
theorem sigmaPsh_shapeRestr_id (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctor.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S)) :
    (sigmaPshData S F.toPresheafPFunctorData).ShapeRestrId := by
  intro j
  funext s
  obtain ⟨a, rfl⟩ := s
  refine Subtype.ext ?_
  have hsrc : (⟨(F.q a).1, S.map (sigmaLiftHom S F.toPresheafPFunctorData
      (𝟙 ((F.q a).1)) ⟨a, rfl⟩).1.op (F.q a).2⟩ : ElObj S) = F.q a :=
    Sigma.ext rfl (heq_of_eq (by simp [sigmaLiftHom]))
  have hval : (eqToHom hsrc : _ ⟶ F.q a).1 = 𝟙 (F.q a).1 := by
    rw [elCategory_eqToHom_val]
    simp
  have hm : sigmaLiftHom S F.toPresheafPFunctorData (𝟙 ((F.q a).1)) ⟨a, rfl⟩
      = eqToHom hsrc ≫ 𝟙 (F.q a) :=
    Subtype.ext (by
      simp only [sigmaLiftHom, eqToHom_refl, op_comp, op_id, Category.comp_id]
      exact hval.symm)
  change (F.shapeRestr (sigmaLiftHom S F.toPresheafPFunctorData (𝟙 _) ⟨a, rfl⟩) ⟨a, rfl⟩).1 = a
  rw [hm]
  refine Eq.trans (shapeRestr_val_eqToHom_comp F hsrc (𝟙 (F.q a)) ⟨a, rfl⟩) ?_
  exact congrArg Subtype.val (congrFun (F.isFunctorial.shapeRestr_id (F.q a)) ⟨a, rfl⟩)


end Sigma

section Incompleteness

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- Every reindexing map of `F` is a bijection. Equivalently, the fibres of
`objPresheaf F` are cartesian over the shape presheaf: restricting a shape
along `g : j' ⟶ j` neither discards nor invents directions. -/
def HasBijectiveReindex (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) : Prop :=
  ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (a : F.Shape j) (i : I),
    Function.Bijective (F.reindex g a (i := i))

/-- The constant functor at a representable has bijective reindexing: it has no
directions at all. -/
theorem hasBijectiveReindex_iotaPresheaf (j₀ : J) :
    HasBijectiveReindex (iotaPresheaf.{uI, uJ, uB, vI, vJ} (I := I) j₀) := by
  intro j j' g a i
  exact ⟨fun x _ _ ↦ PEmpty.elim x.1, fun y ↦ PEmpty.elim y.1⟩

/-- The constant functor at an arbitrary presheaf has bijective reindexing, for
the same reason. -/
theorem hasBijectiveReindex_iotaConst (P : Jᵒᵖ ⥤ Type uB) :
    HasBijectiveReindex (iotaConst.{uI, uJ, uB, vI, vJ} (I := I) P) := by
  intro j j' g a i
  exact ⟨fun x _ _ ↦ PEmpty.elim x.1, fun y ↦ PEmpty.elim y.1⟩

/-- Bijective reindexing is inherited by coproducts: a coproduct's reindexing is
the reindexing of the summand a shape came from. -/
theorem hasBijectiveReindex_coprod (S : Type uS)
    (sub : S → PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (h : ∀ s, HasBijectiveReindex (sub s)) :
    HasBijectiveReindex (coprod S sub) := by
  intro j j' g a i
  exact h a.1.1 g ⟨a.1.2, a.2⟩ i

/-- Bijective reindexing is inherited by `δ` exactly when the adjoined arity's
own reindexing is bijective: the two summands of a `δ` direction are reindexed
independently. -/
theorem hasBijectiveReindex_delta (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (P : ShapeArity F.toPresheafPFunctorData) (hP : P.IsFunctorial F)
    (hF : HasBijectiveReindex F)
    (hPb : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (s : F.Shape j) (i : I),
      Function.Bijective (P.reindex g s (i := i))) :
    HasBijectiveReindex (delta F P hP) := by
  intro j j' g a i
  refine ⟨?_, ?_⟩
  · rintro ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ hd
    cases b₁ with
    | inl c₁ =>
        cases b₂ with
        | inl c₂ =>
            have hv : (Sum.inl (P.reindex g a ⟨c₁, h₁⟩).1 : (P.fam a.1).carrier ⊕ F.B a.1) =
                Sum.inl (P.reindex g a ⟨c₂, h₂⟩).1 := congrArg Subtype.val hd
            exact Subtype.ext (congrArg (fun x : (P.fam (F.shapeRestr g a).1).Dir i ↦
              (Sum.inl x.1 : (P.fam (F.shapeRestr g a).1).carrier ⊕ F.B (F.shapeRestr g a).1))
              ((hPb g a i).1 (Subtype.ext (Sum.inl.inj hv))))
        | inr b₂ =>
            have hv : (Sum.inl (P.reindex g a ⟨c₁, h₁⟩).1 : (P.fam a.1).carrier ⊕ F.B a.1) =
                Sum.inr (F.reindex g a ⟨b₂, h₂⟩).1 := congrArg Subtype.val hd
            simp at hv
    | inr b₁ =>
        cases b₂ with
        | inl c₂ =>
            have hv : (Sum.inr (F.reindex g a ⟨b₁, h₁⟩).1 : (P.fam a.1).carrier ⊕ F.B a.1) =
                Sum.inl (P.reindex g a ⟨c₂, h₂⟩).1 := congrArg Subtype.val hd
            simp at hv
        | inr b₂ =>
            have hv : (Sum.inr (F.reindex g a ⟨b₁, h₁⟩).1 : (P.fam a.1).carrier ⊕ F.B a.1) =
                Sum.inr (F.reindex g a ⟨b₂, h₂⟩).1 := congrArg Subtype.val hd
            exact Subtype.ext (congrArg (fun x : F.Direction (F.shapeRestr g a).1 i ↦
              (Sum.inr x.1 : (P.fam (F.shapeRestr g a).1).carrier ⊕ F.B (F.shapeRestr g a).1))
              ((hF g a i).1 (Subtype.ext (Sum.inr.inj hv))))
  · rintro ⟨b, h⟩
    cases b with
    | inl c =>
        obtain ⟨e, he⟩ := (hPb g a i).2 ⟨c, h⟩
        exact ⟨⟨Sum.inl e.1, e.2⟩,
          Subtype.ext (congrArg (fun x : (P.fam a.1).Dir i ↦
            (Sum.inl x.1 : (P.fam a.1).carrier ⊕ F.B a.1)) he)⟩
    | inr b =>
        obtain ⟨e, he⟩ := (hF g a i).2 ⟨b, h⟩
        exact ⟨⟨Sum.inr e.1, e.2⟩,
          Subtype.ext (congrArg (fun x : F.Direction a.1 i ↦
            (Sum.inr x.1 : (P.fam a.1).carrier ⊕ F.B a.1)) he)⟩

/-- Bijective reindexing is inherited by `δ` at a constant arity, whose
reindexing is the identity.

With `hasBijectiveReindex_coprod` and the two `iota` cases, this is the
syntactic form of the argument recorded in `PresheafIRProto.Basic`'s `Reindex`
section: everything the presheaf reading of the `ι` / `σ` / `δ` rules of
[HancockMcBrideGhaniMalatestaAltenkirch2013] generates has bijective
reindexing. -/
theorem hasBijectiveReindex_deltaConst (G : DomArity.{uI, uB, vI} I) (hG : G.IsFunctorial)
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (hF : HasBijectiveReindex F) :
    HasBijectiveReindex (delta F (ShapeArity.const F.toPresheafPFunctorData G)
      (ShapeArity.isFunctorial_const F G hG)) :=
  hasBijectiveReindex_delta F _ _ hF (by intro j j' g s i; exact Function.bijective_id)

/-- The witness: `arityVaries` has non-bijective reindexing. Its shape presheaf
is terminal, yet the arity over `1` is inhabited while the arity over `0` is
empty, so reindexing along `0 ⟶ 1` is the map out of the empty type.

With `hasBijectiveReindex_deltaConst` this rules out `arityVaries` having a code
in the presheaf reading of the `ι` / `σ` / `δ` rules: `δ` must admit arities
that vary over the output object. The argument is syntactic — it bounds what the
constructions above produce on the nose, not up to isomorphism of the
interpreted functors. -/
theorem not_hasBijectiveReindex_arityVaries : ¬ HasBijectiveReindex arityVaries := by
  intro h
  have hb := (h (homOfLE (show (0 : Fin 2) ≤ 1 by omega))
    (⟨(1 : Fin 2), rfl⟩ : arityVaries.Shape (1 : Fin 2)) (0 : Fin 1)).2
  obtain ⟨d, -⟩ := hb ⟨⟨(0 : Fin 1)⟩, rfl⟩
  exact d.1.down.elim0

end Incompleteness

section VaryingWitness

/-!
The positive counterpart of `not_hasBijectiveReindex_arityVaries`: a `δ` whose
arity varies over the shape presheaf does reach `arityVaries`. The base is
`unitPsh`, whose shape presheaf is terminal and which has no directions, so
every direction of the `δ` comes from the adjoined arity.
-/

set_option linter.checkUnivs false in
/-- Operations of the unit for `δ`: one shape over each output object, no
directions. Its shape presheaf is terminal. -/
def unitPshData (I : Type uI) [Category.{vI} I] (J : Type uJ) [Category.{vJ} J] :
    PresheafPFunctorData.{uI, uJ, uJ, uB, vI, vJ} I J where
  A := J
  B := fun _ ↦ PEmpty
  r := fun x ↦ PEmpty.elim x.2
  q := id
  directionRestr := fun _ {_ _} _g d ↦ PEmpty.elim d.1
  shapeRestr := fun {_ j'} _g _s ↦ ⟨j', rfl⟩
  reindex := fun {_ _} _g _s {_} d ↦ PEmpty.elim d.1

set_option linter.checkUnivs false in
/-- The unit for `δ` is a `PresheafPFunctor`: every `Shape j` is the singleton
`{j}`, and every direction fiber is empty. -/
def unitPsh (I : Type uI) [Category.{vI} I] (J : Type uJ) [Category.{vJ} J] :
    PresheafPFunctor.{uI, uJ, uJ, uB, vI, vJ} I J where
  toPresheafPFunctorData := unitPshData I J
  isFunctorial :=
    { directionRestr_id := by intro a i; funext d; exact PEmpty.elim d.1
      directionRestr_comp := by intro a i i' i'' f g; funext d; exact PEmpty.elim d.1
      shapeRestr_id := by
        intro j
        funext s
        exact Subtype.ext s.2.symm
      shapeRestr_comp := by intro j j' j'' g h; funext s; rfl
      reindex_naturality := by intro j j' g a i i' f; funext d; exact PEmpty.elim d.1
      reindex_id := by intro j a i d; exact PEmpty.elim d.1
      reindex_comp := by intro j j' j'' g h a i d; exact PEmpty.elim d.1 }

/-- The arity of `arityVaries`, presented as a `ShapeArity` over `unitPsh`: one
direction over the shape at `1`, none over the shape at `0`, reindexed along
`0 ⟶ 1` by the map out of the empty type. -/
@[reducible] def arityVariesShapeArity : ShapeArity (unitPshData (Fin 1) (Fin 2)) where
  fam := fun a ↦
    { carrier := arityB a
      proj := fun _ ↦ 0
      restr := fun {_ _} _f d ↦ ⟨d.1, Subsingleton.elim _ _⟩ }
  reindex := fun {_ j'} g s {_} d ↦
    ⟨⟨Fin.castLE
        (show j'.val ≤ s.1.val by
          rw [show (s.1 : Fin 2) = _ from s.2]
          exact leOfHom g)
        d.1.down⟩,
      Subsingleton.elim _ _⟩

/-- Each fiber of `arityVariesShapeArity` has at most one element. Stated as a
lemma rather than a `Subsingleton` instance because `DomArity.Dir` is
`@[reducible]`, so instance search sees past it to a bare `Subtype`. -/
theorem arityVariesShapeArity_dir_ext (a : Fin 2) (i : Fin 1)
    (x y : (arityVariesShapeArity.fam a).Dir i) : x = y :=
  Subtype.ext (Subsingleton.elim (α := arityB a) x.1 y.1)

/-- The arity is functorial; its content is not in the laws but in the fibers,
which are empty over `0` and inhabited over `1`. -/
theorem isFunctorial_arityVariesShapeArity :
    arityVariesShapeArity.IsFunctorial (unitPsh (Fin 1) (Fin 2)) where
  restr_id := by intro a i; funext d; exact arityVariesShapeArity_dir_ext _ _ _ _
  restr_comp := by intro a i i' i'' f g; funext d; exact arityVariesShapeArity_dir_ext _ _ _ _
  reindex_naturality := by
    intro j j' g s i i' f
    funext d
    exact arityVariesShapeArity_dir_ext _ _ _ _
  reindex_id := by intro j s i d; exact arityVariesShapeArity_dir_ext _ _ _ _
  reindex_comp := by intro j j' j'' g h s i d; exact arityVariesShapeArity_dir_ext _ _ _ _

/-- The `δ` at the varying arity, over the unit. Its universes are pinned so
that the two theorems below elaborate without universe metavariables. -/
def deltaVarying : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Fin 1) (Fin 2) :=
  delta (unitPsh (Fin 1) (Fin 2)) arityVariesShapeArity isFunctorial_arityVariesShapeArity

/-- The `δ`'s directions over the shape at `0` are empty: the adjoined arity is
empty there, and `unitPsh` contributes none. -/
theorem deltaVarying_source_empty
    (d : deltaVarying.Direction (0 : Fin 2) (0 : Fin 1)) : False := by
  obtain ⟨b, -⟩ := d
  cases b with
  | inl c => exact (ULift.down c).elim0
  | inr e => exact e.elim

/-- The `δ` at that varying arity has non-bijective reindexing, so it lies
outside the class `hasBijectiveReindex_deltaConst` bounds. Admitting arities
that vary over the shape presheaf is therefore not a convenience but the
difference between reaching `arityVaries` and not. -/
theorem not_hasBijectiveReindex_deltaVarying : ¬ HasBijectiveReindex deltaVarying := by
  intro h
  have w : deltaVarying.Direction (1 : Fin 2) (0 : Fin 1) :=
    ⟨Sum.inl (ULift.up (0 : Fin 1)), rfl⟩
  obtain ⟨d, -⟩ := (h (homOfLE (show (0 : Fin 2) ≤ 1 by omega))
    (⟨(1 : Fin 2), rfl⟩ : deltaVarying.Shape (1 : Fin 2)) (0 : Fin 1)).2 w
  exact deltaVarying_source_empty d

end VaryingWitness


end GebProto
