/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.PresheafIRProto.Basic
public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Prototype: code combinators at the presheaf p.r.a. level

Throwaway exploration, not upstream-eligible content. Continues
`PresheafIRProto.Basic` with the semantic counterparts of the code
constructors of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013],
generalized from families to presheaves. `Basic` supplies the `ι` case
(`iotaPresheaf`, `iotaConst`); this module supplies `σ` and `δ`.

## Main definitions

* `GebProto.coprodData` / `GebProto.coprod` — the coproduct of a family of
  presheaf p.r.a. functors indexed by a type. The base change is `sigmaPsh`;
  `coprod` enters only through `deltaRec`.
* `GebProto.DomArity` — a presheaf on `I` unbundled, in the presentation
  `PresheafDomPFunctorData` uses for its arities.
* `GebProto.ShapeArity` / `GebProto.ShapeArity.const` — the arity a `δ` adjoins,
  varying over the shape presheaf, and the constant one.
* `GebProto.adjoinArityData` / `GebProto.adjoinArity` — the `δ` case: adjoin a `ShapeArity`
  to every arity of a functor.
* `GebProto.BaseArity` / `GebProto.BaseArity.pullback` — the arity a code's `δ`
  carries, indexed by output objects rather than by shapes, and its pullback
  along a functor's shape-output map to the `ShapeArity` that `adjoinArity` consumes.
* `GebProto.HasBijectiveReindex` — the property that every reindexing map is a
  bijection.
* `GebProto.ElObj` / `GebProto.elCategory` — the category of elements of a
  presheaf on `J`, as a base category; presheaves on it are the slice
  `PSh(J)/S`.
* `GebProto.sigmaLiftHom` / `GebProto.sigmaPshData` / `GebProto.sigmaPsh` — the
  `σ` case: push a functor over the base `ElObj S` forward along the projection
  to `J`.
* `GebProto.elEqToHom` — the transport in the category of elements, with its
  underlying `J`-morphism definitionally an `eqToHom`.
* `GebProto.unitPsh` — the unit for `δ`: terminal shape presheaf, no directions.
* `GebProto.arityVariesShapeArity` / `GebProto.adjoinArityVarying` — the arity of
  `arityVaries` as a `ShapeArity` over `unitPsh`, and the `δ` at it.
* `GebProto.PshMor` — a morphism from a `DomArity` to a presheaf, unbundled:
  the decodings a `δ`'s continuation may depend on.
* `GebProto.fibreArity` — the arity a decoding adjoins, its fibres.
* `GebProto.deltaRec` — the `δ` whose continuation depends on the decoding,
  as a coproduct over the decodings of non-recursive `δ`s.
* `GebProto.decPresheaf` / `GebProto.decArity` / `GebProto.delta` — the
  decodings of an output-varying arity as a presheaf on the output base, the
  arity indexed by that presheaf's elements, and the `δ` carrying both
  features.
* `GebProto.CodeShape` / `GebProto.CodeDir` / `GebProto.CodeNext` /
  `GebProto.codePFunctor` — the polynomial functor on `Cat` whose W-type is the
  type of codes, and `GebProto.Code`, that W-type.
* `GebProto.praCode` / `GebProto.deltaCode` — the two code constructors. `pra`
  abbreviates parametric right adjoint: the leaf injects a presheaf p.r.a.
  functor as it stands, and `δ` adjoins an arity with a decoding-indexed
  continuation.
* `GebProto.Interp` — the interpretation's target, a presheaf p.r.a. functor
  paired with the base category it lands in.
* `GebProto.deltaCodeVaries` — a `δ` code whose interpretation lies outside the
  bound.
* `GebProto.codeAlgOn` / `GebProto.codeAlg` / `GebProto.interp` — the
  interpretation of a code node, the slice algebra it assembles into, and the
  fold.

## Main statements

* `GebProto.hasBijectiveReindex_iotaPresheaf`,
  `GebProto.hasBijectiveReindex_iotaConst`,
  `GebProto.hasBijectiveReindex_coprod`,
  `GebProto.hasBijectiveReindex_adjoinArityConst`, `GebProto.hasBijectiveReindex_unitPsh`,
  `GebProto.hasBijectiveReindex_sigmaPsh` — every generator and operation of the
  constant-arity fragment has, or preserves, bijective reindexing.
* `GebProto.hasBijectiveReindex_adjoinArity` — a `δ`'s reindexing is bijective when
  the adjoined arity's is. The converse is not proved.
* `GebProto.not_hasBijectiveReindex_arityVaries` — `arityVaries` is not such a
  functor, so those rules do not generate it.
* `GebProto.not_hasBijectiveReindex_adjoinArityVarying` — a `δ` at an arity that does
  vary over the shape presheaf is not such a functor either, so the extended
  rule reaches past the bound.
* `GebProto.BaseArity.isFunctorial_pullback` — the pullback of a functorial
  `BaseArity` is functorial, so a code's `δ` need not mention its subcode's
  shapes.
* `GebProto.sigmaPsh_shapeRestr_id`, `GebProto.sigmaPsh_shapeRestr_comp`,
  `GebProto.sigmaPsh_reindex_naturality`, `GebProto.sigmaPsh_reindex_id`,
  `GebProto.sigmaPsh_reindex_comp` — the five laws the `σ` case does not
  inherit unchanged from its subfunctor.
* `GebProto.elObj_eq_of_hom` / `GebProto.elHom_eq_eqToHom_comp` — the source of
  a morphism of elements is determined by its base and its underlying
  `J`-morphism, and two morphisms with equal underlying `J`-morphisms differ by
  that transport.
* `GebProto.interp_praCode`, `GebProto.interp_deltaCode` — the interpretation's
  computation rules, one per constructor, each definitional. The first of them
  is what makes the interpretation surjective on objects.
* `GebProto.interp_praCode_interp` — every code has the interpretation of a
  one-node code, so `δ` adds no functor the leaf does not already supply.
* `GebProto.hasBijectiveReindex_deltaRec` — the recursion alone does not reach
  past the bound.
* `GebProto.interp_deltaCodeVaries`,
  `GebProto.not_hasBijectiveReindex_interp_deltaCodeVaries` — that bound
  restated about a code rather than about the semantic operations.
* `GebProto.interp_fst` — a code's index is the base its interpretation lands
  in.
* `GebProto.not_hasBijectiveReindex_deltaVaries` — the fused `δ` at an
  output-varying arity lies outside the bound, so fusing the decoding-indexed
  continuation onto the rule does not cost the output-varying arity.
* `GebProto.subsingleton_pshMor_to_terminal` — at the terminal decoding the
  recursion degenerates.

## Implementation notes

`ShapeArity` indexes the adjoined arity by `F`'s shapes rather than by output
objects, which is what keeps `adjoinArityData` free of transports: the arity of the
shape `a` is `fam a`, not `fam (F.q a)` transported along `a`'s membership
proof. Its `IsFunctorial` mirrors `PresheafPFunctorData.IsFunctorial` clause for
clause, so `adjoinArity`'s law proofs split over the two direction summands into the
arity's law and `F`'s.

`BaseArity.pullback` is where the transport `ShapeArity` avoids reappears: its
reindexing runs along `g` conjugated by the two shape-membership proofs, so its
two transported laws reduce to equalities of `J`-morphisms built from
`eqToHom`s. `BaseArity.reindex_eqToHom`, `BaseArity.reindex_cast_shape` and
`BaseArity.reindex_comp_apply` are the three lemmas that reduction needs.

The `σ` case's laws are `eqToHom` bookkeeping over `ElObj S`. Two devices carry
them. `elEqToHom` is a transport whose underlying `J`-morphism reduces
definitionally, because `eqToHom` is opaque to `rw` and `simp` and blocks the
`J`-level identities the laws reduce to. And the reindexing laws are stated and
combined through `HEq`, because a direction over a restricted shape and its
counterpart over the same shape reached by a different route have types that
agree only once the morphisms are identified; `reindex_heq_congr_shape`,
`reindex_heq_eqToHom`, `reindex_eq_of_eq_comp` and
`reindex_eq_of_eq_eqToHom_comp` are the resulting toolkit.

The code type is the W-type of a slice polynomial functor on `Cat`, not an
inductive family: the index is a base category, which `δ` replaces by the
category of elements of its decoding presheaf. `Cat.{v, u}` is closed under
that step because the category of elements of a presheaf valued in `Type u` on
a base in `Type u` is again in `Type u`, with homs a subtype of the base's. The
arity carrier universe is pinned to the base's, which the prototype does not
need to vary. Nothing here is defined simultaneously with anything else, so no
inductive-inductive definition or encoding of one is required.

The generators the codes had before `pra` — `iotaPresheaf`, `unitPshLift`,
`sigmaPsh`, `adjoinArity` — remain as semantic operations, and the results
about them stand: `elSliceEquiv`, the `HasBijectiveReindex` bound, and
`praWitnessLift` measure what a generated fragment reaches. They are no longer
code constructors, because a code built from them is `praCode` of their
composite and records nothing further.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

prototype, inductive-recursive, presheaf, parametric right adjoint
-/

@[expose] public section

universe uI uJ uA uB uS uD vI vJ u v

open CategoryTheory

namespace GebProto

section Coprod

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- Operations of the coproduct of an `S`-indexed family of presheaf p.r.a.
functors. This is not the base change, which is `sigmaPsh`. A shape is a
shape of one summand tagged with its index; the directions, both restrictions
and the reindexing are that summand's.
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

/-- The arity as a presheaf on the input base: the fibers of `proj` with their
own restriction. A `DomArity` is the total-space presentation of a discrete
fibration over `I`, and this is the presheaf that fibration classifies. -/
def presheaf (G : DomArity.{uI, uB, vI} I) (hG : G.IsFunctorial) : Iᵒᵖ ⥤ Type uB where
  obj i := G.Dir i.unop
  map f := ↾ G.restr f.unop
  map_id i := by
    ext c
    exact congrArg Subtype.val (congrFun (hG.restr_id i.unop) c)
  map_comp f g := by
    ext c
    exact congrArg Subtype.val (congrFun (hG.restr_comp f.unop g.unop) c)

/-- Every presheaf on the input base arises as an arity: its total space is the
carrier and its projection the base-point map. -/
def ofPresheaf (P : Iᵒᵖ ⥤ Type uB) : DomArity.{uI, max uI uB, vI} I where
  carrier := Σ i : I, P.obj ⟨i⟩
  proj := Sigma.fst
  restr := fun {_ i'} f c ↦
    match c with
    | ⟨⟨_, x⟩, rfl⟩ => ⟨⟨i', P.map f.op x⟩, rfl⟩

/-- `ofPresheaf` lands in the functorial arities, its two laws being `P`'s. -/
theorem isFunctorial_ofPresheaf (P : Iᵒᵖ ⥤ Type uB) :
    (ofPresheaf.{uI, uB, vI} P).IsFunctorial where
  restr_id := by
    intro i
    funext c
    obtain ⟨⟨_, x⟩, rfl⟩ := c
    refine Subtype.ext (congrArg (Sigma.mk _) ?_)
    simp
    rfl
  restr_comp := by
    intro i i' i'' f g
    funext c
    obtain ⟨⟨_, x⟩, rfl⟩ := c
    refine Subtype.ext (congrArg (Sigma.mk _) ?_)
    simp
    rfl

/-- The fibers of `ofPresheaf P` are `P`'s own values. Stated fiberwise rather
than as an isomorphism of presheaves because `ofPresheaf` raises the carrier's
universe from `uB` to `max uI uB`, so the two presheaves inhabit different
functor categories. -/
def dirEquivOfPresheaf (P : Iᵒᵖ ⥤ Type uB) (i : I) :
    (ofPresheaf.{uI, uB, vI} P).Dir i ≃ P.obj ⟨i⟩ where
  toFun := fun c ↦ match c with | ⟨⟨_, x⟩, rfl⟩ => x
  invFun := fun x ↦ ⟨⟨i, x⟩, rfl⟩
  left_inv := by rintro ⟨⟨_, x⟩, rfl⟩; rfl
  right_inv := by intro x; rfl

/-- That equivalence carries `ofPresheaf`'s restriction to `P`'s own action, so
the two agree as presheaves and not merely fiberwise. -/
theorem dirEquivOfPresheaf_restr (P : Iᵒᵖ ⥤ Type uB) ⦃i i' : I⦄ (f : i' ⟶ i)
    (c : (ofPresheaf.{uI, uB, vI} P).Dir i) :
    dirEquivOfPresheaf.{uI, uB, vI} P i' ((ofPresheaf P).restr f c) =
      P.map f.op (dirEquivOfPresheaf P i c) := by
  obtain ⟨⟨_, x⟩, rfl⟩ := c
  rfl

/-- The other round trip: an arity's carrier is the total space of its fibers,
which is the object part of the category of elements of `presheaf`. -/
def sigmaDirEquivCarrier (G : DomArity.{uI, uB, vI} I) : (Σ i : I, G.Dir i) ≃ G.carrier where
  toFun := fun x ↦ x.2.1
  invFun := fun c ↦ ⟨G.proj c, ⟨c, rfl⟩⟩
  left_inv := by rintro ⟨_, ⟨c, rfl⟩⟩; rfl
  right_inv := by intro c; rfl

end DomArity

end Arity

section Delta

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

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

/-- Operations of the `δ` case: adjoin the arity `P` to every arity of `F`,
leaving the shapes untouched. -/
def adjoinArityData (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) (P : ShapeArity F) :
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
theorem adjoinArity_cast_inl {j : J} {i : I} {t t' : F.Shape j} (e : t = t')
    (d : (P.fam t.1).Dir i) :
    cast (congrArg (fun u : F.Shape j ↦ (adjoinArityData F P).Direction u.1 i) e)
        (⟨Sum.inl d.1, d.2⟩ : (adjoinArityData F P).Direction t.1 i) =
      ⟨Sum.inl (cast (congrArg (fun u : F.Shape j ↦ (P.fam u.1).Dir i) e) d).1,
        (cast (congrArg (fun u : F.Shape j ↦ (P.fam u.1).Dir i) e) d).2⟩ := by
  cases e
  rfl

/-- Transport of an original direction along an equality of shapes is the
transport of that direction inside `F`. -/
theorem adjoinArity_cast_inr {j : J} {i : I} {t t' : F.Shape j} (e : t = t')
    (d : F.Direction t.1 i) :
    cast (congrArg (fun u : F.Shape j ↦ (adjoinArityData F P).Direction u.1 i) e)
        (⟨Sum.inr d.1, d.2⟩ : (adjoinArityData F P).Direction t.1 i) =
      ⟨Sum.inr (cast (congrArg (fun u : F.Shape j ↦ F.Direction u.1 i) e) d).1,
        (cast (congrArg (fun u : F.Shape j ↦ F.Direction u.1 i) e) d).2⟩ := by
  cases e
  rfl

/-- Adjoining an arity to a presheaf p.r.a. functor yields one: the shape-side
laws are `F`'s unchanged, and each direction-side law splits over the two
summands into the arity's law and `F`'s.

This is not `δ`. It is `δ`'s direction-adjoining half; `delta` is the rule,
and adds the coproduct over decodings that this leaves out. -/
def adjoinArity (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (P : ShapeArity F.toPresheafPFunctorData) (hP : P.IsFunctorial F) :
    PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J where
  toPresheafPFunctorData := adjoinArityData F.toPresheafPFunctorData P
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
            refine Eq.trans ?_ (adjoinArity_cast_inl F.toPresheafPFunctorData P
              (congrFun (F.isFunctorial.shapeRestr_id j) a) ⟨c, h⟩).symm
            exact Subtype.ext (congrArg (fun x : (P.fam a.1).Dir i ↦ Sum.inl x.1)
              (hP.reindex_id a ⟨c, h⟩))
        | inr b =>
            refine Eq.trans ?_ (adjoinArity_cast_inr F.toPresheafPFunctorData P
              (congrFun (F.isFunctorial.shapeRestr_id j) a) ⟨b, h⟩).symm
            exact Subtype.ext (congrArg (fun x : F.Direction a.1 i ↦ Sum.inr x.1)
              (F.isFunctorial.reindex_id a ⟨b, h⟩))
      reindex_comp := by
        intro j j' j'' g h a i d
        obtain ⟨b, hb⟩ := d
        cases b with
        | inl c =>
            refine Eq.trans ?_ (congrArg (fun z ↦
              (adjoinArityData F.toPresheafPFunctorData P).reindex g a
                ((adjoinArityData F.toPresheafPFunctorData P).reindex h
                  ((adjoinArityData F.toPresheafPFunctorData P).shapeRestr g a) z))
              (adjoinArity_cast_inl F.toPresheafPFunctorData P
                (congrFun (F.isFunctorial.shapeRestr_comp g h) a) ⟨c, hb⟩)).symm
            exact Subtype.ext (congrArg (fun x : (P.fam a.1).Dir i ↦ Sum.inl x.1)
              (hP.reindex_comp g h a ⟨c, hb⟩))
        | inr b =>
            refine Eq.trans ?_ (congrArg (fun z ↦
              (adjoinArityData F.toPresheafPFunctorData P).reindex g a
                ((adjoinArityData F.toPresheafPFunctorData P).reindex h
                  ((adjoinArityData F.toPresheafPFunctorData P).shapeRestr g a) z))
              (adjoinArity_cast_inr F.toPresheafPFunctorData P
                (congrFun (F.isFunctorial.shapeRestr_comp g h) a) ⟨b, hb⟩)).symm
            exact Subtype.ext (congrArg (fun x : F.Direction a.1 i ↦ Sum.inr x.1)
              (F.isFunctorial.reindex_comp g h a ⟨b, hb⟩)) }

section Base

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The arity a code's `δ` carries: a presheaf on `I` for each *output object*,
with a reindexing along `J`-morphisms. This is the data of a functor
`J ⥤ (Iᵒᵖ ⥤ Type)`, unbundled.

A code's `δ` must be indexed this way rather than by shapes: the shapes belong
to the subcode's interpretation, which a code cannot mention. `pullback`
converts it to the shape-indexed `ShapeArity` that `adjoinArity` consumes. -/
structure BaseArity (I : Type uI) [Category.{vI} I] (J : Type uJ) [Category.{vJ} J] :
    Type (max (uB + 1) uI uJ vI vJ) where
  /-- The presheaf on `I` carried over each output object. -/
  fam : J → DomArity.{uI, uB, vI} I
  /-- Reindexing along a `J`-morphism, covariant, matching the direction of
  `PresheafPFunctorData.reindex`. -/
  reindex : ∀ ⦃j j' : J⦄, (j' ⟶ j) → ∀ ⦃i : I⦄, (fam j').Dir i → (fam j).Dir i

namespace BaseArity

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

/-- Each fibrewise arity of a functorial `BaseArity` is itself functorial: the
first two clauses of `IsFunctorial` are `DomArity.IsFunctorial` at each output
object. -/
theorem isFunctorial_fam (hP : P.IsFunctorial) (j : J) : (P.fam j).IsFunctorial where
  restr_id := hP.restr_id j
  restr_comp := hP.restr_comp j

/-- The arity carried over the output object `j`, as a presheaf on the input
base — equivalently, as the discrete fibration over `I` that `δ` adjoins
there. -/
def famPresheaf (hP : P.IsFunctorial) (j : J) : Iᵒᵖ ⥤ Type uB :=
  (P.fam j).presheaf (isFunctorial_fam P hP j)

/-- Reindexing along a `J`-morphism is a morphism of those presheaves. Stated as
a bare `NatTrans` rather than as a functor-category `⟶`, which would need the
`Classical.choice`-dependent `Functor.category` instance. -/
def reindexHom (hP : P.IsFunctorial) ⦃j j' : J⦄ (g : j' ⟶ j) :
    NatTrans (famPresheaf P hP j') (famPresheaf P hP j) where
  app i := ↾ P.reindex g (i := i.unop)
  naturality := by
    intro i i' f
    ext d
    simp only [TypeCat.Fun.toFun_apply, comp_apply, ConcreteCategory.hom_ofHom]
    exact congrFun (hP.reindex_naturality g f.unop).symm d

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

/-- Reindexing after a transport along an equality of shapes is reindexing
along the composite with that equality's `eqToHom`. -/
theorem reindex_cast_shape (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J)
    {j : J} {t t' : F.Shape j} (hh : t = t') {x : J} (k : F.q t'.1 ⟶ x) {i : I}
    (d : (P.fam (F.q t.1)).Dir i) :
    P.reindex k (cast (congrArg (fun u : F.Shape j ↦ (P.fam (F.q u.1)).Dir i) hh) d) =
      P.reindex (eqToHom (congrArg (fun u : F.Shape j ↦ F.q u.1) hh) ≫ k) d := by
  cases hh
  simp

/-- Pull a `BaseArity` back along a functor's shape-output map: the arity over
the shape `a` is the arity over `F.q a`, reindexed along the `J`-morphism `g`
transported by the two shape-membership proofs. -/
def pullback (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) : ShapeArity F where
  fam := fun a ↦ P.fam (F.q a)
  reindex := fun {_ _} g s {_} d ↦
    P.reindex (eqToHom (F.shapeRestr g s).2 ≫ g ≫ eqToHom s.2.symm) d

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

/-- The underlying `J`-morphism of an identity in the category of elements. -/
@[simp] theorem elCategory_id_val (S : Jᵒᵖ ⥤ Type uS) (x : ElObj.{uJ, uS, vJ} S) :
    (𝟙 x : x ⟶ x).1 = 𝟙 x.1 := rfl

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

/-- The transport morphism in the category of elements, defined so that its
underlying `J`-morphism is definitionally an `eqToHom`. `eqToHom` itself is
opaque under `rw` and `simp`, which blocks the `J`-level identities the `σ`
laws reduce to. -/
def elEqToHom (S : Jᵒᵖ ⥤ Type uS) {x y : ElObj.{uJ, uS, vJ} S} (h : x = y) : x ⟶ y :=
  ⟨eqToHom (congrArg Sigma.fst h), by cases h; simp⟩

/-- `elEqToHom` is the categorical transport. Deliberately not `@[simp]`: the
`J`-level identities the `σ` laws reduce to need the `elEqToHom` form. -/
theorem elEqToHom_eq (S : Jᵒᵖ ⥤ Type uS) {x y : ElObj.{uJ, uS, vJ} S} (h : x = y) :
    elEqToHom S h = eqToHom h := by
  cases h
  rfl

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

/-- The `σ` operation preserves the shape-restriction composition law. -/
theorem sigmaPsh_shapeRestr_comp (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctor.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S)) :
    (sigmaPshData S F.toPresheafPFunctorData).ShapeRestrComp := by
  intro j j' j'' g h
  funext s
  obtain ⟨a, rfl⟩ := s
  refine Subtype.ext ?_
  change (F.shapeRestr (sigmaLiftHom S F.toPresheafPFunctorData (h ≫ g) ⟨a, rfl⟩) ⟨a, rfl⟩).1 =
    (F.shapeRestr (sigmaLiftHom S F.toPresheafPFunctorData h
        ((sigmaPshData S F.toPresheafPFunctorData).shapeRestr g ⟨a, rfl⟩))
      ⟨(F.shapeRestr (sigmaLiftHom S F.toPresheafPFunctorData g ⟨a, rfl⟩) ⟨a, rfl⟩).1, rfl⟩).1
  set Lg := sigmaLiftHom S F.toPresheafPFunctorData g ⟨a, rfl⟩ with hLgdef
  set b := F.shapeRestr Lg ⟨a, rfl⟩ with hbdef
  set Lh := sigmaLiftHom S F.toPresheafPFunctorData h
    ((sigmaPshData S F.toPresheafPFunctorData).shapeRestr g ⟨a, rfl⟩) with hLhdef
  have hval : (sigmaLiftHom S F.toPresheafPFunctorData (h ≫ g) ⟨a, rfl⟩).1 =
      eqToHom (rfl : j'' = j'') ≫ ((Lh ≫ elEqToHom S b.2) ≫ Lg).1 := by
    simp [hLhdef, hLgdef, sigmaLiftHom, elEqToHom]
  have hsplit : (F.shapeRestr (Lh ≫ elEqToHom S b.2) b).1 = (F.shapeRestr Lh ⟨b.1, rfl⟩).1 := by
    refine Eq.trans (congrArg Subtype.val
      (congrFun (F.isFunctorial.shapeRestr_comp (elEqToHom S b.2) Lh) b)) ?_
    refine congrArg (fun t ↦ (F.shapeRestr Lh t).1) ?_
    rw [elEqToHom_eq, shapeRestr_eqToHom]
    exact Subtype.ext (cast_shape_val F.toPresheafPFunctorData b.2.symm b)
  rw [elHom_eq_eqToHom_comp S (sigmaLiftHom S F.toPresheafPFunctorData (h ≫ g) ⟨a, rfl⟩)
      ((Lh ≫ elEqToHom S b.2) ≫ Lg) rfl hval,
    shapeRestr_val_eqToHom_comp,
    congrFun (F.isFunctorial.shapeRestr_comp Lg (Lh ≫ elEqToHom S b.2)) ⟨a, rfl⟩,
    Function.comp_apply]
  exact hsplit

/-- The `σ` operation preserves the reindexing naturality law: its shapes and
directions are the subfunctor's unchanged. -/
theorem sigmaPsh_reindex_naturality (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctor.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S)) :
    (sigmaPshData S F.toPresheafPFunctorData).ReindexNaturality := by
  intro j j' g s i i' f
  exact F.isFunctorial.reindex_naturality (sigmaLiftHom S F.toPresheafPFunctorData g s)
    ⟨s.1, rfl⟩ f

/-- Reindexing along a transport is heterogeneously the identity. -/
theorem reindex_heq_eqToHom {K : Type uK} [Category.{vK} K]
    (F : PresheafPFunctor.{uI, uK, uA, uB, vI, vK} I K) {x y : K} {m : x ⟶ y} (h : x = y)
    (hm : m = eqToHom h) (s : F.Shape y) {i : I}
    (d : F.Direction (F.shapeRestr m s).1 i) : HEq (F.reindex m s d) d := by
  cases hm
  cases h
  exact HEq.trans (heq_of_eq (F.isFunctorial.reindex_id s d)) (cast_heq _ d)

/-- Reindexing along a composite factors, on heterogeneously equal
directions. -/
theorem reindex_eq_of_eq_comp {K : Type uK} [Category.{vK} K]
    (F : PresheafPFunctor.{uI, uK, uA, uB, vI, vK} I K) {x y z : K} {m : x ⟶ z}
    (m₁ : x ⟶ y) (m₂ : y ⟶ z) (hm : m = m₁ ≫ m₂) (s : F.Shape z) {i : I}
    (d : F.Direction (F.shapeRestr m s).1 i)
    (d' : F.Direction (F.shapeRestr m₁ (F.shapeRestr m₂ s)).1 i) (hd : HEq d d') :
    F.reindex m s d = F.reindex m₂ s (F.reindex m₁ (F.shapeRestr m₂ s) d') := by
  cases hm
  refine Eq.trans (F.isFunctorial.reindex_comp m₂ m₁ s d) ?_
  exact congrArg (fun z ↦ F.reindex m₂ s (F.reindex m₁ (F.shapeRestr m₂ s) z))
    (eq_of_heq (HEq.trans (cast_heq _ d) hd))

/-- Reindexing is congruent in the shape, on heterogeneously equal
directions. -/
theorem reindex_heq_congr_shape {K : Type uK} [Category.{vK} K]
    (F : PresheafPFunctor.{uI, uK, uA, uB, vI, vK} I K) {x y : K} (m : x ⟶ y)
    {s s' : F.Shape y} (hs : s = s') {i : I}
    (d : F.Direction (F.shapeRestr m s).1 i) (d' : F.Direction (F.shapeRestr m s').1 i)
    (hd : HEq d d') : HEq (F.reindex m s d) (F.reindex m s' d') := by
  cases hs
  cases hd
  rfl

/-- Reindexing along a composite carrying a transport prefix. -/
theorem reindex_eq_of_eq_eqToHom_comp {K : Type uK} [Category.{vK} K]
    (F : PresheafPFunctor.{uI, uK, uA, uB, vI, vK} I K) {w x y z : K} {m : w ⟶ z}
    (e : w = x) (m₁ : x ⟶ y) (m₂ : y ⟶ z) (hm : m = eqToHom e ≫ (m₁ ≫ m₂)) (s : F.Shape z)
    {i : I} (d : F.Direction (F.shapeRestr m s).1 i)
    (d' : F.Direction (F.shapeRestr m₁ (F.shapeRestr m₂ s)).1 i) (hd : HEq d d') :
    F.reindex m s d = F.reindex m₂ s (F.reindex m₁ (F.shapeRestr m₂ s) d') := by
  cases hm
  cases e
  exact reindex_eq_of_eq_comp F m₁ m₂ (Category.id_comp _) s d d' hd

/-- The `σ` operation preserves the reindexing identity law. -/
theorem sigmaPsh_reindex_id (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctor.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S)) :
    (sigmaPshData S F.toPresheafPFunctorData).ReindexId (sigmaPsh_shapeRestr_id S F) := by
  intro j s i d
  obtain ⟨a, rfl⟩ := s
  refine eq_of_heq (HEq.trans ?_ (cast_heq _ d).symm)
  have hsrc : (⟨(F.q a).1, S.map (sigmaLiftHom S F.toPresheafPFunctorData
      (𝟙 ((F.q a).1)) ⟨a, rfl⟩).1.op (F.q a).2⟩ : ElObj S) = F.q a :=
    Sigma.ext rfl (heq_of_eq (by simp [sigmaLiftHom]))
  have hval : (eqToHom hsrc : _ ⟶ F.q a).1 = 𝟙 (F.q a).1 := by
    rw [elCategory_eqToHom_val]
    simp
  have hm : sigmaLiftHom S F.toPresheafPFunctorData (𝟙 ((F.q a).1)) ⟨a, rfl⟩ = eqToHom hsrc :=
    Subtype.ext (by
      simp only [sigmaLiftHom, eqToHom_refl, op_comp, op_id, Category.comp_id]
      exact hval.symm)
  exact reindex_heq_eqToHom F hsrc hm ⟨a, rfl⟩ d

/-- The `σ` operation preserves the reindexing composition law. The chain
follows `sigmaPsh_shapeRestr_comp`: decompose the lifted morphism, split the
reindexing twice, and discard the two transports. -/
theorem sigmaPsh_reindex_comp (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctor.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S)) :
    (sigmaPshData S F.toPresheafPFunctorData).ReindexComp (sigmaPsh_shapeRestr_comp S F) := by
  intro j j' j'' g h s i d
  obtain ⟨a, rfl⟩ := s
  set Lg := sigmaLiftHom S F.toPresheafPFunctorData g ⟨a, rfl⟩ with hLgdef
  set b := F.shapeRestr Lg ⟨a, rfl⟩ with hbdef
  set Lh := sigmaLiftHom S F.toPresheafPFunctorData h
    ((sigmaPshData S F.toPresheafPFunctorData).shapeRestr g ⟨a, rfl⟩) with hLhdef
  have hval : (sigmaLiftHom S F.toPresheafPFunctorData (h ≫ g) ⟨a, rfl⟩).1 =
      eqToHom (rfl : j'' = j'') ≫ ((Lh ≫ elEqToHom S b.2) ≫ Lg).1 := by
    simp [hLhdef, hLgdef, sigmaLiftHom, elEqToHom]
  have hm := elHom_eq_eqToHom_comp S (sigmaLiftHom S F.toPresheafPFunctorData (h ≫ g) ⟨a, rfl⟩)
    ((Lh ≫ elEqToHom S b.2) ≫ Lg) rfl hval
  have hsh : F.shapeRestr (elEqToHom S b.2) b = ⟨b.1, rfl⟩ := by
    rw [elEqToHom_eq, shapeRestr_eqToHom]
    exact Subtype.ext (cast_shape_val F.toPresheafPFunctorData b.2.symm b)
  have hs1 : (F.shapeRestr (sigmaLiftHom S F.toPresheafPFunctorData (h ≫ g) ⟨a, rfl⟩)
      ⟨a, rfl⟩).1 = (F.shapeRestr (Lh ≫ elEqToHom S b.2) b).1 := by
    rw [hm, shapeRestr_val_eqToHom_comp,
      congrFun (F.isFunctorial.shapeRestr_comp Lg (Lh ≫ elEqToHom S b.2)) ⟨a, rfl⟩,
      Function.comp_apply]
  have hs2 : (F.shapeRestr (Lh ≫ elEqToHom S b.2) b).1 =
      (F.shapeRestr Lh (F.shapeRestr (elEqToHom S b.2) b)).1 :=
    congrArg Subtype.val (congrFun (F.isFunctorial.shapeRestr_comp (elEqToHom S b.2) Lh) b)
  refine Eq.trans (reindex_eq_of_eq_eqToHom_comp F _ (Lh ≫ elEqToHom S b.2) Lg hm ⟨a, rfl⟩ d
    (cast (congrArg (fun x ↦ F.Direction x i) hs1) d) (cast_heq _ d).symm) ?_
  refine congrArg (F.reindex Lg ⟨a, rfl⟩ (i := i)) ?_
  refine Eq.trans (reindex_eq_of_eq_comp F Lh (elEqToHom S b.2) rfl b _
    (cast (congrArg (fun x ↦ F.Direction x i) hs2)
      (cast (congrArg (fun x ↦ F.Direction x i) hs1) d)) (cast_heq _ _).symm) ?_
  refine eq_of_heq (HEq.trans (reindex_heq_eqToHom F b.2 (elEqToHom_eq S b.2) b _) ?_)
  have hs3 : (F.shapeRestr Lh (F.shapeRestr (elEqToHom S b.2) b)).1 =
      (F.shapeRestr Lh (⟨b.1, rfl⟩ : F.Shape (F.q b.1))).1 :=
    congrArg (fun t ↦ (F.shapeRestr Lh t).1) hsh
  refine HEq.trans (reindex_heq_congr_shape F Lh hsh _
    (cast (congrArg (fun x ↦ F.Direction x i) hs3) _) (cast_heq _ _).symm) ?_
  refine heq_of_eq (congrArg (F.reindex Lh ⟨b.1, rfl⟩ (i := i)) (eq_of_heq ?_))
  exact (cast_heq _ _).trans ((cast_heq _ _).trans ((cast_heq _ d).trans (cast_heq _ d).symm))

/-- The `σ` case as a `PresheafPFunctor`: pushing a functor over the base
`ElObj S` forward along the projection to `J` yields a presheaf p.r.a. functor.
Its shape presheaf is the total space of `S` paired with the subfunctor's
shapes, which is what lets a later `δ` adjoin an arity varying over the
elements of `S` — the capability `not_hasBijectiveReindex_arityVaries` shows a
`δ` over `J` alone cannot supply. -/
def sigmaPsh (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctor.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S)) :
    PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J where
  toPresheafPFunctorData := sigmaPshData S F.toPresheafPFunctorData
  isFunctorial :=
    { directionRestr_id := F.isFunctorial.directionRestr_id
      directionRestr_comp := F.isFunctorial.directionRestr_comp
      shapeRestr_id := sigmaPsh_shapeRestr_id S F
      shapeRestr_comp := sigmaPsh_shapeRestr_comp S F
      reindex_naturality := sigmaPsh_reindex_naturality S F
      reindex_id := sigmaPsh_reindex_id S F
      reindex_comp := sigmaPsh_reindex_comp S F }

/-- The slice of `ElObj S` over an element collapses to the slice of `J` over
its output object. `el(S) → J` is a discrete fibration, so a morphism into `y₀`
is determined by its image in `J`, the source's `S`-component being forced. -/
def elSliceEquiv (S : Jᵒᵖ ⥤ Type uS) (y₀ : ElObj.{uJ, uS, vJ} S) :
    (Σ y' : ElObj.{uJ, uS, vJ} S, (y' ⟶ y₀)) ≃ (Σ j' : J, (j' ⟶ y₀.1)) where
  toFun x := ⟨x.1.1, x.2.1⟩
  invFun x := ⟨⟨x.1, S.map x.2.op y₀.2⟩, ⟨x.2, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨j', s'⟩, ⟨g, hg⟩⟩
    dsimp only at g hg ⊢
    congr!
  right_inv := by intro x; rfl

/-- That collapse is over `J`: it commutes with the shape-output maps. So
`sigmaPsh S (iotaPresheaf y₀)` and `iotaPresheaf y₀.1` have the same shape
presheaf, and `σ` over `ι` contributes no shapes of its own.

This bounds `sigmaPsh`. Small induction recursion builds an arbitrary shape
set as `σ S K` with `K : S → IR I O` a family of `ι`s, one output index per
element; the presheaf base change takes a single functor over `ElObj S`, so
that functor's own shapes take over and the composite collapses. An arbitrary
shape presheaf is therefore not reachable by `sigmaPsh` over `iotaPresheaf`,
which is what the p.r.a. formula `F Z j = Σ (a : T₁ j), Hom (E ⟨j, a⟩) Z`
requires; `praWitness` reaches it by putting the unit at the foot instead. -/
theorem elSliceEquiv_fst (S : Jᵒᵖ ⥤ Type uS) (y₀ : ElObj.{uJ, uS, vJ} S)
    (x : Σ y' : ElObj.{uJ, uS, vJ} S, (y' ⟶ y₀)) :
    (elSliceEquiv S y₀ x).1 =
      (sigmaPshData S (iotaPresheafData.{uI, max uJ uS, uB, vI, vJ} (I := I) y₀)).q x :=
  rfl

end Sigma

section Incompleteness

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- Every reindexing map of `F` is a bijection. Read informally, and not
established here: the fibres of `objPresheaf F` are then cartesian over the
shape presheaf, restricting a shape along `g : j' ⟶ j` neither discarding nor
inventing directions. -/
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

/-- Bijective reindexing is inherited by `δ` from the adjoined arity's own
reindexing: the two summands of a `δ` direction are reindexed independently.
Only this direction is proved; the converse is not used. -/
theorem hasBijectiveReindex_adjoinArity (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J)
    (P : ShapeArity F.toPresheafPFunctorData) (hP : P.IsFunctorial F)
    (hF : HasBijectiveReindex F)
    (hPb : ∀ ⦃j j' : J⦄ (g : j' ⟶ j) (s : F.Shape j) (i : I),
      Function.Bijective (P.reindex g s (i := i))) :
    HasBijectiveReindex (adjoinArity F P hP) := by
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
theorem hasBijectiveReindex_adjoinArityConst (G : DomArity.{uI, uB, vI} I) (hG : G.IsFunctorial)
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (hF : HasBijectiveReindex F) :
    HasBijectiveReindex (adjoinArity F (ShapeArity.const F.toPresheafPFunctorData G)
      (ShapeArity.isFunctorial_const F G hG)) :=
  hasBijectiveReindex_adjoinArity F _ _ hF (by intro j j' g s i; exact Function.bijective_id)

/-- The witness: `arityVaries` has non-bijective reindexing. Its shape presheaf
is terminal, yet the arity over `1` is inhabited while the arity over `0` is
empty, so reindexing along `0 ⟶ 1` is the map out of the empty type.

With `hasBijectiveReindex_adjoinArityConst` this rules out `arityVaries` being
generated by the presheaf reading of the `ι` / `σ` / `δ` rules of
[HancockMcBrideGhaniMalatestaAltenkirch2013]: `δ` must admit arities
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
arity varies over the shape presheaf carries `arityVaries`'s arity, and so
falls outside the bound. It is not `arityVaries` itself, and nothing here
constructs an isomorphism: `adjoinArityVarying`'s directions are
`arityB a ⊕ PEmpty`, `arityVaries`'s are `arityB a`. The base is `unitPsh`,
whose shape presheaf is terminal and which has no directions, so every
direction of the `δ` comes from the adjoined arity.
-/

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

/-- The unit at the shape universe the representables force. `unitPsh`'s shape
type is `J` itself, at `uJ`, where `iotaPresheaf`'s is the total space of a
hom-family, at `max uJ vJ`; admitting both to one code leaf needs them in one
`PresheafPFunctor` universe, so this lifts the shape type. -/
def unitPshLiftData (I : Type uI) [Category.{vI} I] (J : Type uJ) [Category.{vJ} J] :
    PresheafPFunctorData.{uI, uJ, max uJ vJ, uB, vI, vJ} I J where
  A := ULift.{vJ} J
  B := fun _ ↦ PEmpty
  r := fun x ↦ PEmpty.elim x.2
  q := ULift.down
  directionRestr := fun _ {_ _} _g d ↦ PEmpty.elim d.1
  shapeRestr := fun {_ j'} _g _s ↦ ⟨⟨j'⟩, rfl⟩
  reindex := fun {_ _} _g _a {_} d ↦ PEmpty.elim d.1

/-- The lifted unit is a genuine `PresheafPFunctor`: its direction fibers are
empty and its shape presheaf is terminal. -/
def unitPshLift (I : Type uI) [Category.{vI} I] (J : Type uJ) [Category.{vJ} J] :
    PresheafPFunctor.{uI, uJ, max uJ vJ, uB, vI, vJ} I J where
  toPresheafPFunctorData := unitPshLiftData I J
  isFunctorial :=
    { directionRestr_id := by intro a i; funext d; exact PEmpty.elim d.1
      directionRestr_comp := by intro a i i' i'' f g; funext d; exact PEmpty.elim d.1
      shapeRestr_id := by
        intro j
        funext s
        exact Subtype.ext (congrArg ULift.up s.2.symm)
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
def adjoinArityVarying : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Fin 1) (Fin 2) :=
  adjoinArity (unitPsh (Fin 1) (Fin 2)) arityVariesShapeArity isFunctorial_arityVariesShapeArity

/-- The `δ`'s directions over the shape at `0` are empty: the adjoined arity is
empty there, and `unitPsh` contributes none. -/
theorem adjoinArityVarying_source_empty
    (d : adjoinArityVarying.Direction (0 : Fin 2) (0 : Fin 1)) : False := by
  obtain ⟨b, -⟩ := d
  cases b with
  | inl c => exact (ULift.down c).elim0
  | inr e => exact e.elim

/-- The `δ` at that varying arity has non-bijective reindexing, so it lies
outside the class `hasBijectiveReindex_adjoinArityConst` bounds. Admitting arities
that vary over the shape presheaf is therefore not a convenience but the
difference between reaching `arityVaries` and not. -/
theorem not_hasBijectiveReindex_adjoinArityVarying : ¬ HasBijectiveReindex adjoinArityVarying := by
  intro h
  have w : adjoinArityVarying.Direction (1 : Fin 2) (0 : Fin 1) :=
    ⟨Sum.inl (ULift.up (0 : Fin 1)), rfl⟩
  obtain ⟨d, -⟩ := (h (homOfLE (show (0 : Fin 2) ≤ 1 by omega))
    (⟨(1 : Fin 2), rfl⟩ : adjoinArityVarying.Shape (1 : Fin 2)) (0 : Fin 1)).2 w
  exact adjoinArityVarying_source_empty d

/-- The chain that reaches the p.r.a. formula's data, with the unit at its
foot: `sigmaPsh` at an arbitrary shape presheaf `T`, over `adjoinArity` at an
arbitrary output-indexed arity, over the terminal shape presheaf. -/
def praWitness
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS) (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T))
    (hA : A.IsFunctorial) :
    PresheafPFunctor.{uI, uJ, max uJ uS, max uB 0, vI, vJ} I J :=
  sigmaPsh T (adjoinArity (unitPsh I (ElObj.{uJ, uS, vJ} T)) (A.pullback _)
    (A.isFunctorial_pullback hA _))

/-- Its shape presheaf is `T`: the chain reproduces an arbitrary shape
presheaf, which `σ` over `ι` could not. -/
def praWitnessShapeEquiv
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS)
    (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T)) (hA : A.IsFunctorial) (j : J) :
    (praWitness T A hA).Shape j ≃ T.obj ⟨j⟩ where
  toFun x := match x with | ⟨⟨_, t⟩, rfl⟩ => t
  invFun t := ⟨⟨j, t⟩, rfl⟩
  left_inv := by rintro ⟨⟨j', t⟩, rfl⟩; rfl
  right_inv := by intro t; rfl

/-- Its directions at a shape are that shape's arity, so the chain reproduces
an arbitrary arity as well. -/
def praWitnessDirEquiv
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS)
    (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T)) (hA : A.IsFunctorial)
    (a : (praWitness T A hA).A) (i : I) :
    (praWitness T A hA).Direction a i ≃ (A.fam a).Dir i where
  toFun d := match d with | ⟨Sum.inl c, h⟩ => ⟨c, h⟩ | ⟨Sum.inr e, _⟩ => e.elim
  invFun c := ⟨Sum.inl c.1, c.2⟩
  left_inv := by
    rintro ⟨c | e, h⟩
    · rfl
    · exact e.elim
  right_inv := by intro c; rfl

/-- `praWitness` with the lifted unit at its foot, which is the form that
lives at the shape universe `Interp` pins. -/
def praWitnessLift
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS) (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T))
    (hA : A.IsFunctorial) :
    PresheafPFunctor.{uI, uJ, max uJ uS vJ, max uB 0, vI, vJ} I J :=
  sigmaPsh T (adjoinArity (unitPshLift I (ElObj.{uJ, uS, vJ} T)) (A.pullback _)
    (A.isFunctorial_pullback hA _))

/-- The `T`-component of a shape of the chain, transported to the object that
shape lies over. Named rather than written inline so that the naturality lemma
can be stated about it with no `Equiv` coercion in the way, which is what
blocks reduction. -/
def praWitnessLiftShapeVal
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS) (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T))
    (hA : A.IsFunctorial) {j : J} (x : (praWitnessLift T A hA).Shape j) : T.obj ⟨j⟩ :=
  cast (congrArg (fun k ↦ T.obj ⟨k⟩) x.2) x.1.down.2

/-- It is natural in `J`, so the chain's shape presheaf and `T` agree as
presheaves and not merely fibrewise. -/
theorem praWitnessLiftShapeVal_naturality
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS) (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T))
    (hA : A.IsFunctorial) ⦃j j' : J⦄ (g : j' ⟶ j)
    (x : (praWitnessLift T A hA).Shape j) :
    praWitnessLiftShapeVal T A hA ((praWitnessLift T A hA).shapeRestr g x) =
      T.map g.op (praWitnessLiftShapeVal T A hA x) := by
  obtain ⟨⟨⟨jj, t⟩⟩, hj⟩ := x
  have hj' : jj = j := hj
  subst hj'
  dsimp only [praWitnessLiftShapeVal, praWitnessLift, sigmaPsh, sigmaPshData, adjoinArity,
    adjoinArityData, unitPshLift, unitPshLiftData]
  simp only [eqToHom_refl, Category.comp_id]
  rfl

/-- Its shape presheaf is `T` objectwise; `praWitnessLiftShapeVal_naturality`
makes it an isomorphism of presheaves. -/
def praWitnessLiftShapeEquiv
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS) (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T))
    (hA : A.IsFunctorial) (j : J) :
    (praWitnessLift T A hA).Shape j ≃ T.obj ⟨j⟩ where
  toFun x := praWitnessLiftShapeVal T A hA x
  invFun t := ⟨⟨⟨j, t⟩⟩, rfl⟩
  left_inv := by rintro ⟨⟨⟨j', t⟩⟩, rfl⟩; rfl
  right_inv := by intro t; rfl

/-- Its directions at a shape are that shape's arity. -/
def praWitnessLiftDirEquiv
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS) (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T))
    (hA : A.IsFunctorial) (a : (praWitnessLift T A hA).A) (i : I) :
    (praWitnessLift T A hA).Direction a i ≃ (A.fam a.down).Dir i where
  toFun d := match d with | ⟨Sum.inl c, h⟩ => ⟨c, h⟩ | ⟨Sum.inr e, _⟩ => e.elim
  invFun c := ⟨Sum.inl c.1, c.2⟩
  left_inv := by
    rintro ⟨c | e, h⟩
    · rfl
    · exact e.elim
  right_inv := by intro c; rfl

/-- And compatibly with restriction along an input morphism, so the arity too
is matched as a presheaf. -/
theorem praWitnessLiftDirEquiv_restr
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (T : Jᵒᵖ ⥤ Type uS) (A : BaseArity.{uI, max uJ uS, uB, vI, vJ} I (ElObj T))
    (hA : A.IsFunctorial) (a : (praWitnessLift T A hA).A) ⦃i i' : I⦄ (f : i' ⟶ i)
    (d : (praWitnessLift T A hA).Direction a i) :
    praWitnessLiftDirEquiv T A hA a i' ((praWitnessLift T A hA).directionRestr a f d) =
      (A.fam a.down).restr f (praWitnessLiftDirEquiv T A hA a i d) := by
  obtain ⟨c | e, h⟩ := d
  · rfl
  · exact e.elim

end VaryingWitness

section Closure

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

/-- The unit has bijective reindexing: it has no directions at all. -/
theorem hasBijectiveReindex_unitPsh :
    HasBijectiveReindex (unitPsh.{uI, uJ, uB, vI, vJ} I J) := by
  intro j j' g a i
  exact ⟨fun x _ _ ↦ PEmpty.elim x.1, fun y ↦ PEmpty.elim y.1⟩

/-- Bijective reindexing is inherited by the `σ` base change: its reindexing is
its subfunctor's, at the lifted morphism. -/
theorem hasBijectiveReindex_sigmaPsh (S : Jᵒᵖ ⥤ Type uS)
    (F : PresheafPFunctor.{uI, max uJ uS, uA, uB, vI, vJ} I (ElObj S))
    (hF : HasBijectiveReindex F) : HasBijectiveReindex (sigmaPsh S F) := by
  intro j j' g s i
  exact hF (sigmaLiftHom S F.toPresheafPFunctorData g s) ⟨s.1, rfl⟩ i

end Closure

section Decoding

variable {I : Type uI} [Category.{vI} I]

/-- A morphism of presheaves on `I`, unbundled. This is the type `δ`'s subcode
family is indexed by once a decoding presheaf is supplied: the analogue of
`IR.delta`'s `B → I`, and of the sections `(p : P) → D (i p)` of Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013].

Unbundled for the usual reason: `P ⟶ D` between objects of a presheaf category
would draw in `Classical.choice`. -/
@[ext] structure PshMor (G : DomArity.{uI, uD, vI} I) (D : Iᵒᵖ ⥤ Type uD) :
    Type (max uI uD vI) where
  /-- The components. -/
  app : ∀ ⦃i : I⦄, G.Dir i → D.obj ⟨i⟩
  /-- Naturality. -/
  naturality : ∀ ⦃i i' : I⦄ (f : i' ⟶ i) (x : G.Dir i),
    app (G.restr f x) = D.map f.op (app x)

/-- The arity a `δ` adjoins at the decoding `s`: the fibres of `s`, as a
presheaf on the base `ElObj D`. The fibre over `y` is the elements of `P` at
`y.1` that `s` sends to `y.2`, and it is `s`'s naturality that makes those
fibres close under restriction — which is why the decoding must be a presheaf
morphism and not a bare family.

The carrier is indexed by `ElObj D` with `proj` the projection, rather than
being the total space of `P` with `proj` computed from `s`, so that a direction
destructures to its fibre without transporting the element. -/
@[reducible] def fibreArity {G : DomArity.{uI, uD, vI} I} {D : Iᵒᵖ ⥤ Type uD} (s : PshMor G D) :
    DomArity.{max uI uD, max uI uD, vI} (ElObj.{uI, uD, vI} D) where
  carrier := Σ y : ElObj.{uI, uD, vI} D, {x : G.Dir y.1 // s.app x = y.2}
  proj := Sigma.fst
  restr := fun {_ y'} f d ↦
    match d with
    | ⟨⟨_, p⟩, rfl⟩ =>
        ⟨⟨y', ⟨G.restr f.1 p.1, by rw [s.naturality, p.2]; exact f.2⟩⟩, rfl⟩

/-- The underlying element of a restricted fibre direction, so that the two
laws below need not unfold `fibreArity`'s matcher. -/
theorem fibreArity_restr_val {G : DomArity.{uI, uD, vI} I} {D : Iᵒᵖ ⥤ Type uD}
    (s : PshMor G D) {y' z : ElObj.{uI, uD, vI} D}
    (p : {q : G.Dir z.1 // s.app q = z.2}) (f : y' ⟶ z) :
    (((fibreArity s).restr f ⟨⟨z, p⟩, rfl⟩).1).2.1 = G.restr f.1 p.1 := rfl

/-- The fibre arity is a presheaf: both laws are `P`'s own, the fibre condition
being carried along by `s`'s naturality. -/
theorem isFunctorial_fibreArity {G : DomArity.{uI, uD, vI} I} (hG : G.IsFunctorial)
    {D : Iᵒᵖ ⥤ Type uD} (s : PshMor G D) : (fibreArity s).IsFunctorial where
  restr_id := by
    intro y
    funext d
    obtain ⟨⟨z, p⟩, rfl⟩ := d
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    exact (fibreArity_restr_val s p (𝟙 z)).trans (by
      simpa using congrFun (hG.restr_id z.1) p.1)
  restr_comp := by
    intro y y' y'' f g
    funext d
    obtain ⟨⟨z, p⟩, rfl⟩ := d
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    refine Eq.trans (fibreArity_restr_val s p (g ≫ f)) ?_
    refine Eq.trans ?_ (fibreArity_restr_val s
      (⟨G.restr f.1 p.1, by rw [s.naturality, p.2]; exact f.2⟩ :
        {q : G.Dir y'.1 // s.app q = y'.2}) g).symm
    exact congrFun (hG.restr_comp f.1 g.1) p.1

/-- The recursive `δ`: adjoin the arity `P` and let the continuation depend on
the decoding. This is a semantic operation; it is the rule of Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013], whose subcode family is indexed
by the sections `(p : P) → D (i p)`, generalized to presheaves — the sections
become `PshMor P D`.

It needs no new construction: regrouping `IR.delta`'s coproduct over
assignments by the decoding they induce presents it as a coproduct, over the
decodings, of the non-recursive `δ` at the corresponding fibre arity. Both
`coprod` and `adjoinArity` already carry all seven functor laws, so this does
too. -/
def deltaRec {J : Type uJ} [Category.{vJ} J] {G : DomArity.{uI, uD, vI} I}
    (hG : G.IsFunctorial) {D : Iᵒᵖ ⥤ Type uD}
    (K : PshMor G D →
      PresheafPFunctor.{max uI uD, uJ, max uI uD vI uA, max uI uD, vI, vJ}
        (ElObj.{uI, uD, vI} D) J) :
    PresheafPFunctor.{max uI uD, uJ, max uI uD vI uA, max uI uD, vI, vJ}
      (ElObj.{uI, uD, vI} D) J :=
  coprod (PshMor G D) fun s ↦
    adjoinArity (K s) (ShapeArity.const (K s).toPresheafPFunctorData (fibreArity s))
      (ShapeArity.isFunctorial_const (K s) (fibreArity s) (isFunctorial_fibreArity hG s))

/-- The recursive `δ` inherits bijective reindexing from its continuations: the
arity it adjoins at a decoding is that decoding's fibre arity, which is
constant over the output object, so `ShapeArity.const`'s reindexing is the
identity. The recursion therefore does not by itself reach past the bound of
`hasBijectiveReindex_adjoinArityConst`; `delta` is what does, per
`not_hasBijectiveReindex_deltaVaries`. -/
theorem hasBijectiveReindex_deltaRec {J : Type uJ} [Category.{vJ} J]
    {G : DomArity.{uI, uD, vI} I} (hG : G.IsFunctorial) {D : Iᵒᵖ ⥤ Type uD}
    (K : PshMor G D →
      PresheafPFunctor.{max uI uD, uJ, max uI uD vI uA, max uI uD, vI, vJ}
        (ElObj.{uI, uD, vI} D) J)
    (hK : ∀ s, HasBijectiveReindex (K s)) :
    HasBijectiveReindex (deltaRec.{uI, uJ, uA, uD, vI, vJ} hG K) := by
  refine hasBijectiveReindex_coprod _ _ fun s ↦ ?_
  refine hasBijectiveReindex_adjoinArity _ _ _ (hK s) ?_
  intro j j' g a i
  exact Function.bijective_id

/-- At the terminal decoding the recursive `δ` degenerates: `PshMor P ⊤` is a
singleton, so the coproduct has one summand and the continuation cannot depend
on anything. That is the case the base-category layer builds. -/
theorem subsingleton_pshMor_to_terminal (G : DomArity.{uI, uD, vI} I)
    (D : Iᵒᵖ ⥤ Type uD) (hD : ∀ i : I, Subsingleton (D.obj ⟨i⟩)) :
    Subsingleton (PshMor G D) :=
  ⟨fun s t ↦ by
    obtain ⟨sa, -⟩ := s
    obtain ⟨ta, -⟩ := t
    exact congrArg (fun a ↦ PshMor.mk a (by
      intro i i' f p
      exact (hD i').elim _ _))
      (funext fun i ↦ funext fun p ↦ (hD i).elim _ _)⟩

/-- The decoding presheaf of an output-varying arity: over the output object
`b`, the decodings of the arity there. Restriction along `g : b' ⟶ b` is
precomposition with `A.reindex g`, which is what makes the decodings vary
contravariantly and so form a presheaf on `J`.

This is the object that keeps `δ` free of mutuality: a continuation depending
functorially on the decoding is a single code over `ElObj` of this presheaf,
not a family of codes indexed by decodings. -/
def decPresheaf {J : Type uJ} [Category.{vJ} J] (A : BaseArity.{uI, uJ, uD, vI, vJ} I J)
    (hA : A.IsFunctorial) (D : Iᵒᵖ ⥤ Type uD) : Jᵒᵖ ⥤ Type (max uI uD vI) where
  obj b := PshMor (A.fam b.unop) D
  map g := ↾ fun s ↦
    { app := fun {i} x ↦ s.app (A.reindex g.unop x)
      naturality := fun {i i'} f x ↦
        (congrArg (fun y ↦ s.app (i := i') y)
          (congrFun (hA.reindex_naturality g.unop f) x).symm).trans
          (s.naturality f (A.reindex g.unop x)) }
  map_id b := by
    ext s i x
    exact congrArg (fun y ↦ s.app (i := i) y) (congrFun (hA.reindex_id b.unop i) x)
  map_comp g h := by
    ext s i x
    exact congrArg (fun y ↦ s.app (i := i) y) (congrFun (hA.reindex_comp g.unop h.unop i) x)

/-- The arity `δ` adjoins, indexed by the objects of `ElObj (decPresheaf …)`.
Each such object carries its own decoding, so the arity over it is that
decoding's fibre arity — and the arity therefore varies over the output, which
`not_hasBijectiveReindex_arityVaries` shows is necessary.

Reindexing along a morphism of elements applies `A.reindex` to the fibre
element; the morphism's own condition says the two decodings agree after that,
so no transport is needed. -/
def decArity {J : Type uJ} [Category.{vJ} J] (A : BaseArity.{uI, uJ, uD, vI, vJ} I J)
    (hA : A.IsFunctorial) (D : Iᵒᵖ ⥤ Type uD) :
    BaseArity.{max uI uD, max uI uJ uD vI, max uI uD, vI, vJ}
      (ElObj.{uI, uD, vI} D) (ElObj.{uJ, max uI uD vI, vJ} (decPresheaf A hA D)) where
  fam y := fibreArity y.2
  reindex := fun {y y'} f z d ↦
    match d with
    | ⟨⟨_, ⟨x, hx⟩⟩, rfl⟩ =>
        ⟨⟨z, ⟨A.reindex f.1 x, by rw [show y.2.app (A.reindex f.1 x) = y'.2.app x from
          congrArg (fun t : PshMor (A.fam y'.1) D ↦ t.app x) f.2, hx]⟩⟩, rfl⟩

/-- The underlying fibre element of a reindexed `decArity` direction, so the
laws below need not unfold the matcher. -/
theorem decArity_reindex_val {J : Type uJ} [Category.{vJ} J]
    (A : BaseArity.{uI, uJ, uD, vI, vJ} I J) (hA : A.IsFunctorial) (D : Iᵒᵖ ⥤ Type uD)
    {y y' : ElObj.{uJ, max uI uD vI, vJ} (decPresheaf A hA D)} (f : y' ⟶ y)
    {z : ElObj.{uI, uD, vI} D} (x : (A.fam y'.1).Dir z.1) (hx : y'.2.app x = z.2) :
    (((decArity A hA D).reindex f ⟨⟨z, ⟨x, hx⟩⟩, rfl⟩).1).2.1 = A.reindex f.1 x := rfl

/-- The adjoined arity is functorial: the fibre laws are `A`'s own, and the
reindexing laws are `A.reindex`'s. -/
theorem isFunctorial_decArity {J : Type uJ} [Category.{vJ} J]
    (A : BaseArity.{uI, uJ, uD, vI, vJ} I J) (hA : A.IsFunctorial) (D : Iᵒᵖ ⥤ Type uD) :
    (decArity A hA D).IsFunctorial where
  restr_id := fun y ↦ (isFunctorial_fibreArity ⟨hA.restr_id y.1, hA.restr_comp y.1⟩ y.2).restr_id
  restr_comp := by
    intro y i i' i'' f g
    exact (isFunctorial_fibreArity ⟨hA.restr_id y.1, hA.restr_comp y.1⟩ y.2).restr_comp f g
  reindex_id := by
    intro y z
    funext d
    obtain ⟨⟨w, ⟨x, hx⟩⟩, rfl⟩ := d
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    exact (decArity_reindex_val A hA D (𝟙 y) x hx).trans (congrFun (hA.reindex_id y.1 w.1) x)
  reindex_comp := by
    intro y y' y'' g h z
    funext d
    obtain ⟨⟨w, ⟨x, hx⟩⟩, rfl⟩ := d
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    refine Eq.trans (decArity_reindex_val A hA D (h ≫ g) x hx) ?_
    exact congrFun (hA.reindex_comp g.1 h.1 w.1) x
  reindex_naturality := by
    intro y y' g z z' f
    funext d
    obtain ⟨⟨w, ⟨x, hx⟩⟩, rfl⟩ := d
    refine Subtype.ext (Sigma.ext rfl (heq_of_eq (Subtype.ext ?_)))
    exact congrFun (hA.reindex_naturality g.1 f.1) x

/-- The `δ` rule: an arity that varies over the output object, whose
continuation depends on the decoding. It is the presheaf reading of the `δ`
rule of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013] with both
features present at once.

It decomposes as `sigmaPsh (decPresheaf A hA D) ∘ adjoinArity`: the inner
factor adjoins the directions and the outer one takes the coproduct over the
decodings, `decPresheaf` at `b` being the decodings at `b`. That coproduct is
the shape half of Dybjer–Setzer's `δ` under the regrouping
`Σ_{g : P → X} ⟦F (f ∘ g)⟧ = Σ_{d : P → D} (sections of f over d) × ⟦F d⟧`,
which `deltaRec` uses as well.

No `A` field grows in the process, and that is not an accident. A shape
presheaf here is a total space `A` fibred by `q`, so a coproduct over the
fibres of a discrete fibration is a *re-fibring* of the same total space, not
an enlargement of it: `sigmaPsh` changes only `q`, and `Σ_{s ∈ S j} F.Shape
⟨j, s⟩` and `F.A` over `ElObj S` are the same total space, which is
`elSliceEquiv` again. `coprod` does enlarge `A`, its index being a bare type
rather than the fibres of a fibration.

It needs no operation beyond those already proved. Over the base
`ElObj (decPresheaf A hA D)` every object carries its own decoding, so
`decArity` is an ordinary `BaseArity` there and `BaseArity.pullback` turns it
into the shape-indexed arity `adjoinArity` consumes; `sigmaPsh` then pushes the
result forward to `J`. In particular the continuation `F` is a single code's
interpretation over that base, not a family of them indexed by decodings, so
nothing is defined simultaneously with anything else. -/
def delta {J : Type uJ} [Category.{vJ} J] (A : BaseArity.{uI, uJ, uD, vI, vJ} I J)
    (hA : A.IsFunctorial) (D : Iᵒᵖ ⥤ Type uD)
    (F : PresheafPFunctor.{max uI uD, max uI uJ uD vI, uA, max uI uD, vI, vJ}
      (ElObj.{uI, uD, vI} D) (ElObj.{uJ, max uI uD vI, vJ} (decPresheaf A hA D))) :
    PresheafPFunctor.{max uI uD, uJ, uA, max uI uD, vI, vJ} (ElObj.{uI, uD, vI} D) J :=
  sigmaPsh (decPresheaf A hA D)
    (adjoinArity F ((decArity A hA D).pullback F.toPresheafPFunctorData)
      ((decArity A hA D).isFunctorial_pullback (isFunctorial_decArity A hA D) F))

end Decoding

section FusedWitness

/-!
That the fused `δ` keeps the output-varying arity, checked rather than argued:
at the terminal decoding, where the recursion degenerates, `delta` at an
output-varying arity still lies outside the bound of
`hasBijectiveReindex_adjoinArityConst`.
-/

open CategoryTheory

/-- The terminal presheaf on `Fin 1`, as a decoding: every fibre a singleton,
so the decodings of any arity form a singleton and the recursion degenerates. -/
def termPsh : (Fin 1)ᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := ↾ fun _ ↦ PUnit.unit

/-- `arityVaries`'s arity as an output-varying `BaseArity`: empty over `0`,
inhabited over `1`, reindexed along `0 ⟶ 1` by the map out of the empty type. -/
def arityVariesBase : BaseArity.{0, 0, 0, 0, 0} (Fin 1) (Fin 2) where
  fam b :=
    { carrier := arityB b
      proj := fun _ ↦ 0
      restr := fun {_ _} _f d ↦ ⟨d.1, Subsingleton.elim _ _⟩ }
  reindex := fun {_ _} g {_} d ↦
    ⟨⟨Fin.castLE (leOfHom g) d.1.down⟩, Subsingleton.elim _ _⟩

/-- Each fibre of `arityVariesBase` has at most one element. -/
theorem arityVariesBase_dir_ext (b : Fin 2) (i : Fin 1)
    (x y : (arityVariesBase.fam b).Dir i) : x = y :=
  Subtype.ext (Subsingleton.elim (α := arityB b) x.1 y.1)

/-- The arity is functorial; its content is the variation of the fibres, not
the laws. -/
theorem isFunctorial_arityVariesBase : arityVariesBase.IsFunctorial where
  restr_id := by intro b i; funext d; exact arityVariesBase_dir_ext _ _ _ _
  restr_comp := by intro b i i' i'' f g; funext d; exact arityVariesBase_dir_ext _ _ _ _
  reindex_id := by intro b i; funext d; exact arityVariesBase_dir_ext _ _ _ _
  reindex_comp := by intro b b' b'' g h i; funext d; exact arityVariesBase_dir_ext _ _ _ _
  reindex_naturality := by
    intro b b' g i i' f
    funext d
    exact arityVariesBase_dir_ext _ _ _ _

/-- The unique decoding into the terminal presheaf. -/
def decUnit (b : Fin 2) : PshMor (arityVariesBase.fam b) termPsh where
  app := fun {_} _ ↦ PUnit.unit
  naturality := by intros; rfl

/-- The element of the decoding presheaf that the `ι` continuation is taken at:
the arity is inhabited over `1`, which is where reindexing fails. -/
def decVariesElt :
    ElObj.{0, 0, 0} (decPresheaf arityVariesBase isFunctorial_arityVariesBase termPsh) :=
  ⟨1, decUnit 1⟩

/-- The `δ` at an output-varying arity, its continuation the representable at
`decVariesElt`. -/
def deltaVaries : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (ElObj.{0, 0, 0} termPsh) (Fin 2) :=
  delta arityVariesBase isFunctorial_arityVariesBase termPsh
    (iotaPresheaf (I := ElObj.{0, 0, 0} termPsh) decVariesElt)

/-- `δ` at an output-varying arity has non-bijective reindexing, so it lies
outside the bound of `hasBijectiveReindex_adjoinArityConst`. Carrying the
decoding-indexed continuation on the rule does not cost the output-varying
arity: both features are present at once. -/
theorem not_hasBijectiveReindex_deltaVaries :
    ¬ HasBijectiveReindex deltaVaries := by
  intro h
  have hb := (h (homOfLE (show (0 : Fin 2) ≤ 1 by omega))
    (⟨⟨decVariesElt, 𝟙 _⟩, rfl⟩ : deltaVaries.Shape (1 : Fin 2))
    (⟨(0 : Fin 1), PUnit.unit⟩ : ElObj.{0, 0, 0} termPsh)).2
  obtain ⟨d, -⟩ := hb
    ⟨Sum.inl ⟨⟨(0 : Fin 1), PUnit.unit⟩,
      ⟨⟨⟨(0 : Fin 1)⟩, Subsingleton.elim _ _⟩, rfl⟩⟩, rfl⟩
  obtain ⟨b, -⟩ := d
  cases b with
  | inl c => exact (c.2.1.1.down).elim0
  | inr e => exact e.elim

end FusedWitness

section CodeType

variable (I : Type u) [Category.{u} I] (D : Iᵒᵖ ⥤ Type u)

/-- The shape of a code node over the base category `𝔹`: a presheaf p.r.a.
functor over `𝔹` taken as it stands (`pra`), or an output-varying arity `A`
adjoined with the continuation over the category of elements of its decoding
presheaf (`δ`).

`pra` stands where small induction recursion has `ι` and `σ`. There the target
— slice polynomial functors — is reached by generators, and the correspondence
with the codes is a theorem. Here the target is already a type, so the codes
take it as their leaf; the interpretation is then surjective on objects by
construction and the content sits in `δ` being an operation on presheaf p.r.a.
functors at all, which is the content of `delta`'s type. What a code records is
a derivation, and the same two rules over a restricted leaf make closure under
`δ` a question again.

`δ` carries the recursion: a continuation depending functorially on the
decoding is one code over `ElObj (decPresheaf …)`, not a family of codes
indexed by decodings. The index is therefore a parameter, and nothing is
defined simultaneously with anything else.

The input side is the fixed pair `(I, D)`; the interpretation's input base is
`ElObj D`. Universes are pinned so that `Cat.{v, u}` is closed under the
continuation step. -/
def CodeShape (𝔹 : Cat.{v, u}) : Type (max (u + 1) (v + 1)) :=
  PresheafPFunctor.{u, u, max u v, u, u, v} (ElObj.{u, u, u} D) 𝔹 ⊕
    {A : BaseArity.{u, u, u, u, v} I 𝔹 // A.IsFunctorial}

/-- The subcode slots of a code shape: none for `pra`, one for `δ`. -/
def CodeDir (𝔹 : Cat.{v, u}) : CodeShape I D 𝔹 → Type
  | Sum.inl _ => PEmpty.{1}
  | Sum.inr _ => PUnit.{1}

/-- The base category the subcode of a code shape lives over: the category of
elements of the decoding presheaf of the adjoined arity. `Cat` is closed under
that step, which is what lets the codes be an ordinary W-type. -/
def CodeNext (𝔹 : Cat.{v, u}) : (sh : CodeShape I D 𝔹) → CodeDir I D 𝔹 sh → Cat.{v, u}
  | Sum.inl _, b => PEmpty.elim b
  | Sum.inr ⟨A, hA⟩, _ => Cat.of (ElObj.{u, u, v} (decPresheaf A hA D))

/-- The slice polynomial functor on `Cat` whose W-type is the type of codes. -/
def codePFunctor :
    SlicePFunctor.{max (u + 1) (v + 1), 0,
      max (u + 1) (v + 1), max (u + 1) (v + 1)} Cat.{v, u} Cat.{v, u} where
  toPFunctor := ⟨Σ 𝔹 : Cat.{v, u}, CodeShape I D 𝔹, fun x ↦ CodeDir I D x.1 x.2⟩
  r := fun x ↦ CodeNext I D x.1.1 x.1.2 x.2
  q := fun x ↦ x.1

/-- The type of codes: the W-type of `codePFunctor`, fibred over `Cat` by the
base category its root sits over. -/
def Code : Type (max (u + 1) (v + 1)) :=
  (codePFunctor.{u, v} I D).W

/-- The target of the interpretation: a presheaf p.r.a. functor on the input
base `ElObj D`, together with the base category it lands in. -/
def Interp : Type (max (u + 1) (v + 1)) :=
  Σ 𝔹 : Cat.{v, u}, PresheafPFunctor.{u, u, max u v, u, u, v} (ElObj.{u, u, u} D) 𝔹

/-- The interpretation of one code node, given its subcode's interpretation
already at the base its slot prescribes: `pra` is the injected functor itself,
`δ` is the rule at its arity. -/
def codeAlgOn (𝔹 : Cat.{v, u}) :
    (sh : CodeShape I D 𝔹) →
      ((b : CodeDir I D 𝔹 sh) →
        PresheafPFunctor.{u, u, max u v, u, u, v} (ElObj.{u, u, u} D) (CodeNext I D 𝔹 sh b)) →
      PresheafPFunctor.{u, u, max u v, u, u, v} (ElObj.{u, u, u} D) 𝔹
  | Sum.inl F, _ => F
  | Sum.inr ⟨A, hA⟩, c => delta A hA D (c PUnit.unit)

/-- The slice algebra the interpretation folds with. -/
def codeAlg :
    (codePFunctor.{u, v} I D).toSliceDomPFunctor.Obj
        (Sigma.fst : Interp.{u, v} I D → Cat.{v, u}) →
      Interp.{u, v} I D :=
  fun x ↦ ⟨x.1.1.1, codeAlgOn I D x.1.1.1 x.1.1.2 fun b ↦
    cast (congrArg (fun 𝔻 : Cat.{v, u} ↦
        PresheafPFunctor.{u, u, max u v, u, u, v} (ElObj.{u, u, u} D) 𝔻)
      (((codePFunctor.{u, v} I D).toSliceDomPFunctor.compatible_iff _ _ _).mp x.2 b))
      (x.1.2 b).2⟩

/-- The interpretation of a code, as the fold of `codeAlg`. -/
def interp : Code.{u, v} I D → Interp.{u, v} I D :=
  SlicePFunctor.W.elim (codePFunctor.{u, v} I D) (Interp.{u, v} I D) Sigma.fst
    (codeAlg.{u, v} I D) rfl

/-- The `pra` code over `𝔹` at a presheaf p.r.a. functor: the leaf that injects
the semantics. -/
def praCode (𝔹 : Cat.{v, u})
    (F : PresheafPFunctor.{u, u, max u v, u, u, v} (ElObj.{u, u, u} D) 𝔹) :
    Code.{u, v} I D :=
  SlicePFunctor.W.mk
    ⟨⟨⟨𝔹, Sum.inl F⟩, fun b ↦ PEmpty.elim b⟩, funext fun b ↦ PEmpty.elim b⟩

/-- The `δ` code over `𝔹`: adjoin the output-varying arity `A`, the subcode
being one over the category of elements of `A`'s decoding presheaf. -/
def deltaCode (𝔹 : Cat.{v, u}) (A : BaseArity.{u, u, u, u, v} I 𝔹) (hA : A.IsFunctorial)
    (K : Code.{u, v} I D)
    (hK : (codePFunctor.{u, v} I D).wIndex K =
      Cat.of (ElObj.{u, u, v} (decPresheaf A hA D))) :
    Code.{u, v} I D :=
  SlicePFunctor.W.mk
    ⟨⟨⟨𝔹, Sum.inr ⟨A, hA⟩⟩, fun _ ↦ K⟩, funext fun _ ↦ hK⟩

/-- The interpretation of a `pra` code is the injected functor, so `praCode`
is a section of `interp` and the interpretation is surjective on objects. -/
theorem interp_praCode (𝔹 : Cat.{v, u})
    (F : PresheafPFunctor.{u, u, max u v, u, u, v} (ElObj.{u, u, u} D) 𝔹) :
    interp.{u, v} I D (praCode I D 𝔹 F) = ⟨𝔹, F⟩ := rfl

/-- Every code has the interpretation of a one-node code. So `δ` adds no
functor that `pra` does not already supply, and what a code carries beyond its
interpretation is the derivation. Equivalently, `praCode ∘ interp` is
idempotent over `interp`. It does not say that the two codes differ, and for a
`pra` code they do not. -/
theorem interp_praCode_interp (K : Code.{u, v} I D) :
    interp.{u, v} I D (praCode I D (interp I D K).1 (interp I D K).2) =
      interp.{u, v} I D K := rfl

/-- The index of a code is the base its interpretation lands in. -/
theorem interp_fst (K : Code.{u, v} I D) :
    (interp I D K).1 = (codePFunctor.{u, v} I D).wIndex K :=
  congrFun (SlicePFunctor.W.comp_elim (codePFunctor.{u, v} I D) (Interp.{u, v} I D)
    Sigma.fst (codeAlg I D) rfl) K

/-- The interpretation of a `δ` code is the rule at its arity. -/
theorem interp_deltaCode (𝔹 : Cat.{v, u}) (A : BaseArity.{u, u, u, u, v} I 𝔹)
    (hA : A.IsFunctorial) (K : Code.{u, v} I D)
    (hK : (codePFunctor.{u, v} I D).wIndex K =
      Cat.of (ElObj.{u, u, v} (decPresheaf A hA D))) :
    interp I D (deltaCode I D 𝔹 A hA K hK) =
      ⟨𝔹, delta A hA D (cast (congrArg (fun 𝔻 : Cat.{v, u} ↦
        PresheafPFunctor.{u, u, max u v, u, u, v} (ElObj.{u, u, u} D) 𝔻)
        ((interp_fst I D K).trans hK)) (interp I D K).2)⟩ := rfl

/-- A `δ` *code* whose interpretation lies outside the bound of
`hasBijectiveReindex_adjoinArityConst`, restating
`not_hasBijectiveReindex_deltaVaries` about a code rather than about the
semantic operations. It says nothing about what the constant-arity fragment
admits: that fragment's own code type is not built here, and this code type's
leaf admits every presheaf p.r.a. functor. -/
def deltaCodeVaries : Code.{0, 0} (Fin 1) termPsh :=
  deltaCode (Fin 1) termPsh (Cat.of (Fin 2)) arityVariesBase isFunctorial_arityVariesBase
    (praCode (Fin 1) termPsh
      (Cat.of (ElObj.{0, 0, 0} (decPresheaf arityVariesBase isFunctorial_arityVariesBase
        termPsh)))
      (iotaPresheaf (I := ElObj.{0, 0, 0} termPsh) decVariesElt)) rfl

/-- Its interpretation is the `δ` at the output-varying arity. -/
theorem interp_deltaCodeVaries :
    interp (Fin 1) termPsh deltaCodeVaries = ⟨Cat.of (Fin 2), deltaVaries⟩ := rfl

/-- So a code's interpretation lies outside the bound. -/
theorem not_hasBijectiveReindex_interp_deltaCodeVaries :
    ¬ HasBijectiveReindex (interp (Fin 1) termPsh deltaCodeVaries).2 :=
  not_hasBijectiveReindex_deltaVaries

end CodeType

end GebProto
