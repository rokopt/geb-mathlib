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
* `GebProto.deltaConstData` / `GebProto.deltaConst` — the `δ` case at a constant
  arity: adjoin a `DomArity` to every arity of a functor.
* `GebProto.HasBijectiveReindex` — the property that every reindexing map is a
  bijection.

## Main statements

* `GebProto.hasBijectiveReindex_iotaPresheaf`,
  `GebProto.hasBijectiveReindex_iotaConst`,
  `GebProto.hasBijectiveReindex_coprod`,
  `GebProto.hasBijectiveReindex_deltaConst` — the presheaf reading of the
  `ι` / `σ` / `δ` rules generates only functors with bijective reindexing.
* `GebProto.not_hasBijectiveReindex_arityVaries` — `arityVaries` is not such a
  functor, so those rules do not generate it.

## Implementation notes

`deltaConst` adjoins an arity that does not vary over the output object.
A `δ` whose arity does vary is what
`GebProto.not_hasBijectiveReindex_arityVaries` shows to be necessary; its
operations require an `eqToHom` transport between `P.carrier (F.q a)` and
`P.carrier j`, which `deltaConst` avoids.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

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

section DeltaConst

variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]

set_option linter.checkUnivs false in
/-- Operations of the `δ` case at a *constant* arity: adjoin the presheaf `G`
on `I` to every arity of `F`, leaving the shapes untouched. This is the
presheaf reading of the `δ` rule of Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013], whose arity is a set `P` labelled
by `i : P → I` — an object of `Set/I`, which is a presheaf on a discrete `I`.

The adjoined directions do not depend on the output object, so `reindex` is the
identity on them; that is the whole content of `deltaConst_reindex_inl`, and
through it of `hasBijectiveReindex_deltaConst`. -/
def deltaConstData (G : DomArity.{uI, uB, vI} I)
    (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J) :
    PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J where
  A := F.A
  B := fun a ↦ G.carrier ⊕ F.B a
  r := fun x ↦ Sum.elim G.proj (fun b ↦ F.r ⟨x.1, b⟩) x.2
  q := F.q
  directionRestr := fun a _ _ g d ↦
    match d with
    | ⟨Sum.inl c, h⟩ => ⟨Sum.inl (G.restr g ⟨c, h⟩).1, (G.restr g ⟨c, h⟩).2⟩
    | ⟨Sum.inr b, h⟩ => ⟨Sum.inr (F.directionRestr a g ⟨b, h⟩).1, (F.directionRestr a g ⟨b, h⟩).2⟩
  shapeRestr := fun {_ _} g s ↦ F.shapeRestr g s
  reindex := fun {_ _} g s _ d ↦
    match d with
    | ⟨Sum.inl c, h⟩ => ⟨Sum.inl c, h⟩
    | ⟨Sum.inr b, h⟩ => ⟨Sum.inr (F.reindex g s ⟨b, h⟩).1, (F.reindex g s ⟨b, h⟩).2⟩

variable (G : DomArity.{uI, uB, vI} I) (F : PresheafPFunctorData.{uI, uJ, uA, uB, vI, vJ} I J)

/-- Transport of an adjoined direction along an equality of shapes leaves it
alone: the adjoined arity does not depend on the shape. -/
theorem deltaConst_cast_inl {j : J} {i : I} {t t' : F.Shape j} (e : t = t')
    (c : G.carrier) (h : G.proj c = i) :
    cast (congrArg (fun u : F.Shape j ↦ (deltaConstData G F).Direction u.1 i) e)
        (⟨Sum.inl c, h⟩ : (deltaConstData G F).Direction t.1 i) = ⟨Sum.inl c, h⟩ := by
  cases e
  rfl

/-- Transport of an original direction along an equality of shapes is the
transport of that direction inside `F`. -/
theorem deltaConst_cast_inr {j : J} {i : I} {t t' : F.Shape j} (e : t = t')
    (d : F.Direction t.1 i) :
    cast (congrArg (fun u : F.Shape j ↦ (deltaConstData G F).Direction u.1 i) e)
        (⟨Sum.inr d.1, d.2⟩ : (deltaConstData G F).Direction t.1 i) =
      ⟨Sum.inr (cast (congrArg (fun u : F.Shape j ↦ F.Direction u.1 i) e) d).1,
        (cast (congrArg (fun u : F.Shape j ↦ F.Direction u.1 i) e) d).2⟩ := by
  cases e
  rfl

set_option linter.checkUnivs false in
/-- Adjoining a constant arity to a presheaf p.r.a. functor yields one: the
shape-side laws are `F`'s unchanged, and each direction-side law splits over
the two summands into `G`'s law and `F`'s. -/
def deltaConst (G : DomArity.{uI, uB, vI} I) (hG : G.IsFunctorial)
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J where
  toPresheafPFunctorData := deltaConstData G F.toPresheafPFunctorData
  isFunctorial :=
    { directionRestr_id := by
        intro a i
        funext d
        obtain ⟨b, h⟩ := d
        cases b with
        | inl c =>
            exact Subtype.ext (congrArg (fun x : G.Dir i ↦ Sum.inl x.1)
              (congrFun (hG.restr_id i) ⟨c, h⟩))
        | inr b =>
            exact Subtype.ext (congrArg (fun x : F.Direction a i ↦ Sum.inr x.1)
              (congrFun (F.isFunctorial.directionRestr_id a i) ⟨b, h⟩))
      directionRestr_comp := by
        intro a i i' i'' f g
        funext d
        obtain ⟨b, h⟩ := d
        cases b with
        | inl c =>
            exact Subtype.ext (congrArg (fun x : G.Dir i'' ↦ Sum.inl x.1)
              (congrFun (hG.restr_comp f g) ⟨c, h⟩))
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
        | inl c => rfl
        | inr b =>
            exact Subtype.ext (congrArg (fun x : F.Direction a.1 i' ↦ Sum.inr x.1)
              (congrFun (F.isFunctorial.reindex_naturality g a f) ⟨b, h⟩))
      reindex_id := by
        intro j a i d
        obtain ⟨b, h⟩ := d
        cases b with
        | inl c =>
            exact (deltaConst_cast_inl G F.toPresheafPFunctorData
              (congrFun (F.isFunctorial.shapeRestr_id j) a) c h).symm
        | inr b =>
            refine Eq.trans ?_ (deltaConst_cast_inr G F.toPresheafPFunctorData
              (congrFun (F.isFunctorial.shapeRestr_id j) a) ⟨b, h⟩).symm
            exact Subtype.ext (congrArg (fun x : F.Direction a.1 i ↦ Sum.inr x.1)
              (F.isFunctorial.reindex_id a ⟨b, h⟩))
      reindex_comp := by
        intro j j' j'' g h a i d
        obtain ⟨b, hb⟩ := d
        cases b with
        | inl c =>
            exact Eq.trans rfl (congrArg (fun z ↦
              (deltaConstData G F.toPresheafPFunctorData).reindex g a
                ((deltaConstData G F.toPresheafPFunctorData).reindex h
                  ((deltaConstData G F.toPresheafPFunctorData).shapeRestr g a) z))
              (deltaConst_cast_inl G F.toPresheafPFunctorData
                (congrFun (F.isFunctorial.shapeRestr_comp g h) a) c hb)).symm
        | inr b =>
            refine Eq.trans ?_ (congrArg (fun z ↦
              (deltaConstData G F.toPresheafPFunctorData).reindex g a
                ((deltaConstData G F.toPresheafPFunctorData).reindex h
                  ((deltaConstData G F.toPresheafPFunctorData).shapeRestr g a) z))
              (deltaConst_cast_inr G F.toPresheafPFunctorData
                (congrFun (F.isFunctorial.shapeRestr_comp g h) a) ⟨b, hb⟩)).symm
            exact Subtype.ext (congrArg (fun x : F.Direction a.1 i ↦ Sum.inr x.1)
              (F.isFunctorial.reindex_comp g h a ⟨b, hb⟩)) }

end DeltaConst

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

/-- Bijective reindexing is inherited by `δ` at a constant arity: the adjoined
directions do not depend on the output object, so `reindex` acts on them as the
identity.

With `hasBijectiveReindex_coprod` and the two `iota` cases, this is the
syntactic form of the argument recorded in `PresheafIRProto.Basic`'s `Reindex`
section: everything the presheaf reading of the `ι` / `σ` / `δ` rules of
[HancockMcBrideGhaniMalatestaAltenkirch2013] generates has bijective
reindexing. -/
theorem hasBijectiveReindex_deltaConst (G : DomArity.{uI, uB, vI} I) (hG : G.IsFunctorial)
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (hF : HasBijectiveReindex F) :
    HasBijectiveReindex (deltaConst G hG F) := by
  intro j j' g a i
  refine ⟨?_, ?_⟩
  · rintro ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ hd
    cases b₁ with
    | inl c₁ =>
        cases b₂ with
        | inl c₂ =>
            have hv : (Sum.inl c₁ : G.carrier ⊕ F.B a.1) = Sum.inl c₂ :=
              congrArg Subtype.val hd
            exact Subtype.ext (congrArg (fun c : G.carrier ↦
              (Sum.inl c : G.carrier ⊕ F.B (F.shapeRestr g a).1)) (Sum.inl.inj hv))
        | inr b₂ =>
            have hv : (Sum.inl c₁ : G.carrier ⊕ F.B a.1) =
                Sum.inr (F.reindex g a ⟨b₂, h₂⟩).1 := congrArg Subtype.val hd
            simp at hv
    | inr b₁ =>
        cases b₂ with
        | inl c₂ =>
            have hv : (Sum.inr (F.reindex g a ⟨b₁, h₁⟩).1 : G.carrier ⊕ F.B a.1) =
                Sum.inl c₂ := congrArg Subtype.val hd
            simp at hv
        | inr b₂ =>
            have hv : (Sum.inr (F.reindex g a ⟨b₁, h₁⟩).1 : G.carrier ⊕ F.B a.1) =
                Sum.inr (F.reindex g a ⟨b₂, h₂⟩).1 := congrArg Subtype.val hd
            exact Subtype.ext (congrArg (fun x : F.Direction (F.shapeRestr g a).1 i ↦
              Sum.inr x.1) ((hF g a i).1 (a₁ := ⟨b₁, h₁⟩) (a₂ := ⟨b₂, h₂⟩)
                (Subtype.ext (Sum.inr.inj hv))))
  · rintro ⟨b, h⟩
    cases b with
    | inl c => exact ⟨⟨Sum.inl c, h⟩, rfl⟩
    | inr b =>
        obtain ⟨e, he⟩ := (hF g a i).2 ⟨b, h⟩
        exact ⟨⟨Sum.inr e.1, e.2⟩,
          Subtype.ext (congrArg (fun x : F.Direction a.1 i ↦ Sum.inr x.1) he)⟩

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

end GebProto
