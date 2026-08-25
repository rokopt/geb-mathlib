/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.UniverseVariance.Basic

/-!
# Prototype: the two universe examples over the split-epimorphism base

Throwaway exploration, not upstream-eligible content. Every declaration here is
`Classical.choice`-free.

Examples 3.5 and 3.6 of [GhaniNordvallForsbergMalatesta2015] over a decoding
category whose morphisms carry a chosen section. The paper's Example 3.5 gives
the dependent-sum universe over `Fam(Setᵒᵖ)` and its Example 3.6 shows the
dependent-product universe extends to neither `Fam(Set)` nor `Fam(Setᵒᵖ)`, only
to the groupoid `Fam(Set≅)`. Here both are given over `Fam` of the category
whose morphisms are embedding-projection pairs: the morphism map that Example
3.6 shows cannot exist over `Set` is `piUnivHom`.

`FamHom`'s components are an embedding-projection pair, the form the section
takes once the decoding maps are packaged: a map each way with `proj ∘ emb` the
identity. That is the classical device for solving recursive domain equations —
restricting to the subcategory of embeddings makes a mixed-variance functor
covariant, as in Theorem 5.8 of [LindenhoviusMisloveZamdzhiev2021] — transported
to the inductive-recursive setting.

The code map `univCodeMap` reindexes the binder's family along `proj`. That is
the `replace` of the discrete presentation, and it is why the two formers'
retraction proofs carry a transport: the family is read at
`proj u (emb u x)` where the source reads it at `x`.

## Main definitions

* `Fam` / `FamHom` — a family of types, and a map of codes together with a
  `Split` at each code: the projection is the split epimorphism and the
  embedding its chosen section.
* `FamHom.proj` / `FamHom.emb` / `FamHom.proj_emb` — the pair read off.
* `FamHom.id` / `FamHom.comp` — the identity and composition.
* `UnivCode` / `univDec` / `univObj` — the universe functor on objects,
  parameterized by a base type and a type former.
* `univCodeMap` — its action on codes, reindexing the binder's family along
  `proj`.
* `sigmaFormer` / `piFormer` — the two formers.
* `sigmaUnivHom` — Example 3.5's morphism map.
* `piUnivHom` — Example 3.6's morphism map, the one that does not exist over
  `Set`.

## Main statements

* `FamHom.id_comp` / `comp_id` / `comp_assoc` — `FamHom` composes as a category.
* `univCodeMap_id` / `univCodeMap_comp` — the action on codes is functorial. The
  functor laws for the decoding components are not formalized; the formers'
  laws in isolation are `Basic.piMap_id` and `Basic.piMap_comp`.
* `heq_proj_cast` / `cast_proj_emb` — the two transport lemmas the formers'
  retraction proofs need.

## References

* [GhaniNordvallForsbergMalatesta2015]
* [LindenhoviusMisloveZamdzhiev2021]

## Tags

prototype, inductive-recursive, universe, variance, split epimorphism,
embedding-projection pair
-/

@[expose] public section

namespace GebProto.UniverseVariance

/-! ## The ambient category -/

/-- An object of `Fam` over the split-epimorphism base: a type of codes together
with a decoding. -/
structure Fam : Type 1 where
  /-- The codes. -/
  Code : Type
  /-- The decoding. -/
  dec : Code → Type

/-- A morphism of families: a map of codes together with an
embedding-projection pair between each code's decoding and its image's. The
projection is what the dependent-product former runs the reindexing backwards
along. -/
structure FamHom (A B : Fam) : Type where
  /-- The map of codes. -/
  code : A.Code → B.Code
  /-- The embedding-projection pair at each code: the projection is the split
  epimorphism and the embedding its chosen section. -/
  ep : ∀ u, Split (B.dec (code u)) (A.dec u)

namespace FamHom

/-- The projection of a decoding onto its source. -/
def proj {A B : Fam} (m : FamHom A B) (u : A.Code) :
    B.dec (m.code u) → A.dec u :=
  (m.ep u).toFun

/-- The embedding of a decoding into its image's. -/
def emb {A B : Fam} (m : FamHom A B) (u : A.Code) :
    A.dec u → B.dec (m.code u) :=
  (m.ep u).sect

/-- The projection retracts the embedding. -/
theorem proj_emb {A B : Fam} (m : FamHom A B) (u : A.Code) (x : A.dec u) :
    m.proj u (m.emb u x) = x :=
  (m.ep u).toFun_sect x

/-- The identity morphism. -/
def id (A : Fam) : FamHom A A where
  code := _root_.id
  ep u := Split.id (A.dec u)

/-- Composition: the codes compose forwards and the embedding-projection pairs
compose as `Split`s, so the retraction is inherited. -/
def comp {A B C : Fam} (m : FamHom A B) (m' : FamHom B C) : FamHom A C where
  code := m'.code ∘ m.code
  ep u := (m'.ep (m.code u)).comp (m.ep u)

/-- Composition with the identity on the left. -/
theorem id_comp {A B : Fam} (m : FamHom A B) : (FamHom.id A).comp m = m := rfl

/-- Composition with the identity on the right. -/
theorem comp_id {A B : Fam} (m : FamHom A B) : m.comp (FamHom.id B) = m := rfl

/-- Composition is associative. -/
theorem comp_assoc {A B C D : Fam} (m : FamHom A B) (m' : FamHom B C)
    (m'' : FamHom C D) : (m.comp m').comp m'' = m.comp (m'.comp m'') := rfl

end FamHom

/-! ## The universe functor on objects -/

/-- The codes of the universe: one nullary code for the base type, and one
binder code per code and family of codes indexed by its decoding. -/
def UnivCode (A : Fam) : Type :=
  Unit ⊕ Σ u : A.Code, (A.dec u → A.Code)

/-- The decoding of the universe's codes, at a base type and a type former. -/
def univDec (base : Type) (former : (S : Type) → (S → Type) → Type) (A : Fam) :
    UnivCode A → Type
  | .inl _ => base
  | .inr ⟨u, v⟩ => former (A.dec u) (fun x ↦ A.dec (v x))

/-- The universe functor on objects. -/
def univObj (base : Type) (former : (S : Type) → (S → Type) → Type) (A : Fam) :
    Fam where
  Code := UnivCode A
  dec := univDec base former A

/-- The action on codes: the bound code goes forward and the binder's family is
reindexed along the projection. This is the `replace` of the discrete
presentation. -/
def univCodeMap {A B : Fam} (m : FamHom A B) : UnivCode A → UnivCode B
  | .inl _ => .inl ()
  | .inr ⟨u, v⟩ => .inr ⟨m.code u, fun y ↦ m.code (v (m.proj u y))⟩

/-- The action on codes preserves the identity. -/
theorem univCodeMap_id (A : Fam) :
    univCodeMap (FamHom.id A) = _root_.id := by
  funext c
  cases c <;> rfl

/-- The action on codes preserves composition: the two reindexings of the
binder's family along the projections compose. -/
theorem univCodeMap_comp {A B C : Fam} (m : FamHom A B) (m' : FamHom B C) :
    univCodeMap (m.comp m') = univCodeMap m' ∘ univCodeMap m := by
  funext c
  cases c <;> rfl

/-! ## The transport lemmas

Both formers' retraction proofs compare a value read at `x` with one read at
`proj u (emb u x)`. Abstracting the equality between those two indices makes
both provable by case analysis on it. -/

/-- The projection of an embedded value, transported across an equality of
indices, is the original value, heterogeneously. -/
theorem heq_proj_cast {A B : Fam} (m : FamHom A B) {u : A.Code}
    (v : A.dec u → A.Code) {a a' : A.dec u} (h : a' = a) (z : A.dec (v a)) :
    m.proj (v a')
      (cast (congrArg (fun w ↦ B.dec (m.code (v w))) h.symm) (m.emb (v a) z)) ≍ z := by
  cases h
  exact heq_of_eq (m.proj_emb (v a) z)

/-- The projection of an embedded value at a shifted index, transported back, is
the original value. -/
theorem cast_proj_emb {A B : Fam} (m : FamHom A B) {u : A.Code}
    (v : A.dec u → A.Code) {a a' : A.dec u} (h : a' = a)
    (s : (x : A.dec u) → A.dec (v x)) :
    cast (congrArg (fun w ↦ A.dec (v w)) h)
      (m.proj (v a') (m.emb (v a') (s a'))) = s a := by
  cases h
  exact m.proj_emb (v a) (s a)

/-! ## Example 3.5: the dependent-sum universe -/

/-- The dependent-sum former. -/
def sigmaFormer : (S : Type) → (S → Type) → Type :=
  fun S T ↦ Σ x : S, T x

/-- The morphism map of the dependent-sum universe. The embedding pairs the
embedded index with the embedded value, transported across the reindexing of the
family; the projection needs no transport. -/
def sigmaUnivHom {A B : Fam} (base : Type) (m : FamHom A B) :
    FamHom (univObj base sigmaFormer A) (univObj base sigmaFormer B) where
  code := univCodeMap m
  ep
    | .inl _ => Split.id base
    | .inr ⟨u, v⟩ =>
        { toFun := fun q ↦ ⟨m.proj u q.1, m.proj (v (m.proj u q.1)) q.2⟩
          sect := fun p ↦
            ⟨m.emb u p.1,
              cast (congrArg (fun w ↦ B.dec (m.code (v w))) (m.proj_emb u p.1).symm)
                (m.emb (v p.1) p.2)⟩
          toFun_sect := fun p ↦
            Sigma.ext (m.proj_emb u p.1) (heq_proj_cast m v (m.proj_emb u p.1) p.2) }

/-! ## Example 3.6: the dependent-product universe

The morphism map the paper shows does not exist over `Set`: its embedding
evaluates the given section family at the projection, and its projection runs
the reindexing backwards along the embedding. Neither is available without the
section. -/

/-- The dependent-product former. -/
def piFormer : (S : Type) → (S → Type) → Type :=
  fun S T ↦ (x : S) → T x

/-- The morphism map of the dependent-product universe. -/
def piUnivHom {A B : Fam} (base : Type) (m : FamHom A B) :
    FamHom (univObj base piFormer A) (univObj base piFormer B) where
  code := univCodeMap m
  ep
    | .inl _ => Split.id base
    | .inr ⟨u, v⟩ =>
        { toFun := fun t x ↦
            cast (congrArg (fun w ↦ A.dec (v w)) (m.proj_emb u x))
              (m.proj (v (m.proj u (m.emb u x))) (t (m.emb u x)))
          sect := fun s y ↦ m.emb (v (m.proj u y)) (s (m.proj u y))
          toFun_sect := fun s ↦
            funext fun x ↦ cast_proj_emb m v (m.proj_emb u x) s }

end GebProto.UniverseVariance
