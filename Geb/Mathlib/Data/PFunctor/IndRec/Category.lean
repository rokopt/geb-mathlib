/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Naturality

/-!
# The category of IR codes

Corollary 2 of [HancockMcBrideGhaniMalatestaAltenkirch2013]: `IR`
codes and the homsets of Definition 8 form a category. Composition
is transferred through the full-and-faithful interpretation of
Theorem 3 — the code morphism carried by the vertical composite of
the interpreted transformations — and the category laws follow from
the vertical laws together with the round-trip laws of the Theorem 3
equivalence. The identity laws additionally consume the
identity-image equation `IR.interpHom_id`, proved by induction on
the domain code over the stack of `IR.preUnitStack`, against the
semantic counterpart of that stack: an iterated coproduct tower with
its iterated Lemma 4 isomorphism.

## Main definitions

* `IR.mplus`, `IR.mplusInj`, `IR.mplusMorMap` — the iterated
  coproduct object of a stack of superscripts, its iterated
  injection, and its action on morphisms.
* `IR.mprecompIso` — the iterated Lemma 4 isomorphism between the
  interpretation of an iterated precomposition and the
  interpretation at `IR.mplus`.
* `IR.preUnitComponent` — the semantic pre-unit component: the
  interpretation image of `IR.mplusInj`, composed with the inverse
  of `IR.mprecompIso`.

## Main statements

* `IR.mplus_snoc`, `IR.mplusInj_snoc`, `IR.mprecompIso_snoc_hom`,
  `IR.mprecompIso_snoc_invHom` — the tower at a right-appended
  superscript, the direction in which the `δ`-case of the
  identity-image induction extends the stack.
* `IR.mprecompIso_natural` — naturality of the tower isomorphism in
  the interpreted object.
* `IR.preUnitComponent_nil` — the semantic pre-unit component at the
  empty stack is the identity.

## Implementation notes

The tower constructions recurse on the stack through `List.rec`, not
on codes; the snoc lemmas are the corresponding `List.rec`
inductions, with the motive quantified over the code where the
recursion changes it (`IR.mprecompIso` and its snoc lemmas). Object
equalities entering the tower (`IR.mplus_snoc`, `IR.mprecomp_snoc`)
are carried as `FreeCoprodCompDisc.isoOfEq` transports and commuted
across the Lemma 4 isomorphism by elimination of the generalized
equality.

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, morphism, category
-/

@[expose] public section

universe uA uB uI uO

namespace IndRec

open CategoryTheory

variable (I : Type uI) (O : Type uO)

namespace IR

/-- The iterated coproduct object: fold `plus` over the stack. -/
def mplus (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.{max uA uB, uI} I :=
  L.rec X (fun b _L ih => FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b ih)

/-- `mplus` at a right-appended superscript feeds the coproduct at the
inner position. -/
theorem mplus_snoc (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    mplus.{uA, uB, uI} I (L ++ [b]) X =
      mplus.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X) :=
  L.rec (motive := fun L => mplus.{uA, uB, uI} I (L ++ [b]) X =
      mplus.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
    rfl
    (fun a _L ih => congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) ih)

/-- The iterated right injection into `mplus`. -/
def mplusInj (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom I X (mplus.{uA, uB, uI} I L X) :=
  L.rec (motive := fun L => FreeCoprodCompDisc.Hom I X (mplus.{uA, uB, uI} I L X))
    (FreeCoprodCompDisc.Hom.id I X)
    (fun b _L ih => FreeCoprodCompDisc.Hom.comp I ih
      (FreeCoprodCompDisc.coprodPairInr I b (mplus.{uA, uB, uI} I _L X)))

/-- The iterated Lemma 4 isomorphism between the interpretation of an
iterated precomposition and the interpretation at `mplus`. -/
def mprecompIso (L : List (SupObj.{uB, uI} I)) :
    ∀ (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I),
      FreeCoprodCompDisc.Iso O (interpObj I O (mprecomp I O L γ) X)
        (interpObj I O γ (mplus.{uA, uB, uI} I L X)) :=
  L.rec (motive := fun L => ∀ γ X,
      FreeCoprodCompDisc.Iso O (interpObj I O (mprecomp I O L γ) X)
        (interpObj I O γ (mplus.{uA, uB, uI} I L X)))
    (fun γ X => FreeCoprodCompDisc.Iso.refl O (interpObj I O γ X))
    (fun b _L ih γ X =>
      FreeCoprodCompDisc.Iso.trans O (ih (precomp I O b.1 b.2 γ) X)
        (interpPrecompIso I O γ b.1 b.2 (mplus.{uA, uB, uI} I _L X)))

/-- The semantic pre-unit component: the interpretation image of the
iterated injection, composed with the inverse of the iterated Lemma 4
isomorphism. -/
def preUnitComponent (γ : IR.{max uA uB, uB, uI, uO} I O)
    (L : List (SupObj.{uB, uI} I)) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom O (interpObj I O γ X)
      (interpObj I O (mprecomp I O L γ) X) :=
  FreeCoprodCompDisc.Hom.comp O
    (interpMor I O γ X (mplus.{uA, uB, uI} I L X) (mplusInj.{uA, uB, uI} I L X))
    (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O L γ X))

/-- At the empty stack the semantic pre-unit component is the
identity. -/
theorem preUnitComponent_nil (γ : IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    preUnitComponent I O γ [] X = FreeCoprodCompDisc.Hom.id O (interpObj I O γ X) :=
  (congrArg (fun t => FreeCoprodCompDisc.Hom.comp O t
      (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O [] γ X)))
    (interpMor_id I O γ X)).trans
    (FreeCoprodCompDisc.Hom.id_comp O
      (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O [] γ X)))

/-- Transport of a composite with a fresh right injection along an
equality of the inner object, by elimination of the generalized
equality: the cast passes to the left factor. -/
theorem comp_coprodPairInr_cast (a : SupObj.{uB, uI} I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W')
      (u : FreeCoprodCompDisc.Hom I X W),
      cast (congrArg (FreeCoprodCompDisc.Hom I X)
          (congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) e))
        (FreeCoprodCompDisc.Hom.comp I u
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W)) =
      FreeCoprodCompDisc.Hom.comp I
        (cast (congrArg (FreeCoprodCompDisc.Hom I X) e) u)
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W') :=
  fun W _W' e =>
    Eq.rec (motive := fun W'' e' => ∀ u : FreeCoprodCompDisc.Hom I X W,
        cast (congrArg (FreeCoprodCompDisc.Hom I X)
            (congrArg (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a) e'))
          (FreeCoprodCompDisc.Hom.comp I u
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W)) =
        FreeCoprodCompDisc.Hom.comp I
          (cast (congrArg (FreeCoprodCompDisc.Hom I X) e') u)
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a W''))
      (fun _ => rfl) e

/-- `IR.mplusInj` at a right-appended superscript, transported along
`IR.mplus_snoc`: the fresh inner injection followed by the tower
injection at the enlarged base. -/
theorem mplusInj_snoc (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    cast (congrArg (FreeCoprodCompDisc.Hom I X) (mplus_snoc.{uA, uB, uI} I L b X))
        (mplusInj.{uA, uB, uI} I (L ++ [b]) X) =
      FreeCoprodCompDisc.Hom.comp I
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
        (mplusInj.{uA, uB, uI} I L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)) :=
  L.rec (motive := fun L' =>
      cast (congrArg (FreeCoprodCompDisc.Hom I X) (mplus_snoc.{uA, uB, uI} I L' b X))
          (mplusInj.{uA, uB, uI} I (L' ++ [b]) X) =
        FreeCoprodCompDisc.Hom.comp I
          (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
          (mplusInj.{uA, uB, uI} I L'
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
    ((FreeCoprodCompDisc.Hom.id_comp I
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)).trans
      (FreeCoprodCompDisc.Hom.comp_id I
        (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)).symm)
    (fun a _L ih =>
      (comp_coprodPairInr_cast I a X (mplus.{uA, uB, uI} I (_L ++ [b]) X)
          (mplus.{uA, uB, uI} I _L (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
          (mplus_snoc.{uA, uB, uI} I _L b X)
          (mplusInj.{uA, uB, uI} I (_L ++ [b]) X)).trans
        ((congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp I t
              (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
                (mplus.{uA, uB, uI} I _L
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
            ih).trans
          (FreeCoprodCompDisc.Hom.comp_assoc I
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I b X)
            (mplusInj.{uA, uB, uI} I _L
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
            (FreeCoprodCompDisc.coprodPairInr.{uI, uB, max uA uB} I a
              (mplus.{uA, uB, uI} I _L
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))))

/-- The Lemma 4 isomorphism commutes object-equality transports across
its two sides (forward direction), by elimination of the generalized
equality. -/
theorem interpPrecompIso_hom_isoOfEq (γ : IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) :
    ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W'),
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O (precomp I O Q q γ)) e)))
          (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W')) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg
              (fun w => interpObj I O γ
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
              e))) :=
  fun W _W' e =>
    Eq.rec (motive := fun W'' e' =>
        FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O (precomp I O Q q γ)) e')))
            (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W'')) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O γ Q q W))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg
                (fun w => interpObj I O γ
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
                e'))))
      rfl e

/-- The Lemma 4 isomorphism commutes object-equality transports across
its two sides (inverse direction), by elimination of the generalized
equality. -/
theorem interpPrecompIso_invHom_isoOfEq (γ : IR.{max uA uB, uB, uI, uO} I O)
    (Q : Type uB) (q : Q → I) :
    ∀ (W W' : FreeCoprodCompDisc.{max uA uB, uI} I) (e : W = W'),
      FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg
              (fun w => interpObj I O γ
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
              e)))
          (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W')) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O (precomp I O Q q γ)) e))) :=
  fun W _W' e =>
    Eq.rec (motive := fun W'' e' =>
        FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg
                (fun w => interpObj I O γ
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ w))
                e')))
            (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W'')) =
          FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.invHom O (interpPrecompIso I O γ Q q W))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O (precomp I O Q q γ)) e'))))
      rfl e

/-- The forward component of `IR.mprecompIso` at a right-appended
superscript: one Lemma 4 layer at the base of the tower, conjugated by
the `IR.mprecomp_snoc` and `IR.mplus_snoc` transports. -/
theorem mprecompIso_snoc_hom (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O (L ++ [b]) γ X) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun c => interpObj I O c X) (mprecomp_snoc I O L b γ))))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X)))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X).symm)))) :=
  L.rec (motive := fun L' => ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
      FreeCoprodCompDisc.Iso.hom O
          (mprecompIso.{uA, uB, uI, uO} I O (L' ++ [b]) γ' X) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun c => interpObj I O c X) (mprecomp_snoc I O L' b γ'))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (mprecomp I O L' γ') b.1 b.2 X)))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L' γ'
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ')
                (mplus_snoc.{uA, uB, uI} I L' b X).symm)))))
    (fun _ => rfl)
    (fun a _L ih γ' =>
      (congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O t
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O γ' a.1 a.2
                (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
          (ih (precomp I O a.1 a.2 γ'))).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (fun c => interpObj I O c X)
                  (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')))))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                  b.1 b.2 X)))
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                  (mplus_snoc.{uA, uB, uI} I _L b X).symm))))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O γ' a.1 a.2
                (mplus.{uA, uB, uI} I (_L ++ [b]) X)))).trans
          (congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun c => interpObj I O c X)
                    (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')))))
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O
                    (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))))
            ((FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                    (mplus_snoc.{uA, uB, uI} I _L b X).symm)))
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I (_L ++ [b]) X)))).trans
              ((congrArg
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O a.1 a.2 γ')
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
                  (interpPrecompIso_hom_isoOfEq I O γ' a.1 a.2
                    (mplus.{uA, uB, uI} I _L
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
                    (mplus.{uA, uB, uI} I (_L ++ [b]) X)
                    (mplus_snoc.{uA, uB, uI} I _L b X).symm)).trans
                (FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O γ' a.1 a.2
                      (mplus.{uA, uB, uI} I _L
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
                  (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                    (congrArg
                      (fun w => interpObj I O γ'
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a w))
                      (mplus_snoc.{uA, uB, uI} I _L b X).symm)))).symm)))))
    γ

/-- The inverse component of `IR.mprecompIso` at a right-appended
superscript: the inverse of one Lemma 4 layer at the base of the
tower, conjugated by the `IR.mplus_snoc` and `IR.mprecomp_snoc`
transports. -/
theorem mprecompIso_snoc_invHom (L : List (SupObj.{uB, uI} I)) (b : SupObj.{uB, uI} I)
    (γ : IR.{max uA uB, uB, uI, uO} I O) (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Iso.invHom O
        (mprecompIso.{uA, uB, uI, uO} I O (L ++ [b]) γ X) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (interpObj I O γ) (mplus_snoc.{uA, uB, uI} I L b X))))
          (FreeCoprodCompDisc.Iso.invHom O (mprecompIso.{uA, uB, uI, uO} I O L γ
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.invHom O
            (interpPrecompIso I O (mprecomp I O L γ) b.1 b.2 X))
          (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
            (congrArg (fun c => interpObj I O c X)
              (mprecomp_snoc I O L b γ).symm)))) :=
  L.rec (motive := fun L' => ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
      FreeCoprodCompDisc.Iso.invHom O
          (mprecompIso.{uA, uB, uI, uO} I O (L' ++ [b]) γ' X) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (interpObj I O γ') (mplus_snoc.{uA, uB, uI} I L' b X))))
            (FreeCoprodCompDisc.Iso.invHom O
              (mprecompIso.{uA, uB, uI, uO} I O L' γ'
                (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))))
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.invHom O
              (interpPrecompIso I O (mprecomp I O L' γ') b.1 b.2 X))
            (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
              (congrArg (fun c => interpObj I O c X)
                (mprecomp_snoc I O L' b γ').symm)))))
    (fun _ => rfl)
    (fun a _L ih γ' =>
      (congrArg
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Iso.invHom O
              (interpPrecompIso I O γ' a.1 a.2
                (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
          (ih (precomp I O a.1 a.2 γ'))).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Iso.invHom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X))))
            (FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                  (mplus_snoc.{uA, uB, uI} I _L b X))))
              (FreeCoprodCompDisc.Iso.invHom O
                (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.invHom O
                  (interpPrecompIso I O
                    (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))
                (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                  (congrArg (fun c => interpObj I O c X)
                    (mprecomp_snoc I O _L b (precomp I O a.1 a.2 γ')).symm)))))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Iso.invHom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X)))
              (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                (congrArg (interpObj I O (precomp I O a.1 a.2 γ'))
                  (mplus_snoc.{uA, uB, uI} I _L b X))))
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Iso.invHom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ')
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.invHom O
                    (interpPrecompIso I O
                      (mprecomp I O _L (precomp I O a.1 a.2 γ')) b.1 b.2 X))
                  (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                    (congrArg (fun c => interpObj I O c X)
                      (mprecomp_snoc I O _L b
                        (precomp I O a.1 a.2 γ')).symm)))))).symm.trans
            ((congrArg
                (fun t => FreeCoprodCompDisc.Hom.comp O t
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.invHom O
                      (mprecompIso.{uA, uB, uI, uO} I O _L
                        (precomp I O a.1 a.2 γ')
                        (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O
                          (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                          b.1 b.2 X))
                      (FreeCoprodCompDisc.Iso.hom O
                        (FreeCoprodCompDisc.isoOfEq O
                          (congrArg (fun c => interpObj I O c X)
                            (mprecomp_snoc I O _L b
                              (precomp I O a.1 a.2 γ')).symm))))))
                (interpPrecompIso_invHom_isoOfEq I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I (_L ++ [b]) X)
                  (mplus.{uA, uB, uI} I _L
                    (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X))
                  (mplus_snoc.{uA, uB, uI} I _L b X)).symm).trans
              ((FreeCoprodCompDisc.Hom.comp_assoc O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                      (congrArg
                        (fun w => interpObj I O γ'
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a w))
                        (mplus_snoc.{uA, uB, uI} I _L b X))))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O γ' a.1 a.2
                        (mplus.{uA, uB, uI} I _L
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))))
                  (FreeCoprodCompDisc.Iso.invHom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O a.1 a.2 γ')
                      (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O
                        (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                        b.1 b.2 X))
                    (FreeCoprodCompDisc.Iso.hom O (FreeCoprodCompDisc.isoOfEq O
                      (congrArg (fun c => interpObj I O c X)
                        (mprecomp_snoc I O _L b
                          (precomp I O a.1 a.2 γ')).symm))))).trans
                ((congrArg
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (FreeCoprodCompDisc.isoOfEq O
                          (congrArg
                            (fun w => interpObj I O γ'
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                I a w))
                            (mplus_snoc.{uA, uB, uI} I _L b X)))))
                    (FreeCoprodCompDisc.Hom.comp_assoc O
                      (FreeCoprodCompDisc.Iso.invHom O
                        (interpPrecompIso I O γ' a.1 a.2
                          (mplus.{uA, uB, uI} I _L
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                              I b X))))
                      (FreeCoprodCompDisc.Iso.invHom O
                        (mprecompIso.{uA, uB, uI, uO} I O _L
                          (precomp I O a.1 a.2 γ')
                          (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I b X)))
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.invHom O
                          (interpPrecompIso I O
                            (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                            b.1 b.2 X))
                        (FreeCoprodCompDisc.Iso.hom O
                          (FreeCoprodCompDisc.isoOfEq O
                            (congrArg (fun c => interpObj I O c X)
                              (mprecomp_snoc I O _L b
                                (precomp I O a.1 a.2 γ')).symm)))))).symm.trans
                  (FreeCoprodCompDisc.Hom.comp_assoc O
                    (FreeCoprodCompDisc.Hom.comp O
                      (FreeCoprodCompDisc.Iso.hom O
                        (FreeCoprodCompDisc.isoOfEq O
                          (congrArg
                            (fun w => interpObj I O γ'
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                I a w))
                            (mplus_snoc.{uA, uB, uI} I _L b X))))
                      (FreeCoprodCompDisc.Hom.comp O
                        (FreeCoprodCompDisc.Iso.invHom O
                          (interpPrecompIso I O γ' a.1 a.2
                            (mplus.{uA, uB, uI} I _L
                              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                                I b X))))
                        (FreeCoprodCompDisc.Iso.invHom O
                          (mprecompIso.{uA, uB, uI, uO} I O _L
                            (precomp I O a.1 a.2 γ')
                            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB}
                              I b X)))))
                    (FreeCoprodCompDisc.Iso.invHom O
                      (interpPrecompIso I O
                        (mprecomp I O _L (precomp I O a.1 a.2 γ'))
                        b.1 b.2 X))
                    (FreeCoprodCompDisc.Iso.hom O
                      (FreeCoprodCompDisc.isoOfEq O
                        (congrArg (fun c => interpObj I O c X)
                          (mprecomp_snoc I O _L b
                            (precomp I O a.1 a.2 γ')).symm))))))))))
    γ

/-- The tower action on morphisms: the identity on every stacked
superscript, the given morphism at the base. -/
def mplusMorMap (L : List (SupObj.{uB, uI} I))
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h : FreeCoprodCompDisc.Hom I X Y) :
    FreeCoprodCompDisc.Hom I (mplus.{uA, uB, uI} I L X) (mplus.{uA, uB, uI} I L Y) :=
  L.rec (motive := fun L' =>
      FreeCoprodCompDisc.Hom I (mplus.{uA, uB, uI} I L' X) (mplus.{uA, uB, uI} I L' Y))
    h
    (fun b _L ih =>
      FreeCoprodCompDisc.coprodPairMor I (FreeCoprodCompDisc.Hom.id I b) ih)

/-- The iterated Lemma 4 naturality: `IR.mprecompIso` is natural in the
interpreted object, between the tower interpretation's morphism map and
the direct interpretation's at the `IR.mplusMorMap` image. -/
theorem mprecompIso_natural (L : List (SupObj.{uB, uI} I))
    (γ : IR.{max uA uB, uB, uI, uO} I O)
    (X Y : FreeCoprodCompDisc.{max uA uB, uI} I) (h : FreeCoprodCompDisc.Hom I X Y) :
    FreeCoprodCompDisc.Hom.comp O
        (interpMor I O (mprecomp I O L γ) X Y h)
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ Y)) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O (mprecompIso.{uA, uB, uI, uO} I O L γ X))
        (interpMor I O γ (mplus.{uA, uB, uI} I L X) (mplus.{uA, uB, uI} I L Y)
          (mplusMorMap.{uA, uB, uI} I L X Y h)) :=
  L.rec (motive := fun L' => ∀ γ' : IR.{max uA uB, uB, uI, uO} I O,
      FreeCoprodCompDisc.Hom.comp O
          (interpMor I O (mprecomp I O L' γ') X Y h)
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O L' γ' Y)) =
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O L' γ' X))
          (interpMor I O γ' (mplus.{uA, uB, uI} I L' X)
            (mplus.{uA, uB, uI} I L' Y) (mplusMorMap.{uA, uB, uI} I L' X Y h)))
    (fun γ' =>
      (FreeCoprodCompDisc.Hom.comp_id O (interpMor I O γ' X Y h)).trans
        (FreeCoprodCompDisc.Hom.id_comp O (interpMor I O γ' X Y h)).symm)
    (fun a _L ih γ' =>
      (FreeCoprodCompDisc.Hom.comp_assoc O
          (interpMor I O (mprecomp I O _L (precomp I O a.1 a.2 γ')) X Y h)
          (FreeCoprodCompDisc.Iso.hom O
            (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ') Y))
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O γ' a.1 a.2
              (mplus.{uA, uB, uI} I _L Y)))).symm.trans
        ((congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O γ' a.1 a.2 (mplus.{uA, uB, uI} I _L Y))))
            (ih (precomp I O a.1 a.2 γ'))).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Iso.hom O
                (mprecompIso.{uA, uB, uI, uO} I O _L (precomp I O a.1 a.2 γ') X))
              (interpMor I O (precomp I O a.1 a.2 γ') (mplus.{uA, uB, uI} I _L X)
                (mplus.{uA, uB, uI} I _L Y) (mplusMorMap.{uA, uB, uI} I _L X Y h))
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I _L Y)))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Iso.hom O
                    (mprecompIso.{uA, uB, uI, uO} I O _L
                      (precomp I O a.1 a.2 γ') X)))
                (interpPrecompIso_natural I O γ' a.1 a.2
                  (mplus.{uA, uB, uI} I _L X) (mplus.{uA, uB, uI} I _L Y)
                  (mplusMorMap.{uA, uB, uI} I _L X Y h))).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Iso.hom O
                  (mprecompIso.{uA, uB, uI, uO} I O _L
                    (precomp I O a.1 a.2 γ') X))
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O γ' a.1 a.2 (mplus.{uA, uB, uI} I _L X)))
                (interpMor I O γ'
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                    (mplus.{uA, uB, uI} I _L X))
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I a
                    (mplus.{uA, uB, uI} I _L Y))
                  (FreeCoprodCompDisc.coprodPairMor I
                    (FreeCoprodCompDisc.Hom.id I a)
                    (mplusMorMap.{uA, uB, uI} I _L X Y h)))).symm))))
    γ

end IR

end IndRec
