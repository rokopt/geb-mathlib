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
* `IR.interpHomDeltaSummand` — the per-summand transport of the
  `δ`-domain case of `IR.interpHomEquiv`.
* `IR.InterpHomSigmaPushMotive` — the statement of the
  `IR.sigmaPush` characterization at one code.
* `IR.interpHomIotaComposite`, `IR.interpHomIotaCast` — the
  `ι`-branch equivalence of the Theorem 3 step and its transport
  along a code equality.

## Main statements

* `IR.mplus_snoc`, `IR.mplusInj_snoc`, `IR.mprecompIso_snoc_hom`,
  `IR.mprecompIso_snoc_invHom` — the tower at a right-appended
  superscript, the direction in which the `δ`-case of the
  identity-image induction extends the stack.
* `IR.mprecompIso_natural` — naturality of the tower isomorphism in
  the interpreted object.
* `IR.preUnitComponent_nil` — the semantic pre-unit component at the
  empty stack is the identity.
* `IR.interpHomEquiv_mk`, `IR.innerHomEquiv_mk` — the reductions of
  the Theorem 3 equivalence and of the inner-hom equivalence at an
  `IR.mk`-built domain code.
* `IR.interpHom_iota`, `IR.interpHom_sigma`, `IR.interpHom_delta` —
  the component of `IR.interpHom` at each shape of domain code.
* `IR.deltaDesc_comp`, `IR.interpMor_sigma_inj` — right-composition
  of the `δ`-cotuple, and the commutation of a semantic
  `σ`-injection with the morphism map of a `σ`-interpretation.
* `IR.interpHom_sigmaPush` — `IR.interpHom` sends `IR.sigmaPush` to
  composition with the semantic `σ`-injection.
* `IR.interpPrecompIso_sigma_inj` — the Lemma 4 `σ`-square.

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

/-- Components pass through `NatTrans.congrSource` unchanged. -/
theorem congrSource_symm_fst {F G : FreeCoprodCompDisc.Map.{uA, uI, uO} I O}
    {mF mF' : FreeCoprodCompDisc.MapMor I O F} (e : mF = mF')
    (mG : FreeCoprodCompDisc.MapMor I O G)
    (η : FreeCoprodCompDisc.NatTrans I O F G mF' mG) :
    ((FreeCoprodCompDisc.NatTrans.congrSource e mG).symm η).1 = η.1 :=
  Eq.rec (motive := fun mF'' e' =>
      ∀ η' : FreeCoprodCompDisc.NatTrans I O F G mF'' mG,
        ((FreeCoprodCompDisc.NatTrans.congrSource e' mG).symm η').1 = η'.1)
    (fun _ => rfl) e η

/-- The characterizing equation of `IR.interpHomEquiv` at `IR.mk`. -/
theorem interpHomEquiv_mk (s : Shape.{max uA uB, uB, uO} O)
    (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O)
    (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    interpHomEquiv I O (mk I O s d) γ' =
      interpHomEquivStep I O s d (fun x => interpHomEquiv I O (d x)) γ' :=
  congrFun (rec_mk I O (interpHomEquivStep I O) s d) γ'

/-- The component of `IR.interpHom` at an `ι`-domain: the singleton
morphism carried by the inner hom, composed with the codomain's image
of the unique morphism out of the initial object. -/
theorem interpHom_iota (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : InnerHom.{uA, uB, uI, uO} I O o γ')
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O (iota.{max uA uB, uB, uI, uO} I O o) γ' f).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((FreeCoprodCompDisc.homSingletonEquiv O o
            (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))).symm
          (innerHomEquiv I O o γ' f))
        (interpMor I O γ' (FreeCoprodCompDisc.emptyObj I) X
          (FreeCoprodCompDisc.emptyDesc I X)) :=
  congrArg (fun e => (e f).1 X)
    (interpHomEquiv_mk I O (Sum.inl o) PEmpty.elim γ')

/-- The component of `IR.interpHom` at a `σ`-domain: the cotuple of the
subcode components. -/
theorem interpHom_sigma (A : Type (max uA uB))
    (K : A → IR.{max uA uB, uB, uI, uO} I O)
    (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O (sigma I O A K) γ')
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O (sigma I O A K) γ' f).1 X =
      FreeCoprodCompDisc.coprodDesc O A (fun a => interpObj I O (K a) X)
        (interpObj I O γ' X)
        (fun a => (interpHom I O (K a) γ' (f a)).1 X) :=
  (congrArg (fun e => (e f).1 X)
      (interpHomEquiv_mk I O (Sum.inr (Sum.inl A)) (K ∘ ULift.down) γ')).trans
    (congrFun
      (congrSource_symm_fst.{max uA uB, uI, uO} I O
        (interpMor_sigma.{max uA uB, uB, uI, uO} I O A K) _
        (FreeCoprodCompDisc.natCoprodEquiv.{max uA uB, uI, uO} A
            (fun a => interpObj I O (K a))
            (fun a => interpMor I O (K a)) (interpObj I O γ')
            (interpMor I O γ')
          |>.symm (fun a => interpHomEquiv I O (K a) γ' (f a))))
      X)

/-- The per-summand transport of the `δ`-domain case of
`IR.interpHomEquiv`: the interpretation of a clause 3 component,
transported to a transformation out of the copower summand by the
Lemma 4 pair, the bridge pair, and the copower adjunction. -/
def interpHomDeltaSummand (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (γ' : IR.{max uA uB, uB, uI, uO} I O) (i : B → I)
    (g : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i γ')) :
    FreeCoprodCompDisc.NatTrans I O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)))
      (interpObj I O γ')
      (FreeCoprodCompDisc.copowerHomMapMor
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpMor I O (c i)))
      (interpMor I O γ') :=
  (FreeCoprodCompDisc.natCopowerPlusEquiv
      (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
      (interpMor I O (c i)) (interpMor I O γ')
      (interpMor_id I O (c i)) (interpMor_comp I O (c i))
      (interpMor_id I O γ') (interpMor_comp I O γ')).symm
    (FreeCoprodCompDisc.NatTrans.vcomp
      (FreeCoprodCompDisc.NatTrans.vcomp
        (interpHom I O (c i) (precomp I O B i γ') g)
        (FreeCoprodCompDisc.NatTrans.ofIsoFamily
          (fun k => interpPrecompIso I O γ' B i k)
          (interpPrecompIso_natural I O γ' B i)))
      (plusLiftBridgeNatInv I O B i γ'))

/-- The component of `IR.interpHom` at a `δ`-domain: the cotuple of the
transported subcode components. -/
theorem interpHom_delta (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (f : Hom.{uA, uB, uI, uO} I O (delta I O B c) γ')
    (X : FreeCoprodCompDisc.{max uA uB, uI} I) :
    (interpHom I O (delta I O B c) γ' f).1 X =
      deltaDesc I O B c X (interpObj I O γ' X)
        (fun i => (interpHomDeltaSummand I O B c γ' i (f i)).1 X) :=
  congrArg (fun e => (e f).1 X)
    (interpHomEquiv_mk I O (Sum.inr (Sum.inr B)) (c ∘ ULift.down) γ')

/-- `IR.deltaDesc` composes on the right componentwise. -/
theorem deltaDesc_comp (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (Z W : FreeCoprodCompDisc.{max uA uB, uO} O)
    (m : (i : B → I) → FreeCoprodCompDisc.Hom O
      (FreeCoprodCompDisc.copowerHomMap
        (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩)
        (interpObj I O (c i)) X) Z)
    (g : FreeCoprodCompDisc.Hom O Z W) :
    FreeCoprodCompDisc.Hom.comp O (deltaDesc I O B c X Z m) g =
      deltaDesc I O B c X W (fun i => FreeCoprodCompDisc.Hom.comp O (m i) g) :=
  deltaHom_ext I O B c X W _ _ (fun i =>
    ((FreeCoprodCompDisc.Hom.comp_assoc O (deltaInto I O B c i X)
        (deltaDesc I O B c X Z m) g).symm.trans
      (congrArg (fun t => FreeCoprodCompDisc.Hom.comp O t g)
        (deltaInto_desc I O B c i X Z m))).trans
    (deltaInto_desc I O B c i X W
      (fun i' => FreeCoprodCompDisc.Hom.comp O (m i') g)).symm)

/-- The `σ`-injection square: a semantic `σ`-injection commutes the
morphism map of a `σ`-interpretation with the summand's. -/
theorem interpMor_sigma_inj (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (Z W : FreeCoprodCompDisc.{max uA uB, uI} I)
    (h : FreeCoprodCompDisc.Hom I Z W) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) Z) a')
        (interpMor I O (sigma I O A' K') Z W h) =
      FreeCoprodCompDisc.Hom.comp O (interpMor I O (K' a') Z W h)
        (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) W) a') :=
  (congrArg
      (fun (t : MorMapSig I O (sigma I O A' K')) =>
        FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) Z) a')
          (t Z W h))
      (interpMor_sigma.{max uA uB, uB, uI, uO} I O A' K')).trans
    (FreeCoprodCompDisc.coprodInj_mor O A' A' _root_.id
        (fun a => interpObj I O (K' a) Z) (fun a => interpObj I O (K' a) W)
        (fun a => interpMor I O (K' a) Z W h) a').symm

/-- The characterizing equation of `IR.innerHomEquiv` at `IR.mk`. -/
theorem innerHomEquiv_mk (o : O) (s : Shape.{max uA uB, uB, uO} O)
    (d : Direction I O s → IR.{max uA uB, uB, uI, uO} I O) :
    innerHomEquiv I O o (mk I O s d) =
      innerHomEquivStep I O o s d (fun x => innerHomEquiv I O o (d x)) :=
  rec_mk I O (innerHomEquivStep I O o) s d

/-- The statement of the `IR.sigmaPush` characterization at one code:
`IR.interpHom` sends a pushed morphism to the composite with the
semantic `σ`-injection. -/
def InterpHomSigmaPushMotive (γ : IR.{max uA uB, uB, uI, uO} I O) : Prop :=
  ∀ (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A') (f : Hom.{uA, uB, uI, uO} I O γ (K' a'))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I),
    (interpHom I O γ (sigma I O A' K') (sigmaPush I O γ A' K' a' f)).1 X =
      FreeCoprodCompDisc.Hom.comp O ((interpHom I O γ (K' a') f).1 X)
        (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) X) a')

/-- The `ι`-composite of the Theorem 3 step at codomain `γ'`
(definitionally the equivalence the step transports). -/
def interpHomIotaComposite (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O) :
    InnerHom.{uA, uB, uI, uO} I O o γ' ≃
      FreeCoprodCompDisc.NatTrans I O
        (interpObj I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpObj I O γ')
        (interpMor I O (iota.{max uA uB, uB, uI, uO} I O o)) (interpMor I O γ') :=
  (innerHomEquiv I O o γ').trans
    ((FreeCoprodCompDisc.homSingletonEquiv O o
        (interpObj I O γ' (FreeCoprodCompDisc.emptyObj I))).symm.trans
      (natIotaEquiv I O o γ').symm)

/-- The transport of `IR.interpHomIotaComposite` along a code equality
(definitionally the `ι`-branch of `IR.interpHomEquivStep`). -/
def interpHomIotaCast (o : O) (γ' : IR.{max uA uB, uB, uI, uO} I O)
    (ir : IR.{max uA uB, uB, uI, uO} I O)
    (e : iota.{max uA uB, uB, uI, uO} I O o = ir) :
    InnerHom.{uA, uB, uI, uO} I O o γ' ≃
      FreeCoprodCompDisc.NatTrans I O (interpObj I O ir) (interpObj I O γ')
        (interpMor I O ir) (interpMor I O γ') :=
  Eq.rec (motive := fun ir' _ =>
      InnerHom.{uA, uB, uI, uO} I O o γ' ≃
        FreeCoprodCompDisc.NatTrans I O (interpObj I O ir') (interpObj I O γ')
          (interpMor I O ir') (interpMor I O γ'))
    (interpHomIotaComposite I O o γ') e

/-- The singleton morphism at a `σ`-summand name factors through the
semantic `σ`-injection. -/
theorem homSingletonEquiv_symm_inj (o : O) (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (z : {z : (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I)).1 //
      (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I)).2 z = o}) :
    (FreeCoprodCompDisc.homSingletonEquiv O o
        (interpObj I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I))).symm
        ⟨⟨a', z.1⟩, z.2⟩ =
      FreeCoprodCompDisc.Hom.comp O
        ((FreeCoprodCompDisc.homSingletonEquiv O o
            (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I))).symm z)
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a => interpObj I O (K' a) (FreeCoprodCompDisc.emptyObj I)) a') :=
  Subtype.ext (funext (fun _ => rfl))

/-- The `σ`-push equation for the transported `ι`-composite, by
elimination of the code equality: at the reflexive instance both sides
compute to singleton morphisms into the initial-object fiber, related
by `IR.homSingletonEquiv_symm_inj` and the `σ`-injection square. -/
theorem interpHomIotaCast_sigmaPush (o : O) (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (f : InnerHom.{uA, uB, uI, uO} I O o (K' a'))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (ir : IR.{max uA uB, uB, uI, uO} I O)
    (e : iota.{max uA uB, uB, uI, uO} I O o = ir) :
    ((interpHomIotaCast I O o (sigma I O A' K') ir e) ⟨a', f⟩).1 X =
      FreeCoprodCompDisc.Hom.comp O
        (((interpHomIotaCast I O o (K' a') ir e) f).1 X)
        (FreeCoprodCompDisc.coprodInj O A' (fun a => interpObj I O (K' a) X) a') :=
  Eq.rec (motive := fun ir' e' =>
      ((interpHomIotaCast I O o (sigma I O A' K') ir' e') ⟨a', f⟩).1 X =
        FreeCoprodCompDisc.Hom.comp O
          (((interpHomIotaCast I O o (K' a') ir' e') f).1 X)
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a => interpObj I O (K' a) X) a'))
    ((congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O
          ((FreeCoprodCompDisc.homSingletonEquiv O o
              (interpObj I O (sigma I O A' K')
                (FreeCoprodCompDisc.emptyObj I))).symm (t ⟨a', f⟩))
          (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
            (FreeCoprodCompDisc.emptyDesc I X)))
        (innerHomEquiv_mk I O o (Sum.inr (Sum.inl A')) (K' ∘ ULift.down))).trans
      ((congrArg
          (fun t => FreeCoprodCompDisc.Hom.comp O t
            (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
              (FreeCoprodCompDisc.emptyDesc I X)))
          (homSingletonEquiv_symm_inj I O o A' K' a'
            (innerHomEquiv I O o (K' a') f))).trans
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            ((FreeCoprodCompDisc.homSingletonEquiv O o
                (interpObj I O (K' a') (FreeCoprodCompDisc.emptyObj I))).symm
              (innerHomEquiv I O o (K' a') f))
            (FreeCoprodCompDisc.coprodInj O A'
              (fun a => interpObj I O (K' a) (FreeCoprodCompDisc.emptyObj I)) a')
            (interpMor I O (sigma I O A' K') (FreeCoprodCompDisc.emptyObj I) X
              (FreeCoprodCompDisc.emptyDesc I X))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                ((FreeCoprodCompDisc.homSingletonEquiv O o
                    (interpObj I O (K' a')
                      (FreeCoprodCompDisc.emptyObj I))).symm
                  (innerHomEquiv I O o (K' a') f)))
              (interpMor_sigma_inj I O A' K' a'
                (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O
              ((FreeCoprodCompDisc.homSingletonEquiv O o
                  (interpObj I O (K' a')
                    (FreeCoprodCompDisc.emptyObj I))).symm
                (innerHomEquiv I O o (K' a') f))
              (interpMor I O (K' a') (FreeCoprodCompDisc.emptyObj I) X
                (FreeCoprodCompDisc.emptyDesc I X))
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a) X) a')).symm))))
    e

/-- The `ι`-case of the `IR.sigmaPush` characterization. -/
theorem interpHom_sigmaPush_mk_iota (o : O)
    (d : Direction I O (Sum.inl o : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O) :
    InterpHomSigmaPushMotive I O (mk I O (Sum.inl o) d) :=
  fun A' K' a' f X =>
    (congrArg
        (fun t => (interpHom I O (mk I O (Sum.inl o) d)
          (sigma I O A' K') t).1 X)
        (sigmaPush_mk_iota I O o d A' K' a' f)).trans
      ((congrArg (fun e => (e (⟨a', f⟩ :
            InnerHom.{uA, uB, uI, uO} I O o (sigma I O A' K'))).1 X)
          (interpHomEquiv_mk I O (Sum.inl o) d (sigma I O A' K'))).trans
        ((interpHomIotaCast_sigmaPush I O o A' K' a' f X
            (mk I O (Sum.inl o) d)
            (mk_congr I O (Sum.inl o)
              (funext (fun x => nomatch x)) :
                mk I O (Sum.inl o) PEmpty.elim = mk I O (Sum.inl o) d)).trans
          (congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a) X) a'))
            (congrArg (fun e => (e f).1 X)
              (interpHomEquiv_mk I O (Sum.inl o) d (K' a'))).symm)))

/-- The `σ`-domain case of the `IR.sigmaPush` characterization:
componentwise by the inductive hypotheses, then the cotuple
compatibility. -/
theorem interpHom_sigmaPush_mk_sigma (A : Type (max uA uB))
    (d : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inl A) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomSigmaPushMotive I O (d x)) :
    InterpHomSigmaPushMotive I O (mk I O (Sum.inr (Sum.inl A)) d) :=
  fun A' K' a' f X =>
    (congrArg
        (fun t => (interpHom I O (mk I O (Sum.inr (Sum.inl A)) d)
          (sigma I O A' K') t).1 X)
        (sigmaPush_mk_sigma I O A d A' K' a' f)).trans
      ((interpHom_sigma I O A (fun a => d (ULift.up a)) (sigma I O A' K')
          (fun b => sigmaPush I O (d (ULift.up b)) A' K' a' (f b)) X).trans
        ((congrArg
            (FreeCoprodCompDisc.coprodDesc O A
              (fun a => interpObj I O (d (ULift.up a)) X)
              (interpObj I O (sigma I O A' K') X))
            (funext (fun b => ih (ULift.up b) A' K' a' (f b) X))).trans
          ((FreeCoprodCompDisc.coprodDesc_comp O A
              (fun a => interpObj I O (d (ULift.up a)) X)
              (interpObj I O (K' a') X) (interpObj I O (sigma I O A' K') X)
              (fun b => (interpHom I O (d (ULift.up b)) (K' a') (f b)).1 X)
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a) X) a')).symm.trans
            (congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O t
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a) X) a'))
              (interpHom_sigma I O A (fun a => d (ULift.up a))
                (K' a') f X).symm))))

/-- The Lemma 4 `σ`-square: the isomorphism of `IR.interpPrecompIso`
at a `σ`-code commutes the lifted-summand injection with the direct
summand injection. -/
theorem interpPrecompIso_sigma_inj (A' : Type (max uA uB))
    (K' : A' → IR.{max uA uB, uB, uI, uO} I O) (a' : A')
    (Q : Type uB) (q : Q → I) (k : FreeCoprodCompDisc.{max uA uB, uI} I) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
          (fun x => interpObj I O (precomp I O Q q (K' x.down)) k)
          (ULift.up a'))
        (FreeCoprodCompDisc.Iso.hom O
          (interpPrecompIso I O (sigma I O A' K') Q q k)) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Iso.hom O (interpPrecompIso I O (K' a') Q q k))
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a => interpObj I O (K' a)
            (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨Q, q⟩ k)) a') :=
  (congrArg
      (fun t => FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
          (fun x => interpObj I O (precomp I O Q q (K' x.down)) k)
          (ULift.up a'))
        (FreeCoprodCompDisc.Iso.hom O (t Q q k)))
      (interpPrecompIso_mk I O (Sum.inr (Sum.inl A')) (K' ∘ ULift.down))).trans
    (Subtype.ext (funext (fun _ => rfl)))

/-- The transported-composite equation behind the `δ`-domain case: a
`σ`-injection pushed through the Lemma 4 isomorphism and the bridge
factors out of the transported composite. -/
theorem interpHomDeltaSummand_theta (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A') (i : B → I)
    (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (sigma I O A' K')))
    (v : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (K' a')))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (hu : (interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
        (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
          (fun x => interpObj I O (precomp I O B i (K' x.down)) X)
          (ULift.up a'))) :
    FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          ((interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X)
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (sigma I O A' K') B i X)))
        ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X) =
      FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K' a') B i X)))
          ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a => interpObj I O (K' a)
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
          a') :=
  (congrArg
      (fun t => FreeCoprodCompDisc.Hom.comp O
        (FreeCoprodCompDisc.Hom.comp O t
          (FreeCoprodCompDisc.Iso.hom O
            (interpPrecompIso I O (sigma I O A' K') B i X)))
        ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X))
      hu).trans
    ((congrArg
        (fun t => FreeCoprodCompDisc.Hom.comp O t
          ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X))
        ((FreeCoprodCompDisc.Hom.comp_assoc O
            ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
            (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
              (fun x => interpObj I O (precomp I O B i (K' x.down)) X)
              (ULift.up a'))
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (sigma I O A' K') B i X))).trans
          ((congrArg
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X))
              (interpPrecompIso_sigma_inj I O A' K' a' B i X)).trans
            (FreeCoprodCompDisc.Hom.comp_assoc O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K' a') B i X))
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a)
                  (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X))
                a')).symm))).trans
      ((FreeCoprodCompDisc.Hom.comp_assoc O
          (FreeCoprodCompDisc.Hom.comp O
            ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
            (FreeCoprodCompDisc.Iso.hom O
              (interpPrecompIso I O (K' a') B i X)))
          (FreeCoprodCompDisc.coprodInj O A'
            (fun a => interpObj I O (K' a)
              (FreeCoprodCompDisc.plus.{uI, uB, max uA uB} I ⟨B, i⟩ X)) a')
          ((plusLiftBridgeNatInv I O B i (sigma I O A' K')).1 X)).trans
        ((congrArg
            (FreeCoprodCompDisc.Hom.comp O
              (FreeCoprodCompDisc.Hom.comp O
                ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                (FreeCoprodCompDisc.Iso.hom O
                  (interpPrecompIso I O (K' a') B i X))))
            (interpMor_sigma_inj I O A' K' a'
              (FreeCoprodCompDisc.plus I ⟨B, i⟩ X)
              (FreeCoprodCompDisc.plus I
                (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
              (plusLiftBridgeInvHom I B i X))).trans
          (FreeCoprodCompDisc.Hom.comp_assoc O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K' a') B i X)))
            ((plusLiftBridgeNatInv I O B i (K' a')).1 X)
            (FreeCoprodCompDisc.coprodInj O A'
              (fun a => interpObj I O (K' a)
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
              a')).symm)))

/-- The per-summand transport of a `σ`-injection through the `δ`-case
target transports, given the summand's own push equation. -/
theorem interpHomDeltaSummand_inj (B : Type uB)
    (c : (B → I) → IR.{max uA uB, uB, uI, uO} I O)
    (A' : Type (max uA uB)) (K' : A' → IR.{max uA uB, uB, uI, uO} I O)
    (a' : A') (i : B → I)
    (u : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (sigma I O A' K')))
    (v : Hom.{uA, uB, uI, uO} I O (c i) (precomp I O B i (K' a')))
    (X : FreeCoprodCompDisc.{max uA uB, uI} I)
    (hu : (interpHom I O (c i) (precomp I O B i (sigma I O A' K')) u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
        (FreeCoprodCompDisc.coprodInj O (ULift.{uB} A')
          (fun x => interpObj I O (precomp I O B i (K' x.down)) X)
          (ULift.up a'))) :
    (interpHomDeltaSummand I O B c (sigma I O A' K') i u).1 X =
      FreeCoprodCompDisc.Hom.comp O
        ((interpHomDeltaSummand I O B c (K' a') i v).1 X)
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a => interpObj I O (K' a) X) a') :=
  (congrArg
      (FreeCoprodCompDisc.coprodDesc O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ => interpObj I O (c i) X)
        (interpObj I O (sigma I O A' K') X))
      (funext (fun e =>
        (congrArg
            (fun t => FreeCoprodCompDisc.Hom.comp O t
              (interpMor I O (sigma I O A' K')
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                X
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X))))
            (interpHomDeltaSummand_theta I O B c A' K' a' i u v X hu)).trans
          ((FreeCoprodCompDisc.Hom.comp_assoc O
              (FreeCoprodCompDisc.Hom.comp O
                (FreeCoprodCompDisc.Hom.comp O
                  ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                  (FreeCoprodCompDisc.Iso.hom O
                    (interpPrecompIso I O (K' a') B i X)))
                ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a)
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X))
                a')
              (interpMor I O (sigma I O A' K')
                (FreeCoprodCompDisc.plus I
                  (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                X
                (FreeCoprodCompDisc.coprodPairDesc I e
                  (FreeCoprodCompDisc.Hom.id I X)))).trans
            ((congrArg
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    (FreeCoprodCompDisc.Hom.comp O
                      ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                      (FreeCoprodCompDisc.Iso.hom O
                        (interpPrecompIso I O (K' a') B i X)))
                    ((plusLiftBridgeNatInv I O B i (K' a')).1 X)))
                (interpMor_sigma_inj I O A' K' a'
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X)))).trans
              (FreeCoprodCompDisc.Hom.comp_assoc O
                (FreeCoprodCompDisc.Hom.comp O
                  (FreeCoprodCompDisc.Hom.comp O
                    ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
                    (FreeCoprodCompDisc.Iso.hom O
                      (interpPrecompIso I O (K' a') B i X)))
                  ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
                (interpMor I O (K' a')
                  (FreeCoprodCompDisc.plus I
                    (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
                  X
                  (FreeCoprodCompDisc.coprodPairDesc I e
                    (FreeCoprodCompDisc.Hom.id I X)))
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a) X) a')).symm))))).trans
    (FreeCoprodCompDisc.coprodDesc_comp O
        (FreeCoprodCompDisc.Hom I
          (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X)
        (fun _ => interpObj I O (c i) X) (interpObj I O (K' a') X)
        (interpObj I O (sigma I O A' K') X)
        (fun e => FreeCoprodCompDisc.Hom.comp O
          (FreeCoprodCompDisc.Hom.comp O
            (FreeCoprodCompDisc.Hom.comp O
              ((interpHom I O (c i) (precomp I O B i (K' a')) v).1 X)
              (FreeCoprodCompDisc.Iso.hom O
                (interpPrecompIso I O (K' a') B i X)))
            ((plusLiftBridgeNatInv I O B i (K' a')).1 X))
          (interpMor I O (K' a')
            (FreeCoprodCompDisc.plus I
              (FreeCoprodCompDisc.lift.{uB, uI, max uA uB} I ⟨B, i⟩) X) X
            (FreeCoprodCompDisc.coprodPairDesc I e
              (FreeCoprodCompDisc.Hom.id I X))))
        (FreeCoprodCompDisc.coprodInj O A'
          (fun a => interpObj I O (K' a) X) a')).symm

/-- The `δ`-domain case of the `IR.sigmaPush` characterization. -/
theorem interpHom_sigmaPush_mk_delta (B : Type uB)
    (d : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O) →
      IR.{max uA uB, uB, uI, uO} I O)
    (ih : (x : Direction I O (Sum.inr (Sum.inr B) : Shape.{max uA uB, uB, uO} O)) →
      InterpHomSigmaPushMotive I O (d x)) :
    InterpHomSigmaPushMotive I O (mk I O (Sum.inr (Sum.inr B)) d) :=
  fun A' K' a' f X =>
    (congrArg
        (fun t => (interpHom I O (mk I O (Sum.inr (Sum.inr B)) d)
          (sigma I O A' K') t).1 X)
        (sigmaPush_mk_delta I O B d A' K' a' f)).trans
      ((interpHom_delta I O B (fun j => d (ULift.up j)) (sigma I O A' K')
          (fun i => sigmaPush I O (d (ULift.up i)) (ULift.{uB} A')
            (fun x => precomp I O B i (K' x.down)) (ULift.up a') (f i)) X).trans
        ((congrArg
            (deltaDesc I O B (fun j => d (ULift.up j)) X
              (interpObj I O (sigma I O A' K') X))
            (funext (fun i =>
              interpHomDeltaSummand_inj I O B (fun j => d (ULift.up j))
                A' K' a' i
                (sigmaPush I O (d (ULift.up i)) (ULift.{uB} A')
                  (fun x => precomp I O B i (K' x.down)) (ULift.up a') (f i))
                (f i) X
                (ih (ULift.up i) (ULift.{uB} A')
                  (fun x => precomp I O B i (K' x.down)) (ULift.up a')
                  (f i) X)))).trans
          ((deltaDesc_comp I O B (fun j => d (ULift.up j)) X
              (interpObj I O (K' a') X) (interpObj I O (sigma I O A' K') X)
              (fun i => (interpHomDeltaSummand I O B (fun j => d (ULift.up j))
                (K' a') i (f i)).1 X)
              (FreeCoprodCompDisc.coprodInj O A'
                (fun a => interpObj I O (K' a) X) a')).symm.trans
            (congrArg
              (fun t => FreeCoprodCompDisc.Hom.comp O t
                (FreeCoprodCompDisc.coprodInj O A'
                  (fun a => interpObj I O (K' a) X) a'))
              (interpHom_delta I O B (fun j => d (ULift.up j))
                (K' a') f X).symm))))

/-- `IR.interpHom` sends `IR.sigmaPush` to composition with the
semantic `σ`-injection, by `IR.induction`. -/
theorem interpHom_sigmaPush (γ : IR.{max uA uB, uB, uI, uO} I O) :
    InterpHomSigmaPushMotive I O γ :=
  induction I O (InterpHomSigmaPushMotive I O)
    (fun s => match s with
      | Sum.inl o => fun d _ => interpHom_sigmaPush_mk_iota I O o d
      | Sum.inr (Sum.inl A) => fun d ih => interpHom_sigmaPush_mk_sigma I O A d ih
      | Sum.inr (Sum.inr B) => fun d ih => interpHom_sigmaPush_mk_delta I O B d ih)
    γ

end IR

end IndRec
