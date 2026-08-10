# Novelty note: the presheaf p.r.a. IR code `δ`

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Claim](#claim)
- [The rules compared](#the-rules-compared)
  - [Family-level `δ`](#family-level-%CE%B4)
  - [Indexed-induction-recursion `δ`](#indexed-induction-recursion-%CE%B4)
  - [Positive IR `δ`](#positive-ir-%CE%B4)
  - [Presheaf p.r.a. `δ`](#presheaf-pra-%CE%B4)
- [What distinguishes the presheaf `δ`](#what-distinguishes-the-presheaf-%CE%B4)
- [Sources examined](#sources-examined)
- [Assessment](#assessment)
- [Limits of this review](#limits-of-this-review)
- [Open points in the repository](#open-points-in-the-repository)
- [Suggested wording](#suggested-wording)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Status: draft for review. This note records the scope of a novelty claim and
the sources examined; it is not itself a claim of publication-grade novelty.

## Claim

`GebProto.delta` in `Geb/Internal/PresheafIRProto/Codes.lean` — the `δ`
constructor of a code system whose semantics are presheaf parametric
right-adjoint (p.r.a.) functors — has no precedent in the sources listed
under [Sources examined](#sources-examined). No source was found presenting
an inductive-recursive code system over presheaf categories, and none
presenting a `δ` rule that combines an output-varying arity with a
decoding-dependent continuation whose decodings are natural transformations.

## The rules compared

### Family-level `δ`

The codes of [GhaniNordvallForsbergMalatesta2015] Definition 2.1, following
[DybjerSetzer1999] and [DybjerSetzer2003]:

```text
ι d : IR(D)                          d : D
σ A f : IR(D)                        A : Set, f : A → IR(D)
δ A F : IR(D)                        A : Set, F : (A → D) → IR(D)
```

interpreted (Theorem 2.4, attributed there to [DybjerSetzer2003]) as
endofunctors of the category of set-indexed families `Fam |D|` over the
discrete category `|D|`:

```text
⟦δ A F⟧ (X, P) = Σ g : A → X, ⟦F (P ∘ g)⟧ (X, P)
```

The repository's family-level rule is this presentation with the
input/output index split of [HancockMcBrideGhaniMalatestaAltenkirch2013]
Definition 3: `IR.delta B c` with `c : (B → I) → IR I O` in
`Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`, interpreted in the free
coproduct completions (`FreeCoprodCompDisc`, i.e. `Fam`).

### Indexed-induction-recursion `δ`

The `δ` rule of small indexed induction recursion, recalled in Section 6
of [HancockMcBrideGhaniMalatestaAltenkirch2013] from [DybjerSetzer2006]
(verified against the authors' extended preprint and its literate Agda
source; see [Sources examined](#sources-examined)):

```text
δ : (P : Set) (i : P → I) (K : ((p : P) → D (i p)) → IIR D E) → IIR D E
⟦δ P i K⟧ G j = Σ (ig : (p : P) → dom (G (i p))),
                  ⟦K (λ p → fun (G (i p)) (ig p))⟧ G j
```

The semantics live in families of slice categories, `(i : I) → Set/(D i)`;
the direction set `P` is constant, and the decodings are plain sections
`(p : P) → D (i p)`.

### Positive IR `δ`

The closest precedent: [GhaniNordvallForsbergMalatesta2015] Section 3
generalizes the semantics of IR codes to `Fam(C)` for an arbitrary
(non-discrete) category `C`. The `δ` rule is

```text
δ A F : IR⁺(C)    A : Set, F : (A → C) → IR⁺(C) a functor
```

The continuation `F` is required to be a functor on the code category,
which forces codes and morphisms to be defined simultaneously, in an
inductive-inductive fashion (their Definition 3.1). The direction set `A`
remains a plain set, the decodings remain plain maps `A → C` with no
naturality condition, and the semantics are families over `C`, not
presheaves.

### Presheaf p.r.a. `δ`

`GebProto.delta` (in `Geb/Internal/PresheafIRProto/Codes.lean`), with
`A : BaseArity I J` an output-varying arity, `D : Iᵒᵖ ⥤ Type` a decoding
target, and `F` a presheaf p.r.a. functor:

```lean
def delta {J : Type uJ} [Category.{vJ} J]
    (A : BaseArity.{uI, uJ, uD, vI, vJ} I J) (hA : A.IsFunctorial)
    (D : Iᵒᵖ ⥤ Type uD)
    (F : PresheafPFunctor.{max uI uD, max uI uJ uD vI, uA, max uI uD, vI, vJ}
      (ElObj.{uI, uD, vI} D)
      (ElObj.{uJ, max uI uD vI, vJ} (decPresheaf A hA D))) :
    PresheafPFunctor.{max uI uD, uJ, uA, max uI uD, vI, vJ} (ElObj.{uI, uD, vI} D) J
```

It decomposes as `sigmaPsh (decPresheaf A hA D) ∘ adjoinArity F …`, where

- `decPresheaf A hA D` is the decoding presheaf on `J`: at the output
  object `b` it is the set `PshMor (A.fam b) D` of natural transformations
  from the arity at `b` into `D`, reindexed by precomposition with
  `A.reindex`;
- `adjoinArity` adjoins to every shape of `F` the fibre arity of its
  decoding — the directions `{(y, x) : y : ElObj D, x : (A.fam b).Dir y.1,
  s.app x = y.2}` — leaving the shapes untouched;
- `sigmaPsh` takes the coproduct over the decodings, pushing the functor
  forward along the projection `ElObj (decPresheaf A hA D) → J`.

The value at a presheaf `Z` on `ElObj D` and an output object `b`:

```text
⟦δ A hA D F⟧ Z b = Σ (s : PshMor (A.fam b) D), ⟦F⟧ Z ⟨b, s⟩
```

The worked example `GebProto.deltaVaries` is a `δ` over the walking arrow
whose arity is empty over `0` and inhabited over `1`: an arity genuinely
varying over the output object, which no family-level rule can express.

## What distinguishes the presheaf `δ`

- **Output-varying arity.** In every rule above the direction set is a
  constant set (`A` or `P`). Here the directions form a presheaf on the
  input category varying over the output objects (`BaseArity I J`). This
  has no counterpart in [DybjerSetzer1999], [DybjerSetzer2003],
  [DybjerSetzer2006], or [HancockMcBrideGhaniMalatestaAltenkirch2013].
- **Natural decodings.** The family-level decodings are plain functions
  (`A → D`, sections `(p : P) → D (i p)`, `A → C`); in those settings
  naturality is vacuous — [GhaniNordvallForsbergMalatesta2015]
  Remark 2.3: "the naturality condition in the definition of a morphism
  of families is vacuous as the domains of the functors in question are
  discrete". Here a decoding is a natural transformation `PshMor (A.fam
  b) D`, and the load is real: `GebProto.fibreArity`'s functoriality uses
  `s.naturality`, so a bare family of decodings would not close under
  restriction.
- **Mutuality-free continuation.** Where
  [GhaniNordvallForsbergMalatesta2015] Section 3 buys functorial
  dependence on the decoding with an inductive-inductive definition of
  codes and morphisms, the presheaf `δ` takes one continuation over the
  category of elements of the decoding presheaf, so the codes remain an
  ordinary W-type (`GebProto.codePFunctor` over `Cat`).
- **Presheaf semantics.** The interpretation lands in presheaf p.r.a.
  functors `PSh(ElObj D) → PSh(J)` — functors of the p.r.a. form of
  [Weber2007] — rather than in `Fam(C)`.

## Sources examined

- [DybjerSetzer1999] P. Dybjer, A. Setzer, A Finite Axiomatization of
  Inductive-Recursive Definitions, TLCA 1999, LNCS 1581, 129–146.
- [DybjerSetzer2003] P. Dybjer, A. Setzer, Induction–recursion and
  initial algebras, Annals of Pure and Applied Logic 124 (2003) 1–47.
- [DybjerSetzer2006] P. Dybjer, A. Setzer, Indexed induction-recursion,
  Journal of Logic and Algebraic Programming 66 (2006) 1–49. Not yet an
  entry in `docs/references.bib`; the attribution of the IIR `δ` rule
  above follows the account in [HancockMcBrideGhaniMalatestaAltenkirch2013]
  Section 6.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] P. Hancock, C. McBride,
  N. Ghani, L. Malatesta, T. Altenkirch, Small Induction Recursion,
  TLCA 2013, LNCS 7941, 156–172. Verified against the authors' extended
  preprint (<https://personal.cis.strath.ac.uk/conor.mcbride/pub/SmallIR/SmallIR.pdf>)
  and its literate Agda source
  (<https://personal.cis.strath.ac.uk/conor.mcbride/pub/SmallIR/SmallIR.lagda>).
- [GhaniNordvallForsbergMalatesta2015] N. Ghani, L. Malatesta,
  F. Nordvall Forsberg, Positive Inductive-Recursive Definitions, LMCS
  11(1:13), 2015, arXiv:1502.05561 (full text checked: Definitions 2.1,
  2.2, Theorem 2.4, Remarks 2.3, Section 3).
- [AltenkirchGhaniHancockMcBrideMorris2015] T. Altenkirch, N. Ghani,
  P. Hancock, C. McBride, P. Morris, Indexed containers, JFP 25:e5,
  2015. Indexed containers over families `I → Set`; no presheaf setting
  and no `δ` combinator.
- [Weber2007] M. Weber, Familial 2-functors and parametric right
  adjoints, TAC 18(22), 665–732 (full text checked). The p.r.a. theory
  and generic morphisms; the `δ` used there is the generic-morphism
  filler, not a code constructor.
- [GambinoKock2013] N. Gambino, J. Kock, Polynomial functors and
  polynomial monads, Math. Proc. Camb. Phil. Soc. 154 (2013) 153–192,
  arXiv:0906.4931 (full text checked). Polynomials over a category and
  their functors between presheaf categories — the p.r.a. side — with no
  code system.

## Assessment

The building blocks are standard: presheaf p.r.a. / polynomial functors
([Weber2007], [GambinoKock2013]), categories of elements, the family-level
and IIR `δ` rules ([DybjerSetzer1999], [DybjerSetzer2003],
[DybjerSetzer2006], [HancockMcBrideGhaniMalatestaAltenkirch2013],
[GhaniNordvallForsbergMalatesta2015]), and W-type constructions in
presheaf categories (Moerdijk–Palmgren, Wellfounded trees in categories,
APAL 104 (2000) 189–218 — initial algebras for single polynomial
endofunctors, not a code system).

None of the sources examined combines an inductive-recursive code system
with presheaf semantics, an output-varying arity, or natural decodings.
The closest precedent, [GhaniNordvallForsbergMalatesta2015] Section 3,
differs on all three counts and additionally pays for functoriality with
an inductive-inductive code-and-morphism definition that the presheaf
rule avoids. The claim is therefore that the presheaf p.r.a. `δ` of
`GebProto.delta` is new as a code constructor; the claim does not extend
to its constituents, all of which are standard.

## Limits of this review

- The TLCA 2013 proceedings PDF is paywalled; the verification used the
  authors' extended preprint, the URL of which `docs/references.bib`
  already records. `TODO.md` records the proceedings-to-preprint
  numbering correspondence (the proceedings' Corollary 4 is the
  preprint's Corollary 22, the IIR–Poly equivalence), which places the
  IIR material in the proceedings as well; the proceedings' Section 6
  was not itself inspected.
- The review is not exhaustive: arXiv metadata searches plus the full
  texts of the two most relevant category-theory papers ([Weber2007],
  [GambinoKock2013]) and of the IR-code papers listed. Adjacent lines —
  fibrational induction, generic containers, 2-dimensional monad theory,
  theses, workshop proceedings — were not searched exhaustively.
- The claim concerns the rule as constructed in `Codes.lean`, whose
  closed instance computes (`interp_deltaCodeVaries` holds by `rfl`).
  The repository does not yet establish the structural results that
  would complete the mathematical picture; see the next section.

## Open points in the repository

- The presheaf-level regrouping — the analogue of Lemma 3 of
  [HancockMcBrideGhaniMalatestaAltenkirch2013], stated in the `delta`
  docstring as `Σ_{g : P → X} ⟦F (f ∘ g)⟧ = Σ_{d : P → D} (sections of f
  over d) × ⟦F d⟧` — is stated and not proved.
- The embedding of the constant-arity IIR rule as a special case of the
  presheaf rule is not proved (`decArity`'s docstring records that the
  properness of the generalization of Section 6's constant arity is not
  established).
- Initial algebras for interpreted endofunctors (the presheaf analogue
  of Theorem 2.4's semantics and of the `IR I I` initiality) are future
  work; see `TODO.md` § Complete Theorem 2.4 for `IndRec` and § Theorems
  2 and 4 for `IR` codes.
- If this note is adopted, add a `DybjerSetzer2006` entry to
  `docs/references.bib`.

## Suggested wording

If the claim is adopted, a module-docstring or paper sentence along
these lines, with the caveats above:

> `GebProto.delta` is the presheaf p.r.a. reading of the `δ` rule of
> Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013], generalized
> in two directions that, to the best of our knowledge and the sources
> examined, have no precedent: the direction set becomes an arity that
> varies over the output object, and the decodings become natural
> transformations into a decoding presheaf, the continuation being a
> single code over the category of elements of that presheaf rather than
> a family of codes indexed by decodings. The closest precedent,
> [GhaniNordvallForsbergMalatesta2015] Section 3, keeps a constant
> direction set and non-natural decodings and requires an
> inductive-inductive definition of codes and morphisms; here the codes
> are an ordinary W-type over `Cat`.
