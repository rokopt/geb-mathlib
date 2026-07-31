# Codes for presheaf parametric-right-adjoint functors

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Scope of this document](#scope-of-this-document)
- [Motivation](#motivation)
- [Stage 1: morphisms and the representation theorem](#stage-1-morphisms-and-the-representation-theorem)
- [Stage 2: the code system](#stage-2-the-code-system)
  - [The setting is indexed induction-recursion, not induction-recursion](#the-setting-is-indexed-induction-recursion-not-induction-recursion)
  - [The three rules and their semantics](#the-three-rules-and-their-semantics)
  - [Why `δ`'s arity must vary over the shape presheaf](#why-%CE%B4s-arity-must-vary-over-the-shape-presheaf)
  - [Why no inductive-inductive definition is needed](#why-no-inductive-inductive-definition-is-needed)
- [Definitions: transcription or novel](#definitions-transcription-or-novel)
- [Proof obligations](#proof-obligations)
- [Open questions](#open-questions)
- [Non-goals](#non-goals)
- [Notes](#notes)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope of this document

This specifies a workstream on morphisms of presheaf parametric-right-adjoint
functors and on codes denoting them, in two stages. Stage 1 is settled and
machine-checked. Stage 2 is elaborated far enough that its shape is fixed and
its central obstruction is proved, but its completeness and its morphism theory
remain open.

The prototype at `Geb/Internal/PresheafIRProto/` is the source this document
transcribes. It compiles, is linted, and is audited by
`GebMeta.detectNonstandardAxiom`; every declaration cited below is
`Classical.choice`-free except where noted. Where this document and the
prototype disagree, the prototype is right. Claims marked *inference* are not
elaborated there; every other claim names the declaration that establishes it.

The prototype is not deliverable content. It is removed with this spec and the
plan, together with the `Geb.Internal.PresheafIRProto.Functor` entry in
`GebMeta.classicalAllowedModules`.

## Motivation

The repository's existing code system, `IndRec.IR I O`, denotes functors
between free coproduct completions of discrete index types. Its interpretation
is a functor `Fam(I) ⥤ Fam(O)`. Two capabilities it lacks motivate the
generalisation to presheaf bases:

- Only one of the two index sets varies under iteration. In the endofunctor
  case the initial algebra generates a type together with a decoding into a
  *fixed* type. A presheaf on the walking arrow is a function between two sets,
  so an endofunctor there varies both sets and the map between them at once —
  which is what an inductive-inductive definition is.
- Full and faithfulness of the interpretation is not available over `Fam(C)`.
  Section 2 of [GhaniNordvallForsbergMalatesta2015] records that the
  characterization of the `δ` interpretation as a left Kan extension fails for
  non-discrete `C`, and lists recovering it as an open problem. Remark 3.4 of
  the same paper offers the alternative — morphisms `Hom(x,y) = ⟦x⟧ → ⟦y⟧`,
  full and faithful by definition — at the cost of defining `⟦−⟧`
  simultaneously with the codes.

Stage 1 obtains full and faithfulness structurally instead, from the fact that
a presheaf p.r.a. functor's interpretation is by construction a coproduct of
representables.

## Stage 1: morphisms and the representation theorem

Settled. `Geb/Internal/PresheafIRProto/Basic.lean` carries it, choice-free;
`Functor.lean` carries the bundled restatement, which writes `⟶` between
objects of a presheaf category and so depends on `Classical.choice` through
`CategoryTheory.Functor.category`.

| Declaration | Content |
| --- | --- |
| `shapePresheaf`, `arityPresheaf` | the shape presheaf `T₁` and each arity `E(a)`, as functors |
| `ArityHom` | the unbundled presheaf hom `E(a) ⟶ Z` |
| `objEquivSigmaArityHom` | the interpretation is a coproduct of representables, at arbitrary `uZ` |
| `DomHom`, `domHomEquivNatFamily` | the representation theorem, domain level |
| `ShapeHom`, `PshHom` | the morphism type: shape map forward, arity maps backward, `reindexCompat` |
| `pshHomFib_objFibRestr` | the action commutes with the `J`-restriction |
| `pshHomEquivNatFamily` | the representation theorem in full |

Four facts follow, each backed by a declaration:

1. Natural transformations between presheaf p.r.a. functors are classified by
   shape-map-forward and arity-map-backward data (`pshHomEquivNatFamily`). Full
   and faithfulness is definitional rather than a theorem to be hoped for.
2. The classification is available because the interpretation is a coproduct of
   representables (`objEquivSigmaArityHom`), not because of any property of the
   ambient category: Yoneda holds in any locally small category.
3. Unbundling buys constructivity and universe polymorphism together.
   `objEquivSigmaArityHom` holds at arbitrary `uZ`; its bundled wrapper
   `objEquivSigmaHom` is pinned to `uZ := uB`. Both restrictions come from
   requiring the arity presheaf and the input presheaf to lie in one functor
   category, which is what `⟶` demands and what draws in `Classical.choice`.
4. `PresheafPFunctorData` already is the familial presentation in unbundled
   form. `shapeRestr` gives `T₁` its presheaf structure, `directionRestr` gives
   each `E(a)` its own, and `ReindexNaturality` says exactly that
   `reindex g a : E(shapeRestr g a) ⟶ E(a)` is a presheaf morphism.

## Stage 2: the code system

`Geb/Internal/PresheafIRProto/Codes.lean` carries it, choice-free.

### The setting is indexed induction-recursion, not induction-recursion

`IR I O` collapses two roles that Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013] keeps apart. In
`IR.delta B (c : (B → I) → IR I O)` the map `B → I` is simultaneously the
arity's index-labelling and the decoding of the recursive arguments; in that
paper's `IIR D E` the labelling `i : P → I` is fixed data and the subcodes are
indexed by the decodings `(p : P) → D (i p)`.

The presheaf setting forces the split. A `δ` whose arity is a bare set `B`
labelled by `ℓ : B → I` admits no `directionRestr`: `Direction a i` is the
fibre of `ℓ` over `i`, and for `f : i′ ⟶ i` that fibre can be inhabited over
`i` while empty over `i′`. The labelling must therefore be code data, and the
arity must carry presheaf structure. So the presheaf system generalises `IIR`,
not `IR`.

*Inference, not elaborated.* The semantic counterpart of that split is the
equivalence `PSh(𝕀)/D ≃ PSh(el D)`: `IIR D E` interprets into
`Set/ΣD → Set/ΣE`, and the presheaf analogue of the total-space collapse needs
the category of elements rather than a bare `Σ`. Consequently a presheaf-`IIR`
code over `(𝕀, D)`, `(𝕁, E)` denotes an ordinary
`PresheafPFunctor (el D) (el E)`, and the code system's semantics needs no
notion beyond Stage 1's. The prototype uses the category of elements as a base
category (`ElObj`, `elCategory`) but does not construct that equivalence; in
mathlib it is the composite of `overEquivPresheafCostructuredArrow` and
`CategoryOfElements.costructuredArrowYonedaEquivalence`, and the exploratory
repository has it directly as `sliceEquivCopresheaf`.

### The three rules and their semantics

A code is indexed by the base category it denotes a functor into. The
constructors, with the semantic operation each folds to:

| Rule | Code constructor | Semantics |
| --- | --- | --- |
| `ι` | `iotaCode 𝔹` | `unitPsh` — terminal shape presheaf, no directions |
| `σ` | `sigmaCode 𝔹 S K` | `sigmaPsh S` — push a functor over `ElObj S` forward to `𝔹` |
| `δ` | `deltaCode 𝔹 P hP K` | `delta` at `BaseArity.pullback P` — adjoin the arity `P` |

`σ`'s subcode sits over the category of elements of `S`, so the base changes;
`δ`'s sits over the same base. The interpretation is `interp`, the fold of
`codeAlg` over the W-type; its three computation rules `interp_iotaCode`,
`interp_sigmaCode` and `interp_deltaCode` are definitional, and `interp_fst`
records that a code's index is the base its interpretation lands in.

Each semantic operation is a `PresheafPFunctor` — that is, all seven functor
laws are proved, not assumed: `coprod` (the coproduct of a family, used for a
`σ` over a bare type), `delta`, `unitPsh` and `sigmaPsh`.

### Why `δ`'s arity must vary over the shape presheaf

This is the design's load-bearing negative result, and the reason the naive
lift of `ι` / `σ` / `δ` does not work.

- `HasBijectiveReindex F` says every reindexing map of `F` is a bijection.
- It holds of `iotaPresheaf` and `iotaConst`
  (`hasBijectiveReindex_iotaPresheaf`, `hasBijectiveReindex_iotaConst`), is
  inherited by coproducts (`hasBijectiveReindex_coprod`), and is inherited by a
  `δ` exactly when the adjoined arity's own reindexing is bijective
  (`hasBijectiveReindex_delta`) — in particular by a `δ` at a *constant* arity,
  whose reindexing is the identity (`hasBijectiveReindex_deltaConst`).
- `arityVaries`, a functor over the walking arrow whose shape presheaf is
  terminal and whose arity is inhabited over `1` and empty over `0`, does not
  satisfy it (`not_hasBijectiveReindex_arityVaries`).

So the presheaf reading of the rules of
[HancockMcBrideGhaniMalatestaAltenkirch2013] Section 6, whose `δ` arity is an
object of `Set/I` and carries no dependence on the output object, cannot denote
`arityVaries`. The repair is `ShapeArity`: an arity varying over the shape
presheaf, which is the unbundled data of a functor `el(T₁)ᵒᵖ ⥤ (Iᵒᵖ ⥤ Type)`.
`deltaVarying` is the `δ` at such an arity reaching `arityVaries`'s, and
`not_hasBijectiveReindex_deltaVarying` records that it lies outside the bound.

**The result is syntactic.** It bounds what the constructions produce on the
nose, not up to isomorphism of the interpreted functors. Transporting
`HasBijectiveReindex` along an isomorphism follows from
`pshHomEquivNatFamily`, but needs identities and composition on `PshHom`, which
the prototype does not build. Closing that gap is proof obligation 4.

### Why no inductive-inductive definition is needed

A code's `δ` cannot mention its subcode's shapes, so its arity is indexed by
output objects (`BaseArity`) and pulled back along the shape-output map
(`BaseArity.pullback`, `BaseArity.isFunctorial_pullback`). The transport that
the pullback carries is the reason `ShapeArity` is indexed by shapes rather
than by output objects: `deltaData` is then free of it.

The code type is the W-type of a slice polynomial functor on `Cat`
(`codePFunctor`, `Code`), not an inductive family. `Cat.{v, u}` is closed under
the step `σ` takes, because the category of elements of a presheaf valued in
`Type u` over a base in `Type u` is again in `Type u`, with homs a subtype of
the base's. The index is therefore an ordinary parameter, and nothing is
defined simultaneously with anything else. This answers negatively the question
of whether codes must be encoded to work around Lean's lack of
inductive-inductive types, and it avoids the route Remark 3.4 of
[GhaniNordvallForsbergMalatesta2015] describes and declines.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing.

| Definition | Status |
| --- | --- |
| `PresheafPFunctor.Hom` (Stage 1's `PshHom`) | Novel in this repository. The shapes-forward arities-backward form is Definition 7 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (morphisms of indexed containers) in the discrete case; its Definition 6 is the dependent-polynomial presentation whose `r`/`q` naming this repository follows |
| The action of a `Hom`, and its naturality | Novel |
| The representation theorem | Novel at this level; the discrete analogue is Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013], present as `IR.interpHomEquiv` |
| Identity, composition, and the category structure on `Hom` | Novel |
| The `ι` / `σ` / `δ` code rules | Transcription of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013], generalized from families to presheaves. The generalization of `δ`'s arity from an object of `Set/I` to one varying over the shape presheaf is novel, and § Why `δ`'s arity must vary shows it is forced |
| Indexing the code type by a base category, with `σ` replacing it by a category of elements | Novel |
| The coproduct, unit, base-change and arity-adjoining operations on `PresheafPFunctor` | Novel at this level; the discrete analogues are `SlicePFunctor.coprod`, `SlicePFunctor.representable` and `SlicePFunctor.prodSlice` |

## Proof obligations

Each is unproved at the time of writing. Ordered by dependency.

1. **Stage 1 at upstream quality.** Port `PshHom`, its action, and
   `pshHomEquivNatFamily` from the prototype into `Geb/Mathlib/`, against the
   choice-free `objPresheaf` and `mapPresheaf` rather than
   `PresheafPFunctor.functor`. The `functor` form is a corollary and belongs in
   a module on `GebMeta.classicalAllowedModules`.
2. **Category structure.** That `PshHom` has identities and composition, that
   composition is associative with those identities as units, and that the
   equivalence of obligation 1 carries them to the identities and composition
   of natural transformations.
3. **Stage 2 at upstream quality.** Port the four operations, the code type and
   the interpretation. The prototype's `ElObj` / `elCategory` is written out
   rather than reused; the upstream version should be `S.Elementsᵒᵖ`, and the
   `Opposite` transport that reuse costs is to be measured, not assumed
   tolerable.
4. **Iso-invariance of the bound.** That `HasBijectiveReindex` transports along
   an isomorphism of interpreted functors, upgrading
   `not_hasBijectiveReindex_arityVaries` from a syntactic to a semantic
   statement. Depends on obligation 2.
5. **Completeness.** Whether every `PresheafPFunctor` has a code — the analogue
   of Lemma 1 of [HancockMcBrideGhaniMalatestaAltenkirch2013]. The shape of the
   expected witness is `sigmaCode` at the shape presheaf over a `deltaCode` at
   the arity over `iotaCode`; that this reconstructs an arbitrary functor is
   conjecture, not elaboration.
6. **Code morphisms.** The code-level morphism type, mirroring `PshHom`, and
   the code-level representation theorem, the analogue of
   `pshHomEquivNatFamily`. Stage 1 determines the shape of both.

## Open questions

Not blocking, and to be answered by the work rather than before it.

1. Whether the `(𝕀, D)` presentation — codes parameterized by a base category
   and a decoding presheaf, interpreting into `PresheafPFunctor (el D) (el E)`
   — should be built as a layer over the base-category presentation, or left as
   the observation that the latter subsumes it at `el D`.
2. Whether the arity carrier universe, pinned to the base's in the prototype,
   needs to vary.
3. Whether `iotaPresheaf j₀` and `iotaConst (yoneda.obj j₀)` are isomorphic as
   functors. Their shape types agree definitionally
   (`iotaConst`'s section, `Basic.lean`); nothing more is established.
4. Whether the walking arrow should be a worked example, exercising
   `shapeRestr`, `reindex` and `reindexCompat` non-trivially while staying
   small enough to compute with by hand. `arityVaries` is already a
   `PresheafPFunctor (Fin 1) (Fin 2)` over it.
5. Whether `PresheafPFunctor` at discrete `I` and `J` carries information
   beyond `SlicePFunctor`, and whether the code system degenerates to `IR`
   there.

## Non-goals

- Positive inductive-recursive definitions over `Fam(C)`
  ([GhaniNordvallForsbergMalatesta2015]). They meet the full-and-faithfulness
  requirement only by Remark 3.4's route, defining the interpretation
  simultaneously with the codes; the presheaf setting reaches it structurally.
  If wanted they are better recovered inside the presheaf construction,
  `Fam(C)` embedding in presheaves as the coproducts of representables.
- Initial algebras of the interpreted functors. `IR`'s are not constructed
  either; the set-theoretic model of [DybjerSetzer2003] justifies their
  existence using a Mahlo cardinal.
- Uniqueness of the interpretation fold. `Geb/Mathlib/Data/PFunctor/Slice/W.lean`
  establishes only the existence half of the initial-algebra universal
  property, and this workstream inherits that.

## Notes

`docs/references.bib` has the author order of
`GhaniNordvallForsbergMalatesta2015` wrong. The published LMCS byline is Ghani,
Malatesta, Nordvall Forsberg; the entry and the citation key both encode the
arXiv preprint's order. Pre-existing, used by seven files, deferred to its own
branch per one concern per branch.

## References

- [GhaniNordvallForsbergMalatesta2015] — positive inductive-recursive
  definitions; Remark 3.4 on the choice of morphism collection, and Section 2
  on the loss of full and faithfulness over `Fam(C)`.
- [GhaniMalatestaNordvallForsberg2014Agda] — its Agda formalization.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] — small induction recursion;
  Section 6 for `IIR`, Definition 6 for morphisms of dependent polynomials,
  Definition 7 for morphisms of indexed containers, Theorem 3 for the discrete
  representation theorem, Lemma 1 for completeness.
- [Weber2007], [nLabParametricRightAdjoint] — parametric right adjoints and
  familial functors.
- [SpivakGarnerFairbanks2021], [Shapiro2021] — parametric right adjoints
  between presheaf categories.
- [AltenkirchGhaniHancockMcBrideMorris2015] — indexed containers.
- [DybjerSetzer1999], [DybjerSetzer2003] — inductive-recursive definitions.
