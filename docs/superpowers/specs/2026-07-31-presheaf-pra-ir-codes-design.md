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
- [Branches](#branches)
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
its obstruction is reduced to a one-step induction whose base and step cases
are proved; its recursion, its completeness and its morphism theory remain
open.

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
generalization to presheaf bases:

- Only one of the two index sets varies under iteration. In the endofunctor
  case the initial algebra generates a type together with a decoding into a
  *fixed* type. A presheaf on the walking arrow is a function between two sets,
  so an endofunctor there varies both sets and the map between them at once —
  which is what an inductive-inductive definition is.
- Full and faithfulness of the interpretation is not available over `Fam(C)`.
  Section 2 of [GhaniNordvallForsbergMalatesta2015] records that the
  characterization of the `δ` interpretation as a left Kan extension fails for
  non-discrete `C`; its Conclusions and Future Work section lists recovering
  that characterization as future work, and separately records as an open
  problem whether the definable functors are closed under composition. Remark
  3.4 of
  the same paper offers the alternative — morphisms `Hom(x,y) = ⟦x⟧ → ⟦y⟧`,
  full and faithful by definition — at the cost of defining `⟦−⟧`
  simultaneously with the codes.

Stage 1 puts full and faithfulness within reach structurally instead, from the
fact that a presheaf p.r.a. functor's interpretation is by construction a
coproduct of representables. What it delivers is the hom-set bijection;
obligations 2 and 3 carry that to full and faithfulness.

## Stage 1: morphisms and the representation theorem

Settled up to the two identifications recorded as obligations 2 and 3.
`Geb/Internal/PresheafIRProto/Basic.lean` carries it, choice-free;
`Functor.lean` carries what depends on `Classical.choice` through
`CategoryTheory.Functor.category`: the bundled restatement, which writes `⟶`
between objects of a presheaf category, and
`iotaPresheafData_A_eq_iotaConstData_yoneda`, whose `yoneda` lands in a functor
category.

| Declaration | Content |
| --- | --- |
| `shapePresheaf`, `arityPresheaf` | the shape presheaf `T₁` and each arity `E(a)`, as functors |
| `ArityHom` | the unbundled presheaf hom `E(a) ⟶ Z` |
| `objEquivSigmaArityHom` | the interpretation is a coproduct of representables, at arbitrary `uZ` |
| `DomHom`, `domHomEquivNatFamily` | the representation theorem, domain level |
| `ShapeHom`, `PshHom` | the morphism type: shape map forward, arity maps backward, `reindexCompat` |
| `idPshHom` | the identity morphism, `reindexCompat` included |
| `pshHomFib_objFibRestr` | the action commutes with the `J`-restriction |
| `pshHomEquivNatFamily` | the representation theorem in full |

Four facts follow. The first and third name the declarations that establish
them; the second and fourth are readings of the construction, backed by
structure fields rather than by theorems:

1. Shape-map-forward and arity-map-backward data classify the natural families
   between presheaf p.r.a. functors: `pshHomEquivNatFamily` is a bijection
   `PshHom F F' ≃ PshNatFamily F F'`. It is not definitional — its round-trip
   laws rest on `natFamily_generic`, `natFamilyPshHom`,
   `objFibMap_eq_objFibRestr_apply` and `natFamilyArity_pshHomFamily`. Two
   steps separate it from full and faithfulness of the interpretation, both
   obligations rather than results: `PshNatFamily` is an unbundled proxy and is
   nowhere related to `PresheafPFunctor.functor`'s natural transformations
   (obligation 3), and fullness and faithfulness are properties of a functor,
   so they need composition on `PshHom` carried across the bijection
   (obligation 2).
2. The classification is available because the interpretation is a coproduct of
   representables (`objEquivSigmaArityHom`), not because of any property of the
   ambient category: Yoneda holds in any locally small category.
3. Unbundling yields constructivity and universe polymorphism together.
   `objEquivSigmaArityHom` holds at arbitrary `uZ`; its bundled wrapper
   `objEquivSigmaHom` is pinned to `uZ := uB`. Both restrictions come from
   requiring the arity presheaf and the input presheaf to lie in one functor
   category, which is what `⟶` demands and what introduces `Classical.choice`.
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

The presheaf setting forces the split. The following paragraph is an
inference, not elaborated: a `δ`
whose arity is a bare set `B` labelled by `ℓ : B → I` admits no
`directionRestr`: `Direction a i` is the
fibre of `ℓ` over `i`, and for `f : i′ ⟶ i` that fibre can be inhabited over
`i` while empty over `i′`. The labelling must therefore be code data, and the
arity must carry presheaf structure — which is the separation `IIR` makes and
`IR` does not.

The prototype builds only the layer in which the decoding presheaf is terminal.
There `δ`'s subcode family, indexed in Section 6 by the decodings
`(p : P) → D (i p)`, is a singleton, and `deltaCode` accordingly carries a
single continuation over the same base. That layer has no recursion: nothing in
it lets a continuation depend on a decoding. Supplying the decoding presheaf —
codes over `(𝕀, D)` and `(𝕁, E)`, with `δ`'s subcodes indexed by presheaf
morphisms `P ⟶ D` — is what makes the system inductive-*recursive*, and is
obligation 8. Until it lands, what the prototype denotes are presheaf indexed
containers with a varying arity.

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

`Code` is a single unindexed type, fibred over `Cat` by the projection
`codePFunctor.wIndex`; each constructor with a subcode takes an explicit
hypothesis `hK` aligning that subcode's fibre with the slot it fills. The
constructors, with the semantic operation each folds to:

| Rule | Code constructor | Semantics |
| --- | --- | --- |
| `ι` | `iotaCode 𝔹` | `unitPsh` — terminal shape presheaf, no directions |
| `σ` | `sigmaCode 𝔹 S K (hK : wIndex K = Cat.of (ElObj S))` | `sigmaPsh S` — push a functor over `ElObj S` forward to `𝔹` |
| `δ` | `deltaCode 𝔹 P hP K (hK : wIndex K = 𝔹)` | `delta` at `BaseArity.pullback P` — adjoin the arity `P` |

`σ`'s subcode sits over the category of elements of `S`, so the base changes;
`δ`'s sits over the same base. The interpretation is `interp`, the fold of
`codeAlg` over the W-type; its three computation rules `interp_iotaCode`,
`interp_sigmaCode` and `interp_deltaCode` are definitional, and `interp_fst`
records that a code's index is the base its interpretation lands in.

Each of the three semantic operations is a `PresheafPFunctor` — that is, all
seven functor laws are proved, not assumed: `unitPsh`, `sigmaPsh` and `delta`.
The prototype also carries `coprod`, the coproduct of a type-indexed family,
likewise with all seven laws; the code system does not use it, and it appears
only as the `σ` of the rejected fragment in § Why `δ`'s arity must vary.

### Why `δ`'s arity must vary over the shape presheaf

This is the negative result the design rests on, and the reason the
constant-arity reading of `ι` / `σ` / `δ` does not suffice.

- `HasBijectiveReindex F` says every reindexing map of `F` is a bijection.
- It holds of `iotaPresheaf` and `iotaConst`
  (`hasBijectiveReindex_iotaPresheaf`, `hasBijectiveReindex_iotaConst`), is
  inherited by coproducts (`hasBijectiveReindex_coprod`), by the `σ` base
  change (`hasBijectiveReindex_sigmaPsh`), and by the unit
  (`hasBijectiveReindex_unitPsh`); and a `δ` inherits it from the adjoined
  arity's own reindexing together with the subfunctor's
  (`hasBijectiveReindex_delta` requires both), in particular from a constant
  arity, whose reindexing is the identity (`hasBijectiveReindex_deltaConst`).
  Only that direction is proved; the converse is not used.
- `arityVaries`, a functor whose output base is the walking arrow, whose shape
  presheaf is terminal and whose arity is inhabited over `1` and empty over
  `0`, does not satisfy it (`not_hasBijectiveReindex_arityVaries`).

Call the *constant-arity fragment* the codes generated by `unitPsh`,
`iotaPresheaf`, `iotaConst`, `coprod`, `sigmaPsh` and `δ` at a constant arity —
that is, the presheaf reading of the rules of
[HancockMcBrideGhaniMalatestaAltenkirch2013] Section 6, whose `δ` arity is an
object of `Set/I` and so carries no dependence on the output object.
`hasBijectiveReindex_unitPsh`, `_iotaPresheaf` and `_iotaConst` are its base
cases; `_coprod`, `_sigmaPsh` and `_deltaConst` are its step cases. Together
they cover every generator and every operation of that fragment.

*Inference, not elaborated.* That the fragment therefore cannot denote
`arityVaries` is a one-step induction over its codes. The prototype does not
formalize it: it builds a code type for the adopted rules only, so there is
no code type for the fragment to induct over. Formalizing it is obligation 7.

The replacement is `ShapeArity`: an arity varying over the shape
presheaf, which is the unbundled data of a functor `el(T₁)ᵒᵖ ⥤ (Iᵒᵖ ⥤ Type)`.
`deltaVarying` is the `δ` carrying `arityVaries`'s arity, and
`not_hasBijectiveReindex_deltaVarying` records that it lies outside the bound.
It is not isomorphic to `arityVaries` on the nose — its directions are
`arityB a ⊕ PEmpty` — and no isomorphism is constructed.

The result is syntactic: it bounds what the constructions produce on the
nose, not up to isomorphism of the interpreted functors. Obligation 6 expects
to derive the transport of `HasBijectiveReindex` along an isomorphism from
`pshHomEquivNatFamily`, but needs composition on `PshHom`, which the prototype
does not build (`idPshHom` supplies the identity). That is proof obligation 2.

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
the base's. The fibre is therefore recovered by a projection out of an
ordinary W-type, and nothing is defined simultaneously with anything else. This
answers negatively the question of whether codes must be encoded to work
around Lean's lack of
inductive-inductive types, and it avoids the route Remark 3.4 of
[GhaniNordvallForsbergMalatesta2015] describes and declines.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing.

| Definition | Status |
| --- | --- |
| `PshHom`, to be named `PresheafPFunctor.Hom` upstream | Novel in this repository. The shapes-forward arities-backward form is Definition 7 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (morphisms of indexed containers) in the discrete case; its Definition 6 is the dependent-polynomial presentation whose `r`/`q` naming this repository follows |
| The action of a `Hom`, and its naturality | Novel |
| The representation theorem (`pshHomEquivNatFamily`) | Novel at this level. Its discrete analogue is Theorem 1 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (that paper's restatement of Theorem 2.12 of [GambinoKock2013]), together with Definition 7 for the indexed-container form. Theorem 3 of the same paper is the code-level statement, present as `IR.interpHomEquiv`, and is the analogue of proof obligation 10, not of this |
| Identity, composition, and the category structure on `Hom` | Novel |
| The `σ` / `δ` code rules | Transcription of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013], generalized from families to presheaves. The generalization of `δ`'s arity from an object of `Set/I` to one varying over the shape presheaf is novel, and § Why `δ`'s arity must vary shows it is forced |
| The `ι` code rule | Novel. Section 6's `ι` takes a point of the output total space `ΣE`; `iotaCode 𝔹` takes none and denotes `unitPsh`, one shape over every object of `𝔹`. The pointed form exists in the prototype as `iotaPresheaf j₀` but is not what the code system uses, and that `σ` at a representable over `iotaCode` recovers it is unelaborated |
| Indexing the code type by a base category, with `σ` replacing it by a category of elements | Novel |
| `coprod`, the coproduct of a type-indexed family | Novel at this level; the discrete analogue is `SlicePFunctor.coprod` |
| `unitPsh`, the unit | Novel at this level; the discrete analogue is `SlicePFunctor.representable` at the empty direction type |
| `delta`, adjoining an arity | Novel at this level; the discrete analogue is `SlicePFunctor.prodSlice` against a representable |
| `sigmaPsh`, the base change along `ElObj S → J` | Novel. It has no discrete analogue in this repository: over a discrete base the category of elements is discrete and the base change collapses into `SlicePFunctor.coprod` |
| `DomArity` — a presheaf on `I`, unbundled | Novel presentation of a standard object, chosen so its directions plug into a `PresheafPFunctorData`'s without transport |
| `ShapeArity`, `ShapeArity.const` — the arity a `δ` adjoins, varying over the shape presheaf | Novel; it is the unbundled data of a functor `el(T₁)ᵒᵖ ⥤ (Iᵒᵖ ⥤ Type)`. `const` is the case Section 6's `δ` arity occupies |
| `BaseArity`, `BaseArity.pullback` — the arity indexed by output objects, and its pullback along `q` | Novel |
| `ElObj`, `elCategory` — the category of elements as a base category | Transcription. It is `S.Elementsᵒᵖ`, written out to avoid `Opposite` transport; obligation 4 revisits the choice |
| `HasBijectiveReindex` | Novel; it is the property that the interpretation's fibres are cartesian over the shape presheaf |
| `CodeShape`, `CodeDir`, `CodeNext`, `codePFunctor`, `Code` | Novel. Indexing by a base category, with `σ` replacing it by a category of elements, has no counterpart in the cited literature |
| `codeAlgOn`, `codeAlg`, `interp` — the interpretation | Novel at this level; the discrete analogue is `IR.interpObj` |
| The constant-arity fragment's code type (obligation 7) | Novel |
| The code-level morphism type (obligation 10) | Novel at this level; the discrete analogue is `IndRec.IR.Hom` |

## Branches

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape binds one concern
per branch. The obligations below divide into six.

| Branch | Obligations | Acceptance |
| --- | --- | --- |
| W-a — Stage 1 upstream | 1, 2, 3 | `PshHom`, its action and the hom-set bijection in `Geb/Mathlib/`, choice-free; composition and the category structure; and the bijection related to natural transformations of the interpreted functors |
| W-c — Stage 2 upstream | 4, 5 | the four operations, the code type, the interpretation, and the bound's vocabulary in `Geb/Mathlib/` |
| W-b — the bound | 6, 7 | `HasBijectiveReindex` transports along an isomorphism, and the constant-arity fragment's induction is formalized against a code type for that fragment |
| W-d — the decoding layer | 8 | codes over `(𝕀, D)` and `(𝕁, E)`, with `δ`'s subcodes indexed by presheaf morphisms `P ⟶ D`, interpreting into `PresheafPFunctor (el D) (el E)` |
| W-e — completeness | 9 | either a code for every `PresheafPFunctor`, or a counterexample together with a proof of completeness for the fragment named in obligation 9 |
| W-f — code morphisms | 10 | the code-level morphism type and representation theorem |

W-c depends on nothing; W-a depends on nothing; W-b depends on W-a and W-c;
W-d depends on W-c; W-e depends on W-c and W-d; W-f depends on W-a and W-c.

This document is the design record for all six and is removed with the last of
them, which deviates from § Concern shape's per-branch spec lifetime. The
rationale: between branches it presents decisions that are pending, not
superseded, which is what that section guards against. If W-a lands and the
rest are deferred, the deviation is to be resolved by moving the design record
into `docs/` as persistent documentation rather than leaving a spec on `main`.

## Proof obligations

Each is unproved at the time of writing.

1. **Stage 1 at upstream quality** (W-a). Port `PshHom`, its action, and
   `pshHomEquivNatFamily` from the prototype into `Geb/Mathlib/`, against the
   choice-free `objPresheaf` and `mapPresheaf` rather than
   `PresheafPFunctor.functor`. The `functor` form is a corollary and belongs in
   a module on `GebMeta.classicalAllowedModules`.
2. **Category structure** (W-a). Composition on `PshHom` (`idPshHom` already
   supplies the identity), that composition is associative with that identity
   as unit, and that the bijection of obligation 1 carries them to the
   identities and composition of natural transformations. Full and
   faithfulness of the interpretation is this obligation's deliverable, not
   obligation 1's.
3. **The natural-transformation identification** (W-a). That `PshNatFamily`,
   the unbundled proxy `pshHomEquivNatFamily` lands in, is equivalent to the
   natural transformations `F.functor ⟶ F'.functor`. The prototype relates
   `PshNatFamily` to nothing outside `Basic.lean`.
4. **Stage 2 at upstream quality** (W-c). Port `unitPsh`, `sigmaPsh`, `delta`
   and `coprod`, the code type and the interpretation. The prototype's
   `ElObj` / `elCategory` is written out rather than reused; the upstream
   version should be `S.Elementsᵒᵖ`. Acceptance for that choice: reuse is
   adopted unless it requires more transport lemmas than the four
   (`elObj_eq_of_hom`, `elHom_eq_eqToHom_comp`, `elEqToHom`, `elEqToHom_eq`)
   the written-out version needs.
5. **The bound's vocabulary at upstream quality** (W-c). Port
   `HasBijectiveReindex`, its six closure lemmas, `iotaPresheaf`, `iotaConst`,
   `ShapeArity.const`, `arityVaries` and `deltaVarying`. Obligations 6 and 7
   consume these, and the prototype is removed with this document, so without
   this obligation W-b has no inputs.
6. **Iso-invariance of the bound** (W-b). That `HasBijectiveReindex` transports
   along an isomorphism of interpreted functors, upgrading
   `not_hasBijectiveReindex_arityVaries` from a syntactic to a semantic
   statement. Depends on obligations 2 and 5.
7. **The fragment induction** (W-b). A code type for the constant-arity
   fragment, and the induction over it showing every code it admits denotes a
   functor with bijective reindexing. The three base cases and three step cases
   are proved in the prototype and ported by obligation 5; only the induction
   is missing.
8. **The decoding layer** (W-d). Codes parameterized by a base category and a
   decoding presheaf — `(𝕀, D)` and `(𝕁, E)` — with `δ`'s subcodes indexed by
   presheaf morphisms `P ⟶ D`, generalizing the singleton family the prototype
   carries. This is what supplies the recursion of induction-recursion, and
   until it lands the system denotes presheaf indexed containers rather than
   presheaf inductive-recursive definitions. The semantics is expected to need
   nothing new: `PSh(𝕀)/D ≃ PSh(el D)` should make such a code denote an
   ordinary `PresheafPFunctor (el D) (el E)`, which is the inference recorded
   in § The setting is indexed induction-recursion.
9. **Completeness** (W-e). Whether every `PresheafPFunctor` has a code — the
   analogue of Lemma 1 of [HancockMcBrideGhaniMalatestaAltenkirch2013]
   ("Every dependent polynomial functor is an IR functor"). The shape of the
   expected witness is `sigmaCode` at the shape presheaf over a `deltaCode` at
   the arity over `iotaCode`; that this reconstructs an arbitrary functor is
   conjecture, not elaboration. If it is false, the branch delivers the
   counterexample together with completeness for the fragment of functors whose
   arity is constant on each connected component of the shape presheaf.
10. **Code morphisms** (W-f). The code-level morphism type, mirroring `PshHom`,
    and the code-level representation theorem — the analogue of Theorem 3 of
    [HancockMcBrideGhaniMalatestaAltenkirch2013], present in the discrete case
    as `IR.interpHomEquiv`. Stage 1 determines the shape of both.

## Open questions

To be answered by the work rather than before it.

1. Whether the arity carrier universe, pinned to the base's in the prototype,
   needs to vary.
2. Whether `iotaPresheaf j₀` and `iotaConst (yoneda.obj j₀)` are isomorphic as
   functors. Their shape types agree definitionally
   (`iotaPresheafData_A_eq_iotaConstData_yoneda`, in the allowlisted `Functor`
   module because `yoneda` lands in a functor category); nothing more is
   established.
3. Whether the walking arrow should carry a worked example exercising
   `shapeRestr`, `reindex` and `reindexCompat` together, while staying small
   enough to compute with by hand. `arityVaries` has the walking arrow as its
   output base and exercises `reindex` alone: its shape presheaf is fibrewise a
   singleton (`arityVariesShapeEquiv`), its input base `Fin 1` makes
   `directionRestr` trivial, and `reindexCompat` is a `PshHom` field, of which
   it carries none. The worked example would be new.
4. Whether `PresheafPFunctor` at discrete `I` and `J` carries information
   beyond `SlicePFunctor`, and whether the code system degenerates to `IR`
   there.

## Non-goals

- Positive inductive-recursive definitions over `Fam(C)`
  ([GhaniNordvallForsbergMalatesta2015]). They meet the full-and-faithfulness
  requirement only by Remark 3.4's route, defining the interpretation
  simultaneously with the codes; the presheaf setting reaches it structurally.
  If wanted they are better recovered inside the presheaf construction, since
  `Fam(C)` embeds in presheaves as the coproducts of representables — an
  embedding this document does not establish, and whose fullness the recovery
  would need.
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
arXiv preprint's order. Pre-existing, with five persistent consumers besides `docs/references.bib`,
this spec and the transient prototype, deferred to its own branch per one
concern per branch.

## References

- [GhaniNordvallForsbergMalatesta2015] — positive inductive-recursive
  definitions; Remark 3.4 on the choice of morphism collection, and Section 2
  on the loss of full and faithfulness over `Fam(C)`.
- [GhaniMalatestaNordvallForsberg2014Agda] — its Agda formalization.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] — small induction recursion;
  Section 6 for `IIR`, Definition 6 for morphisms of dependent polynomials,
  Definition 7 for morphisms of indexed containers, Theorem 1 for the discrete
  representation theorem, Theorem 3 for the code-level full-and-faithfulness
  statement, Lemma 1 for completeness.
- [Weber2007], [nLabParametricRightAdjoint] — parametric right adjoints and
  familial functors.
- [SpivakGarnerFairbanks2021], [Shapiro2021] — parametric right adjoints
  between presheaf categories.
- [AltenkirchGhaniHancockMcBrideMorris2015] — indexed containers.
- [GambinoKock2013] — polynomial functors; Theorem 2.12, which
  [HancockMcBrideGhaniMalatestaAltenkirch2013] restates as its Theorem 1.
- [DybjerSetzer1999], [DybjerSetzer2003] — inductive-recursive definitions.
