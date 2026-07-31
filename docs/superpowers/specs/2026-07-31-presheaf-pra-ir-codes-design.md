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
  - [The two features of `δ` are orthogonal, and the fused rule has both](#the-two-features-of-%CE%B4-are-orthogonal-and-the-fused-rule-has-both)
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
machine-checked. Stage 2 is elaborated: the three rules, the code type and the
interpretation are built, and the recursion is present. Its obstruction is
reduced to a one-step induction whose base and step cases are proved; its
completeness and its morphism theory remain open.

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
preserves identities and composition (`IR.interpMor_id`, `IR.interpMor_comp`);
the `⥤` packaging is deferred to a `Classical.choice`-enabled wrapper. Two
capabilities it lacks motivate the generalization to presheaf bases:

- *Inference, not elaborated* — the prototype constructs no initial algebras
  (§ Non-goals) and no walking-arrow endofunctor (open question 4). Only one of
  the two index sets varies under iteration. In the endofunctor
  case the initial algebra generates a type together with a decoding into a
  *fixed* type. A presheaf on the walking arrow is a function between two sets,
  so an endofunctor there varies both sets and the map between them at once —
  which is what an inductive-inductive definition is.
- Full and faithfulness of the interpretation is not available over `Fam(C)`
  without defining the interpretation simultaneously with the codes.
  Section 2 of [GhaniNordvallForsbergMalatesta2015] records that the
  characterization of the `δ` interpretation as a left Kan extension fails for
  non-discrete `C`; its Conclusions and Future Work section lists recovering
  that characterization as future work, and separately records as an open
  problem whether the definable functors are closed under composition. Remark
  3.4 of
  the same paper offers the alternative — morphisms `Hom(x,y) = ⟦x⟧ → ⟦y⟧`,
  full and faithful by definition — at the cost of defining `⟦−⟧`
  simultaneously with the codes.

Stage 1 obtains the ingredients of full and faithfulness structurally instead,
from the fact that a presheaf p.r.a. functor's interpretation is by construction
a
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

So the presheaf system generalizes `IIR`, not `IR`: its input side is the pair
`(𝕀, D)` of a base category and a decoding presheaf, and `δ`'s continuation
depends on the decoding, which is `PshMor` — the presheaf reading of Section
6's sections `(p : P) → D (i p)`.

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
| `δ` | `deltaCode 𝔹 A hA K (hK : wIndex K = Cat.of (ElObj (decPresheaf A hA D)))` | `deltaFused A hA D` — adjoin the output-varying arity `A`, the continuation depending on its decoding |

Both continuations sit over a category of elements the shape determines, so
each rule has exactly one subcode slot. The interpretation is `interp`, the
fold of `codeAlg` over the W-type; its three computation rules
`interp_iotaCode`, `interp_sigmaCode` and `interp_deltaCode` are definitional,
and `interp_fst` records that a code's index is the base its interpretation
lands in.

Every semantic operation is a `PresheafPFunctor` — that is, all seven functor
laws are proved, not assumed: `unitPsh`, `sigmaPsh`, `delta`, `coprod`,
`deltaRec` and `deltaFused`. The last two are composites of the others and so
inherit their laws rather than needing new ones.

### Why `δ`'s arity must vary over the shape presheaf

This is the negative result the design depends on, and the reason the
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
It is not `arityVaries`: its directions are `arityB a ⊕ PEmpty`, and no
isomorphism is constructed.

The result is syntactic: it bounds what the constructions produce on the
nose, not up to isomorphism of the interpreted functors. Obligation 6 expects
to derive the transport of `HasBijectiveReindex` along an isomorphism from
`pshHomEquivNatFamily`, but needs composition on `PshHom`, which the prototype
does not build (`idPshHom` supplies the identity). That is proof obligation 2.

### The two features of `δ` are orthogonal, and the fused rule has both

An arity varying over the output object and a continuation depending on the
decoding are independent: the recursion does not by itself reach past the
bound.

`deltaRec` is the intermediate construction that shows this, and the code
system does not use it. Regrouping `IR.delta`'s coproduct over
assignments by the decoding each induces presents it as a coproduct, over the
decodings `PshMor G D`, of non-recursive `δ`s at the corresponding fibre arity
(`fibreArity`, whose closure under restriction is exactly the decoding's
naturality). It needs no new functoriality proof, being built from `coprod` and
`delta`. Its adjoined arity is constant over the output, so it lies inside the
same bound as `deltaConst` (`hasBijectiveReindex_deltaRec`).

`deltaFused` has both. Three steps, none of them a new operation:

1. The decodings of an output-varying arity form a presheaf on the output base
   (`decPresheaf`), restriction along `g : b' ⟶ b` being precomposition with
   `A.reindex g`; its functor laws are `A`'s reindexing laws.
2. Over `ElObj (decPresheaf A hA D)` every object carries its own decoding, so
   the adjoined arity is an ordinary `BaseArity` there (`decArity`,
   `isFunctorial_decArity`), and `BaseArity.pullback` turns it into the
   shape-indexed arity `delta` consumes.
3. `sigmaPsh` pushes the result forward to the output base.

`not_hasBijectiveReindex_deltaFusedVaries` checks that the fusion does not cost
the output-varying arity: at the terminal decoding, where the recursion
degenerates (`subsingleton_pshMor_to_terminal`), the fused `δ` at an
output-varying arity still lies outside the bound.

### Why no inductive-inductive definition is needed

A code's `δ` cannot mention its subcode's shapes, so its arity is indexed by
output objects (`BaseArity`) and pulled back along the shape-output map
(`BaseArity.pullback`, `BaseArity.isFunctorial_pullback`). The transport that
the pullback carries is the reason `ShapeArity` is indexed by shapes rather
than by output objects: `deltaData` is then free of it.

Nor does the recursion force mutuality. A continuation depending functorially
on the decoding is one code over `ElObj (decPresheaf A hA D)`, not a family of
codes indexed by decodings — the same collapse `σ` already makes. So `δ`, like
`σ`, has a single subcode slot at a base the shape determines.

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
| `PshHom`, to be named `PresheafPFunctor.Hom` upstream | Novel in this repository. The shapes-forward arities-backward form is Definition 7 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (morphisms of indexed containers) in the discrete case; its Definition 6 is the dependent-polynomial presentation of morphisms; the `r`/`t`/`q` naming this repository follows is its Definition 1 |
| The action of a `Hom`, and its naturality | Novel |
| The representation theorem (`pshHomEquivNatFamily`) | Novel at this level. Its discrete analogue is Theorem 1 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (that paper's restatement of Theorem 2.12 of [GambinoKock2013]), together with Definition 7 for the indexed-container form. Theorem 3 of the same paper is the code-level statement, present as `IR.interpHomEquiv`, and is the analogue of proof obligation 9, not of this |
| Identity, composition, and the category structure on `Hom` | Novel |
| The `σ` / `δ` code rules | Transcription of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013], generalized from families to presheaves: `σ`'s family over a set becomes a base change along a category of elements, and `δ`'s sections `(p : P) → D (i p)` become `PshMor`. The further generalization of `δ`'s arity from an object of `Set/I` to one varying over the output object is novel, and § Why `δ`'s arity must vary over the shape presheaf shows it is forced |
| The `ι` code rule | Novel. Section 6's `ι` takes a point of the output total space `ΣE`; `iotaCode 𝔹` takes none and denotes `unitPsh`, one shape over every object of `𝔹`. The pointed form exists in the prototype as `iotaPresheaf j₀` but is not what the code system uses, and that `σ` at a representable over `iotaCode` recovers it is unelaborated |
| Indexing the code type by a base category, with `σ` replacing it by a category of elements | Novel |
| `coprod`, the coproduct of a type-indexed family | Novel at this level; the discrete analogue is `SlicePFunctor.coprod` |
| `unitPsh`, the unit | Novel at this level; the discrete analogue is `SliceDomPFunctor.representable` at the empty direction type |
| `delta`, adjoining an arity | Novel at this level; the discrete analogue is `SliceDomPFunctor.prodSlice` against a representable |
| `sigmaPsh`, the base change along `ElObj S → J` | Novel. It has no discrete analogue in this repository: over a discrete base the category of elements is discrete and the base change collapses into `SlicePFunctor.coprod` |
| `DomArity` — a presheaf on `I`, unbundled | Novel presentation of a standard object, chosen so its directions plug into a `PresheafPFunctorData`'s without transport |
| `ShapeArity`, `ShapeArity.const` — the arity a `δ` adjoins, varying over the shape presheaf | Novel; it is the unbundled data of a functor `el(T₁)ᵒᵖ ⥤ (Iᵒᵖ ⥤ Type)`. `const` is the case Section 6's `δ` arity occupies |
| `BaseArity`, `BaseArity.pullback` — the arity indexed by output objects, and its pullback along `q` | Novel |
| `ElObj`, `elCategory` — the category of elements as a base category | Transcription. It is `S.Elementsᵒᵖ`, written out to avoid `Opposite` transport; obligation 4 revisits the choice |
| `HasBijectiveReindex` | Novel; the property that every reindexing map is a bijection. That this is cartesianness of `objPresheaf`'s fibres over the shape presheaf is an unelaborated reading |
| `CodeShape`, `CodeDir`, `CodeNext`, `codePFunctor`, `Code` | Novel. Indexing by a base category, with `σ` replacing it by a category of elements, has no counterpart in the cited literature |
| `codeAlgOn`, `codeAlg`, `interp` — the interpretation | Novel at this level; the discrete analogue is `IR.interpObj` |
| The constant-arity fragment's code type (obligation 7) | Novel |
| The code-level morphism type (obligation 9) | Novel at this level; the discrete analogue is `IR.Hom` |
| `PshMor` — a morphism from a `DomArity` to a presheaf, unbundled | Novel presentation; it is the presheaf reading of Section 6's sections `(p : P) → D (i p)` |
| `fibreArity` — the arity a decoding adjoins | Novel |
| `deltaRec` — the `δ` whose continuation depends on the decoding | Transcription of Section 6's `δ` rule at a constant arity |
| `decPresheaf` — the decodings of an output-varying arity, as a presheaf on the output base | Novel |
| `decArity` — that arity, indexed by the elements of `decPresheaf` | Novel |
| `deltaFused` — the `δ` carrying both features | Novel; it is Section 6's `δ` rule with the arity generalized as § Why `δ`'s arity must vary requires |

## Branches

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape binds one concern
per branch. The obligations below divide into five.

| Branch | Obligations | Acceptance |
| --- | --- | --- |
| W-a — Stage 1 upstream | 1, 2, 3 | `PshHom`, its action and the hom-set bijection in `Geb/Mathlib/`, choice-free; composition and the category structure; and the bijection related to natural transformations of the interpreted functors |
| W-b — Stage 2 upstream | 4, 5 | the semantic operations, the decoding layer, the code type, the interpretation, and the bound's vocabulary in `Geb/Mathlib/` |
| W-c — the bound | 6, 7 | `HasBijectiveReindex` transports along an isomorphism, and the constant-arity fragment's induction is formalized against a code type for that fragment |
| W-d — completeness | 8 | either a code for every `PresheafPFunctor`, or a counterexample together with a proof of completeness for the fragment named in obligation 8 |
| W-e — code morphisms | 9 | the code-level morphism type and representation theorem |

W-a and W-b depend on nothing; W-c depends on W-a and W-b; W-d depends on W-b;
W-e depends on W-a and W-b.

This document is the design record for all five and is removed with the last of
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
4. **Stage 2 at upstream quality** (W-b). Port `unitPsh`, `sigmaPsh`, `delta`,
   `coprod`, `PshMor`, `fibreArity`, `decPresheaf`, `decArity`, `deltaFused`,
   the code type and the interpretation, together with the structures they rest
   on — `DomArity`, `ShapeArity` and `ShapeArity.const`, `BaseArity` with
   `pullback` and `isFunctorial_pullback`, `ElObj` / `elCategory`,
   `sigmaLiftHom`, `elEqToHom` and `Interp`. `deltaRec` and
   `subsingleton_pshMor_to_terminal` are deliberately not ported: the code
   system does not use them, and per [CONTRIBUTING.md](../../../CONTRIBUTING.md)
   § Code is cost they earn no upstream byte. The prototype's
   `ElObj` / `elCategory` is written out rather than reused; the upstream
   version should be `S.Elementsᵒᵖ`. Acceptance for that choice: reuse is
   adopted unless it requires more transport and projection lemmas than the
   seven (`elObj_eq_of_hom`, `elHom_eq_eqToHom_comp`, `elEqToHom`,
   `elEqToHom_eq`, `elCategory_eqToHom_val`, `elCategory_id_val`,
   `elCategory_comp_val`) the written-out version needs.
5. **The bound's vocabulary at upstream quality** (W-b). Port
   `HasBijectiveReindex`; its six closure lemmas together with the general
   `hasBijectiveReindex_delta` they rest on; the three negative theorems
   `not_hasBijectiveReindex_arityVaries`,
   `not_hasBijectiveReindex_deltaVarying` and
   `not_hasBijectiveReindex_deltaFusedVaries`; and the witnesses they need —
   `iotaPresheaf`, `iotaConst`, `arityVaries` with `arityVariesShapeArity` and
   `isFunctorial_arityVariesShapeArity`, `deltaVarying` with
   `deltaVarying_source_empty`, and `termPsh`, `arityVariesBase`,
   `isFunctorial_arityVariesBase`, `decUnit`, `deltaFusedVaries`. Obligations 6
   and 7 consume these, and
   [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md)
   § Subtree import rules forbids `Geb/Mathlib/` from importing
   `Geb.Internal.*`, so without this obligation W-c has no inputs whether or
   not the prototype still exists.
6. **Iso-invariance of the bound** (W-c). That `HasBijectiveReindex` transports
   along an isomorphism of interpreted functors, upgrading
   `not_hasBijectiveReindex_arityVaries` from a syntactic to a semantic
   statement. Depends on obligations 2 and 5.
7. **The fragment induction** (W-c). A code type for the constant-arity
   fragment, and the induction over it showing every code it admits denotes a
   functor with bijective reindexing. The three base cases and three step cases
   are proved in the prototype and ported by obligation 5; only the induction
   is missing.
8. **Completeness** (W-d). Whether every `PresheafPFunctor` has a code — the
   analogue of Lemma 1 of [HancockMcBrideGhaniMalatestaAltenkirch2013]
   ("Every dependent polynomial functor is an IR functor"). The shape of the
   expected witness is `sigmaCode` at the shape presheaf over a `deltaCode` at
   the arity over `iotaCode`; that this reconstructs an arbitrary functor is
   conjecture, not elaboration. If it is false, the branch delivers the
   counterexample together with completeness for the fragment of functors whose
   arity is constant on each connected component of `el(T₁)`, the category of
   elements of the shape presheaf.
9. **Code morphisms** (W-e). The code-level morphism type, mirroring `PshHom`,
   and the code-level representation theorem — the analogue of Theorem 3 of
   [HancockMcBrideGhaniMalatestaAltenkirch2013], present in the discrete case
   as `IR.interpHomEquiv`. Stage 1 determines the shape of both.

## Open questions

To be answered by the work rather than before it.

1. Whether the universes the code type pins — the input base, its homs and the
   decoding presheaf all at `u` — need to vary. The pinning is what makes
   `Cat.{v, u}` closed under both continuation steps.
2. Whether the output side should also carry a decoding presheaf `E`, as
   Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013] does. The
   prototype's output index is a bare category, which by the collapse of
   § The setting already subsumes a pair `(𝕁, E)` at `el E`; whether the syntax
   gains from naming `E` separately is not settled.
3. Whether `iotaPresheaf j₀` and `iotaConst (yoneda.obj j₀)` are isomorphic as
   functors. Their shape types agree definitionally
   (`iotaPresheafData_A_eq_iotaConstData_yoneda`, in the allowlisted `Functor`
   module because `yoneda` lands in a functor category); nothing more is
   established.
4. Whether the walking arrow should carry a worked example exercising
   `shapeRestr`, `reindex` and `reindexCompat` together, while staying small
   enough to compute with by hand. `arityVaries` has the walking arrow as its
   output base and exercises `reindex` alone: its shape presheaf is fibrewise a
   singleton (`arityVariesShapeEquiv`), its input base `Fin 1` makes
   `directionRestr` trivial, and `reindexCompat` is a `PshHom` field, of which
   it carries none. The worked example would be new.
5. Whether `PresheafPFunctor` at discrete `I` and `J` carries information
   beyond `SlicePFunctor`, and whether the code system degenerates to `IR`
   there.

## Non-goals

- Positive inductive-recursive definitions over `Fam(C)`
  ([GhaniNordvallForsbergMalatesta2015]). They meet the full-and-faithfulness
  requirement only by Remark 3.4's route, defining the interpretation
  simultaneously with the codes; the presheaf setting obtains it structurally.
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

`docs/references.bib`'s note on
`HancockMcBrideGhaniMalatestaAltenkirch2013` records the proceedings-vs-preprint
renumbering only for the results cited before this workstream. This document
adds Lemma 1, Definition 1, Definition 6, Definition 7 and Theorem 1, all
verified against the TLCA 2013 proceedings; extending the note to cover them is
part of obligation 4's documentation.

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
