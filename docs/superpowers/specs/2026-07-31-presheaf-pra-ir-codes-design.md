# Codes for presheaf parametric-right-adjoint functors

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with
[DocToc](https://github.com/thlorenz/doctoc)*

- [Scope of this document](#scope-of-this-document)
- [The rules as a generalization of small induction recursion](#the-rules-as-a-generalization-of-small-induction-recursion)
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
bounded rather than discharged: the bound's three generator and four operation
cases are proved, but the code type they would run over is a different one from
the prototype's — its `δ` carries a `PshMor`-indexed subcode family, so it is a
different slice polynomial functor — and building it, running the induction
over it, and supplying the composition and the iso-transport the semantic form
of the bound needs are all outstanding (obligations 2, 6 and 7). Its
completeness and its morphism theory remain open.

The prototype at `Geb/Internal/PresheafIRProto/` is the source this document
transcribes. It compiles, is linted, and is audited by
`GebMeta.detectNonstandardAxiom`; every declaration cited below is
`Classical.choice`-free except where noted. Where this document and the
prototype's *elaborated content* disagree, the prototype is right; its prose
carries no such authority. Claims marked *inference*, *unelaborated* or
*conjecture* are not elaborated there. Every other claim names the declaration
that establishes it, with three classes of exception, each flagged where it
arises: readings of a construction, backed by structure fields rather than by
theorems (§ Stage 1, facts 2 and 4); the discrete analogues named in §
Definitions' `Status` cells, no one of which is an elaborated identification;
and statements about ambient mathematics rather than about this development (§
Stage 1, fact 2's appeal to Yoneda in any locally small category).

The prototype is not deliverable content. Each branch removes the part of it
that branch ports, rather than the whole surviving until the last branch. W-a
and W-b are independent in their deliverables but both edit
`Geb/Internal/PresheafIRProto/Basic.lean` and
`Geb/Internal/PresheafIRProto/Functor.lean` — W-a removing
`arityHomEquivNatTrans` and `objEquivSigmaHom` from the latter, W-b rewriting
the `iotaPresheafData_A_eq_iotaConstData_yoneda` that survives it — so
whichever lands second rebases over the other's edits: after W-a and W-b, what
remains is the retained derivation below. Removal alone does not leave it
buildable. Most of it names declarations the ports move and rename —
`arityVariesShapeEquiv` and the two `arityVariesData_B_*` checks name
`arityVariesData`; `iotaPresheafData_A_eq_iotaConstData_yoneda` names
`iotaPresheafData` and `iotaConstData`; `arityPresheafHomAtUB` and
`arityPresheafHomULifted` name `arityPresheaf`; the whole domain-level warm-up
names `objEquivSigmaArityHom`, `ArityHom` and the four shared `ArityHom`
declarations — so each of W-a and W-b also rewrites the retained remainder
against the names it has just established in `Geb/Mathlib/`, and the prototype
gains imports of the new modules, which `Geb/Internal/` is permitted. Only
`SliceHom`, `sliceHomApp`, `Functoriality` and `iotaDiscreteShapeEquiv` stand
free of both ports. Whichever of W-c to W-f lands last removes the remainder
together with this document, the plan, the directory index
`Geb/Internal/PresheafIRProto.lean`, `Geb/Internal.lean` — whose sole import is
that index, leaving it empty — the `public import Geb.Internal` in `Geb.lean`,
the `Geb.Internal.PresheafIRProto.Functor` entry in
`GebMeta.classicalAllowedModules`, and the two module-docstring mentions of
`Geb.Internal` — a bullet in `Geb.lean`, a clause in `GebTests.lean` —
`GebTests/Internal/` itself surviving as the axiom-linter fixtures; W-c, W-d
and W-e are mutually unordered and W-f precedes W-d, so any of those three may
land last and which does is not determined in advance, and the removal is a
condition on the last rather than an assignment to a named branch. Carrying the
whole prototype alongside its port would define the same declarations twice on
`main`, against [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Code is cost.

It also retains steps of the derivation that the obligations do not port, and
which exist to record how the design was reached rather than to be delivered:
the domain-level warm-up (`DomHom`, `DomNatFamily`, `domHomEquivNatFamily` and
their lemmas), the slice-level morphism formula (`SliceHom`, `sliceHomApp`),
`Functoriality`, `iotaDiscreteShapeEquiv`, the universe-formability
demonstrations in `Functor.lean` (`arityPresheafHomAtUB`,
`arityPresheafHomULifted`), `iotaPresheafData_A_eq_iotaConstData_yoneda`, which
open question 3 cites and no obligation ports, and the small computation checks
(`arityVariesData_B_zero`, `arityVariesData_B_one`,
`domHom_eq_pi_sigma_arityHom`), and `arityVariesShapeEquiv`, which open
question 4 cites and no obligation ports, so that citation lapses with the
prototype. None is reachable from the code system. Within the domain-level
warm-up the line falls thus: `idArityHom`, `natTransOfArityHom`,
`postcompArityHom` and `map_symm_arityHom` are shared with the `PshHom` layer
and are ported by obligation 1; `idElt`, `map_idElt`,
`objEquivSigmaArityHom_idElt`, `domHomSigma`, `domHomFamily`,
`domHomFamily_symm` and `domHomEquivNatFamily` are warm-up only and are not.

## The rules as a generalization of small induction recursion

The code system is presented here as a generalization of `IR I O`, taken rule
by rule, rather than of Section 6's `IIR D E`. The two readings agree: `IR I O`
denotes a functor `Set/I → Set/O`, which under the equivalence between slices
of `Set` and presheaves on discrete categories is `PSh(|I|) → PSh(|O|)`, and
generalizing `I` and `O` from sets to categories reintroduces the indexing by
itself, since a slice of a presheaf category is a presheaf category over
another base (§ Proof obligations, obligation 9).

One principle covers all three rules: **replace equality by a morphism**. In a
discrete category `Hom(x, y)` is `x = y`, so each rule collapses to its
small-IR counterpart over a discrete base, which is what makes the
generalization conservative.

| Rule | Small `IR` | Here | Status |
| --- | --- | --- | --- |
| `ι` | takes `o : O`, denoting `o' ↦ (o' = o)` | takes `j₀ : 𝔹`, denoting `j' ↦ Hom(j', j₀)` — the representable | Confirmed. `interp_iotaCode` folds `iotaCode 𝔹 j₀` to `iotaPresheaf j₀`; `iotaDiscreteShapeEquiv` is the discrete collapse |
| `σ` | takes `S : Set` and a family `K : S → IR I O`, denoting a coproduct | takes `S : 𝔹ᵒᵖ ⥤ Type u` and one subcode over `el(S)`, denoting the dependent sum along `el(S) → 𝔹` | Open, and the one place the parallel does not yet line up; see open question 7 |
| `δ` | takes `P : Set` and `i : P → I`, the node's directions and their labelling | takes a `BaseArity`; each `fam j` is a discrete fibration over `I`, in the same directions role, and the output-indexing is functorial | Confirmed. `DomArity.presheaf` and `BaseArity.functor`; [nLabParametricRightAdjoint] is the characterization that fixes it |

Two facts recur across the confirmations and are stated once here rather than
at each site. First, a total space costs one universe: `Interp`'s shape
universe is `max u v` and `DomArity.ofPresheaf`'s carrier is at `max uI uB`,
both because a family of fibres indexed by the base is larger than either.
Second, the boundary between the choice-free core and the
`GebMeta.classicalAllowedModules` wrapper falls in one place — writing `⟶`
between two objects of a functor category, or `⥤` into one, invokes
`CategoryTheory.Functor.category`, which depends on `Classical.choice`, where
the corresponding bare `NatTrans` or unbundled data does not. That is why
`arityHomEquivNatTrans`, `objEquivSigmaHom` and `BaseArity.functor` are in
`Functor.lean` while `reindexHom` and `ArityHom` are not.

Reorganizing this document to lead with the codes and their interpretation, so
that the table above rather than the setting comes first, is deferred until the
`σ` question is settled, since the rule it would present is the one still in
question.

## Motivation

The repository's existing code system, `IndRec.IR I O`, denotes functors
between free coproduct completions of discrete index types. Its interpretation
preserves identities and composition (`IR.interpMor_id`, `IR.interpMor_comp`);
the `⥤` packaging is deferred to a `Classical.choice`-enabled wrapper. One
capability it lacks, and one property that the `Fam(C)`-based positive
inductive-recursive definitions of [GhaniNordvallForsbergMalatesta2015] lack,
motivate the generalization to presheaf bases. `IR I O` itself is full and
faithful — Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013], present
here as `IR.interpHomEquiv` — so the second point is about the `Fam(C)`
generalization, not about `IR I O`:

- *Inference, not elaborated* — the prototype constructs no initial algebras (§
  Non-goals) and no walking-arrow endofunctor. Only one of the two index sets
  varies under iteration. In the endofunctor case the initial algebra generates
  a type together with a decoding into a *fixed* type. A presheaf on the
  walking arrow is a function between two sets, so an endofunctor there varies
  both sets and the map between them at once — which is what an
  inductive-inductive definition is.
- *Inference, not elaborated* — the paper asserts no impossibility; Remark 3.4
  places `Hom(x,y) = ⟦x⟧ → ⟦y⟧` at one end of a range of admissible morphism
  collections, and Section 2 records only that its own choice loses the
  property, adding that it "is not an essential property". That nothing short
  of the simultaneous definition recovers it over `Fam(C)` is this document's
  reading. The prototype argues the loss concretely rather than from Remark
  3.4: by Theorem 2.4 of [GhaniNordvallForsbergMalatesta2015] the `δ`
  interpretation's coproduct is indexed by set maps `A → X`, whereas by its
  Definition 2.2 a `Fam(C)`-morphism carries `C`-morphism data that index does
  not, so the interpretation is not a coproduct of `Fam(C)`-representables.
  Full and faithfulness of the interpretation is not available over `Fam(C)`
  without defining the interpretation simultaneously with the codes. Section 2
  of [GhaniNordvallForsbergMalatesta2015] records that the characterization of
  the `δ` interpretation as a left Kan extension fails for non-discrete `C`;
  its Conclusions and Future Work section lists recovering that
  characterization as future work, and separately records as an open problem
  whether the definable functors are closed under composition. Remark 3.4 of
  the same paper offers the alternative — morphisms `Hom(x,y) = ⟦x⟧ → ⟦y⟧`,
  full and faithful by definition — at the cost of defining `⟦−⟧`
  simultaneously with the codes.

Stage 1 obtains the ingredients of full and faithfulness structurally instead,
from the fact that a presheaf p.r.a. functor's interpretation is by
construction a coproduct of representables. What it delivers is the hom-set
bijection; obligations 2 and 3 carry that to full and faithfulness.

## Stage 1: morphisms and the representation theorem

Settled up to the category structure and the identification recorded as
obligations 2 and 3. `Geb/Internal/PresheafIRProto/Basic.lean` carries it,
choice-free; `Functor.lean` carries what depends on `Classical.choice` through
`CategoryTheory.Functor.category`: `arityHomEquivNatTrans` and
`objEquivSigmaHom`, which write `⟶` between objects of a presheaf category; the
two universe-formability demonstrations `arityPresheafHomAtUB` and
`arityPresheafHomULifted`, which do the same; and
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
   `PshHom F F' ≃ PshNatFamily F F'`. It is not definitional: its inverse is
   `natFamilyPshHom`, whose `reindexCompat` field is discharged by
   `natFamily_generic` and `objFibMap_eq_objFibRestr_apply`; the equivalence's
   own `left_inv` rests on `natFamilyArity_pshHomFamily` and `pshHom_ext`. Two
   steps separate it from full and faithfulness of the interpretation, both
   obligations rather than results: `PshNatFamily` is an unbundled proxy and is
   nowhere related to `PresheafPFunctor.functor`'s natural transformations
   (obligation 3), and fullness and faithfulness are properties of a functor,
   so they need composition on `PshHom` carried across the bijection
   (obligation 2).
2. The classification is available because the interpretation is a coproduct of
   representables (`objEquivSigmaArityHom`), not because of any property of the
   ambient category: Yoneda holds in any locally small category.
3. Unbundling yields constructivity, and universe polymorphism where the
   statement admits it. `objEquivSigmaArityHom` holds at arbitrary `uZ`; its
   bundled wrapper `objEquivSigmaHom` is pinned to `uZ := uB`. The Stage 1
   deliverable `pshHomEquivNatFamily` carries the same pinning as the bundled
   version, `PshNatFamily` quantifying only over `Z : Iᵒᵖ ⥤ Type uB`; what
   unbundling buys there is constructivity alone. `objEquivSigmaHom`'s
   restriction comes from requiring the arity presheaf and the input presheaf
   to lie in one functor category, which is what `⟶` demands and what
   introduces `Classical.choice`. `pshHomEquivNatFamily`'s comes from
   `PshNatFamily`'s own quantification and is choice-free.
4. `PresheafPFunctorData` already is the familial presentation in unbundled
   form. `shapeRestr` gives `T₁` its presheaf structure, `directionRestr` gives
   each `E(a)` its own, and `ReindexNaturality` says exactly that `reindex g a
   : E(shapeRestr g a) ⟶ E(a)` is a presheaf morphism.

## Stage 2: the code system

`Geb/Internal/PresheafIRProto/Codes.lean` carries it, choice-free.

### The setting is indexed induction-recursion, not induction-recursion

`IR I O` collapses two roles that Section 6 of
[HancockMcBrideGhaniMalatestaAltenkirch2013] keeps apart. In `IR.delta B (c :
(B → I) → IR I O)` the map `B → I` is simultaneously the arity's
index-labelling and the decoding of the recursive arguments; in that paper's
`IIR D E` the labelling `i : P → I` is fixed data and the subcodes are indexed
by the decodings `(p : P) → D (i p)`.

The presheaf setting forces the split, and what it forces the arity to be is
fixed by the ambient characterization rather than by this design.
[nLabParametricRightAdjoint] presents the p.r.a. functors between presheaf
categories as the polynomials `I ← E → K → J` in `Cat` in which the last leg `K
→ J` is a discrete fibration and the first two form a two-sided discrete
fibration, the leg into `I` being a fibration and the leg into `K` an
opfibration.

The first condition is this repository's shape presheaf: `q : A → J` with
`shapeRestr` and its two laws is a discrete fibration over `J`. *Inference, not
elaborated*: the second condition is the arity side, the fibration into `I`
being the presheaf structure carried at each shape and the two-sidedness the
compatibility `reindex` and `ReindexNaturality` impose between that structure
and shape restriction. Nothing here identifies the two presentations; what is
elaborated is only that the arity datum is a presheaf on `I`.

A discrete fibration over `I` is a presheaf on `I` presented by the total space
of its own fibres — not to be confused with the polynomial's `E`, the total
space of directions over shapes — and that is what `DomArity` is: `carrier`,
`proj`, and a contravariant action on the fibres of `proj`. It is the arity at
*one* shape, occupying the `B`-slot of `deltaData`, where `ShapeArity.fam` and
`BaseArity.fam` supply the parameterization by shape and by output object; the
paper's `P` and `i : P → I` are `carrier` and `proj`, and the decodings that
`δ` turns into shapes are `PshMor`, reaching the shape presheaf through
`sigmaPsh` rather than through the arity. The total-space presentation is what
`deltaData` consumes, needing one type per shape in its `B`-slot and recovering
the `I`-indexing through `r`; `DomArity.presheaf` is the fibrewise form,
`ofPresheaf` converts back, and `dirEquivOfPresheaf`,
`dirEquivOfPresheaf_restr` and `sigmaDirEquivCarrier` are the round trips. The
labelling is therefore code data carrying presheaf structure, which is the
separation `IIR` makes and `IR` does not.

The round trip is stated fibrewise rather than as an isomorphism of presheaves
because `ofPresheaf` raises the carrier's universe from `uB` to `max uI uB`, so
the two presheaves inhabit different functor categories and no isomorphism
between them is formable.

`δ`'s own datum is the output-indexed version: `BaseArity.isFunctorial_fam`
gives each `fam j` its two presheaf laws, `famPresheaf` names the resulting
presheaf on `I`, and `reindexHom` is the morphism of presheaves that
`reindex_naturality` supplies for each output morphism. `BaseArity.functor`
bundles the four as a functor `J ⥤ (Iᵒᵖ ⥤ Type uB)` — the output base to
discrete fibrations over the input base — whose two laws are `IsFunctorial`'s
remaining `reindex_id` and `reindex_comp` clauses.

So the presheaf system generalizes `IIR`, not `IR`: its input side is the pair
`(𝕀, D)` of a base category and a decoding presheaf, and `δ`'s continuation
depends on the decoding, which is `PshMor` — the presheaf reading of Section
6's sections `(p : P) → D (i p)`.

Throughout, `el(−)` is mathlib's category of elements, so that the base
category whose presheaves are the slice `PSh(𝕀)/D` is `el(D)ᵒᵖ` — which the
prototype writes `ElObj D`.

*Inference, not elaborated.* The semantic counterpart of that split is the
equivalence `PSh(𝕀)/D ≃ PSh(el(D)ᵒᵖ)`: `IIR D E` interprets into `Set/ΣD →
Set/ΣE`, and the presheaf analogue of the total-space collapse needs the
category of elements rather than a bare `Σ`. Consequently a presheaf-`IIR` code
over `(𝕀, D)`, `(𝕁, E)` denotes an ordinary `PresheafPFunctor (el(D)ᵒᵖ)
(el(E)ᵒᵖ)`, and the code system's semantics needs no notion beyond Stage 1's.
The prototype uses the category of elements as a base category (`ElObj`,
`elCategory`) but does not construct that equivalence; in mathlib it is the
composite of `overEquivPresheafCostructuredArrow` and
`CategoryOfElements.costructuredArrowYonedaEquivalence`.

### The three rules and their semantics

`Code` is a single unindexed type, fibred over `Cat` by the projection
`codePFunctor.wIndex`; each constructor with a subcode takes an explicit
hypothesis `hK` aligning that subcode's fibre with the slot it fills. The
constructors, with the semantic operation each folds to:

| Rule | Code constructor | Semantics |
| --- | --- | --- |
| `ι` | `iotaCode 𝔹 j₀` | `iotaPresheaf j₀` — the constant functor at the representable `y j₀`, no directions |
| `σ` | `sigmaCode 𝔹 S K (hK : wIndex K = Cat.of (ElObj S))` | `sigmaPsh S` — push a functor over `ElObj S` forward to `𝔹` |
| `δ` | `deltaCode 𝔹 A hA K (hK : wIndex K = Cat.of (ElObj (decPresheaf A hA D)))` | `deltaFused A hA D` — adjoin the output-varying arity `A`, the continuation depending on its decoding |

Both continuations sit over a category of elements the shape determines, so
each rule has exactly one subcode slot. The interpretation is `interp`, the
fold of `codeAlg` over the W-type; its three computation rules
`interp_iotaCode`, `interp_sigmaCode` and `interp_deltaCode` are definitional,
and `interp_fst` records that a code's index is the base its interpretation
lands in.

Every operation and generator named in this document is a `PresheafPFunctor` —
that is, all seven functor laws are proved, not assumed: `unitPsh`,
`iotaPresheaf`, `iotaConst`, `sigmaPsh`, `delta`, `coprod`, `deltaRec` and
`deltaFused`. The last two are composites of the others and so inherit their
laws rather than needing new ones. `unitPsh` is no longer among the code
system's semantics; it survives as a semantic operation, as a generator of the
fragment below, and as the base of the `arityVaries` fixtures.

### Why `δ`'s arity must vary over the shape presheaf

This is the negative result the design depends on, and the reason the
constant-arity reading of `ι` / `σ` / `δ` does not suffice.

- `HasBijectiveReindex F` says every reindexing map of `F` is a bijection.
- It holds of `iotaPresheaf` and `iotaConst`
  (`hasBijectiveReindex_iotaPresheaf`, `hasBijectiveReindex_iotaConst`), is
  held by the unit (`hasBijectiveReindex_unitPsh`), inherited by coproducts
  (`hasBijectiveReindex_coprod`) and by the `σ` base change
  (`hasBijectiveReindex_sigmaPsh`); and a `δ` inherits it from the adjoined
  arity's own reindexing together with the subfunctor's
  (`hasBijectiveReindex_delta` requires both), in particular from a constant
  arity, whose reindexing is the identity (`hasBijectiveReindex_deltaConst`).
  Only that direction is proved; the converse is not used.
- `arityVaries`, a functor whose output base is the walking arrow, whose shape
  presheaf is terminal and whose arity is inhabited over `1` and empty over
  `0`, does not satisfy it (`not_hasBijectiveReindex_arityVaries`).

Define the *constant-arity fragment* once, as a generator and operation list:
its generators are `unitPsh`, `iotaPresheaf` and `iotaConst`; its operations
are `coprod`, `sigmaPsh`, `delta` at a `ShapeArity.const` — written
`deltaConst` below, though the prototype names only the lemma
`hasBijectiveReindex_deltaConst` and not the operation — and `deltaRec`. Every
`δ` in it adjoins an arity constant over the output object; `deltaConst` is the
case with a single continuation and `deltaRec` the case with a continuation
indexed by the decoding, and both are primitives of the fragment, `deltaRec`
because obligation 7's code type must carry the decoding-indexed subcode family
in order to contain Section 6's `δ`.

The fragment contains the presheaf reading of the rules of
[HancockMcBrideGhaniMalatestaAltenkirch2013] Section 6 — `iotaPresheaf` for its
pointed `ι`, `sigmaPsh` for its `σ` (`coprod` entering only as the operation
`deltaRec` is built from), `deltaRec` for its `δ`, whose arity is an object of
`Set/I` and so carries no dependence on the output object. *Inference, not
elaborated*: it is larger, `unitPsh` having no Section 6 counterpart, Section
6's `ι` being pointed, and `iotaConst` being the constant functor at an
arbitrary presheaf, which `iotaPresheaf` and `coprod` are not expected to
reach, those generating only coproducts of representables. Nothing establishes
that non-reachability, so the bound is stated over the fragment as defined
above and no claim is made about how much larger than Section 6's rules that
is.

`hasBijectiveReindex_unitPsh`, `_iotaPresheaf` and `_iotaConst` are the
generators' cases; `_coprod`, `_sigmaPsh`, `_deltaConst` and `_deltaRec` are
the operations'.

*Inference, not elaborated.* That the fragment therefore cannot denote
`arityVaries` is an induction over its codes. The prototype does not formalize
it: it builds a code type for the adopted rules only, and the fragment's is a
different one, its `δ` carrying a decoding-indexed subcode family. Building
that code type and running the induction is obligation 7.

The replacement is `ShapeArity`: an arity varying over the shape presheaf,
which is the unbundled data of a functor `el(T₁)ᵒᵖ ⥤ (Iᵒᵖ ⥤ Type)`.
`deltaVarying` is the `δ` carrying `arityVaries`'s arity, and
`not_hasBijectiveReindex_deltaVarying` records that it lies outside the bound.
It is not `arityVaries`: its directions are `arityB a ⊕ PEmpty`, and no
isomorphism is constructed.

The result is syntactic: it bounds what the constructions produce on the nose,
not up to isomorphism of the interpreted functors. Obligation 6 expects to
derive the transport of `HasBijectiveReindex` along an isomorphism from
`pshHomEquivNatFamily`, but needs composition on `PshHom`, which the prototype
does not build (`idPshHom` supplies the identity). That is proof obligation 2.

### The two features of `δ` are orthogonal, and the fused rule has both

An arity varying over the output object and a continuation depending on the
decoding are independent: the recursion does not by itself reach past the
bound.

`deltaRec` is the construction that shows this; the code system does not use
it, and it belongs to the bound rather than to the rules. *Inference, not
elaborated*: regrouping `IR.delta`'s coproduct over assignments by the decoding
each induces presents it as a coproduct, over the decodings `PshMor G D`, of
non-recursive `δ`s at the corresponding fibre arity (`fibreArity`, whose
closure under restriction is exactly the decoding's naturality). It needs no
new functoriality proof, being built from `coprod` and `delta`. Its adjoined
arity is constant over the output, so it lies inside the same bound as
`deltaConst` (`hasBijectiveReindex_deltaRec`).

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
the output-varying arity: at the terminal decoding the fused `δ` at an
output-varying arity still lies outside the bound.
`subsingleton_pshMor_to_terminal` states the degeneracy in general; the
prototype does not instantiate it at `termPsh`, so the witness rests on the
construction rather than on that lemma. `deltaCodeVaries` is a *code* whose
interpretation is that functor (`interp_deltaCodeVaries`, itself definitional),
so `not_hasBijectiveReindex_interp_deltaCodeVaries` states the conclusion about
the code system rather than about the operations.

### Why no inductive-inductive definition is needed

A code's `δ` cannot mention its subcode's shapes, so its arity is indexed by
output objects (`BaseArity`) and pulled back along the shape-output map
(`BaseArity.pullback`, `BaseArity.isFunctorial_pullback`). The transport that
the pullback carries is the reason `ShapeArity` is indexed by shapes rather
than by output objects: `deltaData` is then free of it.

Nor does the recursion force mutuality. *Inference, not elaborated*, being the
collapse of § The setting is indexed induction-recursion, not
induction-recursion again: a continuation depending functorially on the
decoding is one code over `ElObj (decPresheaf A hA D)`, not a family of codes
indexed by decodings — the same step `σ` already makes. So `δ`, like `σ`, has a
single subcode slot at a base the shape determines.

The code type is the W-type of a slice polynomial functor on `Cat`
(`codePFunctor`, `Code`), not an inductive family. `Cat.{v, u}` is closed under
both continuation steps, `CodeNext` being the witness: the category of elements
of a presheaf valued in `Type u` over a base in `Type u` is again in `Type u`
(`ElObj`), with homs a subtype of the base's (`elCategory`). The fibre is
therefore recovered by a projection out of an ordinary W-type, and nothing is
defined simultaneously with anything else. This answers negatively the question
of whether codes must be encoded to work around Lean's lack of
inductive-inductive types, and it avoids the route Remark 3.4 of
[GhaniNordvallForsbergMalatesta2015] describes and declines.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature when
transcribing.

No discrete analogue named in a `Status` cell below is an elaborated
identification: each names the declaration occupying the corresponding role
over a discrete base, and nothing relates the two. The `iotaPresheaf` row is
the sharpest case — the prototype's `iotaDiscreteShapeEquiv` docstring
explicitly declines the identification with `IR.toSlicePFunctorIota`, the two
being at different universe instantiations.

| Definition | Status |
| --- | --- |
| `PshHom`, to be named `PresheafPFunctor.Hom` upstream | Novel in this repository. The shapes-forward arities-backward form is Definition 7 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (morphisms of indexed containers) in the discrete case; its Definition 6 is the dependent-polynomial presentation of morphisms; the `r`/`q` naming this repository follows comes from the `(r, t, q)` triples of its Definition 1, this repository absorbing `t` into the dependent family `B` |
| The action of a `Hom`, and its naturality | Novel |
| The representation theorem (`pshHomEquivNatFamily`) | Novel at this level. Its discrete analogue is Theorem 1 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (which that paper states as "Theorem 1 ([13] Theorem 2.12)", its [13] being the 2010 arXiv version of [GambinoKock2013]; whether the numbering 2.12 survives into the 2013 journal article is unchecked), together with Definition 7 for the indexed-container form. Theorem 3 of the same paper is the code-level statement, present as `IR.interpHomEquiv`, and is the analogue of proof obligation 10, not of this |
| Identity, composition, and the category structure on `Hom` | Novel |
| The `σ` / `δ` code rules | Transcription of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013], generalized from families to presheaves: `σ`'s family over a set becomes a base change along a category of elements, and `δ`'s sections `(p : P) → D (i p)` become `PshMor`. The further generalization of `δ`'s arity from an object of `Set/I` to one varying over the output object is novel, and § Why `δ`'s arity must vary over the shape presheaf shows it is forced |
| The `ι` code rule | Transcription of small induction recursion's `ι : O → IR I O`, generalized by replacing equality with a morphism: its interpretation sends `o'` to `o' = o`, and `iotaCode 𝔹 j₀` denotes `iotaPresheaf j₀`, which sends `j'` to `Hom(j', j₀)`. `iotaDiscreteShapeEquiv` records that the two agree over a discrete base, and `iotaPresheafData_A_eq_iotaConstData_yoneda` that the shape presheaf is `yoneda.obj j₀` on the nose |
| Indexing the code type by a base category, with `σ` replacing it by a category of elements | Novel |
| `coprod`, the coproduct of a type-indexed family | Novel at this level; the discrete analogue is `SlicePFunctor.coprod` |
| `unitPsh`, the unit | Novel at this level; the discrete analogue is `SliceDomPFunctor.representable` at the empty direction type |
| `delta`, adjoining an arity | Novel at this level; the discrete analogue is `SliceDomPFunctor.prodSlice` against a representable |
| `sigmaPsh`, the base change along `ElObj S → J` | Novel. It has no discrete analogue in this repository: over a discrete base the category of elements is discrete, so the base change is expected to collapse into `SlicePFunctor.coprod`; open question 5 leaves the discrete degeneration open and nothing establishes this |
| `DomArity` — a presheaf on `I`, unbundled | Novel presentation of a standard object, chosen so its directions plug into a `PresheafPFunctorData`'s without transport |
| `ShapeArity`, `ShapeArity.const` — the arity a `δ` adjoins, varying over the shape presheaf | Novel; it is the unbundled data of a functor `el(T₁)ᵒᵖ ⥤ (Iᵒᵖ ⥤ Type)`. `const` is the case Section 6's `δ` arity occupies |
| `BaseArity`, `BaseArity.pullback` — the arity indexed by output objects, and its pullback along `q` | Novel |
| `ElObj`, `elCategory` — the category of elements as a base category | Transcription of the category of elements, [MacLaneMoerdijk1992] Chapter I; in mathlib it is `S.Elementsᵒᵖ`, written out here to avoid `Opposite` transport, and obligation 4 revisits the choice |
| `HasBijectiveReindex` | Novel; the property that every reindexing map is a bijection. That this is cartesianness of `objPresheaf`'s fibres over the shape presheaf is an unelaborated reading |
| `CodeShape`, `CodeDir`, `CodeNext`, `codePFunctor`, `Code` | Novel. Indexing by a base category, with `σ` replacing it by a category of elements, has no counterpart in the cited literature |
| `codeAlgOn`, `codeAlg`, `interp` — the interpretation | Novel at this level; the discrete analogue is `IR.interpObj` |
| The constant-arity fragment's code type (obligation 7) | Novel |
| The code-level morphism type (obligation 10) | Novel at this level; the discrete analogue is `IR.Hom` |
| The p.r.a. formula `T Z ≃ Σ a, Hom(E(a), Z)` (`objEquivSigmaArityHom`, bundled as `objEquivSigmaHom`) | Transcription: the familial presentation of a parametric right adjoint, [Weber2007]; novel only in being stated with the hom unbundled |
| `shapePresheaf`, `arityPresheaf` — `T₁` and each `E(a)` as functors | Transcription: the familial presentation of [Weber2007] |
| `SliceHom`, `sliceHomApp` — the slice-level morphism formula | Transcription of Definition 7 of [HancockMcBrideGhaniMalatestaAltenkirch2013] at a discrete base; retained in the prototype as the derivation and ported by nothing |
| `Functoriality` — the witness family attached over pre-codes | Novel; retained in the prototype as the derivation and ported by nothing |
| `ArityHom` — the unbundled presheaf hom `E(a) ⟶ Z` | Novel presentation of a standard object, chosen to avoid the functor category's `Classical.choice` |
| `ShapeHom` — the unbundled presheaf hom `T₁ ⟶ T₁'` | Novel presentation, as `ArityHom` |
| `ObjFib`, `objFibRestr`, `objFibMap` — the output presheaf's fibres and their two actions, unbundled | Novel presentation. They are `objPresheaf`'s and `mapPresheaf`'s components; obligation 1 states the interpretation against those directly |
| `PshNatFamily` — the natural families a `PshHom` represents | Novel; obligation 3 relates it to natural transformations of the interpreted functors |
| `DomHom`, `DomNatFamily` — the domain-level morphism data and its natural families | Novel. The domain-level warm-up for `PshHom`, superseded by it; retained in the prototype as the derivation and ported by nothing |
| `iotaPresheaf`, `iotaConst` — the constant functors at a representable and at an arbitrary presheaf | Novel at this level; the discrete analogue of the first is `IR.iota` |
| `sigmaLiftHom` — the morphism of elements a `σ` restricts along | Novel |
| `elEqToHom` — the transport in the category of elements with a definitionally reducing underlying morphism | Novel; a presentational device, `elEqToHom_eq` identifying it with `eqToHom` |
| `Interp` — the interpretation's target, a functor paired with its base | Novel |
| `arityHomEquivNatTrans` — the bundling isomorphism `ArityHom ≃ (arityPresheaf ⟶ Z)` | Novel; it is the elaborated form of the `ArityHom` row's identification |
| `arityPresheafHomAtUB`, `arityPresheafHomULifted` — the universes at which the bundled hom is formable | Novel; retained in the prototype as the derivation and ported by nothing |
| `iotaDiscreteShapeEquiv`, `arityVariesShapeEquiv` — the discrete collapse of `iotaPresheaf`'s shape type, and the terminality of `arityVaries`'s shape presheaf | Novel; retained in the prototype as the derivation and ported by nothing |
| `genericFib`, `idElt`, `ofSigmaFib`, `reindexArityHom`, `pshHomSigma`, `domHomSigma` — the fibre-level intermediates of the representation theorem | Novel presentations; those the theorem needs travel with obligation 1, the rest are retained derivation |
| `arityB`, `arityVariesData`, `arityVaries`, `arityVariesShapeArity`, `deltaVarying`, `termPsh`, `arityVariesBase`, `decUnit`, `deltaFusedVaries`, `deltaCodeVaries` — the witnesses of § Why `δ`'s arity must vary over the shape presheaf | Novel. Fixtures, carrying no mathematics beyond the theorems they witness |
| `PshMor` — a morphism from a `DomArity` to a presheaf, unbundled | Novel presentation; it is the presheaf reading of Section 6's sections `(p : P) → D (i p)` |
| `fibreArity` — the arity a decoding adjoins | Novel |
| `deltaRec` — the `δ` whose continuation depends on the decoding, at an arity constant over the output | Transcription of Section 6's `δ` rule, generalized from families to presheaves as the `δ` code rule row describes: its subcodes are indexed by `PshMor`, not by sections. A semantic operation, where Section 6's `δ` is a code rule |
| `decPresheaf` — the decodings of an output-varying arity, as a presheaf on the output base | Novel |
| `decArity` — that arity, indexed by the elements of `decPresheaf` | Novel |
| `deltaFused` — the `δ` carrying both features. Its output-varying arity is witnessed by `not_hasBijectiveReindex_deltaFusedVaries`; its decoding-dependence is by construction, and no theorem relates it to `deltaRec`, whose decoding-dependence is the same construction at a constant arity. Supplying that relation is not an obligation of this workstream | Novel; it is Section 6's `δ` rule with the arity generalized as § Why `δ`'s arity must vary over the shape presheaf requires |

## Branches

[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape binds one concern
per branch. The ten obligations below divide into six. W-f is separate because
nothing in W-a to W-c or W-e consumes the collapse: for them it justifies the
input-side design rather than being used by it. W-d does consume it, as
obligation 8 states.

| Branch | Obligations | Acceptance |
| --- | --- | --- |
| W-a — Stage 1 upstream | 1, 2, 3 | `PshHom`, its action and the hom-set bijection in `Geb/Mathlib/`, choice-free, with the bundled restatements and the natural-transformation identification in a module on `GebMeta.classicalAllowedModules`; composition and the category structure; and `docs/index.md` entries |
| W-b — Stage 2 upstream | 4, 5 | the semantic operations, the decoding layer, the code type, the interpretation, and the bound's vocabulary, in `Geb/Mathlib/`, each new module carrying its `docs/index.md` entry |
| W-c — the bound | 6, 7 | `HasBijectiveReindex` transports along an isomorphism, and the constant-arity fragment's code type and induction are built, in `Geb/Mathlib/`, with `docs/index.md` entries |
| W-d — completeness | 8 | either, for every `PresheafPFunctor` out of `ElObj D` at the universes `CodeShape` pins, a code whose interpretation is isomorphic to it, or a counterexample, in `Geb/Mathlib/`, with `docs/index.md` entries. Characterising a class over which completeness does hold is not this branch's acceptance: if the conjecture fails, the branch delivers the counterexample and records the characterisation as follow-on work in `TODO.md` |
| W-e — code morphisms | 10 | the code-level morphism type and representation theorem, in `Geb/Mathlib/`, with `docs/index.md` entries |
| W-f — the collapse | 9 | `PSh(𝕀)/D ≃ PSh(el(D)ᵒᵖ)` in `Geb/Mathlib/`, in a module on `GebMeta.classicalAllowedModules`, with its `docs/index.md` entry |

W-a and W-b depend on nothing; W-c depends on W-a and W-b; W-d depends on W-a,
W-b and W-f; W-e depends on W-a and W-b. W-f depends on nothing.

Each acceptance cell's "in `Geb/Mathlib/`" carries the repository's standing
practice for that subtree: a `GebTests/Mathlib/` mirror per new module, which
79 of the 80 existing `Geb/Mathlib/` modules have, and which
`GebMeta.classicalAllowedModules`' own docstring requires of any module a
branch adds to that allowlist ("Feature branches append their own wrapper
module names together with their test parallels"). W-a and W-f each add one
such module — W-a's carrying obligation 1's `functor`-form corollary and
obligation 3's identification together, as its acceptance cell says — so each
adds one allowlist pair.

`docs/index.md` describes some directories module by module, others by a single
directory bullet, and several — `Data/PFunctor/Presheaf/` and
`Data/PFunctor/IndRec/` among them — by a directory bullet plus per-module
bullets for later additions. A branch adding to a directory that already has a
bullet adds per-module bullets beneath it; a branch creating a directory writes
the directory bullet.

This document is the design record for all six and is removed with the last of
them, which deviates from § Concern shape's per-branch spec lifetime. The
rationale: between branches it presents decisions that are pending, not
superseded, which is what that section guards against. If W-a lands and the
rest are deferred, the deviation is to be resolved by moving the design record
into `docs/` as persistent documentation rather than leaving a spec on `main`.

## Proof obligations

Each is unproved at the time of writing.

1. **Stage 1 at upstream quality** (W-a). Port `PshHom`, its action, and
   `pshHomEquivNatFamily` from the prototype into `Geb/Mathlib/`, together with
   what they rest on: `shapePresheaf` and `arityPresheaf`, `ArityHom`,
   `ShapeHom`, `objEquivSigmaArityHom` with `ofArityHomElt` and
   `value_ofArityHom`, `reindexArityHom`, `sigmaArityHom_ext`, `idArityHom`,
   `natTransOfArityHom`, `postcompArityHom`, `map_symm_arityHom`, `idPshHom`,
   `PshNatFamily`, and the round-trip lemmas `natFamily_generic`,
   `natFamilyPshHom`, `objFibMap_eq_objFibRestr_apply`,
   `natFamilyArity_pshHomFamily` and `pshHom_ext`. This port is
   dependency-closed on the same grounds as obligation 4's: anything a listed
   item needs travels with it. Port it against the choice-free `objPresheaf`
   and `mapPresheaf` rather than `PresheafPFunctor.functor`, and drop the
   prototype's parallel `ObjFib` / `objFibRestr` / `objFibMap` layer entirely:
   `ObjFib` is `objPresheaf`'s object part at `j.unop` and the two actions are
   `objPresheaf.map` and `mapPresheaf.app` verbatim, so nothing of it survives
   the replacement. The `functor` form is a corollary and belongs in a module
   on `GebMeta.classicalAllowedModules`, together with `arityHomEquivNatTrans`
   and `objEquivSigmaHom`, the prototype's two bundled restatements. The ported
   chain needs `PresheafPFunctor.value_objRestrElt`, which is `private` in
   `Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean` and which the prototype
   restates locally; this obligation decides between dropping the `private` and
   shipping a restatement.
2. **Category structure** (W-a). Composition on `PshHom` (`idPshHom` already
   supplies the identity), that composition is associative with that identity
   as unit, and that the bijection of obligation 1 carries them to the
   identities and composition of natural transformations. Full and faithfulness
   of the interpretation is delivered by this obligation and obligation 3
   jointly, not by obligation 1: the predicate is not even well-formed until
   obligation 3 identifies `PshNatFamily` with natural transformations. Depends
   on obligation 3.
3. **The natural-transformation identification** (W-a). That `PshNatFamily`,
   the unbundled proxy `pshHomEquivNatFamily` lands in, is equivalent to the
   natural transformations `F.functor ⟶ F'.functor`. The prototype relates
   `PshNatFamily` to nothing outside `Basic.lean`. Its statement writes `⟶` in
   a functor category, so the deliverable belongs in a module on
   `GebMeta.classicalAllowedModules`, as obligations 1 and 9's choice-dependent
   halves do.
4. **Stage 2 at upstream quality** (W-b). Port `iotaPresheaf`, `sigmaPsh`,
   `delta`, `coprod`, `PshMor`, `fibreArity`, `decPresheaf`, `decArity`,
   `deltaFused`, the code type and the interpretation, together with the
   structures and lemmas they rest on: `DomArity` with the discrete-fibration
   identification `presheaf`, `ofPresheaf`, `isFunctorial_ofPresheaf`,
   `dirEquivOfPresheaf`, `dirEquivOfPresheaf_restr` and `sigmaDirEquivCarrier`;
   `ShapeArity`, `ShapeArity.const` and `ShapeArity.isFunctorial_const`;
   `BaseArity` with `pullback`, `isFunctorial_pullback`, the three lemmas that
   reduction needs (`reindex_eqToHom`, `reindex_comp_apply`,
   `reindex_cast_shape`) and the fibration layer `isFunctorial_fam`,
   `famPresheaf` and `reindexHom`; `ElObj` / `elCategory` with
   `elCategory_id_val`, `elCategory_comp_val` and `elCategory_eqToHom_val`;
   `sigmaLiftHom`, `elEqToHom` and `elEqToHom_eq`; `isFunctorial_fibreArity`
   and `fibreArity_restr_val`; `isFunctorial_decArity` and
   `decArity_reindex_val`; `delta_cast_inl` and `delta_cast_inr`; the three
   code constructors `iotaCode`, `sigmaCode` and `deltaCode` with their
   computation rules `interp_iotaCode`, `interp_sigmaCode`, `interp_deltaCode`
   and `interp_fst`, which nothing else in this obligation's list depends on,
   so the closure clause does not reach them, and which obligation 5's
   `deltaCodeVaries` and obligation 8's expected witness both need; the five
   `σ` laws (`sigmaPsh_shapeRestr_id`, `_shapeRestr_comp`,
   `_reindex_naturality`, `_reindex_id`, `_reindex_comp`) with the transport
   lemmas they use (`elObj_eq_of_hom`, `elHom_eq_eqToHom_comp`,
   `shapeRestr_eqToHom`, `cast_shape_val`, `shapeRestr_val_eqToHom_comp`,
   `reindex_heq_congr_shape`, `reindex_heq_eqToHom`, `reindex_eq_of_eq_comp`,
   `reindex_eq_of_eq_eqToHom_comp`); and `Interp`. The port is to be
   dependency-closed: anything a listed item needs travels with it, since
   [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md) §
   Subtree import rules forbids `Geb/Mathlib/` importing `Geb.Internal.*`.
   `deltaRec`, `subsingleton_pshMor_to_terminal`, `unitPsh` and `unitPshData`
   belong to the bound rather than to the rules, and are ported by obligation 5
   instead; the code system itself does not use them. The prototype's `ElObj` /
   `elCategory` is written out rather than reused; the upstream version should
   be `S.Elementsᵒᵖ`. Acceptance for that choice: reuse is adopted unless it
   requires more transport and projection lemmas than the seven the written-out
   version needs: `elObj_eq_of_hom`, `elHom_eq_eqToHom_comp` and `elEqToHom_eq`
   at explicit call sites, the `def` `elEqToHom` they are stated about, and the
   three `@[simp]` projection lemmas `elCategory_eqToHom_val`,
   `elCategory_id_val` and `elCategory_comp_val`, of which only the first has
   an explicit call site; whether the other two fire is to be confirmed when
   the count is taken.
5. **The bound's vocabulary at upstream quality** (W-b). Port
   `HasBijectiveReindex`; the three generators' cases and four operations'
   cases, together with the general `hasBijectiveReindex_delta` that
   `hasBijectiveReindex_deltaConst` and `hasBijectiveReindex_deltaRec` both
   rest on, and `deltaRec` with `hasBijectiveReindex_deltaRec`, which is the
   fragment's decoding-indexed operation case, and
   `subsingleton_pshMor_to_terminal`, whose port is conditional on its being
   instantiated at `termPsh` so that the witness rests on it; if it is not, it
   is dropped rather than landed dead; the three negative theorems
   `not_hasBijectiveReindex_arityVaries`,
   `not_hasBijectiveReindex_deltaVarying` and
   `not_hasBijectiveReindex_deltaFusedVaries`; and the witnesses they need —
   `iotaPresheaf`, `iotaConst`, `arityVaries`, and `arityVariesShapeArity` with
   `isFunctorial_arityVariesShapeArity` as `deltaVarying`'s arity,
   `deltaVarying` with `deltaVarying_source_empty`, and `termPsh`,
   `arityVariesBase`, `isFunctorial_arityVariesBase`, `decUnit`,
   `decVariesElt`, `deltaFusedVaries`, `deltaCodeVaries` with
   `interp_deltaCodeVaries` and
   `not_hasBijectiveReindex_interp_deltaCodeVaries`, and the underlying
   `arityB`, `arityVariesData`, `iotaPresheafData`, `iotaConstData`,
   `subsingletonIotaDirection`, `subsingletonIotaConstDirection`,
   `subsingletonArityB`, `subsingletonArityVariesDirection`,
   `arityVariesShapeArity_dir_ext` and `arityVariesBase_dir_ext`. (`unitPsh`
   and `unitPshData` belong here rather than to obligation 4: the code system
   no longer denotes them, and what still needs them is this obligation's
   fragment vocabulary and the `arityVaries` fixtures.) `shapePresheaf` is
   ported by obligation 1 beside `arityPresheaf`, not here; obligation 8's
   expected witness needs it, so W-d depends on W-a as well as W-b. Obligations
   6 and 7 consume these, and
   [docs/rules/upstream-eligible.md](../../rules/upstream-eligible.md) §
   Subtree import rules forbids `Geb/Mathlib/` from importing `Geb.Internal.*`,
   so without this obligation W-c has no inputs whether or not the prototype
   still exists.
6. **Iso-invariance of the bound** (W-c). That `HasBijectiveReindex` transports
   along an isomorphism of interpreted functors, upgrading
   `not_hasBijectiveReindex_arityVaries` from a syntactic to a semantic
   statement. Depends on obligations 2 and 5.
7. **The fragment induction** (W-c). A code type for the constant-arity
   fragment as § Why `δ`'s arity must vary over the shape presheaf defines it —
   including the decoding-indexed `δ`, so the fragment's code type carries a
   subcode family indexed by `PshMor`, not the single subcode the adopted rules
   use — and the induction over it showing every code it admits denotes a
   functor with bijective reindexing. The three base cases and four step cases
   are proved in the prototype and ported by obligation 5; only the induction
   is missing.
8. **Completeness** (W-d). Whether every `PresheafPFunctor` over the
   interpretation's own input base — `interp` lands in `Σ 𝔹, PresheafPFunctor
   (ElObj D) 𝔹`, so the question is about functors out of `ElObj D` at the
   universes `CodeShape` pins, not about `PresheafPFunctor` at large — has a
   code, up to isomorphism of the interpreted functors. On the nose it is
   refutable by inspection: `sigmaPshData` keeps the subfunctor's shape type
   and drops only the `ElObj`-component of its shape-output map, so the
   expected witness's shape presheaf at `j` is the decodings paired with the
   target's shapes, not the target's shapes. The analogue is Lemma 1 of
   [HancockMcBrideGhaniMalatestaAltenkirch2013] ("Every dependent polynomial
   functor is an IR functor"). The shape of the expected witness is `sigmaCode`
   at the shape presheaf over a `deltaCode` at the arity over `iotaCode`; that
   this reconstructs an arbitrary functor is conjecture, not elaboration. That
   `deltaCode`'s arity is where W-f enters: `BaseArity` carries `fam : 𝔹 →
   DomArity I` over the fixed input base `I`, while an arbitrary target's arity
   lives over `ElObj D`, so re-presenting the one as the other is a direction
   of the collapse, and W-d depends on W-f as well as on W-a and W-b. If the
   conjecture is false, the branch delivers the counterexample. What
   completeness then holds of is for that branch to determine; the natural
   candidate is the functors whose arity is constant on each connected
   component of `el(T₁)`, but nothing here argues it, and "fragment" in that
   sense is a class of functors, not the class of codes § Why `δ`'s arity must
   vary over the shape presheaf names.
9. **The collapse** (W-f). The equivalence `PSh(𝕀)/D ≃ PSh(el(D)ᵒᵖ)`, which the
   § The setting is indexed induction-recursion, not induction-recursion
   section marks as an inference, and on which the input-side design, the
   no-mutuality argument of § Why no inductive-inductive definition is needed,
   and open question 2 all rest. In mathlib it is the composite of
   `overEquivPresheafCostructuredArrow` and
   `CategoryOfElements.costructuredArrowYonedaEquivalence`, the second
   transported through the presheaf construction before the two compose. Both
   name functor-category instances and so depend on `Classical.choice`, and the
   deliverable therefore belongs in a module on
   `GebMeta.classicalAllowedModules`.
10. **Code morphisms** (W-e). The code-level morphism type, mirroring `PshHom`,
    and the code-level representation theorem — the analogue of Theorem 3 of
    [HancockMcBrideGhaniMalatestaAltenkirch2013], present in the discrete case
    as `IR.interpHomEquiv`. Stage 1 determines the shape of both.

## Open questions

To be answered by the work rather than before it.

1. Whether the universes the code type pins need to vary. `CodeShape` puts the
   input base and the decoding presheaf, the `σ`-presheaf's values, the
   `δ`-arity's carrier, and `Cat.{v, u}`'s object universe all at `u`, and the
   input base's homs at `u` as well. Taking the pointed `ι` as a primitive rule
   rather than deriving it costs one universe and no more: `Interp`'s shape
   universe is `max u v`, because a representable's shape type is the total
   space of a hom-family. Deriving it instead, by `σ` at a representable over
   an unpointed `ι`, would have needed `v = u` or a `ULift`, since `yoneda.obj
   j₀ : 𝔹ᵒᵖ ⥤ Type v` cannot fill the `σ` rule's `𝔹ᵒᵖ ⥤ Type u`. The same
   total-space bump appears in `DomArity.ofPresheaf`, so it is a property of
   fibre-families in this development rather than of the `ι` rule. The pinning
   is what makes `Cat.{v, u}` closed under both continuation steps.
2. Whether the output side should also carry a decoding presheaf `E`, as
   Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013] does. The
   prototype's output index is a bare category, which by the collapse of § The
   setting is indexed induction-recursion, not induction-recursion already
   subsumes a pair `(𝕁, E)` at `el(E)ᵒᵖ`; whether the syntax gains from naming
   `E` separately is not settled.
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
6. A source, with a searchable identifier, for the embedding of `Fam(C)` in
   presheaves as the coproducts of representables, and for its fullness. The §
   Non-goals section invokes it in passing; nothing in the workstream depends
   on it.

7. Whether `σ` needs its index to be a category and its subcodes a functor into
   the codes, interpreted by a Grothendieck construction, rather than a
   presheaf with a single subcode over `el(S)`. The present rule is more
   general than small `IR`'s in one direction — `S` varies over the output
   object where small `IR`'s is a constant set — and less general in another:
   one code over a larger base has shapes and arities that may vary with `s`,
   but a code tree that may not, so `σ Bool (fun b ↦ if b then ι x else δ …)`
   has no evident image. Whether that is a restriction is undetermined: `δ`'s
   arity varies over the output object, so over a base like `𝔹 ⊔ 𝔹` a single
   `δ` may be empty on one side and inhabited on the other, which is what
   distinguishes a nullary constructor from a recursive one. The question is
   settled by building a datatype with two constructors of different arity in
   the prototype and seeing whether a uniform code tree suffices. If it does,
   non-uniform constructors come from output-varying data and the rule stands;
   if it does not, `CodeDir` must return a non-trivial type at `σ` and the
   codes stop being a W-type with at most one subcode per node.

## Non-goals

- Positive inductive-recursive definitions over `Fam(C)`
  ([GhaniNordvallForsbergMalatesta2015]). They meet the full-and-faithfulness
  requirement, on the reading recorded in § Motivation, only by Remark 3.4's
  route, defining the interpretation simultaneously with the codes; the
  presheaf setting obtains it structurally. If wanted they are better recovered
  inside the presheaf construction, since `Fam(C)` embeds in presheaves as the
  coproducts of representables — an embedding this document neither establishes
  nor cites to a source, and whose fullness the recovery would need. Locating a
  source for it is recorded as open question 6, not as an obligation: nothing
  in the workstream depends on it.
- Initial algebras of the interpreted functors. `IR`'s are not constructed
  either; the set-theoretic model of [DybjerSetzer1999] justifies their
  existence using a Mahlo cardinal. [GhaniNordvallForsbergMalatesta2015] § 7
  attributes it there: "We briefly revisit the initial algebra argument used by
  Dybjer and Setzer [DS99]".
- Uniqueness of the interpretation fold.
  `Geb/Mathlib/Data/PFunctor/Slice/W.lean` establishes only the existence half
  of the initial-algebra universal property, and this workstream inherits that.

## Notes

`docs/references.bib`'s note on `HancockMcBrideGhaniMalatestaAltenkirch2013` is
wrong, not merely narrow. It claims the extended preprint "renumbers two of"
the results this repository cites. Checked against the preprint, the preprint
numbers Definitions, Examples, Lemmas, Theorems and Corollaries in one shared
sequence, where the proceedings number each kind separately. Definitions 1 to 4
are unaffected, being the first four numbered items in both; everything from
the proceedings' Example 1 onward shifts, because the preprint's counter
absorbs the examples. Across every numbered result this repository cites or a
branch of this workstream will cite — Corollary 4 being cited only by the
transient handoff, and Definitions 6 and 7 and Theorem 1 only prospectively —
the proceedings' Definition 2, Definition 3, Definition 5, Definition 6,
Definition 7, Definition 8, Example 1, Lemma 1, Lemma 2, Lemma 3, Lemma 4,
Theorem 1, Theorem 2, Theorem 3, Theorem 4, Corollary 2 and Corollary 4 are the
preprint's Definition 2, Definition 3, Definition 8, Definition 10, Definition
11, Definition 17, Example 5, Lemma 7, Lemma 9, Lemma 14, Lemma 16, Theorem 12,
Theorem 15, Theorem 18, Theorem 21, Corollary 19 and Corollary 22. Example 1 is
cited by `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean`, its test module and
`docs/index.md:402`. No branch of this workstream touches the first two, and
each branch adds to `docs/index.md` without touching that line, so that
citation's correction is independent of the ordering constraint below. The
existing note covers Definition 8, Theorems 2, 3 and 4 and Corollary 2. Of the
results it does not, the repository's most-cited are Lemma 4 (62 occurrences
over 7 files, the most-cited outright), Lemma 3 (14 over 5) and Definition 5
(13 over 2). Definition 5 is cited in
`Geb/Mathlib/Data/PFunctor/IndRec/Slice.lean` and its test mirror; Lemma 3 in
`Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`,
`Geb/Mathlib/Data/PFunctor/IndRec/{Basic,Naturality}.lean`, one test mirror and
`docs/index.md`; Lemma 4 in
`Geb/Mathlib/Data/PFunctor/IndRec/{Basic,Category,Naturality}.lean`, their
three test mirrors and `docs/index.md`, `Category.lean` being its largest
single consumer. A key-only search under-scopes both, as it does the author
order below. One collision deserves recording on its own: the preprint's
Definition 8 is the proceedings' Definition 5, while the proceedings'
Definition 8 is the preprint's Definition 17, so a reader who does not know
which numbering a citation uses lands on the wrong statement. Section numbering
is unchanged, though the preprint adds numbered subsections the proceedings
runs in. The preprint is not merely a renumbering: it carries a different title
and a different author order, so the key
`HancockMcBrideGhaniMalatestaAltenkirch2013` names the proceedings version
alone, and its Corollary 19 states more than the proceedings' Corollary 2.
Correcting and extending the note is recorded in [TODO.md](../../../TODO.md) §
Citation corrections deferred to their own branch, and must land before
whichever branch first cites an uncovered result — W-a for Definitions 6 and 7
and Theorem 1, W-d for Lemma 1, W-e for Theorem 3. W-b cites the `δ` rule by
section, and section numbering is unchanged, so W-b is unconstrained. That
ordering constraint is recorded in `TODO.md` too, this document being removed
with the last branch.

The author order of `GhaniNordvallForsbergMalatesta2015` in
`docs/references.bib` is wrong. The published LMCS byline is Ghani, Malatesta,
Nordvall Forsberg, and so is the arXiv preprint's. What the entry and the
citation key encode is the metadata order — what arXiv's listing, the LMCS
landing page and the DOI record `10.2168/LMCS-11(1:13)2015` all return — which
disagrees with the byline of either PDF. A reviewer of the correction branch
who checks the DOI record alone will find the present entry matches it, so the
correction cites the article itself. It is pre-existing. Four persistent
modules carry the key — `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
and `Geb/Mathlib/Data/PFunctor/IndRec/{Basic,Functor,Universes}.lean` — besides
`docs/references.bib`, `TODO.md`, this spec, the transient prototype and the
transient handoff. The repair surface is larger than the key count:
`docs/index.md` spells the wrong order out in prose at three places without
using the key, so a key-only search under-scopes the branch. It is deferred to
its own branch per one concern per branch, recorded in `TODO.md`.

## References

Each key is cited in the body above; the bibliographic detail lives in
[docs/references.bib](../../references.bib).

- [GhaniNordvallForsbergMalatesta2015] — positive inductive-recursive
  definitions; Remark 3.4 on the choice of morphism collection, and Section 2
  on the loss of full and faithfulness over `Fam(C)`.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] — small induction recursion;
  Section 6 for `IIR`, Definition 1 for the `(r, t, q)` presentation of
  dependent polynomials, Definition 6 for morphisms of dependent polynomials,
  Definition 7 for morphisms of indexed containers, Theorem 1 for the discrete
  representation theorem, Theorem 3 for the code-level full-and-faithfulness
  statement, Lemma 1 for completeness.
- [Weber2007] — parametric right adjoints and familial functors.
- [nLabParametricRightAdjoint] — the presentation of presheaf p.r.a. functors
  as the polynomials `I ← E → K → J` in `Cat` whose last leg is a discrete
  fibration and whose first two form a two-sided discrete fibration, which is
  what fixes the shape and arity data.
- [MacLaneMoerdijk1992] — the category of elements.
- [GambinoKock2013] — polynomial functors. The result
  [HancockMcBrideGhaniMalatestaAltenkirch2013] restates as its Theorem 1 is
  numbered 2.12 in the 2010 arXiv version it cites; whether that numbering
  survives into the 2013 journal article this key names is unchecked.
- [DybjerSetzer1999] — inductive-recursive definitions.
