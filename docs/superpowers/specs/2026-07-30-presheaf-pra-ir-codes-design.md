# Codes for presheaf p.r.a. functors

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Motivation](#motivation)
- [Two prior generalizations, on independent axes](#two-prior-generalizations-on-independent-axes)
- [Prototype findings](#prototype-findings)
- [Design](#design)
  - [Semantic target](#semantic-target)
  - [Stage 1: codes over `Fam(C)`](#stage-1-codes-over-famc)
  - [Stage 2: codes over presheaf categories](#stage-2-codes-over-presheaf-categories)
- [Definitions: transcription or novel](#definitions-transcription-or-novel)
- [Proof obligations](#proof-obligations)
- [Non-goals](#non-goals)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Spec for a generalization of the `IndRec` code system from slice
polynomial functors to presheaf parametric-right-adjoint functors.

## Scope of this document

This is a brainstorming-phase spec: it fixes the design, the staging, and
the proof obligations. It does not fix the implementation order; that is
the plan's concern. Per
[CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape, this file and
its plan are transient and are removed in the final commits of the topic
branch.

## Motivation

`IR.toSlicePFunctor` translates an `IR` code to a
`SlicePFunctor I O`, a functor `Type/I → Type/O`
([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 2 / Definition 5),
and `IR.sliceCode` translates back (Lemma 1). The repository also has
`PresheafPFunctor I J`, a parametric right adjoint
`(Iᵒᵖ ⥤ Type) → (Jᵒᵖ ⥤ Type)` for categories `I` and `J`, which
degenerates to `SlicePFunctor` when `I` and `J` are discrete. No code
system denotes those functors. This spec designs one.

## Two prior generalizations, on independent axes

Dybjer–Setzer inductive-recursive definitions
([DybjerSetzer1999], [DybjerSetzer2003]) describe functors
`Fam(D) → Fam(D)` for a set `D`. Two published generalizations move in
different directions.

| Work | Direction generalized | Cost |
| --- | --- | --- |
| [HancockMcBrideGhaniMalatestaAltenkirch2013] | Smallness, yielding the equivalence with dependent polynomials and indexed containers. `IR.Hom` is the homset of the interpreted functors, computed by `IR.elimAlg` on the codomain nested in `IR.elimAlg` on the domain | Definition 8's homset; the identity morphism is not given by the paper and is constructed here as `IR.id` |
| [GhaniNordvallForsbergMalatesta2015] | The decoding target from a set to a category `C`, giving functors `Fam(C) → Fam(C)` | A functoriality witness on the `δ` constructor, and a type of code morphisms defined mutually with the codes |

The axes are independent, and `PresheafPFunctor` sits past both:
`Fam(C)` is the free coproduct completion of `C`, `Iᵒᵖ ⥤ Type` is the
free colimit completion, and the former embeds in the latter as the
coproducts of representables. A presheaf-level code system is therefore
a simultaneous generalization along both axes.

Related work at the semantic level: parametric right adjoints between
presheaf categories are characterized in [Weber2007] and
[nLabParametricRightAdjoint]; [SpivakGarnerFairbanks2021] presents them
as polynomial bicomodules between categories; [Shapiro2021] describes
the data specifying a familially representable monad on a presheaf
category.

## Prototype findings

`Geb/Internal/PresheafIRProto.lean` is throwaway exploration, not
upstream-eligible content. It establishes the following by elaboration.

1. `iotaPresheaf j₀` — the constant functor at the representable
   `y j₀` is a `PresheafPFunctor`, with shape type the total space
   `Σ j', (j' ⟶ j₀)` rather than a single shape. All seven functor laws
   are discharged: the shape-side laws are the category laws of `J`, the
   direction-side laws hold because every direction fiber is empty.
2. `iotaDiscreteShapeEquiv` — for a discrete `J` that shape type is
   equivalent to `PUnit`, recovering `IR.toSlicePFunctorIota`'s single
   shape.
3. `iotaConst P` — the constant functor at an arbitrary presheaf `P` on
   `J` is a `PresheafPFunctor`, with shapes the total space of `P` and
   `shapeRestr` the restriction of `P`. The representable case is the
   `P := yoneda.obj j₀` case: the two shape types are definitionally
   equal.
4. `Functoriality` — the functoriality witness of
   [GhaniNordvallForsbergMalatesta2015]'s `δ` is definable over the
   existing `IR` codes by `IR.rec`, against the existing `IR.Hom`.
5. `arityVaries` — a `PresheafPFunctor (Fin 1) (Fin 2)` whose shape
   presheaf is terminal (every `Shape j` is equivalent to `PUnit`) and
   whose arity is empty at the shape over `0` and a singleton at the
   shape over `1`, so `reindex` along `0 ⟶ 1` is the map out of the
   empty type and is not invertible.

## Design

### Semantic target

`PresheafPFunctor I J`, already in
`Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`. Its operations are a
`SliceDomPFunctor` on the objects of `I` together with `directionRestr`
(arities are presheaves on `I`), `q`, `shapeRestr` (shapes form a
presheaf on `J`), and `reindex` (the arity assignment is functorial on
`el(T₁)`).

### Stage 1: codes over `Fam(C)`

A transcription of [GhaniNordvallForsbergMalatesta2015]. Three
observations reduce the work.

- The pre-codes are the existing `IR` codes. That paper's `ι` carries an
  object of `C`, its `σ` a set with subcodes indexed by it, and its `δ` a
  set with subcodes indexed by `A → C`. At `uA = uB` and up to the
  universe lifts in `IR.Direction`, these are `IR.Shape` and
  `IR.Direction` at `I = O = C₀`. No new code type is required.
- The mutual definition of codes and code morphisms is eliminable. In
  that paper's `δ→δ` constructor the two functoriality witnesses appear
  only as implicit indices and are never used, so the morphism type does
  not depend on them. The witness is therefore attachable after the
  codes, by `IR.rec` against the already-defined `IR.Hom`. This is
  required because [docs/rules/lean-coding.md](../../rules/lean-coding.md)
  § Recursion and induction through recursors forbids an `inductive`
  containing an instance of itself, which the paper's inductive-inductive
  presentation would require.
- `Fam(C)` for a general category `C` is the contravariant Grothendieck
  construction on the family functor. `CoGrothendieck` is in
  `Geb/Mathlib/CategoryTheory/Grothendieck.lean`;
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` covers only the
  discrete case.

New content in this stage: the interpretation into `Fam(C)`, its
morphism part (which consumes the functoriality witness), and the
functoriality witness family.

### Stage 2: codes over presheaf categories

Two changes to the Stage 1 code system.

- `ι` is relaxed from an object of `J` to a presheaf on `J`. The old
  `ι j` is recovered as `ι (y j)`. Prototype finding 3 establishes that
  the semantics of the relaxed constructor exists; finding 1 that the
  representable case is a special case of it. This is what a Lemma-1
  analogue requires: `ι` and `σ` alone generate coproducts of
  representables, and a general shape presheaf is not one.
- A constructor indexed by a presheaf on `J`, with a subcode family
  functorial over `el(P)` and a functoriality witness that is a code
  morphism. This supplies `shapeRestr` and `reindex`.

The second change is forced by prototype finding 5, by the following
argument. In a code system whose constructors are `ι` at a presheaf, `σ`
over a set, and `δ` adjoining a fixed arity, a shape is a path through
the code tree terminating at an `ι` leaf; `shapeRestr` acts only on that
leaf's presheaf component, leaving the tree path, and hence the arity
accumulated from the `δ` nodes along it, unchanged. Every such code
therefore has `reindex` an isomorphism, and none of them denotes
`arityVaries`, whose shape presheaf is terminal. Arity variation is
therefore independent of the shape presheaf.

The two functoriality witnesses are dual: the one on `δ` varies over
input labellings and yields `directionRestr`; the one on the new
constructor varies over `el(P)` and yields `shapeRestr` and `reindex`.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing.

| Definition | Status |
| --- | --- |
| Stage 1 code type | Transcription, [GhaniNordvallForsbergMalatesta2015]; and already present as `IR` |
| Stage 1 functoriality witness | Transcription of that paper's `F→`, in a non-mutual presentation. The non-mutual presentation is novel |
| Stage 1 interpretation into `Fam(C)` and its morphism part | Transcription of that paper's `⟦_⟧IR+` and `⟦_⟧→` |
| `Fam(C)` as a contravariant Grothendieck construction | Transcription; that paper, Remarks 2.3 |
| Stage 2 relaxation of `ι` to a presheaf | Novel |
| Stage 2 constructor indexed by a presheaf on `J`, and its witness | Novel |
| Stage 2 interpretation into `PresheafPFunctor` | Novel |

No presheaf-level code system was located in the literature search; the
nearest prior art is [SpivakGarnerFairbanks2021], which presents the
functors but not an inductive syntax for them.

## Proof obligations

These are stated as obligations, not assumptions. Each is unproved at the
time of writing.

1. **Incompleteness argument.** That every code in the Stage 1 grammar
   extended by `ι` at a presheaf has `reindex` an isomorphism. The
   argument is sketched above; it is not machine-checked. If it fails,
   the Stage 2 constructor may be unnecessary.
2. **Variance of the Stage 2 witness.** `reindex` maps the restricted
   shape's directions into the original's, so for `g : j' ⟶ j` the
   witness must be a code morphism `c(j) ⟶ c(j')`, directions travelling
   backward along code morphisms. This has been reasoned through but not
   elaborated; it inverts silently if written from memory.
3. **Correctness of the Stage 1 witness.** That codes together with
   `Functoriality` interpret into `Fam(C)` and that the interpretation is
   functorial. Prototype finding 4 establishes only that the witness type
   elaborates.
4. **Degeneracy.** That the Stage 2 system at discrete `I` and `J` agrees
   with the existing `IR` system, and the Stage 1 system at a discrete
   `C` likewise. Prototype finding 2 covers only the `ι` shape type.
5. **Lemma 1 analogue.** That every `PresheafPFunctor` has a code. This
   is the completeness target that motivates the Stage 2 relaxation of
   `ι`.
6. **Relation of the two morphism notions.** The code system inherits
   two candidate morphism types: the inductive one required for the
   witnesses, and the Definition 8 homset of
   [HancockMcBrideGhaniMalatestaAltenkirch2013] that realizes the
   equivalence of categories. Whether they agree, in the discrete case
   and in general, is open.

## Non-goals

- Universe polymorphism beyond what the existing `IR` and
  `PresheafPFunctor` declarations carry. The prototype's `Functoriality`
  is at a single universe; generalizing it is plan-level work.
- The `W`-type of a presheaf code, and initial algebras. This spec covers
  the codes and their interpretation only.
- Any change to `SlicePFunctor` or to the existing `IR` code type. Stage
  1 adds to them; it does not modify them.
- Retention of `Geb/Internal/PresheafIRProto.lean`. It is exploration,
  not deliverable content, and is removed with the spec and the plan.

## References

- [DybjerSetzer1999], [DybjerSetzer2003] — inductive-recursive
  definitions.
- [GhaniNordvallForsbergMalatesta2015] — positive inductive-recursive
  definitions; the Stage 1 source.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] — small induction
  recursion; the existing `IR` system's source.
- [Weber2007], [nLabParametricRightAdjoint] — parametric right adjoints.
- [SpivakGarnerFairbanks2021], [Shapiro2021] — parametric right adjoints
  between presheaf categories.
- [AltenkirchGhaniHancockMcBrideMorris2015] — indexed containers.
