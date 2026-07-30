# Codes for positive inductive-recursive definitions, and a presheaf direction

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Motivation](#motivation)
- [Two prior lines of work, on independent axes](#two-prior-lines-of-work-on-independent-axes)
- [Prototype findings](#prototype-findings)
- [Semantic targets](#semantic-targets)
- [Stage 1: codes over `Fam(C)`](#stage-1-codes-over-famc)
- [Direction: codes over presheaf categories](#direction-codes-over-presheaf-categories)
- [Definitions: transcription or novel](#definitions-transcription-or-novel)
- [Proof obligations](#proof-obligations)
- [Non-goals](#non-goals)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Spec for codes over `Fam(C)` for a category `C`, and for the direction
that generalizes them to presheaf parametric-right-adjoint functors.

## Scope of this document

This is a brainstorming-phase spec. It fixes the design of one
workstream, Stage 1: codes for functors `Fam(C) → Fam(C)`, a
transcription of [GhaniNordvallForsbergMalatesta2015]. Its proof
obligations are in § Proof obligations.

It does **not** fix a design for Stage 2, the presheaf generalization.
The prototype settles several questions about what Stage 2 must contain,
and those are recorded in § Direction: codes over presheaf categories
together with the questions that remain open. The Stage 2 code type is
undetermined here, and a separate brainstorming phase is required before
it can be planned. Nothing in Stage 1 depends on Stage 2.

Neither stage's implementation order is fixed; that is the plan's
concern. Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape,
this file and its plan are transient and are removed in the final commits
of the topic branch.

## Motivation

`IR.toSlicePFunctor` translates an `IR` code to a
`SlicePFunctor I O`, a functor `Type/I → Type/O`
([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 2 / Definition 5),
and `IR.sliceCode` translates back (Lemma 1). The repository also has
`PresheafPFunctor I J`, a parametric right adjoint
`(Iᵒᵖ ⥤ Type) → (Jᵒᵖ ⥤ Type)` for categories `I` and `J`. No code system
denotes those functors.

`PresheafPFunctorData` extends `SlicePFunctor` unconditionally, adding
`directionRestr`, `shapeRestr` and `reindex`. At discrete `I` and `J`
those three fields are expected to carry no information beyond the
`SlicePFunctor` they extend; that expectation is obligation 8 below, not
an established fact.

## Two prior lines of work, on independent axes

Dybjer–Setzer inductive-recursive definitions
([DybjerSetzer1999], [DybjerSetzer2003]) describe functors
`Fam |D| → Fam |D|` for a possibly large type `D`, where `|D|` is the
discrete category on `D`. Two published works move in different
directions.

| Work | Direction | Cost |
| --- | --- | --- |
| [HancockMcBrideGhaniMalatestaAltenkirch2013] | Splits the single index type into distinct input and output types `I` and `O`, and restricts to the case where both are sets ("small"), obtaining the equivalence with dependent polynomials and indexed containers. `IR.Hom` is the homset of the interpreted functors, computed by `IR.elimAlg` on the codomain nested in `IR.elimAlg` on the domain | Smallness is a restriction, not a generalization. Definition 8's homset; the identity morphism is not given by the paper and is constructed here as `IR.id` |
| [GhaniNordvallForsbergMalatesta2015] | Replaces the discrete category on `D` by an arbitrary category `C`, giving functors `Fam(C) → Fam(C)` | A type of code morphisms, defined simultaneously with the codes, whose `ι` rule carries a `C`-morphism |

The axes are independent, and `PresheafPFunctor` sits past both:
`Fam(C)` is the free set-indexed coproduct completion of `C`,
`Cᵒᵖ ⥤ Type` is the free colimit completion, and the former embeds in
the latter as the coproducts of representables.

The two directions are not compatible by default. Section 2 of
[GhaniNordvallForsbergMalatesta2015] records that its morphisms differ
from those of [HancockMcBrideGhaniMalatestaAltenkirch2013], whose
characterization of the interpretation of `δ` codes as left Kan
extensions fails when `C` is non-discrete, so that full and faithfulness
of the interpretation is lost. That loss is what makes a separate
morphism notion necessary in Stage 1.

Related work at the semantic level: parametric right adjoints between
presheaf categories are characterized in [Weber2007] and
[nLabParametricRightAdjoint]; [SpivakGarnerFairbanks2021] presents them
as polynomial bicomodules between categories; [Shapiro2021] describes
the data specifying a familially representable monad on a presheaf
category.

## Prototype findings

`Geb/Internal/PresheafIRProto.lean` is exploration, not upstream-eligible
content. It establishes the following by elaboration. Each entry states
what the prototype establishes and nothing further.

1. `iotaPresheaf j₀` — the constant functor at the representable
   `y j₀` is a `PresheafPFunctor`, with shape type the total space
   `Σ j', (j' ⟶ j₀)` rather than a single shape. All seven functor laws
   are discharged: the shape-side laws are the category laws of `J`, the
   direction-side laws hold because every direction fiber is empty.
2. `iotaDiscreteShapeEquiv` — for a discrete `J` the type
   `Σ j' : Discrete O, (j' ⟶ ⟨o⟩)` is equivalent to `PUnit`. Its
   identification with `(iotaPresheafData ⟨o⟩).A` is definitional. No
   identification with `IR.toSlicePFunctorIota`'s shape type is
   established: the two `PUnit`s are at different universe
   instantiations, and reconciling them is part of obligation 8.
3. `iotaConst P` — the constant functor at an arbitrary presheaf `P` on
   `J` is a `PresheafPFunctor`, with shapes the total space of `P` and
   `shapeRestr` the restriction of `P`. Its shape type at
   `P := yoneda.obj j₀` is definitionally the shape type of finding 1.
   No relation between the two functors beyond that is established; see
   § Direction, open question 5.
4. `Functoriality` — a witness family over pre-codes is definable by
   `IR.rec`, whose `δ` clause has access to the subcode family. This
   establishes only that `IR.rec` reaches the subcodes. The witness type
   the prototype uses is built from `IR.Hom` and is the wrong one, and
   the after-the-fact attachment it demonstrates is superseded by the
   simultaneous construction of Stage 1 below.
5. `arityVaries` — a `PresheafPFunctor (Fin 1) (Fin 2)` whose shape
   presheaf is terminal (every `Shape j` is equivalent to `PUnit`) and
   whose arity is empty at the shape over `0` and a singleton at the
   shape over `1`, so `reindex` along `0 ⟶ 1` is the map out of the
   empty type and is not invertible.

## Semantic targets

`Fam(C)` for Stage 1. `PresheafPFunctor I J`, already in
`Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`, for the presheaf
direction: a `SliceDomPFunctor` on the objects of `I` together with
`directionRestr` (arities are presheaves on `I`), `q`, `shapeRestr`
(shapes form a presheaf on `J`), and `reindex` (the arity assignment is a
functor on `el(T₁)ᵒᵖ`, contravariantly).

## Stage 1: codes over `Fam(C)`

A transcription of [GhaniNordvallForsbergMalatesta2015]. Five
observations fix the shape of the work.

- The pre-codes are the existing `IR` codes. That paper's Definition 3.1
  gives `ι` an object of `C`, `σ` a set `A` with `f : A → IR⁺(C)`, and
  `δ` a set `A` with `F : (A → C) → IR⁺(C)`. At `uA = uB` and up to the
  universe lifts in `IR.Direction`, these are `IR.Shape` and
  `IR.Direction` at `I = O = C₀`. Whether the identification survives the
  functoriality data is obligation 2.
- `IR.Hom` cannot serve as the morphism notion. Definition 3.1's `ι`
  rule takes a `C`-morphism `HomC(c, c′)`, whereas `IR.Hom` at an
  `ι`-leaf is propositional equality of indices: the identification of
  `IR.Hom C₀ C₀ (iota c) (iota c′)` with `ULift (PLift (c = c′))` is
  definitional. That type ignores `C₀`'s morphisms entirely, so at a
  non-discrete `C₀` it is strictly smaller than `HomC(c, c′)`. Stage 1
  therefore defines its own `PosHom`, whose `ι` clause is `c ⟶ c′` and
  whose `σ` and `δ` clauses transcribe Definition 3.1.
- The mutuality of codes and morphisms is **not** eliminable, and the
  construction is simultaneous. Definition 3.1's `δ` morphism rule takes
  `ρ : Nat(F, G(− ∘ α))`, a natural transformation, whose naturality is
  stated in terms of the morphism actions of `F` and `G` — that is, in
  terms of the functoriality witnesses. So the morphism rules do inspect
  those witnesses. The accompanying Agda weakens `ρ` to a bare family and
  thereby breaks the dependency, but adopting that weakening to ease
  implementation is forbidden by
  [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Non-negotiable interfaces
  for formalising pre-existing objects. `PosHom` and the functoriality
  witness family are therefore built **simultaneously**, by a single
  `IR.rec` into a product motive. Every premise recurses on subcodes, so
  the recursion is structural.
- An inductive `PosHom` is independently forbidden: its `σ` and `δ` rules
  take `PosHom` premises, so it would be an `inductive` containing an
  instance of itself, which
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Recursion and
  induction through recursors rejects. The simultaneous `IR.rec`
  construction satisfies that rule; it uses one recursor and introduces
  no self-referential inductive.
- `Fam(C)` for a general category `C`: the presentation as a
  contravariant Grothendieck construction on the family functor is this
  project's Lean presentation, not new mathematics. Remarks 2.3 of that
  paper records four properties of `Fam(C)` — that it is fibred over
  `Set` with a standard split cleavage, that it is the free set-indexed
  coproduct completion, that it is cocomplete iff `C` has small connected
  colimits, and that `Fam` is a functor `CAT → CAT` — and the split
  cleavage is the same content as the family functor under the standard
  correspondence. `CoGrothendieck` is in
  `Geb/Mathlib/CategoryTheory/Grothendieck.lean`, but the family functor
  `Typeᵒᵖ ⥤ Cat`, `X ↦ Cˣ`, does not exist in the repository.
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` covers only the
  discrete case.

New content in this stage: `PosHom` and the functoriality witness family,
built simultaneously; the family functor `Typeᵒᵖ ⥤ Cat`; the
interpretation of codes into `Fam(C)`; its morphism part, which consumes
the functoriality witness; and the interpretation of code morphisms as
`Fam(C)`-morphisms, which the morphism part applies to that witness and
which therefore cannot be omitted.

## Direction: codes over presheaf categories

Not a fixed design. What the prototype settles, and what it does not.

Settled:

- A constant-functor constructor at an arbitrary presheaf on `J` has a
  semantics (finding 3), and at a representable its shape type is that of
  finding 1. Some such relaxation is needed for a Lemma-1 analogue, since
  a constructor at an object of `J` together with set-indexed coproducts
  reaches only coproducts of representables.
- A `δ` whose arity is a bare set `B` labelled by `ℓ : B → I` admits no
  `directionRestr` at all: `Direction a i` is the fiber of `ℓ` over `i`,
  and for `f : i′ ⟶ i` that fiber can be inhabited over `i` while empty
  over `i′`. The arity must carry presheaf structure.
- Arity variation is independent of shape-presheaf complexity: finding 5
  exhibits a functor with terminal shape presheaf and non-invertible
  `reindex`. So `reindex` cannot be recovered from the shape presheaf.
- If a constructor supplies `reindex` through a witness that is a code
  morphism, its variance is determined: `reindex g a` maps the directions
  of `shapeRestr g a` into those of `a`; morphisms of codes carry shapes
  forward and directions backward; and a morphism of `el(T₁)` from
  `(j, a)` to `(j′, a′)` is backed by `g : j′ ⟶ j`. So for `g : j′ ⟶ j`
  the witness is a code morphism `c(j) ⟶ c(j′)`.

Open, and blocking a Stage 2 design:

1. The Stage 2 code type. Full premises and conclusions for every
   constructor, not only their arity and index data.
2. How Stage 1's single category `C` splits into the distinct `I` and
   `J`, across the `ι`, `δ` and witness rules.
3. What indexes the `δ` subcode family once the arity is a presheaf on
   `I` — presheaf morphisms out of the arity, or maps out of its total
   space. These differ, and only the former reduces to the `A → X`
   coproduct index of Definition 5 at discrete `I`.
4. What "denotes" means, before any incompleteness claim can be stated:
   equality of `PresheafPFunctorData`, isomorphism of `PresheafPFunctor`s,
   or natural isomorphism of the induced functors. Whether "`reindex` is
   an isomorphism" is invariant under that relation is a further claim.
   Only once both are fixed can the conjecture be posed that every code
   in the fragment without a `J`-indexed constructor has `reindex` an
   isomorphism, and hence that none denotes `arityVaries`.
5. Whether `iotaPresheaf j₀` and `iotaConst (yoneda.obj j₀)` are
   isomorphic as functors. Finding 3 establishes only that their shape
   types agree; their `shapeRestr` fields are not definitionally equal.
6. Soundness: that a Stage 2 code interprets to a `PresheafPFunctorData`
   satisfying all seven `IsFunctorial` fields, with `reindex_id` and
   `reindex_comp` discharged by functoriality of the witness assignment.
7. A Stage 2 morphism type, and that it composes and has identities.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing. Stage 2 has no rows because it has no fixed
definitions.

| Definition | Status |
| --- | --- |
| Stage 1 code type | Transcription, [GhaniNordvallForsbergMalatesta2015] Definition 3.1; identified with the existing `IR` modulo obligation 2 |
| Stage 1 `PosHom` | Transcription of Definition 3.1's morphism rules, in a computed rather than inductive presentation. The computed presentation is novel |
| Stage 1 functoriality witness family | Transcription of Definition 3.1's functoriality side condition on `F`. Its simultaneous construction with `PosHom`, rather than as a code field, is novel |
| Stage 1 family functor `Typeᵒᵖ ⥤ Cat` | Novel in this repository |
| `Fam(C)` as a contravariant Grothendieck construction | Novel Lean presentation; the underlying split fibration `Fam(C) → Set` is Remarks 2.3 of that paper |
| Stage 1 interpretation of codes into `Fam(C)` and its morphism part | Transcription of that paper's Theorem 3.2 and the corresponding Agda definitions |
| Stage 1 interpretation of code morphisms as `Fam(C)`-morphisms | Transcription of the Agda's corresponding definition |

No presheaf-level code system was located in the literature search; the
nearest prior art is [SpivakGarnerFairbanks2021], which presents the
functors but not an inductive syntax for them.

## Proof obligations

Stage 1 only. Each is unproved at the time of writing.

1. **Simultaneous construction.** That `PosHom` and the functoriality
   witness family can be built by one `IR.rec` into a product motive,
   with every premise recursing on subcodes, and that the result agrees
   with Definition 3.1.
2. **Code identification.** That `IR⁺(C)` is equivalent to
   `Σ γ : IR, Functoriality γ`, so that identifying the pre-codes with
   the existing `IR` loses nothing.
3. **Category structure.** That `PosHom` composes and has identities,
   which that paper proves by recursion on the structure of morphisms
   (its Lemma 3.2).
4. **Naturality.** That the `Nat` premise of Definition 3.1's `δ`
   morphism rule is transcribed faithfully, and that the Agda's weakening
   of it is not silently adopted anywhere in the construction.
5. **Interpretation.** That codes with their witnesses interpret into
   `Fam(C)`, and that the interpretation is functorial. Prototype
   finding 4 establishes nothing about this.
6. **Morphism interpretation.** That code morphisms interpret as
   `Fam(C)`-morphisms, and that the object interpretation's morphism part
   agrees with it where both apply.
7. **Relation to `IR.Hom`.** Whether `PosHom` and the Definition 8 homset
   agree at discrete `C`. They do not agree in general: the `ι`-clause
   comparison above shows `IR.Hom` ignores `C`'s morphisms. Section 2 of
   [GhaniNordvallForsbergMalatesta2015] is cited only for the loss of
   full and faithfulness, not for the non-agreement.
8. **Degeneracy.** That the Stage 1 system at a discrete `C` agrees with
   the existing `IR` system, and that `PresheafPFunctor` at discrete `I`
   and `J` carries no information beyond `SlicePFunctor`. Prototype
   finding 2 covers only one shape type, and only up to a universe
   instantiation it does not fix.
9. **Constructive discipline.** `Geb.Mathlib.CategoryTheory.Grothendieck`
   is listed in `GebMeta.classicalAllowedModules`, whereas no `IndRec`
   or `FreeCoprodCompDisc` module is. Building the Stage 1 semantic
   target on `CoGrothendieck` would introduce `Classical.choice` into an
   interpretation presently free of it. Either the affected modules are
   added to that allowlist with a justification, per
   [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only, or a
   `Fam(C)` construction avoiding `Cat` is used.

## Non-goals

- A Stage 2 design. See § Direction for what is settled and what is open.
- Universe polymorphism beyond what the existing `IR` and
  `PresheafPFunctor` declarations carry. The prototype's `Functoriality`
  is at a single universe; generalizing it is plan-level work.
- The `W`-type of a code, and initial algebras. This spec covers the
  codes and their interpretation only.
- Full and faithfulness of the Stage 1 interpretation.
  [GhaniNordvallForsbergMalatesta2015] does not have it for non-discrete
  `C` and proves its results without it.
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
