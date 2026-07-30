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
`(Iᵒᵖ ⥤ Type) → (Jᵒᵖ ⥤ Type)` for categories `I` and `J`. No code system
denotes those functors. This spec designs one.

`PresheafPFunctorData` extends `SlicePFunctor` unconditionally, adding
`directionRestr`, `shapeRestr` and `reindex`. At discrete `I` and `J`
those three fields are expected to carry no information beyond the
`SlicePFunctor` they extend; that expectation is obligation 6 below, not
an established fact.

## Two prior generalizations, on independent axes

Dybjer–Setzer inductive-recursive definitions
([DybjerSetzer1999], [DybjerSetzer2003]) describe functors
`Fam(D) → Fam(D)` for a set `D`. Two published generalizations move in
different directions.

| Work | Direction generalized | Cost |
| --- | --- | --- |
| [HancockMcBrideGhaniMalatestaAltenkirch2013] | Smallness, yielding the equivalence with dependent polynomials and indexed containers. `IR.Hom` is the homset of the interpreted functors, computed by `IR.elimAlg` on the codomain nested in `IR.elimAlg` on the domain | Definition 8's homset; the identity morphism is not given by the paper and is constructed here as `IR.id` |
| [GhaniNordvallForsbergMalatesta2015] | The decoding target from a set to a category `C`, giving functors `Fam(C) → Fam(C)` | A type of code morphisms, defined simultaneously with the codes, whose `ι` rule carries a `C`-morphism |

The axes are independent, and `PresheafPFunctor` sits past both:
`Fam(C)` is the free set-indexed coproduct completion of `C`,
`Cᵒᵖ ⥤ Type` is the free colimit completion, and the former embeds in
the latter as the coproducts of representables. A presheaf-level code
system is therefore a simultaneous generalization along both axes.

The two directions are not compatible by default. Section 2 of
[GhaniNordvallForsbergMalatesta2015] records that its morphisms differ
from those of [HancockMcBrideGhaniMalatestaAltenkirch2013], whose
characterization of the interpretation of `δ` codes as left Kan
extensions fails when `C` is non-discrete, at the cost of full and
faithfulness of the interpretation. This is what forces a new morphism
notion in Stage 1 below.

Related work at the semantic level: parametric right adjoints between
presheaf categories are characterized in [Weber2007] and
[nLabParametricRightAdjoint]; [SpivakGarnerFairbanks2021] presents them
as polynomial bicomodules between categories; [Shapiro2021] describes
the data specifying a familially representable monad on a presheaf
category.

## Prototype findings

`Geb/Internal/PresheafIRProto.lean` is throwaway exploration, not
upstream-eligible content. It establishes the following by elaboration.
Each entry states what the prototype establishes and nothing further.

1. `iotaPresheaf j₀` — the constant functor at the representable
   `y j₀` is a `PresheafPFunctor`, with shape type the total space
   `Σ j', (j' ⟶ j₀)` rather than a single shape. All seven functor laws
   are discharged: the shape-side laws are the category laws of `J`, the
   direction-side laws hold because every direction fiber is empty.
2. `iotaDiscreteShapeEquiv` — for a discrete `J` the type
   `Σ j' : Discrete O, (j' ⟶ ⟨o⟩)` is equivalent to `PUnit`. Its
   identification with `(iotaPresheafData ⟨o⟩).A`, and with
   `IR.toSlicePFunctorIota`'s single shape, is definitional and is not
   separately recorded.
3. `iotaConst P` — the constant functor at an arbitrary presheaf `P` on
   `J` is a `PresheafPFunctor`, with shapes the total space of `P` and
   `shapeRestr` the restriction of `P`. Its shape type at
   `P := yoneda.obj j₀` is definitionally the shape type of finding 1.
   No relation between the two functors beyond that is established; see
   obligation 8.
4. `Functoriality` — a witness family over pre-codes is definable by
   `IR.rec`, whose `δ` clause has access to the subcode family. This
   establishes the attachment mechanism only. The witness type the
   prototype uses is built from `IR.Hom` and is the wrong one; see
   Stage 1 below.
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

A transcription of [GhaniNordvallForsbergMalatesta2015]. Four
observations fix the shape of the work.

- The pre-codes are the existing `IR` codes. That paper's Definition 3.1
  gives `ι` an object of `C`, `σ` a set `A` with `f : A → IR⁺(C)`, and
  `δ` a set `A` with `F : (A → C) → IR⁺(C)`. At `uA = uB` and up to the
  universe lifts in `IR.Direction`, these are `IR.Shape` and
  `IR.Direction` at `I = O = C₀`. No new code type is required.
- `IR.Hom` cannot serve as the morphism notion. Definition 3.1's `ι`
  rule takes a `C`-morphism `HomC(c, c′)`, whereas `IR.Hom` at an
  `ι`-leaf is propositional equality of indices:
  `IR.Hom C₀ C₀ (iota c) (iota c′)` is `ULift (PLift (c = c′))`, which
  holds by `rfl`. At a non-discrete `C₀` a witness demanding the latter
  is generally uninhabited. Stage 1 therefore defines its own `PosHom`,
  whose `ι` clause is `c ⟶ c′` and whose `σ` and `δ` clauses transcribe
  Definition 3.1. This is not a presentational difference; it is why
  that paper introduces morphisms of codes at all.
- Two departures from the paper's presentation are forced, not one.
  First, the paper defines codes and morphisms simultaneously; the
  mutuality is eliminable by erasure, since the morphism rules never
  inspect a functoriality witness. The published `δ` code rule carries
  no such witness at all: functoriality enters as the side condition
  that `F` be a functor, which the accompanying Agda materializes as a
  field. Second, and separately, an inductive `PosHom` would still be an
  `inductive` containing an instance of itself, since its `σ` and `δ`
  rules take `PosHom` premises, which
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Recursion and
  induction through recursors forbids. `PosHom` must therefore be
  computed by recursion over pre-codes, as `IR.Hom` is. Obligation 3
  covers the agreement of the computed form with Definition 3.1.
- `Fam(C)` for a general category `C`: the presentation as a
  contravariant Grothendieck construction on the family functor is this
  project's, not the paper's. Remarks 2.3 states that `Fam(C)` is fibred
  over `Set` and is the free set-indexed coproduct completion, and does
  not mention a Grothendieck construction. `CoGrothendieck` is in
  `Geb/Mathlib/CategoryTheory/Grothendieck.lean`, but the family functor
  `Typeᵒᵖ ⥤ Cat`, `X ↦ Cˣ`, does not exist in the repository.
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` covers only the
  discrete case.

New content in this stage: `PosHom`; the functoriality witness family
over pre-codes; the family functor `Typeᵒᵖ ⥤ Cat`; the interpretation of
codes into `Fam(C)`; its morphism part, which consumes the functoriality
witness; and the interpretation of code morphisms as `Fam(C)`-morphisms,
which the morphism part applies to that witness and which therefore
cannot be omitted.

### Stage 2: codes over presheaf categories

Three changes to the Stage 1 code system.

- `ι` is relaxed from an object of `J` to a presheaf on `J`. The old
  `ι j` is recovered as `ι (y j)`. Prototype finding 3 establishes that
  the semantics of the relaxed constructor exists, and that its shape
  type at a representable is the shape type of finding 1. This is what a
  Lemma-1 analogue requires: `ι` and `σ` alone generate coproducts of
  representables, and a general shape presheaf is not one.
- `δ`'s arity becomes a presheaf on `I`. With the arity a bare set `B`
  labelled by `ℓ : B → I`, `Direction a i` is the fiber of `ℓ` over `i`,
  and for `f : i′ ⟶ i` that fiber can be inhabited over `i` while empty
  over `i′`, so no `directionRestr` exists. Replacing the arity by the
  total space of `⨿_B y (ℓ b)` makes `directionRestr` precomposition,
  mirroring on the direction side what finding 1 does on the shape side.
  No code-level witness is involved.
- A constructor indexed by a presheaf `P` on `J`, with a subcode family
  functorial over `el(P)` and a functoriality witness that is a code
  morphism. This supplies `shapeRestr` and `reindex`.

The variance of that witness is fixed. `reindex g a` maps the directions
of `shapeRestr g a` into those of `a`; morphisms of codes carry shapes
forward and directions backward; and a morphism of `el(T₁)` from `(j, a)`
to `(j′, a′)` is backed by `g : j′ ⟶ j`. So for `g : j′ ⟶ j` the witness
is a code morphism `c(j) ⟶ c(j′)`.

The third change is forced by prototype finding 5. Obligation 1 states
the incompleteness claim relative to a named interpretation; the
argument is that in the fragment without that constructor the arity of a
shape is determined by the `σ` branch and the `δ` nodes above it, while
`shapeRestr` acts only within the `ι` leaf's presheaf and so fixes both,
whence `reindex` is an identity. `arityVaries` has non-invertible
`reindex`, so it lies outside the fragment. Its shape presheaf is
terminal, so arity variation is independent of the shape presheaf.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing.

| Definition | Status |
| --- | --- |
| Stage 1 code type | Transcription, [GhaniNordvallForsbergMalatesta2015] Definition 3.1; already present as `IR` |
| Stage 1 `PosHom` | Transcription of that Definition's morphism rules, in a computed rather than inductive presentation. The computed presentation is novel |
| Stage 1 functoriality witness family | Transcription of the accompanying Agda's `F→`, attached after the codes rather than as a code field. The non-mutual attachment is novel |
| Stage 1 family functor `Typeᵒᵖ ⥤ Cat` | Novel in this repository |
| `Fam(C)` as a contravariant Grothendieck construction | Novel; Remarks 2.3 states only the fibration and the coproduct completion |
| Stage 1 interpretation of codes into `Fam(C)` and its morphism part | Transcription of that paper's interpretation and the Agda's morphism part |
| Stage 1 interpretation of code morphisms as `Fam(C)`-morphisms | Transcription of the Agda's corresponding definition |
| Stage 2 code type | Novel |
| Stage 2 relaxation of `ι` to a presheaf | Novel |
| Stage 2 presheaf arity for `δ` | Novel |
| Stage 2 constructor indexed by a presheaf on `J`, and its witness | Novel |
| Stage 2 interpretation into `PresheafPFunctor` | Novel |

No presheaf-level code system was located in the literature search; the
nearest prior art is [SpivakGarnerFairbanks2021], which presents the
functors but not an inductive syntax for them.

## Proof obligations

These are stated as obligations, not assumptions. Each is unproved at the
time of writing.

1. **Incompleteness.** Fix the restriction of the Stage 2 interpretation
   to the fragment generated by `ι` at a presheaf, `σ` over a set, and
   `δ` with a presheaf arity. That every code in the fragment has
   `reindex` an isomorphism, and hence that none denotes `arityVaries`.
   The argument is sketched above and is not machine-checked. If it
   fails, the third Stage 2 change may be unnecessary.
2. **Erasure faithfulness.** That `IR⁺(C)` is equivalent to
   `Σ γ : IR, Functoriality γ` — that erasing the functoriality witness
   from the code and reattaching it loses nothing.
3. **`PosHom` agreement.** That the computed `PosHom` agrees with
   Definition 3.1's inductive morphism type, and that it composes and
   has identities, which that paper proves by recursion on the structure
   of morphisms (its Lemma 3.2).
4. **Naturality.** Definition 3.1's `δ` rule takes
   `ρ : Nat(F, G(− ∘ α))`, a natural transformation; the accompanying
   Agda weakens `ρ` to a bare family and drops naturality. Which is
   transcribed is a decision to be recorded, with its consequences for
   obligation 3.
5. **Stage 1 witness correctness.** That codes together with the witness
   family interpret into `Fam(C)` and that the interpretation is
   functorial. Prototype finding 4 establishes only the attachment
   mechanism.
6. **Degeneracy.** That the Stage 2 system at discrete `I` and `J`
   agrees with the existing `IR` system, that the Stage 1 system at a
   discrete `C` likewise, and that `PresheafPFunctor` at discrete `I`
   and `J` carries no information beyond `SlicePFunctor`. Prototype
   finding 2 covers only the `ι` shape type.
7. **Lemma 1 analogue.** That every `PresheafPFunctor` has a code. This
   is the completeness target that motivates the Stage 2 relaxation of
   `ι`.
8. **Representable constant functors.** That `iotaPresheaf j₀` and
   `iotaConst (yoneda.obj j₀)` are isomorphic as functors. Prototype
   finding 3 establishes only that their shape types agree; their
   `shapeRestr` fields are not definitionally equal.
9. **Relation of the morphism notions.** The design has two: `PosHom`,
   required for the witnesses, and the Definition 8 homset `IR.Hom`,
   which realizes the equivalence of categories in the discrete case.
   Whether they agree at discrete `C` is open. They do not agree in
   general: Section 2 of [GhaniNordvallForsbergMalatesta2015] states
   that the Kan-extension characterization behind `IR.Hom` fails for
   non-discrete `C`.
10. **Constructive discipline.** `Geb.Mathlib.CategoryTheory.Grothendieck`
    is listed in `GebMeta.classicalAllowedModules`, whereas no `IndRec`
    or `FreeCoprodCompDisc` module is. Building the Stage 1 semantic
    target on `CoGrothendieck` would introduce `Classical.choice` into an
    interpretation presently free of it. Either the affected modules are
    added to that allowlist with a justification, per
    [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only, or a
    `Fam(C)` construction avoiding `Cat` is used.

## Non-goals

- Universe polymorphism beyond what the existing `IR` and
  `PresheafPFunctor` declarations carry. The prototype's `Functoriality`
  is at a single universe; generalizing it is plan-level work.
- The `W`-type of a presheaf code, and initial algebras. This spec covers
  the codes and their interpretation only.
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
