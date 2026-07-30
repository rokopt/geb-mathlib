# Codes for positive inductive-recursive definitions, and a presheaf direction

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Unresolved, and blocking](#unresolved-and-blocking)
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

It does not fix a design for Stage 2, the presheaf generalization. The
prototype settles several questions about what Stage 2 must contain, and
those are recorded in § Direction: codes over presheaf categories
together with the questions that remain open. The Stage 2 code type is
undetermined here, and a separate brainstorming phase is required before
it can be planned. Nothing in Stage 1 depends on Stage 2.

Neither stage's implementation order is fixed; that is the plan's
concern. Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape,
this file and its plan are transient and are removed in the final commits
of the topic branch.

## Unresolved, and blocking

Two decisions are open. Until they are made, § Stage 1's third and fourth
bullets, the `PosHom` and `PosFunctoriality` rows of § Definitions, and
obligations 1 to 6 are provisional.

1. **Which morphism collection.** Definition 3.1 of
   [GhaniNordvallForsbergMalatesta2015] takes `ρ : Nat(F, G(− ∘ α))`;
   [GhaniMalatestaNordvallForsberg2014Agda] takes a bare family of
   components. Remark 3.4 permits any collection "that represents
   natural transformations between the codes … as long as the identity
   morphisms and composition can be defined". Whether the Agda's
   collection meets the first condition is unsettled here: it admits
   families that are not natural, yet the paper states its material has
   been formalised in that development. Adopting `Nat` requires
   composition of code morphisms in order to state the premise, so codes,
   morphisms and composition would be constructed together; adopting the
   Agda's collection permits a sequential construction but forfeits the
   claim of transcribing Definition 3.1.
2. **Whether `F→` carries its functor laws.** Definition 3.1 requires
   `F : (A → C) → IR⁺(C)` to be a functor, so `F→` must preserve
   identities and composition. The Agda's `F→` field carries no laws.
   Obligation 5 cannot be discharged without them, so either
   `PosFunctoriality` becomes a law-carrying bundle or obligation 5 is
   weakened to something correspondingly weaker.

## Motivation

`IR.toSlicePFunctor` translates an `IR` code to a
`SlicePFunctor I O`, a functor `Type/I → Type/O`
([HancockMcBrideGhaniMalatestaAltenkirch2013], Lemma 2 / Definition 5),
and `IR.sliceCode` translates back (Lemma 1). The repository also has
`PresheafPFunctor I J`, a parametric right adjoint
`(Iᵒᵖ ⥤ Type) → (Jᵒᵖ ⥤ Type)` for categories `I` and `J`. No code system
denotes those functors.

`PresheafPFunctorData` extends `PresheafDomPFunctorData`, which carries
`directionRestr`, and `SlicePFunctor`; it adds `shapeRestr` and
`reindex`. At discrete `I` and `J` those fields are expected to carry no
information beyond the `SlicePFunctor` they extend; that expectation is
an open question of § Direction, not an established fact.

## Two prior lines of work, on independent axes

Dybjer–Setzer inductive-recursive definitions
([DybjerSetzer1999], [DybjerSetzer2003]) describe functors
`Fam |D| → Fam |D|` for a possibly large type `D`, where `|D|` is the
discrete category on `D`. Two published works move in different
directions.

| Work | Direction | Cost |
| --- | --- | --- |
| [HancockMcBrideGhaniMalatestaAltenkirch2013] | Splits the single index type into distinct input and output types `I` and `O`, and restricts to the case where both are sets ("small"), obtaining the equivalence with dependent polynomials and indexed containers ([AltenkirchGhaniHancockMcBrideMorris2015]). `IR.Hom` is the homset of the interpreted functors, computed by `IR.elimAlg` on the codomain nested in `IR.elimAlg` on the domain | Smallness is a restriction, not a generalization. Definition 8's homset; the identity morphism is not given by the paper and is constructed here as `IR.id` |
| [GhaniNordvallForsbergMalatesta2015] | Replaces the discrete category on `D` by an arbitrary category `C`, giving functors `Fam(C) → Fam(C)` | A type of code morphisms, defined simultaneously with the codes, whose `ι` rule carries a `C`-morphism |

The axes are independent, and `PresheafPFunctor` sits past both:
`Fam(C)` is the free set-indexed coproduct completion of `C`,
`Cᵒᵖ ⥤ Type` is the free colimit completion, and the former embeds in
the latter as the coproducts of representables.

Why the second work needs code morphisms at all: per its Section 3.1,
the `δ` introduction rule deploys a proper functor
`F : (A → C) → IR⁺(C)`, which requires `IR⁺(C)` to be a category. That
is what forces codes and morphisms to be introduced together. Separately,
Section 2 records that these morphisms differ from those of
[HancockMcBrideGhaniMalatestaAltenkirch2013], whose characterization of
the interpretation of `δ` codes as left Kan extensions fails for
non-discrete `C`; the consequences are that full and faithfulness of the
interpretation is lost and that the category laws must be proved by hand.

Related work at the semantic level: parametric right adjoints between
presheaf categories are characterized in [Weber2007] and
[nLabParametricRightAdjoint]; [SpivakGarnerFairbanks2021] presents them
as polynomial bicomodules between categories; [Shapiro2021] describes
the data specifying a familially representable monad on a presheaf
category.

## Prototype findings

`Geb/Internal/PresheafIRProto.lean` is exploration, not upstream-eligible
content. Each entry states what the prototype elaborates; inferences
drawn from an entry are marked as such.

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
   instantiations.
3. `iotaConst P` — the constant functor at an arbitrary presheaf `P` on
   `J` is a `PresheafPFunctor`, with shapes the total space of `P` and
   `shapeRestr` the restriction of `P`. Its shape type at
   `P := yoneda.obj j₀` is definitionally the shape type of finding 1.
   No relation between the two functors beyond that is established.
4. `Functoriality` — that `IR.rec` reaches the subcodes, which is all it
   elaborates. The witness type it uses is built from `IR.Hom`, whose
   `ι` clause ignores `C₀`'s morphisms, and is not the one Stage 1 needs.
5. `arityVaries` — a `PresheafPFunctor (Fin 1) (Fin 2)` whose every
   `Shape j` is equivalent to `PUnit`, and whose arity is elaborated as
   `ULift (Fin 0)` at the shape over `0` and `ULift (Fin 1)` at the shape
   over `1`. Inference, one step and not elaborated: `Direction a i` is a
   subtype of the arity and `I` has one object, so the arity fibers are
   empty over `0` and inhabited over `1`, whence `reindex` along `0 ⟶ 1`
   is the map out of the empty type and is not invertible.

## Semantic targets

`Fam(C)` for Stage 1. `PresheafPFunctor I J`, already in
`Geb/Mathlib/Data/PFunctor/Presheaf/Basic.lean`, for the presheaf
direction: a `SliceDomPFunctor` on the objects of `I` together with
`directionRestr` (arities are presheaves on `I`), `q`, `shapeRestr`
(shapes form a presheaf on `J`), and `reindex` (the arity assignment is a
functor on `el(T₁)ᵒᵖ`).

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
  rule takes a `C`-morphism `HomC(c, c′)`, whereas the identification of
  `IR.Hom C₀ C₀ (iota c) (iota c′)` with `ULift (PLift (c = c′))` is
  definitional. That type is a subsingleton and ignores `C₀`'s morphisms,
  so wherever `C₀` has non-identity morphisms between the relevant
  objects it is strictly smaller than `HomC(c, c′)`. Stage 1 therefore
  defines its own `PosHom`, whose `ι` clause is `c ⟶ c′`.
- The morphism collection is a parameter of the source, and Stage 1
  fixes it to the one its Agda formalization uses. Remark 3.4 of
  [GhaniNordvallForsbergMalatesta2015] states that its results are
  "completely parametric in the choice of morphisms used; any collection
  that represents natural transformations between the codes works, as
  long as the identity morphisms and composition can be defined", and
  describes a range from no non-identity morphisms up to
  `Hom(x, y) = ⟦x⟧ → ⟦y⟧`, which would force the interpretation to be
  defined simultaneously with the codes. Definition 3.1's `δ` morphism
  rule takes `ρ : Nat(F, G(− ∘ α))`, a natural transformation;
  [GhaniMalatestaNordvallForsberg2014Agda] weakens `ρ` to a bare family
  of components. Stage 1 adopts the latter. This is an instantiation of a
  parameter the source supplies, not a weakening of a fixed interface, so
  [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Structure and
  typeclass patterns, "Non-negotiable interfaces for formalising
  pre-existing objects", does not bite. Obligation 3 discharges
  Remark 3.4's two conditions for this choice.
- Consequently `PosHom` and the functoriality witness family are built
  sequentially, not simultaneously: with `ρ` a bare family, the morphism
  rules do not mention the witnesses, so `PosHom` is definable first — by
  `IR.elimAlg` on the codomain nested in `IR.elimAlg` on the domain, as
  `IR.Hom` already is — and the witness family follows by `IR.rec`, whose
  step reaches the subcodes. Had Definition 3.1's `Nat` premise been
  adopted instead, naturality would refer to the witnesses and to
  composition of code morphisms, which the source defines only afterwards
  in its Lemma 3.2; that variant is not reachable by this construction
  and is not taken.
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

On the presentation of `PosHom`:
[docs/rules/lean-coding.md](../../rules/lean-coding.md) § Recursion and
induction through recursors rejects an `inductive PosHom`, since its `σ`
and `δ` rules take `PosHom` premises. That rule sanctions a W-type
presentation as the alternative to a computed one, and `PosHom` is an
indexed family over `IR × IR` for which the repository's slice W-type
machinery would serve. Stage 1 takes the computed presentation because
the recursion is structural on the domain code; the W-type presentation
is not evaluated further here.

New content in this stage: `PosHom`; the functoriality witness family;
the family functor `Typeᵒᵖ ⥤ Cat`; the interpretation of codes into
`Fam(C)`; its morphism part, which consumes the functoriality witness;
and the interpretation of code morphisms as `Fam(C)`-morphisms, which the
morphism part applies to that witness and which therefore cannot be
omitted.

## Direction: codes over presheaf categories

Not a fixed design.

Settled by elaboration:

- A constant-functor constructor at an arbitrary presheaf on `J` has a
  semantics (finding 3), and at a representable its shape type is that of
  finding 1. Some such relaxation is needed for a Lemma-1 analogue, since
  a constructor at an object of `J` together with set-indexed coproducts
  reaches only coproducts of representables.
- Arity variation is independent of shape-presheaf complexity: finding 5
  exhibits a functor whose every shape fiber is a singleton and whose
  `reindex` is not invertible. So `reindex` cannot be recovered from the
  shape presheaf.

Settled by argument, with no corresponding declaration:

- A `δ` whose arity is a bare set `B` labelled by `ℓ : B → I` admits no
  `directionRestr` at all: `Direction a i` is the fiber of `ℓ` over `i`,
  and for `f : i′ ⟶ i` that fiber can be inhabited over `i` while empty
  over `i′`. The arity must carry presheaf structure.
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
8. Whether `PresheafPFunctor` at discrete `I` and `J` carries any
   information beyond `SlicePFunctor`.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing. Stage 2 has no rows because it has no fixed
definitions.

| Definition | Status |
| --- | --- |
| Stage 1 code type | Transcription, [GhaniNordvallForsbergMalatesta2015] Definition 3.1; identified with the existing `IR` modulo obligation 2 |
| Stage 1 `PosHom` | Transcription of the morphism collection of [GhaniMalatestaNordvallForsberg2014Agda], one admissible choice under Remark 3.4 of the paper. The computed rather than inductive presentation is novel |
| Stage 1 functoriality witness family `PosFunctoriality` | Transcription of the same source's `F→`, attached after the codes rather than as a code field. The attachment is novel |
| Stage 1 family functor `Typeᵒᵖ ⥤ Cat` | Novel in this repository |
| `Fam(C)` as a contravariant Grothendieck construction | Novel Lean presentation; the underlying split fibration `Fam(C) → Set` is Remarks 2.3 of the paper |
| Stage 1 interpretation of codes into `Fam(C)` and its morphism part | Transcription, [GhaniNordvallForsbergMalatesta2015] Theorem 3.3, whose object action is inherited from its Theorem 2.4 |
| Stage 1 interpretation of code morphisms as `Fam(C)`-morphisms | Transcription of the corresponding definition of [GhaniMalatestaNordvallForsberg2014Agda] |

No presheaf-level code system was located in the literature search; the
nearest prior art is [SpivakGarnerFairbanks2021], which presents the
functors but not an inductive syntax for them.

## Proof obligations

Stage 1 only. Each is unproved at the time of writing.

1. **Construction.** That `PosHom` is definable by `IR.rec` on the
   domain with case analysis on the codomain's shape and subcodes. Not by
   nested `IR.elimAlg`: `IR.Alg`'s `σ` and `δ` components receive
   `A → V` and `(B → I) → V`, recursive results only, whereas
   Definition 3.1's `σ` and `δ` morphism rules need the codomain's raw
   subcode family to state `PosHom (f x) (g (α x))`. `IR.Hom` escapes
   this because Definition 8 passes the codomain opaquely in those
   clauses, its inner fold sitting only in the `ι` case.
2. **Code identification.** That `IR⁺(C)` is adequately represented by
   `Σ γ : IR, PosFunctoriality γ`, so that identifying the pre-codes with
   the existing `IR` loses nothing. `IR⁺(C)` is an informal object, so
   this is an argued adequacy claim, not a Lean theorem; what is a Lean
   theorem is whatever equivalence obligation 3 and the interpretation
   obligations require of the bundled type.
3. **Remark 3.4's conditions.** That the adopted morphism collection
   represents natural transformations between the codes, and that
   identity morphisms and composition are definable for it, and that
   composition is associative with the identities as left and right
   units, so that the codes form a category. The last is required because
   Definition 3.1's `δ` premise calls `F` a functor into `IR⁺(C)`, which
   presupposes a category; it is the full content of the source's
   Lemma 3.2.
4. **Naturality not silently assumed.** An argued claim, not a Lean
   theorem, and contingent on unresolved decision 1: that no step relies
   on a naturality property of `ρ` the adopted collection does not carry.
   The concrete instance is that the source's Theorem 3.3 `δ` formula and
   the Agda's differ by a naturality square of the interpreted `F→`.
5. **Interpretation.** That codes with their witnesses interpret into
   `Fam(C)`, and that the interpretation is functorial. This depends on
   `F→` preserving identities and composition, per unresolved decision 2:
   `⟦δ_A F⟧` preserves identities and composition only if `F→` does. Prototype
   finding 4 establishes nothing about this.
6. **Morphism interpretation.** That code morphisms interpret as
   `Fam(C)`-morphisms, and that the source's Theorem 3.3 `δ` formula and
   the Agda's agree, naming the hypothesis that reconciles them.
7. **Coproducts in `Fam(C)`.** That the `CoGrothendieck` presentation of
   the family functor has the set-indexed coproducts, and the functorial
   action on them, that the interpretation of `σ` and `δ` uses; and that
   its objects and morphisms agree with that paper's Definition 2.2.
8. **`PosHom` and `IR.Hom`.** These do not agree at any `C`, discrete or
   not, so no obligation asserts that they do. Definition 3.1's rules are
   all shape-preserving, whereas Definition 8's `σ` and `δ` clauses leave
   the codomain's shape unconstrained: the type
   `IR.Hom C₀ C₀ (sigma PEmpty f) (iota c)` is inhabited, by
   `fun a ↦ a.elim`, while the corresponding
   `PosHom` is empty. The obligation is to identify the relation that
   does hold — an embedding of `PosHom` into `IR.Hom` at discrete `C`, or
   agreement of the two interpretations on its image.
9. **Degeneracy.** That the Stage 1 system at a discrete `C` agrees with
   the existing `IR` system, where agreement means an equivalence of code
   types carrying `PosHom` to `IR.Hom` and commuting with the two
   interpretations up to natural isomorphism. Prototype finding 2 covers
   only one shape type, and only up to a universe instantiation it does
   not fix.
10. **Constructive discipline.** `Geb.Mathlib.CategoryTheory.Grothendieck`
    is listed in `GebMeta.classicalAllowedModules`, whereas no `IndRec`
    or `FreeCoprodCompDisc` module is. Building the Stage 1 semantic
    target on `CoGrothendieck` would introduce `Classical.choice` into an
    interpretation presently free of it. Either the affected modules are
    added to that allowlist with a justification, per
    [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only, or a
    `Fam(C)` construction avoiding `Cat` is used.

## Non-goals

- A Stage 2 design. See § Direction for what is settled and what is open.
- The morphism collection of Definition 3.1 itself, with its `Nat`
  premise. Stage 1 adopts the Agda's collection under Remark 3.4;
  transcribing the `Nat` variant would additionally require composition
  of code morphisms in order to state the premise, and is not attempted.
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
- [GhaniMalatestaNordvallForsberg2014Agda] — its Agda formalization,
  whose morphism collection Stage 1 adopts.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] — small induction
  recursion; the existing `IR` system's source.
- [Weber2007], [nLabParametricRightAdjoint] — parametric right adjoints.
- [SpivakGarnerFairbanks2021], [Shapiro2021] — parametric right adjoints
  between presheaf categories.
- [AltenkirchGhaniHancockMcBrideMorris2015] — indexed containers.
