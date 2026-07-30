# Morphisms of presheaf p.r.a. functors, and codes for them

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Motivation](#motivation)
- [The formula, and why the setting matters](#the-formula-and-why-the-setting-matters)
- [Prototype findings](#prototype-findings)
- [Stage 1: morphisms and the representation theorem](#stage-1-morphisms-and-the-representation-theorem)
- [Direction: codes](#direction-codes)
- [Definitions: transcription or novel](#definitions-transcription-or-novel)
- [Proof obligations](#proof-obligations)
- [Non-goals](#non-goals)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Spec for morphisms of presheaf parametric-right-adjoint functors and their
representation theorem, and for the direction that builds codes on top of
them.

## Scope of this document

This is a brainstorming-phase spec. It fixes the design of one
workstream, Stage 1: morphisms of `PresheafPFunctor` and the theorem that
they are exactly the natural transformations of the interpreted functors.
Its proof obligations are in § Proof obligations.

It does not fix a design for Stage 2, codes denoting those functors. What
is settled about Stage 2 and what remains open is in § Direction. Nothing
in Stage 1 depends on Stage 2.

Neither stage's implementation order is fixed; that is the plan's
concern. Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Concern shape,
this file and its plan are transient and are removed in the final commits
of the topic branch.

## Motivation

`PresheafPFunctor I J` is a parametric right adjoint
`(Iᵒᵖ ⥤ Type) → (Jᵒᵖ ⥤ Type)`. The repository has its object and morphism
actions, its W-type, and its categorical packaging, but no notion of
morphism *between* two such functors. Every downstream question needs
one: a code system denoting these functors is a category only if its
codes have morphisms, and the codes' morphisms are worth having only if
they are exactly the natural transformations.

The requirement fixed for this workstream is that the morphism collection
be exactly the natural transformations — no fewer, so that the
interpretation is full, and no more, so that it is faithful.

## The formula, and why the setting matters

For `F` given by a shape presheaf `T₁` on `J` and an arity presheaf
`E(a)` on `I` for each element `a` of `T₁`, the interpretation is

```text
F(Z)(j) = Σ (a : T₁ j), Hom_{PSh(I)}(E a, Z)
```

a coproduct of representables in `Z`. Yoneda then computes the natural
transformations:

```text
Nat(Σ_a Hom(E a, −), Σ_b Hom(E' b, −))
  = Π_a Nat(Hom(E a, −), Σ_b Hom(E' b, −))
  = Π_a (Σ_b Hom(E' b, −))(E a)
  = Π_a Σ_b Hom(E' b, E a)
```

so a transformation is a map of shapes forward together with, at each
shape, a map of arities backward. Naturality in `Z` is automatic. What
remains as data is naturality in the indices: the shape map is a morphism
of presheaves on `J`, and the arity maps are natural over `el(T₁)ᵒᵖ`.

The step that carries this is Yoneda, which requires the domain to be a
presheaf category. This is why the same argument is unavailable over
`Fam(C)`, the free set-indexed coproduct completion, and it matches the
failure reported in Section 2 of
[GhaniNordvallForsbergMalatesta2015]: the characterization of the
interpretation of `δ` codes as left Kan extensions fails for non-discrete
`C`, and full and faithfulness of the interpretation is lost. That paper
then takes, per its Remark 3.4, the "smallest possible usable" morphism
collection. The presheaf setting is therefore not only the further
generalization; it is the setting in which the natural-transformation
formula is regular, and consequently the setting in which the
full-and-faithfulness requirement above is attainable at all.

## Prototype findings

`Geb/Internal/PresheafIRProto.lean` is exploration, not upstream-eligible
content. Each entry states what the prototype elaborates; inferences
drawn from an entry are marked as such.

1. `SliceHom` — the formula's data at the slice level: a map of shapes
   over each output index, and at each shape a map of arities in the
   opposite direction.
2. `sliceHomApp` — the action of that data on the domain-restricted
   functor's value, constructed with no further data and no side
   condition. This is the content of the formula: the shape travels
   forward, each direction of the new shape is filled by pulling it back
   along the arity map, and compatibility follows by composing the
   original element's compatibility with the arity map's fiber witness.
3. `iotaPresheaf j₀` — the constant functor at the representable `y j₀`
   is a `PresheafPFunctor`, with shape type the total space
   `Σ j', (j' ⟶ j₀)` rather than a single shape. All seven functor laws
   are discharged.
4. `iotaDiscreteShapeEquiv` — for a discrete `J` the type
   `Σ j' : Discrete O, (j' ⟶ ⟨o⟩)` is equivalent to `PUnit`. No
   identification with `IR.toSlicePFunctorIota`'s shape type is
   established; the two are at different universe instantiations.
5. `iotaConst P` — the constant functor at an arbitrary presheaf `P` on
   `J` is a `PresheafPFunctor`. Its shape type at `P := yoneda.obj j₀` is
   definitionally the shape type of finding 3.
6. `Functoriality` — that `IR.rec` reaches the subcodes, which is all it
   elaborates. Its witness type is built from `IR.Hom` and is retained
   only as a record of the discrete case.
7. `arityVaries` — a `PresheafPFunctor (Fin 1) (Fin 2)` whose every
   `Shape j` is equivalent to `PUnit`, and whose arity is elaborated as
   `ULift (Fin 0)` at the shape over `0` and `ULift (Fin 1)` at the shape
   over `1`. Inference, one step and not elaborated: the arity fibers are
   accordingly empty over `0` and inhabited over `1`, so `reindex` along
   `0 ⟶ 1` is the map out of the empty type and is not invertible.

## Stage 1: morphisms and the representation theorem

Three components.

- `PresheafPFunctor.Hom F F'`: a morphism of shape presheaves
  `T₁ ⟶ T₁'` on `J`; for each element `a` of `T₁`, a morphism of arity
  presheaves `E'(φ a) ⟶ E(a)` on `I`; and the condition that the latter
  family is natural over `el(T₁)ᵒᵖ`. The arity component's variance is
  the same as that of the existing `reindex` field, which is an instance
  of it: `reindex g a` maps the directions of `shapeRestr g a` into those
  of `a`.
- The action of a `Hom` on `objPresheaf`, and the proof that it is a
  natural transformation. Finding 2 constructs the slice-level action;
  the presheaf level adds compatibility with `objRestr`.
- The representation theorem: `Hom F F'` is equivalent to
  `NatTrans (F.functor) (F'.functor)`, with both round trips. Fullness
  and faithfulness are the two directions.

The template is `IR.interpHomEquiv` in
`Geb/Mathlib/Data/PFunctor/IndRec/Naturality.lean`, which proves the
corresponding statement for the discrete `IR` system against
`FreeCoprodCompDisc.NatTrans`, by `IR.rec` on the domain code, together
with its round-trip laws. Stage 1 is the same statement one level up, and
about functors rather than codes, so it is proved directly rather than by
recursion.

Identity and composition of `Hom`, and the category structure, follow;
whether they are defined directly or transported along the equivalence is
a plan-level choice.

## Direction: codes

Not a fixed design. What Stage 1 settles for it, and what remains open.

Settled by Stage 1, once it exists:

- The code-level morphism type is determined: it mirrors the Stage 1
  formula, and the code-level analogue of the representation theorem is
  what makes the interpretation full and faithful. This removes the
  question that the `Fam(C)` route could not answer.
- Because naturality is carried as data, the codes and their morphisms do
  not require an inductive-inductive definition, and in particular do not
  require the interpretation to be defined simultaneously with the codes
  — the alternative Remark 3.4 describes and declines.

Settled by elaboration, from the findings:

- A constant-functor constructor at an arbitrary presheaf on `J` has a
  semantics (finding 5), and at a representable its shape type is that of
  finding 3.
- Arity variation is independent of shape-presheaf complexity
  (finding 7), so `reindex` cannot be recovered from the shape presheaf.

Settled by argument, with no corresponding declaration:

- A `δ` whose arity is a bare set `B` labelled by `ℓ : B → I` admits no
  `directionRestr`: `Direction a i` is the fiber of `ℓ` over `i`, and for
  `f : i′ ⟶ i` that fiber can be inhabited over `i` while empty over
  `i′`. The arity must carry presheaf structure.

Open:

1. The code type: full premises and conclusions for every constructor.
2. How the input and output categories `I` and `J` are threaded through
   the constructors.
3. What indexes the `δ` subcode family once the arity is a presheaf on
   `I` — presheaf morphisms out of the arity, or maps out of its total
   space. These differ, and only the former reduces to the `A → X`
   coproduct index of Definition 5 of
   [HancockMcBrideGhaniMalatestaAltenkirch2013] at discrete `I`.
4. Whether the codes are represented as a W-type of a presheaf p.r.a.
   functor over a category of sorts, so that the dependency of morphisms
   on codes is carried by presheaf restriction. Lean has no
   inductive-inductive types — a second type may not be indexed by a type
   being defined simultaneously with it — and
   [docs/rules/lean-coding.md](../../rules/lean-coding.md) § Recursion and
   induction through recursors independently forbids a self-referential
   `inductive`, so some such encoding is required if the two are mutual.
   Stage 1 removes the reason to expect that they are.
5. Whether every `PresheafPFunctor` has a code, the analogue of Lemma 1
   of [HancockMcBrideGhaniMalatestaAltenkirch2013].
6. Whether `iotaPresheaf j₀` and `iotaConst (yoneda.obj j₀)` are
   isomorphic as functors. Finding 5 establishes only that their shape
   types agree.
7. Whether `PresheafPFunctor` at discrete `I` and `J` carries any
   information beyond `SlicePFunctor`, and whether a code system over it
   degenerates to the existing `IR`.

Positive inductive-recursive definitions over `Fam(C)`
([GhaniNordvallForsbergMalatesta2015]) are not a stage of this
workstream. They cannot meet the full-and-faithfulness requirement, for
the reason in § The formula. If wanted, they are better recovered inside
the presheaf construction, `Fam(C)` embedding in presheaves as the
coproducts of representables, than built separately.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing. Stage 2 has no rows because it has no fixed
definitions.

| Definition | Status |
| --- | --- |
| `PresheafPFunctor.Hom` | Novel in this repository. The shapes-forward arities-backward form is the standard morphism notion for familial functors; obligation 5 records verifying the precise correspondence against [Weber2007] and [Shapiro2021], and against Definition 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013] in the discrete case |
| The action of a `Hom`, and its naturality | Novel |
| The representation theorem | Novel at this level; the discrete analogue is Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013], present as `IR.interpHomEquiv` |
| Identity, composition, and the category structure on `Hom` | Novel |

## Proof obligations

Stage 1 only. Each is unproved at the time of writing.

1. **The action.** That a `Hom` acts on `objPresheaf` and that the action
   is a natural transformation, including compatibility with `objRestr`.
   Finding 2 establishes the slice-level action only.
2. **Representation.** That `Hom F F'` is equivalent to
   `NatTrans (F.functor) (F'.functor)`, with both round trips.
3. **Category structure.** That `Hom` has identities and composition,
   that composition is associative with those identities as units, and
   that the equivalence of obligation 2 carries them to the identities
   and composition of natural transformations.
4. **Naturality over `el(T₁)`.** That the naturality condition on the
   arity family is exactly what the representation theorem needs — that
   dropping it makes the equivalence fail, so the condition is neither
   redundant nor too strong.
5. **Correspondence with the literature.** That `PresheafPFunctor.Hom`
   agrees with the familial morphism notion of [Weber2007] and
   [Shapiro2021], and with Definition 6 of
   [HancockMcBrideGhaniMalatestaAltenkirch2013] when `I` and `J` are
   discrete.
6. **Universes.** That the equivalence is statable at the universes the
   existing declarations carry. `NatTrans` between functors on presheaf
   categories is large, and `PresheafPFunctor` already pins six universe
   parameters; that the two sides of obligation 2 live at the same
   universe is not obvious and is not assumed.
7. **Constructive discipline.** That the development stays free of
   `Classical.choice`, or that any module needing it is added to
   `GebMeta.classicalAllowedModules` with a justification per
   [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only. The
   categorical packaging in `Presheaf.Functor` is already on that list;
   `Presheaf.Basic` is not, and `Hom` should follow `Basic`.

## Non-goals

- A code system. See § Direction.
- Positive inductive-recursive definitions over `Fam(C)` as a separate
  construction, for the reason given in § Direction.
- The `W`-type of a code, and initial algebras.
- Any change to `SlicePFunctor`, `PresheafPFunctor` or the existing `IR`
  code type. Stage 1 adds to them; it does not modify them.
- Retention of `Geb/Internal/PresheafIRProto.lean`. It is exploration,
  not deliverable content, and is removed with the spec and the plan.

## References

- [GhaniNordvallForsbergMalatesta2015] — positive inductive-recursive
  definitions; Remark 3.4 on the choice of morphism collection, and
  Section 2 on the loss of full and faithfulness over `Fam(C)`.
- [GhaniMalatestaNordvallForsberg2014Agda] — its Agda formalization.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] — small induction
  recursion; Definition 6 for morphisms of dependent polynomials,
  Theorem 3 for the discrete representation theorem.
- [Weber2007], [nLabParametricRightAdjoint] — parametric right adjoints
  and familial functors.
- [SpivakGarnerFairbanks2021], [Shapiro2021] — parametric right adjoints
  between presheaf categories.
- [AltenkirchGhaniHancockMcBrideMorris2015] — indexed containers.
- [DybjerSetzer1999], [DybjerSetzer2003] — inductive-recursive
  definitions.
