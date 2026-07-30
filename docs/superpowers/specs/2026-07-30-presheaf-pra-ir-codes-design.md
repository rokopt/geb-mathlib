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
Nat_Z(Σ_{a : T₁ j} Hom(E a, −), Σ_{b : T₁' j} Hom(E' b, −))
  ≅ Π_{a : T₁ j} Nat_Z(Hom(E a, −), Σ_{b : T₁' j} Hom(E' b, −))
  ≅ Π_{a : T₁ j} (Σ_{b : T₁' j} Hom(E' b, −))(E a)          -- Yoneda
  ≅ Π_{a : T₁ j} Σ_{b : T₁' j} Hom(E' b, E a)
```

at each fixed output index `j`. So a transformation is a map of shapes
forward together with, at each shape, a map of arities backward.
Naturality in `Z` is thereby accounted for. What remains, as conditions
rather than data, is naturality in the indices: the shape map is a
morphism of presheaves on `J`, and the arity maps are natural over
`el(T₁)ᵒᵖ`.

What makes the classification available is not the ambient category but
the shape of the functor: Yoneda holds in any locally small category, and
`PresheafPFunctor` is by construction familial, its interpretation being
a coproduct of representables in `Z`.

Over `Fam(C)` the classification does not apply, because the
interpretation of a `δ` code is not a coproduct of `Fam(C)`-representables.
Theorem 2.4 of [GhaniNordvallForsbergMalatesta2015] indexes that
coproduct by the set maps `A → X`, whereas a `Fam(C)`-morphism
`(X, P) → (Y, Q)` is by its Definition 2.2 a pair `(h, k)` with
`h : X → Y` and `k : P ⟹ Q ∘ h`, carrying `C`-morphism data the index
does not. Section 2 of that paper reports the consequence as the
breakdown of the characterization of the `δ` interpretation as a left Kan
extension, and its concluding section lists recovering that
characterization as an open problem rather than an impossibility.

Full and faithfulness over `Fam(C)` is therefore attainable, not
excluded. Remark 3.4 records that taking `Hom(x, y) = ⟦x⟧ → ⟦y⟧` gives it
"by definition", at the cost of defining the interpretation
simultaneously with the codes, so that the definition of the code system
is itself inductive-recursive. What the presheaf setting offers is the
same property without that cost: the classification supplies the
morphisms structurally, from data the p.r.a. structure already carries.

## Prototype findings

`Geb/Internal/PresheafIRProto.lean` is exploration, not upstream-eligible
content. Each entry states what the prototype elaborates; inferences
drawn from an entry are marked as such.

1. `SliceHom` — the formula's data at the slice level: a map of shapes
   over each output index, and at each shape a map of arities in the
   opposite direction.
2. `sliceHomApp` — the forward action of that data on the
   domain-restricted functor's value, definable with no further data: the
   shape travels forward, each direction of the new shape is filled by
   pulling it back along the arity map, and compatibility follows by
   composing the original element's compatibility with the arity map's
   fiber witness. It establishes neither naturality nor the equivalence.
   It is at the slice level, where the `el(T₁)ᵒᵖ` condition is vacuous, so
   it is not evidence that the presheaf-level `Hom` needs no condition.
3. `iotaPresheaf j₀` — the data with shape type the total space
   `Σ j', (j' ⟶ j₀)`, no directions, and `shapeRestr` precomposition is a
   `PresheafPFunctor`; all seven functor laws are discharged. Inference,
   not elaborated: its interpretation is the constant functor at the
   representable `y j₀`. Nothing relates `objPresheaf` to `yoneda.obj j₀`.
4. `iotaDiscreteShapeEquiv` — for a discrete `J` the type
   `Σ j' : Discrete O, (j' ⟶ ⟨o⟩)` is equivalent to `PUnit`. No
   identification with `IR.toSlicePFunctorIota`'s shape type is
   established; the two are at different universe instantiations.
5. `iotaConst P` — the data with shapes the total space of an arbitrary
   presheaf `P` on `J` and `shapeRestr` the restriction of `P` is a
   `PresheafPFunctor`. Its shape type at `P := yoneda.obj j₀` is
   definitionally the shape type of finding 3. Inference, not elaborated:
   its interpretation is the constant functor at `P`.
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
  family is natural over `el(T₁)ᵒᵖ`. The arity component's variance is the
  same as that of the existing `reindex` field, which is an instance
  as that of the existing `reindex` field, though it is not an instance of
  it: `reindex` is indexed by `J`-morphisms and relates two arities of one
  functor, whereas this component is indexed by shapes and relates arities
  of two functors.
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
- Because the p.r.a. structure carries the index actions as fields
  (`directionRestr`, `reindex`) rather than as witnesses referring to code
  morphisms, a `δ` constructor need not carry a functoriality witness of
  the kind that forces mutuality. The interpretation therefore need not be
  defined simultaneously with the codes — the route Remark 3.4 describes
  and declines.

Settled by elaboration, from the findings:

- The data of a constant-functor constructor at an arbitrary presheaf on
  `J` is functorial (finding 5), and at a representable its shape type is
  that of finding 3. That its interpretation is the constant functor is
  an inference, not elaborated.
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
   space. These differ; which of them degenerates at discrete `I` to the
   unconstrained `A → X` index of Definition 4 of
   [HancockMcBrideGhaniMalatestaAltenkirch2013] is to be derived, not
   assumed.
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
workstream. They can meet the full-and-faithfulness requirement, but only
by the route of Remark 3.4, defining the interpretation simultaneously
with the codes; the presheaf setting reaches it structurally instead. If
wanted, they are better recovered inside the presheaf construction,
`Fam(C)` embedding in presheaves as the coproducts of representables,
than built separately.

## Definitions: transcription or novel

Per [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Cite the literature
when transcribing. Stage 2 has no rows because it has no fixed
definitions.

| Definition | Status |
| --- | --- |
| `PresheafPFunctor.Hom` | Novel in this repository. The shapes-forward arities-backward form is the standard morphism notion for familial functors; obligation 5 records verifying the precise correspondence against [Weber2007] and [Shapiro2021], and against Definition 7 of [HancockMcBrideGhaniMalatestaAltenkirch2013] (morphisms of indexed containers, whose form this is) and its Definition 6 (the dependent-polynomial presentation the repository's `r`/`q` naming follows) in the discrete case |
| The action of a `Hom`, and its naturality | Novel |
| The representation theorem | Novel at this level; the discrete analogue is Theorem 3 of [HancockMcBrideGhaniMalatestaAltenkirch2013], present as `IR.interpHomEquiv` |
| Identity, composition, and the category structure on `Hom` | Novel |

## Proof obligations

Stage 1 only. Each is unproved at the time of writing.

1. **The action.** That a `Hom` acts on `objPresheaf` and that the action
   is a natural transformation, including compatibility with `objRestr`.
   Finding 2 establishes the slice-level action only.
2. **Representation.** That `Hom F F'` is equivalent to the
   natural transformations of the interpreted functors, stated against the
   `Classical.choice`-free `objPresheaf` and `mapPresheaf` rather than
   against `PresheafPFunctor.functor`, which depends on
   `Classical.choice`. The `functor` form is a corollary, and belongs in a
   module on `GebMeta.classicalAllowedModules`.
3. **Category structure.** That `Hom` has identities and composition,
   that composition is associative with those identities as units, and
   that the equivalence of obligation 2 carries them to the identities
   and composition of natural transformations.
4. **Non-redundancy.** That dropping the `el(T₁)ᵒᵖ` naturality condition
   makes the equivalence fail. That it is not too strong is obligation 2's
   fullness direction and is not a separate obligation. A candidate
   witness is `arityVaries`, whose `reindex` is not invertible.
5. **Correspondence with the literature.** That `PresheafPFunctor.Hom`
   agrees with the familial morphism notion of [Weber2007] and
   [Shapiro2021], and with Definitions 6 and 7 of
   [HancockMcBrideGhaniMalatestaAltenkirch2013] when `I` and `J` are
   discrete.
6. **Universes.** That the arity presheaf `E a`, whose values lie in
   `Type uB`, is an object of the domain category `Iᵒᵖ ⥤ Type uZ` that the
   classification quantifies over. This needs a universe relation such as
   `uB ≤ uZ`, or an explicit `ULift`; without one the interpretation is
   still defined but is not a coproduct of representables of that
   category. The obligation is to fix the relation and say whether the
   equivalence is claimed at a fixed `uZ` or for all `uZ`. Note that
   `Equiv` is universe-heterogeneous, so the two sides needing the same
   universe is not itself a requirement.
7. **Bundling.** That `T₁ : Jᵒᵖ ⥤ Type` and `E a : Iᵒᵖ ⥤ Type uB` exist
   as `Functor` values, assembled from `shapeRestr`, `directionRestr` and
   `isFunctorial`, and that
   `{ z : F.obj Z // F.q z.shape = j }` is equivalent to
   `Σ a : T₁ j, (E a ⟶ Z)`, naturally in `Z` and in `j`. Neither presheaf
   exists in the repository today — the fields are raw, with their laws in
   a separate `Prop` — and every phrase in Stage 1 that speaks of a
   morphism of shape or arity presheaves presupposes them.
8. **Constructive discipline.** That `Hom` and obligation 2's statement
   stay free of `Classical.choice`, per
   [CONTRIBUTING.md](../../../CONTRIBUTING.md) § Constructive-only.
   `Presheaf.Functor` is on `GebMeta.classicalAllowedModules` and
   `Presheaf.Basic` is not; `Hom` follows `Basic`, which is what
   obligation 2's restatement is for.

## Non-goals

- A code system. See § Direction.
- Positive inductive-recursive definitions over `Fam(C)` as a separate
  construction, for the reason given in § Direction. This is a choice
  about cost, not an impossibility claim.
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
