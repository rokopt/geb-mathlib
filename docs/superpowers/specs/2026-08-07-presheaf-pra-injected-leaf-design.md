# Presheaf p.r.a. codes over an injected leaf

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [The change](#the-change)
- [The two rules](#the-two-rules)
- [The equivalence with the unextended target](#the-equivalence-with-the-unextended-target)
- [What the change retires](#what-the-change-retires)
- [What the change preserves](#what-the-change-preserves)
- [Definitions: transcription or novel](#definitions-transcription-or-novel)
- [Branches](#branches)
- [Non-goals](#non-goals)
- [References](#references)

<!-- END doctoc -->

## Scope of this document

This specifies the code system for presheaf parametric-right-adjoint
functors as two rules over an injected leaf, superseding the design
recorded in
[docs/superpowers/specs/2026-07-31-presheaf-pra-ir-codes-design.md](docs/superpowers/specs/2026-07-31-presheaf-pra-ir-codes-design.md).
It covers the code type, its interpretation, the statement relating the
codes to the functors they denote, and the material the change retires.
It does not cover morphisms of presheaf p.r.a. functors, which are
unaffected.

The prototype is `Geb/Internal/PresheafIRProto/`, downstream-only
throwaway exploration. Nothing here is upstream-eligible content.

## The change

[HancockMcBrideGhaniMalatestaAltenkirch2013] takes the code system of
[DybjerSetzer1999] as given and proves that, for small codomain types,
its interpretation lands in the slice polynomial functors and that every
such functor is so reached. The codes there are generators: `ι` and `σ`
build the non-recursive part from below, `δ` supplies the recursion, and
the correspondence with the target is a theorem about what the
generators reach.

The generalization to p.r.a. functors between presheaf categories is not
a transcription of that argument, because the target is already
available as a type. Taking it as the leaf inverts the burden:

- the leaf is a presheaf p.r.a. functor as it stands, injected;
- `δ` is the one rule with a recursive argument, and is defined from
  operations already available on presheaf p.r.a. functors.

The standard definition of a presheaf p.r.a. functor is flat, so `δ` is
the only recursive constructor and the compilation is the identity on
the leaf together with the translation of that one case. Completeness is
then definitional rather than a theorem: every presheaf p.r.a. functor
is the interpretation of its own leaf code.

## The two rules

Over a fixed input base `𝕀` and decoding target `D : 𝕀ᵒᵖ ⥤ Type u`, a
code is indexed by the output base category it denotes a functor into.
`GebProto.CodeShape` is the sum of the two rules and
`GebProto.Code` is the W-type of the resulting slice polynomial functor
on `Cat`.

- `pra 𝔹 F` — the leaf, at any
  `F : PresheafPFunctor (ElObj D) 𝔹`. No subcodes.
- `δ 𝔹 A hA K` — at a functorial output-varying arity
  `A : BaseArity 𝕀 𝔹`, with one subcode `K` over
  `ElObj (decPresheaf A hA D)`.

`δ`'s continuation is a single code over the category of elements of the
decoding presheaf, not a family of codes indexed by decodings, so the
index is a parameter and nothing is defined simultaneously with anything
else. `Cat.{v, u}` is closed under that step, which is what lets the
codes be an ordinary W-type rather than an inductive family.

Semantically `GebProto.delta` is
`sigmaPsh (decPresheaf A hA D) ∘ adjoinArity (decArity A hA D)`: the
inner factor adjoins the decoding's fibres to every arity, the outer one
sums over the decodings. That regrouping,

```text
Σ_{g : P → X} ⟦F (f ∘ g)⟧ = Σ_{d : P → D} (sections of f over d) × ⟦F d⟧,
```

is [DybjerSetzer1999]'s `δ` read in presheaves. It is stated in the
prototype's docstrings; no declaration establishes it as an equation.

The dependent sum over decodings is therefore internal to `δ`, not a
rule beside it. `GebProto.sigmaPsh` and the category of elements survive
as `δ`'s machinery; `σ` as a code constructor does not exist.

## The equivalence with the unextended target

`GebProto.interp` folds a code to a presheaf p.r.a. functor paired with
the base it lands in (`GebProto.Interp`). The relation to the unextended
target is that `interp` is a split epimorphism with the leaf as its
section:

```lean
def praCodeOf (p : Interp I D) : Code I D := praCode I D p.1 p.2

theorem leftInverse_interp_praCodeOf :
    Function.LeftInverse (interp I D) (praCodeOf I D)

theorem surjective_interp : Function.Surjective (interp I D)
```

The first holds by `rfl`, `interp`'s leaf clause being the identity; the
second is that statement read as surjectivity. With
`GebProto.interp_praCode_interp` — every code has the interpretation of
a one-node code — this says the codes denote exactly the presheaf p.r.a.
functors: `δ` adds no functor the leaf does not already supply, and what
a code carries beyond its interpretation is its derivation.

No `Category` instance on presheaf p.r.a. functors is required, so this
does not depend on branch W-a below.

## What the change retires

The retired material was written to bound what a *restricted* leaf
reaches. An unrestricted leaf leaves it without a subject.

- `GebProto.HasBijectiveReindex` and its closure and witness families —
  the constant-arity fragment's bound.
- `GebProto.coprod` and `GebProto.deltaRec` — the regrouping as a
  coproduct over decodings, superseded by the `sigmaPsh` form, which is
  the one that keeps the output-varying arity.
- `GebProto.unitPsh`, `GebProto.unitPshLift`,
  `GebProto.praWitnessLift` and `GebProto.adjoinArityVarying` — the
  chain reproducing the p.r.a. formula from restricted leaves.
- `GebProto.elSliceEquiv` — the measurement of what a `σ`-over-`ι` leaf
  reaches.
- `GebProto.iotaConst`, `GebProto.iotaDiscreteShapeEquiv` and the
  `GebProto.arityVaries` fixture — `ι` as a generator, and the fixture
  the bound was stated about.
- `GebProto.DomArity.ofPresheaf` and its lemmas — the presheaf-to-arity
  direction, which only the retired material consumed.

`GebProto.deltaCodeVaries` and its fixtures (`termPsh`,
`arityVariesBase`, `decUnit`, `decVariesElt`, `deltaVaries`) are kept as
a worked example, with `GebProto.interp_deltaCodeVaries` as the check
that `delta` and `deltaCode` compute. `GebProto.iotaPresheaf` is kept as
that example's continuation.

## What the change preserves

The morphism theory of `PresheafIRProto/Basic.lean` — `ArityHom`,
`objEquivSigmaArityHom`, `DomHom`, `PshHom`, `pshHomEquivNatFamily` and
the fibre apparatus — is untouched: it concerns morphisms of presheaf
p.r.a. functors, which the code system's shape does not bear on.

`δ`'s own machinery is untouched: `DomArity`, `ShapeArity`,
`adjoinArity`, `BaseArity` with its pullback and its bundling as a
functor, `ElObj` with `sigmaPsh` and its five laws, `PshMor`,
`fibreArity`, `decPresheaf`, `decArity` and `delta`.

## Definitions: transcription or novel

- `delta`, and the regrouping it implements — transcription of the `δ`
  rule of Section 6 of [HancockMcBrideGhaniMalatestaAltenkirch2013],
  generalized from families to presheaves. The sections
  `(p : P) → D (i p)` its subcode family is indexed by become `PshMor`.
- `praCode` as the leaf — novel. The small-IR code system has no
  such rule; it is what replaces `ι` and `σ` when the target is
  available as a type.
- `Code`, `interp`, `CodeShape`, `CodeDir`, `CodeNext` — novel, as the
  W-type presentation of a code system indexed by base categories.
- `PresheafPFunctor` and the p.r.a. formula it presents —
  transcription of [Weber2007], as recorded in the prototype's
  existing docstrings.
- `decPresheaf`, `decArity`, `fibreArity` — novel; the presheaf
  reading of the decoding layer that Section 6 of
  [HancockMcBrideGhaniMalatestaAltenkirch2013] states for families.

## Branches

W-c of the superseded design — the bound, and the constant-arity
fragment's code type and induction — is dropped: it existed to
establish incompleteness of a restricted leaf. The remaining branches
are unchanged.

- W-a: morphisms of presheaf p.r.a. functors, their action and the
  hom-set bijection; their composition and category structure; the
  bundled restatements and natural-transformation identification, in a
  `Classical`-allowed module. Upstream-eligible.
- W-b: the semantic operations, the decoding layer, the code type and
  the interpretation. Upstream-eligible.
- W-d: code-level morphisms and their representation theorem. Depends
  on W-a and W-b.
- W-e: the collapse `PSh(𝕀)/D ≃ PSh(el(D))`.

W-a, W-b and W-e depend on nothing.

## Non-goals

- An equivalence of categories between codes and presheaf p.r.a.
  functors. That needs composition of `PshHom`, which is W-a; the
  split-epimorphism statement above is what this workstream establishes.
- Any claim that two codes with equal interpretations are equal. They
  are not, and the derivation a code records is the difference.
- Any statement about codes over equivalent rather than equal base
  categories. `SlicePFunctor.W.mk` aligns a subcode's index by strict
  equality of bundled categories, a constraint of the W-type
  presentation.

## References

- [DybjerSetzer1999]
- [HancockMcBrideGhaniMalatestaAltenkirch2013]
- [Weber2007]
