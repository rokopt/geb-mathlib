# The universe over presheaf p.r.a. functors — findings and handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope](#scope)
- [Goals](#goals)
- [Findings](#findings)
  - [The walking-arrow formulation](#the-walking-arrow-formulation)
  - [What presheaf p.r.a. computes over a non-discrete base](#what-presheaf-pra-computes-over-a-non-discrete-base)
  - [Variance, and the morphisms the formers act along](#variance-and-the-morphisms-the-formers-act-along)
  - [Where `Fam(C)` sits inside `PSh(C)`](#where-famc-sits-inside-pshc)
  - [Strictness, universal elements, and the stability ladder](#strictness-universal-elements-and-the-stability-ladder)
  - [Terminology](#terminology)
  - [Claims tested and rejected](#claims-tested-and-rejected)
  - [Mechanical findings](#mechanical-findings)
- [References](#references)
- [Open questions](#open-questions)
- [Proposed order](#proposed-order)
- [Handoff](#handoff)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Scope

Findings from the prototypes on branch `feat/presheaf-universe-prototypes`,
which ask what a dependent-type universe becomes when its decoding is expressed
over a base category rather than over `Type` treated as discrete. The
inductive-recursive presentation this departs from is
`Geb/Mathlib/Data/PFunctor/IndRec/Universes.lean`; the prototypes are
`Geb/Prototypes/PresheafUniverse/`, `Geb/Prototypes/FinCardUniverse/`,
`Geb/Prototypes/UniverseVariance/`, and `Geb/Prototypes/FamBoundary.lean`.

This document is a transient process artifact in the sense of
`CONTRIBUTING.md` § Concern shape: remove it in the final
commits of the branch. What is permanent is in the module docstrings and in
`docs/index.md`.

## Goals

The development has two independent axes.

The first is the ambient in which induction-recursion is interpreted, in three
stages, each with an inductive-recursive syntax to be defined and shown
equivalent to the corresponding class of functors:

1. slice polynomial functors, matching small induction-recursion — established
   in [HancockMcBrideGhaniMalatestaAltenkirch2013] and implemented in
   `Geb/Mathlib/Data/PFunctor/IndRec/Slice.lean`;
2. presheaf parametric-right-adjoint functors, matching large
   induction-recursion, with codes a presheaf and decodings into a category;
3. `Cat`-valued parametric-right-adjoint functors, with codes a category and the
   decoding a functor.

Stated by what codes and decoding are at each stage:

| stage | codes | decoding | ambient |
| --- | --- | --- | --- |
| 1 | a set | into a discrete category | `Type/D = Fam(\|D\|)` |
| 2 | a set with an `I`-action | into a category | `Fam(C) ⊆ PSh(C)` |
| 3 | a category | a functor | lax slice `Cat//C` |

The second axis is variance. A universe closed under dependent products is not
functorial in the decoding category's morphisms, because the dependent-product
former is contravariant in its domain. Every stage of the first axis needs an
answer on the second.

## Findings

### The walking-arrow formulation

`Geb/Prototypes/PresheafUniverse/` expresses the universe as a presheaf
polynomial endofunctor over the walking arrow, with the code object and the term
object as the two base objects. Two identifications hold on the nose:

- hereditary naturality of a term tree is its well-typedness;
- the presheaf restriction along the arrow's non-identity morphism is the typing
  map (`typeOf_pairTerm`).

Shapes and directions are finite, so fibre membership is decided by
`FinitePresheafPFunctor.memWBool`. The family a binder carries in the
inductive-recursive presentation is not expressible: an arity is fixed
independently of the input presheaf, so it cannot be indexed by the decoding of
a code chosen at another direction. The two binder codes therefore take a single
subcode in each argument and denote the non-dependent product and function
space, and the dependent-product former has no introduction shape.

### What presheaf p.r.a. computes over a non-discrete base

`Geb/Prototypes/FinCardUniverse/` builds the same universe over `Card`, the
finite cardinals with functions between their elements as morphisms, with the
type former a parameter. `sigmaUniverse` and `piUniverse` differ only in the
shape-output map: over presheaves the dependent-product former is no harder than
the dependent-sum former.

The reason is `arityHomEquiv`, which computes the arity homs into a family of
codes `(U, d)` presented as the presheaf `Σ_u y(d u)`:

```text
ArityHom (universeFunctor former) a (famPresheaf U d)
  ≃ ∀ k, Σ u, (bound a.1 k ⟶ d u)
```

The inductive-recursive presentation over a discrete base has an equality
`bound a.1 k = d u` in that position. Over a base with morphisms the equality is
a hom, and two consequences follow:

- `junkArity` and `junk_decoding_ne`: a binder declaring the empty object
  accepts a code denoting the singleton, the empty function being the coercion
  the constraint asks for;
- `out_emptyBind` and `famDec_eq`: the object a code decodes to is fixed by the
  shape's declaration, with the codes the shape binds nowhere in it.

The second is the substantive one. The recursion of induction-recursion is the
computation of a code's decoding from the decodings of the codes it binds; over
presheaves that computation is replaced by a label carried on the shape.

### Variance, and the morphisms the formers act along

`piFormer_not_covariant` reproduces Example 3.6 of
[GhaniNordvallForsbergMalatesta2015] at the smallest scale that hosts it: the
empty dependent product is the singleton and the dependent product of the
counterexample family is empty, so the action the former would need is a map
from the singleton to the empty object. `sigmaFormer_covariant` shows the
dependent-sum former survives the same instance, and `counterMap_not_split`
records that the morphism there admits no section.

`Geb/Prototypes/UniverseVariance/Basic.lean` establishes that a section is what
the dependent-product former needs, and that invertibility — the paper's answer,
the groupoid `Set≅` — is more than it needs. `piMap` builds
`Π X' (Y ∘ f) → Π X Y` from a chosen section of `f` and transports along the
right-inverse witness, which is the move the discrete case makes along an
equality of decodings; `piMap_id` and `piMap_comp` are its functor laws.
`Split.ofEquiv` places the groupoid inside the class and the mirror exhibits a
split epimorphism that is not injective, so the containment is strict in both
directions. `twIdEquivSplit` identifies the class: a morphism between identity
arrows in the twisted-arrow category is exactly a function with a chosen
section.

The mechanism is not new. Theorem 5.8 of [LindenhoviusMisloveZamdzhiev2021],
crediting Fiore's thesis, makes a mixed-variance functor covariant by
restricting to the subcategory of embeddings and using the projection in the
contravariant slot; classically this is how recursive domain equations are
solved. What the searches did not find is any application of it to
induction-recursion. One difference from the domain-theoretic setting: an
embedding-projection pair there also satisfies `e ∘ p ⊑ id`, which needs the
order; in `Set` only the retraction survives.

`Geb/Prototypes/UniverseVariance/Universe.lean` gives Examples 3.5 and 3.6 over
that base. `FamHom` is a map of codes together with a `Split` at each code —
an embedding-projection pair — and `FamHom` composition is `Split` composition,
so the retraction is inherited. `piUnivHom` is the morphism map the paper shows
cannot be given over `Set` or `Setᵒᵖ`.

### Where `Fam(C)` sits inside `PSh(C)`

`Fam(C)`, the free set-indexed coproduct completion (Remarks 2.3 of
[GhaniNordvallForsbergMalatesta2015]), embeds into `PSh(C)` as the coproducts of
representables. Equivalently, in the fibrational picture, it is the discrete
fibrations each of whose connected components has a terminal object; and,
equivalently again, the categories of elements are the coproducts of slice
categories, with functors over the base as morphisms.

`Geb/Prototypes/FamBoundary.lean` brackets membership:

- `isFamPsh_praPsh` — a sum over shapes of a representable times a set, which is
  the shape of the p.r.a. formula's value, is a family presheaf whatever the
  set. So a coercion multiplicity is no obstruction to restricting: it lands in
  the code type, the completion being closed under set-indexed coproducts.
- `isFamPsh_topPsh_of_terminal` and `not_isFamPsh_topPsh` — the terminal
  presheaf is a family presheaf over a base with a terminal object and is not
  over the walking parallel pair.

Since the shape presheaf is the functor's value at the terminal presheaf, the
second is where the general claim fails: a presheaf p.r.a. functor carries
`Fam(C)` into itself when its shape presheaf lies there, and the category of
elements of the terminal presheaf being the base itself is why the condition
reads as a terminal object in each component of the base.

`Geb/Prototypes/FinCardUniverse/Restriction.lean` applies this to the universe.
`shapePshEquiv` and `arityPshEquiv` identify both the shape type and each arity
as total spaces of family presheaves, so both halves of the functor's data are
coproducts of representables and the universe functor does restrict. `famCode`
and `famDec` are the family obtained, and `famDec_eq` records that it decodes by
the code former alone. Restricting is therefore not what strictness turns on:
the coercion enters when mapping into the input, not from the shapes or the
arities.

### Strictness, universal elements, and the stability ladder

Strictness is the property that the constraint a direction imposes on its value
is an equation: the chosen code's decoding *is* the object the shape declares.
It is what ties a shape's declaration to its children, and it cannot hold in a
presheaf — the assignment `c ↦ {u | d u = c}` is not functorial as soon as the
base has a morphism between distinct objects, and the universal repair is the
representable, which replaces the equation by a hom.

Fibrationally the constraint is expressible: it asks the value to be the
universal element of its component, the code carrying the identity. What
prevents imposing it is that universality is not stable — a morphism of families
sends the universal element of `u` to its own comparison map, which is universal
only when that map is a transport. `isUniversalElement_famMorApp` is the
stability on exactly those morphisms, the split cartesian fragment, which
[GhaniNordvallForsbergMalatesta2015] identifies as Dybjer and Setzer's setting.

`IsSplitCoercion` weakens the constraint to "the coercion is a split
epimorphism" and `isSplitCoercion_famMorApp` shows it stable under morphisms
whose comparison maps are split epimorphisms, with
`isSplitCoercion_of_isUniversalElement` showing the weakening proper. So there
is a constraint short of strictness that survives non-invertible morphisms, over
the same class both type formers act along. The resulting picture is one axis —
how far a morphism moves the universal element:

| a morphism moves the universal element | comparison map | theory |
| --- | --- | --- |
| not at all | a transport | Dybjer–Setzer (split cartesian) |
| along an isomorphism | invertible | positive IR over `Set≅` |
| along a split epimorphism | split, with a section | `UniverseVariance` |
| arbitrarily | any | positive IR over `Set`, `Setᵒᵖ` |
| no universal elements | — | presheaf p.r.a. |

### Terminology

"Generic" is reserved for the parametric-right-adjoint sense: a morphism
`f : B ⟶ T A` is `T`-generic when every commuting square over it has a unique
`T`-fill, and `T` is a parametric right adjoint exactly when every map into a
`T`-value factors as a generic followed by a `T`-image
([nLabParametricRightAdjoint], [Weber2007]). Under that factorization the
coercion is the generic part, so the element carrying the identity — the one
whose factorization is trivial — is named the universal element instead.

### Claims tested and rejected

Recorded so they are not re-derived:

- "No presheaf p.r.a. functor reproduces the arrow-formulated universe" holds
  over the walking arrow only. Over the discrete category on `Type` the universe
  is such a functor, which is what `IndRec/Slice.lean` compiles.
- "The universe functor does not restrict to `Fam(C)`" is false. It conflated
  *representable* with *coproduct of representables*; `isFamPsh_praPsh` is the
  correction.
- Restricting the shapes and arities to coproducts of slices does not recover
  strictness: `shapePshEquiv` and `arityPshEquiv` show the prototype already has
  that form.

### Mechanical findings

- `Geb/Mathlib/CategoryTheory/FinSetSkel` seals `Hom` `irreducible` so that
  morphism equality is decidable without `Classical.choice`. The seal blocks the
  definitional associativity the arity reindexing and the `ReindexId` and
  `ReindexComp` transports rely on: unfolding a sealed composite reaches a
  projection out of the irreducible `Hom` and the elaborator fails rather than
  getting stuck. `Geb/Prototypes/FinCardUniverse/Basic.lean` defines its own base
  with functions as morphisms for that reason.
- `decide` on `Function.LeftInverse` or `Function.RightInverse` selects a
  `Classical.choice`-dependent `Decidable` instance. Build `FinEnum` equivalence
  laws from `Fin.cases` chains instead.
- For a `Type`-valued functor, `funext` does not apply to `map_id` or
  `map_comp`: the goal's sides are `Quiver.Hom`, and unification will not unfold
  the instance. `ext x` works, splitting a `Sigma` codomain into an `fst` goal
  and a `HEq` `snd` goal.
- `lake shake` cannot see an import used only inside an `example`. Name a `def`
  or `theorem` built from the module under test.
- A `def` whose type is a class (`IsEmpty`, `Decidable`) trips
  `warn.classDefReducibility`; state it as a `theorem` where the class is
  `Prop`-valued.

## References

Bibliographic detail is in `docs/references.bib`.

- [GhaniNordvallForsbergMalatesta2015] — positive induction-recursion, arXiv
  1502.05561. Examples 2.5 and 2.6 (the two universes), 3.5 and 3.6 (which of
  them extends, and the counterexample), Remarks 2.3 (`Fam(C)` as the free
  coproduct completion, split cartesian morphisms), Section 4 (stronger
  elimination principles), Section 5 (nested types as containers, resting on
  `Cont = Fam(Setᵒᵖ)`). Records that full faithfulness of the interpretation is
  lost for non-discrete `C`, the characterization of `δ` as a left Kan extension
  failing.
- [HancockMcBrideGhaniMalatestaAltenkirch2013] — small induction-recursion and
  dependent polynomials.
- [LindenhoviusMisloveZamdzhiev2021] — LNL-FPC, arXiv 1906.09503. Theorem 5.8 is
  the embedding-projection device.
- [Weber2007], [nLabParametricRightAdjoint] — familial 2-functors, generic
  morphisms.
- Sojakova and Johann, *A General Framework for Relational Parametricity*, arXiv
  1805.00067 — Dunphy and Reddy's parametric limits in reflexive graph
  categories, described there as well known and as insufficiently general to
  subsume Reynolds' own model; proof-relevant parametricity after Orsanigo.
- Neumann, *Paranatural Category Theory*, arXiv 2307.09289 — strong dinatural
  transformations, advertised for initial algebras, terminal coalgebras and
  bisimulations.
- Pavlovic, *Logic of Fusion*, arXiv 2007.15697, Proposition 3.1 — an initial
  algebra's homs as parametric transformations, with a parameter.
- Altenkirch, Capriotti, Dijkstra, Kraus and Nordvall Forsberg, *Quotient
  inductive-inductive types*, arXiv 1612.02346 — initial-algebra semantics for
  the definitions stage 3 would need.

Searches that returned nothing: no work after 2015 extending positive
induction-recursion past the groupoid restriction; no application of the
embedding-projection device to induction-recursion.

## Open questions

1. Is "the actual decoding is a retract of the declared one" preserved by the
   two type formers? The binder's family is indexed by the declared object while
   the children are indexed by the actual one, so the comparison needs a
   reindexing along the section. If that coherence must be assumed rather than
   derived, strictness up to retraction is structure the codes carry, not a
   property of the ambient.
2. The functor laws for the decoding components of `sigmaUnivHom` and
   `piUnivHom` are not formalized. Only the action on codes is
   (`univCodeMap_id`, `univCodeMap_comp`).
3. Can inductive-recursive codes be defined over the split base so that the
   interpretation is full and faithful? This is the stage-2 equivalence. A
   conjecture to test first: full faithfulness fails in `Fam(C)` because
   `Fam(C)` lacks the colimits a left Kan extension needs, in which case
   computing the extension in `PSh(C)` and landing in `Fam(C)` may restore it.
4. Do paranatural transformations suffice for a universe, or is the relational
   form needed? The expectation is the latter: a dependent-product code applied
   to a dependent-product code passes the rank at which strong dinaturality and
   parametricity diverge, and `GebLean/ParanaturalTopos.lean` in the old
   experimental tree records that endoprofunctors with paranatural
   transformations lack equalizers, which a parametric-right-adjoint development
   needs.
5. The general membership criterion for `Fam(C)` — every connected component of
   the category of elements has a terminal object, in both directions — is
   stated but not formalized; only the two brackets are.
6. Whether the split-epimorphism rung is folklore in the recursive-domain-
   equations literature under another name. The searches were aimed at
   induction-recursion, not at that literature.
7. Stage 3 needs quotient inductive-inductive definitions for its initial
   algebras, so it also raises the metatheoretic cost;
   [GhaniNordvallForsbergMalatesta2015] deliberately keeps its metatheory at
   inductive-inductive definitions.

## Proposed order

1. Question 1, closure of the retract relation under the two formers. Small, and
   it decides whether the split rung supports an interpretation at all.
2. Question 2, the decoding-component functor laws. Moderate, and it upgrades an
   existing module rather than starting one. Transport bookkeeping, not
   conceptual.
3. Question 4, the rank test for paranaturality. Independent of the others, and
   one worked instance settles it, as `piFormer_not_covariant` settled Example
   3.6.
4. Question 5, the general criterion. Optional; it tidies `FamBoundary`.
5. Question 3, codes and full faithfulness. The research problem, to be started
   after 1 and 2 report.
6. Stage 3, after quotient inductive-inductive tooling exists.

## Handoff

The branch is `feat/presheaf-universe-prototypes`, seven commits on `main`,
unpushed. Verify with

```text
lake build && lake test && lake lint && lake lint -- GebTests
lake shake --add-public --keep-implied --keep-prefix Geb GebTests GebLang
bash scripts/lint-imports.sh && bash scripts/check-transitive-imports.sh
markdownlint-cli2 '**/*.md' && bash scripts/check-md-links.sh
```

Pick up at question 1. What it needs is already present:
`GebProto.UniverseVariance.Split` with `piMap` and `sigmaMap` and their laws;
`GebProto.UniverseVariance.FamHom`, whose comparison maps are exactly the split
epimorphisms in question; and `GebProto.FinCardUniverse.Card` as a base whose
category laws hold definitionally, which is what keeps the transports tractable.

A statement to attempt first, in `Geb/Prototypes/UniverseVariance/`: given a
`Split X' X` and a family `Y : X → Type` together with, for each `x'`, a `Split`
from `Y (f x')` to some `Y' x'`, is there a `Split` from `former X Y` to
`former X' Y'` for each of the two formers, and does it compose? The
dependent-sum case is expected to go through directly; the dependent-product
case is where the reindexing along the section enters, and is the one to write
first, since a failure there answers the question without the rest.

If that succeeds, question 2 becomes worth finishing, and the two together are
what a stage-2 interpretation over the split base would rest on. If it fails,
record the obstruction in this document and move to question 4, which does not
depend on it.
