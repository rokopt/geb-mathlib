# Umbrella spec: `FinSetSkel` as an elementary topos

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope of this document](#scope-of-this-document)
- [Motivation](#motivation)
- [Names fixed here](#names-fixed-here)
- [Findings](#findings)
  - [mathlib's skeletal finite-set category, and what in it is choice-free](#mathlibs-skeletal-finite-set-category-and-what-in-it-is-choice-free)
  - [An isomorphism in `Cat` is achievable](#an-isomorphism-in-cat-is-achievable)
  - [The representation choice, with the evidence on both sides](#the-representation-choice-with-the-evidence-on-both-sides)
  - [mathlib has no elementary topos](#mathlib-has-no-elementary-topos)
  - [The derivation lemmas exist, and their data counterparts are `noncomputable`](#the-derivation-lemmas-exist-and-their-data-counterparts-are-noncomputable)
  - [Chosen cones exist for the generators only](#chosen-cones-exist-for-the-generators-only)
  - [mathlib supplies the index arithmetic](#mathlib-supplies-the-index-arithmetic)
  - [mathlib's categorical vocabulary is choice-tainted](#mathlibs-categorical-vocabulary-is-choice-tainted)
  - [Batteries has union-find; the closure induction is ours](#batteries-has-union-find-the-closure-induction-is-ours)
  - [Reaching Batteries requires relaxing our import lint](#reaching-batteries-requires-relaxing-our-import-lint)
  - [Inverting an injective vector, shared by two rows](#inverting-an-injective-vector-shared-by-two-rows)
- [Constructive layering](#constructive-layering)
- [Workstreams](#workstreams)
  - [W0 — the `Batteries.` allow-list](#w0--the-batteries-allow-list)
  - [W1 — `FinSetSkel`, its isomorphism, and vector inversion](#w1--finsetskel-its-isomorphism-and-vector-inversion)
  - [W2 — the `ElementaryTopos` class](#w2--the-elementarytopos-class)
  - [W3 — the topos structure other than coequalizers](#w3--the-topos-structure-other-than-coequalizers)
  - [W4 — binary coequalizers by union-find](#w4--binary-coequalizers-by-union-find)
  - [W5 — unification](#w5--unification)
- [Why the workstreams compose](#why-the-workstreams-compose)
- [Standing repository obligations](#standing-repository-obligations)
- [Lifespan and branch placement](#lifespan-and-branch-placement)
- [Content destined for `TODO.md`](#content-destined-for-todomd)
- [Process per workstream](#process-per-workstream)
- [References](#references)

<!-- END doctoc -->

## Scope of this document

Five workstreams combine to give an elementary-topos instance for a
computable skeletal category of finite sets, preceded by a sixth, W0,
which carries repository machinery rather than mathematics. Their
content divides by lifespan into three places, and this document is
one of the three.

- Carried forward in `TODO.md`, for the duration of the group: the
  roadmap, the dependency order, the operation table, the
  constructive-layering decision, the cross-workstream interface
  constraints, each workstream's deliverable list, the standing
  repository obligations, and the status of each workstream, among
  the items § Content destined for `TODO.md` fixes. That
  entry is merged to `main` before any workstream begins, so every
  workstream reads it from `main` and no workstream reads another's
  branch. It is itself removed when W5 completes, as `TODO.md`'s
  header prescribes.
- Transient, here: the findings of § Findings and the composition
  argument of § Why the workstreams compose. Both are discharged once
  reviewed. This document is added and removed on the same branch
  that adds the `TODO.md` entry, per `docs/process.md` § Specs and
  plans are transient. § Content destined for `TODO.md` records that
  branch's name and pull-request number — not its merge commit, which
  does not exist when the entry is written — so W0 through W5 can
  recover this document from history when they re-verify the findings
  they consume.
- Persistent, in module docstrings and `docs/index.md`: the design
  rationale — why `ElementaryTopos` carries data, why finite colimits
  are an axiom rather than a consequence — and the two constraints
  that bind any future instance rather than only this group, namely
  the universe convention and the accessor half of the
  instance-registration rule (`Prop` classes as instances,
  data-carrying classes as definitions), which become part of W2's
  module documentation. The rest of that rule is
  `FinSetSkel`-specific registration order and stays in `TODO.md`.
  The morphism-representation choice and the evidence against it
  (§ The representation choice, with the evidence on both sides)
  likewise persist, in W1's module documentation.
  `docs/process.md` § Document only the persistent admits non-obvious
  external constraints on that footing. The branch carrying this
  document also adds the [MacLaneMoerdijk1992] and [Pare1974] entries
  to `docs/references.bib`; those are persistent from the moment they
  are added and precede their Lean citers in W2.

Anything binding on a workstream is in one of the first or third
places, with one class of exception: the route and scope rules
attached to individual deliverables — W1's route for the
isomorphism, W1's restriction on `FinEnum.lean`, W1's choice-free
compression route, and W3's division contingency among them — are
stated here alongside the material that justifies
them, and are recovered with this document rather than duplicated.
Each constrains how a deliverable is done; none produces an artifact
that outlives the group. This document does not fix signatures or
module paths; the proof-strategy sketches it does carry are there
because the cost estimates depend on them. Each workstream has its
own brainstorming spec, adversarial review, plan, and implementation
cycle, written only after the workstreams it depends on are merged —
the pattern `TODO.md` § Polynomial functors already applies.

## Motivation

`Geb` requires a category of finite sets whose morphisms are data:
values that can be pattern-matched, serialised, and compared.

mathlib's skeletal model, `FintypeCat.Skeleton`
(`Mathlib/CategoryTheory/FintypeCat.lean`), takes `X ⟶ Y` to be
`ULift (Fin X.len) → ULift (Fin Y.len)`: a function, not data.
Deciding equality of two such morphisms goes through
`Fintype.decidablePiFintype`, which depends on `Classical.choice`. A
length-indexed vector of codomain indices carries the same
information as first-order data, and its equality is structural.

The two representations are isomorphic. What that isomorphism
transports is small and should not be overstated. The `Skeleton`
namespace holds `mk`, `len`, `ext`, an `Inhabited` instance, the
`SmallCategory` instance, `is_skeletal`, `incl` with its fullness,
faithfulness, essential surjectivity and a `noncomputable`
`IsEquivalence` instance, `equivalence`, and `incl_mk_nat_card`;
`isSkeleton` is in the `FintypeCat` namespace. Two files elsewhere in
mathlib refer to `Skeleton`:
`Topology/Category/LightProfinite/Basic.lean` and
`Condensed/Discrete/Colimit.lean`. The data-carrying results there
are `noncomputable` throughout (§ The derivation lemmas exist, and
their data counterparts are `noncomputable`), so nothing that
computes transports. The `Prop` classes do:
`Adjunction.hasLimitsOfShape_of_equivalence` and its colimit dual
carry `HasFiniteLimits` and `HasFiniteColimits` from `FintypeCat` to
`FintypeCat.Skeleton`, whence `HasEqualizers`, `HasCoequalizers`,
`HasFiniteProducts`, `HasTerminal` and `HasInitial` follow by
instance search. That route is available to `FinSetSkel` through the
isomorphism and is not taken; § Workstreams records why. The results
transported are `Skeletal FinSetSkel` and `IsSkeletonOf`.

## Names fixed here

- `FinSetSkel` — the category defined in W1. `Skel` records that it
  is the skeletal model, parallel to `FintypeCat.Skeleton`.
- `ElementaryTopos` — the class defined in W2. The qualifier
  distinguishes it from a Grothendieck topos; mathlib uses `Topos` in
  `Mathlib/CategoryTheory/Topos/` for sheaf-theoretic material.

W1 through W5 place their modules under `Geb/Mathlib/`, with test
parallels under `GebTests/Mathlib/`; W0 adds no modules. That is
fixed here because it is a cross-workstream fact: W0's relaxation is
scoped to those two roots, and W5 imports modules from every other
workstream. All
other names, including module paths within that root, are settled in
the workstream that introduces them.

## Findings

Verified against the `v4.33.0-rc1` pins in `.lake/packages/` at the
date of this document. Because the repository bumps mathlib on a
weekly cron, each workstream re-verifies the findings it consumes
when it is taken up; the checks are `#print axioms`, `run_cmd` calls
to `Lean.isNoncomputable`, and grep-level, and are cheap to repeat.
The durable content of this section is the pointers, not the axiom
lists or the line numbers.

### mathlib's skeletal finite-set category, and what in it is choice-free

`FintypeCat.Skeleton` is `ULift ℕ`, with

```lean
instance : SmallCategory Skeleton.{u} where
  Hom X Y := ULift.{u} (Fin X.len) → ULift.{u} (Fin Y.len)
  id _ := id
  comp f g := g ∘ f
```

`FintypeCat.Skeleton.instSmallCategory` depends on no axioms. That is
the extent of the choice-free content: `is_skeletal` and `isSkeleton`
both depend on `Classical.choice`, as do `incl` and `equivalence`.
Only the category structure itself is choice-free.

### An isomorphism in `Cat` is achievable

`CategoryTheory.Cat.equivOfIso {C D : Cat} (γ : C ≅ D) : C ≌ D`
(`Mathlib/CategoryTheory/Category/Cat.lean:386`) derives an
equivalence from an isomorphism. Both categories are `SmallCategory`
instances on `Type u`, so both are objects of `Cat.{u, u}`.
`Cat.ext` (`Cat.lean:81`) reduces equality of morphisms in `Cat` to
equality of the underlying functors.

A construction was carried out during review and reported to succeed:
both categories have object type `ULift ℕ`, so `Functor.ext
(fun X => rfl)` applies and the resulting `h_map` goals are
homogeneous, with no residual `eqToHom` obstruction. Between the two
steps the goal needs normalising off `Cat.of`, by
`simp only [Cat.of_α, Functor.toCatHom_toFunctor,
Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor]`; this is mathlib's own
idiom for the same shape, used in `typeToCat.map_id` and `map_comp`
(`Cat.lean:422, 431`; note those carry
`set_option backward.isDefEq.respectTransparency.types false`, which
citing the idiom does not import). A second transparency obstruction
appears after that step: `simp` cannot make progress on the `h_map`
goals while they remain under `Cat.of`. Proving the two functor
composition equalities as standalone lemmas outside that context and
supplying them by `exact` closes both. No artifact of
that construction survives in the tree, and the claim depends on
definitions W1 has not yet written, so W1 establishes it rather than
inheriting it; § W1 — `FinSetSkel`, its isomorphism, and vector
inversion records how to read difficulty in closing it. The
round-trip content is the pair `Vector.ofFn (Vector.get v) = v` and
`(Vector.ofFn f).get = f`. Root-namespace `Vector.ofFn_getElem`
states the first. The second is stated by root `Vector.get_ofFn`,
which is Batteries' (`Batteries/Data/Vector/Lemmas.lean:92`) and not
reachable from any `Mathlib.*` module — the only route is the bare
umbrella `import Mathlib`, which `scripts/lint-imports.sh` forbids in
upstream-eligible files — whereas mathlib's `get_ofFn`
(`Data/Vector/Basic.lean:168`) is `List.Vector`'s. W0 (§ W0 — the
`Batteries.` allow-list, justified in § Reaching Batteries requires
relaxing our import lint) makes the Batteries one reachable; without
it the second direction is proved rather than cited, which is why W0
precedes W1. `Equiv.vectorEquivFin`
(`Mathlib/Data/Vector/Basic.lean:177`) states the corresponding
equivalence of types for `List.Vector`.

The isomorphism is choice-free; the equivalence cannot be, and not
because of the route taken to it. `CategoryTheory.Iso` and
`CategoryTheory.Functor` depend on no axioms, but
`CategoryTheory.Equivalence` depends on `Classical.choice`, so any
term whose type mentions `≌` inherits it — `Cat.equivOfIso` and
`Cat.isoOfEquiv` alike, and equally a hand-built `Equivalence.mk`.
Deriving the isomorphism from an equivalence rather than the reverse
therefore buys nothing. The isomorphism belongs in the choice-free
core, and the equivalence in the wrapper module, which is needed
regardless for the transported `Skeletal` and `IsSkeletonOf` — those
being choice-tainted in mathlib already (§ mathlib's skeletal
finite-set category, and what in it is choice-free).

The equivalence is supplied rather than left to the caller, although
it is the weaker statement and although supplying it costs a
choice-tainted declaration. Its absence would be ambiguous: a caller
who looks for an equivalence and finds none cannot tell that from the
case where none exists, and may construct one rather than look for
something stronger. Defining it as `Cat.equivOfIso` applied to the
isomorphism makes the derivation visible at the point of discovery,
so a caller arriving at the equivalence is led to the isomorphism and
can judge which is wanted.

### The representation choice, with the evidence on both sides

`Mathlib/Data/Vector/Defs.lean` says in full: "Typically, if you are
doing programming or verification, you will primarily use
`Vector α n`, and if you are doing mathematics, you may want to use
`List.Vector α n` instead." The same file records that
`List.Vector`'s API is incomplete relative to `Vector` and that
reducing its use in mathlib is welcome. On axioms, `List.Vector` is
the cleaner of the two: `DecidableEq (List.Vector (Fin m) n)` depends
on no axioms, where `DecidableEq (Vector (Fin m) n)` depends on
`propext` and `Quot.sound`.

Root-namespace `Vector` is chosen notwithstanding, on the grounds
that the morphisms exist to be computed with — array-backed indexing
is constant-time where the list-backed form is linear — and that the
`propext`/`Quot.sound` difference is immaterial, since neither is
`Classical.choice` and the repository accepts both pervasively. The
countervailing evidence is recorded here so the decision is not
revisited on the strength of the half of the quotation that favours
it.

### mathlib has no elementary topos

`Mathlib/CategoryTheory/Topos/Classifier.lean` is a
`deprecated_module (since := "2026-03-03")` forwarding to
`Mathlib/CategoryTheory/Subobject/Classifier/Defs.lean`. No `Topos`,
`IsTopos`, or equivalent class exists in mathlib or in CSLib. The
constituents do exist:

| Constituent | mathlib name | Location |
| --- | --- | --- |
| Subobject classifier (data) | `Subobject.Classifier` | `CategoryTheory/Subobject/Classifier/Defs.lean:81` |
| Subobject classifier (existence) | `HasSubobjectClassifier` | same, line 156 |
| Cartesian structure (data) | `CartesianMonoidalCategory` | `CategoryTheory/Monoidal/Cartesian/Basic.lean:99` |
| Closure (data) | `MonoidalClosed` | `CategoryTheory/Monoidal/Closed/Basic.lean:46` |
| Finite limits (existence) | `HasFiniteLimits` | `CategoryTheory/Limits/Shapes/FiniteLimits.lean:41` |
| Finite colimits (existence) | `HasFiniteColimits` | same, line 88 |

`CartesianClosed` is no longer a class.
`Monoidal/Closed/Cartesian.lean:15` records that it was merged into
`MonoidalClosed`; the name survives as a namespace of derived lemmas
and of the exponential notation `A ⟹ B` for `(ihom A).obj B` (line
42), which is `scoped` and needs `open CartesianClosed` together with
`[Closed A]`. Cartesian closure is `CartesianMonoidalCategory C` together
with `MonoidalClosed C`.

`Subobject.Classifier` has eight fields: `Ω₀`, `Ω`, `truth`,
`mono_truth`, `χ₀`, `χ`, `isPullback`, `uniq`. Of these only `Ω₀`,
`Ω`, `truth`, `χ₀` and `χ` are data; `mono_truth`, `isPullback` and
`uniq` are `Prop`, since `Mono` (`Category/Basic.lean:328`) and
`IsPullback` (`Limits/Shapes/Pullback/IsPullback/Defs.lean:61`) are
both `Prop`. The structure does not require `Ω₀` to be presented as a
chosen terminal object, but mathlib derives that it is one —
`Classifier.isTerminalΩ₀` (`Defs.lean:141`), from the
`Unique (Y ⟶ c.Ω₀)` instance at line 131.
`Classifier.mkOfTerminalΩ₀` (line 109) takes `Ω₀` together with
`IsTerminal Ω₀` and is the constructor W3 uses, so the classifier row
depends on the terminal-object row.

`HasSubobjectClassifier` has instances only for presheaf and sheaf
categories (`Topos/Sheaf.lean:131, 231`). That is a statement about
instance search, not about mathematics: `Type u` is equivalent to
presheaves on the terminal category (`Functor.equiv :
Discrete PUnit ⥤ C ≌ C`, `CategoryTheory/PUnit.lean:54`) and so has a
classifier, but `HasSubobjectClassifier Type` fails to synthesize,
`Type u` not being syntactically `Cᵒᵖ ⥤ Type w`. mathlib carries no
transport of the *class* along an equivalence, though it does carry
one of the structure — `Subobject.Classifier.ofEquivalence`
(`Defs.lean:710`), which `Sheaf.lean:132` uses to derive the class in
one line.

Neither reaches `FinSetSkel`, for a reason that is not about
instances. Presheaf categories are cocomplete; `FinSetSkel` is not,
having no infinite coproducts. It is therefore an elementary topos
that is not a presheaf topos, so mathlib's only classifier instances
are unavailable to it in principle rather than by an accident of
resolution, and row l is new work.

### The derivation lemmas exist, and their data counterparts are `noncomputable`

| Derivation | Lemma | Hypotheses |
| --- | --- | --- |
| finite products from terminal and binary | `hasFiniteProducts_of_has_binary_and_terminal` | `[HasBinaryProducts C] [HasTerminal C]` |
| finite coproducts from initial and binary | `hasFiniteCoproducts_of_has_binary_and_initial` | `[HasBinaryCoproducts C] [HasInitial C]` |
| finite limits from finite products and equalizers | `hasFiniteLimits_of_hasEqualizers_and_finite_products` | `[HasFiniteProducts C] [HasEqualizers C]` |
| finite colimits from finite coproducts and coequalizers | `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts` | `[HasFiniteCoproducts C] [HasCoequalizers C]` |

The first two are in
`CategoryTheory/Limits/Constructions/FiniteProductsOfBinaryProducts.lean`
at lines 106 and 233; the last two are in
`CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`
at lines 141 and 418, with Stacks Project tags `002O` and `002Q`.

All four produce `Prop` classes. Their data-carrying counterparts,
`limitConeOfEqualizerAndProduct` (line 102) and
`colimitCoconeOfCoequalizerAndCoproduct` (line 379), are both
`noncomputable`, because they take `Prop` instances and extract cones
through `getLimitCone`, which is `Classical.choice`. One layer down,
`buildLimit` (line 60), `buildIsLimit` (line 81), `buildColimit`
(line 326) and `buildIsColimit` (line 350) are computable and take
explicit cones. § Chosen cones exist for the generators only records
what that does and does not supply.

### Chosen cones exist for the generators only

Chosen (co)limit cones for an arbitrary finite diagram are not
computably derivable, and no arrangement of the `build*` functions
changes that. `HasFiniteColimits.out` quantifies over arbitrary
`(J : Type) [SmallCategory J] [FinCategory J]`
(`Limits/Shapes/FiniteLimits.lean:91`), and `FinCategory`
(`FinCategory/Basic.lean:45`) carries exactly `fintypeObj` and
`fintypeHom` — no enumeration and no order. `buildColimit` requires
chosen coproduct cocones indexed by `Discrete J` and by
`Discrete (Σ p : J × J, p.1 ⟶ p.2)`
(`LimitsOfProductsAndEqualizers.lean:317`), so assembling its input
means linearising both, and the routes divide in two:

- The choice-extracting routes are `noncomputable`:
  `Fintype.equivFin`, `Finset.toList`, `Multiset.toList`,
  `Trunc.out`, `FinCategory.equivAsType`,
  `FinCategory.categoryAsType`.
- The computable routes have `Trunc` as codomain —
  `Fintype.truncEquivFin` (`Data/Fintype/EquivFin.lean:64`, whose
  module docstring records that a fintype is computably equivalent to
  `Fin (card α)`) and `Fintype.truncEncodable` — and do not escape
  it. `Trunc.lift` requires the lifted function to be constant, and
  the assignment of a coproduct cocone to a linearisation of `J` is
  not: permuting the linearisation preserves the object but changes
  the injections. `Multiset.rec` owes the same obligation, a
  coproduct cocone not being equal to its permutation on the nose:
  addition is commutative in `ℕ`, so the objects `m + n` and `n + m`
  coincide while the two cocones' injections do not. `Encodable`, a
  `LinearOrder` on `J`, and `Quotient.recOnSubsingleton` reduce to it
  as well.
  The `Trunc` codomain is the first closure. `DecidableEq J`, which
  `FinCategory` does not supply, is a second and independent one:
  `truncEquivFin` and `truncEncodable` require it outright, and
  `Fintype.truncFinBijection` (`Data/Fintype/EquivFin.lean:93`) drops
  it only by supplying the forward enumeration
  `Fin (card J) → J` alone, whose inversion is either
  `Equiv.ofBijective`, which is `noncomputable`, or
  `Fintype.bijInv` (`Data/Fintype/Inv.lean:147`), which reinstates
  `DecidableEq`. Indexing a `Cofan` by `Discrete J` needs that
  inverse. `Quot.unquot`, the remaining candidate, is `unsafe` and
  rejected by the kernel in a safe definition.

`CONTRIBUTING.md` § Constructive-only forbids `noncomputable`
outright, so this route is closed rather than merely inconvenient.

What this costs is bounded, and none of it is what `Geb` computes
with. Every generator is over a concrete index shape —
`Discrete PEmpty`, `Discrete WalkingPair`, `WalkingParallelPair` —
where explicit cones are constructible, so the initial and terminal
objects, binary products and coproducts, exponentials, equalizers,
the coequalizer, and the classifier all carry data and compute.
Finite limits and finite colimits over arbitrary finite diagrams are
carried as the `Prop` classes only, obtained from the two derivation
lemmas above, which are `Prop`-valued theorems and so may use choice
freely.

Should chosen cones over `Fin n`-indexed families be wanted later —
for n-ary tuples and variants in the object language, for instance —
the step functions are available: `extendFan`, `extendFanIsLimit`,
`extendCofan` and `extendCofanIsColimit`
(`Constructions/FiniteProductsOfBinaryProducts.lean:47, 61, 173, 187`)
each extend a `Fin n`-indexed cone by one object from binary and
nullary data, and all four are computable notwithstanding the
`noncomputable section` opened at line 29 of that file — that
construct permits noncomputable definitions without individual
markers rather than marking every definition in its scope. The
recursions assembling them are not supplied in usable form:
`hasProduct_fin` (line 96) and `hasCoproduct_fin` (line 223) are both
`private` and `Prop`-valued. Writing them is a fold over `Fin n` and
meets no obstruction; the obstruction above is the step from
`FinCategory J` to a `Fin n` indexing.

### mathlib supplies the index arithmetic

| Construction | mathlib name | Location |
| --- | --- | --- |
| exponential object encoding | `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` | `Algebra/BigOperators/Fin.lean:580` |
| product object encoding | `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)` | `Logic/Equiv/Fin/Basic.lean:334` |
| coproduct object encoding | `finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)` | `Logic/Equiv/Fin/Basic.lean:228` |
| cartesian structure from chosen cones | `CartesianMonoidalCategory.ofChosenFiniteProducts` | `Monoidal/Cartesian/Basic.lean:189` |
| classifier from a terminal `Ω₀` | `Classifier.mkOfTerminalΩ₀` | `Subobject/Classifier/Defs.lean:109` |

`finFunctionFinEquiv` is the base-`m` digit encoding and carries
`_apply` and `_single` lemmas. `ofChosenFiniteProducts` takes a
terminal cone and a family of binary cones, so
`CartesianMonoidalCategory` reduces to those rather than to
associators with pentagon and triangle identities. These are the
reason most of W3's rows are thin: the arithmetic that would
otherwise dominate the exponential and product constructions is
already present, and what remains for the exponential is less than
it appears: `Adjunction.adjunctionOfEquivRight`
(`Adjunction/Basic.lean:671`) builds `tensorLeft X ⊣ _` from an
object map, a hom-level `Equiv`, and a single naturality equation,
deriving the right adjoint's action on morphisms. No functor, unit,
counit or triangle identity is constructed by hand.

### mathlib's categorical vocabulary is choice-tainted

The taint is in the types, so any declaration mentioning them
inherits it:

```text
CategoryTheory.Category                    no axioms
CategoryTheory.Functor                     no axioms
CategoryTheory.Cat                         no axioms
CategoryTheory.Iso                         no axioms
CategoryTheory.Mono                        no axioms
CategoryTheory.Equivalence                 propext, Classical.choice, Quot.sound
CategoryTheory.Limits.Cone                 propext, Classical.choice, Quot.sound
CategoryTheory.Limits.IsLimit              propext, Classical.choice, Quot.sound
CategoryTheory.Limits.LimitCone            propext, Classical.choice, Quot.sound
CategoryTheory.Subobject.Classifier        propext, Classical.choice, Quot.sound
CategoryTheory.CartesianMonoidalCategory   propext, Classical.choice, Quot.sound
CategoryTheory.MonoidalClosed              propext, Classical.choice, Quot.sound
```

Choice-freedom is unavailable to any declaration whose statement
mentions this vocabulary. It remains available to everything beneath,
and the discipline is to keep as much as possible beneath: each
workstream splits into a choice-free module carrying the
constructions and the content of their universal properties — stated
over vectors and `Fin`, quantified and proved directly — and a
wrapper module carrying only the mathlib structures, whose fields are
those choice-free terms and whose obligations are discharged by those
choice-free lemmas. A coequalizer wrapper, for instance, supplies
`IsColimit`'s `desc`, `fac` and `uniq` from a mediating vector and
lemmas that the choice-free module has already established
pointwise; the wrapper adds no argument, only packaging.

`GebMeta.detectNonstandardAxiom` fails `lake lint` for any
declaration outside `{propext, Quot.sound}` unless its module is
listed in `GebMeta.classicalAllowedModules`. Only wrapper modules are
listed, together with their `GebTests` parallels. Allowlisting a
module that contains an argument rather than packaging would be
writing choice-tainted code the interaction with mathlib does not
force, which `CONTRIBUTING.md` § Constructive-only rules out.

This is the layering `TODO.md` § Complete Theorem 2.4 for `IndRec`
already describes — "the wrapper is kept thin" — and the existing
allowlist entries `PFunctor.Slice.Functor`,
`PFunctor.Presheaf.Functor`, `PFunctor.Univariate.Initial` and
`CategoryTheory.Grothendieck` are wrappers of that kind.

Choice-taint is not `noncomputable`.
`Mathlib/CategoryTheory/Monoidal/Types/Basic.lean:24` declares
`typesCartesianMonoidalCategory : CartesianMonoidalCategory (Type u)`
as a plain instance, and `Monoidal/Closed/Types.lean:46` does the
same for `MonoidalClosed (Type v₁)`. `noncomputable` appears on the
extraction direction only — `Prop`, `Trunc`, or quotient to data:
`getLimitCone`, `CartesianMonoidalCategory.ofHasFiniteProducts`,
`ChosenPullbacksAlong.ofHasPullbacksAlong`, and the routes named in
§ Chosen cones exist for the generators only. Building data directly
is computable; extracting it is not. The repository's two rules track
that distinction: `noncomputable` is forbidden everywhere,
`Classical.choice` is permitted per module.

### Batteries has union-find; the closure induction is ours

`Batteries/Data/UnionFind/Basic.lean` and `.../Lemmas.lean` give a
disjoint-set structure with path compression and union by rank.
`Equiv self a b` is `self.rootD a = self.rootD b` (`Basic.lean:583`).
`Lemmas.lean` proves

```lean
@[simp] theorem equiv_empty : Equiv empty a b ↔ a = b
@[simp] theorem equiv_push : Equiv self.push a b ↔ Equiv self a b

theorem equiv_union {self : UnionFind} {x y : Fin self.size} :
    Equiv (union self x y) a b ↔
    Equiv self a b ∨ Equiv self a x ∧ Equiv self y b
                   ∨ Equiv self a y ∧ Equiv self x b
```

`equiv_empty`, `equiv_push`, `equiv_union`, `find_size`, `arr_link`,
`linkAux_size` and `rootD_rootD` all depend only on `propext` and
`Quot.sound`, so W4's non-categorical declarations can be
choice-free.

Three obligations remain with W4, and the algorithm being inherited
should not be read as the proof being inherited:

- `empty` has size 0 — `mkEmpty c` sets `arr := Array.mkEmpty c`,
  allocating capacity but no elements — and `union` requires
  `x y : Fin self.size`, so reaching size `m` takes `m` applications
  of `push`; `equiv_push` is the bridging lemma.
- Batteries proves `find_size` (`Basic.lean:407`) and `linkAux_size`
  (`Basic.lean:487`) but has no `size_union` or `size_link`. Since
  `union` is `find`, `find`, `link` (`Basic.lean:535`), W4 derives
  size preservation before the fold's `Fin self.size` obligations can
  be discharged. It follows from `arr_link` (`Lemmas.lean:43`),
  `linkAux_size` and `find_size`.
- `equiv_union` is a one-edge step lemma, stating that one `union`
  merges the class of `x` with the class of `y` and changes nothing
  else. The statement that the folded structure's `Equiv` is the
  equivalence closure of `{(f i, g i)}` is an induction W4 writes.

What is inherited is the algorithm and its per-step specification,
which is what makes the near-linear complexity available; the fold
and its correctness are W4's.

### Reaching Batteries requires relaxing our import lint

`scripts/lint-imports.sh` restricts `Geb/Mathlib/` to the prefixes
`Mathlib.` and `Geb.Mathlib.`, so `Batteries.` imports fail the
floodgate check. mathlib imports `Batteries.` in over a hundred
files under `Mathlib/`. The precedent matching our use — a Batteries
data module imported into mathematical content, not a tactic
import — is
`Mathlib/Data/Vector/Basic.lean:13`,
`public import Batteries.Data.Fin.Lemmas`. Batteries is already a
transitive dependency through mathlib, so permitting it adds no
package.

mathlib contains no reference to `UnionFind`. A `Geb/Mathlib/` module
importing `Batteries.Data.UnionFind` would therefore introduce a
mathlib-to-Batteries dependency edge that does not yet exist. Whether
upstream accepts that edge is a maintainer judgement rather than a
fact in the tree, so it is a review risk for W4's eventual upstream
submission rather than a settled question. That submission outlives
this group, so W4 records the question as a
`TODO.md` § Triggers (do when condition fires) entry, its condition
being the preparation of W4's upstream submission, rather than
leaving it with content W5 removes.

### Inverting an injective vector, shared by two rows

The operation inverts an injective `ι : Vector (Fin n) k` — the
vector, not a function `Fin k → Fin n`, since morphisms are vectors
here. mathlib packages the inverse, its compression counterpart and
both round-trip laws in one declaration,
`List.Nodup.getEquiv` (`Data/List/NodupEquivFin.lean:55`):

```text
List.Nodup.getEquiv : [DecidableEq α] → (l : List α) → l.Nodup →
    Fin l.length ≃ { x // x ∈ l }
```

Being an `Equiv`, its round trips are `left_inv` and `right_inv`;
being total on the subtype, it needs neither an `Option` nor a
totality side condition. `k = 0` remains reachable — the subtype is
then empty and the equivalence is between empty types.

It depends on `Classical.choice` through exactly one ingredient,
`List.idxOf_lt_length_iff` (`Init/Data/List/Find.lean:1199`).
Substituting `List.idxOf_lt_length_of_mem` (`:1180`, `propext`
alone) gives a choice-free rebuild in six lines, and the compression
follows in three more from `(List.finRange n).filter p` with
`List.nodup_finRange` and `Equiv.subtypeEquivRight`. Both were
elaborated at `propext, Quot.sound`. W1 carries the rebuild.

The alternatives are worse on axioms rather than better. Core's
`Vector.finIdxOf?` (`Init/Data/Vector/Basic.lean:426`) is itself
`propext`-only, but its round-trip laws are `Array`-level and
`Classical.choice`-dependent (`Array.finIdxOf?_eq_some_iff`,
`Init/Data/Array/Find.lean:810`), and `Vector.finIdxOf?` is defined
through `toArray`, so a bridge would be owed as well.
`Function.Injective.invOfMemRange` (`Data/Fintype/Inv.lean:51`) is
`Classical.choice`-dependent too, and is stated over functions.

- The equalizer is carried by the indices at which `f` and `g` agree.
  Its mediating map applies the inverse of the canonical injection to
  a morphism already known to factor through the agreement set;
  uniqueness follows from injectivity of that same injection.
- The coequalizer is carried by the union-find roots, which form a
  subset of `Fin m`; the roots are arbitrary members of `[0, m)` and
  must be renumbered to `[0, k)` before they name an object. The
  inverse is applied to `rootD j`, which is a root by `rootD_rootD`.

The classifier is not a third consumer at the data level: `χ m` is
the characteristic vector of the image and needs decidable membership
only. The fields that would use an inverse, `isPullback` and `uniq`,
are `Prop`; their content is proved choice-free over vectors in W3's
core like everything else, and only their `Subobject.Classifier`-
shaped restatement sits in the wrapper (constraint 8).

`Finset.orderIsoOfFin` and `Finset.orderEmbOfFin` express the
compression and depend on `Classical.choice`. `Finset.sort` depends
on neither,
but `Finset.mem_sort` — the lemma stating that the sorted list
enumerates exactly the satisfying indices, which is the content of
the operation — depends on `Classical.choice`. The choice-free route
is `(List.finRange n).filter p` with `List.mem_filter`, which depends
on `propext` alone.

The operation is consumed by W3 and W4, so it is placed in W1, whose
subject is the representation; that is what keeps W3 and W4
independent of each other.

## Constructive layering

mathlib's limit and classifier interfaces split into data-carrying
and existence-asserting forms. `HasLimit` is a `Prop` class asserting
`Nonempty (LimitCone F)` (`Limits/HasLimits.lean:84`);
`HasFiniteProducts`, `HasFiniteLimits`, `HasFiniteColimits` and
`HasSubobjectClassifier` are `Prop` classes in the same style. By
contrast `CartesianMonoidalCategory`, `MonoidalClosed` and
`Subobject.Classifier` carry their data.

`ElementaryTopos C` carries these fields, by mathlib type. Their
signatures are W2's to fix; the types and their dependencies are
fixed here because W3, W4 and W5 must produce and consume them.

| Field | mathlib type | Supplies rows |
| --- | --- | --- |
| cartesian | `CartesianMonoidalCategory C` | b, d, and hence f |
| closed | `MonoidalClosed C`, over the cartesian field | g |
| initial | `ColimitCocone` over `Discrete PEmpty` | a, and with binary coproducts hence e |
| binary coproducts | `ColimitCocone` over `Discrete WalkingPair`, a family | c, and with initial hence e |
| equalizers | `LimitCone` over `WalkingParallelPair`, a family in the two morphisms | h |
| coequalizers | `ColimitCocone` over `WalkingParallelPair`, a family in the two morphisms | i |
| classifier | `Subobject.Classifier C`, with `Ω₀` the cartesian field's terminal | l |
| finite limits | `HasFiniteLimits C` | j |
| finite colimits | `HasFiniteColimits C` | k |

The last two are `Prop` and are derivable inside the class from the
data fields, so they are redundant in the same sense the colimits are
redundant in the definition. They are fields because the definition
transcribed from [MacLaneMoerdijk1992] names finite limits and finite
colimits, and because they are what a consumer of `[ElementaryTopos
C]` requires. W2 may instead expose them as derived instances. That
is not a free substitution: deriving them generically obliges W2 to
derive `HasFiniteCoproducts` generically too, so rows e, j and k
become W2's one-time derivations rather than per-instance work, they
drop out of W3's and W5's assignments, and W5 reduces to instance
assembly. Row f is unaffected either way, the cartesian field
supplying `HasFiniteProducts` directly. W3 and W5 proceed on the
field form regardless of W2's eventual choice, W3 being independent
of W2 and possibly earlier: should W2 later take the derived-instance
route, W3's rows e and j and W5's row k become redundant `Prop`
instances, which is harmless by proof irrelevance. The operation
table and constraint 5 assume the field form.

Terminal and binary products are not separate fields: they are
reached through the cartesian field only, so that the class carries
one terminal object rather than two that are canonically isomorphic
without being definitionally equal.

Two dependencies among the fields are not optional, and they differ
in how they are enforced. `MonoidalClosed C` takes
`[MonoidalCategory C]` as an instance parameter, supplied by
`CartesianMonoidalCategory`, so the closed field is typed relative to
the cartesian field and the dependency is carried by the field's own
type. The classifier's `Ω₀` must likewise be the cartesian field's
terminal object, but `Subobject.Classifier` bundles `Ω₀` as a field
of its own, so no typing of the classifier field expresses this. W2
therefore chooses the mechanism, subject to the classifier field's
type remaining `Subobject.Classifier C`: constraint 2 forbids a
bespoke bundle of W2's own, since W3 must produce the field without
importing W2. A coherence field asserting the identification meets
that condition. Which mechanism it chooses is W2's; that the class
enforce it
rather than leaving it to each instance is fixed here, since
otherwise a general `[ElementaryTopos C]` may carry two unrelated
terminals and the classifier's universal property would not compose
with the cartesian structure.

The reason for carrying data at all applies at two scales, and is the
same reason both times: a `Prop` form is indifferent to a distinction
that matters computationally, because all limits of a diagram are
isomorphic and none of them run.

- Within a construction, carrying `LimitCone F` rather than
  `Nonempty (LimitCone F)` decides whether anything computes.
  Recovering data from the `Prop` form is `getLimitCone`, which is
  `Classical.choice` and `noncomputable`, and `noncomputable` is
  forbidden by `CONTRIBUTING.md` § Constructive-only.
- Across constructions, carrying the coequalizer as a data field
  rather than deriving it decides which algorithm runs. Colimits are
  redundant as an axiom: [Pare1974] first published the result that
  an elementary topos has finite colimits. But a derived construction
  is whichever one the general proof yields, and that is not
  union-find; an
  instance that knows a better algorithm can supply it only if the
  class has a field to put it in. (The standard route is the
  monadicity of the power-object functor, under which the
  coequalizer routes through `P (Fin m) = Fin (2 ^ m)`, exponential
  in `m` against union-find's near-linear in `n + m`. That
  characterisation of the proof, and the attribution of the result
  itself, are recorded from metadata and secondary sources; neither
  was verified against [Pare1974] directly, and a secondary source
  reports the approach as first introduced by C. J. Mikkelsen and
  first published by Paré, a priority question W2 settles with the
  rest: the publisher
  returned an access denial for both the article page and its PDF, a
  `theoremsearch` query returned no entry for the result, and the
  copy of [MacLaneMoerdijk1992] located exceeded the retrieval size
  limit. W2 verifies it when citing the work in Lean. The design
  decision does not depend on it: any derivation yields the general
  construction rather than the chosen one.)

Nothing is foreclosed by the redundancy. [Pare1974] can later be
added as an alternative constructor, taking finite limits,
exponentials and a classifier and building the colimits, alongside
the full-data constructor rather than replacing it — the shape
`CartesianMonoidalCategory.ofChosenFiniteProducts` already has.

The `Prop` instances are still declared, as the interface through
which mathlib's lemmas apply; `HasLimit.mk (d : LimitCone F)` is the
bridge. They are packaging, so they belong in the wrapper modules
with the rest of it (§ mathlib's categorical vocabulary is
choice-tainted), not in the choice-free modules whose content they
re-express.

The definition of an elementary topos taken here — finite limits,
finite colimits, cartesian closure, subobject classifier — is a
transcription from [MacLaneMoerdijk1992], which mathlib cites under
its own key `MM92` (`Subobject/Classifier/Defs.lean:52`), with one
deliberate redundancy, the colimits, for the reason above. Both
entries are in `docs/references.bib`; W2 cites them from its Lean
sources.

## Workstreams

```text
  W0 Batteries allow-list
   │
   ├► W1 FinSetSkel ────┬──────► W3 topos structure ──────┐
   │                    │            (a–h, j, l, m)       │
   │                    └──────► W4 coequalizers ─────────┼──► W5
   │                                 (i, union-find)      │  unification
   └► W2 ElementaryTopos ───────────────────────────────────┘
```

W0 carries repository machinery rather than mathematics and precedes
the rest. W1 and W2 are independent of each other. W3 and W4 both
depend on W1 and are independent of each other and of W2. W5 depends
on W1 through W4.

W4 requires W0, needing `Batteries.Data.UnionFind`. W1 does not
require it but is shortened by it, root `Vector.get_ofFn` being
Batteries' (§ An isomorphism in `Cat` is achievable); W0 therefore
precedes W1 rather than merely W4, which costs nothing, W0 being
independent of everything. W2 needs nothing from W0, its field types
being mathlib types throughout; the diagram orders it after W0 as
scheduling convenience, not dependency, and W2 may begin whenever.

The topos structure divides as follows. "`Fin k`" abbreviates the
object of `FinSetSkel` whose length is `k`.

| | Operation | Carrier or source | Workstream |
| --- | --- | --- | --- |
| a | Initial object | `Fin 0` | W3 |
| b | Terminal object | `Fin 1` | W3 |
| c | Binary coproducts | `m + n`, via `finSumFinEquiv` | W3 |
| d | Binary products | `m * n`, via `finProdFinEquiv` | W3 |
| e | Finite coproducts (`Prop`) | from a and c | W3 |
| f | Finite products (`Prop`) | from b and d | W3 |
| g | Exponentials (`MonoidalClosed`) | `Fin m ⟹ Fin n` is `Fin (n ^ m)` | W3 |
| h | Binary equalizers, and `HasEqualizers` | agreement subset | W3 |
| i | Binary coequalizers, and `HasCoequalizers` | union-find | W4 |
| j | Finite limits (`Prop`) | from f and h | W3 |
| k | Finite colimits (`Prop`) | from e and i | W5 |
| l | Subobject classifier | `Fin 2`, via `mkOfTerminalΩ₀` | W3 |
| m | `Mono` is an injective vector | — | W3 |

Rows e, f, j and k could instead be transported wholesale from
`FintypeCat` as `Prop` instances (§ Motivation). They are not. The
transport yields `Prop` only, so it touches none of the rows that
carry data; it would replace four one-line derivation-lemma
applications with two lines; and it would put W1's isomorphism on
W3's and W5's critical path, which item 1 of § Why the workstreams
compose deliberately keeps it off. Deriving each row from the
structure below it also keeps the `Prop` instance answering to the
data this category is built to compute with.

Rows e, j and k are the derivation lemmas of § The derivation lemmas
exist, and their data counterparts are `noncomputable`; row f is
discharged instead by rows b and d together, through the
`HasFiniteProducts` instance that `CartesianMonoidalCategory`
supplies at priority 100 (`Monoidal/Cartesian/Basic.lean:498`), so
`hasFiniteProducts_of_has_binary_and_terminal` is not invoked
directly. `HasTerminal` and `HasBinaryProducts` follow from the same
field through `hasLimitsOfShape_discrete`
(`Limits/Shapes/FiniteProducts.lean:43`) at default priority. Rows e,
f, j and k are `Prop`-valued, per § Chosen cones exist for the
generators only. Row k is the only row whose two inputs come from
different workstreams, which is why it is W5's.

Row g uses `finFunctionFinEquiv` instantiated at `m := n, n := m`:
the lemma reads `(Fin n → Fin m) ≃ Fin (m ^ n)`, and `MonoidalClosed`
takes `Closed X` to carry `adj : tensorLeft X ⊣ rightAdj`
(`Monoidal/Closed/Basic.lean:39–43`) with `ihom A = Closed.rightAdj A`
by `rfl` (line 76). `ihom A` is a functor, so the exponential object
is `(ihom A).obj B`, written `A ⟹ B`; here `Fin m ⟹ Fin n` is
`Fin (n ^ m)`.

Row m is the characterisation of `Mono` in `FinSetSkel` as an
injective vector. It is a prerequisite of row l. mathlib has no such
result for `FintypeCat` or its skeleton, but the shape is standard
and `SimplexCategory.mono_iff_injective`
(`AlgebraicTopology/SimplexCategory/Basic.lean:623`) is a three-line
proof of it via `Functor.mono_map_iff_mono`; W3 tries that route
before writing one by hand. It is not the only place the categorical and
the data notions meet — rows h and i each reconcile a categorical
equation with a pointwise condition, using the morphism
extensionality and application lemmas W1 supplies, and row l's
`isPullback` and `uniq` obligations reconcile `IsPullback` with a
pointwise condition — but it is the only place a named mathlib
predicate on a single morphism must be characterised.

W3 holds eleven of the thirteen rows but is not correspondingly
large: rows a, b, e, f and j are near-trivial, and c, d and h are
small given the index equivalences of § mathlib supplies the index
arithmetic. Its substantial rows are g, whose adjunction and
naturality are not supplied by `finFunctionFinEquiv`, and the pair l
and m. Should W3's own spec find it oversized, the division is g, l
and m against the rest; that contingency is recorded rather than
acted on.

### W0 — the `Batteries.` allow-list

`Batteries.` admitted to the `Geb/Mathlib/` and `GebTests/Mathlib/`
allow-lists in every place that states them, per § Standing
repository obligations. No Lean content, so no choice-free/wrapper
split and no `GebMeta.classicalAllowedModules` entry. Its own branch
to `main`: it is CI machinery rather than mathematics, reviewable in
isolation, and bundling it into a workstream would put two concerns
on one branch.

### W1 — `FinSetSkel`, its isomorphism, and vector inversion

- The `SmallCategory` instance at an arbitrary universe, with objects
  `ULift ℕ` and morphisms length-indexed vectors of codomain indices;
  identity and composition in vector form.
- Morphism extensionality, and the lemmas relating identity and
  composition to indexwise application. W1 fixes their `simp`
  orientation — application-normal form — as the shared normal form
  for W3 and W4, which are concurrent and would otherwise each choose
  one, the divergence appearing only when W5 imports both.
- `DecidableEq` on morphisms.
- The choice-free rebuild of `List.Nodup.getEquiv` and the predicate
  compression over it, per § Inverting an injective vector, shared by
  two rows — nine lines in total, the mathlib original being
  `Classical.choice`-dependent through one substitutable lemma.
- The `ULift`-transported forms of `finProdFinEquiv`,
  `finSumFinEquiv` and `finFunctionFinEquiv`.
- The isomorphism in `Cat` to `FintypeCat.Skeleton`, in the
  choice-free core; and, in an allowlisted wrapper module, the
  equivalence defined as `Cat.equivOfIso` of it together with the
  transported `Skeletal` and `IsSkeletonOf` results. The equivalence
  is supplied for discoverability rather than necessity, and its
  definition points back at the isomorphism (§ An isomorphism in
  `Cat` is achievable).
- The `docs/index.md` entry, and the module docstring recording the
  morphism-representation choice together with the evidence against
  it, whose purpose is to stop the decision being revisited.

The `ULift` placement in the morphism type is settled here, subject
to the hom type inhabiting `Type u` so that the `SmallCategory`
instance typechecks and both categories inhabit `Cat.{u, u}`.

The isomorphism is the one deliverable nothing else depends on
(§ Why the workstreams compose item 1), and it is on a branch W3, W4
and W5 all wait for. It is retained here because it is short: a
separate workstream's spec, plan, review and PR would exceed it
several times over. The route is the one in § An isomorphism in `Cat`
is achievable — `Cat.ext`, the `Cat.of` normalisation recorded
there, `Functor.ext (fun X => rfl)`, then the two vector round-trip
equations, one per direction. Difficulty in closing it therefore
indicates that the approach has gone wrong, not that the estimate
was wrong; the response is to return to that route rather than to
enlarge the scope. The two instance-transparency obstructions are
excepted: both are named in § An isomorphism in `Cat` is achievable,
and meeting them is the route working, not failing.

W1 adds to `Geb/Mathlib/Data/FinEnum.lean` what it needs without
changing existing signatures. That module has four importers in
`Geb/` plus a test module, and restructuring it is a refactor of the
polynomial-functor decidability layer — a second concern, and one on
the branch that both W3 and W4 depend on. Any such restructuring is
its own branch, per `CONTRIBUTING.md` § Concern shape.

### W2 — the `ElementaryTopos` class

- The class of § Constructive layering, with the fields of that
  table.
- Derived accessors, and the derived `Prop` instances.
- The `docs/index.md` entry, and the module docstring carrying
  constraint 3 and constraint 5's accessor rule together with the
  rationale for carrying data and for taking finite colimits as an
  axiom.
- Citations of [MacLaneMoerdijk1992] and [Pare1974] in its Lean
  sources.

Its own module, depending on no part of `FinSetSkel`. Its field types
are mathlib types throughout, which is what keeps W3 and W4
independent of it. W2 is the one workstream whose deliverable is
itself packaging — a class over mathlib structures — so it is a
wrapper module in the sense of constraint 8, with no choice-free
counterpart to sit beneath it.

### W3 — the topos structure other than coequalizers

Rows a through h, j, l and m of the operation table, split per
constraint 8: the carriers, the mediating maps, and the content of
each row's universal property — including row m, whose statement
mentions only `Mono`, which is axiom-free, so it belongs choice-free
— in choice-free modules; the
`CartesianMonoidalCategory`, `MonoidalClosed`,
`Subobject.Classifier`, `LimitCone`, `ColimitCocone` and `Prop`
instances in wrappers over them.

### W4 — binary coequalizers by union-find

Row i. Fold `UnionFind.union` over the domain, coequalising `f i`
with `g i` at each index; renumber the roots by the W1 inversion;
prove size preservation, the closure induction, and the universal
property, per § Batteries has union-find; the closure induction is
ours. All of that is choice-free: the union-find core, the
renumbering, and the mediating map with its existence and uniqueness
stated over vectors. The wrapper supplies `ColimitCocone` and
`HasCoequalizers` from those terms, per constraint 8. Also the
`TODO.md` § Triggers (do when condition fires) entry
recording the mathlib-to-Batteries dependency-edge question against
the preparation of W4's upstream submission, which outlives the
group.

### W5 — unification

Row k, by
`hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts`, and the
`ElementaryTopos FinSetSkel` instance assembled from W3's and W4's
outputs. Both are packaging, so W5 is a wrapper module throughout,
per constraint 8. Removes the `TODO.md` entry.

## Why the workstreams compose

The claim is that W5 is discharged from the interfaces of W1 to W4
without new mathematics. It rests on four statements.

1. **The category exists and its morphisms are data.** W1's
   `SmallCategory` instance, together with the extensionality and
   application lemmas, is what W3 and W4 need in order to state and
   prove their universal properties, and what W5 needs in order to
   name the category. The isomorphism to `FintypeCat.Skeleton` is not
   among W5's mathematical dependencies: nothing W3, W4 or W5 states or
   proves refers to it. It is on W1's branch, so it is on the
   schedule; § W1 — `FinSetSkel`, its isomorphism, and vector
   inversion records why that is accepted.
2. **`ElementaryTopos` is exactly what W3, W4 and W5 produce.** Every
   field of the § Constructive layering table is supplied by rows of
   the operation table: W3 supplies the cartesian, closed, initial,
   binary-coproduct, equalizer and classifier fields and the
   finite-limit `Prop`; W4 the coequalizer field; W5 the
   finite-colimit `Prop`. Reading the § Constructive layering
   table's "Supplies rows" column in the construction direction, ten
   rows are field sources — a, b, c, d, g, h, i, j, k, l — and the
   remaining three are prerequisites: e of k, f of j, and m of l.
   Each of the nine fields of that table has a source, and no row is
   neither a source nor a prerequisite. Should W2 take the
   coherence-field mechanism for the classifier
   (§ Constructive layering), that tenth field has no row
   of its own: constraint 6 has W3 build row l over the cartesian
   terminal, which discharges it by `rfl`.
3. **W5's remaining mathematical work is one lemma application and
   field assignment.** Row k is `Prop`-valued, so
   `hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts`
   discharges it from hypotheses W3 and W4 establish, with no cone
   assembly and no fold — a consequence of § Chosen cones exist for
   the generators only, since the class carries chosen cones for the
   generators only and W5 therefore never builds a cocone over an
   arbitrary finite diagram. Assembling the instance from W3's and
   W4's outputs is field assignment, not construction, given
   constraint 5 below.
4. **Eight interface constraints cross workstream boundaries.** These
   are the decisions that would be expensive to discover at W5.
   All eight are reproduced in `TODO.md`; constraint 3 and
   constraint 5's accessor rule also become part of W2's module
   documentation, since those bind any future instance and not only
   this group.
   1. *Data for generators, `Prop` for finite (co)limits.* Settled in
      § Constructive layering; binding on W2 through W5.
   2. *Field types for the topos structure are mathlib types.* Were
      they W2's own, W3 and W4 would import W2 and the claimed
      independence would fail. A `Prop` coherence field of W2's own
      (constraint 6) is admitted, no workstream but W5 producing
      it.
   3. *Universe convention.* `ElementaryTopos` is stated over
      `(C : Type u) [Category.{v} C]`, matching mathlib convention.
      `SmallCategory C` is `Category.{u} C`
      (`Category/Basic.lean:268`), so a formulation over it would
      admit `FinSetSkel`; what it would foreclose is every non-small
      instance, `Type u` itself among them. The general form is
      therefore chosen for what it keeps open, not to make
      `FinSetSkel` fit.
   4. *`ULift` placement.* W1 settles where the `ULift` sits in the
      morphism type, and supplies the transported forms of the three
      index equivalences, rather than leaving each of W3's rows to
      repeat the transport. Every object carrier in the operation
      table is `Fin`-shaped universe-zero data and the equivalences
      are
      `Type 0` statements, so each must cross W1's choice.
   5. *Instance registration.* W3 and W4 register as instances both
      what they consume and what a later workstream consumes. W3
      needs `CartesianMonoidalCategory FinSetSkel` in scope to state
      row g at all; rows e and j elaborate against `HasInitial`,
      `HasBinaryCoproducts`, `HasFiniteProducts` and `HasEqualizers`;
      and row k's two hypotheses are `HasFiniteCoproducts`, which W3
      declares as row e, and `HasCoequalizers`, which W4 declares
      from its row-i data by
      `hasCoequalizers_of_hasColimit_parallelPair`
      (`Limits/Shapes/Equalizers.lean:1287`) — `HasCoequalizers` is
      `HasColimitsOfShape WalkingParallelPair C`, quantifying over
      more functors than `HasColimit.mk` alone supplies. Rows b and
      d are
      exposed only through the cartesian instance, never registered
      independently, or `FinSetSkel` acquires two non-defeq terminals
      and products. Each row's data term is exported under a stable
      public name, since W5's assembly consumes terms and not only
      instances.

      W2's accessors from `[ElementaryTopos C]` divide by whether
      they carry data. To the `Prop` classes — `HasFiniteLimits`,
      `HasFiniteColimits`, and the generator classes — they are
      instances, which is what makes mathlib's lemma library apply to
      a bare `[ElementaryTopos C]` hypothesis; two resolution routes
      are harmless there because the classes are `Prop` and proof
      irrelevance identifies their inhabitants. To the data-carrying
      classes — `CartesianMonoidalCategory`, `MonoidalClosed` — they
      are definitions, because two routes to data need not agree
      definitionally. W5 builds `instance : ElementaryTopos
      FinSetSkel` from W3's and W4's registered instances, so its
      projections are defeq to them, and the data-carrying classes
      resolve for `FinSetSkel` through W3's registrations alone.
   6. *Classifier coherence.* The class enforces that the classifier
      field's `Ω₀` is the cartesian field's terminal object, by a
      mechanism W2 chooses that leaves the field's type
      `Subobject.Classifier C`, per § Constructive layering. W3
      builds row l over its own row b as exposed through the
      cartesian instance, so that its classifier satisfies whichever
      form W2 settles on, and the coherence obligation is `rfl`.
   7. *Placement of shared material.* `DecidableEq` on morphisms, the
      injective-vector inversion and the transported index
      equivalences live in W1, so W3's image-membership and W4's root
      equality derive from a common source. A shared lemma discovered
      after W1 merges goes on its own branch off `main`, which W3 and
      W4 both rebase onto, rather than being duplicated or bundled
      into whichever workstream finds it first.
   8. *Choice-free core, thin wrapper.* Every workstream splits its
      modules as § mathlib's categorical vocabulary is choice-tainted
      prescribes: constructions and the content of their universal
      properties choice-free over vectors and `Fin`; mathlib
      structures and `Prop` instances in a wrapper whose fields are
      those terms. Only wrapper modules reach
      `GebMeta.classicalAllowedModules`. A workstream whose entire
      deliverable is packaging — W2 and W5 — is a wrapper throughout,
      with no choice-free counterpart beneath it. This binds W1
      through W5 and is what keeps the choice-tainted surface to what
      mathlib forces.

`simp` discipline is fixed at the morphism-application layer by W1
(constraint 7's placement, and W1's deliverable list). One layer up,
W3 and W4 each add carrier-level lemmas — index-equivalence
transports, `rootD` normalisation — that first meet at W5. Neither
marks a transport lemma `simp` in a direction that rewrites the
other's normal form; beyond that the risk is accepted and W5
reconciles.

## Standing repository obligations

Both are reproduced in `TODO.md`, since they bind workstreams
beginning after this document is removed.

- **`Batteries.` is admitted to the `Geb/Mathlib/` and
  `GebTests/Mathlib/` allow-lists** — this is W0's whole content —
  in every place that states them,
  not only in the script: `scripts/lint-imports.sh` and its comment
  header, the § Subtree import rules table in
  `docs/rules/upstream-eligible.md`, the `Geb/Mathlib/` line of
  `docs/index.md` § Directory structure, and a case in
  `scripts/tests/test-lint-imports.sh`. The first three state the
  same rule and the last enforces it, so relaxing the script alone
  would leave a binding rule file asserting a rule its enforcement no
  longer implements — the divergence `CONTRIBUTING.md` § Floodgate
  test exists to prevent. The header carries the justification, so
  that it survives this document: mathlib imports Batteries data
  modules directly (`Mathlib/Data/Vector/Basic.lean`,
  `public import Batteries.Data.Fin.Lemmas`), and Batteries is
  already a transitive dependency through mathlib, so permitting it
  adds no package. This is W0, merged before W1 (§ Workstreams). The
  `Geb/Cslib/` allow-lists are extended only if a file under them
  needs it, which none does.
- **`GebMeta.classicalAllowedModules` gains each new wrapper
  module** together with its `GebTests` parallel, appended by the
  workstream that introduces it. W1 through W5 each entail such an
  amendment, W0 adding no Lean content, and none for anything but a
  wrapper: the choice-free
  modules that carry the constructions and their universal properties
  are not listed, per constraint 8.

Both concurrent pairs — W1 with W2, and W3 with W4 — append to files
the other also appends to: `GebMeta.classicalAllowedModules` (a
single bracketed literal beginning at `GebMeta.lean:59`, whose final
element carries the `].foldl` terminator), the `TODO.md` status
table, `docs/index.md`, and any directory index file they share.
These are ordinary textual conflicts, resolved by rebasing the later
sibling before merge; the earlier sibling's merge to `main` is what
makes the conflict visible. Pre-registering the names is not an
option, because module paths are settled by the workstream that
introduces them and `NameSet` accepts a name for a nonexistent module
silently — a wrong guess would leave a dead entry and an
unallowlisted module, surfacing as a `lake lint` failure with no
pointer to the cause. Leaving a conflict unresolved is what
`regenerate-integration.yml` reports as an `integration-regen-fail`
issue.

## Lifespan and branch placement

W0 through W5 are ordinary topic branches off `main`, merged as they
complete. `scripts/lib/topic-revset.sh` collects each topic-branch
prefix's bookmarks not already on `main`
(`TOPIC_TIPS_NOT_ON_MAIN_REVSET`, a seven-way union including
`bookmarks(glob:"feat/*") ~ ::main`), and
`regenerate-integration.yml` dispatches CI on `integration` after
every push to `main`, so the combined view of in-flight work already
exists and requires no new machinery, per `CONTRIBUTING.md` § Code is
cost. Sibling branches also keep W1 and W2 independent in the DAG, as
they do W3 and W4.

This document and the `TODO.md` entry are added on one branch, which
merges to `main` before any of W0 through W5 begins. That branch
carries no plan of its own: its implementation is the transcription
§ Content destined for `TODO.md` itemises, together with the two
`docs/references.bib` entries, so the planning phase that
`CONTRIBUTING.md` § Each phase produces an artifact requires would
restate the itemisation and nothing else. This document is
removed in that branch's final commits, so it never reaches
`main`'s working tree,
satisfying `docs/process.md` § Specs and plans are transient without
amendment. Placing the `TODO.md` entry ahead of every workstream is
what makes "no workstream reads another's branch" true: W2 is
independent of W1 and may begin first, and would otherwise find
neither this document nor the entry on `main`. A workstream begins
once the workstreams it depends on are merged.

An umbrella branch carrying this document across W1 through W5 was
considered and rejected. No pull-request CI would run on W1 through
W4 under it:
`ci.yml`, `markdown-lint.yml` and `doc-build.yml` are all
`pull_request: branches: [main]`, so a pull request into an umbrella
branch matches none of them and only `conflict-check.yml`, whose
`pull_request` trigger is unfiltered, fires. Admitting it would mean
editing three workflow files and reverting them at the end, and W1
through W4 would reach `main` in a single merge rather than as they
complete.

## Content destined for `TODO.md`

The branch that carries this document adds a `TODO.md` § FinSetSkel
as an elementary topos entry under "Next up"; W5's branch removes it,
its content having moved to `docs/index.md` as `TODO.md`'s header
prescribes. It carries a status table, which § Polynomial functors
does not have — that entry tracks status by removal alone, which does
not distinguish six interdependent workstreams. Otherwise it is
structured like § Polynomial functors, and carries:

- The motivation of § Motivation in two sentences.
- The six workstreams with their dependency order and each one's
  deliverable list, W0 carrying no spec and no plan
  (§ Process per workstream), and the statement that each of W1
  through W5's spec and plan
  are written only after the items it depends on are merged. Each of
  W1 through W5's list includes its `docs/index.md` entry, per
  `CONTRIBUTING.md` § Each phase produces an artifact; W0 has none,
  adding no Lean content.
- The two names of § Names fixed here, with the rationale for the
  `Elementary` qualifier, and the placement of W1 through W5's
  modules under `Geb/Mathlib/` with test parallels under
  `GebTests/Mathlib/`.
- The morphism representation: root-namespace `Vector`, not
  `List.Vector`, for constant-time indexing, accepting `propext` and
  `Quot.sound`. This fixes W1's morphism type and every downstream
  carrier, so it is stated where W1 reads it.
- W2's obligation to verify, against the primary source and before
  citing the work in Lean, the [Pare1974] attribution, the
  proof-route characterisation, and the reported Mikkelsen priority,
  per `AGENTS.md` § Verify agent claims.
- The operation table of § Workstreams, including the `Prop` markers
  on rows e, f, j and k.
- The field table of § Constructive layering, and the
  constructive-layering decision in brief with its rationale,
  including the derived-instance alternative for the two `Prop`
  fields and its consequence for rows e, f, j and k.
- All eight interface constraints of § Why the workstreams compose
  item 4, and the `simp` discipline that follows them.
- Both obligations of § Standing repository obligations, including
  that W0 precedes W1, and the conflict-resolution rule for
  concurrent siblings.
- The name and pull-request number of the branch adding the entry,
  so that § Findings, the per-deliverable route and scope rules, and
  this document's rationale can be recovered from history for
  re-verification. The number is filled in after the pull request is
  opened and before user review, the branch name being the only one
  of the two available when the entry is first written.
- The status of each workstream and the module paths of completed
  ones.

The entry moves from "Next up" to "In progress" when the first
workstream begins, as `TODO.md`'s own section split prescribes; the
status table carries per-workstream state within it.

Everything else in this document is transient.

## Process per workstream

Each of W1 through W5 follows the repository's standard cycle on its
own branch off `main`, begun only after the workstreams it depends on
are merged:

1. Brainstorming spec, then adversarial review to convergence
   (`docs/process.md` § Adversarial review), then user review.
2. Implementation plan, then adversarial review to convergence, then
   user review.
3. Subagent-driven development.
4. Pre-push verification, user line-by-line review, PR to `main`.
5. Removal of that workstream's own spec and plan in the branch's
   final commits, and update of the `TODO.md` status.

W0 carries no spec and no plan. Its whole content is the allow-list
transcription of § W0 — the `Batteries.` allow-list, so the phases
`CONTRIBUTING.md` § Each phase produces an artifact requires would
restate that and nothing else, the same reasoning § Lifespan and
branch placement applies to the branch carrying this document. W0 is
step 4 alone: pre-push verification, user line-by-line review, PR to
`main`.

Each of W1 through W5 re-verifies the findings of § Findings that it
consumes, at the mathlib revision current when it is taken up,
reading them from the branch recorded in the `TODO.md` entry.

Deferring each workstream's spec until its dependencies are merged
follows `TODO.md` § Polynomial functors: interface corrections made
while implementing an earlier workstream would otherwise invalidate a
later workstream's plan.

## References

- [MacLaneMoerdijk1992] and [Pare1974] in `docs/references.bib` — the
  definition transcribed and the colimits result.
- `Mathlib/CategoryTheory/FintypeCat.lean` — `FintypeCat.Skeleton`,
  `is_skeletal`, `isSkeleton`.
- `Mathlib/CategoryTheory/Category/Cat.lean` — `Cat.ext`,
  `Cat.equivOfIso`.
- `Mathlib/CategoryTheory/Subobject/Classifier/Defs.lean` —
  `Subobject.Classifier`, `isTerminalΩ₀`, `mkOfTerminalΩ₀`,
  `HasSubobjectClassifier`.
- `Mathlib/CategoryTheory/Monoidal/Cartesian/Basic.lean` —
  `CartesianMonoidalCategory`, `ofChosenFiniteProducts`.
- `Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean` —
  `MonoidalClosed`, `Closed`, `ihom`.
- `Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`
  and `.../FiniteProductsOfBinaryProducts.lean` — the four
  derivations, the `build*` cores, and the `extend*` folds.
- `Mathlib/CategoryTheory/Limits/Shapes/FiniteLimits.lean`,
  `Mathlib/CategoryTheory/FinCategory/Basic.lean` — the finite
  (co)limit classes and what `FinCategory` does and does not carry.
- `Mathlib/Algebra/BigOperators/Fin.lean`,
  `Mathlib/Logic/Equiv/Fin/Basic.lean`,
  `Mathlib/Data/Fintype/EquivFin.lean` — the index equivalences and
  the computable `Trunc`-valued linearisation.
- `Batteries/Data/UnionFind/Basic.lean`, `.../Lemmas.lean` —
  `UnionFind`, `Equiv`, `equiv_empty`, `equiv_push`, `equiv_union`.
- `Mathlib/Data/Vector/Defs.lean`, `Mathlib/Data/Vector/Basic.lean` —
  the representation guidance and `Equiv.vectorEquivFin`.
