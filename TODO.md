# TODO

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Next up](#next-up)
  - [Presheaf parametric-right-adjoint IR codes](#presheaf-parametric-right-adjoint-ir-codes)
  - [Named examples for axiom auditing](#named-examples-for-axiom-auditing)
  - [Citation corrections deferred to their own branch](#citation-corrections-deferred-to-their-own-branch)
  - [Polynomial functors](#polynomial-functors)
    - [1. Categorical wrappers for slice and presheaf W-types as initial algebras](#1-categorical-wrappers-for-slice-and-presheaf-w-types-as-initial-algebras)
    - [2. M-types and their categorical wrappers as terminal coalgebras](#2-m-types-and-their-categorical-wrappers-as-terminal-coalgebras)
    - [3. Universal morphisms](#3-universal-morphisms)
    - [4. Relative (co)free (co)monads](#4-relative-cofree-comonads)
    - [5. Composition and identity of polynomial functors](#5-composition-and-identity-of-polynomial-functors)
  - [Complexity of the decidable validity checkers](#complexity-of-the-decidable-validity-checkers)
  - [Upstream placement of categorical wrappers](#upstream-placement-of-categorical-wrappers)
  - [`FinSetSkel` under `namespace CategoryTheory`](#finsetskel-under-namespace-categorytheory)
  - [Upstream destination of core- and Batteries-targeted content](#upstream-destination-of-core--and-batteries-targeted-content)
  - [Complete Theorem 2.4 for `IndRec`](#complete-theorem-24-for-indrec)
  - [Theorems 2 and 4 for `IR` codes](#theorems-2-and-4-for-ir-codes)
  - [Validate `PresheafPFunctor.functor` as a parametric right adjoint](#validate-presheafpfunctorfunctor-as-a-parametric-right-adjoint)
  - [Exhaustive verification of presheaf PRA laws for finite instances](#exhaustive-verification-of-presheaf-pra-laws-for-finite-instances)
  - [PRA functors over finite-specification base categories](#pra-functors-over-finite-specification-base-categories)
  - [Finite categories as a full subcategory of `Cat`](#finite-categories-as-a-full-subcategory-of-cat)
  - [Bellantoni-Cook](#bellantoni-cook)
  - [Binary trees and their preorder encoding](#binary-trees-and-their-preorder-encoding)
  - [The Bellantoni-Cook tree recognizer](#the-bellantoni-cook-tree-recognizer)
  - [The fold over recognized terms](#the-fold-over-recognized-terms)
  - [Deferred items from the tree recognizers](#deferred-items-from-the-tree-recognizers)
  - [A sharper space bound for the tree scanner](#a-sharper-space-bound-for-the-tree-scanner)
  - [Choice-free patch to Cslib's multi-tape Turing machine API](#choice-free-patch-to-cslibs-multi-tape-turing-machine-api)
  - [Vale configuration](#vale-configuration)
  - [The namespace prefix in a declaration body](#the-namespace-prefix-in-a-declaration-body)
  - [Placement of the choice-free `Nat` residue lemmas](#placement-of-the-choice-free-nat-residue-lemmas)
  - [Concrete-syntax prototype](#concrete-syntax-prototype)
  - [Prose-conformance pass over the concrete-syntax survey](#prose-conformance-pass-over-the-concrete-syntax-survey)
  - [Lambda arrow in `GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean`](#lambda-arrow-in-gebtestsmathlibcategorytheoryelementarytoposlean)
  - [Spec and plan lifecycle beyond one topic branch](#spec-and-plan-lifecycle-beyond-one-topic-branch)
- [Triggers (do when condition fires)](#triggers-do-when-condition-fires)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Active workstreams, in topological order. Workstreams complete → removed;
content merged into the persistent documentation.

## Next up

### Presheaf parametric-right-adjoint IR codes

Morphisms of presheaf p.r.a. functors, and a code system denoting them: a leaf
rule injecting a presheaf p.r.a. functor as it stands, and a `delta` rule
carrying the induction-recursion. The prototype under
`Geb/Internal/PresheafIRProto/` is the design's validated part; four upstream
branches remain:

- W-a: morphisms of presheaf p.r.a. functors, their action and the hom-set
  bijection; their composition and category structure; and the bundled
  restatements and natural-transformation identification, in a
  `Classical`-allowed module. Upstream-eligible.
- W-b: the semantic operations, the decoding layer, the code type, the
  interpretation and the leaf's section, upstream-eligible.
- W-d: code-level morphisms and their representation theorem.
- W-e: the collapse `PSh(𝕀)/D ≃ PSh(el(D))`.

W-a, W-b and W-e depend on nothing; W-d depends on W-a and W-b. W-c, which
would have carried a bound on what a restricted leaf reaches, is withdrawn:
the leaf admits every presheaf p.r.a. functor, so there is no generated
fragment for such a bound to be about. Its letter is not reused.

Completeness needs no branch: the code type's leaf rule injects a presheaf
p.r.a. functor as it stands, so every such functor has a code definitionally.
The prototype states this as `praCodeOf`, naming the leaf as a section of the
interpretation, with `leftInverse_interp_praCodeOf` and `surjective_interp`
stating that `interp` retracts onto it.

### Named examples for axiom auditing

- **Anonymous `example`s escape the axiom linter.**
  `GebMeta.detectNonstandardAxiom` runs over declaration names, so an anonymous
  `example` is never audited: it may depend on `Classical.choice`, or on any
  forbidden axiom, in a module held to the strict permitted set, and `lake
  lint` still passes. This was found by observation — two `example`s naming a
  functor-category `⟶`, whose `Category` instance is
  `Classical.choice`-dependent, sat in a module advertised as choice-free with
  the linter green. A third instance was found the same way: an `example`
  applying `yoneda`, whose target is a functor category, sat in the choice-free
  prototype core; naming it showed the `Classical.choice` dependency and it
  moved to the allowlisted module.
- Give every `example` a name, so that the axiom linter covers it. Those in
  `Geb/` are all named; those in `GebTests/` remain.
- Record the rule in [docs/rules/lean-coding.md](docs/rules/lean-coding.md),
  alongside the other axiom-hygiene material in § Constructive-only Lean code,
  stating the reason rather than only the rule.
- Consider whether the linter itself should flag anonymous `example`s in
  audited modules, which would enforce this rather than relying on convention.

### Citation corrections deferred to their own branch

Each is a defect in committed content, unrelated to the concern of the branch
that found it, so each is deferred per [CONTRIBUTING.md](CONTRIBUTING.md) §
Concern shape.

- **`IndRec/Basic.lean` attributes the Mahlo-cardinal model to the wrong
  paper.** Its module docstring says "the set-theoretic model of
  [DybjerSetzer2003] justifies their existence using a Mahlo cardinal". The
  model is [DybjerSetzer1999]'s; [GhaniNordvallForsbergMalatesta2015] § 7 says
  so explicitly ("We briefly revisit the initial algebra argument used by
  Dybjer and Setzer [DS99]"), and DybjerSetzer2003's own introduction
  attributes the model to its predecessor. Change the key.
- **`docs/references.bib` has the author order of
  `GhaniNordvallForsbergMalatesta2015` wrong.** The published LMCS byline is
  Ghani, Malatesta, Nordvall Forsberg; the entry and the citation key both
  encode the order arXiv's listing and the LMCS landing page give in metadata,
  which differs from the byline of either PDF: the preprint's typeset byline is
  the published one. A reviewer who checks the DOI record alone will find the
  current entry matches it, so the correction cites the article itself. Five
  persistent consumers name the key —
  `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`,
  `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`, `IndRec/Functor.lean`,
  `IndRec/Universes.lean` and `docs/references.bib` — and `docs/index.md`
  spells the wrong order out in prose at three further places without using
  the key, so a key-only search under-scopes the branch.
  `docs/references.bib`'s own note also names the work in the wrong order.
- **`docs/references.bib`'s note on
  `HancockMcBrideGhaniMalatestaAltenkirch2013` is unverified and incomplete.**
  It claims the extended preprint "renumbers two of" the results this
  repository cites. Checked against the preprint, that is false. The preprint
  numbers Definitions, Examples, Lemmas, Theorems and Corollaries in one shared
  sequence where the proceedings number each kind separately, so Definitions 1
  to 4 are unaffected, being the first four numbered items in both, and
  everything from the proceedings' Example 1 onward shifts. The proceedings'
  Lemma 1, Definition 6, Definition 7, Theorem 1, Theorem 2, Theorem 3, Theorem
  4, Definition 8 and Corollary 2 are the preprint's Lemma 7, Definition 10,
  Definition 11, Theorem 12, Theorem 15, Theorem 18, Theorem 21, Definition 17
  and Corollary 19. Across everything this repository cites, add also: the
  proceedings' Definition 2, Definition 3, Definition 5, Example 1, Lemma 2,
  Lemma 3, Lemma 4 and Corollary 4 are the preprint's Definition 2, Definition
  3, Definition 8, Example 5, Lemma 9, Lemma 14, Lemma 16 and Corollary
  22. Example 1 is cited by `Geb/Mathlib/Data/PFunctor/IndRec/Container.lean`,
      its test module and `docs/index.md:402`, none of which the presheaf
      p.r.a. workstream touches, so that citation's correction is independent
      of its branches. Record the collision explicitly: the preprint's
      Definition 8 is the proceedings' Definition 5, while the proceedings'
      Definition 8 is the preprint's Definition 17, so a citation that does not
      say which numbering it uses sends a reader to the wrong statement — and
      Definition 5, Lemma 3 and Lemma 4 are, of the results the present note
      does not cover, the repository's most-cited. Section numbering is
      unchanged. Note too that the preprint carries a different title and
      author order, so the key names the proceedings version alone. This
      correction must land before any branch of the presheaf p.r.a. workstream
      that cites an uncovered result: W-a for Definitions 6 and 7 and Theorem
      1. Lemma 1 is due already rather than at a branch: it is cited in
      persistent content at three sites in
      `Geb/Mathlib/Data/PFunctor/IndRec/Slice.lean` and once in its test
      mirror, uncovered by the existing note. Theorem 3, which W-d cites, the
      existing note already covers.

### Polynomial functors

The polynomial-functor roadmap below is a partial order of separate
planning–implementation cycles. Items with disjoint file sets that do not
depend on one another may be taken in either order. Each item's full spec and
plan are written only after the items it depends on are implemented: the
project is too large to fix every earlier interface on the first attempt, so
interface corrections in an earlier item can invalidate a later item's plan.
Each item lives on its own topic branch and migrates to persistent
documentation under `docs/index.md` on completion.

The current stack, each layer expressed as restrictions or assignments on the
layer below: mathlib `PFunctor` (`Type` endofunctors) → slice polynomial
functors (`Geb/Mathlib/Data/PFunctor/Slice/`) → presheaf
parametric-right-adjoint functors (`Geb/Mathlib/Data/PFunctor/Presheaf/`).
Categorical interpretations into mathlib's category theory are kept thin to
minimise the `Classical.choice` surface. Slice and presheaf W-types
(`Slice/W.lean`, `Presheaf/W.lean`) exist, with the existence half of
initiality only; the roadmap extends the stack upward.

#### 1. Categorical wrappers for slice and presheaf W-types as initial algebras

Characterise the slice and presheaf W-types as the initial objects of the
categories of algebras of their functors, reusing the `PFunctor` and `WType`
wrappers described under `Geb/Mathlib/Data/PFunctor/Univariate/` in
`docs/index.md`. Build the presheaf initiality proof on the slice initiality
proof, and the slice proof on the `WType` initiality established there.

#### 2. M-types and their categorical wrappers as terminal coalgebras

Define the M-types (greatest fixed points) of the slice and presheaf functors
on mathlib's `PFunctor.M`, following mathlib's standard construction of M-types
on W-types, and characterise them as the terminal coalgebras of their functors.
Following the base-layer-first pattern of the `PFunctor` wrappers and item 1,
build a categorical wrapper for the terminality of mathlib's `PFunctor.M`
first, reusable in the slice and presheaf terminality proofs.

#### 3. Universal morphisms

Establish the universal morphisms of the slice and presheaf functors, layering
the slice constructions on mathlib's `PFunctor` and the presheaf constructions
on the slice constructions. Per the survey, mathlib carries little or none of
this for `PFunctor`, so a base layer for mathlib's `PFunctor` is likely
required. Model formulas for a different representation, to be adapted, are in
[rokopt/geb
`PolyUMorph.lean`](https://github.com/rokopt/geb/blob/main/geb-lean/GebLean/PolyUMorph.lean).

Implement in this order, each step layered across the three forms:

1. Representables (every representable is polynomial).
2. Small coproducts (indexed by any `Type u`): every polynomial is then a
   coproduct of representables; the first part of general colimits; includes
   the initial object (the coproduct over `Empty`).
3. Day convolution: the first part of general limits.
4. Commutativity of coproducts with Day convolution.
5. Small products, as an instantiation of Day convolution.
6. Small parallel products, as an instantiation of Day convolution.
7. Exponential objects.
8. Left Kan extension.
9. Equalizers.
10. All small limits, by instantiating mathlib's construction of limits from
    products and equalizers.
11. Coequalizers.
12. All small colimits, by instantiating mathlib's construction of colimits
    from coproducts and coequalizers.

Following the general definitions, implement the decidable-case specializations
of those universal morphisms with interesting decidable forms, building on the
`PFunctor.Finitary` layer documented in `docs/index.md`.

#### 4. Relative (co)free (co)monads

Build the relative free monads and relative cofree comonads of the slice and
presheaf functors for all three forms, and prove the relative universal
property. A slice or presheaf functor is an endofunctor only when its domain
and codomain bases coincide, so the relative notion
[AltenkirchChapmanUustalu2015] is the appropriate one for the general
(non-endofunctor) case; the ordinary free monad and cofree comonad are the `J =
id` special case. The formal theory is [ArkorMcDermott2024]. Model definitions:
cslib's `PFunctor` free monad (`Cslib/Foundations/Data/PFunctor/Free.lean`, the
ordinary case) and [rokopt/geb
`RelativeMonad.lean`](https://github.com/rokopt/geb/blob/main/geb-lean/GebLean/Binding/RelativeMonad.lean)
(the relative case, in extension form). The first intended application is
generic syntaxes with binding [AllaisAtkeyChapmanMcBrideMcKinna2021], which
also supplies test material for the relative monads.

Open technical question, resolved when this item is taken up, that determines
implementation order: whether the relative (co)free (co)monad can be built on
top of the ordinary one — as the slice functors are built on `PFunctor` and the
presheaf functors on the slice functors. The primary constraint is to avoid
code duplication; within that, build the simpler pieces first and the more
complex on top of them when that can be done without duplication. If the
relative version can be built on the ordinary one, do so (simpler-first with
reuse); otherwise build the relative version and define the ordinary one as its
`J = id` specialization — known achievable, the ordinary case being the
discrete degeneration. Relate each construction to the corresponding
slice/presheaf W-type (item 1) or M-type (item 2) and show the definitions
equivalent, as in the superseded free-monad and cofree-comonad items.

#### 5. Composition and identity of polynomial functors

Establish that the interpretation of mathlib's `PFunctor` carries
`PFunctor.comp` to composition of the corresponding functors, and supply the
identity polynomial functor together with the isomorphism identifying its
interpretation with the identity functor. mathlib defines `comp`, `comp.mk`,
and `comp.get` and states no lemma about them, so the mutual-inverse laws
`comp.get_mk` and `comp.mk_get` are part of the item.

This is the 1-cell composition of `Cat`, a 2-categorical operation, not a
universal morphism. It is independent of the items above and may be taken in
any order relative to them. Two design points are settled: the identity
polynomial functor is `protected def PFunctor.id`, since an unprotected `id`
shadows `_root_.id` throughout the `PFunctor` namespace and breaks uses such as
`P.map id`; and both isomorphisms admit an ambient universe beyond the
parameters of the functors involved.

### Complexity of the decidable validity checkers

Prove the complexity bounds conjectured, but not proved, for the checkers in
`Geb/Mathlib/Data/PFunctor/Slice/Decidable.lean` and
`Geb/Mathlib/Data/PFunctor/Presheaf/Decidable.lean` (see `docs/index.md`). With
`n` the number of nodes of the input term, `h` its height, `k` the branching
bound, `κ` the number of objects of `I`, and `H` the maximal hom-set size, and
taking equality in `I`, in `dom`, and in the presheaf's value types to cost
`O(1)`: the four single-step checks are constant-time in `n`, with node-level
factors `1` for the two fiber predicates, `k` for `Compatible`, and `κ²Hk` for
`IsNatural`; `WValid` runs in `O(k · n)`, a single fold with an `O(1)`
accumulator; and `IsHereditarilyNatural` runs in `O(κ²Hk · n · h)`, worst case
`O(n²)`, because each node's local condition is an equation between a subtree
and the root-restriction of a sibling, whose decision cost is linear in subtree
size. All six are polynomial time, and the functor's data enters as
multiplicative constants rather than as a change of complexity class. Upper
bounds only: a `Bool` fold short-circuits, so no matching lower bound is
claimed on rejecting inputs.

A sharing or hash-consing representation would reduce `IsHereditarilyNatural`'s
checker to linear time, each subtree comparison becoming a pointer comparison;
building that representation is out of scope for this item.

[Leivant1999], [DalLagoMartiniZorzi2010], and [AvanziniDalLago2018] place the
checkers' complexity: every recursion here is a non-dependent fold at a
first-order carrier, the regime those results place in first-order polynomial
time, as against the higher-order and word-algebra regimes in which they
identify an elementary or exponential jump.

`FinCat.assocCheck` (`Geb/Mathlib/CategoryTheory/FinCat/Basic.lean`) is in
scope for the same treatment. It enumerates `Θ(objCount⁴) + O(M³)` tuples,
where `M` is the total non-identity morphism count: four object quantifiers
stand outside the three morphism quantifiers, so a discrete category on `n`
objects costs `n⁴` iterations even at `M = 0`. Reserving an index for each
identity keeps the identity cases out of the quantifier entirely, the identity
laws holding by construction, so the morphism factor is the non-identity count
rather than the total. As above this is an upper bound only, the `Bool`
conjunction short-circuiting on rejection.

### Upstream placement of categorical wrappers

Settle where the categorical wrappers under `Geb/Mathlib/Data/` belong
upstream. No file under mathlib's `Mathlib/Data/` imports
`Mathlib.CategoryTheory.*`; mathlib packages category-theoretic material under
`Mathlib/Algebra/Category/` and `Mathlib/CategoryTheory/`. In scope is every
file under `Geb/Mathlib/Data/` that directly imports `Mathlib.CategoryTheory.*`
or `Geb.Mathlib.CategoryTheory.*`, the latter because it extracts to the
former: currently `PFunctor/Slice/Functor.lean`,
`PFunctor/Presheaf/Basic.lean`, `PFunctor/Presheaf/Functor.lean`,
`PFunctor/Univariate/Functor.lean`, `PFunctor/Univariate/W.lean`,
`PFunctor/Univariate/Initial.lean`, `PFunctor/IndRec/Basic.lean`, and
`PFunctor/IndRec/Naturality.lean`. Files importing those transitively —
`PFunctor/Presheaf/W.lean`, the rest of the `IndRec` family — follow whatever
placement is settled for them. Scoping the item by that criterion rather than
by a module list keeps it from being settled incompletely.

### `FinSetSkel` under `namespace CategoryTheory`

Move `FinSetSkel` and the modules under
`Geb/Mathlib/CategoryTheory/FinSetSkel/`, together with their
`GebTests/Mathlib/CategoryTheory/FinSetSkel/` parallels, from the root
namespace into `namespace CategoryTheory`, as mathlib places essentially all of
`Mathlib/CategoryTheory/`. A root-namespace `FinSetSkel` draws the
upstream-eligibility objection that moved `CategoryTheory.FinCat`; it is a
separate concern and so a separate branch.

### Upstream destination of core- and Batteries-targeted content

Settle where content under `Geb/Mathlib/` whose upstream target is Lean core or
Batteries rather than mathlib4 belongs. Such content exists because
`docs/rules/upstream-eligible.md` § Subtree import rules restricts
`Geb/Mathlib/` modules to `Mathlib.*`, `Batteries.*` and `Geb.Mathlib.*`
imports: a dependency of a `Geb/Mathlib/` module cannot live in
`Geb/Internal/`, so a module restating core or Batteries API sits under
`Geb/Mathlib/` while its upstream is neither mathlib4 nor CSLib. In scope is
every module under `Geb/Mathlib/`, and every `GebTests/Mathlib/` parallel,
whose declarations restate or replace declarations of Lean core or Batteries
rather than of mathlib: currently `Geb/Mathlib/Data/Vector/OfFn.lean` and
`Geb/Mathlib/Data/UnionFind/OfEdges.lean`, and their test parallels. The
criterion does not literally reach `OfEdges.lean`, whose declarations extend a
Batteries type with new statements rather than restating or replacing existing
ones; it is listed here because this item's subject — content under
`Geb/Mathlib/` whose upstream target is not mathlib4 — is where such a module
belongs. Reconciling the criterion's wording with that subject is a separate
concern, on its own branch. Scoping the item by that criterion rather than by a
module list keeps it from being settled incompletely; the criterion does not
reach `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`, whose statement is an
`Equiv` and so has no core or Batteries home.

`scripts/extract-pr.sh` is the enforcer: its `Geb/Mathlib/*` arm maps
unconditionally to `Mathlib/` and its `GebTests/Mathlib/*` arm to
`MathlibTest/`, so a core-targeted module extracts to the wrong upstream
silently. Changing either mapping waits on this item's outcome.

### Complete Theorem 2.4 for `IndRec`

Layered like the polynomial-functor code (constructive core first, thin
`Classical.choice`-enabled categorical wrapper second). The two remaining
layers for Theorem 2.4 of [GhaniNordvallForsbergMalatesta2015] follow.

In the existing constructive files, without `Classical.choice`, remaining: the
uniqueness properties of `IR.elim` and `IR.rec` as algebra morphisms,
constructively stated (the Theorem 3 development does not need this item).

In a separate sibling file wrapping the constructive proofs in mathlib
`Category`/`Functor` interfaces (pretty much everything involving mathlib's
`Category` pulls in `Classical.choice`, so the wrapper is kept thin, following
`Slice/Functor.lean` and `Presheaf/Functor.lean`):

1. `FreeCoprodCompDisc` as a `Category` and the interpretation of a code as a
   `Functor`.
2. The initiality of `IR` in the category of algebras (mathlib's
   `CategoryTheory.Endofunctor.Algebra`), wrapping the constructive uniqueness
   proofs.

### Theorems 2 and 4 for `IR` codes

Parallel to "Complete Theorem 2.4 for `IndRec`", and building on the category
of `IR` codes in `Geb/Mathlib/Data/PFunctor/IndRec/Category.lean` (see
`docs/index.md`). Two results of [HancockMcBrideGhaniMalatestaAltenkirch2013]
remain: Theorem 2, the left-Kan-extension characterization of the `δ`-code
interpretation, and Theorem 4, the equivalence with dependent polynomial
functors.

### Validate `PresheafPFunctor.functor` as a parametric right adjoint

Establish the natural isomorphism confirming that `PresheafPFunctor.functor` is
the parametric right adjoint determined by its generic data `(T1, E_T)`.

### Exhaustive verification of presheaf PRA laws for finite instances

The `FinitePresheafPFunctor` structure bundles `FinEnum J` alongside the domain
finiteness. With both index categories finite, the functor laws
(`ShapeRestrId`, `ShapeRestrComp`, `ReindexNaturality`, `ReindexId`,
`ReindexComp`, and the domain-side `DirectionRestrId`, `DirectionRestrComp`)
are exhaustively verifiable by enumeration: each law quantifies over finitely
many objects, morphisms, shapes, and directions, and the equalities are
decidable (shapes and directions have `DecidableEq` from the bundled `FinEnum`
evidence). A `decide`- based test harness can confirm that a concrete
`FinitePresheafPFunctor` satisfies all laws without manual proof, turning the
law fields from trusted input into checked input. The laws quantifying over
`J`-morphisms additionally need finite `J`-hom-sets, which the structure does
not currently bundle: a `finEnumHomJ` field is added by the commit that first
consumes it. This is a testing/verification concern (not a new decidability
instance) and is distinct from the decidability of fiber membership already
implemented.

### PRA functors over finite-specification base categories

Instantiate the presheaf parametric-right-adjoint functors of
`Geb/Mathlib/Data/PFunctor/Presheaf/` at base categories presented by `FinCat`
specifications (`Geb/Mathlib/CategoryTheory/FinCat/`), derive decidable
equality on their W-types from the specification's own, and specify the natural
transformations among the resulting functors.

This is the consumer that justifies the functor, 2-cell, `Bicategory` and
`DecidableEq`/`Repr` layers of the `FinCat` workstream under CONTRIBUTING §
Code is cost. Without it those layers have no in-tree consumer: the comparison
with `Cat` below is the only other one and is itself deferred.

It also supplies what § Exhaustive verification of presheaf PRA laws for finite
instances records as missing. That entry notes that the laws quantifying over
`J`-morphisms need finite `J`-hom-sets, which `FinitePresheafPFunctor` does not
bundle, and anticipates a `finEnumHomJ` field. A `FinCat` specification carries
finite hom-sets with decidable equality by construction, so the field may be
discharged from a specification rather than added.

One interface constraint carries over. `FinitePresheafPFunctor` bundles
`FinEnum J`, and the `FinCat` workstream establishes by measurement that
mathlib's only `FinEnum (Fin n)` instance, `FinEnum.fin`, depends on
`Classical.choice`, as does `ULift.instFinEnum` over it. Supplying that field
from a `FinCat` specification choice-free therefore needs a `FinEnum` built
directly as a cardinality with `Equiv.refl`, which competes with `FinEnum.fin`
at the same head symbol and so requires the explicit-supply mitigation
`Geb/Mathlib/Data/FinEnum.lean` documents. The `FinCat` workstream declines
that trade, having no need of `FinEnum`; this item does need it and should
price it.

Its dependency, the `FinCat` workstream, is implemented under
`Geb/Mathlib/CategoryTheory/FinCat/`.

### Finite categories as a full subcategory of `Cat`

Compare the `FinCat` specifications with the finite categories among mathlib's,
comprising:

- the object property on `Cat.{v, u}` selecting the categories with finitely
  many objects and finitely many morphisms in each hom-set, stated as a `Prop`
  in the shape of `CategoryTheory.CountableCategory`. mathlib has no such
  property: `Mathlib/CategoryTheory/Cat/` contains no `ObjectProperty` file,
  and `CategoryTheory.FinCategory` requires `SmallCategory` and so does not
  express it at independent universe levels;
- the 2-functor from `FinCat` to `Cat.{v, u}` extending `FinCat.Hom.toFunctor`;
- the proof that it is an equivalence onto that full subcategory.

Two observations from the `FinCat` workstream. Essential surjectivity chooses
`Obj ≃ Fin n` and a bijection on each hom-set, so it depends on
`Fintype.equivFin` and is classical; and because the chosen map on objects is a
bijection, the result is an isomorphism in `Cat` rather than only an
equivalence, as `Geb/Mathlib/CategoryTheory/FinSetSkel/Skeleton.lean` obtains
for its own comparison. The hom-set bijections must be chosen to carry each
identity to the index `FinCat` reserves for it, which is a constraint that
workstream's conventions impose on this one.

Deferred rather than scheduled: this item is the least predictable of the three
that the `FinCat` brainstorming identified, and it is the one most likely to
force revision of `FinCat`'s identity convention or hom encoding, so it is
taken after that workstream's interface has been exercised by the PRA item
above.

Its dependency, the `FinCat` workstream, is implemented under
`Geb/Mathlib/CategoryTheory/FinCat/`.

### Bellantoni-Cook

Three items, in dependency order, each over its own destination file.

1. `MultiPoly`, the multivariate polynomial library of the reference
   development. Required by its `BC_to_Cobham.v:2`, by its
   `Cobham_to_BC.v:2`, and by Proposition 2, whose statement
   `polymax_bounding` (`BC.v:1128`) is over `poly_BC` (`:1075`), built from
   `pcst`, `pproj`, `pplus`, `pmult`, `pcomp`, `pshift` and `pplusl`.
   Returns the polynomial apparatus items 2 and 3 are stated over.
2. Proposition 2, the polymax bounding of `B`. Depends on 1. Returns the
   length bound the translation of item 3 requires.
3. The translations of Theorems 1 and 2 between `B`
   (`Geb/Mathlib/Computability/BellantoniCook/Basic.lean`) and Cobham's
   class `C`, the latter now implemented at
   `Geb/Mathlib/Computability/Cobham/Basic.lean`. Still depends on 1 and
   2: item 1's `MultiPoly` is required by both translation directions,
   and item 2 returns the length bound the `B → C` direction needs to
   build a `boundedRec` node's bound term explicitly — a dependence `C`'s
   own construction, needing neither, did not incur. The `C → B`
   direction additionally needs a `∗` case: `concat` has no counterpart
   in [HeraudNowak2011]'s grammar for `C`, which the reference
   development's `Cobham_to_BC.v` formalizes, so translating a `concat`
   node is work beyond it. Returns the characterization of the
   polynomial-time functions, and is the consumer that justifies the
   definitions already committed.

### Binary trees and their preorder encoding

Items over `Geb/Mathlib/Data/Tree/`.

1. Define `ConcreteSyntax.Ast` from `RankedAlphabet`, the labelled ranked
   alphabet documented in [docs/index.md](docs/index.md), removing the
   duplication between them. `Geb/Internal/ConcreteSyntax.lean` carries the
   initial algebra of `Fin k + X × X` with its own `leaf`, `fork`,
   induction principle `Ast.ind` and parse/print retraction, so the
   condition on this item is met; the import rules bar `Geb/Mathlib/` from
   reaching `Geb/Internal/`, so the dependency runs the other way.
2. Whether `RankedAlphabet.Term.size`
   (`Geb/Mathlib/Data/Tree/Ranked/Basic.lean`), which counts leaves alongside
   internal nodes, should be stated through a transfer to mathlib's
   `BinaryTree.numNodes`, and whether the name `size` survives beside
   `numNodes`, `numLeaves` and `height` —
   `Geb/Mathlib/Data/Tree/Ranked/Binary.lean` presents the two-symbol
   alphabet's terms as the unlabelled binary trees, in the same
   `Mathlib/Data/Tree/` file-path family `BinaryTree` occupies.
3. Relate `binRanked.spell` to `DyckWord.equivTree`, connecting this
   encoding to mathlib's Catalan-number apparatus. Wanted only if a
   counting result is ever needed.

### The Bellantoni-Cook tree recognizer

Items for the Bellantoni-Cook tree recognizer, each covering its own
destination.

1. The tree recursor — the analogue of `safeRec` on the encoded tree,
   whose step receives the two subtree spellings in normal position and
   the two recursive values in safe position. Its soundness is a new
   theorem, not a corollary: [HeraudNowak2011] Proposition 2 is proved by
   induction over the constructors of `B`, and a tree recursor is a
   further constructor. The expected argument is that the step inherits
   the maximum bound, giving
   `|f(node l r)| ≤ p(|l| + |r|) + max(|f l|, |f r|, |ā|)`, and induction
   on height gives a polynomial. Depends on this recognizer's scan for
   the split point.
2. Extract the unfolding and environment lemmas into their own module
   once a second Bellantoni-Cook function needs them.
3. The labelled variant, tracking `RankedAlphabet`, the labelled ranked
   alphabet documented in [docs/index.md](docs/index.md).
4. Verify the claim of [DalLagoMartiniZorzi2010] § 1 that polynomiality
   extends to constructors `s₁ × ⋯ × sₙ → s` under the constraint that
   `s` occurs at most once among the `sᵢ`. Nothing in the design depends
   on it.
5. A linear-logic strand. [Hofmann2000]'s abstract states soundness for
   recursion over trees in a system it describes as modally and linearly
   typed, and the light and soft linear logics tune one family of
   systems to several complexity classes. The motivation to record is
   that tunability. Against it: those systems are reported to need more
   elaborate syntax or encodings than the function algebras, and a
   well-typed term there does not carry its own bound — the type
   derivation is needed to extract it, which tells against the
   representation strategy used here, in which the program is the term.
   Any pursuit of this item begins by verifying both claims against
   primary sources.

### The fold over recognized terms

`Geb/Internal/Computability/CobhamFoldProto/` generalizes
`Cobham/RankedTree.lean`'s recognizer to a fold at an algebra of the ranked
alphabet, computing `RankedAlphabet.parse` followed by the algebra morphism out
of the term algebra. It carries two constructions over one semantic core: one at
a carrier with a fixed-width bit encoding, whose steps dispatch on a constant
window, and one at the carrier `List Bool` with the algebra's operations
supplied as expressions of the class. Each is tied to the shared semantic layer
separately — `foldOutSem_eq` and `foldOutSemV_eq` — and
`foldOut_algOfFixed` relates the folds their algebras denote there, up to
the encoding, at a carrier that stays within a fixed width. The output words
agree on an accepted word; on a rejected one they differ at `p > 0`, the
fixed-width construction emitting `false :: List.replicate p false` where the
bitstring construction emits `[false]`, and coincide at `p = 0`.
The agreement is therefore stated at the `Option` level. These items remain
before any of it is upstream-eligible.

- Neither construction is exercised on an input at the expression level. The
  samples evaluate the semantic fold, and the `decide` on `unitExpr` checks
  tree shape rather than value, so no expression's output word has been computed
  from an input word. `Geb.CobhamFold.foldOutSemV_algMk` characterises one
  expression's output word for every input word, at the algebra rebuilding its
  argument, but characterises it symbolically rather than computing it: the
  readout dispatches on `2 ^ readoutWidthV R` branches, so the characterisation
  is by proof rather than by normalization. What remains outstanding is an
  output word computed from an input word.
- The bitstring construction's smash-freeness is conditional on the algebra's:
  `smashFree_foldOutExprV` assumes each `algOf i` smash-free, the expressions
  being spliced into the tree unconstrained. Whether the linear-growth
  condition that `stackSize_le_of_growth` consumes itself forces the algebra
  into the subalgebra is unestablished, as is the converse of
  `smashFree_foldOutExprV`. That superlinear growth of the fold's values forces
  `smash`, `concat` giving only linear multiples of the input, is argued
  informally and formalized nowhere.
- The fixed-width construction does not scale in the carrier's width. Its
  dispatch tree has `2 ^ dispatchWidthF` branches and, `Cobham.casesRaw`
  recursing with three children per level, a normal form growing by about a
  factor of three per bit of dispatch width. The term itself elaborates at any
  width, `Cobham.casesOf` taking its branch family as a function; what the width
  ends is normalization, a `decide` about the term exceeding the default
  heartbeat budget from a dispatch width of eleven, so beyond a carrier of a few
  bits every statement must be symbolic. The bitstring construction has no such
  growth, its dispatch reading only the flag, the slot and the count; its cost
  is in time instead, each step walking the state.
- Three parameterizations the prototype introduces belong upstream, each in the
  merged module whose special case it generalizes: the bound child and the
  arity-two scan node `scan2Raw` into
  `Geb/Mathlib/Computability/Cobham/Scan.lean`, and the state decoder's window
  into `Geb/Mathlib/Computability/Cobham/RankedTree.lean`, whose
  `Cobham.decodeState` is `Geb.CobhamFold.decodeVAt` at the dispatch window and
  shares its body verbatim. `scanBRaw_boundRaw` identifies `Cobham.scanRaw` as the
  additive instance, so the substitution is definitionally transparent, but it
  touches merged modules and the consumers `Cobham/Tree.lean`,
  `Cobham/RankedTree.lean`, `Cobham/Fold.lean` and
  `GebTests/Mathlib/Computability/Cobham/Scan.lean`.
- A general-alphabet, general-carrier Turing machine for the linear-time bound.
  `Geb/Internal/Computability/TreeScanner/` decides `binRanked.validBool` in
  `2 * n + 3` steps with the pending count as the work head's position, writing
  no work cell outside the two it marks; a fold needs the stack's contents on
  the tape. A machine reading them costs `(2 + R.maxArity / R.width) * n` steps
  and `n / R.width` work cells, which at `binRanked` is worse than the existing
  machine, and a general-alphabet recognizer machine is a prerequisite. Nothing
  of this is formalized, beyond the work-cell count, which is
  `Geb.CobhamFold.width_mul_depth_scanFinal_le` applied to each suffix of the
  input. The machine sketch applies at a finite carrier only, its state count
  being `|α| ^ R.maxArity` and its work alphabet `|α|` and a constant; the
  bitstring construction's steps are not constant-time in any case.

### Deferred items from the tree recognizers

Deferred while the ranked-tree recognizers over `Geb/Mathlib/Data/Tree/`,
`Geb/Mathlib/Computability/Cobham/` and `Geb/Internal/` were built, each
independent of the others and none scheduled.

- The Bellantoni-Cook port of the scan combinator, whose signature is over
  arities in normal and safe position and so is a branch rather than a
  transcription; the paramorphism whose step receives a subterm's
  spelling, which the head-locality of the state layout admits only at
  quadratic cost; and the depth-first unary degree sequence encoding, whose
  condition for adoption is unbounded arity. The fold at an infinite carrier is
  built, at the carrier `List Bool`, by
  `Geb/Internal/Computability/CobhamFoldProto/Variable.lean`, and
  `smashFree_foldOutExprV` shows it smash-free when the algebra's own
  expressions are, the machinery contributing only `comp`, `proj`, `succ`,
  `zero`, `concat` and `boundedRec` nodes and the algebra's expressions being
  spliced in unconstrained. So an infinite carrier does not by itself force the
  generator.
- `Cobham/RankedTree.lean` and `Cobham/Fold.lean` say `DecidableEq (Fin n →
  Bool)` resolves through `Fintype.decidablePiFintype`. It resolves through
  `Geb/Mathlib/Data/FinEnum.lean`'s choice-free `FinEnum.decidablePiFinEnum` at
  mathlib's `FinEnum.fin`, which is where the `Classical.choice` dependence
  enters; the conclusion each module draws is unaffected. Correcting merged
  upstream-eligible modules is a branch of its own.
- `Cobham/Tree.lean`'s `isTree_smashFree` names the predicate `Cobham.SmashFree`
  subject-first, where mathlib's naming guide names a theorem by its conclusion
  read in order, giving the `smashFree_isTree` form that
  `Geb/Internal/Computability/CobhamFoldProto/` uses throughout. Renaming it
  touches a merged upstream-eligible module, so it is a branch of its own.
- `Cobham/Tree.lean`'s `oneAtOf` and `falseAtOf` duplicate `constAtOf`, and
  its `predPred` duplicates `predIter 2`. Substituting the general form is
  definitionally transparent — `oneAtRaw`, `falseAtRaw` and `predPredRaw`
  reduce to the corresponding `prependRaw`/`predIterRaw` applications by
  `rfl`, so `combSem_nil` and `isTreeSem_eq_eval` read through the
  substitution unchanged. Each is left in place because removing the
  duplication is a separate concern, not because the substitution is
  risky.
- Whether `Cobham/Tree.lean`'s `combSem`, a parameterless `def`, generates
  an equation lemma the way `RankedTree.lean`'s `rankedSem` does.
  `combSem_def`'s docstring states that a `def` carries no equation
  lemma, while `length_rankedSem_le` here rewrites by `rankedSem`'s
  generated one; whether the same holds of `combSem` is untried. Check
  whether `rw [combSem]` closes where `combSem_def` is used, and correct
  the docstring in `Cobham/Tree.lean` only if it does. A short branch of
  its own either way.
- Whether `Cobham/Tree.lean`'s recognizer `isTree` is redundant beside
  `Cobham/RankedTree.lean`'s `isRanked` at `binRanked`, now that
  `isRankedSem_binRanked_eq_singleton_iff_isTreeSem` identifies the
  languages the two accept. `isTree_smashFree` and the [Strahm2003]
  Theorem 1(2) corollary it supports are the residue that is not:
  `isRanked` at `binRanked` is not itself shown `SmashFree`, so the
  polynomial-time-and-linear-space membership `Cobham/Tree.lean` states
  has no counterpart in `Cobham/RankedTree.lean`. What that deferral lacks, a
  symbolic route in place of the kernel evaluation `decide` performs, is
  available in `Geb/Internal/Computability/CobhamFoldProto/SmashFree.lean` as
  `instFinEnumSigB`, `smashFreeBool_mk_iff` and the branch-family recursion
  `smashFreeBool_casesRaw`, though the subtree import rules keep
  `Cobham/RankedTree.lean` from citing them.
- A sweep-scale cross-check of `Cobham.isTreeSem` against
  `binRanked.validBool`, beyond length six. At length six and below it
  follows from `GebTests/Mathlib/Computability/Cobham/RankedTree.lean`'s
  `isRankedSem_eq_validBool_binRanked` together with the bridge theorem
  `isRankedSem_binRanked_eq_singleton_iff_isTreeSem`, so the deferral is
  worth taking only above that budget. A lighter computation was measured
  reaching the 200000-heartbeat `isDefEq` limit at 511 words, so a sweep
  above length seven may not elaborate at all.
- Aligning `Geb/Mathlib/Computability/BellantoniCook/Tree.lean`'s
  `isTreeSem_eq_singleton_iff_valid` and `isTreeSem_eq_ite`, which each
  carry the same `ok`/`depth` case analysis rather than sharing it, with
  `Geb/Mathlib/Computability/Cobham/Tree.lean`, which states the `ite`
  form first and derives the `iff` from it in a few lines. A short branch
  of its own.

`BarringtonCorbett1989` is deliberately absent from `docs/references.bib`:
neither its bibliographic detail nor the DLOGTIME-uniform TC⁰ claim
attributed to it has been verified against the article. The branch that
first needs it verifies it against the primary source before recording the
key, per [AGENTS.md](AGENTS.md) § Verify agent claims. The same holds for
the succinct tree-encoding references
`BenoitDemaineMunroRamanRamanRao2005`, `Mehlhorn1980` and
`BraunmuhlVerbeek1983` — verified but unused, and so added by the branch that
first cites them.

### A sharper space bound for the tree scanner

`Geb/Internal/Computability/TreeScanner/Bound.lean`'s
`computableInTimeAndSpace_validBool` gives a space bound affine in the step
count. A sharper bound, `spaceUsed ≤ n + 2`, follows from
`RankedAlphabet.Binary.depth_le_length` and a computation of
`Turing.MultiTapeTM.visitedByTapeHead` as a `Finset` image, since the count
never exceeds the word length and the plant step's excursion to cell `1`
adds nothing above that except at `n = 0`.

Pursuing it raises whether `treeScanner`'s marks representation — the
pending count as the work head's position, as opposed to a run of marks
read off the tape — would then be preferable, since a sharper bound wanting
the count readable from the tape rather than from the head position would
need it.

### Choice-free patch to Cslib's multi-tape Turing machine API

Cleaning the first root is one line in
`Turing.MultiTapeTM.Cfg.inputSymbol`'s index bound, verified to leave all of
Cslib building; cleaning the third is a reproof of
`Turing.MultiTapeTM.inputSymbolInner`, not yet attempted. Both together
would make the time-side API choice-free for downstream users; either alone
would not. It is a Cslib pull request rather than content of this
repository, so it belongs to neither upstream-eligible subtree and is
recorded here as its own item. Its pull request description is
user-authored, per [CONTRIBUTING.md](CONTRIBUTING.md) § Submission policy.

`Geb/Internal/Computability/TreeScanner/Steps.lean`'s `step_of_state`, a
step from a known state over an arbitrary machine, configuration and state,
is a second candidate for that pull request: Cslib states `step_of_halt`
beside it and no companion for a configuration that has not halted.

Neither patch reaches `Turing.MultiTapeTM.spaceUsed`'s `Finset.image` root,
through `Turing.MultiTapeTM.visitedByTapeHead`: mathlib's `Finset.image`
depends on `Classical.choice`, a dependence neither this repository nor
Cslib can remove without redefining the space measure. See § Triggers (do
when condition fires), below.

### Vale configuration

The tree carries a Vale configuration (`.vale.ini` and `styles/`) that
neither `scripts/pre-push.sh` nor any workflow runs. Its default package
set flags the spaced em-dash every committed document using one writes,
and the filename `TODO.md`. Adopting it, with those rules downgraded, or
removing it, is its own branch.

### The namespace prefix in a declaration body

[docs/rules/lean-coding.md](docs/rules/lean-coding.md) § Naming conventions
says "Do not include the namespace in the declaration body's identifiers; rely
on `namespace` to scope". `Geb/Mathlib/Data/Tree/Ranked/Basic.lean` writes
`Term.mk` inside `theorem Term.induction`. Upstream's own guide states the
rule for lemma names rather than declaration bodies, so what is diverged from
is a local strengthening. Settle whether the rule binds declaration bodies,
and either amend it or correct the site. Whether one remaining site still
warrants a branch of its own, rather than folding the correction into
whatever branch next touches the file, is open.

### Placement of the choice-free `Nat` residue lemmas

`RankedAlphabet.mod_two_mul` (`Geb/Mathlib/Data/Tree/Ranked/Code.lean`) and
`RankedAlphabet.add_one_mod` (`.../Ranked/Preorder.lean`) are facts about `ℕ`
with no ranked-alphabet content, stated there because mathlib's counterparts
depend on `Classical.choice` and `omega` cannot discharge a residue identity
whose modulus is a variable. Under `open RankedAlphabet` they present bare
beside `Nat`'s own residue API. The repository's pattern for a supplement to a
mathlib module is a module mirroring its path, as
`Geb/Mathlib/Data/Vector/OfFn.lean` and `Geb/Mathlib/Logic/Equiv/Basic.lean`
do, which would put them under `Geb/Mathlib/Data/Nat/`.

### Concrete-syntax prototype

`Geb/Internal/ConcreteSyntax.lean` implements the format-independent
core and the canonical S-expression form of RFC 9804 restricted to the
bare tree, `Geb/Internal/CanonicalSExpr.lean` a second spelling of
the same grammar, and `Geb/Internal/ReadableSExpr.lean` a readable
spelling of the rose presentation over a different grammar, with tests
in the corresponding `GebTests` modules.
[docs/concrete-syntaxes.md](docs/concrete-syntaxes.md) § Roadmap
states the staging; the next items are the JSON core profile,
deterministic CBOR after it, the
cross-syntax agreement theorem, and the lift of every syntax from `Ast`
to `Doc`. The readable spelling is the first syntax over a second data
model, non-negative integers and lists where the canonical encoding has
octet strings, so what the JSON core profile adds is the
bracket-and-comma grammar, the `Lean.Json` differential-testing oracle
and cross-language reach.

The occurrence vocabulary is absent, so the two design consequences that
[docs/concrete-syntaxes.md](docs/concrete-syntaxes.md) § Which
occurrences the rose presentation can name draws are unformalized.
Formalizing them takes a `Dir`/`Path` word type, a subtree selector
interpreting a path against a tree, a map from rose child indices to
binary paths, and a proof that every path in its image is empty or ends
in `L` — that inclusion, not its converse, is what the consequences
rest on; the converse upgrades it to the biconditional the document
states. A path vocabulary with no selector to interpret it has no
consumer, so all of this belongs to the stage at which a syntax
annotates occurrences, not before. The rose/binary orientation
`Ast.toRose` fixes has to be versioned at that point, since a path's
meaning depends on it.

`Geb.finEnumFin` and `Geb.finEnumEmpty` are choice-free `FinEnum`
constructions with nothing syntax-specific about them, standing in for
mathlib's `FinEnum.fin` and `FinEnum.empty`, which reach
`Classical.choice` through `FinEnum.ofList`. `Geb.finEnumFin` duplicates
`finEnumFin2` and `finEnumFin0` in
`GebTests/Mathlib/Data/PFunctor/Presheaf/Fixtures.lean`, which take the
same `Equiv.refl` route for the same reason, and duplicates the shared
`FinEnum.finFin` in `Geb/Mathlib/Data/FinEnum.lean`; `Geb.finEnumEmpty`
is `FinEnum Empty`, built from an explicit `Empty ≃ Fin 0`, and
subsumes none of the shared instances there (`FinEnum.unit` and
`FinEnum.finSum` do not reach it). Moving all of them beside
the choice-free decidability instances in `Geb/Mathlib/Data/FinEnum.lean`
is a separate concern from the syntax layer, so it belongs on its own
branch per [CONTRIBUTING.md](CONTRIBUTING.md) § Concern shape.

Reusing core's decimal layer is foreclosed, not merely costlier. Core
supplies the whole layer, including the decoder `Nat.ofDigitChars` and
the round trip `Nat.ofDigitChars_ten_toDigits`, which is
`Csexp.digitsVal_decOf` verbatim. Measured at v4.33.0-rc1, that theorem
depends on `Classical.choice`, as does every core lemma relating
`Nat.toDigits b n` to `Nat.toDigits b (n / b)`, `Nat.toDigits_eq_if`
among them — so the round trip can be neither imported nor reproved from
core's recursion equation. Choice-free in core are `Nat.digitChar`,
`Nat.toNat_digitChar_of_lt_ten`, `Nat.isDigit_of_mem_toDigits` and
`Nat.length_toDigits_pos`, which is not enough to build on. Reopen if a
choice-free recursion equation for `Nat.toDigits` lands upstream.

Follow-on work on the readable spelling, none of it scheduled.

- **Indentation.** The printer emits one line, which is deterministic
  and needs no layout rule; a multi-line discipline is a formatter
  refinement over the same grammar. Any such formatter must respect
  that parinfer's Indent Mode is permitted to change the AST by design,
  so only its Paren Mode composes with a retraction law.
- **Atom quoting and escaping.** Reached at roadmap stage 2, when
  `Ann`'s `Option String` and `List String` enter the syntax. Until
  then every atom is `[0-9]+`.
- **Named labels.** Labels are `Fin k` and print as numerals. A label
  type carrying names would let one printer serve a syntax with
  constructor names, and is a change to the rose layer with its own
  concern.
- **Comments.** R7RS, EDN and `sexplib` all provide them; nothing in
  the bare tree consumes one, and
  [docs/concrete-syntaxes.md](docs/concrete-syntaxes.md) § Lexical
  comments are not durable records why they are not part of the durable
  model.
- **Commas as whitespace.** Admitting them would accept the
  comma-separated spellings of the lists the grammar already covers,
  which are well-formed EDN; no tree needs it, and EDN's vectors, maps,
  sets, strings, keywords and tagged elements stay outside the grammar
  either way.
- **Reading hand-written text as a `String`.** The parser consumes a
  `List Char`, and core's `String.toList` depends on
  `Classical.choice`, so the bridge from a written file to the parser's
  input is not choice-free as core supplies it; the tests use
  `List Char` literals and fixtures instead. Trigger: a choice-free
  conversion, which no part of the current design supplies.

### Prose-conformance pass over the concrete-syntax survey

In [docs/concrete-syntaxes.md](docs/concrete-syntaxes.md), § Local
verification, § Roadmap with § Relation to existing repository content,
§ Caveats, § Readable S-expressions (R7RS, EDN, sexplib) with the
readable form's profile decisions in § Canonical S-expressions
(RFC 9804), and the paragraphs elsewhere that describe this repository's
implementation were written here; the rest, between § The AST and its
isomorphisms and § References, is inherited text. The inherited material
has not had a pass against
[CONTRIBUTING.md](CONTRIBUTING.md) § Style and references, and carries
value-laden adjectives and evaluative framing that the style rule
excludes. § Status states the same scope, listing itself and
§ References's opening paragraph among the repository-written material
as well.

One factual item rides along with that pass: the document's
§ References duplicates bibliographic detail that
[docs/references.bib](docs/references.bib) holds for RFC 9804, the
Petit-Huguenin draft, R7RS, EDN, RFC 8259, RFC 6962
and Uustalu and Vene 2011, and roughly thirty-five further works there
have no `.bib` entry, several no searchable identifier.

### Lambda arrow in `GebTests/Mathlib/CategoryTheory/ElementaryTopos.lean`

Six ordinary lambdas there are spelled `fun x => ...` rather than
`fun x ↦ ...`. [docs/rules/lean-coding.md](docs/rules/lean-coding.md)
binds every `.lean` file in the repository through its `paths`
frontmatter, and its § Coding style lists `↦` among the Unicode forms
mathlib uses; every other `.lean` file in the repository follows it.
Correcting these is a separate concern from any current branch per
[CONTRIBUTING.md](CONTRIBUTING.md) § Concern shape.

### Spec and plan lifecycle beyond one topic branch

[CONTRIBUTING.md](CONTRIBUTING.md) § Concern shape orders spec and plan
commits for a workstream that is one topic branch. It says nothing about
a series of branches merging separately into an append-only `main`, nor
about a topic branch with two topic-branch parents. Since that ordering
was introduced, `main` has never carried two specs at once, so no
practice settles either question. Settle both.

## Triggers (do when condition fires)

- **Choice-free bound for `Fin.divNat` in Batteries**:
  `Geb/Mathlib/Data/Fin/Basic.lean` exists because Batteries' `Fin.divNat`
  proves its bound through `Nat.div_lt_of_lt_mul`, which depends on
  `Classical.choice`, and the two round trips stated over `Fin.divNat` inherit
  that dependence; `Fin.modNat` and `Fin.mkDivMod` depend on no axiom outside
  `propext`. A choice-free bound upstream removes the reason for the module.
  Trigger: Batteries admits such a bound, at which point
  `Geb/Mathlib/Data/Fin/Basic.lean` and its test parallel are deleted and
  `Geb/Mathlib/Logic/Equiv/Fin/Basic.lean` is restated over `Fin.divNat`,
  `Fin.modNat` and `Fin.mkDivMod`.
- **Choice-free tree-scanner allowlist entries**:
  `Geb/Internal/Computability/TreeScanner/Steps.lean`, `Bound.lean` and the
  `GebTests/Internal/Computability/TreeScanner/Machine.lean` mirror are in
  `GebMeta.classicalAllowedModules` because Cslib's
  `Turing.MultiTapeTM.Cfg.inputSymbol` and
  `Turing.MultiTapeTM.inputSymbolInner` depend on `Classical.choice` (see
  § Choice-free patch to Cslib's multi-tape Turing machine API). Trigger:
  both are cleaned upstream and the pin moves past them, at which point
  `Steps.lean` and the mirror recover choice-free content of their own;
  leaving their entries in place past that point would misdescribe the
  allowlist's criterion, so the entries are removed, leaving only
  `Bound.lean` admitted — `Turing.MultiTapeTM.spaceUsed`'s `Finset.image`
  root is a separate, unremovable dependence that keeps `Bound.lean`
  admitted regardless.
- **`lake shake --keep-implied` versus mathlib CI's plain `lake shake`**: a
  repo-wide decision, on a separate branch, on whether to drop `--keep-implied`
  from the `lake shake` step in `scripts/pre-push.sh` and minimise imports
  across the affected files,
  or to record why the project diverges from mathlib CI here.
  `Geb/Mathlib/CategoryTheory/ElementaryTopos.lean` imports
  `Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts`,
  which is transitively supplied by the next import,
  `scripts/pre-push.sh`'s `lake shake` report, but without that flag, `lake
  shake` reports it as removable, and reports the same pattern across the tree:
  `lake shake --add-public --keep-prefix Geb GebTests` reports 14
  `Geb/Mathlib/` files and 5 `GebTests` ones, exiting 1. mathlib CI runs `lake
  shake` without `--keep-implied`, and `CONTRIBUTING.md` § Floodgate test
  commits the repo to shipping `Geb/Mathlib/` PRs with no source-code changes.
- **Slice polynomial functor natural isomorphism**: when a constructive
  (computable) `Type`-is-locally-cartesian-closed structure is available, in
  mathlib or built here, establish the natural isomorphism between
  `SlicePFunctor.functor` and the categorical composite `Σ_t ∘ Π_f ∘ Δ_s`.
- **Adopt `leanprover-community/upstreaming-dashboard-action`**: when we judge
  we have enough novel and interesting content that members of the mathlib
  community would likely want to be made aware of the project — a standing
  question, revisited as content grows. Then add the action to CI plus a
  Pages-published dashboard following FLT's pattern.
- **`downstream-reports` registration**: a manual periodic checkpoint by the
  user. Trigger: "do we have enough substantive content that registration would
  be informative for the community, given the daily Zulip notification cost?"
  The pipeline and its trigger are described in `docs/process.md` § LKG/FKB
  pipeline.
- **Verso adoption** (three scopes with distinct gates; doc-gen4 and Verso are
  complementary, not alternatives — doc-gen4 generates the API reference, Verso
  authors hand-written prose):
  1. Docstrings in `.lean` files: gated on doc-gen4 gaining Verso-aware
     rendering and mathlib migrating to Verso; contraindicated for
     `Geb/Mathlib/` and `Geb/Cslib/` until both hold (Verso-markup docstrings
     would read as foreign to mathlib reviewers and would not render on the
     doc-gen4 site).
  2. Persistent prose (`docs/`, a future Geb-language exposition): gated on the
     prose growing substantial and describing stable, existing code.
     `CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`, `docs/process.md`, and
     `docs/rules/*` remain Markdown regardless (GitHub rendering, tool and
     `@import` consumption, markdownlint, doctoc).
  3. Transient design docs on feature branches: no external gate; candidate for
     a local-only Verso build to evaluate authoring ergonomics and
     type-checking of embedded Lean.

  Currently using Markdown rendered by doc-gen4. A local pilot (2026-07-02)
  validated the mechanism: Verso and mathlib coexist in one lake project at
  v4.32.0-rc1, embedded Lean type-checks (a mismatch fails the build with a
  locatable error), and within-document references resolve. Two follow-up
  workstreams, each its own spec/plan cycle when taken up:
  - Persistent Geb-language exposition seed chapter in Verso (scope 2), once
    exposition-worthy prose exists.
  - Verso for transient feature-branch design docs (scope 3); a change to the
    current Markdown-based brainstorming and writing-plans flow, so it needs
    its own scoping.
- **Project-specific `geb-development` skill**: when recurring patterns
  accumulate that fit neither `CONTRIBUTING.md`, `AGENTS.md`, `CLAUDE.md`,
  `docs/process.md`, `docs/rules/*.md`, nor existing `.claude/rules/*.md`.
  Default is to wait for friction.
- **Author `.github/PULL_REQUEST_TEMPLATE/` for our repo**: trigger when the
  first PR against our own repo is opened (most likely the bump-PR cron).
- **Curated `notes` / `journal` directory**: trigger if recurring ad-hoc
  explorations accumulate that don't fit `docs/`.
- **Migrate `update.yml` from `GITHUB_TOKEN` to a PAT**: trigger if the manual
  close-and-reopen-to-fire-CI overhead on cron- created bump-PRs becomes
  burdensome.
- **Reconcile test-module import visibility**: `GebTests/` modules disagree on
  whether to `public import` the module under test: most do, a minority use
  plain `import`; `GebTests/Internal/`'s `public meta import` lines are in the
  same category. Import visibility changes what a module re-exports, so it is
  deferred. Trigger: the next branch that revises the test modules' interfaces.
- **Decide a test-declaration privacy discipline**: test modules mix `private`
  and public declarations with no uniform rule; the IndRec test's type-valued
  definitions must stay `@[expose]` public for cross-module compilation, so
  blanket privatization is not obviously desirable. Privacy changes
  module-interface visibility, so it is deferred. Trigger: the next branch that
  revises the test modules' interfaces.
- **Add `ext_iff` companions**: mathlib's naming guide (§ Extensionality)
  prescribes bidirectional `f = g ↔ ∀ x, f x = g x` companions alongside `ext`
  lemmas; none exist for `GrothendieckOp.hom_ext`, `CoGrothendieck.hom_ext`, or
  `IR.ext` (`IR.snd_eq_of_eq` is a converse but is not packaged as `ext_iff`).
  Adding them alters the theorem-set, so it is deferred. Trigger: the next
  branch that revises these interfaces.
- **Extract a shared presheaf test-fixtures module**: the `presheafWitness :
  PresheafPFunctor (Fin 2) (Fin 2)` fixture is duplicated in
  `GebTests/Mathlib/Data/PFunctor/Presheaf/Basic.lean` and
  `.../Presheaf/W.lean` because the `Basic` test module has no `public
  section`. Trigger when a third consumer appears: introduce a
  `public`-exported `GebTests/Mathlib/Data/PFunctor/Presheaf/Fixtures.lean` and
  import it from each. The condition has been met:
  `.../Presheaf/Decidable.lean` re-declares the same fixture data as a third
  consumer. Take the extraction together with the two items above (test-module
  import visibility, test-declaration privacy discipline); the extraction
  entails both, since the fixtures module can only be shared by making the
  currently-private fixture data public and importing it from every consumer.
- **Choice-free `Array.ofFn` lemmas**: when an upstream submission touching
  root `Vector`'s `ofFn` API is prepared, give `Array.getElem_ofFn_go`
  (`Init/Data/Array/Lemmas.lean`) a choice-free proof in Lean core, from which
  `Array.getElem_ofFn`, `Array.toList_ofFn`, `List.toArray_ofFn`,
  `Vector.getElem_ofFn`, `Vector.ofFn_getElem`, `Vector.getElem_range` and
  `Vector.getElem_finRange` all follow, retiring `Vector.ofFnC` and its round
  trips. It does not retire the `get`/`getElem` bridge in the same module: core
  states no `Vector.get_eq_getElem`, and a repaired core lemma is still in
  `getElem` form. The bridge goes only if the direct
  `Batteries.Data.Vector.Lemmas` import is taken at the same time, which the
  repair would make safe by de-tainting Batteries' `get_ofFn` and `get_range`;
  that is a second decision, not a consequence of this one. This is a Lean core
  submission, not a mathlib one, and it does not reach
  `Geb/Mathlib/Data/Vector/NodupEquivFin.lean`, whose statement is an `Equiv`
  and so has no core or Batteries home.
- **Choice-free `Skeletal FinSetSkel`**: when a use for it arises outside an
  allowlisted module, prove it directly rather than transporting it along the
  isomorphism to `FintypeCat.Skeleton`. That needs a choice-free pigeonhole,
  mathlib's `Fin.equiv_iff_eq`, `Fintype.card_congr` and `Fintype.card_fin` all
  depending on `Classical.choice`. Its consumers are the wrapper and the one
  allowlisted test module that identifies a pushout, so no such use has arisen.
- **mathlib-to-Batteries dependency edge**: whether mathlib accepts a
  `Mathlib/`-to-`Batteries/` dependency edge is a maintainer judgement — no
  `Mathlib.*` module references `UnionFind` — and
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`, the mathlib-targeted
  consumer of the union-find layer, needs one to extract.
  (`Geb/Mathlib/Data/UnionFind/OfEdges.lean` itself does not: its own upstream
  target is Batteries.) Trigger: the preparation of that module's upstream
  submission, which outlives the FinSetSkel development.
- **Check the leakage prefix in an import line's comment tail**:
  `scripts/lint-imports.sh` Rule 2 exempts a whole import line from the
  self-prefix check, so a self-prefix in a trailing comment on an import line
  passes clean — verified by adding `public import Geb.Mathlib.Bar  -- see
  Geb.Mathlib.Baz` under `GebTests/Mathlib/`. Not a regression: the rule has
  always exempted whole lines. The fix direction is to exempt the import path
  alone and apply the prefix check to the line's comment tail. Trigger: the
  next branch that revises `scripts/lint-imports.sh`.
- **Repo-relative paths in upstream-eligible docstrings**: docstrings under
  `Geb/Mathlib/` name paths that carry no meaning for a mathlib reviewer, and
  `scripts/extract-pr.sh` rewrites import lines only, so such prose survives
  extraction unchanged. Instances include the module path in
  `Geb/Mathlib/CategoryTheory/FinSetSkel/Coequalizer.lean` and the same pattern
  in `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`. Repo-wide, so no one
  workstream's to fix. Trigger: a repo-wide pass over upstream-eligible
  docstrings, on its own branch. Workstream labels were a second instance of
  this and are gone: a workstream is a transient concept whose name is
  arbitrary, so it cannot be referred to from persistent code or documentation
  at all. `TODO.md` is where workstreams are named, being the roadmap that
  defines them.
- **`scripts/extract-pr.sh` does not rewrite `meta import` lines**: its rewrite
  is anchored to `^(public import|import)`, so a `public meta import` of a
  self-prefixed sibling is emitted with the `Geb.Mathlib.` prefix intact and
  the extracted file does not compile. The two such lines are
  `GebTests/Mathlib/Data/UnionFind/OfEdges.lean` and
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/Quotient.lean`, where the
  `#guard` assertions need the module under test available to meta code. This
  is the rewriter's counterpart to the `lint-imports.sh` item above: both
  enumerate import forms and both predate the module system's `meta` forms.
  Trigger: the next branch that revises `scripts/extract-pr.sh`, or the first
  extraction of either module.
- **Verify the attested locators**: three locators are recorded from secondary
  attestation and none is verified against its primary source.
  [nLabSkeletalCategory] attests Mac Lane, _Categories for the Working
  Mathematician_ (1971), p. 91 and Riehl, _Category Theory in Context_ (2017),
  p. 34 for the skeleton of a category; [nLabFinSet] attests Johnstone,
  _Sketches of an Elephant_, example 2.1.2 for the category of finite sets
  being an elementary topos. Attestation by a secondary source is not
  verification, on the [Pare1974] precedent. Four further primary sources are
  cited unread, on the same footing: `docs/references.bib` attests
  [Thompson1972] and [Cobham1965] through [Strahm2003] and [Clote1999], and
  [Ritchie1963] and [Bellantoni1992] through [Clote1999] alone. Trigger: the
  acquisition of any of the seven primary sources, which discharges that
  locator or attribution and leaves the entry standing for the others.
- **Reconcile `## Main statements` across the test modules**:
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean` carries
  the section, and its siblings do not although each declares named
  theorems. `docs/rules/lean-coding.md` § Documentation requires a section
  when it has content. Trigger: the next occasion to revise those modules.
- **A workstream needs programmable building blocks for terms of `B`**:
  port the derived function library of the reference development's
  `BCLib.v`. Its `Require Import` line also names `BellantoniCook.Bitstring`,
  whose bitstring type is the notation `bs := list bool`; that type is
  `List Bool` directly here, so the port is unaffected by the additional
  dependency.
- **A consumer needs `DecidableEq` or `Repr` for `BellantoniCook.BC`**:
  derive them on `Shape` and lift along `sig.W`'s subtype.
- **A workstream needs the polytime checker of [HeraudNowak2011] as a
  term-level artifact**: add an untyped `Ast` and
  `check : Ast → Option ((n s : ℕ) × BellantoniCook.BCOf n s)` over
  `SlicePFunctor.decidableWValid`.
- **Allowing `Geb/Cslib/` to import `Geb.Mathlib.*`**: the case for it is
  the reason `docs/rules/upstream-eligible.md` gives, that unupstreamed
  mathlib-targeted content is unavailable to a CSLib PR, holds equally of
  one `Geb/Mathlib/` module importing another. The case against it, which
  the change must answer: extraction of a `Geb/Mathlib/` module orders
  PRs within one review queue, whereas a `Geb/Cslib/` module importing
  `Geb.Mathlib.*` waits on mathlib merge, mathlib release and CSLib's own
  mathlib bump, three cadences the project does not set, against
  CONTRIBUTING § Floodgate test's "on short notice". The converse
  direction stays barred on its own reason: mathlib does not depend on
  CSLib, so no ordering makes a `Geb/Mathlib/` module's `Cslib.*` import
  extractable. The change set discovered so far:
  - `scripts/lint-imports.sh` — the two Cslib `check_subtree` calls, with
    `Geb.Mathlib.` added to both the allowed-prefix and the
    leakage-prefix list, since extraction rewrites that prefix too; and
    the header comment block restating the allowed-import table.
  - `scripts/extract-pr.sh` — the `Geb/Cslib/*` and `GebTests/Cslib/*`
    arms set one `rewrite_prefix` each, so a `Geb.Mathlib.` import is
    emitted verbatim and the extracted file does not compile. A second
    rewrite pair is needed.
  - `scripts/tests/test-lint-imports.sh` — the case asserting exit 1 on
    `import Geb.Mathlib.Foo` in `Geb/Cslib/` must be inverted; a
    `GebTests/Cslib/` parallel case does not exist and should be added.
  - `scripts/tests/test-extract-pr.sh` — a case for the new rewrite.
  - `docs/rules/upstream-eligible.md` — the `Geb/Cslib/` and
    `GebTests/Cslib/` table rows, the § Floodgate test sentence asserting
    that each subtree's extractability is independent of the other,
    which the change falsifies, and the closing cross-subtree paragraph.
  - `docs/process.md` § Floodgate test, which carries the rationale.
  - Adjacent and not bundled: `Batteries.` is arguably missing from the
    `Geb/Cslib/` allowed list by the same argument, CSLib depending on
    mathlib which depends on Batteries.

  Trigger: a `Geb/Cslib/` module needing content from `Geb/Mathlib/`.
- **A recursion combinator for `Geb/Mathlib/Computability/Cobham/`**:
  discharging the `Rec` bound of [HeraudNowak2011] § 3.1 once for all
  users rather than at each use, by truncating each layer against the
  bound, with an agreement law relating it to naive recursion, at the
  arities `Cobham.COf n` already tracks, and a naming question, the
  module carrying no settled name for it.
  [BeckmannBussFriedmanMuellerThapen2017] Definition 2.7's syntactic
  Cobham recursion, which removes the embedding proviso by returning `0`
  where the condition fails, is the nearest published precedent for a
  recursion scheme discharging its own bound, and is not this
  construction. Deferred: at the Cobham tree recognizer's three
  recursions it is net cost, the agreement law's hypothesis needing the
  naive recursion's unfolding lemmas anyway. Trigger: a Cobham module
  reaching a fourth recursion.
- **`Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc/` gains a second
  module, or either `FreeCoprodCompDisc.lean` is edited for another
  reason**: split `Geb/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean`
  and `GebTests/Mathlib/CategoryTheory/FreeCoprodCompDisc.lean` into
  directory indexes over `Basic.lean` files, as
  `Geb/Mathlib/Computability/BellantoniCook.lean` was split. Both
  `FreeCoprodCompDisc/` directories currently have no index of their own:
  `CategoryTheory.lean` imports the module and its `NatTrans` sibling
  directly, indexing two levels, which is what CONTRIBUTING.md § Repo
  structure's "one indexing file per directory" rules out.
  `GebTests/Mathlib/CategoryTheory/FinSetSkel/ElementaryTopos.lean` carries the
  section, and its siblings do not although each declares named theorems.
  `docs/rules/lean-coding.md` § Documentation requires a section when it has
  content. Trigger: the next occasion to revise those modules.
